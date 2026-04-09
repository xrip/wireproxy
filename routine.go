package wireproxy

import (
	"bytes"
	"context"
	srand "crypto/rand"
	"crypto/subtle"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"os"
	"path"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/net/icmp"
	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"
	"golang.zx2c4.com/wireguard/device"

	"github.com/things-go/go-socks5"
	"github.com/things-go/go-socks5/bufferpool"
	"github.com/things-go/go-socks5/statute"

	"net/netip"

	"golang.zx2c4.com/wireguard/tun/netstack"
)

// errorLogger is the logger to print error message
var errorLogger = log.New(os.Stderr, "ERROR: ", log.LstdFlags)

// CredentialValidator stores the authentication data of a socks5 proxy
type CredentialValidator struct {
	username string
	password string
}

// VirtualTun stores a reference to netstack network and DNS configuration
type VirtualTun struct {
	Tnet          *netstack.Net
	Dev           *device.Device
	SystemDNS     bool
	Conf          *DeviceConfig
	ResolveConfig *ResolveConfig
	// PingRecord stores the last time an IP was pinged
	PingRecord     map[string]uint64
	PingRecordLock *sync.Mutex
}

// RoutineSpawner spawns a routine (e.g. socks5, tcp static routes) after the configuration is parsed
type RoutineSpawner interface {
	SpawnRoutine(vt *VirtualTun)
}

type addressPort struct {
	address string
	port    uint16
}

// LookupAddr lookups a hostname.
// DNS traffic may or may not be routed depending on VirtualTun's setting
func (d VirtualTun) LookupAddr(ctx context.Context, name string) ([]string, error) {
	if d.SystemDNS {
		return net.DefaultResolver.LookupHost(ctx, name)
	}
	return d.Tnet.LookupContextHost(ctx, name)
}

// ResolveAddrWithContext resolves a hostname and returns an AddrPort.
// DNS traffic may or may not be routed depending on VirtualTun's setting
func (d VirtualTun) ResolveAddrWithContext(ctx context.Context, name string) (*netip.Addr, error) {
	addrs, err := d.LookupAddr(ctx, name)
	if err != nil {
		return nil, err
	}

	addrs_v4 := []netip.Addr{}
	addrs_v6 := []netip.Addr{}

	for _, saddr := range addrs {
		addr, err := netip.ParseAddr(saddr)
		if err == nil {
			if addr.Is4() {
				addrs_v4 = append(addrs_v4, addr)
			} else if addr.Is6() {
				addrs_v6 = append(addrs_v6, addr)
			}
		}
	}

	rand.Shuffle(len(addrs_v4), func(i, j int) {
		addrs_v4[i], addrs_v4[j] = addrs_v4[j], addrs_v4[i]
	})
	rand.Shuffle(len(addrs_v6), func(i, j int) {
		addrs_v6[i], addrs_v6[j] = addrs_v6[j], addrs_v6[i]
	})

	addrs_all := []netip.Addr{}

	switch d.ResolveConfig.ResolveStrategy {
	case "ipv4":
		addrs_all = append(addrs_v4, addrs_v6...)
	case "ipv6":
		addrs_all = append(addrs_v6, addrs_v4...)
	}

	if len(addrs_all) == 0 {
		return nil, errors.New("no address found for: " + name)
	}

	return &addrs_all[0], nil
}

// Resolve resolves a hostname and returns an IP.
// DNS traffic may or may not be routed depending on VirtualTun's setting
func (d VirtualTun) Resolve(ctx context.Context, name string) (context.Context, net.IP, error) {
	log.Printf("Resolving address for %s\n", name)

	addr, err := d.ResolveAddrWithContext(ctx, name)
	if err != nil {
		return nil, nil, err
	}

	return ctx, addr.AsSlice(), nil
}

func parseAddressPort(endpoint string) (*addressPort, error) {
	name, sport, err := net.SplitHostPort(endpoint)
	if err != nil {
		return nil, err
	}

	port, err := strconv.Atoi(sport)
	if err != nil || port < 0 || port > 65535 {
		return nil, &net.OpError{Op: "dial", Err: errors.New("port must be numeric")}
	}

	return &addressPort{address: name, port: uint16(port)}, nil
}

func (d VirtualTun) resolveToAddrPort(endpoint *addressPort) (*netip.AddrPort, error) {
	addr, err := d.ResolveAddrWithContext(context.Background(), endpoint.address)
	if err != nil {
		return nil, err
	}

	addrPort := netip.AddrPortFrom(*addr, endpoint.port)
	return &addrPort, nil
}

// makeAssociateHandler creates a custom UDP ASSOCIATE handler that binds to the
// TCP connection's local address instead of 0.0.0.0, fixing the BND.ADDR issue
// where clients can't handle 0.0.0.0:port in the reply.
func makeAssociateHandler(vt *VirtualTun, bufferPool bufferpool.BufPool) func(ctx context.Context, writer io.Writer, request *socks5.Request) error {
	return func(ctx context.Context, writer io.Writer, request *socks5.Request) error {
		// Extract listen IP from the TCP connection's local address
		localTCPAddr, ok := request.LocalAddr.(*net.TCPAddr)
		if !ok {
			errorLogger.Printf("UDP Associate: failed to get local TCP address: %v\n", request.LocalAddr)
			if err := socks5.SendReply(writer, statute.RepServerFailure, nil); err != nil {
				return err
			}
			return errors.New("failed to get local TCP address")
		}

		// Bind to the same IP as the TCP listener, not 0.0.0.0
		bindAddr := &net.UDPAddr{IP: localTCPAddr.IP, Port: 0}
		bindLn, err := net.ListenUDP("udp", bindAddr)
		if err != nil {
			errorLogger.Printf("UDP Associate: failed to listen on %v: %v\n", bindAddr, err)
			if err := socks5.SendReply(writer, statute.RepServerFailure, nil); err != nil {
				return err
			}
			return fmt.Errorf("listen udp failed: %w", err)
		}

		// Send BND.ADDR reply with actual listen address (not 0.0.0.0)
		if err := socks5.SendReply(writer, statute.RepSuccess, bindLn.LocalAddr()); err != nil {
			bindLn.Close()
			return fmt.Errorf("failed to send reply: %w", err)
		}

		// Spawn goroutine for UDP relay
		go func() {
			conns := sync.Map{}
			buf := bufferPool.Get()
			defer func() {
				bufferPool.Put(buf)
				bindLn.Close()
				conns.Range(func(key, value any) bool {
					if connTarget, ok := value.(net.Conn); ok {
						connTarget.Close()
					}
					return true
				})
			}()

			for {
				n, srcAddr, err := bindLn.ReadFromUDP(buf[:cap(buf)])
				if err != nil {
					if errors.Is(err, io.EOF) || errors.Is(err, net.ErrClosed) {
						return
					}
					continue
				}

				pk, err := statute.ParseDatagram(buf[:n])
				if err != nil {
					continue
				}

				// Validate source address matches the associate request
				srcEqual := (request.DestAddr.IP.IsUnspecified() || request.DestAddr.IP.Equal(srcAddr.IP)) &&
					(request.DestAddr.Port == 0 || request.DestAddr.Port == srcAddr.Port)
				if !srcEqual {
					continue
				}

				connKey := srcAddr.String() + "--" + pk.DstAddr.String()

				if target, ok := conns.Load(connKey); !ok {
					// Dial through WireGuard tunnel using vt.Tnet.DialContext
					targetNew, err := vt.Tnet.DialContext(ctx, "udp", pk.DstAddr.String())
					if err != nil {
						errorLogger.Printf("UDP Associate: dial to %v failed: %v\n", pk.DstAddr, err)
						continue
					}
					conns.Store(connKey, targetNew)

					// Read from remote and write back to client
					go func() {
						buf := bufferPool.Get()
						defer func() {
							targetNew.Close()
							conns.Delete(connKey)
							bufferPool.Put(buf)
						}()

						for {
							n, err := targetNew.Read(buf[:cap(buf)])
							if err != nil {
								if errors.Is(err, io.EOF) || errors.Is(err, net.ErrClosed) {
									return
								}
								errorLogger.Printf("UDP Associate: read from remote %s failed: %v\n", targetNew.RemoteAddr(), err)
								return
							}

							tmpBuf := bufferPool.Get()
							tmpBuf = append(tmpBuf, pk.Header()...)
							tmpBuf = append(tmpBuf, buf[:n]...)
							if _, err := bindLn.WriteTo(tmpBuf, srcAddr); err != nil {
								bufferPool.Put(tmpBuf)
								errorLogger.Printf("UDP Associate: write to client %s failed: %v\n", srcAddr, err)
								return
							}
							bufferPool.Put(tmpBuf)
						}
					}()

					if _, err := targetNew.Write(pk.Data); err != nil {
						errorLogger.Printf("UDP Associate: write to remote %s failed: %v\n", targetNew.RemoteAddr(), err)
						return
					}
				} else {
					if _, err := target.(net.Conn).Write(pk.Data); err != nil {
						errorLogger.Printf("UDP Associate: write to remote %s failed: %v\n", target.(net.Conn).RemoteAddr(), err)
						return
					}
				}
			}
		}()

		// Wait for TCP control connection to close
		buf := bufferPool.Get()
		defer bufferPool.Put(buf)

		for {
			_, err := request.Reader.Read(buf[:cap(buf)])
			if err != nil {
				bindLn.Close()
				if errors.Is(err, io.EOF) || errors.Is(err, net.ErrClosed) {
					return nil
				}
				return err
			}
		}
	}
}

// SpawnRoutine spawns a socks5 server.
func (config *Socks5Config) SpawnRoutine(vt *VirtualTun) {
	var authMethods []socks5.Authenticator
	if username := config.Username; username != "" {
		authMethods = append(authMethods, socks5.UserPassAuthenticator{
			Credentials: socks5.StaticCredentials{username: config.Password},
		})
	} else {
		authMethods = append(authMethods, socks5.NoAuthAuthenticator{})
	}

	bufferPool := bufferpool.NewPool(256 * 1024)
	options := []socks5.Option{
		socks5.WithDial(vt.Tnet.DialContext),
		socks5.WithResolver(vt),
		socks5.WithAuthMethods(authMethods),
		socks5.WithBufferPool(bufferPool),
		socks5.WithAssociateHandle(makeAssociateHandler(vt, bufferPool)),
	}

	server := socks5.NewServer(options...)

	if err := server.ListenAndServe("tcp", config.BindAddress); err != nil {
		log.Fatal(err)
	}
}

// SpawnRoutine spawns a http server.
func (config *HTTPConfig) SpawnRoutine(vt *VirtualTun) {
	server := &HTTPServer{
		config: config,
		dial:   vt.Tnet.Dial,
		auth:   CredentialValidator{config.Username, config.Password},
	}
	if config.Username != "" || config.Password != "" {
		server.authRequired = true
	}

	if config.CertFile != "" && config.KeyFile != "" {
		server.tlsRequired = true
	}

	if err := server.ListenAndServe("tcp", config.BindAddress); err != nil {
		log.Fatal(err)
	}
}

// Valid checks the authentication data in CredentialValidator and compare them
// to username and password in constant time.
func (c CredentialValidator) Valid(username, password string) bool {
	u := subtle.ConstantTimeCompare([]byte(c.username), []byte(username))
	p := subtle.ConstantTimeCompare([]byte(c.password), []byte(password))
	return u&p == 1
}

// connForward copy data from `from` to `to`
func connForward(from io.ReadWriteCloser, to io.ReadWriteCloser) {
	defer func() { _ = from.Close() }()
	defer func() { _ = to.Close() }()

	_, err := io.Copy(to, from)
	if err != nil {
		errorLogger.Printf("Cannot forward traffic: %s\n", err.Error())
	}
}

// tcpClientForward starts a new connection via wireguard and forward traffic from `conn`
func tcpClientForward(vt *VirtualTun, raddr *addressPort, conn net.Conn) {
	target, err := vt.resolveToAddrPort(raddr)
	if err != nil {
		errorLogger.Printf("TCP Server Tunnel to %s: %s\n", target, err.Error())
		return
	}

	tcpAddr := net.TCPAddrFromAddrPort(*target)

	sconn, err := vt.Tnet.DialTCP(tcpAddr)
	if err != nil {
		errorLogger.Printf("TCP Client Tunnel to %s: %s\n", target, err.Error())
		return
	}

	go connForward(sconn, conn)
	go connForward(conn, sconn)
}

// STDIOTcpForward starts a new connection via wireguard and forward traffic from `conn`
func STDIOTcpForward(vt *VirtualTun, raddr *addressPort, input *os.File, output *os.File) {
	target, err := vt.resolveToAddrPort(raddr)
	if err != nil {
		errorLogger.Printf("Name resolution error for %s: %s\n", raddr.address, err.Error())
		return
	}

	tcpAddr := net.TCPAddrFromAddrPort(*target)
	sconn, err := vt.Tnet.DialTCP(tcpAddr)
	if err != nil {
		errorLogger.Printf("TCP Client Tunnel to %s (%s): %s\n", target, tcpAddr, err.Error())
		return
	}

	go connForward(input, sconn)
	go connForward(sconn, output)
}

// SpawnRoutine spawns a local TCP server which acts as a proxy to the specified target
func (conf *TCPClientTunnelConfig) SpawnRoutine(vt *VirtualTun) {
	raddr, err := parseAddressPort(conf.Target)
	if err != nil {
		log.Fatal(err)
	}

	server, err := net.ListenTCP("tcp", conf.BindAddress)
	if err != nil {
		log.Fatal(err)
	}

	for {
		conn, err := server.Accept()
		if err != nil {
			log.Fatal(err)
		}
		go tcpClientForward(vt, raddr, conn)
	}
}

// SpawnRoutine connects to the specified target and plumbs it to STDIN / STDOUT
func (conf *STDIOTunnelConfig) SpawnRoutine(vt *VirtualTun) {
	raddr, err := parseAddressPort(conf.Target)
	if err != nil {
		log.Fatal(err)
	}

	go STDIOTcpForward(vt, raddr, conf.Input, conf.Output)
}

// tcpServerForward starts a new connection locally and forward traffic from `conn`
func tcpServerForward(vt *VirtualTun, raddr *addressPort, conn net.Conn) {
	target, err := vt.resolveToAddrPort(raddr)
	if err != nil {
		errorLogger.Printf("TCP Server Tunnel to %s: %s\n", target, err.Error())
		return
	}

	tcpAddr := net.TCPAddrFromAddrPort(*target)

	sconn, err := net.DialTCP("tcp", nil, tcpAddr)
	if err != nil {
		errorLogger.Printf("TCP Server Tunnel to %s: %s\n", target, err.Error())
		return
	}

	go connForward(sconn, conn)
	go connForward(conn, sconn)

}

// SpawnRoutine spawns a TCP server on wireguard which acts as a proxy to the specified target
func (conf *TCPServerTunnelConfig) SpawnRoutine(vt *VirtualTun) {
	raddr, err := parseAddressPort(conf.Target)
	if err != nil {
		log.Fatal(err)
	}

	addr := &net.TCPAddr{Port: conf.ListenPort}
	server, err := vt.Tnet.ListenTCP(addr)
	if err != nil {
		log.Fatal(err)
	}

	for {
		conn, err := server.Accept()
		if err != nil {
			log.Fatal(err)
		}
		go tcpServerForward(vt, raddr, conn)
	}
}

func (d VirtualTun) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	log.Printf("Health metric request: %s\n", r.URL.Path)
	switch path.Clean(r.URL.Path) {
	case "/readyz":
		body, err := json.Marshal(d.PingRecord)
		if err != nil {
			errorLogger.Printf("Failed to get device metrics: %s\n", err.Error())
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		status := http.StatusOK
		for _, record := range d.PingRecord {
			lastPong := time.Unix(int64(record), 0)
			// +2 seconds to account for the time it takes to ping the IP
			if time.Since(lastPong) > time.Duration(d.Conf.CheckAliveInterval+2)*time.Second {
				status = http.StatusServiceUnavailable
				break
			}
		}

		w.WriteHeader(status)
		_, _ = w.Write(body)
		_, _ = w.Write([]byte("\n"))
	case "/metrics":
		get, err := d.Dev.IpcGet()
		if err != nil {
			errorLogger.Printf("Failed to get device metrics: %s\n", err.Error())
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		var buf bytes.Buffer
		for _, peer := range strings.Split(get, "\n") {
			pair := strings.SplitN(peer, "=", 2)
			if len(pair) != 2 {
				buf.WriteString(peer)
				continue
			}
			if pair[0] == "private_key" || pair[0] == "preshared_key" {
				pair[1] = "REDACTED"
			}
			buf.WriteString(pair[0])
			buf.WriteString("=")
			buf.WriteString(pair[1])
			buf.WriteString("\n")
		}

		w.WriteHeader(http.StatusOK)
		_, _ = w.Write(buf.Bytes())
	default:
		w.WriteHeader(http.StatusNotFound)
	}
}

func (d VirtualTun) pingIPs() {
	for _, addr := range d.Conf.CheckAlive {
		socket, err := d.Tnet.Dial("ping", addr.String())
		if err != nil {
			errorLogger.Printf("Failed to ping %s: %s\n", addr, err.Error())
			continue
		}

		data := make([]byte, 16)
		_, _ = srand.Read(data)

		requestPing := icmp.Echo{
			Seq:  rand.Intn(1 << 16),
			Data: data,
		}

		var icmpBytes []byte
		if addr.Is4() {
			icmpBytes, _ = (&icmp.Message{Type: ipv4.ICMPTypeEcho, Code: 0, Body: &requestPing}).Marshal(nil)
		} else if addr.Is6() {
			icmpBytes, _ = (&icmp.Message{Type: ipv6.ICMPTypeEchoRequest, Code: 0, Body: &requestPing}).Marshal(nil)
		} else {
			errorLogger.Printf("Failed to ping %s: invalid address: %s\n", addr, addr.String())
			continue
		}

		_ = socket.SetReadDeadline(time.Now().Add(time.Duration(d.Conf.CheckAliveInterval) * time.Second))
		_, err = socket.Write(icmpBytes)
		if err != nil {
			errorLogger.Printf("Failed to ping %s: %s\n", addr, err.Error())
			continue
		}

		addr := addr
		go func() {
			n, err := socket.Read(icmpBytes[:])
			if err != nil {
				errorLogger.Printf("Failed to read ping response from %s: %s\n", addr, err.Error())
				return
			}

			replyPacket, err := icmp.ParseMessage(1, icmpBytes[:n])
			if err != nil {
				errorLogger.Printf("Failed to parse ping response from %s: %s\n", addr, err.Error())
				return
			}

			if addr.Is4() {
				replyPing, ok := replyPacket.Body.(*icmp.Echo)
				if !ok {
					errorLogger.Printf("Failed to parse ping response from %s: invalid reply type: %s\n", addr, replyPacket.Type)
					return
				}
				if !bytes.Equal(replyPing.Data, requestPing.Data) || replyPing.Seq != requestPing.Seq {
					errorLogger.Printf("Failed to parse ping response from %s: invalid ping reply: %v\n", addr, replyPing)
					return
				}
			}

			if addr.Is6() {
				replyPing, ok := replyPacket.Body.(*icmp.RawBody)
				if !ok {
					errorLogger.Printf("Failed to parse ping response from %s: invalid reply type: %s\n", addr, replyPacket.Type)
					return
				}

				seq := binary.BigEndian.Uint16(replyPing.Data[2:4])
				pongBody := replyPing.Data[4:]
				if !bytes.Equal(pongBody, requestPing.Data) || int(seq) != requestPing.Seq {
					errorLogger.Printf("Failed to parse ping response from %s: invalid ping reply: %v\n", addr, replyPing)
					return
				}
			}

			d.PingRecordLock.Lock()
			d.PingRecord[addr.String()] = uint64(time.Now().Unix())
			d.PingRecordLock.Unlock()

			defer func() { _ = socket.Close() }()
		}()
	}
}

func (d VirtualTun) StartPingIPs() {
	d.PingRecordLock.Lock()
	for _, addr := range d.Conf.CheckAlive {
		d.PingRecord[addr.String()] = 0
	}
	d.PingRecordLock.Unlock()

	go func() {
		for {
			d.pingIPs()
			time.Sleep(time.Duration(d.Conf.CheckAliveInterval) * time.Second)
		}
	}()
}
