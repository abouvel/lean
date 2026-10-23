"""CONNECT-only egress proxy; never logs headers, payloads, or credentials."""
import select
import socket
import socketserver

ALLOWED = {
    "chatgpt.com", "api.openai.com", "auth.openai.com",
    "sdmntprindiasocentral.oaiusercontent.com",
    "sdmntprsouthcentralus.oaiusercontent.com",
    "sdmntprcentralus.oaiusercontent.com",
}


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        self.request.settimeout(20)
        header = b""
        while b"\r\n\r\n" not in header and len(header) < 16384:
            data = self.request.recv(4096)
            if not data:
                return
            header += data
        try:
            method, target, _ = header.split(b"\r\n", 1)[0].decode("ascii").split()
            host, port_text = target.rsplit(":", 1)
            port = int(port_text)
        except (ValueError, UnicodeDecodeError):
            self.request.sendall(b"HTTP/1.1 400 Bad Request\r\n\r\n")
            return
        host = host.lower()
        if method != "CONNECT" or host not in ALLOWED or port != 443:
            print("DENIED", method, host, port, flush=True)
            self.request.sendall(b"HTTP/1.1 403 Forbidden\r\n\r\n")
            return
        try:
            upstream = socket.create_connection((host, port), timeout=20)
        except OSError:
            self.request.sendall(b"HTTP/1.1 502 Bad Gateway\r\n\r\n")
            return
        print("ALLOWED", host, port, flush=True)
        self.request.sendall(b"HTTP/1.1 200 Connection Established\r\n\r\n")
        _, extra = header.split(b"\r\n\r\n", 1)
        if extra:
            upstream.sendall(extra)
        with upstream:
            self.request.settimeout(None)
            upstream.settimeout(None)
            while True:
                ready, _, _ = select.select([self.request, upstream], [], [], 240)
                if not ready:
                    break
                for source in ready:
                    try:
                        data = source.recv(65536)
                        if not data:
                            return
                        (upstream if source is self.request else self.request).sendall(data)
                    except OSError:
                        return


class Server(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


if __name__ == "__main__":
    with Server(("0.0.0.0", 3128), Handler) as server:
        server.serve_forever()
