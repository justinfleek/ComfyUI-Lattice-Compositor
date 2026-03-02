#!/usr/bin/env python3
"""
Bridge between Firecracker vsock and Cloud Hypervisor vsock

Listens on Firecracker's vsock socket and forwards to CH vsock broker.
"""
import socket
import os
import sys
import select
import threading

FC_SOCK_BASE = "/tmp/fc-worker.sock"
FC_PORT = 9999
CH_SOCK = "/tmp/gpu-vm-vsock.sock"
CH_PORT = 9999

def proxy_data(src, dst, name):
    """Proxy data from src to dst"""
    try:
        while True:
            data = src.recv(65536)
            if not data:
                break
            dst.sendall(data)
    except Exception as e:
        pass
    finally:
        try:
            src.close()
        except:
            pass
        try:
            dst.close()
        except:
            pass

def handle_client(fc_conn):
    """Handle a Firecracker vsock client connection"""
    try:
        # Connect to Cloud Hypervisor vsock
        ch_sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        ch_sock.connect(CH_SOCK)
        
        # Send CONNECT command
        ch_sock.sendall(f"CONNECT {CH_PORT}\n".encode())
        
        # Read response
        response = ch_sock.recv(1024)
        if not response.startswith(b"OK"):
            print(f"CH vsock connect failed: {response}")
            fc_conn.close()
            ch_sock.close()
            return
        
        print(f"Bridge established to CH vsock port {CH_PORT}")
        
        # Start bidirectional proxy
        t1 = threading.Thread(target=proxy_data, args=(fc_conn, ch_sock, "FC->CH"))
        t2 = threading.Thread(target=proxy_data, args=(ch_sock, fc_conn, "CH->FC"))
        t1.start()
        t2.start()
        t1.join()
        t2.join()
        
    except Exception as e:
        print(f"Bridge error: {e}")
    finally:
        try:
            fc_conn.close()
        except:
            pass

def main():
    fc_sock_path = f"{FC_SOCK_BASE}_{FC_PORT}"
    
    # Remove existing socket
    try:
        os.unlink(fc_sock_path)
    except:
        pass
    
    # Listen on Firecracker vsock socket
    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    server.bind(fc_sock_path)
    os.chmod(fc_sock_path, 0o777)
    server.listen(100)
    
    print(f"Vsock bridge listening on {fc_sock_path}")
    print(f"  -> Forwarding to {CH_SOCK} port {CH_PORT}")
    
    while True:
        conn, _ = server.accept()
        print(f"New Firecracker client connected")
        t = threading.Thread(target=handle_client, args=(conn,))
        t.start()

if __name__ == "__main__":
    main()
