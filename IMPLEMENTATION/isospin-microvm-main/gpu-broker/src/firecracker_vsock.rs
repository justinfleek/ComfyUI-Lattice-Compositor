// SPDX-License-Identifier: MIT
//! Firecracker vsock server
//!
//! Firecracker exposes vsock as a Unix domain socket. This module provides a
//! server that listens on the Firecracker vsock Unix socket and handles broker
//! requests.
//!
//! The wire protocol is identical to the regular vsock module.

use crate::broker::{Operation, Request, Response, SeqNo};
use crate::driver::Driver;
use crate::handle_table::ClientId;
use crate::proxy::BrokerProxy;
use std::io::{self, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;

// Import wire protocol from vsock module
use crate::vsock::{decode_operation, encode_response, WireRequest, WireResponse, WIRE_MAGIC, WIRE_VERSION, MAX_PAYLOAD_SIZE};

/// Configuration for Firecracker vsock server
#[derive(Debug, Clone)]
pub struct FirecrackerVsockConfig {
    /// Port to accept connections on (guest connects to this port)
    pub port: u32,
    /// Maximum concurrent connections
    pub max_connections: usize,
}

impl Default for FirecrackerVsockConfig {
    fn default() -> Self {
        Self {
            port: 9999,
            max_connections: 1000,
        }
    }
}

/// Firecracker vsock server
pub struct FirecrackerVsockServer<D: Driver + Send + 'static> {
    config: FirecrackerVsockConfig,
    uds_path: String,
    proxy: Arc<std::sync::Mutex<BrokerProxy<D>>>,
    next_client_id: AtomicU64,
    shutdown: AtomicBool,
}

impl<D: Driver + Send + 'static> FirecrackerVsockServer<D> {
    /// Create a new Firecracker vsock server
    pub fn new(uds_path: String, config: FirecrackerVsockConfig, proxy: BrokerProxy<D>) -> Self {
        Self {
            config,
            uds_path,
            proxy: Arc::new(std::sync::Mutex::new(proxy)),
            next_client_id: AtomicU64::new(1),
            shutdown: AtomicBool::new(false),
        }
    }

    /// Run the server (blocking)
    pub fn run(&self) -> io::Result<()> {
        // Firecracker vsock protocol: guest-initiated connections to port N
        // are forwarded to <uds_path>_<port> on the host.
        // So if uds_path=/tmp/fc.sock and port=9999, we listen on /tmp/fc.sock_9999
        let socket_path = format!("{}_{}", self.uds_path, self.config.port);
        
        tracing::info!(
            "Firecracker vsock server listening on {} (base={}, port={})",
            socket_path,
            self.uds_path,
            self.config.port
        );

        // Remove existing socket if present
        std::fs::remove_file(&socket_path).ok();
        
        // Create Unix socket listener
        let listener = UnixListener::bind(&socket_path)?;

        while !self.shutdown.load(Ordering::Relaxed) {
            match listener.accept() {
                Ok((stream, _)) => {
                    let client_id = self.next_client_id.fetch_add(1, Ordering::Relaxed);
                    let proxy = Arc::clone(&self.proxy);

                    tracing::info!("New Firecracker vsock connection, client_id={}", client_id);

                    thread::spawn(move || {
                        if let Err(e) = Self::handle_connection(stream, client_id, proxy) {
                            tracing::error!("Firecracker connection error for client {}: {}", client_id, e);
                        }
                        tracing::info!("Firecracker client {} disconnected", client_id);
                    });
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(std::time::Duration::from_millis(10));
                }
                Err(e) => {
                    tracing::error!("Accept error: {}", e);
                }
            }
        }

        Ok(())
    }

    /// Handle a single client connection
    fn handle_connection(
        mut stream: UnixStream,
        client_id: u64,
        proxy: Arc<std::sync::Mutex<BrokerProxy<D>>>,
    ) -> io::Result<()> {
        let mut header_buf = [0u8; 32];
        let mut payload_buf = vec![0u8; MAX_PAYLOAD_SIZE];

        // Register client with proxy
        {
            let mut proxy = proxy.lock().unwrap();
            let req = Request {
                client: ClientId(client_id),
                seq: SeqNo(0),
                op: Operation::RegisterClient,
            };
            let _ = proxy.process(req);
        }

        loop {
            // Read request header
            if let Err(e) = stream.read_exact(&mut header_buf) {
                if e.kind() == io::ErrorKind::UnexpectedEof {
                    break; // Client disconnected
                }
                return Err(e);
            }

            // Parse header
            let req_header = match WireRequest::from_bytes(&header_buf) {
                Some(h) => h,
                None => {
                    tracing::warn!("Invalid request header");
                    continue;
                }
            };

            // Copy fields from packed struct to local variables
            let magic = req_header.magic;
            let op_type = req_header.op_type;
            let payload_len = req_header.payload_len as usize;
            let seq = req_header.seq;

            // Validate magic
            if magic != WIRE_MAGIC {
                tracing::warn!("Bad magic: 0x{:x}", magic);
                continue;
            }
            if payload_len > MAX_PAYLOAD_SIZE {
                tracing::warn!("Payload too large: {}", payload_len);
                continue;
            }

            if payload_len > 0 {
                stream.read_exact(&mut payload_buf[..payload_len])?;
            }

            // Decode operation
            let operation = match decode_operation(op_type, &payload_buf[..payload_len]) {
                Some(op) => op,
                None => {
                    tracing::warn!("Failed to decode operation type {}", op_type);
                    // Send error response
                    let resp = WireResponse::new(
                        client_id,
                        seq,
                        false,
                        0,
                    );
                    stream.write_all(&resp.to_bytes())?;
                    continue;
                }
            };

            // Process through proxy
            let request = Request {
                client: ClientId(client_id),
                seq: SeqNo(seq),
                op: operation,
            };

            let response = {
                let mut proxy = proxy.lock().unwrap();
                proxy.process(request)
            };

            // Encode result
            let (success, result_bytes) = encode_response(&response);

            // Send response header
            let resp = WireResponse::new(
                client_id,
                seq,
                success,
                result_bytes.len() as u32,
            );
            stream.write_all(&resp.to_bytes())?;

            // Send result payload
            if !result_bytes.is_empty() {
                stream.write_all(&result_bytes)?;
            }
        }

        // Unregister client
        {
            let mut proxy = proxy.lock().unwrap();
            let req = Request {
                client: ClientId(client_id),
                seq: SeqNo(0),
                op: Operation::UnregisterClient,
            };
            let _ = proxy.process(req);
        }

        Ok(())
    }

    /// Signal shutdown
    #[allow(dead_code)]
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::Relaxed);
    }
}
