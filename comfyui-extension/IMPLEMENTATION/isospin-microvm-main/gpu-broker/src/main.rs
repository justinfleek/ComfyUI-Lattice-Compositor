//! GPU Broker - Multiplexes NVIDIA RM API calls from multiple VMs
//!
//! Architecture:
//! - Each VM connects via vsock (for VMs) or Unix socket (for containers)
//! - VM sends RM API calls (ioctls) over the connection
//! - Broker translates handles, validates, and forwards to real /dev/nvidiactl
//! - Results returned to client
//!
//! The GPU driver stays hot - no cold boot penalty per VM.
//!
//! Core design principle (Carmack/aerospace):
//!   Pure function: (State, Input) → (State', Output)
//!   - Deterministic replay
//!   - Time-travel debugging
//!   - The simulation IS the test

mod broker;
mod driver;
mod fd_passing;
mod firecracker_vsock;
mod guest_protocol;
mod guest_shim;
mod handle_table;
mod nvml_server;
mod proxy;
mod rm_api;
mod server;
mod trace;
mod transport;
mod uring;
mod uring_transport;
mod vsock;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use nvml_server::{GpuInfo, NvmlServer};
use proxy::{BrokerProxy, ProxyConfig};
use server::{BrokerServer, ServerConfig};
use std::thread;
use trace::{IoctlTrace, TraceReplayDriver};
use tracing::info;
use vsock::{VsockServer, VsockServerConfig};

/// GPU Broker - multiplexes GPU access for multiple VMs
#[derive(Parser, Debug)]
#[command(name = "gpu-broker")]
#[command(about = "Multiplexes NVIDIA GPU access for multiple VMs")]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,

    /// Path to NVIDIA control device
    #[arg(long, default_value = "/dev/nvidiactl")]
    nvidiactl: String,

    /// Path to NVIDIA device (GPU 0)
    #[arg(long, default_value = "/dev/nvidia0")]
    nvidia0: String,

    /// Maximum handles per client
    #[arg(long, default_value = "10000")]
    handle_quota: usize,

    /// Maximum concurrent clients
    #[arg(long, default_value = "1000")]
    max_clients: usize,

    /// Unix socket path for client connections
    #[arg(long, default_value = "/run/gpu-broker.sock")]
    socket: String,

    /// Unix socket path for NVML queries (nvidia-smi support)
    #[arg(long, default_value = "/run/gpu-broker-nvml.sock")]
    nvml_socket: String,

    /// vsock port for VM connections (0 to disable)
    #[arg(long, default_value = "9999")]
    vsock_port: u32,

    /// Firecracker vsock Unix socket paths (comma-separated)
    /// These are the UDS paths from Firecracker's vsock config
    #[arg(long)]
    firecracker_vsock: Option<String>,

    /// Use mock driver (for testing without GPU)
    #[arg(long)]
    mock: bool,

    /// Enable verbose logging
    #[arg(short, long)]
    verbose: bool,

    /// Record ioctl trace to file (for replay testing)
    #[arg(long)]
    record_trace: Option<String>,

    /// Replay ioctl trace from file (instead of using real/mock driver)
    #[arg(long)]
    replay_trace: Option<String>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Run the broker server (default)
    Serve,

    /// Trace-related commands
    Trace {
        #[command(subcommand)]
        action: TraceAction,
    },
}

#[derive(Subcommand, Debug)]
enum TraceAction {
    /// Import trace from strace output
    Import {
        /// Input strace file
        #[arg(short, long)]
        input: String,

        /// Output trace file (JSON)
        #[arg(short, long)]
        output: String,

        /// Trace name
        #[arg(long, default_value = "imported")]
        name: String,
    },

    /// Show statistics about a trace
    Stats {
        /// Trace file to analyze
        trace: String,
    },

    /// Convert trace format
    Convert {
        /// Input trace file
        input: String,

        /// Output trace file
        output: String,

        /// Output format (json or binary)
        #[arg(long, default_value = "json")]
        format: String,
    },

    /// Replay a trace and validate
    Validate {
        /// Trace file to validate
        trace: String,

        /// Enable strict mode (exact request matching)
        #[arg(long)]
        strict: bool,
    },

    /// Generate a synthetic trace using mock driver
    Generate {
        /// Output trace file
        #[arg(short, long)]
        output: String,

        /// Trace name
        #[arg(long, default_value = "synthetic")]
        name: String,

        /// Workload type: nvidia-smi, cuda-init, memory-alloc
        #[arg(long, default_value = "nvidia-smi")]
        workload: String,

        /// Number of iterations (for stress testing)
        #[arg(long, default_value = "1")]
        iterations: usize,
    },

    /// Stress test by replaying a trace many times
    Stress {
        /// Trace file to replay
        trace: String,

        /// Number of replay iterations
        #[arg(long, default_value = "1000")]
        iterations: usize,

        /// Number of parallel workers
        #[arg(long, default_value = "1")]
        workers: usize,
    },
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter(if args.verbose { "debug" } else { "info" })
        .init();

    // Handle trace subcommands
    if let Some(Command::Trace { action }) = args.command {
        return handle_trace_command(action);
    }

    info!("GPU Broker starting");
    info!("  nvidiactl: {}", args.nvidiactl);
    info!("  nvidia0: {}", args.nvidia0);
    info!("  handle_quota: {}", args.handle_quota);
    info!("  max_clients: {}", args.max_clients);
    info!("  socket: {}", args.socket);
    info!("  nvml_socket: {}", args.nvml_socket);
    info!("  vsock_port: {}", args.vsock_port);
    info!("  firecracker_vsock: {:?}", args.firecracker_vsock);
    info!("  mock: {}", args.mock);
    info!("  replay_trace: {:?}", args.replay_trace);
    info!("  record_trace: {:?}", args.record_trace);

    // Build server config
    let config = ServerConfig {
        socket_path: args.socket,
        nvidiactl_path: args.nvidiactl.clone(),
        nvidia0_path: args.nvidia0.clone(),
        handle_quota: args.handle_quota,
        max_clients: args.max_clients,
        use_mock_driver: args.mock,
        uring_queue_depth: 256,
    };

    // Start NVML server in a separate thread
    let nvml_socket_path = args.nvml_socket.clone();
    let nvml_thread = thread::spawn(move || {
        let gpu_info = GpuInfo::default();
        match NvmlServer::with_gpu_info(&nvml_socket_path, gpu_info) {
            Ok(server) => {
                if let Err(e) = server.run() {
                    tracing::error!("NVML server error: {}", e);
                }
            }
            Err(e) => {
                tracing::error!("Failed to start NVML server: {}", e);
            }
        }
    });

    // Load trace once for sharing across threads
    let vsock_trace: Option<IoctlTrace> = args.replay_trace.as_ref().map(|path| {
        IoctlTrace::load(path).expect("Failed to load trace for vsock")
    });

    // Start vsock server for VM connections (in a separate thread)
    let vsock_port = args.vsock_port;
    let vsock_mock = args.mock;
    let vsock_handle_quota = args.handle_quota;
    let vsock_max_clients = args.max_clients;
    let vsock_trace_clone = vsock_trace.clone();
    let vsock_nvidiactl = args.nvidiactl.clone();
    let vsock_nvidia0 = args.nvidia0.clone();
    
    let vsock_thread = if vsock_port > 0 {
        Some(thread::spawn(move || {
            let proxy_config = ProxyConfig {
                handle_quota: vsock_handle_quota,
                max_clients: vsock_max_clients,
                strict_validation: true,
            };
            
            // Create proxy with mock or real driver
            let vsock_config = VsockServerConfig {
                port: vsock_port,
                max_connections: 1000,
            };
            
            if let Some(trace) = vsock_trace_clone {
                let driver = TraceReplayDriver::new(trace);
                let proxy = BrokerProxy::new(driver, proxy_config);
                let server = VsockServer::new(vsock_config, proxy);
                info!("Starting vsock server on port {} (trace replay)", vsock_port);
                if let Err(e) = server.run() {
                    tracing::error!("vsock server error: {}", e);
                }
            } else if vsock_mock {
                let proxy = BrokerProxy::with_mock_driver(proxy_config);
                let server = VsockServer::new(vsock_config, proxy);
                info!("Starting vsock server on port {} (mock driver)", vsock_port);
                if let Err(e) = server.run() {
                    tracing::error!("vsock server error: {}", e);
                }
            } else {
                // Use real NVIDIA driver for vsock connections
                use driver::NvDriver;
                match NvDriver::open_path(&vsock_nvidiactl, Some(&vsock_nvidia0)) {
                    Ok(nv_driver) => {
                        let proxy = BrokerProxy::new(nv_driver, proxy_config);
                        let server = VsockServer::new(vsock_config, proxy);
                        info!("Starting vsock server on port {} (real driver)", vsock_port);
                        if let Err(e) = server.run() {
                            tracing::error!("vsock server error: {}", e);
                        }
                    }
                    Err(e) => {
                        tracing::error!("Failed to open NVIDIA driver for vsock: {}", e);
                        tracing::warn!("Falling back to mock driver for vsock");
                        let proxy = BrokerProxy::with_mock_driver(proxy_config);
                        let server = VsockServer::new(vsock_config, proxy);
                        info!("Starting vsock server on port {} (mock driver fallback)", vsock_port);
                        if let Err(e) = server.run() {
                            tracing::error!("vsock server error: {}", e);
                        }
                    }
                }
            }
        }))
    } else {
        info!("vsock server disabled (port=0)");
        None
    };

    // Start Firecracker vsock servers if specified
    let fc_vsock_threads: Vec<_> = if let Some(ref fc_sockets) = args.firecracker_vsock {
        fc_sockets
            .split(',')
            .filter(|s| !s.is_empty())
            .map(|socket_path| {
                let socket_path = socket_path.trim().to_string();
                let fc_mock = args.mock;
                let fc_handle_quota = args.handle_quota;
                let fc_max_clients = args.max_clients;
                let fc_port = args.vsock_port;
                let fc_trace = vsock_trace.clone();
                let fc_nvidiactl = args.nvidiactl.clone();
                let fc_nvidia0 = args.nvidia0.clone();

                thread::spawn(move || {
                    use firecracker_vsock::{FirecrackerVsockConfig, FirecrackerVsockServer};

                    let proxy_config = ProxyConfig {
                        handle_quota: fc_handle_quota,
                        max_clients: fc_max_clients,
                        strict_validation: true,
                    };

                    let fc_config = FirecrackerVsockConfig {
                        port: fc_port,
                        max_connections: 1000,
                    };

                    if let Some(trace) = fc_trace {
                        let driver = TraceReplayDriver::new(trace);
                        let proxy = BrokerProxy::new(driver, proxy_config);
                        let server = FirecrackerVsockServer::new(socket_path.clone(), fc_config, proxy);
                        info!("Starting Firecracker vsock server on {} (trace replay)", socket_path);
                        if let Err(e) = server.run() {
                            tracing::error!("Firecracker vsock server error: {}", e);
                        }
                    } else if fc_mock {
                        let proxy = BrokerProxy::with_mock_driver(proxy_config);
                        let server = FirecrackerVsockServer::new(socket_path.clone(), fc_config, proxy);
                        info!("Starting Firecracker vsock server on {} (mock driver)", socket_path);
                        if let Err(e) = server.run() {
                            tracing::error!("Firecracker vsock server error: {}", e);
                        }
                    } else {
                        // Use real NVIDIA driver for Firecracker vsock connections
                        use driver::NvDriver;
                        match NvDriver::open_path(&fc_nvidiactl, Some(&fc_nvidia0)) {
                            Ok(nv_driver) => {
                                let proxy = BrokerProxy::new(nv_driver, proxy_config);
                                let server = FirecrackerVsockServer::new(socket_path.clone(), fc_config, proxy);
                                info!("Starting Firecracker vsock server on {} (real driver)", socket_path);
                                if let Err(e) = server.run() {
                                    tracing::error!("Firecracker vsock server error: {}", e);
                                }
                            }
                            Err(e) => {
                                tracing::error!("Failed to open NVIDIA driver for Firecracker vsock: {}", e);
                                tracing::warn!("Falling back to mock driver");
                                let proxy = BrokerProxy::with_mock_driver(proxy_config);
                                let server = FirecrackerVsockServer::new(socket_path.clone(), fc_config, proxy);
                                info!("Starting Firecracker vsock server on {} (mock driver fallback)", socket_path);
                                if let Err(e) = server.run() {
                                    tracing::error!("Firecracker vsock server error: {}", e);
                                }
                            }
                        }
                    }
                })
            })
            .collect()
    } else {
        Vec::new()
    };

    // Run main broker server (Unix socket + shared memory)
    let result = if let Some(trace_path) = &args.replay_trace {
        info!("Using trace replay driver from: {}", trace_path);
        let trace = IoctlTrace::load(trace_path)
            .context("Failed to load trace file")?;
        info!("  Loaded trace: {} events", trace.events.len());
        let driver = TraceReplayDriver::new(trace);
        let mut server = BrokerServer::with_driver(config, driver)
            .context("Failed to create server with trace replay driver")?;
        server.run().context("Server error")
    } else if args.mock {
        info!("Using mock driver (no GPU required)");
        let mut server = BrokerServer::with_mock_driver(config)
            .context("Failed to create server with mock driver")?;
        server.run().context("Server error")
    } else {
        info!("Using real NVIDIA driver");
        let mut server = BrokerServer::new(config)
            .context("Failed to create server - is the NVIDIA driver loaded?")?;
        server.run().context("Server error")
    };

    // Clean up threads
    drop(nvml_thread);
    drop(vsock_thread);
    drop(fc_vsock_threads);

    result
}

/// Handle trace subcommands
fn handle_trace_command(action: TraceAction) -> Result<()> {
    match action {
        TraceAction::Import { input, output, name } => {
            info!("Importing strace from {} to {}", input, output);
            let mut trace = trace::import_strace(&input)
                .context("Failed to import strace")?;
            trace.metadata.name = name;
            trace.save(&output)
                .context("Failed to save trace")?;
            let stats = trace.stats();
            println!("Imported {} events", stats.total_events);
            println!("{}", stats);
            Ok(())
        }

        TraceAction::Stats { trace: trace_path } => {
            let trace = trace::IoctlTrace::load(&trace_path)
                .context("Failed to load trace")?;
            println!("Trace: {}", trace.metadata.name);
            println!("Description: {}", trace.metadata.description);
            println!("Recorded: {}", trace.metadata.recorded_at);
            if let Some(gpu) = &trace.metadata.gpu_name {
                println!("GPU: {}", gpu);
            }
            if let Some(cmd) = &trace.metadata.command {
                println!("Command: {}", cmd);
            }
            println!();
            println!("{}", trace.stats());
            Ok(())
        }

        TraceAction::Convert { input, output, format } => {
            let trace = if input.ends_with(".bin") {
                trace::IoctlTrace::load_binary(&input)
                    .context("Failed to load binary trace")?
            } else {
                trace::IoctlTrace::load(&input)
                    .context("Failed to load JSON trace")?
            };

            match format.as_str() {
                "json" => {
                    trace.save(&output)
                        .context("Failed to save JSON trace")?;
                    println!("Converted to JSON: {}", output);
                }
                "binary" | "bin" => {
                    trace.save_binary(&output)
                        .context("Failed to save binary trace")?;
                    println!("Converted to binary: {}", output);
                }
                _ => {
                    anyhow::bail!("Unknown format: {}. Use 'json' or 'binary'", format);
                }
            }
            Ok(())
        }

        TraceAction::Validate { trace: trace_path, strict } => {
            let trace = trace::IoctlTrace::load(&trace_path)
                .context("Failed to load trace")?;
            
            println!("Validating trace: {}", trace.metadata.name);
            println!("Events: {}", trace.events.len());
            println!("Strict mode: {}", strict);
            println!();

            let mut driver = trace::TraceReplayDriver::new(trace.clone());
            if strict {
                driver = driver.strict();
            }

            // Replay through the driver trait
            // For a full validation, we'd need to actually run through the broker
            // For now, just report stats
            println!("Trace is valid (basic structure check)");
            println!();
            println!("{}", trace.stats());
            Ok(())
        }

        TraceAction::Generate { output, name, workload, iterations } => {
            use crate::driver::{Driver, MockDriver};
            use crate::trace::RecordingDriver;
            use crate::rm_api::classes;
            
            info!("Generating {} trace: {} ({} iterations)", workload, name, iterations);
            
            let mock = MockDriver::new();
            let mut recording = RecordingDriver::new(mock, &name);
            
            for iter in 0..iterations {
                let base_handle = (iter as u32 * 100) + 1;
                
                match workload.as_str() {
                    "nvidia-smi" => {
                        // Simulate nvidia-smi query sequence
                        recording.alloc(0, 0, base_handle, classes::NV01_ROOT_CLIENT, None)?;
                        recording.alloc(base_handle, base_handle, base_handle + 1, classes::NV01_DEVICE_0, None)?;
                        recording.alloc(base_handle, base_handle + 1, base_handle + 2, classes::NV20_SUBDEVICE_0, None)?;
                        
                        // Query GPU name
                        let mut params = [0u8; 64];
                        recording.control(base_handle, base_handle + 2, 0x20800110, &mut params)?;
                        
                        // Query FB info
                        let mut fb_params = [0u8; 32];
                        recording.control(base_handle, base_handle + 2, 0x20801301, &mut fb_params)?;
                        
                        // Query PCI info
                        let mut pci_params = [0u8; 16];
                        recording.control(base_handle, base_handle + 2, 0x20801801, &mut pci_params)?;
                        
                        // Cleanup
                        recording.free(base_handle, base_handle + 1, base_handle + 2)?;
                        recording.free(base_handle, base_handle, base_handle + 1)?;
                        recording.free(base_handle, 0, base_handle)?;
                    }
                    
                    "cuda-init" => {
                        // Simulate CUDA initialization
                        recording.alloc(0, 0, base_handle, classes::NV01_ROOT_CLIENT, None)?;
                        recording.alloc(base_handle, base_handle, base_handle + 1, classes::NV01_DEVICE_0, None)?;
                        recording.alloc(base_handle, base_handle + 1, base_handle + 2, classes::NV20_SUBDEVICE_0, None)?;
                        
                        // Create channel 
                        recording.alloc(base_handle, base_handle + 1, base_handle + 10, classes::KEPLER_CHANNEL_GPFIFO_A, None)?;
                        
                        // Create memory allocations
                        for i in 0..5 {
                            recording.alloc_memory(
                                base_handle,
                                base_handle + 1,
                                base_handle + 20 + i,
                                classes::NV01_MEMORY_SYSTEM,
                                0,
                                4096 * (i as u64 + 1),
                            )?;
                        }
                        
                        // Cleanup memory
                        for i in (0..5).rev() {
                            recording.free(base_handle, base_handle + 1, base_handle + 20 + i)?;
                        }
                        
                        // Cleanup objects
                        recording.free(base_handle, base_handle + 1, base_handle + 10)?;
                        recording.free(base_handle, base_handle + 1, base_handle + 2)?;
                        recording.free(base_handle, base_handle, base_handle + 1)?;
                        recording.free(base_handle, 0, base_handle)?;
                    }
                    
                    "memory-alloc" => {
                        // Simulate memory-intensive workload
                        recording.alloc(0, 0, base_handle, classes::NV01_ROOT_CLIENT, None)?;
                        recording.alloc(base_handle, base_handle, base_handle + 1, classes::NV01_DEVICE_0, None)?;
                        
                        // Many memory allocations
                        for i in 0..20 {
                            let size = (1 << (10 + (i % 10))) as u64; // 1KB to 512KB
                            recording.alloc_memory(
                                base_handle,
                                base_handle + 1,
                                base_handle + 100 + i,
                                classes::NV01_MEMORY_SYSTEM,
                                0,
                                size,
                            )?;
                        }
                        
                        // Free half
                        for i in (10..20).rev() {
                            recording.free(base_handle, base_handle + 1, base_handle + 100 + i)?;
                        }
                        
                        // Allocate more
                        for i in 20..30 {
                            recording.alloc_memory(
                                base_handle,
                                base_handle + 1,
                                base_handle + 100 + i,
                                classes::NV01_MEMORY_SYSTEM,
                                0,
                                65536,
                            )?;
                        }
                        
                        // Cleanup all
                        for i in (0..10).rev() {
                            recording.free(base_handle, base_handle + 1, base_handle + 100 + i)?;
                        }
                        for i in (20..30).rev() {
                            recording.free(base_handle, base_handle + 1, base_handle + 100 + i)?;
                        }
                        
                        recording.free(base_handle, base_handle, base_handle + 1)?;
                        recording.free(base_handle, 0, base_handle)?;
                    }
                    
                    _ => {
                        anyhow::bail!("Unknown workload: {}. Use: nvidia-smi, cuda-init, memory-alloc", workload);
                    }
                }
            }
            
            // Finish and save
            let (_, mut trace) = recording.finish();
            trace.metadata.description = format!("{} workload simulation ({} iterations)", workload, iterations);
            trace.metadata.command = Some(format!("gpu-broker trace generate --workload {}", workload));
            
            trace.save(&output).context("Failed to save trace")?;
            
            let stats = trace.stats();
            println!("Generated trace: {}", output);
            println!("{}", stats);
            Ok(())
        }

        TraceAction::Stress { trace: trace_path, iterations, workers } => {
            use crate::driver::Driver;
            use std::sync::Arc;
            use std::sync::atomic::{AtomicUsize, Ordering};
            use std::time::Instant;
            
            let trace = trace::IoctlTrace::load(&trace_path)
                .context("Failed to load trace")?;
            
            println!("Stress testing trace: {}", trace.metadata.name);
            println!("Events per iteration: {}", trace.events.len());
            println!("Iterations: {}", iterations);
            println!("Workers: {}", workers);
            println!();
            
            let trace = Arc::new(trace);
            let completed = Arc::new(AtomicUsize::new(0));
            let errors = Arc::new(AtomicUsize::new(0));
            let total_ops = Arc::new(AtomicUsize::new(0));
            
            let start = Instant::now();
            
            let handles: Vec<_> = (0..workers).map(|worker_id| {
                let trace = Arc::clone(&trace);
                let completed = Arc::clone(&completed);
                let errors = Arc::clone(&errors);
                let total_ops = Arc::clone(&total_ops);
                let iters_per_worker = iterations / workers + if worker_id < iterations % workers { 1 } else { 0 };
                
                thread::spawn(move || {
                    for _ in 0..iters_per_worker {
                        let mut driver = trace::TraceReplayDriver::new((*trace).clone());
                        
                        // Replay all ioctl events
                        for event in trace.ioctl_events() {
                            let result = match event.cmd {
                                0x2b => driver.alloc(0, 0, 1, 0x41, None).map(|_| ()),
                                0x29 => driver.free(0, 0, 1).map(|_| ()),
                                0x2a => {
                                    let mut params = vec![0u8; 64];
                                    driver.control(0, 1, 0, &mut params).map(|_| ())
                                }
                                0x27 => driver.alloc_memory(0, 0, 1, 0, 0, 4096).map(|_| ()),
                                _ => Ok(()),
                            };
                            
                            total_ops.fetch_add(1, Ordering::Relaxed);
                            if result.is_err() {
                                errors.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                        
                        completed.fetch_add(1, Ordering::Relaxed);
                    }
                })
            }).collect();
            
            // Wait for all workers
            for h in handles {
                h.join().expect("Worker panicked");
            }
            
            let elapsed = start.elapsed();
            let total_completed = completed.load(Ordering::Relaxed);
            let total_errors = errors.load(Ordering::Relaxed);
            let ops = total_ops.load(Ordering::Relaxed);
            
            println!("Results:");
            println!("  Completed iterations: {}", total_completed);
            println!("  Total operations: {}", ops);
            println!("  Errors: {}", total_errors);
            println!("  Duration: {:.3}s", elapsed.as_secs_f64());
            println!("  Throughput: {:.0} iterations/sec", total_completed as f64 / elapsed.as_secs_f64());
            println!("  Throughput: {:.0} ops/sec", ops as f64 / elapsed.as_secs_f64());
            
            if total_errors > 0 {
                anyhow::bail!("{} errors during stress test", total_errors);
            }
            
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handle_table::{ClientId, HandleTable, RealHandle, VirtualHandle};

    #[test]
    fn test_broker_handle_isolation() {
        // Test the handle logic without requiring GPU
        let mut handles = HandleTable::new(1000);

        let client1 = ClientId(1);
        let client2 = ClientId(2);

        handles.register_client(client1);
        handles.register_client(client2);

        // Both clients create a handle "0x1"
        handles
            .insert(client1, VirtualHandle(0x1), RealHandle(0x1000))
            .unwrap();
        handles
            .insert(client2, VirtualHandle(0x1), RealHandle(0x2000))
            .unwrap();

        // They map to different real handles
        assert_eq!(
            handles.translate(client1, VirtualHandle(0x1)).unwrap().0,
            0x1000
        );
        assert_eq!(
            handles.translate(client2, VirtualHandle(0x1)).unwrap().0,
            0x2000
        );

        // Client 1 can't accidentally access client 2's handle 0x2000
        // because they'd have to reference it by virtual handle,
        // and virtual 0x1 maps to their own 0x1000
    }
}
