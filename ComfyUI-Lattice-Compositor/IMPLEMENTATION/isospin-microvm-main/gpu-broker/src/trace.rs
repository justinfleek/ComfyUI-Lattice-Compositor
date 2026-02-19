//! Ioctl Trace Recorder and Replayer
//!
//! This module provides tools for recording and replaying NVIDIA driver ioctls.
//! Key use cases:
//! - Record real ioctl sequences from actual GPU workloads
//! - Replay traces for deterministic testing without hardware
//! - Import traces from strace output
//! - Build a corpus of traces for different workloads
//!
//! ## Trace Format
//!
//! Traces are sequences of `IoctlEvent`s, each containing:
//! - Timestamp (nanoseconds since trace start)
//! - Device path (/dev/nvidiactl, /dev/nvidia0, /dev/nvidia-uvm)
//! - Ioctl command number
//! - Request data (bytes sent to driver)
//! - Response data (bytes returned from driver)
//! - Return value (0 for success, errno for failure)
//!
//! ## Example Usage
//!
//! ```ignore
//! // Recording
//! let mut recorder = TraceRecorder::new();
//! recorder.record_ioctl("/dev/nvidiactl", 0x2b, &request, &response, 0);
//! recorder.save("nvidia-smi.trace")?;
//!
//! // Replaying  
//! let trace = IoctlTrace::load("nvidia-smi.trace")?;
//! let driver = TraceReplayDriver::new(trace);
//! // driver implements Driver trait, returns recorded responses
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Read, Write};
use std::path::Path;
use std::time::{Duration, Instant};

// =============================================================================
// TRACE DATA STRUCTURES
// =============================================================================

/// A trace event (ioctl, mmap, open, close, etc.)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum TraceEvent {
    /// An ioctl call
    Ioctl(IoctlEvent),
    
    /// A memory mapping
    Mmap(MmapEvent),
    
    /// A memory unmapping
    Munmap(MunmapEvent),
    
    /// Opening an NVIDIA device
    Open(OpenEvent),
    
    /// Closing an NVIDIA device
    Close(CloseEvent),
}

/// A single ioctl event in the trace
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct IoctlEvent {
    /// Monotonic timestamp in nanoseconds since trace start
    pub timestamp_ns: u64,

    /// Device path (e.g., "/dev/nvidiactl", "/dev/nvidia0")
    pub device: String,

    /// Ioctl command number (the escape code, e.g., 0x2b for RM_ALLOC)
    pub cmd: u32,

    /// Full ioctl request number (includes magic, direction, size)
    pub ioctl_nr: u64,

    /// Request data sent to driver (before ioctl)
    /// In JSON format, this is hex-encoded for readability; in binary it's raw bytes
    pub request: Vec<u8>,

    /// Response data from driver (after ioctl, may be same buffer modified)
    /// In JSON format, this is hex-encoded for readability; in binary it's raw bytes
    pub response: Vec<u8>,

    /// Return value (0 = success, negative = -errno)
    pub ret: i32,

    /// Optional: Decoded operation name for readability
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub op_name: Option<String>,
}

/// Memory mapping event
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MmapEvent {
    pub timestamp_ns: u64,
    pub device: String,
    pub addr: u64,
    pub length: u64,
    pub prot: u32,
    pub flags: u32,
    pub fd: i32,
    pub offset: i64,
    #[serde(default)]
    pub has_redzone: bool,
}

/// Memory unmapping event
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct MunmapEvent {
    pub timestamp_ns: u64,
    pub addr: u64,
    pub length: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub device: Option<String>,
}

/// Device open event
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OpenEvent {
    pub timestamp_ns: u64,
    pub device: String,
    pub fd: i32,
}

/// Device close event
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CloseEvent {
    pub timestamp_ns: u64,
    pub device: String,
    pub fd: i32,
}

/// A complete trace of events
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IoctlTrace {
    /// Trace metadata
    pub metadata: TraceMetadata,

    /// Ordered list of events (can be ioctl, mmap, open, close, etc.)
    pub events: Vec<TraceEvent>,
}

/// Metadata about the trace
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceMetadata {
    /// Human-readable name for this trace
    pub name: String,

    /// Description of what workload was traced
    pub description: String,

    /// When the trace was recorded (ISO 8601)
    pub recorded_at: String,

    /// Total duration of the trace in nanoseconds
    pub duration_ns: u64,

    /// GPU that was used (if known)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub gpu_name: Option<String>,

    /// Driver version (if known)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub driver_version: Option<String>,

    /// Command that was traced (e.g., "nvidia-smi -L")
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command: Option<String>,
}

impl Default for TraceMetadata {
    fn default() -> Self {
        Self {
            name: "unnamed".to_string(),
            description: String::new(),
            recorded_at: chrono::Utc::now().to_rfc3339(),
            duration_ns: 0,
            gpu_name: None,
            driver_version: None,
            command: None,
        }
    }
}

impl IoctlTrace {
    /// Create a new empty trace
    pub fn new(name: &str) -> Self {
        Self {
            metadata: TraceMetadata {
                name: name.to_string(),
                ..Default::default()
            },
            events: Vec::new(),
        }
    }

    /// Load a trace from a file (JSON format)
    pub fn load<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        serde_json::from_reader(reader)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }

    /// Save the trace to a file (JSON format)
    pub fn save<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let file = File::create(path)?;
        let writer = BufWriter::new(file);
        serde_json::to_writer_pretty(writer, self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
    }

    /// Load a trace from binary format (compact, uses JSON internally for robustness)
    pub fn load_binary<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        // For maximum compatibility, use gzipped JSON instead of bincode
        // This avoids serialization bugs while still being compact
        use std::io::Read;
        use flate2::read::GzDecoder;
        
        let file = File::open(path)?;
        let mut decoder = GzDecoder::new(file);
        let mut json_data = String::new();
        decoder.read_to_string(&mut json_data)?;
        
        serde_json::from_str(&json_data)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("json error: {}", e)))
    }

    /// Save the trace in binary format (compact, uses gzipped JSON internally)
    pub fn save_binary<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        use std::io::Write;
        use flate2::write::GzEncoder;
        use flate2::Compression;
        
        let file = File::create(path)?;
        let mut encoder = GzEncoder::new(file, Compression::default());
        
        let json_data = serde_json::to_string(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("json error: {}", e)))?;
        encoder.write_all(json_data.as_bytes())?;
        encoder.finish()?;
        Ok(())
    }

    /// Get statistics about the trace
    pub fn stats(&self) -> TraceStats {
        let mut cmd_counts: HashMap<u32, usize> = HashMap::new();
        let mut device_counts: HashMap<String, usize> = HashMap::new();
        let mut total_request_bytes = 0;
        let mut total_response_bytes = 0;
        let mut mmap_count = 0;
        let mut munmap_count = 0;
        let mut open_count = 0;
        let mut close_count = 0;

        for event in &self.events {
            match event {
                TraceEvent::Ioctl(e) => {
                    *cmd_counts.entry(e.cmd).or_default() += 1;
                    *device_counts.entry(e.device.clone()).or_default() += 1;
                    total_request_bytes += e.request.len();
                    total_response_bytes += e.response.len();
                }
                TraceEvent::Mmap(e) => {
                    mmap_count += 1;
                    *device_counts.entry(e.device.clone()).or_default() += 1;
                }
                TraceEvent::Munmap(_) => {
                    munmap_count += 1;
                }
                TraceEvent::Open(e) => {
                    open_count += 1;
                    *device_counts.entry(e.device.clone()).or_default() += 1;
                }
                TraceEvent::Close(e) => {
                    close_count += 1;
                    *device_counts.entry(e.device.clone()).or_default() += 1;
                }
            }
        }

        TraceStats {
            total_events: self.events.len(),
            duration_ns: self.metadata.duration_ns,
            cmd_counts,
            device_counts,
            total_request_bytes,
            total_response_bytes,
            mmap_count,
            munmap_count,
            open_count,
            close_count,
        }
    }
    
    /// Get only the ioctl events (for backward compatibility)
    pub fn ioctl_events(&self) -> impl Iterator<Item = &IoctlEvent> {
        self.events.iter().filter_map(|e| match e {
            TraceEvent::Ioctl(ioctl) => Some(ioctl),
            _ => None,
        })
    }
}

/// Statistics about a trace
#[derive(Debug, Clone)]
pub struct TraceStats {
    pub total_events: usize,
    pub duration_ns: u64,
    pub cmd_counts: HashMap<u32, usize>,
    pub device_counts: HashMap<String, usize>,
    pub total_request_bytes: usize,
    pub total_response_bytes: usize,
    pub mmap_count: usize,
    pub munmap_count: usize,
    pub open_count: usize,
    pub close_count: usize,
}

impl std::fmt::Display for TraceStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Trace Statistics:")?;
        writeln!(f, "  Total events: {}", self.total_events)?;
        writeln!(
            f,
            "  Duration: {:.3}ms",
            self.duration_ns as f64 / 1_000_000.0
        )?;
        writeln!(f, "  Ioctl data: {} bytes request, {} bytes response", 
                 self.total_request_bytes, self.total_response_bytes)?;
        writeln!(f, "  Event types:")?;
        writeln!(f, "    ioctls: {}", self.cmd_counts.values().sum::<usize>())?;
        writeln!(f, "    mmap: {}", self.mmap_count)?;
        writeln!(f, "    munmap: {}", self.munmap_count)?;
        writeln!(f, "    open: {}", self.open_count)?;
        writeln!(f, "    close: {}", self.close_count)?;
        writeln!(f, "  Ioctl commands:")?;
        let mut cmds: Vec<_> = self.cmd_counts.iter().collect();
        cmds.sort_by_key(|(cmd, _)| *cmd);
        for (cmd, count) in cmds {
            let name = decode_op_name(*cmd);
            if let Some(n) = name {
                writeln!(f, "    0x{:02x} ({}): {} calls", cmd, n, count)?;
            } else {
                writeln!(f, "    0x{:02x}: {} calls", cmd, count)?;
            }
        }
        writeln!(f, "  Devices:")?;
        for (device, count) in &self.device_counts {
            writeln!(f, "    {}: {} events", device, count)?;
        }
        Ok(())
    }
}

// =============================================================================
// TRACE RECORDER
// =============================================================================

/// Records ioctls as they happen
pub struct TraceRecorder {
    trace: IoctlTrace,
    start_time: Instant,
}

impl TraceRecorder {
    /// Create a new trace recorder
    pub fn new(name: &str) -> Self {
        Self {
            trace: IoctlTrace::new(name),
            start_time: Instant::now(),
        }
    }

    /// Set trace metadata
    pub fn set_metadata(&mut self, metadata: TraceMetadata) {
        self.trace.metadata = metadata;
    }

    /// Record an ioctl event
    pub fn record(
        &mut self,
        device: &str,
        cmd: u32,
        ioctl_nr: u64,
        request: &[u8],
        response: &[u8],
        ret: i32,
    ) {
        let timestamp_ns = self.start_time.elapsed().as_nanos() as u64;

        self.trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns,
            device: device.to_string(),
            cmd,
            ioctl_nr,
            request: request.to_vec(),
            response: response.to_vec(),
            ret,
            op_name: decode_op_name(cmd),
        }));
    }
    
    /// Record an mmap event
    pub fn record_mmap(
        &mut self,
        device: &str,
        addr: u64,
        length: u64,
        prot: u32,
        flags: u32,
        fd: i32,
        offset: i64,
        has_redzone: bool,
    ) {
        let timestamp_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace.events.push(TraceEvent::Mmap(MmapEvent {
            timestamp_ns,
            device: device.to_string(),
            addr,
            length,
            prot,
            flags,
            fd,
            offset,
            has_redzone,
        }));
    }
    
    /// Record a munmap event
    pub fn record_munmap(&mut self, addr: u64, length: u64, device: Option<&str>) {
        let timestamp_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace.events.push(TraceEvent::Munmap(MunmapEvent {
            timestamp_ns,
            addr,
            length,
            device: device.map(|s| s.to_string()),
        }));
    }
    
    /// Record an open event
    pub fn record_open(&mut self, device: &str, fd: i32) {
        let timestamp_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace.events.push(TraceEvent::Open(OpenEvent {
            timestamp_ns,
            device: device.to_string(),
            fd,
        }));
    }
    
    /// Record a close event
    pub fn record_close(&mut self, device: &str, fd: i32) {
        let timestamp_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace.events.push(TraceEvent::Close(CloseEvent {
            timestamp_ns,
            device: device.to_string(),
            fd,
        }));
    }

    /// Finish recording and get the trace
    pub fn finish(mut self) -> IoctlTrace {
        self.trace.metadata.duration_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace
    }

    /// Save the trace to a file
    pub fn save<P: AsRef<Path>>(&mut self, path: P) -> io::Result<()> {
        self.trace.metadata.duration_ns = self.start_time.elapsed().as_nanos() as u64;
        self.trace.save(path)
    }
}

/// Decode ioctl command to human-readable name
fn decode_op_name(cmd: u32) -> Option<String> {
    match cmd {
        0x29 => Some("RM_FREE".to_string()),
        0x2a => Some("RM_CONTROL".to_string()),
        0x2b => Some("RM_ALLOC".to_string()),
        0x27 => Some("RM_ALLOC_MEMORY".to_string()),
        0x4e => Some("RM_MAP_MEMORY".to_string()),
        0x4f => Some("RM_UNMAP_MEMORY".to_string()),
        0x34 => Some("RM_DUP_OBJECT".to_string()),
        0x35 => Some("RM_SHARE".to_string()),
        0xc8 => Some("CARD_INFO".to_string()),
        0xc9 => Some("ATTACH_GPUS_TO_FD".to_string()),
        0xd2 => Some("CHECK_VERSION".to_string()),
        0xd6 => Some("SYS_PARAMS".to_string()),
        0xd7 => Some("GET_PCI_INFO".to_string()),
        0xda => Some("EXPORT_DEVICE_FD".to_string()),
        _ => None,
    }
}

// =============================================================================
// TRACE REPLAY DRIVER
// =============================================================================

use crate::driver::{Driver, DriverError, DriverResult};
use crate::rm_api::{NvCardInfo, NvHandle, NvRmApiVersion};

/// A driver that replays recorded traces
///
/// When an ioctl is called, it finds a matching event in the trace
/// and returns the recorded response.
pub struct TraceReplayDriver {
    trace: IoctlTrace,
    /// Current position in the trace
    position: usize,
    /// Whether to require exact request matching
    strict_mode: bool,
    /// Index by (device, cmd) for fast lookup
    index: HashMap<(String, u32), Vec<usize>>,
    /// Next index to use for each (device, cmd) pair
    next_index: HashMap<(String, u32), usize>,
    /// Statistics about replay
    pub stats: ReplayStats,
}

/// Statistics about trace replay
#[derive(Debug, Clone, Default)]
pub struct ReplayStats {
    /// Total ioctls replayed
    pub total_replayed: usize,
    /// Exact matches (request bytes matched)
    pub exact_matches: usize,
    /// Fuzzy matches (cmd matched but request differed)
    pub fuzzy_matches: usize,
    /// Misses (no matching event found)
    pub misses: usize,
}

impl TraceReplayDriver {
    /// Create a new replay driver from a trace
    pub fn new(trace: IoctlTrace) -> Self {
        let mut index: HashMap<(String, u32), Vec<usize>> = HashMap::new();

        // Build index (only for ioctl events)
        for (i, event) in trace.events.iter().enumerate() {
            if let TraceEvent::Ioctl(ioctl) = event {
                let key = (ioctl.device.clone(), ioctl.cmd);
                index.entry(key).or_default().push(i);
            }
        }

        Self {
            trace,
            position: 0,
            strict_mode: false,
            index,
            next_index: HashMap::new(),
            stats: ReplayStats::default(),
        }
    }

    /// Enable strict mode (require exact request matching)
    pub fn strict(mut self) -> Self {
        self.strict_mode = true;
        self
    }

    /// Reset replay to the beginning
    pub fn reset(&mut self) {
        self.position = 0;
        self.next_index.clear();
        self.stats = ReplayStats::default();
    }

    /// Find the next matching event for a given device and command
    fn find_event(&mut self, device: &str, cmd: u32, request: &[u8]) -> Option<&IoctlEvent> {
        let key = (device.to_string(), cmd);

        // Get the list of events for this (device, cmd)
        let indices = self.index.get(&key)?;

        // Get current position in this list
        let pos = self.next_index.entry(key.clone()).or_insert(0);

        if *pos >= indices.len() {
            // No more events for this command
            return None;
        }

        let event_idx = indices[*pos];
        
        // Get the ioctl event from the trace
        let event = match &self.trace.events[event_idx] {
            TraceEvent::Ioctl(e) => e,
            _ => return None, // Should not happen due to how we build the index
        };

        // In strict mode, verify request matches
        if self.strict_mode && event.request != request {
            return None;
        }

        // Advance position
        *pos += 1;
        self.position = event_idx + 1;

        // Update stats
        self.stats.total_replayed += 1;
        if event.request == request {
            self.stats.exact_matches += 1;
        } else {
            self.stats.fuzzy_matches += 1;
        }

        Some(event)
    }

    /// Get the underlying trace
    pub fn trace(&self) -> &IoctlTrace {
        &self.trace
    }
}

impl Driver for TraceReplayDriver {
    fn alloc(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_object: NvHandle,
        h_class: u32,
        params: Option<&[u8]>,
    ) -> DriverResult<u32> {
        // Build request bytes (simplified - real impl would use actual struct layout)
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());
        request.extend_from_slice(&h_class.to_le_bytes());
        if let Some(p) = params {
            request.extend_from_slice(p);
        }

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x2b, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            // Extract status from response (last 4 bytes typically)
            if event.response.len() >= 4 {
                let status = u32::from_le_bytes(
                    event.response[event.response.len() - 4..].try_into().unwrap(),
                );
                return Ok(status);
            }
            Ok(0)
        } else {
            self.stats.misses += 1;
            // Return success by default for non-strict mode
            Ok(0)
        }
    }

    fn free(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_object: NvHandle,
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x29, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            Ok(0)
        } else {
            self.stats.misses += 1;
            Ok(0)
        }
    }

    fn control(
        &mut self,
        h_client: NvHandle,
        h_object: NvHandle,
        cmd: u32,
        params: &mut [u8],
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());
        request.extend_from_slice(&cmd.to_le_bytes());
        request.extend_from_slice(params);

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x2a, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            // Copy response params back
            let param_offset = 12; // Skip h_client, h_object, cmd
            if event.response.len() > param_offset {
                let response_params = &event.response[param_offset..];
                let copy_len = response_params.len().min(params.len());
                params[..copy_len].copy_from_slice(&response_params[..copy_len]);
            }
            Ok(0)
        } else {
            self.stats.misses += 1;
            Ok(0)
        }
    }

    fn alloc_memory(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_memory: NvHandle,
        h_class: u32,
        flags: u32,
        size: u64,
    ) -> DriverResult<(u64, u32)> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&h_class.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());
        request.extend_from_slice(&size.to_le_bytes());

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x27, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            // Extract address and status from response
            if event.response.len() >= 16 {
                let addr = u64::from_le_bytes(event.response[0..8].try_into().unwrap());
                let status = u32::from_le_bytes(event.response[8..12].try_into().unwrap());
                return Ok((addr, status));
            }
            Ok((0x1000_0000_0000, 0))
        } else {
            self.stats.misses += 1;
            Ok((0x1000_0000_0000, 0))
        }
    }

    fn map_memory(
        &mut self,
        h_client: NvHandle,
        h_device: NvHandle,
        h_memory: NvHandle,
        offset: u64,
        length: u64,
        flags: u32,
    ) -> DriverResult<(u64, u32)> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_device.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&offset.to_le_bytes());
        request.extend_from_slice(&length.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x4e, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            if event.response.len() >= 12 {
                let addr = u64::from_le_bytes(event.response[0..8].try_into().unwrap());
                let status = u32::from_le_bytes(event.response[8..12].try_into().unwrap());
                return Ok((addr, status));
            }
            Ok((0x1000_0000_0000, 0))
        } else {
            self.stats.misses += 1;
            Ok((0x1000_0000_0000, 0))
        }
    }

    fn unmap_memory(
        &mut self,
        h_client: NvHandle,
        h_device: NvHandle,
        h_memory: NvHandle,
        address: u64,
        flags: u32,
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_device.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&address.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());

        if let Some(event) = self.find_event("/dev/nvidiactl", 0x4f, &request) {
            if event.ret != 0 {
                return Err(DriverError::IoError(event.ret));
            }
            Ok(0)
        } else {
            self.stats.misses += 1;
            Ok(0)
        }
    }

    fn card_info(&self, cards: &mut [NvCardInfo]) -> DriverResult<usize> {
        // For card_info, we look for a CARD_INFO event in the trace
        // This is a const method so we can't update position, just scan
        for event in &self.trace.events {
            if let TraceEvent::Ioctl(ioctl) = event {
                if ioctl.device == "/dev/nvidiactl" && ioctl.cmd == 0xc8 {
                    // Found a card_info event
                    // The response contains an array of NvCardInfo structs
                    let card_size = std::mem::size_of::<NvCardInfo>();
                    let num_cards = ioctl.response.len() / card_size;
                    let copy_count = num_cards.min(cards.len());

                    for i in 0..copy_count {
                        let offset = i * card_size;
                        if offset + card_size <= ioctl.response.len() {
                            // Safety: NvCardInfo is a plain data struct
                            unsafe {
                                std::ptr::copy_nonoverlapping(
                                    ioctl.response[offset..].as_ptr(),
                                    &mut cards[i] as *mut NvCardInfo as *mut u8,
                                    card_size,
                                );
                            }
                        }
                    }
                    return Ok(copy_count);
                }
            }
        }

        // No card info in trace, return 0 cards
        Ok(0)
    }

    fn check_version(&self, version: &mut NvRmApiVersion) -> DriverResult<()> {
        // Look for a CHECK_VERSION event
        for event in &self.trace.events {
            if let TraceEvent::Ioctl(ioctl) = event {
                if ioctl.device == "/dev/nvidiactl" && ioctl.cmd == 0xd2 {
                    // Copy response into version struct
                    let ver_size = std::mem::size_of::<NvRmApiVersion>();
                    if ioctl.response.len() >= ver_size {
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                ioctl.response.as_ptr(),
                                version as *mut NvRmApiVersion as *mut u8,
                                ver_size,
                            );
                        }
                    }
                    return Ok(());
                }
            }
        }

        // Default: return success with standard version
        version.reply = 1; // NV_RM_API_VERSION_REPLY_RECOGNIZED
        Ok(())
    }

    fn is_real(&self) -> bool {
        false
    }
}

// =============================================================================
// STRACE IMPORT
// =============================================================================

/// Import a trace from strace output
///
/// Parses strace output like:
/// ```text
/// ioctl(3, _IOC(_IOC_READ|_IOC_WRITE, 0x46, 0x2b, 0x20), 0x7ffe...) = 0
/// ```
pub fn import_strace<P: AsRef<Path>>(path: P) -> io::Result<IoctlTrace> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    let mut trace = IoctlTrace::new("strace-import");
    trace.metadata.description = "Imported from strace output".to_string();

    // Regex patterns for parsing strace output
    // Format: ioctl(fd, cmd, addr) = ret
    let ioctl_pattern =
        regex::Regex::new(r"ioctl\((\d+),\s*(?:_IOC\([^)]+\)|0x[0-9a-fA-F]+),\s*0x([0-9a-fA-F]+)")
            .unwrap();

    // Track fd -> device mapping
    let mut fd_device: HashMap<i32, String> = HashMap::new();

    // Look for open() calls to map fds to devices
    let open_pattern =
        regex::Regex::new(r#"openat?\([^,]*,\s*"(/dev/nvidia[^"]*)"[^)]*\)\s*=\s*(\d+)"#).unwrap();

    let mut timestamp_ns: u64 = 0;
    let timestamp_step: u64 = 1_000_000; // 1ms between events (approximation)

    for line in reader.lines() {
        let line = line?;

        // Check for open() to track fd -> device
        if let Some(caps) = open_pattern.captures(&line) {
            let device = caps.get(1).unwrap().as_str().to_string();
            let fd: i32 = caps.get(2).unwrap().as_str().parse().unwrap_or(-1);
            if fd >= 0 {
                fd_device.insert(fd, device);
            }
            continue;
        }

        // Check for ioctl
        if let Some(caps) = ioctl_pattern.captures(&line) {
            let fd: i32 = caps.get(1).unwrap().as_str().parse().unwrap_or(-1);

            // Try to determine the device
            let device = fd_device
                .get(&fd)
                .cloned()
                .unwrap_or_else(|| "/dev/nvidiactl".to_string());

            // Extract ioctl command - look for the escape code
            let cmd = extract_ioctl_cmd(&line);

            // Parse return value
            let ret = if line.contains("= 0") {
                0
            } else if line.contains("= -1") {
                -1
            } else {
                0
            };

            // We don't have the actual data from strace easily
            // For a real implementation, we'd use strace -e read=... or similar
            trace.events.push(TraceEvent::Ioctl(IoctlEvent {
                timestamp_ns,
                device,
                cmd,
                ioctl_nr: 0, // Would need to parse from strace
                request: Vec::new(),
                response: Vec::new(),
                ret,
                op_name: decode_op_name(cmd),
            }));

            timestamp_ns += timestamp_step;
        }
    }

    trace.metadata.duration_ns = timestamp_ns;
    Ok(trace)
}

/// Extract ioctl command (escape code) from strace line
fn extract_ioctl_cmd(line: &str) -> u32 {
    // Look for patterns like:
    // _IOC(_IOC_READ|_IOC_WRITE, 0x46, 0x2b, 0x20)
    // or just hex numbers like 0xc0204629

    // Try to find escape code in _IOC format
    let ioc_pattern = regex::Regex::new(r"_IOC\([^,]+,\s*0x46,\s*0x([0-9a-fA-F]+)").unwrap();
    if let Some(caps) = ioc_pattern.captures(line) {
        if let Ok(cmd) = u32::from_str_radix(caps.get(1).unwrap().as_str(), 16) {
            return cmd;
        }
    }

    // Try to extract from raw ioctl number
    // NVIDIA ioctls use magic 'F' (0x46) and escape code in bits 0-7
    let raw_pattern = regex::Regex::new(r"0x([0-9a-fA-F]{8})").unwrap();
    if let Some(caps) = raw_pattern.captures(line) {
        if let Ok(raw) = u64::from_str_radix(caps.get(1).unwrap().as_str(), 16) {
            // Extract escape code (bits 0-7 of the ioctl number)
            return (raw & 0xFF) as u32;
        }
    }

    0 // Unknown
}

// =============================================================================
// RECORDING WRAPPER
// =============================================================================

use crate::driver::NvDriver;

/// A driver wrapper that records all ioctls to a trace
pub struct RecordingDriver<D: Driver> {
    inner: D,
    recorder: TraceRecorder,
}

impl<D: Driver> RecordingDriver<D> {
    /// Create a new recording driver wrapping an inner driver
    pub fn new(inner: D, trace_name: &str) -> Self {
        Self {
            inner,
            recorder: TraceRecorder::new(trace_name),
        }
    }

    /// Get the recorded trace
    pub fn finish(self) -> (D, IoctlTrace) {
        (self.inner, self.recorder.finish())
    }

    /// Save the trace so far
    pub fn save<P: AsRef<Path>>(&mut self, path: P) -> io::Result<()> {
        self.recorder.save(path)
    }
}

impl<D: Driver> Driver for RecordingDriver<D> {
    fn alloc(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_object: NvHandle,
        h_class: u32,
        params: Option<&[u8]>,
    ) -> DriverResult<u32> {
        // Build request for recording
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());
        request.extend_from_slice(&h_class.to_le_bytes());
        if let Some(p) = params {
            request.extend_from_slice(p);
        }

        // Call inner driver
        let result = self.inner.alloc(h_root, h_parent, h_object, h_class, params);

        // Record the event
        let (response, ret) = match &result {
            Ok(status) => {
                let mut resp = request.clone();
                resp.extend_from_slice(&status.to_le_bytes());
                (resp, 0)
            }
            Err(DriverError::IoError(e)) => (request.clone(), *e),
            Err(_) => (request.clone(), -1),
        };

        self.recorder
            .record("/dev/nvidiactl", 0x2b, 0, &request, &response, ret);

        result
    }

    fn free(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_object: NvHandle,
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());

        let result = self.inner.free(h_root, h_parent, h_object);

        let (response, ret) = match &result {
            Ok(status) => {
                let mut resp = request.clone();
                resp.extend_from_slice(&status.to_le_bytes());
                (resp, 0)
            }
            Err(DriverError::IoError(e)) => (request.clone(), *e),
            Err(_) => (request.clone(), -1),
        };

        self.recorder
            .record("/dev/nvidiactl", 0x29, 0, &request, &response, ret);

        result
    }

    fn control(
        &mut self,
        h_client: NvHandle,
        h_object: NvHandle,
        cmd: u32,
        params: &mut [u8],
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_object.to_le_bytes());
        request.extend_from_slice(&cmd.to_le_bytes());
        request.extend_from_slice(params);

        let result = self.inner.control(h_client, h_object, cmd, params);

        let mut response = Vec::new();
        response.extend_from_slice(&h_client.to_le_bytes());
        response.extend_from_slice(&h_object.to_le_bytes());
        response.extend_from_slice(&cmd.to_le_bytes());
        response.extend_from_slice(params); // params may have been modified

        let ret = match &result {
            Ok(_) => 0,
            Err(DriverError::IoError(e)) => *e,
            Err(_) => -1,
        };

        self.recorder
            .record("/dev/nvidiactl", 0x2a, 0, &request, &response, ret);

        result
    }

    fn alloc_memory(
        &mut self,
        h_root: NvHandle,
        h_parent: NvHandle,
        h_memory: NvHandle,
        h_class: u32,
        flags: u32,
        size: u64,
    ) -> DriverResult<(u64, u32)> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_root.to_le_bytes());
        request.extend_from_slice(&h_parent.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&h_class.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());
        request.extend_from_slice(&size.to_le_bytes());

        let result = self
            .inner
            .alloc_memory(h_root, h_parent, h_memory, h_class, flags, size);

        let (response, ret) = match &result {
            Ok((addr, status)) => {
                let mut resp = Vec::new();
                resp.extend_from_slice(&addr.to_le_bytes());
                resp.extend_from_slice(&status.to_le_bytes());
                (resp, 0)
            }
            Err(DriverError::IoError(e)) => (Vec::new(), *e),
            Err(_) => (Vec::new(), -1),
        };

        self.recorder
            .record("/dev/nvidiactl", 0x27, 0, &request, &response, ret);

        result
    }

    fn map_memory(
        &mut self,
        h_client: NvHandle,
        h_device: NvHandle,
        h_memory: NvHandle,
        offset: u64,
        length: u64,
        flags: u32,
    ) -> DriverResult<(u64, u32)> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_device.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&offset.to_le_bytes());
        request.extend_from_slice(&length.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());

        let result = self
            .inner
            .map_memory(h_client, h_device, h_memory, offset, length, flags);

        let (response, ret) = match &result {
            Ok((addr, status)) => {
                let mut resp = Vec::new();
                resp.extend_from_slice(&addr.to_le_bytes());
                resp.extend_from_slice(&status.to_le_bytes());
                (resp, 0)
            }
            Err(DriverError::IoError(e)) => (Vec::new(), *e),
            Err(_) => (Vec::new(), -1),
        };

        self.recorder
            .record("/dev/nvidiactl", 0x4e, 0, &request, &response, ret);

        result
    }

    fn unmap_memory(
        &mut self,
        h_client: NvHandle,
        h_device: NvHandle,
        h_memory: NvHandle,
        address: u64,
        flags: u32,
    ) -> DriverResult<u32> {
        let mut request = Vec::new();
        request.extend_from_slice(&h_client.to_le_bytes());
        request.extend_from_slice(&h_device.to_le_bytes());
        request.extend_from_slice(&h_memory.to_le_bytes());
        request.extend_from_slice(&address.to_le_bytes());
        request.extend_from_slice(&flags.to_le_bytes());

        let result = self
            .inner
            .unmap_memory(h_client, h_device, h_memory, address, flags);

        let ret = match &result {
            Ok(_) => 0,
            Err(DriverError::IoError(e)) => *e,
            Err(_) => -1,
        };

        self.recorder
            .record("/dev/nvidiactl", 0x4f, 0, &request, &request, ret);

        result
    }

    fn card_info(&self, cards: &mut [NvCardInfo]) -> DriverResult<usize> {
        // Note: This is a const method, so we can't record here
        // A real implementation would need interior mutability
        self.inner.card_info(cards)
    }

    fn check_version(&self, version: &mut NvRmApiVersion) -> DriverResult<()> {
        // Note: This is a const method, so we can't record here
        self.inner.check_version(version)
    }

    fn is_real(&self) -> bool {
        self.inner.is_real()
    }
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::MockDriver;

    #[test]
    fn test_trace_record_save_load() {
        let mut recorder = TraceRecorder::new("test-trace");

        // Record some events
        recorder.record(
            "/dev/nvidiactl",
            0x2b,
            0,
            &[1, 2, 3, 4],
            &[1, 2, 3, 4, 0, 0, 0, 0],
            0,
        );
        recorder.record(
            "/dev/nvidiactl",
            0x2a,
            0,
            &[5, 6, 7, 8],
            &[5, 6, 7, 8, 9, 10],
            0,
        );

        let trace = recorder.finish();

        assert_eq!(trace.events.len(), 2);
        
        // Extract ioctl events
        let ioctls: Vec<_> = trace.ioctl_events().collect();
        assert_eq!(ioctls.len(), 2);
        assert_eq!(ioctls[0].cmd, 0x2b);
        assert_eq!(ioctls[0].op_name, Some("RM_ALLOC".to_string()));
        assert_eq!(ioctls[1].cmd, 0x2a);
        assert_eq!(ioctls[1].op_name, Some("RM_CONTROL".to_string()));

        // Save and reload
        let tmp = tempfile::NamedTempFile::new().unwrap();
        trace.save(tmp.path()).unwrap();

        let loaded = IoctlTrace::load(tmp.path()).unwrap();
        assert_eq!(loaded.events.len(), 2);
        let loaded_ioctls: Vec<_> = loaded.ioctl_events().collect();
        assert_eq!(loaded_ioctls[0].request, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_trace_stats() {
        let mut trace = IoctlTrace::new("test");
        trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns: 0,
            device: "/dev/nvidiactl".to_string(),
            cmd: 0x2b,
            ioctl_nr: 0,
            request: vec![0; 32],
            response: vec![0; 40],
            ret: 0,
            op_name: Some("RM_ALLOC".to_string()),
        }));
        trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns: 1000,
            device: "/dev/nvidiactl".to_string(),
            cmd: 0x2a,
            ioctl_nr: 0,
            request: vec![0; 64],
            response: vec![0; 64],
            ret: 0,
            op_name: Some("RM_CONTROL".to_string()),
        }));
        trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns: 2000,
            device: "/dev/nvidia0".to_string(),
            cmd: 0xc9,
            ioctl_nr: 0,
            request: vec![0; 8],
            response: vec![0; 8],
            ret: 0,
            op_name: Some("ATTACH_GPUS_TO_FD".to_string()),
        }));

        let stats = trace.stats();
        assert_eq!(stats.total_events, 3);
        assert_eq!(stats.cmd_counts.get(&0x2b), Some(&1));
        assert_eq!(stats.cmd_counts.get(&0x2a), Some(&1));
        assert_eq!(stats.cmd_counts.get(&0xc9), Some(&1));
        assert_eq!(stats.device_counts.get("/dev/nvidiactl"), Some(&2));
        assert_eq!(stats.device_counts.get("/dev/nvidia0"), Some(&1));
    }

    #[test]
    fn test_replay_driver() {
        // Create a trace
        let mut trace = IoctlTrace::new("test-replay");
        trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns: 0,
            device: "/dev/nvidiactl".to_string(),
            cmd: 0x2b,
            ioctl_nr: 0,
            request: vec![1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0x41, 0, 0, 0],
            response: vec![1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0x41, 0, 0, 0, 0, 0, 0, 0],
            ret: 0,
            op_name: Some("RM_ALLOC".to_string()),
        }));

        let mut driver = TraceReplayDriver::new(trace);

        // This should find the recorded event and return success
        let status = driver.alloc(1, 1, 2, 0x41, None).unwrap();
        assert_eq!(status, 0);
        assert_eq!(driver.stats.total_replayed, 1);
    }

    #[test]
    fn test_recording_driver() {
        let mock = MockDriver::new();
        let mut recording = RecordingDriver::new(mock, "test-recording");

        // Perform some operations
        let _ = recording.alloc(1, 1, 2, 0x41, None);
        let _ = recording.control(1, 2, 0x1234, &mut [0u8; 8]);
        let _ = recording.free(1, 1, 2);

        // Get the trace
        let (_, trace) = recording.finish();

        assert_eq!(trace.events.len(), 3);
        let ioctls: Vec<_> = trace.ioctl_events().collect();
        assert_eq!(ioctls[0].cmd, 0x2b); // RM_ALLOC
        assert_eq!(ioctls[1].cmd, 0x2a); // RM_CONTROL
        assert_eq!(ioctls[2].cmd, 0x29); // RM_FREE
    }

    #[test]
    fn test_binary_format() {
        let mut trace = IoctlTrace::new("binary-test");
        trace.events.push(TraceEvent::Ioctl(IoctlEvent {
            timestamp_ns: 0,
            device: "/dev/nvidiactl".to_string(),
            cmd: 0x2b,
            ioctl_nr: 0,
            request: vec![1, 2, 3, 4, 5, 6, 7, 8],
            response: vec![8, 7, 6, 5, 4, 3, 2, 1],
            ret: 0,
            op_name: None,
        }));

        // Test file save/load
        let tmp = tempfile::NamedTempFile::new().unwrap();
        trace.save_binary(tmp.path()).expect("save_binary failed");

        // Check file size
        let metadata = std::fs::metadata(tmp.path()).expect("metadata failed");
        assert!(metadata.len() > 0, "Binary file is empty");

        let loaded = IoctlTrace::load_binary(tmp.path()).expect("load_binary failed");
        assert_eq!(loaded.events.len(), 1);
        
        let loaded_ioctls: Vec<_> = loaded.ioctl_events().collect();
        let orig_ioctls: Vec<_> = trace.ioctl_events().collect();
        assert_eq!(loaded_ioctls[0].request, orig_ioctls[0].request);
    }

    /// Test that generates a realistic nvidia-smi-like sequence,
    /// records it, saves to file, reloads, and replays
    #[test]
    fn test_record_and_replay_roundtrip() {
        use crate::rm_api::classes;
        
        // Step 1: Record a session with MockDriver
        let mock = MockDriver::new();
        let mut recording = RecordingDriver::new(mock, "nvidia-smi-simulation");
        
        // Simulate nvidia-smi startup sequence
        // 1. Create root client
        let status = recording.alloc(0, 0, 1, classes::NV01_ROOT_CLIENT, None).unwrap();
        assert_eq!(status, 0);
        
        // 2. Create device
        let status = recording.alloc(1, 1, 2, classes::NV01_DEVICE_0, None).unwrap();
        assert_eq!(status, 0);
        
        // 3. Create subdevice  
        let status = recording.alloc(1, 2, 3, classes::NV20_SUBDEVICE_0, None).unwrap();
        assert_eq!(status, 0);
        
        // 4. Query GPU name (control call)
        let mut params = [0u8; 64];
        let status = recording.control(1, 3, 0x20800110, &mut params).unwrap();
        assert_eq!(status, 0);
        
        // 5. Query FB info
        let mut fb_params = [0u8; 32];
        let status = recording.control(1, 3, 0x20801301, &mut fb_params).unwrap();
        assert_eq!(status, 0);
        
        // 6. Cleanup - free in reverse order
        let status = recording.free(1, 2, 3).unwrap();
        assert_eq!(status, 0);
        let status = recording.free(1, 1, 2).unwrap();
        assert_eq!(status, 0);
        let status = recording.free(1, 0, 1).unwrap();
        assert_eq!(status, 0);
        
        // Step 2: Get the trace
        let (_, trace) = recording.finish();
        
        // Verify trace contents
        assert_eq!(trace.events.len(), 8);
        let stats = trace.stats();
        assert_eq!(stats.cmd_counts.get(&0x2b), Some(&3)); // 3 allocs
        assert_eq!(stats.cmd_counts.get(&0x2a), Some(&2)); // 2 controls
        assert_eq!(stats.cmd_counts.get(&0x29), Some(&3)); // 3 frees
        
        // Step 3: Save and reload
        let tmp = tempfile::NamedTempFile::new().unwrap();
        trace.save(tmp.path()).expect("save failed");
        
        let reloaded = IoctlTrace::load(tmp.path()).expect("load failed");
        assert_eq!(reloaded.events.len(), trace.events.len());
        
        // Step 4: Replay through TraceReplayDriver
        let mut replay = TraceReplayDriver::new(reloaded);
        
        // Replay the same sequence
        let status = replay.alloc(0, 0, 1, classes::NV01_ROOT_CLIENT, None).unwrap();
        assert_eq!(status, 0);
        
        let status = replay.alloc(1, 1, 2, classes::NV01_DEVICE_0, None).unwrap();
        assert_eq!(status, 0);
        
        let status = replay.alloc(1, 2, 3, classes::NV20_SUBDEVICE_0, None).unwrap();
        assert_eq!(status, 0);
        
        let mut params = [0u8; 64];
        let status = replay.control(1, 3, 0x20800110, &mut params).unwrap();
        assert_eq!(status, 0);
        
        let mut fb_params = [0u8; 32];
        let status = replay.control(1, 3, 0x20801301, &mut fb_params).unwrap();
        assert_eq!(status, 0);
        
        let status = replay.free(1, 2, 3).unwrap();
        assert_eq!(status, 0);
        let status = replay.free(1, 1, 2).unwrap();
        assert_eq!(status, 0);
        let status = replay.free(1, 0, 1).unwrap();
        assert_eq!(status, 0);
        
        // Verify replay stats
        assert_eq!(replay.stats.total_replayed, 8);
        assert_eq!(replay.stats.misses, 0);
    }

    /// Test that replay handles out-of-order calls gracefully
    #[test]
    fn test_replay_fuzzy_matching() {
        // Create a simple trace
        let mut trace = IoctlTrace::new("fuzzy-test");
        
        // Add some alloc events
        for i in 0..5 {
            trace.events.push(TraceEvent::Ioctl(IoctlEvent {
                timestamp_ns: i * 1000,
                device: "/dev/nvidiactl".to_string(),
                cmd: 0x2b, // RM_ALLOC
                ioctl_nr: 0,
                request: vec![i as u8; 16],
                response: vec![i as u8; 20],
                ret: 0,
                op_name: Some("RM_ALLOC".to_string()),
            }));
        }
        
        let mut replay = TraceReplayDriver::new(trace);
        
        // Call alloc 5 times - should match even without exact request bytes
        for _ in 0..5 {
            let result = replay.alloc(0, 0, 1, 0x41, None);
            assert!(result.is_ok());
        }
        
        // All 5 should have been replayed
        assert_eq!(replay.stats.total_replayed, 5);
        
        // 6th call should still work (returns default) but counts as miss
        let result = replay.alloc(0, 0, 1, 0x41, None);
        assert!(result.is_ok());
        assert_eq!(replay.stats.misses, 1);
    }
}
