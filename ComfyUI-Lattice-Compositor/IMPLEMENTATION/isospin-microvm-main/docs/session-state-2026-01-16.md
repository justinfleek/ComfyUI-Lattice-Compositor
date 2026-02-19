# Isospin Session State - 2026-01-16

## Summary

Built **gpu-broker** - a GPU multiplexer that allows multiple VMs to share a single NVIDIA GPU without the 15-second cold boot penalty per VM. The broker proxies NVIDIA RM API calls (~20 ioctls) and provides per-client handle isolation.

**Two binaries:**
- `gpu-broker` - Host-side server
- `guest-shim` - Guest-side NVIDIA device emulator

## Quick Start

```bash
cd gpu-broker

# Run tests (121 property tests)
cargo test

# Build release binaries
cargo build --release

# Run broker with mock driver (no GPU required)
./target/release/gpu-broker --mock --socket /tmp/gpu-broker.sock

# In another terminal, test guest connection
./target/release/guest-shim --broker-socket /tmp/gpu-broker.sock --dry-run
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Guest VM                                │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ CUDA App → libcuda.so → open("/dev/nvidiactl") + ioctl  │   │
│  └──────────────────────────┬──────────────────────────────┘   │
│                             │                                   │
│  ┌──────────────────────────▼──────────────────────────────┐   │
│  │ guest-shim (CUSE device emulator)                       │   │
│  │  - Emulates /dev/nvidiactl, /dev/nvidia0                │   │
│  │  - Intercepts ioctls, forwards via shared memory        │   │
│  └──────────────────────────┬──────────────────────────────┘   │
│                             │ shared memory + eventfd          │
└─────────────────────────────┼───────────────────────────────────┘
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      gpu-broker (Host)                          │
├─────────────────────────────────────────────────────────────────┤
│  BrokerServer                                                   │
│  ┌────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │ Unix Socket    │  │ io_uring        │  │ BrokerProxy     │  │
│  │ Listener       │──│ Event Loop      │──│ HandleTable     │  │
│  └────────────────┘  └─────────────────┘  └────────┬────────┘  │
│                                                     │           │
│  SharedMemoryRegion (per client)                    │           │
│  ┌─────────────────────────────────────────────┐   │           │
│  │ Request Ring │ Response Ring │ Data Pools   │   │           │
│  └─────────────────────────────────────────────┘   │           │
│                                                     ▼           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ NvDriver - /dev/nvidiactl ioctls                        │   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
                     GPU Hardware (stays warm)
```

## Source Files

### Core Broker (`gpu-broker/src/`)

| File | Lines | Description |
|------|-------|-------------|
| `broker.rs` | ~500 | Pure state machine: `(State, Input) → (State', Output)` |
| `handle_table.rs` | ~600 | Per-client virtual→real handle mapping |
| `rm_api.rs` | ~450 | NVIDIA RM API structs (NvOs00Params, NvOs54Params, etc.) |
| `driver.rs` | ~500 | `NvDriver` (real) + `MockDriver` (testing) |
| `proxy.rs` | ~600 | `BrokerProxy` - handle translation + driver calls |

### Transport Layer

| File | Lines | Description |
|------|-------|-------------|
| `uring.rs` | ~400 | io_uring event loop with PollAdd on client eventfds |
| `uring_transport.rs` | ~760 | Shared memory rings (SPSC, lock-free, cache-aligned) |
| `transport.rs` | ~300 | `SimulatedTransport` for testing |

### Server/Client

| File | Lines | Description |
|------|-------|-------------|
| `server.rs` | ~500 | `BrokerServer` - Unix socket + client management |
| `guest_shim.rs` | ~800 | Guest-side ioctl interception (library) |
| `bin/guest-shim.rs` | ~150 | Guest-side binary |
| `main.rs` | ~130 | Host-side binary entry point |

**Total: ~5,600 lines of Rust**

## Key Design Decisions

### 1. Pure State Machine (Carmack/Aerospace Pattern)
```rust
pub fn tick(mut self, request: Request) -> (Self, Response)
```
- Deterministic replay from any input sequence
- Time-travel debugging (step forward/backward)
- The simulation IS the test

### 2. Handle Isolation
Each VM client has isolated handle namespace:
```
VM 1: virtual 0x1 → real 0x1000
VM 2: virtual 0x1 → real 0x2000  (different!)
```
A malicious VM cannot reference another VM's GPU objects.

### 3. Lock-Free Shared Memory Rings
```rust
#[repr(C, align(64))]  // Cache line aligned
pub struct RingHeader {
    pub head: AtomicU32,  // Consumer updates
    _pad1: [u8; 60],      // Prevent false sharing
    pub tail: AtomicU32,  // Producer updates
    _pad2: [u8; 60],
    ...
}
```
SPSC (Single Producer Single Consumer) - no locks needed.

### 4. io_uring for Scalability
O(1) wake-up regardless of client count (vs epoll's O(n) on completion).

## NVIDIA RM API Coverage

The broker handles these escape codes (from `nvidia-open/kernel-open/nvidia/nv-ioctl.h`):

| Escape | Code | Struct | Description |
|--------|------|--------|-------------|
| `NV_ESC_RM_ALLOC_MEMORY` | 0x27 | `NvOs02Params` | Allocate GPU memory |
| `NV_ESC_RM_ALLOC_OBJECT` | 0x28 | `NvOs05Params` | Allocate GPU object |
| `NV_ESC_RM_FREE` | 0x29 | `NvOs00Params` | Free object |
| `NV_ESC_RM_CONTROL` | 0x2A | `NvOs54Params` | Control command (the big one) |
| `NV_ESC_RM_ALLOC` | 0x2B | `NvOs21Params` | Generic allocation |
| `NV_ESC_RM_MAP_MEMORY` | 0x4E | `NvOs33Params` | Map memory |
| `NV_ESC_RM_UNMAP_MEMORY` | 0x4F | `NvOs34Params` | Unmap memory |
| ... | ... | ... | 20+ more supported |

## Test Coverage

121 property tests covering:
- Handle table isolation and exhaustion attacks
- Ring buffer overflow/underflow
- Request/response routing
- Client connect/disconnect cycles
- Statistics consistency
- Deterministic replay

```bash
cargo test
# test result: ok. 121 passed; 0 failed
```

## Git Commits (This Session)

```
5c1693e feat(gpu-broker): Add guest-shim binary for VM-side NVIDIA device emulation
bdfa0ee feat(gpu-broker): Add BrokerServer with Unix socket accept loop
1ff59c4 feat(gpu-broker): Add guest shim for FUSE-based NVIDIA device emulation
49298f5 docs: Update Chapter 18 with io_uring, driver proxy, shared memory
```

## What's Next

### Immediate (SCM_RIGHTS)
1. **File descriptor passing** - Send shmem_fd, request_eventfd, response_eventfd to guest via SCM_RIGHTS over Unix socket
2. **Guest receives fds** - Map shared memory, set up eventfd signaling

### Then (CUSE)
3. **CUSE device creation** - Implement `/dev/nvidia*` character devices in guest using `/dev/cuse`
4. **ioctl forwarding** - Handle `FUSE_IOCTL` requests, translate to broker operations

### Finally (Integration)
5. **virtio-shmem** - For actual VM integration (not just Unix socket)
6. **Real hardware test** - Test with RTX PRO 6000 Blackwell

## Related Documentation

- `docs/vfio-gpu-passthrough-book.md` - Chapter 18 covers gpu-broker in detail
- `gpu-broker/SECURITY.md` - Threat model and security considerations

## Environment

```bash
# Branch
git branch  # dev

# Rust version
rustc --version  # 1.83.0

# Build
cd gpu-broker && cargo build --release
ls -la target/release/{gpu-broker,guest-shim}
# -rwxr-xr-x 2.4M gpu-broker
# -rwxr-xr-x 2.4M guest-shim
```
