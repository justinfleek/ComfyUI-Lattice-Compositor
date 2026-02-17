# GPU Broker: Path to Complete

**Status: M1 ioctls implemented, ready for end-to-end testing (January 20, 2026)**

This document outlines the concrete steps to move from "one ioctl works" to "nvidia-smi works" to "PyTorch inference works".

## Current State (Updated 2026-01-20)

```
Working:
  [x] nvidia-shim.ko loads in Firecracker guest
  [x] vsock connection to host broker
  [x] NV_ESC_CARD_INFO (ioctl 200) returns mock data
  [x] NV_ESC_CHECK_VERSION_STR (ioctl 210) fixed - wire protocol aligned
  [x] Real GPU passthrough VM boots and runs nvidia-smi successfully
  [x] strace capture of nvidia-smi -L completed
  [x] NV_ESC_SYS_PARAMS (214) - implemented in broker
  [x] /dev/nvidia0 device ioctls:
      - NV_ESC_ATTACH_GPUS_TO_FD (201) - op_type 12
      - NV_ESC_GET_PCI_INFO (215) - op_type 17
      - NV_ESC_EXPORT_DEVICE_FD (218) - op_type 18
  [x] /dev/nvidia-uvm device stubbed (UVM_INITIALIZE, UVM_DEINITIALIZE, UVM_MM_INITIALIZE)
  [x] Wire protocol encoding/decoding for all M1 ioctls
  [x] Kernel module copy_result_to_user() parses broker envelope format
  
Not working (gaps for M1):
  [ ] End-to-end testing (need to build kernel module and boot VM)
  [ ] mmap - not implemented (may not be needed for nvidia-smi -L)
```

## Actual ioctl Trace: nvidia-smi -L

**Captured 2026-01-20** from real GPU passthrough VM with RTX PRO 6000 Blackwell.

### File Descriptors Used
```
fd 9  = /dev/nvidiactl (frontend)
fd 10 = /dev/nvidia0 (device, first open)
fd 11 = /dev/nvidia-uvm (UVM subsystem)
fd 14 = /dev/nvidia-uvm (second open)
fd 15 = /dev/nvidia0 (second open)
fd 16 = /dev/nvidia0 (third open)
```

### Ioctl Coverage Table

#### /dev/nvidiactl (type=0x46 'F')
| Nr (hex) | Nr (dec) | Name                    | Count | Kernel | Broker | Status |
|----------|----------|-------------------------|-------|--------|--------|--------|
| 0x29     | 41       | NV_ESC_RM_FREE          | 3     | YES    | YES    | OK     |
| 0x2a     | 42       | NV_ESC_RM_CONTROL       | 20    | YES    | YES    | OK     |
| 0x2b     | 43       | NV_ESC_RM_ALLOC         | 5     | YES    | YES    | OK     |
| 0xc8     | 200      | NV_ESC_CARD_INFO        | 1     | YES    | YES    | OK     |
| 0xd2     | 210      | NV_ESC_CHECK_VERSION    | 1     | YES    | YES    | FIXED  |
| 0xd6     | 214      | NV_ESC_SYS_PARAMS       | 1     | NO     | NO     | **GAP**|

#### /dev/nvidia0 (type=0x46 'F')
| Nr (hex) | Nr (dec) | Name                      | Count | Kernel | Broker | Status |
|----------|----------|---------------------------|-------|--------|--------|--------|
| 0xc9     | 201      | NV_ESC_ATTACH_GPUS_TO_FD  | 2     | NO     | NO     | **GAP**|
| 0xd7     | 215      | NV_ESC_GET_PCI_INFO       | 1     | NO     | NO     | **GAP**|
| 0xda     | 218      | NV_ESC_EXPORT_DEVICE_FD   | 1     | NO     | NO     | **GAP**|

#### /dev/nvidia-uvm (type=0x00 - separate subsystem)
| Nr (hex) | Name              | Count | Status |
|----------|-------------------|-------|--------|
| 0x01     | UVM_INITIALIZE    | 1     | **GAP**|
| 0x02     | UVM_DEINITIALIZE  | 1     | **GAP**|
| 0x4b     | UVM_MM_INITIALIZE | 1     | **GAP**|

### Key Insight: NV_ESC_RM_CONTROL Dominates

The RM control ioctl (0x2a) is called **20 times** during nvidia-smi -L. This is the main
GPU query path. The broker must translate handles and forward control commands correctly.

## Methodology: Trace, Implement, Test

For each milestone:

1. **Trace** the target workload with strace
2. **Catalog** the exact ioctl sequence
3. **Implement** wire protocol for each ioctl
4. **Test** with mock driver
5. **Validate** against real GPU

## Milestone 1: nvidia-smi -L

**Goal**: `nvidia-smi -L` lists a GPU via the broker

### Step 1.1: Trace on real system - DONE

**Completed 2026-01-20** using GPU passthrough VM with strace.

```bash
# In GPU passthrough VM
strace -e trace=ioctl,openat -f -s 200 /usr/bin/nvidia-smi -L 2>&1
```

Output confirmed working - shows "GPU 0: NVIDIA RTX PRO 6000 Blackwell Workstation Edition".

### Step 1.2: Fix NV_ESC_CHECK_VERSION_STR - DONE

The wire protocol bug was fixed:
- `WireResponse::to_bytes()` was returning 28 bytes but kernel expected 32 bytes
- Added missing `result_len` field to response
- Both NV_ESC_CARD_INFO and NV_ESC_CHECK_VERSION_STR now work

### Step 1.3: Remaining gaps for M1

Based on trace analysis, these are needed:

#### A. NV_ESC_SYS_PARAMS (214) on /dev/nvidiactl
```c
// Add to nvidia-shim.c
#define NV_ESC_SYS_PARAMS 214
// Size: 0x8 bytes
```

#### B. Device-specific ioctls on /dev/nvidia0
Currently nvidia-shim.c routes all ioctls through the same vsock path.
Need to differentiate:
- `/dev/nvidiactl` (minor 255) - control device
- `/dev/nvidia0` (minor 0) - device instance

Ioctls needed on /dev/nvidia0:
```c
#define NV_ESC_ATTACH_GPUS_TO_FD  201  // Different semantics on device fd
#define NV_ESC_GET_PCI_INFO       215  // Size: 0x230 bytes
#define NV_ESC_EXPORT_DEVICE_FD   218  // Size: 0x8 bytes
```

#### C. /dev/nvidia-uvm device (optional for M1?)
Separate character device with type=0x00 ioctls. May be able to stub for M1.

### Step 1.4: Implementation Plan

1. Add NV_ESC_SYS_PARAMS to kernel module and broker
2. Add NV_ESC_GET_PCI_INFO to kernel module and broker
3. Add NV_ESC_EXPORT_DEVICE_FD to kernel module and broker
4. Decide on nvidia-uvm strategy (stub or implement)
5. Test with mock broker

### Step 1.5: Test milestone

```bash
# In guest VM with nvidia-shim.ko + broker
nvidia-smi -L
# Should output: GPU 0: Mock GPU (UUID: GPU-mock-...)
```

## Milestone 2: Full nvidia-smi

**Goal**: `nvidia-smi` shows GPU details, temperature, memory

### Step 2.1: Trace

```bash
sudo strace -e ioctl -o /tmp/nvidia-smi-full.strace nvidia-smi
wc -l /tmp/nvidia-smi-full.strace  # Expect 50-100 ioctls
```

### Step 2.2: Catalog new ioctls

```bash
# Extract unique ioctl numbers
grep "ioctl(" /tmp/nvidia-smi-full.strace | \
  sed "s/.*_IOC.*'F', \(0x[0-9a-f]*\).*/\1/" | \
  sort -u
```

Expected new ioctls:
- `NV_ESC_REGISTER_FD (201)` - Client registration
- `NV_ESC_RM_ALLOC (0x2B)` - Allocate RM objects
- `NV_ESC_RM_CONTROL (0x2A)` - Query GPU properties

### Step 2.3: Implement RM_ALLOC

This is the core handle allocation ioctl:

```c
struct NV_ALLOC_PARAMS {
    uint32_t hRoot;       // Root client handle
    uint32_t hParent;     // Parent handle
    uint32_t hObject;     // New object handle (client-chosen or 0)
    uint32_t hClass;      // Object class
    void*    pAllocParms; // Class-specific params
};
```

The broker must:
1. Receive guest handle
2. Allocate real handle from driver (or mock)
3. Record mapping: guest_handle -> real_handle
4. Return success

### Step 2.4: Implement RM_CONTROL

Control calls query and modify object properties:

```c
struct NV_CONTROL_PARAMS {
    uint32_t hClient;     // Client handle
    uint32_t hObject;     // Target object
    uint32_t cmd;         // Control command
    uint32_t paramsSize;  // Size of params
    void*    params;      // Command-specific params
};
```

The broker must:
1. Translate hClient and hObject to real handles
2. Forward to driver
3. Return result

### Step 2.5: Mock data for nvidia-smi

The mock driver should return plausible data:
- GPU name: "Mock RTX PRO 6000"
- Temperature: 45C
- Memory: 128GB total, 0GB used
- Utilization: 0%

## Milestone 3: torch.cuda.is_available()

**Goal**: PyTorch detects the GPU

### Step 3.1: Trace

```bash
sudo strace -e ioctl python3 -c "import torch; print(torch.cuda.is_available())"
```

### Step 3.2: New ioctls expected

- `NV_ESC_ALLOC_OS_EVENT (206)` - Event allocation
- `NV_ESC_RM_MAP_MEMORY (0x4E)` - Memory mapping

### Step 3.3: Implement mmap handling

When guest calls `mmap()` on `/dev/nvidia0`:

Option A (simple): Return shared memory region
```c
static int nvidia_shim_mmap(struct file *file, struct vm_area_struct *vma) {
    // Map pre-allocated shared memory
    return remap_pfn_range(vma, vma->vm_start,
                           shared_mem_phys >> PAGE_SHIFT,
                           vma->vm_end - vma->vm_start,
                           vma->vm_page_prot);
}
```

Option B (proper): Coordinate with broker for region allocation

## Milestone 4: tensor.cuda()

**Goal**: Allocate GPU tensor

### New requirements

- `NV_ESC_RM_ALLOC_MEMORY (0x27)` - Allocate GPU memory
- Memory must be accessible via mmap

### Handle translation complexity

Guest allocates memory handle H1 → Broker allocates real memory → Returns mock handle
Guest maps H1 → Broker provides shared buffer at that "address"
Guest writes to mapping → Broker copies to real GPU memory (if not mock)

## Milestone 5: Model Inference

**Goal**: Run a real PyTorch model

### New requirements

- Kernel launch ioctls
- Synchronization ioctls
- DMA completion tracking

## File Structure

```
gpu-broker/
├── kernel/
│   └── nvidia-shim.c          # Guest kernel module
├── src/
│   ├── broker.rs              # Core state machine
│   ├── driver.rs              # Real/mock driver interface
│   ├── firecracker_vsock.rs   # Firecracker vsock server
│   ├── handle_table.rs        # Guest<->real handle mapping
│   ├── mock_driver.rs         # Mock responses
│   ├── proxy.rs               # BrokerProxy orchestration
│   ├── rm_api.rs              # RM API type definitions
│   └── vsock.rs               # Wire protocol
└── tests/
    └── ioctl_traces/          # Captured ioctl traces for replay
```

## Testing Infrastructure

### 1. Trace capture

```bash
# Capture trace
./scripts/capture-ioctl-trace.sh nvidia-smi > traces/nvidia-smi.json

# Format: 
# {"op": "ioctl", "fd": 3, "cmd": 200, "arg_hex": "...", "result": 0}
```

### 2. Trace replay

```bash
# Replay against mock broker
./scripts/replay-trace.sh traces/nvidia-smi.json

# Verify all ioctls return expected results
```

### 3. Differential testing

```bash
# Run same trace against real driver and broker
# Compare results
./scripts/differential-test.sh traces/nvidia-smi.json
```

## Next Concrete Steps

1. **Add verbose logging to nvidia-shim.c**
   - Print request bytes before send
   - Print response bytes after receive
   - Identify wire protocol mismatch

2. **Fix NV_ESC_CHECK_VERSION_STR**
   - Align request/response format
   - Test in VM

3. **Trace nvidia-smi -L on host**
   - Capture exact ioctl sequence
   - Document parameter structures

4. **Implement nvidia-smi -L milestone**
   - Add any missing ioctls
   - Test end-to-end

5. **Iterate to full nvidia-smi**

## Success Criteria

| Milestone | Test Command | Expected Output |
|-----------|--------------|-----------------|
| M1 | `nvidia-smi -L` | Lists mock GPU |
| M2 | `nvidia-smi` | Full GPU info |
| M3 | `python -c "import torch; print(torch.cuda.is_available())"` | `True` |
| M4 | `python -c "import torch; print(torch.zeros(1).cuda())"` | `tensor([0.], device='cuda:0')` |
| M5 | `python inference.py` | Model output |

## References

- open-gpu-kernel-modules: `kernel-open/nvidia/nv-ioctl.c`
- NVIDIA RM API: `src/nvidia/interface/rmapi/`
- nouveau: `drivers/gpu/drm/nouveau/` for hardware understanding
