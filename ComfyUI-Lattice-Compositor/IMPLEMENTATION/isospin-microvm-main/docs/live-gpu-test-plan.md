# Live GPU Passthrough Test Plan

## Current Status

**Property Tests**: ✅ 91/91 passing (23,296 test cases)  
**Implementation**: ✅ VFIO primitives complete (~3,200 lines)  
**Integration**: ⏳ Device manager integration needed  
**Hardware**: RTX PRO 6000 Blackwell ready

## The Challenge

The GPU (0000:01:00.0) is currently:
- Bound to `nvidia` driver
- Being used for Wayland display
- Cannot be unbound without dropping the display

## Solution: SSH Testing

### Prerequisites

1. **Enable SSH** (if not already)
   ```bash
   sudo systemctl enable sshd
   sudo systemctl start sshd
   ```

2. **Find your IP**
   ```bash
   ip addr show | grep "inet " | grep -v 127.0.0.1
   ```

3. **SSH from another machine**
   ```bash
   ssh b7r6@<your-ip>
   ```

### Test Execution Steps

Once SSH'd in, run:

```bash
cd /home/b7r6/src/vendor/isospin

# Step 1: Bind GPU to vfio-pci (will drop local display)
sudo ./scripts/vfio-bind.sh 0000:01:00.0 0000:01:00.1

# Step 2: Verify VFIO binding
./scripts/vfio-status.sh

# Step 3: Create VM image (if not exists)
./scripts/create-gpu-image.sh

# Step 4: Run Firecracker with GPU (once integrated)
sudo ./scripts/run-firecracker-gpu.sh

# Step 5: In VM, verify GPU
lspci | grep -i nvidia
nvidia-smi
```

### Restoration

To restore your display after testing:

```bash
# Unbind from vfio-pci and restore nvidia driver
sudo ./scripts/vfio-unbind.sh 0000:01:00.0 0000:01:00.1

# If that doesn't work, reboot
sudo reboot
```

## Integration Work Needed

Before we can test, we need to integrate VfioPciDevice into Firecracker:

### 1. Device Manager Integration (~200 lines)

**File**: `firecracker/src/vmm/src/device_manager/pci_mngr.rs`

Add `attach_vfio_device()` function:
- Allocate PCI BDF
- Create VFIO container and device
- Map guest memory for DMA
- Create MSI-X vector group
- Allocate BARs in MMIO space
- Register with PCI bus and MMIO bus

### 2. Interrupt Routing (~150 lines)

**Files**: 
- `firecracker/src/vmm/src/pci/vfio/device.rs`
- Integration with `firecracker/src/vmm/src/vstate/interrupts.rs`

Add MSI-X interrupt setup:
- Create eventfds for each MSI-X vector
- Call `VFIO_DEVICE_SET_IRQS` to register eventfds with VFIO
- Register eventfds with KVM via `register_irqfd()`

### 3. API Integration (~150 lines)

**Files**:
- `firecracker/src/vmm/src/vmm_config/vfio.rs` (new)
- `firecracker/src/vmm/src/rpc_interface.rs`

Add VFIO device configuration:
```rust
pub struct VfioDeviceConfig {
    pub device_id: String,
    pub sysfs_path: String,  // e.g., "/sys/bus/pci/devices/0000:01:00.0"
}
```

### 4. Builder Integration (~100 lines)

**File**: `firecracker/src/vmm/src/builder.rs`

Wire VFIO devices into `build_microvm_for_boot()`:
- After virtio devices are attached
- Before starting vCPUs

## Estimated Timeline

| Task | Lines | Effort | Status |
|------|-------|--------|--------|
| Device Manager Integration | ~200 | 4-6 hours | ⏳ Not Started |
| Interrupt Routing | ~150 | 3-4 hours | ⏳ Not Started |
| API Integration | ~150 | 2-3 hours | ⏳ Not Started |
| Builder Integration | ~100 | 1-2 hours | ⏳ Not Started |
| Testing & Debugging | - | 4-8 hours | ⏳ Not Started |
| **Total** | **~600** | **14-23 hours** | **⏳ Not Started** |

## Alternative: Test with Cloud Hypervisor

Cloud Hypervisor already has full VFIO support. We can test the hardware setup:

```bash
cd /home/b7r6/src/vendor/isospin

# This will work from SSH
sudo ./scripts/boot-ch-gpu.sh

# SSH into VM
ssh -i .vm-assets/vm_key root@172.16.0.2

# In VM
lspci | grep -i nvidia
nvidia-smi
```

**Pros**:
- Quick validation that hardware setup works
- Confirms our scripts work
- Reference implementation to compare against

**Cons**:
- Not testing Firecracker VFIO implementation
- Doesn't validate our property tests

## Recommendation

**Option A: Complete Integration First** (14-23 hours)
- Finish device manager integration
- Add interrupt routing
- Wire up API
- Then test via SSH

**Option B: Quick Hardware Validation** (1 hour)
- Test Cloud Hypervisor GPU passthrough via SSH
- Validates hardware setup
- Then complete Firecracker integration

**Option C: Hybrid Approach** (Best)
1. Quick CH test via SSH to validate hardware (1 hour)
2. Complete Firecracker integration (14-23 hours)
3. Test Firecracker GPU passthrough via SSH
4. Compare results with CH

## Decision Point

You said "do it" and you're "willing [to lose Wayland] for a successful result."

What would you like to do?

1. **SSH in now** and test Cloud Hypervisor GPU passthrough (quick hardware validation)
2. **Complete Firecracker integration** first, then SSH test everything
3. **Reboot with different display GPU** so we can work normally while testing

The property tests give us high confidence the VFIO primitives are correct. The remaining work is "glue code" to wire everything together.

Your call! 🚀
