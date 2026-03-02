# VFIO Property Test Coverage

This document describes the comprehensive property-based tests for the Firecracker VFIO implementation. Property tests verify that invariants hold for all possible inputs, not just specific test cases.

## Test Categories

### 1. Address Type Properties (6 tests)

**Invariants Verified:**
- GPA ↔ IOVA conversions are bijective (roundtrip preserves value)
- Address arithmetic doesn't overflow for reasonable sizes
- Page alignment is preserved through operations
- Address ordering is consistent with u64 ordering
- Identity mapping (IOVA == GPA) works correctly

**Why This Matters:**
Type confusion between GPA (guest physical), HVA (host virtual), and IOVA (device view) is a common bug in device passthrough code. These tests ensure our type system prevents such bugs at compile time.

### 2. PCI Type Properties (4 tests)

**Invariants Verified:**
- Valid BDF (Bus:Device.Function) strings always parse correctly
- BDF parse/display is idempotent (format → parse → format gives same result)
- BAR config offsets are within PCI config space (0x10-0x24)
- BAR offsets are DWORD-aligned
- BAR index ↔ config offset conversion is bidirectional

**Why This Matters:**
PCI device addressing is specified by strict standards. These tests ensure we correctly handle all valid BDFs and BAR configurations.

### 3. DMA Mapping Properties (8 tests)

**Invariants Verified:**
- **No overlaps**: DMA mappings never overlap, even after sequences of map/unmap operations
- **Total size**: Sum of individual mapping sizes equals tracked total
- **find_containing**: Address lookup returns correct mapping
- **Adjacent allowed**: Adjacent (but non-overlapping) mappings are permitted
- **Unmap non-existent fails**: Attempting to unmap non-existent mapping fails gracefully
- **Map→unmap→remap**: Remapping a previously mapped region succeeds

**Why This Matters:**
DMA mapping bugs can cause:
- Memory corruption (overlapping mappings)
- Kernel panics (invalid IOVAs)
- Security issues (device accessing wrong memory)

The overlap detection is critical - a single overlap could allow a GPU to DMA into kernel memory.

### 4. BAR Allocation Properties (3 tests)

**Invariants Verified:**
- **Natural alignment**: All BAR allocations are naturally aligned (16MB BAR → 16MB aligned address)
- **No overlaps**: BAR regions never overlap
- **Monotonic allocation**: BAR addresses increase (no regression)

**Why This Matters:**
PCIe requires BARs to be naturally aligned. A misaligned BAR will cause:
- Device initialization failure
- Bus errors when accessing the BAR
- Potential system hang

Example: A 256MB GPU VRAM BAR must be 256MB-aligned (address & 0x0FFF_FFFF == 0).

### 5. MSI-X State Machine Properties (8 tests)

**Invariants Verified:**
- **Valid transitions**: Masked → Configured → Enabled → Configured → Masked
- **Cannot enable unconfigured**: Enabling without configuration fails
- **Cannot reconfigure enabled**: Must disable before reconfiguring
- **Invalid index fails**: Out-of-bounds vector access fails
- **Count invariants**: enabled_count ≤ configured_count ≤ total_vectors
- **can_deliver conditions**: Delivery requires (global_enable && !function_masked && vector_enabled)
- **Disable returns eventfd/GSI**: Cleanup information is correctly returned

**Why This Matters:**
MSI-X interrupt delivery is complex multi-step process:
1. Guest writes address/data to MSI-X table
2. VMM configures vector (creates eventfd, allocates GSI)
3. VMM registers with VFIO and KVM
4. Device signals → eventfd → KVM → guest IRQ injection

State machine bugs can cause:
- Lost interrupts (performance degradation)
- Spurious interrupts (system instability)
- Deadlocks (waiting for interrupt that never arrives)

### 6. Config Space Properties (4 tests)

**Invariants Verified:**
- **Shadow isolation**: BAR reads return shadow (guest) addresses, not physical addresses
- **MSI-X parsing stable**: Multiple reads of MSI-X capability return same data
- **Reads idempotent**: Config space reads don't have side effects
- **64-bit BAR consistency**: High/low 32-bit parts of 64-bit BARs are consistent

**Why This Matters:**
Config space virtualization prevents:
- Guest seeing host physical addresses (security)
- Guest reprogramming device BARs (stability)
- Config space confusion between real and shadow values

### 7. Integration Properties (3 tests)

**Invariants Verified:**
- BAR size and alignment requirements match
- DMA mappings (guest RAM) and BARs (device MMIO) don't conflict
- Multiple MSI-X vectors can coexist

**Why This Matters:**
These test cross-module interactions to ensure components work together correctly.

### 8. Edge Case Properties (5 tests)

**Invariants Verified:**
- Zero-size operations are rejected
- Maximum address values don't overflow
- Minimum vector count (1) works
- Maximum vector count (2048) works
- Boundary BAR indices (0, 5, 6, 7+) are handled correctly

**Why This Matters:**
Edge cases are where bugs hide. These tests ensure we handle boundary conditions gracefully.

## Test Execution

### High Iteration Counts

Property tests run with configurable iteration counts:
- **Default**: 256 iterations per property (quick smoke test)
- **CI**: 1,000 iterations (good coverage)
- **Pre-release**: 10,000 iterations (thorough)
- **Stress test**: 100,000+ iterations (find rare bugs)

### Running Tests

```bash
# Quick run (default iterations)
./buck2 test //firecracker/src/vmm:vmm-test -- pci::vfio::proptests

# High iteration count
PROPTEST_CASES=10000 ./buck2 test //firecracker/src/vmm:vmm-test -- pci::vfio::proptests

# Specific property
./buck2 test //firecracker/src/vmm:vmm-test -- prop_dma_no_overlaps_maintained

# With verbose output
./buck2 test //firecracker/src/vmm:vmm-test -- pci::vfio::proptests --nocapture
```

## Coverage Statistics

Total property tests: **41**
- Address types: 6
- PCI types: 4
- DMA mapping: 8
- BAR allocation: 3
- MSI-X: 8
- Config space: 4
- Integration: 3
- Edge cases: 5

Lines of test code: **~850**
Lines of implementation code: **~3,200**
Test-to-code ratio: **26.6%**

## What Property Tests Don't Cover

Property tests verify **logical invariants** but not:
- Hardware interactions (requires real device)
- Performance (requires benchmarks)
- Security (requires fuzzing)
- KVM/VFIO kernel API correctness (requires integration tests)

For these, we need:
1. **Unit tests** (existing): Mock-based tests of individual functions
2. **Integration tests**: End-to-end tests with real hardware
3. **Fuzzing**: Random input generation looking for crashes
4. **Performance tests**: Latency and throughput measurements

## Key Invariants Summary

| Module | Critical Invariant | Test Coverage |
|--------|-------------------|---------------|
| DMA | No overlapping mappings | ✅ Comprehensive |
| BAR | Natural alignment | ✅ Comprehensive |
| MSI-X | State machine correctness | ✅ Comprehensive |
| Config | Shadow isolation | ✅ Comprehensive |
| Types | No address confusion | ✅ Comprehensive |

## Failure Examples

### DMA Overlap Bug (Caught by Property Test)

```rust
// BUG: Forgot to check forward overlap
if prev_end > new_start { return Err(Overlap); }
// Missing: if new_end > next_start { return Err(Overlap); }
```

**Property test that catches this:**
```rust
prop_dma_no_overlaps_maintained // Adds mapping that overlaps with next
```

### BAR Misalignment Bug (Caught by Property Test)

```rust
// BUG: Simple addition without alignment
let addr = self.next_addr;
self.next_addr += size;
// Missing: Align to size boundary first
```

**Property test that catches this:**
```rust
prop_bar_natural_alignment // Verifies addr & (size - 1) == 0
```

### MSI-X State Bug (Caught by Property Test)

```rust
// BUG: Allowing reconfiguration while enabled
pub fn configure(&mut self, ...) {
    self.address = new_address; // Should check if enabled first!
}
```

**Property test that catches this:**
```rust
prop_msix_no_reconfig_enabled // Configure→Enable→Configure fails
```

## Future Enhancements

1. **Shrinking**: When a test fails, proptest shrinks the input to find minimal failing case
2. **Regression tests**: Failed cases can be added as fixed test cases
3. **Cross-validation**: Compare our implementation against reference (Cloud Hypervisor)
4. **Symbolic execution**: Prove properties hold for ALL inputs, not just samples

## Conclusion

The property tests provide **high confidence** that:
- Core VFIO primitives (DMA, BAR, MSI-X) work correctly
- Type safety prevents address confusion
- Invariants hold across all tested input ranges
- Edge cases are handled gracefully

This is crucial before live hardware testing, as VFIO bugs can:
- Crash the host kernel
- Corrupt host memory
- Hang the GPU
- Require reboot to recover

The property tests caught multiple bugs during development and continue to prevent regressions.
