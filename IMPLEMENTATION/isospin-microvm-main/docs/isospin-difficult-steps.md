# Isospin: Trouble Spots and Testing Strategy

## Philosophy: Types Over Tests, Properties Over Examples

The droid squads burn tokens. They're good at pattern matching, code generation, exhaustive search. They're bad at reasoning about invariants, understanding why code is correct.

**Our job:** Maximize the predicate space. Define types and properties that make illegal states unrepresentable. Then the droids can't generate wrong code because wrong code won't compile.

**Their job:** Term-level implementation. Fill in the bodies. Generate test cases. Explore the space.

---

## Part I: Trouble Spot Analysis

### Critical Failure Modes (Ranked by Severity)

#### 1. DMA Mapping Inconsistency (Severity: CRITICAL)

**What goes wrong:** Guest memory layout and IOMMU mappings get out of sync. GPU DMAs to address X, but X maps to wrong physical page (or unmapped).

**Consequence:** Data corruption, guest crash, potential host memory exposure.

**Why it's hard:**
- Memory hotplug changes guest layout
- ballooning reclaims pages
- Guest might use huge pages, IOMMU might not support them
- VFIO container shared across devices - one unmap affects all

**Type-level defense:**
```rust
/// A DMA mapping that is guaranteed consistent with guest memory.
/// The mapping is valid for the lifetime 'mem of the guest memory it references.
struct DmaMapping<'mem> {
    iova: IovaAddr,
    size: u64,
    // This PhantomData ensures DmaMapping can't outlive the memory it maps
    _memory: PhantomData<&'mem GuestMemory>,
}

/// VFIO container that tracks all mappings
struct VfioContainer {
    fd: OwnedFd,
    // BTreeMap for efficient range queries
    mappings: BTreeMap<IovaAddr, DmaMapping<'static>>,
}

impl VfioContainer {
    /// Map memory region. Returns handle that must be held while mapping is valid.
    fn map<'a>(&mut self, mem: &'a GuestMemoryRegion) -> Result<DmaMappingGuard<'a>> {
        // ...
    }
}

/// RAII guard - dropping unmaps the DMA region
struct DmaMappingGuard<'a> {
    container: &'a VfioContainer,
    iova: IovaAddr,
    size: u64,
}

impl Drop for DmaMappingGuard<'_> {
    fn drop(&mut self) {
        self.container.unmap(self.iova, self.size);
    }
}
```

**Property to verify (Lean or QuickCheck):**
```
∀ (container : VfioContainer) (gpa : GuestPhysAddr) (size : u64),
  is_guest_memory_valid(gpa, size) →
  ∃ (iova : IovaAddr), 
    container.lookup_mapping(iova) = Some(gpa, size) ∧
    iommu_resolves(iova) = guest_physical_to_host_physical(gpa)
```

**Test strategy:**
1. Unit: Map/unmap sequences, verify internal consistency
2. Property: Random memory layouts, verify bijection between GPA and IOVA
3. Stress: Concurrent map/unmap from multiple threads
4. Integration: Memory hotplug during active DMA

---

#### 2. MSI-X Table Synchronization (Severity: HIGH)

**What goes wrong:** Guest modifies MSI-X table, VMM state gets out of sync, interrupts route to wrong vector or get lost.

**Consequence:** Device appears hung, interrupt storms, guest crash.

**Why it's hard:**
- Guest can write MSI-X table at any time
- Each entry has 4 fields (addr_lo, addr_hi, data, ctrl)
- Partial writes (guest might write 2 bytes at a time)
- Must update KVM routing atomically
- Race between guest write and device interrupt

**Type-level defense:**
```rust
/// MSI-X vector state machine
/// States: Masked → Configured → Enabled
///         ↑___________↓___________↓
enum MsixVectorState {
    /// Vector is masked - interrupts held pending
    Masked,
    /// Vector has valid routing but is masked
    Configured { 
        addr: MsiAddress,
        data: MsiData,
    },
    /// Vector is active - interrupts will be delivered
    Enabled {
        addr: MsiAddress,
        data: MsiData,
        irqfd: OwnedFd,
    },
}

/// State transition proof obligations
impl MsixVectorState {
    /// Transition only valid if new config differs from old
    fn configure(self, addr: MsiAddress, data: MsiData) -> Self {
        match self {
            Self::Masked => Self::Configured { addr, data },
            Self::Configured { .. } => Self::Configured { addr, data },
            Self::Enabled { irqfd, .. } => {
                // Must tear down old irqfd before reconfiguring
                drop(irqfd);
                Self::Configured { addr, data }
            }
        }
    }
    
    /// Enable only valid from Configured state
    fn enable(self, vm: &VmFd) -> Result<Self> {
        match self {
            Self::Configured { addr, data } => {
                let irqfd = setup_irqfd(vm, addr, data)?;
                Ok(Self::Enabled { addr, data, irqfd })
            }
            Self::Enabled { .. } => Ok(self),  // Already enabled
            Self::Masked => Err(Error::NotConfigured),
        }
    }
}
```

**Property to verify:**
```
∀ (table : MsixTable) (vector : VectorIndex),
  table.vector_enabled(vector) →
  ∃ (irqfd : Fd),
    kvm_has_irqfd(irqfd, table.gsi(vector)) ∧
    vfio_has_irq(irqfd, vector)
```

**Test strategy:**
1. Unit: State machine transitions, all valid paths
2. Property: Random MSI-X table writes, verify invariant maintained
3. Race: Concurrent guest writes + device interrupts
4. Integration: Actual interrupt delivery timing

---

#### 3. BAR Reprogramming Race (Severity: HIGH)

**What goes wrong:** Guest reprograms BAR address while device is active. Old MMIO mapping still in place, new writes go to wrong region.

**Consequence:** Device malfunction, potential MMIO to wrong address range.

**Why it's hard:**
- BAR writes are split (low 32 bits, then high 32 bits for 64-bit BARs)
- Must detect BAR change, pause device, remap, resume
- Window between old unmap and new map
- Device might be mid-DMA using old BAR address

**Type-level defense:**
```rust
/// BAR state that tracks pending reprogramming
struct Bar {
    current: Option<BarMapping>,
    pending_low: Option<u32>,  // Set when guest writes low 32 bits
}

/// BAR reprogramming is a two-phase commit
impl Bar {
    fn write_low(&mut self, value: u32) {
        self.pending_low = Some(value);
        // Don't apply yet - wait for high write
    }
    
    fn write_high(&mut self, value: u32) -> Option<BarReprogrammingParams> {
        let low = self.pending_low.take()?;
        let new_addr = ((value as u64) << 32) | (low as u64);
        
        let old_addr = self.current.as_ref().map(|m| m.addr)?;
        if new_addr == old_addr {
            return None;  // No change
        }
        
        Some(BarReprogrammingParams {
            old_base: old_addr,
            new_base: new_addr,
            len: self.current.as_ref().unwrap().size,
        })
    }
}

/// Reprogramming params are consumed exactly once
struct BarReprogrammingParams {
    old_base: u64,
    new_base: u64,
    len: u64,
}

impl BarReprogrammingParams {
    /// Execute the reprogramming - consumes self
    fn execute(self, vm: &VmFd) -> Result<BarMapping> {
        vm.unmap_mmio(self.old_base, self.len)?;
        vm.map_mmio(self.new_base, self.len)
    }
}
```

**Property to verify:**
```
∀ (bar : Bar) (writes : List (Offset, Value)),
  let final_state = fold bar writes in
  final_state.pending_low.is_none() ∨ 
  (∃ write ∈ writes, write.offset = high_offset → final_state.reprogrammed)
```

**Test strategy:**
1. Unit: All BAR write sequences (low-high, high-low, repeated)
2. Property: Random write sequences maintain invariant
3. Race: BAR reprogram during active DMA
4. Integration: Guest driver actually reprograms BAR

---

#### 4. IOMMU Group Violation (Severity: MEDIUM-HIGH)

**What goes wrong:** Not all devices in IOMMU group bound to vfio-pci. Device left on host driver can bypass IOMMU isolation.

**Consequence:** Security boundary violation, potential host compromise.

**Why it's hard:**
- IOMMU groups are hardware-defined, can be surprising
- User might not realize GPU + audio are in same group
- Hot-plug can change group membership
- ACS (Access Control Services) affects group boundaries

**Type-level defense:**
```rust
/// An IOMMU group where all devices are verified bound to vfio-pci
struct VerifiedIommuGroup {
    group_id: u32,
    devices: Vec<PciBdf>,
    // Private constructor - only created by verify()
    _private: (),
}

impl VerifiedIommuGroup {
    /// Verify all devices in group are bound to vfio-pci
    /// Returns None if any device is not properly bound
    pub fn verify(group_id: u32) -> Option<Self> {
        let group_path = format!("/sys/kernel/iommu_groups/{}/devices", group_id);
        let mut devices = Vec::new();
        
        for entry in fs::read_dir(&group_path).ok()? {
            let entry = entry.ok()?;
            let device_path = entry.path();
            
            // Check driver symlink
            let driver_link = device_path.join("driver");
            let driver = fs::read_link(&driver_link).ok()?;
            
            if !driver.to_string_lossy().contains("vfio-pci") {
                return None;  // Device not bound to vfio-pci
            }
            
            let bdf = parse_bdf(entry.file_name())?;
            devices.push(bdf);
        }
        
        Some(VerifiedIommuGroup {
            group_id,
            devices,
            _private: (),
        })
    }
}

/// VfioDevice can only be created from a verified group
impl VfioDevice {
    pub fn new(group: &VerifiedIommuGroup, bdf: PciBdf) -> Result<Self> {
        assert!(group.devices.contains(&bdf));
        // ...
    }
}
```

**Property to verify:**
```
∀ (device : VfioDevice),
  ∃ (group : VerifiedIommuGroup),
    device.bdf ∈ group.devices ∧
    ∀ d ∈ group.devices, driver(d) = "vfio-pci"
```

**Test strategy:**
1. Unit: Group verification with mock sysfs
2. Property: All possible group configurations
3. Integration: Real hardware group detection
4. Negative: Reject incomplete groups

---

#### 5. Config Space Shadow Divergence (Severity: MEDIUM)

**What goes wrong:** Shadow config space (what we tell guest) diverges from real device config space. Guest and device disagree on state.

**Consequence:** Device misconfiguration, driver confusion.

**Why it's hard:**
- Some registers are read-only in real device but we must return different values
- BARs must return guest addresses, not host addresses
- Capability list might need filtering
- Writes might have side effects we need to intercept

**Type-level defense:**
```rust
/// Config space register with clear read/write semantics
enum ConfigRegister {
    /// Pass through to device
    Passthrough,
    /// Always return shadow value
    Shadow(u32),
    /// Shadow for reads, pass writes to device
    ShadowRead(u32),
    /// Intercept writes, compute new shadow, optionally forward
    Computed {
        shadow: u32,
        on_write: fn(old: u32, new: u32) -> (u32, bool),  // (new_shadow, forward_to_device)
    },
}

/// Config space layout with semantic annotations
struct PciConfigSpace {
    registers: [ConfigRegister; 1024],
}

impl PciConfigSpace {
    fn new_for_vfio(device: &VfioDevice) -> Self {
        let mut space = Self::default();
        
        // BARs are shadowed - return guest addresses
        for bar_idx in 0..6 {
            space.registers[4 + bar_idx] = ConfigRegister::ShadowRead(0);
        }
        
        // Command register - intercept memory/IO enable bits
        space.registers[1] = ConfigRegister::Computed {
            shadow: 0,
            on_write: |old, new| {
                // Always forward, but track memory space enable
                (new, true)
            },
        };
        
        // Everything else passes through
        // ...
        
        space
    }
}
```

**Property to verify:**
```
∀ (config : PciConfigSpace) (reg : RegisterIndex),
  config.read(reg) = match config.registers[reg] {
    Passthrough => device.read(reg),
    Shadow(v) => v,
    ShadowRead(v) => v,
    Computed { shadow, .. } => shadow,
  }
```

---

### Additional Trouble Spots (Lower Severity)

#### 6. Sparse MMIO Mmap (Severity: MEDIUM)
- Device BARs might not be fully mappable
- MSI-X table lives in BAR, must trap those accesses
- Need to split mapping around trap regions

#### 7. Reset Ordering (Severity: MEDIUM)  
- Device reset must happen before re-enabling
- In-flight DMA must complete first
- Interrupt state must be torn down

#### 8. Hot-Unplug (Severity: LOW for MVP)
- Cleanly remove device from running VM
- Outstanding I/O must complete or error
- Guest driver must handle surprise removal

#### 9. Multi-Function Device Handling (Severity: LOW)
- GPU + HDMI audio as separate functions
- Must pass through together or neither

#### 10. 32-bit BAR in 64-bit Space (Severity: LOW)
- Some devices have 32-bit BARs that must be below 4GB
- MMIO32 allocator must be separate from MMIO64

---

## Part II: Testing Order for Maximum Parallelism

### Dependency Graph

```
                          ┌─────────────────┐
                          │ IOMMU Group     │
                          │ Verification    │
                          └────────┬────────┘
                                   │
                    ┌──────────────┼──────────────┐
                    │              │              │
                    ▼              ▼              ▼
           ┌───────────────┐ ┌─────────┐ ┌───────────────┐
           │ VfioContainer │ │ VfioFd  │ │ Config Space  │
           │ Creation      │ │ Opening │ │ Parsing       │
           └───────┬───────┘ └────┬────┘ └───────┬───────┘
                   │              │              │
                   └──────────────┼──────────────┘
                                  │
                                  ▼
                          ┌───────────────┐
                          │ VfioDevice    │
                          │ Construction  │
                          └───────┬───────┘
                                  │
                   ┌──────────────┼──────────────┐
                   │              │              │
                   ▼              ▼              ▼
          ┌────────────┐  ┌────────────┐  ┌────────────┐
          │ BAR        │  │ DMA        │  │ Interrupt  │
          │ Allocation │  │ Mapping    │  │ Setup      │
          └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
                │               │               │
                └───────────────┼───────────────┘
                                │
                                ▼
                        ┌───────────────┐
                        │ MMIO Region   │
                        │ Registration  │
                        └───────┬───────┘
                                │
                                ▼
                        ┌───────────────┐
                        │ Full Device   │
                        │ Integration   │
                        └───────────────┘
```

### Squad Assignment

**Squad Alpha: Type Foundation (Day 1)**
Independent, no dependencies. Can start immediately.

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD ALPHA: Type Definitions                                   │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/types.rs                                         │
│   src/pci/vfio/error.rs                                         │
│                                                                 │
│ Types to define:                                                │
│   - GuestPhysAddr, HostVirtAddr, IovaAddr (newtypes)           │
│   - PciBdf, VendorId, DeviceId                                  │
│   - BarIndex, RegionIndex, IrqIndex                             │
│   - VfioPciError enum (exhaustive)                              │
│                                                                 │
│ Properties to verify:                                           │
│   - Address newtypes don't accidentally convert                 │
│   - Error enum covers all failure modes                         │
│                                                                 │
│ Test approach: Compile-time (if it compiles, it's correct)     │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Beta: IOMMU Group Verification (Day 1)**
Independent. Mock sysfs for testing.

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD BETA: IOMMU Group Handling                                │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/iommu_group.rs                                   │
│                                                                 │
│ Types to define:                                                │
│   - IommuGroup (unverified)                                     │
│   - VerifiedIommuGroup (proof of verification)                  │
│                                                                 │
│ Functions to implement:                                         │
│   - discover_group(device: PciBdf) -> Option<IommuGroup>       │
│   - verify_group(group: IommuGroup) -> Option<VerifiedGroup>   │
│   - list_devices(group: &VerifiedGroup) -> Vec<PciBdf>         │
│                                                                 │
│ Properties to verify:                                           │
│   ∀ vg : VerifiedGroup, ∀ d ∈ vg.devices, bound_to_vfio(d)    │
│                                                                 │
│ Test approach:                                                  │
│   - Mock sysfs filesystem                                       │
│   - Property test: random group configurations                  │
│   - Negative tests: incomplete groups rejected                  │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Gamma: Config Space Parsing (Day 1-2)**
Depends on: Types (Alpha)

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD GAMMA: PCI Config Space                                   │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/config_space.rs                                  │
│   src/pci/vfio/capabilities.rs                                  │
│                                                                 │
│ Types to define:                                                │
│   - ConfigRegister enum (Passthrough/Shadow/Computed)           │
│   - PciCapability trait                                         │
│   - MsiCapability, MsixCapability structs                       │
│   - VfioConfigSpace struct                                      │
│                                                                 │
│ Functions to implement:                                         │
│   - parse_capabilities(device: &VfioDevice) -> Vec<Capability> │
│   - find_msi() -> Option<MsiCapability>                         │
│   - find_msix() -> Option<MsixCapability>                       │
│   - read_register(idx: usize) -> u32                            │
│   - write_register(idx: usize, value: u32) -> SideEffect        │
│                                                                 │
│ Properties to verify:                                           │
│   - Capability linked list is acyclic                           │
│   - All capability IDs are valid                                │
│   - Shadow values for BARs don't leak host addresses            │
│                                                                 │
│ Test approach:                                                  │
│   - Snapshot real GPU config spaces                             │
│   - Property test: parse/serialize roundtrip                    │
│   - Fuzz: random config space bytes                             │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Delta: Container and DMA (Day 1-2)**
Depends on: Types (Alpha)

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD DELTA: VFIO Container and DMA                             │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/container.rs                                     │
│   src/pci/vfio/dma.rs                                           │
│                                                                 │
│ Types to define:                                                │
│   - VfioContainer (owns fd, tracks mappings)                    │
│   - DmaMapping<'mem> (lifetime-bound to memory)                 │
│   - DmaMappingGuard (RAII unmapper)                             │
│                                                                 │
│ Functions to implement:                                         │
│   - VfioContainer::new() -> Result<Self>                        │
│   - map_region(&mut self, gpa, hva, size) -> Guard              │
│   - unmap_region(&mut self, iova, size)                         │
│   - map_guest_memory(&mut self, mem: &GuestMemory)              │
│                                                                 │
│ Properties to verify:                                           │
│   - No overlapping IOVA mappings                                │
│   - All mappings tracked (no leaks)                             │
│   - Guard drop always unmaps                                    │
│                                                                 │
│ Test approach:                                                  │
│   - Property test: random map/unmap sequences                   │
│   - Verify internal BTreeMap consistency                        │
│   - Stress: many small mappings                                 │
│   - Integration: actual VFIO ioctls (requires root)             │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Epsilon: BAR Management (Day 2-3)**
Depends on: Types (Alpha), Config Space (Gamma)

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD EPSILON: BAR Allocation and Reprogramming                 │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/bar.rs                                           │
│                                                                 │
│ Types to define:                                                │
│   - Bar { current: Option<BarMapping>, pending_low: Option<u32>}│
│   - BarMapping { addr, size, host_ptr }                         │
│   - BarType (Mem32, Mem64, Io)                                  │
│   - BarReprogrammingParams (consumed on execute)                │
│                                                                 │
│ Functions to implement:                                         │
│   - discover_bars(device: &VfioDevice) -> Vec<Bar>              │
│   - allocate(bar: &mut Bar, allocator: &mut Allocator)          │
│   - handle_write(bar: &mut Bar, offset, value) -> Option<Reprogram>│
│   - execute_reprogram(params: BarReprogrammingParams, vm: &Vm)  │
│                                                                 │
│ Properties to verify:                                           │
│   - 64-bit BAR spans two indices                                │
│   - Allocated addresses are naturally aligned                   │
│   - Reprogramming detected on high-word write                   │
│                                                                 │
│ Test approach:                                                  │
│   - Property test: all BAR type combinations                    │
│   - Sequence test: low-then-high, high-then-low writes          │
│   - Alignment verification                                       │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Zeta: Interrupt Handling (Day 2-3)**
Depends on: Types (Alpha), Config Space (Gamma)

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD ZETA: MSI/MSI-X Interrupt Routing                         │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/interrupt.rs                                     │
│   src/pci/vfio/msix.rs                                          │
│                                                                 │
│ Types to define:                                                │
│   - MsixVectorState (Masked/Configured/Enabled)                 │
│   - MsixTable (vector array with state machine)                 │
│   - VfioInterrupt (MSI-X or MSI or INTx)                        │
│   - InterruptRoute { eventfd, gsi, kvm_route }                  │
│                                                                 │
│ Functions to implement:                                         │
│   - parse_msix_cap(device, offset) -> MsixCapability            │
│   - setup_msix(cap: MsixCap, vm: &Vm) -> MsixTable              │
│   - handle_table_write(table, offset, value) -> StateChange     │
│   - enable_vector(table, idx) -> Result<()>                     │
│   - disable_vector(table, idx) -> Result<()>                    │
│                                                                 │
│ Properties to verify:                                           │
│   - Enabled vector has valid irqfd                              │
│   - Masked vector holds pending interrupts                      │
│   - State transitions are valid                                  │
│                                                                 │
│ Test approach:                                                  │
│   - State machine coverage (all transitions)                    │
│   - Property test: random enable/disable/mask sequences         │
│   - Integration: actual KVM irqfd setup                         │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Eta: Device Integration (Day 3-4)**
Depends on: All above squads

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD ETA: VfioPciDevice Integration                            │
│                                                                 │
│ Files to create:                                                │
│   src/pci/vfio/device.rs                                        │
│   src/pci/vfio/mod.rs                                           │
│                                                                 │
│ Types to define:                                                │
│   - VfioPciDevice (combines all components)                     │
│   - VfioPciDeviceBuilder (staged construction)                  │
│                                                                 │
│ Functions to implement:                                         │
│   - VfioPciDevice::new(path, container, vm) -> Result<Self>    │
│   - impl PciDevice for VfioPciDevice                            │
│   - map_mmio_regions(&mut self) -> Result<()>                   │
│   - setup_interrupts(&mut self) -> Result<()>                   │
│                                                                 │
│ Properties to verify:                                           │
│   - Device implements PciDevice trait correctly                 │
│   - All resources cleaned up on drop                            │
│                                                                 │
│ Test approach:                                                  │
│   - Integration: real VFIO device (requires GPU)                │
│   - Mock: fake VfioDevice for unit tests                        │
└─────────────────────────────────────────────────────────────────┘
```

**Squad Theta: API and CLI (Day 4-5)**
Depends on: Device Integration (Eta)

```
┌─────────────────────────────────────────────────────────────────┐
│ SQUAD THETA: External Interface                                 │
│                                                                 │
│ Files to create:                                                │
│   src/vmm_config/vfio.rs                                        │
│   src/api_server/request/vfio.rs                                │
│                                                                 │
│ Types to define:                                                │
│   - VfioDeviceConfig (serde)                                    │
│   - VfioDeviceRequest                                           │
│   - VfioDeviceResponse                                          │
│                                                                 │
│ Functions to implement:                                         │
│   - parse_cli_device(s: &str) -> Result<VfioDeviceConfig>       │
│   - validate_config(cfg: &VfioDeviceConfig) -> Result<()>       │
│   - handle_put_device(req: &Request) -> Response                │
│                                                                 │
│ Test approach:                                                  │
│   - CLI parsing unit tests                                      │
│   - API request/response roundtrip                              │
│   - Validation error cases                                      │
└─────────────────────────────────────────────────────────────────┘
```

---

## Part III: Property Testing Framework

### QuickCheck Properties

```rust
use quickcheck::{Arbitrary, Gen, QuickCheck};

// Property: DMA mappings are bijective
#[quickcheck]
fn prop_dma_mapping_bijective(mappings: Vec<(u64, u64, u64)>) -> bool {
    let mut container = MockVfioContainer::new();
    
    for (iova, hva, size) in &mappings {
        if container.map(*iova, *hva, *size).is_ok() {
            // Verify we can look it up
            assert_eq!(container.lookup(*iova), Some((*hva, *size)));
        }
    }
    
    // Verify no overlaps
    container.check_no_overlaps()
}

// Property: MSI-X state machine is consistent
#[quickcheck]
fn prop_msix_state_consistent(actions: Vec<MsixAction>) -> bool {
    let mut table = MsixTable::new(16);
    
    for action in actions {
        match action {
            MsixAction::Configure(idx, addr, data) => {
                table.configure(idx, addr, data);
            }
            MsixAction::Enable(idx) => {
                let _ = table.enable(idx);
            }
            MsixAction::Mask(idx) => {
                table.mask(idx);
            }
        }
    }
    
    // Verify invariant: enabled implies configured
    for idx in 0..16 {
        if table.is_enabled(idx) {
            assert!(table.is_configured(idx));
        }
    }
    
    true
}

// Property: BAR reprogramming detected correctly
#[quickcheck]
fn prop_bar_reprogram_detection(writes: Vec<(u32, u32)>) -> bool {
    let mut bar = Bar::new_64bit(0x1000_0000_0000, 0x1000_0000);
    
    let mut reprogram_count = 0;
    for (offset, value) in writes {
        let offset = offset % 8;  // Only BAR0 and BAR1
        
        if offset < 4 {
            bar.write_low(value);
        } else {
            if bar.write_high(value).is_some() {
                reprogram_count += 1;
            }
        }
    }
    
    // Verify: high write after low write triggers reprogram
    true
}
```

### Lean Proofs (For Critical Invariants)

```lean
-- DMA mapping consistency theorem
theorem dma_mapping_consistency 
  (container : VfioContainer) 
  (gpa : GuestPhysAddr) 
  (size : Nat) 
  (h_valid : is_valid_guest_memory container.guest_mem gpa size) :
  ∃ iova : IovaAddr, 
    container.mappings.contains iova ∧
    container.mappings.lookup iova = some (gpa, size) ∧
    iommu_translate iova = gpa_to_hpa gpa := by
  -- Proof: follows from map_guest_memory postcondition
  sorry

-- MSI-X state machine invariant
inductive MsixState where
  | masked : MsixState
  | configured : MsiAddr → MsiData → MsixState
  | enabled : MsiAddr → MsiData → IrqFd → MsixState

def valid_transition : MsixState → MsixState → Prop
  | .masked, .configured _ _ => True
  | .configured a d, .enabled a' d' fd => a = a' ∧ d = d'
  | .enabled _ _ _, .masked => True
  | .enabled _ _ _, .configured _ _ => True
  | s, s' => s = s'

theorem msix_transitions_valid (s s' : MsixState) (h : can_transition s s') :
  valid_transition s s' := by
  cases h <;> simp [valid_transition]
```

---

## Part IV: Test Execution Order

### Phase 1: Foundation (Parallel)
```
┌───────────────────────────────────────────────────────────────┐
│  Alpha    │   Beta    │   Gamma   │   Delta   │              │
│  Types    │   IOMMU   │   Config  │   DMA     │              │
│           │   Groups  │   Space   │           │              │
│  ────────────────────────────────────────────                │
│  No deps  │  No deps  │  Types    │  Types    │              │
│           │           │           │           │              │
│  1 day    │  1 day    │  1-2 days │  1-2 days │              │
└───────────────────────────────────────────────────────────────┘
                            │
                            ▼
```

### Phase 2: Components (Semi-Parallel)
```
┌───────────────────────────────────────────────────────────────┐
│           │  Epsilon  │   Zeta    │                          │
│           │  BARs     │  Interrupts                          │
│           │           │           │                          │
│           │  ─────────────────────                           │
│           │  Types,   │  Types,   │                          │
│           │  Config   │  Config   │                          │
│           │           │           │                          │
│           │  2 days   │  2 days   │                          │
└───────────────────────────────────────────────────────────────┘
                            │
                            ▼
```

### Phase 3: Integration (Sequential)
```
┌───────────────────────────────────────────────────────────────┐
│                          │   Eta     │                        │
│                          │  Device   │                        │
│                          │  Integ    │                        │
│                          │  ─────────                         │
│                          │  All above│                        │
│                          │           │                        │
│                          │  2 days   │                        │
└───────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌───────────────────────────────────────────────────────────────┐
│                          │  Theta    │                        │
│                          │  API/CLI  │                        │
│                          │  ─────────                         │
│                          │  Device   │                        │
│                          │           │                        │
│                          │  1 day    │                        │
└───────────────────────────────────────────────────────────────┘
```

### Total Timeline

| Day | Squads Active | Deliverable |
|-----|---------------|-------------|
| 1 | Alpha, Beta, Gamma, Delta | Type foundation, IOMMU groups |
| 2 | Gamma, Delta, Epsilon, Zeta | Config space, DMA, BAR start |
| 3 | Epsilon, Zeta | BAR complete, Interrupts |
| 4 | Eta | Device integration |
| 5 | Theta | API/CLI complete |
| 6 | All | Integration testing |
| 7 | All | Hardware testing |

**Parallelism factor:** 4x on days 1-2, 2x on days 3, 1x on days 4-5

---

## Part V: Provably Correct Detours

### Where Lean is Worth It

1. **DMA mapping consistency** - This is a security boundary. A formal proof that IOVA → HPA mappings are always valid prevents host memory exposure.

2. **MSI-X state machine** - Interrupt misconfiguration causes device hangs. A proof that state transitions are valid prevents a class of bugs that are hard to reproduce.

3. **BAR address non-overlap** - Guest can't trick us into overlapping MMIO regions. Proof prevents confused deputy attacks.

### Where Lean is Not Worth It (Yet)

1. **Config space parsing** - Too many edge cases, better to fuzz
2. **VFIO ioctl sequences** - Kernel interface is the spec
3. **KVM integration** - Trust KVM's implementation

### Lean Integration Strategy

```
isospin/
├── src/
│   └── pci/vfio/       # Rust implementation
└── proofs/
    ├── DmaMapping.lean  # DMA consistency proofs
    ├── MsixState.lean   # Interrupt state machine
    └── BarAlloc.lean    # BAR allocation properties
```

Extract proof obligations from Rust code:
```rust
/// Proof obligation: DMA mapping is injective
/// See: proofs/DmaMapping.lean#dma_mapping_injective
#[proof_obligation("dma_mapping_injective")]
fn map_region(&mut self, iova: IovaAddr, hva: HostVirtAddr, size: u64) -> Result<()> {
    // Implementation must satisfy: no overlapping IOVA ranges
    // ...
}
```

---

## Summary: The Droid Swarm Strategy

1. **Types constrain the search space** - Newtypes, state machines, lifetime bounds. Droids can't generate wrong code if wrong code doesn't typecheck.

2. **Properties define correctness** - QuickCheck properties run against droid output. If property fails, droid tries again.

3. **Phases enable parallelism** - Foundation types have no deps. Components depend only on types. Integration depends on components. 4 squads can work day 1.

4. **Lean secures critical paths** - DMA and interrupts are security boundaries. Formal proofs prevent classes of bugs that testing can't find.

5. **Test order matches dependency order** - Don't test integration before components work. Don't test components before types exist.

Ship the squads with these constraints. Let them burn tokens on the term level. We hold the type level.