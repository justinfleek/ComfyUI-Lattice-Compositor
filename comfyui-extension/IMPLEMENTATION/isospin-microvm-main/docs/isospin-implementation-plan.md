# Isospin: VFIO GPU Passthrough for Firecracker v1.13

## Executive Summary

Firecracker v1.13 shipped PCI support in August 2025. The infrastructure for VFIO GPU passthrough is 80% complete. This spec details the remaining 20%: porting Cloud Hypervisor's VFIO implementation to Firecracker's architecture.

**Estimated effort:** 1500-2000 lines of Rust  
**Time to MVP:** 1 week aggressive, 2 weeks conservative  
**Dependencies:** `vfio-ioctls`, `vfio-bindings` (existing rust-vmm crates)

---

## Architecture Comparison

### What Firecracker v1.13 Has

```
src/vmm/src/pci/
├── bus.rs           # PciBus, PciRoot, PciConfigIo, PciConfigMmio
├── configuration.rs # PciConfiguration (Type 0 config space)
├── device.rs        # VirtioPciDevice (virtio-pci transport)
├── msix.rs          # MsixConfig, MsixTableEntry
├── mod.rs           # Module exports
└── pci_segment.rs   # PciSegment wrapper
```

**Key types:**
- `PciDevice` trait with `read_config_register()`, `write_config_register()`, `read_bar()`, `write_bar()`
- `PciBus` with `add_device(device_id, Arc<Mutex<dyn PciDevice>>)`
- `MsixConfig` for MSI-X interrupt management
- BAR allocation via `vm_allocator::AddressAllocator`

### What Cloud Hypervisor Has (to port)

```
pci/src/
├── vfio.rs          # VfioPciDevice, VfioCommon, VfioDmaMapping (2082 lines)
├── vfio_user.rs     # vfio-user protocol (optional, skip for MVP)
vmm/src/
├── device_manager.rs # add_vfio_device(), create_vfio_container()
```

**Key types to port:**
- `VfioPciDevice` - implements PciDevice trait for VFIO devices
- `VfioCommon` - shared VFIO logic (BAR allocation, interrupt routing)
- `VfioDmaMapping` - DMA mapping for VFIO container
- `Interrupt` - MSI/MSI-X/INTx interrupt state

---

## File-by-File Implementation Plan

### Phase 1: Core VFIO Device (Days 1-3)

#### 1.1 Add Dependencies to `Cargo.toml`

```toml
# src/vmm/Cargo.toml
[dependencies]
vfio-bindings = "0.4"
vfio-ioctls = "0.3"
```

#### 1.2 Create `src/vmm/src/pci/vfio_device.rs` (~800 lines)

This is the core VFIO PCI device implementation, ported from Cloud Hypervisor's `vfio.rs`.

```rust
// Copyright 2025 Isospin Authors
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::os::unix::io::AsRawFd;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use vfio_bindings::bindings::vfio::*;
use vfio_ioctls::{VfioContainer, VfioDevice, VfioIrq, VfioRegionInfoCap};
use vm_memory::{GuestAddress, GuestMemory};
use vmm_sys_util::eventfd::EventFd;

use crate::Vm;
use crate::pci::configuration::PciConfiguration;
use crate::pci::msix::{MsixConfig, MsixTableEntry};
use crate::pci::{PciDevice, BarReprogrammingParams};
use crate::vstate::interrupts::MsixVectorGroup;

/// Errors specific to VFIO PCI devices
#[derive(Debug, thiserror::Error, displaydoc::Display)]
pub enum VfioPciError {
    /// Failed to create VFIO container: {0}
    ContainerCreate(#[source] vfio_ioctls::VfioError),
    /// Failed to open VFIO device: {0}
    DeviceOpen(#[source] vfio_ioctls::VfioError),
    /// Failed to map DMA: {0}
    DmaMap(#[source] vfio_ioctls::VfioError),
    /// Failed to enable MSI-X: {0}
    EnableMsix(#[source] vfio_ioctls::VfioError),
    /// Failed to map MMIO region
    MmapRegion,
    /// Invalid BAR configuration
    InvalidBar,
    /// Memory allocation failed
    MemoryAllocation,
}

/// VFIO interrupt state (MSI, MSI-X, or legacy INTx)
pub struct VfioInterrupt {
    /// MSI-X configuration if supported
    pub msix: Option<VfioMsix>,
    /// MSI configuration if supported (fallback)
    pub msi: Option<VfioMsi>,
    /// Legacy INTx if needed
    pub intx: Option<VfioIntx>,
}

pub struct VfioMsix {
    pub config: MsixConfig,
    pub cap_offset: u32,
    pub interrupt_source_group: Arc<MsixVectorGroup>,
}

pub struct VfioMsi {
    pub enabled: bool,
    pub cap_offset: u32,
    pub num_vectors: u16,
}

pub struct VfioIntx {
    pub enabled: bool,
    pub interrupt_source_group: Option<Arc<dyn Send + Sync>>,
}

/// MMIO region that needs to be mapped to guest
#[derive(Clone)]
pub struct VfioMmioRegion {
    pub start: GuestAddress,
    pub length: u64,
    pub bar_index: u32,
    pub host_addr: u64,
}

/// A VFIO PCI device that can be passed through to the guest
pub struct VfioPciDevice {
    /// Device identifier
    id: String,
    /// Reference to the VM
    vm: Arc<Vm>,
    /// The underlying VFIO device
    device: Arc<VfioDevice>,
    /// VFIO container (shared across devices or dedicated for vIOMMU)
    container: Arc<VfioContainer>,
    /// PCI configuration space shadow
    configuration: PciConfiguration,
    /// MMIO regions for this device
    mmio_regions: Vec<VfioMmioRegion>,
    /// Interrupt state
    interrupt: VfioInterrupt,
    /// Whether device is attached to vIOMMU
    iommu_attached: bool,
    /// Guest PCI BDF
    bdf: u32,
    /// Path to the device in sysfs
    device_path: PathBuf,
    /// GPUDirect P2P clique ID (NVIDIA specific)
    x_nv_gpudirect_clique: Option<u8>,
}

impl VfioPciDevice {
    /// Create a new VFIO PCI device
    pub fn new(
        id: String,
        vm: Arc<Vm>,
        device: VfioDevice,
        container: Arc<VfioContainer>,
        bdf: u32,
        device_path: PathBuf,
        x_nv_gpudirect_clique: Option<u8>,
    ) -> Result<Self, VfioPciError> {
        let device = Arc::new(device);
        
        // Reset the device to known state
        device.reset();
        
        // Parse PCI capabilities to discover MSI/MSI-X support
        let (interrupt, configuration) = Self::parse_pci_config(&device, bdf)?;
        
        Ok(VfioPciDevice {
            id,
            vm,
            device,
            container,
            configuration,
            mmio_regions: Vec::new(),
            interrupt,
            iommu_attached: false,
            bdf,
            device_path,
            x_nv_gpudirect_clique,
        })
    }
    
    /// Parse PCI configuration space to discover capabilities
    fn parse_pci_config(
        device: &VfioDevice,
        bdf: u32,
    ) -> Result<(VfioInterrupt, PciConfiguration), VfioPciError> {
        // Read vendor/device ID
        let mut config_data = [0u8; 4];
        device.region_read(VFIO_PCI_CONFIG_REGION_INDEX, &mut config_data, 0);
        let vendor_id = u16::from_le_bytes([config_data[0], config_data[1]]);
        let device_id = u16::from_le_bytes([config_data[2], config_data[3]]);
        
        // Read class code
        device.region_read(VFIO_PCI_CONFIG_REGION_INDEX, &mut config_data, 8);
        let class_code = config_data[3];
        let subclass = config_data[2];
        let revision = config_data[0];
        
        // Create shadow configuration
        let configuration = PciConfiguration::new_type0(
            vendor_id,
            device_id,
            revision,
            pci::PciClassCode::Other,  // Will be overwritten
            &VfioSubclass(subclass),
            0, 0,
            None,
        );
        
        // Parse capabilities to find MSI-X/MSI
        let interrupt = Self::parse_capabilities(device, bdf)?;
        
        Ok((interrupt, configuration))
    }
    
    /// Walk PCI capability list to find MSI/MSI-X
    fn parse_capabilities(
        device: &VfioDevice,
        bdf: u32,
    ) -> Result<VfioInterrupt, VfioPciError> {
        let mut msix = None;
        let mut msi = None;
        
        // Read capabilities pointer (offset 0x34)
        let mut cap_ptr = [0u8; 1];
        device.region_read(VFIO_PCI_CONFIG_REGION_INDEX, &mut cap_ptr, 0x34);
        let mut offset = cap_ptr[0] as u32;
        
        while offset != 0 && offset < 0x100 {
            let mut cap_header = [0u8; 2];
            device.region_read(VFIO_PCI_CONFIG_REGION_INDEX, &mut cap_header, offset.into());
            let cap_id = cap_header[0];
            let next_cap = cap_header[1] as u32;
            
            match cap_id {
                0x11 => {
                    // MSI-X capability
                    let mut msix_ctrl = [0u8; 2];
                    device.region_read(
                        VFIO_PCI_CONFIG_REGION_INDEX,
                        &mut msix_ctrl,
                        (offset + 2).into(),
                    );
                    let table_size = (u16::from_le_bytes(msix_ctrl) & 0x7FF) + 1;
                    
                    // TODO: Create MsixConfig and interrupt source group
                    msix = Some(VfioMsix {
                        config: todo!("Create MsixConfig"),
                        cap_offset: offset,
                        interrupt_source_group: todo!("Create interrupt group"),
                    });
                }
                0x05 => {
                    // MSI capability
                    let mut msi_ctrl = [0u8; 2];
                    device.region_read(
                        VFIO_PCI_CONFIG_REGION_INDEX,
                        &mut msi_ctrl,
                        (offset + 2).into(),
                    );
                    let mmc = (u16::from_le_bytes(msi_ctrl) >> 1) & 0x7;
                    let num_vectors = 1 << mmc;
                    
                    msi = Some(VfioMsi {
                        enabled: false,
                        cap_offset: offset,
                        num_vectors,
                    });
                }
                _ => {}
            }
            
            offset = next_cap;
        }
        
        Ok(VfioInterrupt {
            msix,
            msi,
            intx: None,
        })
    }
    
    /// Allocate BARs for this device
    pub fn allocate_bars(
        &mut self,
        mmio64_allocator: &mut vm_allocator::AddressAllocator,
    ) -> Result<(), VfioPciError> {
        // Query each BAR region
        for bar_id in 0..VFIO_PCI_ROM_REGION_INDEX {
            if let Some(region) = self.device.get_region_info(bar_id) {
                if region.size == 0 {
                    continue;
                }
                
                // Read BAR type from config space
                let bar_offset = 0x10 + (bar_id * 4);
                let mut bar_value = [0u8; 4];
                self.device.region_read(
                    VFIO_PCI_CONFIG_REGION_INDEX,
                    &mut bar_value,
                    bar_offset.into(),
                );
                let flags = u32::from_le_bytes(bar_value);
                
                let is_64bit = (flags & 0x4) != 0;
                let is_prefetchable = (flags & 0x8) != 0;
                let is_io = (flags & 0x1) != 0;
                
                if is_io {
                    // Skip I/O BARs for now (GPUs don't use them)
                    continue;
                }
                
                // Allocate guest address for this BAR
                let guest_addr = mmio64_allocator
                    .allocate(None, region.size, Some(region.size))
                    .ok_or(VfioPciError::MemoryAllocation)?;
                
                // Update shadow config space with guest address
                self.configuration.add_pci_bar(
                    bar_id as usize,
                    guest_addr.raw_value(),
                    region.size,
                );
                
                self.mmio_regions.push(VfioMmioRegion {
                    start: guest_addr,
                    length: region.size,
                    bar_index: bar_id,
                    host_addr: 0, // Filled in during map_mmio_regions
                });
                
                // Skip next BAR if this is 64-bit
                if is_64bit {
                    // bar_id += 1 happens in loop, so we're fine
                }
            }
        }
        
        Ok(())
    }
    
    /// Map MMIO regions into guest address space
    pub fn map_mmio_regions(&mut self) -> Result<(), VfioPciError> {
        for region in &mut self.mmio_regions {
            // Get mmap info from VFIO
            let region_info = self.device
                .get_region_info(region.bar_index)
                .ok_or(VfioPciError::InvalidBar)?;
            
            // Check for sparse mmap capability
            let caps = self.device.get_region_caps(region.bar_index);
            let sparse_areas = Self::get_sparse_areas(&caps, region.length);
            
            for area in sparse_areas {
                // mmap the region from device
                let host_ptr = unsafe {
                    libc::mmap(
                        std::ptr::null_mut(),
                        area.size as usize,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_SHARED,
                        self.device.as_raw_fd(),
                        region_info.offset as i64 + area.offset as i64,
                    )
                };
                
                if host_ptr == libc::MAP_FAILED {
                    return Err(VfioPciError::MmapRegion);
                }
                
                region.host_addr = host_ptr as u64;
                
                // Create KVM memory region for this mapping
                let guest_addr = region.start.raw_value() + area.offset;
                self.vm.create_user_memory_region(
                    guest_addr,
                    area.size,
                    host_ptr as u64,
                    false,
                    false,
                )?;
                
                // Map to VFIO container for DMA
                if !self.iommu_attached {
                    unsafe {
                        self.container.vfio_dma_map(
                            guest_addr,
                            area.size,
                            host_ptr as u64,
                        )
                    }.map_err(VfioPciError::DmaMap)?;
                }
            }
        }
        
        Ok(())
    }
    
    fn get_sparse_areas(
        caps: &[VfioRegionInfoCap],
        region_size: u64,
    ) -> Vec<VfioRegionSparseMmapArea> {
        // Check for sparse mmap capability
        for cap in caps {
            if let VfioRegionInfoCap::SparseMmap(sparse) = cap {
                return sparse.areas.clone();
            }
        }
        
        // No sparse capability - map entire region
        vec![VfioRegionSparseMmapArea {
            offset: 0,
            size: region_size,
        }]
    }
    
    /// Enable MSI-X interrupts
    pub fn enable_msix(&mut self) -> Result<(), VfioPciError> {
        if let Some(msix) = &mut self.interrupt.msix {
            let mut fds: Vec<&EventFd> = Vec::new();
            
            // Collect eventfds from MSI-X config
            // TODO: Wire up actual eventfds from MsixConfig
            
            self.device
                .enable_msix(&fds)
                .map_err(VfioPciError::EnableMsix)?;
        }
        
        Ok(())
    }
    
    /// Get MMIO regions for bus registration
    pub fn mmio_regions(&self) -> &[VfioMmioRegion] {
        &self.mmio_regions
    }
}

// Implement the PciDevice trait for Firecracker's PCI bus
impl PciDevice for VfioPciDevice {
    fn write_config_register(
        &mut self,
        reg_idx: usize,
        offset: u64,
        data: &[u8],
    ) -> Option<Arc<std::sync::Barrier>> {
        let reg = (reg_idx * 4) as u32 + offset as u32;
        
        // Check if this is a BAR write - handle specially
        if (0x10..=0x24).contains(&reg) {
            // BAR reprogramming - update shadow and detect moves
            self.configuration.write_config_register(reg_idx, offset, data);
        }
        
        // Check for MSI-X control register writes
        if let Some(msix) = &mut self.interrupt.msix {
            if reg == msix.cap_offset + 2 && data.len() == 2 {
                let ctrl = u16::from_le_bytes([data[0], data[1]]);
                let enable = (ctrl >> 15) & 1 == 1;
                let mask = (ctrl >> 14) & 1 == 1;
                
                if enable && !mask {
                    let _ = self.enable_msix();
                }
            }
        }
        
        // Forward write to actual device
        self.device.region_write(
            VFIO_PCI_CONFIG_REGION_INDEX,
            data,
            reg.into(),
        );
        
        None
    }
    
    fn read_config_register(&mut self, reg_idx: usize) -> u32 {
        // For BARs, return our shadow values (guest addresses)
        if (4..=9).contains(&reg_idx) || reg_idx == 12 {
            return self.configuration.read_reg(reg_idx);
        }
        
        // For everything else, read from device
        let mut data = [0u8; 4];
        self.device.region_read(
            VFIO_PCI_CONFIG_REGION_INDEX,
            &mut data,
            ((reg_idx * 4) as u64).into(),
        );
        u32::from_le_bytes(data)
    }
    
    fn read_bar(&mut self, bar_index: usize, offset: u64, data: &mut [u8]) {
        // Find the corresponding VFIO region
        let bar_id = bar_index as u32;
        
        // Check if this is MSI-X table access
        if let Some(msix) = &self.interrupt.msix {
            // TODO: Handle MSI-X table reads via MsixConfig
        }
        
        // Read from device region
        self.device.region_read(bar_id, data, offset);
    }
    
    fn write_bar(&mut self, bar_index: usize, offset: u64, data: &[u8]) -> Option<Arc<std::sync::Barrier>> {
        let bar_id = bar_index as u32;
        
        // Check if this is MSI-X table access
        if let Some(msix) = &mut self.interrupt.msix {
            // TODO: Handle MSI-X table writes via MsixConfig
        }
        
        // Write to device region
        self.device.region_write(bar_id, data, offset);
        
        None
    }
}

// Helper subclass type
struct VfioSubclass(u8);
impl pci::PciSubclass for VfioSubclass {
    fn get_register_value(&self) -> u8 {
        self.0
    }
}

#[derive(Clone)]
struct VfioRegionSparseMmapArea {
    offset: u64,
    size: u64,
}
```

#### 1.3 Create `src/vmm/src/pci/vfio_container.rs` (~200 lines)

```rust
// Copyright 2025 Isospin Authors
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use vfio_ioctls::VfioContainer;
use vm_memory::{GuestMemory, GuestMemoryRegion};

use crate::vstate::memory::GuestMemoryMmap;

/// Manages VFIO container and DMA mappings
pub struct VfioContainerManager {
    /// The VFIO container
    container: Arc<VfioContainer>,
    /// Whether DMA is already mapped
    dma_mapped: bool,
}

impl VfioContainerManager {
    /// Create a new VFIO container
    pub fn new() -> Result<Self, vfio_ioctls::VfioError> {
        let container = VfioContainer::new(None)?;
        
        Ok(VfioContainerManager {
            container: Arc::new(container),
            dma_mapped: false,
        })
    }
    
    /// Get the container reference
    pub fn container(&self) -> Arc<VfioContainer> {
        Arc::clone(&self.container)
    }
    
    /// Map all guest memory regions for DMA
    pub fn map_guest_memory(
        &mut self,
        guest_mem: &GuestMemoryMmap,
    ) -> Result<(), vfio_ioctls::VfioError> {
        if self.dma_mapped {
            return Ok(());
        }
        
        for region in guest_mem.iter() {
            unsafe {
                self.container.vfio_dma_map(
                    region.start_addr().raw_value(),
                    region.len(),
                    region.as_ptr() as u64,
                )?;
            }
        }
        
        self.dma_mapped = true;
        Ok(())
    }
    
    /// Unmap guest memory from DMA
    pub fn unmap_guest_memory(
        &mut self,
        guest_mem: &GuestMemoryMmap,
    ) -> Result<(), vfio_ioctls::VfioError> {
        if !self.dma_mapped {
            return Ok(());
        }
        
        for region in guest_mem.iter() {
            self.container.vfio_dma_unmap(
                region.start_addr().raw_value(),
                region.len(),
            )?;
        }
        
        self.dma_mapped = false;
        Ok(())
    }
}

/// DMA mapping handler for VFIO container
/// Implements ExternalDmaMapping trait for memory hotplug support
pub struct VfioDmaMapping {
    container: Arc<VfioContainer>,
}

impl VfioDmaMapping {
    pub fn new(container: Arc<VfioContainer>) -> Self {
        VfioDmaMapping { container }
    }
    
    pub fn map(&self, iova: u64, gpa: u64, size: u64, host_addr: u64) -> Result<(), std::io::Error> {
        unsafe {
            self.container.vfio_dma_map(iova, size, host_addr)
        }.map_err(|e| std::io::Error::other(format!("VFIO DMA map failed: {e:?}")))
    }
    
    pub fn unmap(&self, iova: u64, size: u64) -> Result<(), std::io::Error> {
        self.container.vfio_dma_unmap(iova, size)
            .map_err(|e| std::io::Error::other(format!("VFIO DMA unmap failed: {e:?}")))
    }
}
```

#### 1.4 Update `src/vmm/src/pci/mod.rs`

```rust
// Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Copyright 2025 Isospin Authors
// SPDX-License-Identifier: Apache-2.0

pub mod bus;
pub mod common_config;
pub mod configuration;
pub mod device;
pub mod msix;
pub mod pci_segment;
pub mod vfio_device;      // NEW
pub mod vfio_container;   // NEW

// Re-exports
pub use vfio_device::{VfioPciDevice, VfioPciError, VfioMmioRegion};
pub use vfio_container::{VfioContainerManager, VfioDmaMapping};
```

---

### Phase 2: Device Manager Integration (Days 4-5)

#### 2.1 Update `src/vmm/src/pci_mngr.rs`

Add VFIO device management alongside existing VirtIO devices:

```rust
// Add to imports
use crate::pci::{VfioPciDevice, VfioContainerManager, VfioPciError};
use vfio_ioctls::VfioDevice;
use std::path::PathBuf;

// Add to PciDevices struct
#[derive(Debug, Default)]
pub struct PciDevices {
    pub pci_segment: Option<PciSegment>,
    pub virtio_devices: HashMap<(VirtioDeviceType, String), Arc<Mutex<VirtioPciDevice>>>,
    /// VFIO passthrough devices
    pub vfio_devices: HashMap<String, Arc<Mutex<VfioPciDevice>>>,  // NEW
    /// Shared VFIO container for non-vIOMMU devices
    vfio_container: Option<VfioContainerManager>,  // NEW
}

// Add to PciManagerError
#[derive(Debug, thiserror::Error, displaydoc::Display)]
pub enum PciManagerError {
    // ... existing variants ...
    /// VFIO error: {0}
    Vfio(#[from] VfioPciError),
    /// VFIO container error: {0}
    VfioContainer(#[source] vfio_ioctls::VfioError),
}

impl PciDevices {
    /// Attach a VFIO device for GPU passthrough
    pub fn attach_vfio_device(
        &mut self,
        vm: &Arc<Vm>,
        id: String,
        device_path: PathBuf,
        x_nv_gpudirect_clique: Option<u8>,
    ) -> Result<(), PciManagerError> {
        let pci_segment = self.pci_segment.as_ref().unwrap();
        let pci_device_bdf = pci_segment.next_device_bdf()?;
        
        // Get or create VFIO container
        let container = if let Some(ref manager) = self.vfio_container {
            manager.container()
        } else {
            let mut manager = VfioContainerManager::new()
                .map_err(PciManagerError::VfioContainer)?;
            
            // Map guest memory for DMA
            manager.map_guest_memory(&vm.guest_memory())
                .map_err(PciManagerError::VfioContainer)?;
            
            let container = manager.container();
            self.vfio_container = Some(manager);
            container
        };
        
        // Open the VFIO device
        let vfio_device = VfioDevice::new(&device_path, container.clone())
            .map_err(|e| PciManagerError::VfioContainer(e))?;
        
        // Create the PCI device wrapper
        let mut vfio_pci = VfioPciDevice::new(
            id.clone(),
            vm.clone(),
            vfio_device,
            container,
            pci_device_bdf.into(),
            device_path,
            x_nv_gpudirect_clique,
        )?;
        
        // Allocate BARs
        let mut resource_allocator = vm.resource_allocator();
        vfio_pci.allocate_bars(&mut resource_allocator.mmio64_memory)?;
        
        // Map MMIO regions
        vfio_pci.map_mmio_regions()?;
        
        let vfio_pci = Arc::new(Mutex::new(vfio_pci));
        
        // Add to PCI bus
        pci_segment
            .pci_bus
            .lock()
            .expect("Poisoned lock")
            .add_device(pci_device_bdf.device() as u32, vfio_pci.clone());
        
        // Register MMIO regions with bus
        {
            let device = vfio_pci.lock().expect("Poisoned lock");
            for region in device.mmio_regions() {
                vm.common.mmio_bus.insert(
                    vfio_pci.clone(),
                    region.start.raw_value(),
                    region.length,
                )?;
            }
        }
        
        self.vfio_devices.insert(id, vfio_pci);
        
        Ok(())
    }
    
    /// Get a VFIO device by ID
    pub fn get_vfio_device(&self, id: &str) -> Option<&Arc<Mutex<VfioPciDevice>>> {
        self.vfio_devices.get(id)
    }
}
```

---

### Phase 3: API Surface (Days 6-7)

#### 3.1 Create `src/vmm/src/vmm_config/vfio.rs`

```rust
// Copyright 2025 Isospin Authors
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use serde::{Deserialize, Serialize};

/// Configuration for a VFIO passthrough device
#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
pub struct VfioDeviceConfig {
    /// Unique identifier for the device
    pub device_id: String,
    /// Path to the device in sysfs (e.g., /sys/bus/pci/devices/0000:01:00.0)
    pub path: PathBuf,
    /// NVIDIA GPUDirect P2P clique ID (for multi-GPU direct communication)
    #[serde(default)]
    pub x_nv_gpudirect_clique: Option<u8>,
    /// Whether to attach to vIOMMU (creates dedicated VFIO container)
    #[serde(default)]
    pub iommu: bool,
}

/// Errors for VFIO device configuration
#[derive(Debug, thiserror::Error, displaydoc::Display)]
pub enum VfioConfigError {
    /// Device path does not exist: {0}
    PathNotFound(PathBuf),
    /// Device not bound to vfio-pci driver: {0}
    NotVfioBound(PathBuf),
    /// IOMMU group not accessible: {0}
    IommuGroupError(String),
    /// Device already configured: {0}
    AlreadyConfigured(String),
}

impl VfioDeviceConfig {
    /// Validate the device configuration
    pub fn validate(&self) -> Result<(), VfioConfigError> {
        // Check device path exists
        if !self.path.exists() {
            return Err(VfioConfigError::PathNotFound(self.path.clone()));
        }
        
        // Check device is bound to vfio-pci
        let driver_path = self.path.join("driver");
        if let Ok(link) = std::fs::read_link(&driver_path) {
            if !link.to_string_lossy().contains("vfio-pci") {
                return Err(VfioConfigError::NotVfioBound(self.path.clone()));
            }
        } else {
            return Err(VfioConfigError::NotVfioBound(self.path.clone()));
        }
        
        Ok(())
    }
}
```

#### 3.2 Add REST API endpoint

Update `src/api_server/parsed_request.rs` (or equivalent):

```rust
/// PUT /vfio-devices/{device_id}
pub struct VfioDeviceRequest {
    pub config: VfioDeviceConfig,
}

impl VfioDeviceRequest {
    pub fn parse(body: &[u8]) -> Result<Self, RequestError> {
        let config: VfioDeviceConfig = serde_json::from_slice(body)
            .map_err(|e| RequestError::SerdeJson(e))?;
        
        config.validate()?;
        
        Ok(VfioDeviceRequest { config })
    }
}
```

#### 3.3 Add CLI flag

Update `src/firecracker/src/main.rs`:

```rust
#[derive(Parser)]
struct Args {
    // ... existing args ...
    
    /// Pass through a VFIO device (format: path=/sys/bus/pci/devices/XXXX:XX:XX.X)
    #[arg(long = "device", value_parser = parse_vfio_device)]
    devices: Vec<VfioDeviceConfig>,
}

fn parse_vfio_device(s: &str) -> Result<VfioDeviceConfig, String> {
    // Parse "path=/sys/bus/pci/devices/0000:01:00.0,clique=0"
    let mut path = None;
    let mut clique = None;
    
    for part in s.split(',') {
        if let Some(p) = part.strip_prefix("path=") {
            path = Some(PathBuf::from(p));
        } else if let Some(c) = part.strip_prefix("clique=") {
            clique = Some(c.parse().map_err(|_| "Invalid clique ID")?);
        }
    }
    
    let path = path.ok_or("Missing path= parameter")?;
    let device_id = path.file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("vfio0")
        .to_string();
    
    Ok(VfioDeviceConfig {
        device_id,
        path,
        x_nv_gpudirect_clique: clique,
        iommu: false,
    })
}
```

---

### Phase 4: Interrupt Routing (Days 8-10)

The key integration point is wiring VFIO interrupts to KVM's irqfd mechanism.

#### 4.1 MSI-X Interrupt Setup

```rust
// In vfio_device.rs

impl VfioPciDevice {
    /// Set up MSI-X interrupt routing through KVM irqfd
    pub fn setup_msix_interrupts(&mut self, vm: &Vm) -> Result<(), VfioPciError> {
        let Some(msix) = &mut self.interrupt.msix else {
            return Ok(());
        };
        
        let num_vectors = msix.config.table_entries.len();
        let mut eventfds = Vec::with_capacity(num_vectors);
        
        for idx in 0..num_vectors {
            let eventfd = EventFd::new(0)
                .map_err(|_| VfioPciError::EnableMsix(vfio_ioctls::VfioError::new()))?;
            
            // Wire eventfd to KVM irqfd
            let entry = &msix.config.table_entries[idx];
            if !entry.masked() {
                let irq_routing = kvm_irq_routing_entry {
                    gsi: idx as u32,
                    type_: KVM_IRQ_ROUTING_MSI,
                    u: kvm_irq_routing_entry__bindgen_ty_1 {
                        msi: kvm_irq_routing_msi {
                            address_lo: entry.msg_addr_lo,
                            address_hi: entry.msg_addr_hi,
                            data: entry.msg_data,
                            ..Default::default()
                        },
                    },
                    ..Default::default()
                };
                
                vm.register_irqfd(&eventfd, idx as u32)?;
            }
            
            eventfds.push(eventfd);
        }
        
        // Enable MSI-X in VFIO device with collected eventfds
        let fd_refs: Vec<&EventFd> = eventfds.iter().collect();
        self.device.enable_msix(&fd_refs)
            .map_err(VfioPciError::EnableMsix)?;
        
        Ok(())
    }
}
```

---

## Integration Points Summary

### Firecracker Types to Reuse

| Type | Location | Purpose |
|------|----------|---------|
| `PciDevice` trait | `pci/bus.rs` | Device interface for PCI bus |
| `PciBus` | `pci/bus.rs` | Device enumeration and config space access |
| `MsixConfig` | `pci/msix.rs` | MSI-X table management |
| `PciConfiguration` | `pci/configuration.rs` | Shadow config space |
| `AddressAllocator` | `vm_allocator` crate | BAR address allocation |
| `MsixVectorGroup` | `vstate/interrupts.rs` | Interrupt vector management |

### Cloud Hypervisor Code to Port

| Type | Source | Lines | Complexity |
|------|--------|-------|------------|
| `VfioPciDevice` | `vfio.rs:1450-1992` | ~540 | High - core device |
| `VfioCommon` | `vfio.rs:478-1421` | ~940 | High - shared logic |
| `Interrupt` structs | `vfio.rs:100-260` | ~160 | Medium - interrupt state |
| `VfioDmaMapping` | `vfio.rs:1996-2082` | ~86 | Low - DMA helper |
| Device manager integration | `device_manager.rs:3674-3836` | ~160 | Medium |

### rust-vmm Crates

```toml
vfio-ioctls = "0.3"
vfio-bindings = "0.4"
```

Key APIs:
- `VfioContainer::new()` - Create container
- `VfioDevice::new(path, container)` - Open device
- `VfioDevice::region_read/write()` - Config/BAR access
- `VfioDevice::enable_msix()` - Wire interrupts
- `VfioContainer::vfio_dma_map()` - DMA mapping

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parse_vfio_capabilities() {
        // Mock a config space with MSI-X capability
    }
    
    #[test]
    fn test_bar_allocation() {
        // Test 64-bit BAR allocation
    }
    
    #[test]
    fn test_config_space_shadow() {
        // Verify BAR reads return guest addresses
    }
}
```

### Integration Tests

1. **Single GPU passthrough** - Boot VM with one GPU, verify `lspci` shows device
2. **Multi-GPU passthrough** - Multiple GPUs with GPUDirect P2P
3. **CUDA workload** - Run actual CUDA code in guest
4. **Interrupt latency** - Measure interrupt delivery time

### Hardware Test Matrix

| GPU | Driver | Test |
|-----|--------|------|
| RTX 5090 | vfio-pci | Basic passthrough |
| RTX 6000 Blackwell | vfio-pci | NVFP4 inference |
| H100 | vfio-pci | Multi-GPU P2P |

---

## Build & Run

```bash
# Build Isospin
cargo build --release --features vfio

# Prepare GPU (as root)
echo "0000:01:00.0" > /sys/bus/pci/drivers/nvidia/unbind
echo "vfio-pci" > /sys/bus/pci/devices/0000:01:00.0/driver_override
echo "0000:01:00.0" > /sys/bus/pci/drivers/vfio-pci/bind

# Run with GPU
./target/release/firecracker \
    --enable-pci \
    --device path=/sys/bus/pci/devices/0000:01:00.0 \
    --kernel vmlinux \
    --boot-args "console=ttyS0 pci=realloc"
```

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| MSI-X routing complexity | Medium | High | Cloud Hypervisor reference |
| Memory pinning issues | Low | High | Use existing VFIO patterns |
| BAR sizing edge cases | Medium | Medium | Extensive testing |
| NVIDIA driver compatibility | Low | High | Test on real hardware |
| Performance regression | Low | Medium | Benchmark against CH |

---

## Success Criteria

1. ✅ Boot Firecracker VM with `--device` flag
2. ✅ Guest sees GPU via `lspci`
3. ✅ NVIDIA driver loads in guest
4. ✅ `nvidia-smi` shows GPU
5. ✅ CUDA workload executes successfully
6. ✅ Boot time < 200ms with GPU attached
7. ✅ Interrupt latency < 10μs