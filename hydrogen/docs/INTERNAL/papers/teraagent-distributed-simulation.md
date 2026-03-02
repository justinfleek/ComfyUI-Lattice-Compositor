# TeraAgent: A Distributed Agent-Based Simulation Engine for Simulating Half a Trillion Agents

**Authors:** Lukas Johannes Breitwieser (ETH Zurich), Ahmad Hesam (TU Delft), Abdullah Giray Yağlıkçı (ETH Zurich), Mohammad Sadrosadati (ETH Zurich), Fons Rademakers (CERN), Onur Mutlu (ETH Zurich)

**arXiv:** 2509.24063v1 [cs.DC] 28 Sep 2025

---

## Abstract

Agent-based simulation is an indispensable paradigm for studying complex systems. These systems can comprise billions of agents, requiring the computing resources of multiple servers to simulate. Unfortunately, the state-of-the-art platform, BioDynaMo, does not scale out across servers due to its shared-memory-based implementation.

**TeraAgent** is a distributed agent-based simulation engine that overcomes this limitation.

**Key Challenge:** Exchange of agent information across servers is a major performance bottleneck.

**Solutions:**
1. **Tailored serialization mechanism** — allows agents to be accessed and mutated directly from the receive buffer
2. **Delta encoding** — leverages iterative nature of agent-based simulations to reduce data transfer

**Results:**
- **501.51 billion agents** simulated (84× improvement over state-of-the-art)
- **84,096 CPU cores** on Dutch National Supercomputer
- **110× faster serialization** (median), **37× faster deserialization**
- **3.5× reduction** in message size via delta encoding
- **8× more efficient** than Biocellion per CPU core
- **39× faster** in-situ visualization with ParaView

---

## 1. Introduction

### Agent-Based Modeling Fundamentals

Agent-based modeling is a bottom-up simulation method to study complex systems. The three-step structure:

1. **Define agents** — What does an agent represent? (e.g., a bird with position and velocity)
2. **Define behaviors** — How do agents interact? (e.g., collision avoidance, velocity alignment, flock centering)
3. **Define initial conditions** — Starting distribution, parameter values

**Two key characteristics:**
- **Local interaction** — Agents only interact with local environment (enables spatial partitioning)
- **Emergent behavior** — "The whole is more than the sum of its parts"

### Scale Requirements

| System | Agent Count |
|--------|-------------|
| Human cortex | ~86 billion neurons |
| Each neuron | Several hundred sub-agents |
| **Total** | **Hundreds of billions of agents** |

### BioDynaMo Limitations

BioDynaMo (state-of-the-art) only uses shared-memory parallelism (OpenMP):
- **Max:** ~2 billion agents on 1TB RAM server
- **No scale-out** across multiple servers
- **Poor MPI interoperability** with third-party tools (OpenLB, ParaView)
- **Limited hardware flexibility**

### TeraAgent Contributions

1. **Scale-out architecture** — Divide simulation space via spatial locality
2. **Tailored serialization** — Use objects directly from receive buffer with full mutability
3. **Delta encoding** — Compress communication using iterative nature of simulations
4. **Seamless scaling** — Same code runs on laptop → supercomputer

## 2. The Distributed Simulation Engine

### 2.1 Distribution Overview

**Spatial Partitioning:**
- Simulation space divided into partitioning boxes
- Each MPI rank owns a mutually exclusive volume
- Agents inside belong to that rank

**Three Main Operations per Iteration:**

1. **Aura Update** — Exchange boundary agents with neighbors
2. **Agent Migration** — Move agents that crossed partition boundaries  
3. **Load Balancing** — Redistribute partitions for uniform workload

```
┌─────────────────────────────────────────────┐
│           Simulation Space                   │
│  ┌──────────────┬──────────────┐            │
│  │   Rank 0     │   Rank 1     │            │
│  │              │              │            │
│  │    ●  ●      │      ●  ●    │            │
│  │  ●    ●      │    ●    ●    │            │
│  │      ════════════════       │  ← Aura    │
│  │    (boundary region)        │    region  │
│  └──────────────┴──────────────┘            │
└─────────────────────────────────────────────┘

Aura = agents within max_interaction_distance of boundary
```

### 2.2 Serialization

**Problem:** ROOT I/O (used in BioDynaMo) is a performance bottleneck.

**Observations:**
1. No pointer deduplication needed (BioDynaMo disallows shared pointers)
2. Deserialization is expensive (FlatBuffers shows zero-copy is possible)
3. Same endianness on supercomputers (skip conversion)
4. No schema evolution needed (data exists only during simulation)

**Design Principle:** "What you don't use, you don't pay for" (Stroustrup)

#### TeraAgent IO Algorithm

```cpp
// Objects form a tree structure (no shared pointers allowed)
// Nodes = contiguous heap-allocated memory blocks

struct SerializedBuffer {
    void* data;
    size_t size;
    size_t block_count;  // for deallocation tracking
};
```

**Serialization (In-Order Tree Traversal):**

```cpp
void serialize(RootObject* root, Buffer& output) {
    /*
     * 1. Traverse tree in-order
     * 2. Copy each memory block to buffer
     * 3. Replace pointers with sentinel (0x1)
     * 4. Replace vtable pointers with class ID
     */
    
    std::queue<void*> nodes;
    nodes.push(root);
    
    while (!nodes.empty()) {
        void* node = nodes.front();
        nodes.pop();
        
        // Get type info from vtable
        TypeInfo info = get_type_info(node);
        
        // Replace vtable with class ID (vtables differ across ranks)
        replace_vtable_with_class_id(node, info.class_id);
        
        // Copy memory block to buffer
        output.append(node, info.size);
        
        // Queue child nodes, mark pointers as 0x1
        for (Pointer& ptr : info.pointers) {
            if (ptr.value != nullptr) {
                nodes.push(ptr.value);
                ptr.value = (void*)0x1;  // sentinel
            }
        }
    }
}
```

**Deserialization (Single Pass, Zero Allocation):**

```cpp
RootObject* deserialize(Buffer& input, TypeID root_type) {
    /*
     * Key insight: Don't allocate new memory!
     * Use the receive buffer directly as object memory.
     * 
     * Steps (single traversal):
     * 1. Restore vtable pointers from class IDs
     * 2. Set pointer fields to next block in buffer
     * 3. Count blocks for deallocation tracking
     * 4. Return buffer start as root object pointer
     */
    
    void* cursor = input.data;
    void* end = input.data + input.size;
    size_t block_count = 0;
    
    while (cursor < end) {
        TypeInfo info = restore_vtable(cursor);
        block_count++;
        
        void* next_block = cursor + info.size;
        
        // Restore pointer fields
        for (Pointer& ptr : info.pointers) {
            if (ptr.value == (void*)0x1) {
                ptr.value = next_block;
                next_block += get_block_size(next_block);
            }
        }
        
        cursor = next_block;
    }
    
    // Register buffer for deallocation tracking
    register_delete_filter(input.data, input.size, block_count);
    
    // Return buffer as root object (zero copy!)
    return reinterpret_cast<RootObject*>(input.data);
}
```

**Mutability (The Illusion):**

```cpp
/*
 * Higher-level code doesn't know objects came from a buffer.
 * Full mutability is maintained:
 * 
 * - Change attribute values: Works directly
 * - Add to vector: If capacity exceeded, vector allocates
 *   new memory on heap, deallocates old (in buffer)
 * - The illusion holds because we intercept delete calls
 */

void intercept_delete(void* ptr) {
    // Check if ptr falls within any deserialized buffer
    for (auto& filter : delete_filters) {
        if (ptr >= filter.start && ptr < filter.end) {
            filter.delete_count++;
            
            // All blocks freed? Deallocate whole buffer
            if (filter.delete_count == filter.expected_count) {
                free(filter.buffer);
                remove_filter(filter);
            }
            return;  // Don't actually delete
        }
    }
    
    // Not in buffer, normal delete
    ::operator delete(ptr);
}
```

### 2.3 Data Transfer Minimization (Delta Encoding)

**Observation:** Agent attributes change gradually between iterations.
- Position: small displacement
- Type, diameter: often unchanged

**Delta Encoding Scheme:**

```cpp
struct DeltaReference {
    // Sender and receiver maintain identical reference
    SerializedBuffer reference;
    std::unordered_map<AgentID, size_t> agent_positions;
};

void send_with_delta(Message& msg, DeltaReference& ref) {
    /*
     * Steps:
     * 1. Reorder message to match reference agent ordering
     * 2. Insert placeholders for agents in ref but not in msg
     * 3. Append new agents at end
     * 4. XOR with reference (same values → zeros)
     * 5. Compress with LZ4 (zeros compress well)
     */
    
    // Step 1-3: Reorder and align
    Message aligned = align_to_reference(msg, ref);
    
    // Step 4: Compute delta
    Buffer delta(aligned.size);
    for (size_t i = 0; i < aligned.size; i++) {
        delta[i] = aligned.data[i] ^ ref.reference.data[i];
    }
    
    // Step 5: Compress (zeros from matching data compress well)
    Buffer compressed = lz4_compress(delta);
    
    MPI_Isend(compressed.data, compressed.size, ...);
}

void receive_with_delta(Buffer& compressed, DeltaReference& ref) {
    // Decompress
    Buffer delta = lz4_decompress(compressed);
    
    // Restore original by XOR with reference
    for (size_t i = 0; i < delta.size; i++) {
        delta[i] ^= ref.reference.data[i];
    }
    
    // Remove placeholders (defragment)
    Message msg = defragment(delta);
    
    // Deserialize using TeraAgent IO
    auto* agents = deserialize(msg, AgentContainer);
}
```

**Compression Results:**

| Stage | Compression Ratio |
|-------|-------------------|
| LZ4 alone | 3.0-5.2× |
| LZ4 + Delta | 3.3-18.2× (up to 3.5× additional) |

### 2.4 Implementation Details

#### Partitioning Grid
- Uses Sierra Toolkit (STK) from Trilinos
- Integrated with Zoltan2 for load balancing
- Exports to Exodus format (ParaView compatible)

#### Communication
```cpp
// Non-blocking point-to-point for latency hiding
MPI_Isend(...);
MPI_Irecv(...);
MPI_Probe(...);

// Speculative receives for regular neighbor patterns
// Large messages sent in batches to reduce buffer memory
```

#### Load Balancing

**Global (Zoltan2 RCB):**
```cpp
void global_balance() {
    // Weight = agent_count × last_iteration_runtime
    for (auto& box : partition_boxes) {
        box.weight = box.agent_count * box.last_runtime;
    }
    
    // Recursive Coordinate Bisection
    zoltan2.partition(partition_boxes, num_ranks);
    
    // May cause mass migration
    migrate_agents_to_new_owners();
}
```

**Diffusive (Local Exchange):**
```cpp
void diffusive_balance() {
    double local_avg = compute_neighbor_average_runtime();
    
    if (my_runtime > local_avg) {
        // Send boxes to faster neighbors
        for (auto& neighbor : slower_neighbors) {
            send_partition_boxes(neighbor, excess_boxes);
        }
    }
}
```

#### Unique Agent Identifiers

```cpp
// Local ID: ⟨index, reuse_counter⟩
// - Enables vector-based map (fast lookup)
// - Index reused when agent removed

// Global ID: ⟨rank, counter⟩  
// - rank = where agent was created
// - counter = strictly increasing
// - Constant throughout agent lifetime

// Translation happens only during serialization
// Global IDs generated on-demand (lazy)
```

### 2.5 Parallelization Modes

| Mode | Ranks | Threads | Use Case |
|------|-------|---------|----------|
| MPI Hybrid | 1 per NUMA domain | Many per rank | Best performance |
| MPI Only | 1 per CPU core | 1 per rank | MPI-only third-party tools |

**No recompilation needed to switch modes.**

---

## 3. Evaluation

### 3.1 Benchmark Simulations

Four simulations from BioDynaMo papers:
1. **Cell clustering** — Spatial sorting by cell type
2. **Cell proliferation** — Division and growth
3. **Epidemiology** — SIR disease spread
4. **Oncology** — Tumor spheroid growth

### 3.2 Experimental Setup

**System A (Snellius - Dutch National Supercomputer):**
- 2× AMD Genoa 9654 (96 cores each) per node
- 384 GB RAM per node
- InfiniBand: 200 Gbps (intra-rack), 100 Gbps (inter-rack)

**System B (Two-node cluster):**
- 4× Intel Xeon E7-8890 v3 (72 cores each) per node
- 504/1024 GB RAM
- Gigabit Ethernet

### 3.3 Comparison with BioDynaMo

**Single node, 10⁷ agents:**

| Mode | Slowdown vs OpenMP | Memory |
|------|-------------------|--------|
| MPI Hybrid | 4-9% | ~2× |
| MPI Only | 26-34% | Higher (cling overhead) |

**Exception:** Epidemiology simulation **2.8× faster** in MPI Hybrid due to reduced cross-NUMA traffic.

### 3.4 Comparison with Biocellion

**Cell clustering, 1.72 billion cells:**

| System | Runtime/iter | CPU Cores | Agent Updates/s/core |
|--------|--------------|-----------|---------------------|
| TeraAgent | 15.8s | 144 | **7.56×10⁵** |
| Biocellion | 4.46s | 4096 | 9.42×10⁴ |

**TeraAgent is 8× more efficient per CPU core.**

### 3.5 Scalability

**Strong Scaling (fixed problem size, more nodes):**

| Nodes | CPU Cores | Speedup |
|-------|-----------|---------|
| 1 | 192 | 1.0× |
| 2 | 384 | ~1.9× |
| 4 | 768 | ~3.6× |
| 8 | 1536 | ~6.5× |
| 16 | 3072 | ~8× (load imbalance) |

**Weak Scaling (10⁸ agents/node):**

| Nodes | CPU Cores | Agents | Runtime/iter |
|-------|-----------|--------|--------------|
| 1 | 192 | 10⁸ | baseline |
| 128 | 24,576 | 1.28×10¹⁰ | plateau reached |

### 3.6 Extreme-Scale Simulations

**Experiment 1: 102.4 Billion Agents**
- 128 Snellius nodes
- 24,576 CPU cores
- 40 TB memory
- **7.08 s/iteration**

**Experiment 2: 501.51 Billion Agents**
- 438 Snellius nodes
- 84,096 CPU cores (maximum permitted)
- 92 TB memory
- 147 s/iteration (optimizations disabled for memory)

### 3.7 Serialization Performance

**TeraAgent IO vs ROOT IO (4 nodes, 10⁸ agents):**

| Metric | Speedup |
|--------|---------|
| Simulation runtime | Up to 3.6× |
| Serialization (aura) | Up to 296× (median 110×) |
| Deserialization (aura) | Up to 73× (median 37×) |
| Message size | Equivalent |
| Memory | No increase |

### 3.8 Delta Encoding Performance

**With LZ4 compression as baseline:**

| Metric | LZ4 Only | LZ4 + Delta |
|--------|----------|-------------|
| Message size reduction | 3.0-5.2× | +1.1-3.5× additional |
| Distribution speedup | baseline | Up to 11× |
| Memory overhead | - | +3% (reference storage) |

**Trade-off:** Delta encoding reduces agent operation performance due to reordering. Benefits depend on interconnect bandwidth.

### 3.9 In-Situ Visualization (ParaView)

**Cell clustering, 10M agents, 10 iterations:**

| Configuration | Ranks | Threads | Speedup |
|---------------|-------|---------|---------|
| BioDynaMo (OpenMP) | 1 | 144 | 1× |
| TeraAgent (MPI Hybrid) | 4 | 36 | ~10× |
| TeraAgent (MPI Only) | 72 | 1 | **39×** |

ParaView scales primarily with rank count, not thread count.

---

## 4. Related Work

### Agent-Based Simulation Tools

To our knowledge, TeraAgent is the **only simulation platform capable of simulating 501.51 billion agents**. 

**Largest reported agent populations in literature:**

| Platform | Agent Count | Domain |
|----------|-------------|--------|
| **TeraAgent** | **501.51 billion** | General-purpose |
| Jon Parker [119] | 6 billion | Specialized epidemiological model |
| Biocellion [72] | 1.72 billion | Tissue modeling |

**Other distributed platforms exist but have not demonstrated extreme-scale simulations:**
- Repast HPC [33] — Parallel agent-based simulation
- D-MASON [34] — Distributed multi-agent simulation
- Large-scale 3D cell colony simulations [35]
- Chaste [100] — Computational physiology

### Serialization

Wide range of serialization libraries exist:

| Library | Notes |
|---------|-------|
| ROOT IO [20] | Outperforms others according to Blomer [14] |
| Protobuf [152] | Google's protocol buffers |
| HDF5 [58] | Hierarchical data format |
| Parquet [149] | Columnar storage |
| Avro [148] | Row-oriented serialization |

**MPI [106]** provides functionality to define derived data types, but targets use cases with **regular patterns** (e.g., last element of each row in a matrix). TeraAgent's agents are allocated on the heap with **irregular offsets** and therefore cannot use MPI's solution.

### Delta Encoding

Delta encoding [66] is a widely used concept to minimize data stored or transferred. TeraAgent applies it to aura updates of the agent-based workload (Section 2.3).

**Other applications of delta encoding:**
- Backups [21]
- File revision systems (git) [151]
- Network protocols [69, 102]
- Cache and memory compression [85, 120, 121, 168]
- Virtual machine migration [92, 144]

**Key finding:** We did not find explicit mention of delta encoding in the literature to accelerate distributed execution of agent-based simulations. This appears to be a **novel application** of the technique.

---

## 5. Conclusion and Future Work

This paper presents **TeraAgent**, a distributed simulation engine that addresses the scaling limitations of the state-of-the-art agent-based simulation platform, BioDynaMo.

### Key Achievements

1. **Extreme-scale simulations** — Half a trillion agents (501.51 billion)
2. **Reduced time-to-result** — By adding additional compute nodes
3. **Improved interoperability** — With third-party tools (ParaView 39× faster)
4. **Greater hardware flexibility** — Seamless laptop → supercomputer scaling

### Seamless Scaling

TeraAgent allows researchers to scale out their execution environment seamlessly:
- Laptops
- Workstations  
- Clouds
- Supercomputers

**No model code changes required** for scale-out (Section 3.4).

### Impact

These results clearly show the benefits of distributed computing capabilities. Researchers can leverage these performance improvements and gain new insights into complex systems by building models on an **unprecedented scale** that has not been possible before.

### Technical Contributions Summary

| Contribution | Improvement |
|--------------|-------------|
| Maximum agents simulated | 501.51 billion (84× over state-of-the-art) |
| Serialization speedup | 110× median (up to 296×) |
| Deserialization speedup | 37× median (up to 73×) |
| Delta encoding compression | Up to 3.5× message size reduction |
| ParaView visualization | 39× faster |
| Efficiency vs Biocellion | 8× per CPU core |

---

## Acknowledgments

- Dutch national e-infrastructure (SURF Cooperative, grant no. EINF-5667)
- CERN openlab for server access
- SAFARI Research Group industrial partners: Huawei, Intel, Microsoft, VMware

---

## References

Selected key references (179 total in paper):

- [17] Breitwieser et al. 2021. BioDynaMo: a modular platform for high-performance agent-based simulation. *Bioinformatics* 38(2), 453–460.
- [18] Breitwieser et al. 2023. High-Performance and Scalable Agent-Based Simulation with BioDynaMo. *PPoPP '23*, 174–188.
- [72] Kang et al. 2014. Biocellion: accelerating computer simulation of multicellular biological system models. *Bioinformatics* 30(21), 3101–3108.
- [106] MPI Forum. 1994. MPI: A Message-Passing Interface.
- [119] Parker. 2007. A flexible, large-scale, distributed agent based epidemic model. *Winter Simulation Conference*, 1543–1547.
- [142] Stroustrup. 1994. The design and evolution of C++. ("What you don't use you don't pay for")
- [150] FlatBuffers Project Team. FlatBuffers — access to serialized data without parsing/unpacking.

---

## Appendix: Algorithm Summary

### Core Algorithms Extracted

```
┌─────────────────────────────────────────────────────────────────┐
│                    TERAAGENT ALGORITHM INDEX                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  SERIALIZATION (Section 2.2)                                    │
│  ├── serialize()          — In-order tree traversal to buffer   │
│  ├── deserialize()        — Zero-copy buffer interpretation     │
│  └── intercept_delete()   — Maintain allocation illusion        │
│                                                                  │
│  DELTA ENCODING (Section 2.3)                                   │
│  ├── send_with_delta()    — XOR + LZ4 compression               │
│  └── receive_with_delta() — Decompress + restore from reference │
│                                                                  │
│  LOAD BALANCING (Section 2.4.5)                                 │
│  ├── global_balance()     — Zoltan2 RCB partitioning            │
│  └── diffusive_balance()  — Local neighbor exchange             │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Relevance to Hydrogen

These algorithms are relevant for:

1. **Distributed UI Rendering** — Delta encoding for incremental DOM updates
2. **Agent-Based UI Components** — Billion-scale UI element management
3. **Serialization Patterns** — Zero-copy patterns for high-performance data flow
4. **Load Balancing** — Distributing rendering workload across workers

