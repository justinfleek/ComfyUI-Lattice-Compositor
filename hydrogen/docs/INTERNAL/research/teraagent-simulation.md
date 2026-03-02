# TeraAgent: A Distributed Agent-Based Simulation Engine for Simulating Half a Trillion Agents

**arXiv:** 2509.24063  
**Authors:** Lukas Johannes Breitwieser, Ahmad Hesam, Abdullah Giray Yağlıkçı, Mohammad Sadrosadati, Fons Rademakers, Onur Mutlu (ETH Zurich, Delft, CERN)  
**Status:** IN_PROGRESS

---

## 1. Abstract

TeraAgent is a distributed agent-based simulation engine that enables extreme-scale simulations with half a trillion agents (501.51 billion). Key contributions:
- Scale-out architecture across multiple servers
- Tailored serialization mechanism (110× faster)
- Delta encoding for reduced data transfer (3.5×)
- 84× improvement over state-of-the-art (BioDynaMo)

**Results:**
- 250× more agents than BioDynaMo
- 8× higher agent update rate than Biocellion
- 39× improved visualization performance

---

## 2. Background

### 2.1 Agent-Based Simulation

Agent-based modeling follows three steps:
1. **Define Agent:** What does the agent represent? (e.g., bird with position, velocity)
2. **Define Behaviors:** Rules for agent interactions (e.g., collision avoidance, alignment)
3. **Define Initial Conditions:** Starting state of agents

### 2.2 Key Characteristics

1. **Local Interaction:** Agents only interact with local environment
2. **Emergent Behavior:** Complex patterns arise from simple rules

### 2.3 Existing Limitations

**BioDynaMo** (state-of-the-art):
- Shared-memory only (OpenMP)
- Max 1.7 billion agents on single server
- No distributed execution

---

## 3. TeraAgent Architecture

### 3.1 Scale-Out Design

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Server 1  │     │   Server 2  │     │   Server N  │
│  ┌─────────┐ │     │  ┌─────────┐ │     │  ┌─────────┐ │
│  │ Partition│────▶│─▶│ Partition│────▶│─▶│ Partition│ │
│  └─────────┘ │     │  └─────────┘ │     │  └─────────┘ │
└─────────────┘     └─────────────┘     └─────────────┘
        │                   │                   │
        └───────────────────┴───────────────────┘
                        │
                   MPI Exchange
```

### 3.2 Two Key Innovations

**1. Tailored Serialization:**
- Direct access to objects from receive buffer
- Maintains full mutability
- 110× faster serialization, 37× faster deserialization

**2. Delta Encoding:**
- Exploits iterative nature of agent-based simulations
- Agent attributes change gradually
- Up to 3.5× reduction in data transfer

---

## 4. Distribution Mechanism

### 4.1 Spatial Partitioning

```
Simulation Space:
┌────────────────────────────┐
│  Partition 1  │  Partition 2 │
│    (Server 1) │   (Server 2) │
├────────────────────────────┤
│  Partition 3  │  Partition 4 │
│    (Server 3) │   (Server 4) │
└────────────────────────────┘

Border regions: Agents migrate between partitions
```

### 4.2 Communication Patterns

1. **Agent Migration:** Moving agents between servers
2. **Aura Exchange:** Getting local environment for agent updates
3. **Delta Updates:** Sending only changed attributes

---

## 5. Performance Results

| Metric | BioDynaMo | TeraAgent | Improvement |
|--------|-----------|-----------|-------------|
| Max Agents | 1.7B | 501.51B | 250× |
| Agent Updates/sec/core | - | 8× Biocellion | 8× |
| Serialization | Baseline | 110× | 110× |
| Deserialization | Baseline | 37× | 37× |
| Data Transfer | Baseline | 3.5× reduction | 3.5× |
| Visualization | Baseline | 39× | 39× |

---

## 6. Key Definitions

1. **Agent-Based Simulation:** Bottom-up simulation where complex behavior emerges from simple agent rules
2. **Scale-Out:** Adding more servers to increase computational capacity
3. **Serialization:** Converting agent data structures to transferable format
4. **Delta Encoding:** Sending only changes from previous state
5. **Aura:** Local region around agent used for interaction

---

## 7. Relation to Hydrogen

### 7.1 Swarm Simulation

```purescript
-- Agent representation
data Agent state
  = Agent
      { id :: AgentId
      , position :: Point3D
      , velocity :: Vector3D
      , state :: state
      }

-- Distributed simulation
data DistributedSimulation
  = DistributedSimulation
      { partitions :: Map ServerId (Array (Agent state))
      , migrations :: Channel (Agent state)
      }
```

### 7.2 Spatial Partitioning

```purescript
partitionSpace ::
  Bounds3D ->
  Int ->                    -- Number of partitions
  Map PartitionId (Array AgentId)

getNeighbors ::
  AgentId ->
  PartitionId ->
  Array AgentId
```

---

## 8. Bibliography

1. Breitwieser et al. "TeraAgent: A Distributed Agent-Based Simulation Engine for Simulating Half a Trillion Agents" 2025

---

*Document generated: 2026-02-26*
