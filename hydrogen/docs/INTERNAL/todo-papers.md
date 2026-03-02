# Paper Implementation TODO

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // papers // implementation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Generated:** 2026-02-26
**Total Papers:** 190+
**Target:** Implement insights from ~95 papers (50%)
**Status:** PLANNING

## Document Structure

- Section 1: Schema Foundation (P0)
- Section 2: Core Papers by Priority
- Section 3: Papers Requiring Fetch (arXiv links)
- Section 4: Papers Claude Can Summarize (has training knowledge)
- Section 5: Implementation Checklist

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 1: Schema Foundation Tasks (P0)

These must be implemented FIRST. Everything else depends on them.

### 1.1 GPUStorable Typeclass
- [ ] Define `GPUStorable` in `Hydrogen.Schema.GPU.Storable`
- [ ] Implement for all existing bounded types (UnitInterval, Byte, Degrees, etc.)
- [ ] Lean4 proof: `deserialize (serialize x) = x`
- [ ] Define memory alignment rules matching WebGPU spec
- [ ] Test roundtrip for Color, Point3D, Transform3D

### 1.2 Identified Wrapper (UUID5 Temporal Identity)
- [ ] Define `Identified a` in `Hydrogen.Schema.Identity.Temporal`
- [ ] UUID5 generation from content hash
- [ ] Generation counter for cache invalidation
- [ ] Lean4 proof: determinism (same content = same UUID)
- [ ] Integration with existing `Hydrogen.Schema.Identity`

### 1.3 Patch/Diff System
- [ ] Define `Patch a` ADT in `Hydrogen.Schema.Diff.Patch`
- [ ] `NoChange`, `Replace`, `UpdateField`, `ApplyTransform`, `Composite`
- [ ] Serializable patches (binary format)
- [ ] Patch application function
- [ ] Lean4 proof: `apply (diff old new) old = new`

### 1.4 Hierarchical Groups
- [ ] Define `Group a` in `Hydrogen.Schema.Spatial.Group`
- [ ] Shared transforms for members
- [ ] Bounding volume (AABB) for culling
- [ ] Nested groups support
- [ ] Integration with existing Spatial module

### 1.5 Prioritized/Utility Metadata
- [ ] Define `Prioritized a` in `Hydrogen.Schema.Allocation.Priority`
- [ ] Utility score (UnitInterval)
- [ ] Resource budget tracking
- [ ] LRU timestamp
- [ ] Dependency graph (what breaks if removed)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 2: Core Papers by Priority

### Priority 0: MUST IMPLEMENT (Foundational)

#### Graded Monads & Formal Verification (Section 6, 5)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| Coeffects: Context-Dependent Computation | ICFP 2014 | [ ] | Foundation for co-effect tracking |
| Granule Language | ICFP 2019 | [ ] | Graded modal types implementation |
| NumFuzz: Rounding Error Analysis | 2405.04612 | [ ] | Float error bounds via graded monad |
| Bean: Backward Error Analysis | 2501.14550 | [ ] | Graded coeffects for numerical code |
| Flocq: Floating-Point in Coq | 1106.3448 | [ ] | Formal FP proofs |

#### Constraint Solving (Section 20)
| Paper | Source | Status | Why Critical |
|-------|--------|--------|--------------|
| Cassowary Algorithm | ACM TOCHI 2001 | [ ] | Layout engine foundation |
| Position Based Dynamics | JVCIR 2007 | [ ] | Real-time physics constraints |
| XPBD | MIG 2016 | [ ] | Haptic force estimates |

#### Functional Reactive Programming (Section 7)
| Paper | Source | Status | Why Critical |
|-------|--------|--------|--------------|
| Functional Reactive Animation | ICFP 1997 | [ ] | THE foundational FRP paper |
| Push-Pull FRP | Haskell 2009 | [ ] | Efficient evaluation strategy |
| Monadic Stream Functions | Haskell 2016 | [ ] | Unifies FRP paradigms |
| Adapton | PLDI 2014 | [ ] | Incremental computation |

### Priority 1: HIGH VALUE (Core Capabilities)

#### Real-Time Diffusion (Section 1)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| Consistency Models | 2303.01469 | [ ] | 1-step generation foundation |
| Latent Consistency Models | 2310.04378 | [ ] | 2-4 step high-res |
| StreamDiffusion | 2312.12491 | [ ] | 100+ FPS pipeline |
| SDXL-Lightning | 2402.13929 | [ ] | 1-4 step SDXL |
| Rectified Flow | 2209.03003 | [ ] | Straight trajectories |
| InstaFlow | 2309.06380 | [ ] | 1-step text-to-image |

#### 3D Neural Representations (Section 17)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| 3D Gaussian Splatting | 2308.04079 | [ ] | Real-time neural 3D |
| Instant NGP | 2201.05989 | [ ] | Hash encoding breakthrough |
| 2D Gaussian Splatting | 2403.17888 | [ ] | Accurate geometry |
| Zip-NeRF | 2304.06706 | [ ] | Best of both worlds |

#### Swarm & Multi-Agent (Section 4, 19)
| Paper | arXiv/Source | Status | Why Critical |
|-------|--------------|--------|--------------|
| FLAME GPU | flamegpu.com | [ ] | Massively parallel agents |
| TeraAgent | 2509.24063 | [DONE] | 250x agent scaling |
| Boids | SIGGRAPH 1987 | [ ] | THE flocking paper |
| Vicsek Model | PRL 1995 | [ ] | Phase transitions |
| Topological Interaction | PNAS 2008 | [ ] | ~7 neighbors by rank |
| Cucker-Smale | IEEE TAC 2007 | [ ] | Flocking proofs |

### Priority 2: MEDIUM VALUE (Enhanced Capabilities)

#### Low-Precision Inference (Section 2)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| NVFP4 Adaptive Scaling | 2512.02010 | [ ] | Blackwell optimization |
| AWQ | 2306.00978 | [ ] | 3x speedup weight quant |
| GPTQ | 2210.17323 | [ ] | 175B on single GPU |
| QLoRA (NF4) | 2305.14314 | [ ] | Optimal normal quant |

#### Noise Scheduling (Section 12)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| DDIM | 2010.02502 | [ ] | 10-50x faster sampling |
| DPM-Solver++ | 2211.01095 | [ ] | Default SD sampler |
| EDM (Karras) | 2206.00364 | [ ] | 1.79 FID CIFAR-10 |
| Flow Matching | 2210.02747 | [ ] | Simulation-free CNF |

#### Spatial Data Structures (Section 15)
| Paper | Source | Status | Why Critical |
|-------|--------|--------|--------------|
| Karras BVH | HPG 2012 | [ ] | Parallel GPU BVH |
| Perfect Spatial Hashing | SIGGRAPH 2006 | [ ] | GPU-friendly sparse data |
| Voxel Hashing | TOG 2013 | [ ] | Memory-efficient 3D |

#### Material & Texture Segmentation (NEW)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| MatSeg: Zero-Shot Material States | 2403.03309 | [DONE] | First general benchmark, pattern infusion |
| SAM (Segment Anything) | 2304.02643 | [ ] | Foundation model baseline |
| Materialistic | 2023 | [ ] | PBR-based material segmentation |

### Priority 3: VALUABLE (Specialized Capabilities)

#### Voice & Multimodal (Section 10)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| VALL-E | 2301.02111 | [ ] | Zero-shot TTS |
| F5-TTS | 2410.06885 | [ ] | Flow matching TTS |
| CosyVoice 2 | 2412.10117 | [DONE] | Streaming TTS |
| Multimodal GUI for LLM | 2510.06223 | [DONE] | Voice-driven UI |

#### AI Self-Representation (Section 11)
| Paper | Source | Status | Why Critical |
|-------|--------|--------|--------------|
| Feature Visualization | Distill 2017 | [ ] | Neural interpretability |
| Scaling Monosemanticity | Anthropic 2024 | [ ] | Interpretable features |
| Representation Engineering | 2310.01405 | [ ] | Controlling LLM cognition |

#### World Models (Section 3)
| Paper | arXiv | Status | Why Critical |
|-------|-------|--------|--------------|
| DreamerV3 | 2301.04104 | [ ] | General world model RL |
| GameNGen | 2408.14837 | [ ] | DOOM at 20+ FPS |
| DIAMOND | 2405.12399 | [ ] | RL in diffusion world |
| PAN | 2511.09057 | [DONE] | Long-horizon simulation |
| GAIA-2 | 2503.20523 | [DONE] | Multi-view controllable world model |
| GameFactory | 2501.08325 | [DONE] | Agent simulation factory |
| WorldGen | 2511.16825 | [DONE] | Text to traversable 3D |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 3: Papers Requiring Fetch

These are 2024-2026 papers likely beyond my training cutoff. You'll need to fetch these.

### MUST FETCH (Critical, Recent)
```
arXiv:2512.02010  - NVFP4 Adaptive Block Scaling (Blackwell GPUs)
| arXiv:2509.25149  - Pretraining LLMs with NVFP4 
arXiv:2509.23202  - Microscaling FP4 Promise vs Performance [DONE: docs/research/MICROSCALING_FP4_QUANTIZATION.md]
arXiv:2505.19115  - FP4 All the Way [DONE: docs/research/FP4_ALL_THE_WAY.md]
arXiv:2505.14669  - Quartet: Native FP4 Training [DONE: docs/research/QUARTET_FP4_TRAINING.md]
arXiv:2509.24063  - TeraAgent [DONE: docs/research/TERAAGENT_SIMULATION.md]
arXiv:2503.20523  - GAIA-2 (multi-view world model) [DONE: docs/research/GAIA2_WORLD_MODEL.md]
arXiv:2509.24527  - Dreamer 4 (scalable world models)
arXiv:2501.16496  - Open Problems in Mechanistic Interpretability
arXiv:2501.14598  - Type-Based Rounding Error Analysis [DONE: docs/research/ROUNDING_ERROR_TYPES.md]
arXiv:2501.14550  - Bean: Backward Error Analysis [DONE: included in ROUNDING_ERROR_TYPES.md]
arXiv:2510.06223  - Multimodal GUI for LLM Assistants [DONE: docs/research/MULTIMODAL_GUI.md]
arXiv:2412.10117  - CosyVoice 2 (streaming TTS) [DONE: docs/research/COSYVOICE2_TTS.md]
arXiv:2503.20215  - Qwen2.5-Omni (multimodal) [DONE: docs/research/QWEN25_OMNI.md]
arXiv:2501.06282  - MinMo (~100ms speech latency) [DONE: docs/research/MinMo_Voice.md]
arXiv:2503.17359  - Interactive Generative Video as Game Engine [DONE: docs/research/INTERACTIVE_GAME_VIDEO.md]
arXiv:2511.16825  - WorldGen (text to 3D) [DONE: docs/research/WORLDGEN_3D.md]
arXiv:2511.09057  - PAN (long-horizon simulation) [DONE: docs/research/PAN_WORLD_MODEL.md]
arXiv:2501.08325  - GameFactory [DONE: docs/research/GAMEFACTORY.md]
arXiv:2510.20532  - Sound and Complete Effect Inference
arXiv:2507.09901  - Large Population Models (AgentTorch)
arXiv:2507.10566  - AI Mother Tongue (emergent symbols)
arXiv:2505.12872  - From Grunts to Grammar
arXiv:2502.01568  - Visual Theory of Mind Writing
arXiv:2502.19457  - 3DGS Compression Survey
arXiv:2403.03309  - MatSeg: Zero-Shot Material States (DONE: docs/research/MATERIAL_STATE_SEGMENTATION.md)
arXiv:2512.15716  - Spatia: Video Generation with Spatial Memory (DONE: docs/research/SPATIA_VIDEO_MEMORY.md)
arXiv:2503.20215  - Qwen2.5-Omni (DONE: docs/research/QWEN25_OMNI.md)
```

### SHOULD FETCH (Valuable, Recent)
```
arXiv:2406.05768  - MLCM (multistep consistency)
arXiv:2405.18407  - Phased Consistency Model
arXiv:2404.13686  - Hyper-SD
arXiv:2405.14867  - DMD2 (improved distillation)
arXiv:2405.05967  - Diffusion to GAN distillation
arXiv:2407.02398  - Consistency Flow Matching
arXiv:2407.15595  - Discrete Flow Matching
arXiv:2412.20720  - 4D Gaussian Splatting
arXiv:2406.18462  - GaussianDreamerPro
arXiv:2407.14499  - Discover-then-Name (concept bottlenecks)
arXiv:2504.02821  - SAE for Vision-Language Models
arXiv:2411.07039  - Event-based Multi-Agent Learning
arXiv:2410.06885  - F5-TTS
arXiv:2407.05407  - CosyVoice
arXiv:2407.10759  - Qwen2-Audio
arXiv:2408.16725  - Mini-Omni
arXiv:2407.04051  - FunAudioLLM
arXiv:2409.01824  - DarthShader (WebGPU fuzzing)
arXiv:2409.03755  - DC-Solver
arXiv:2404.14507  - Align Your Steps
arXiv:2407.03297  - Improved Noise Schedule
```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 4: Papers I Can Summarize (In Training)

These are foundational/classic papers I have detailed knowledge of.

### Foundational (Pre-2024, Well-Known)
- Cassowary (2001) - I know the dual simplex algorithm in detail
- Position Based Dynamics (2007) - Constraint projection loop
- XPBD (2016) - Compliance parameters, force estimation
- Boids (1987) - Separation, alignment, cohesion rules
- Vicsek Model (1995) - Phase transition mathematics
- Cucker-Smale (2007) - Flocking convergence proofs
- FRP Animation (1997) - Behaviors, events, denotational semantics
- Push-Pull FRP (2009) - Reactive normal form
- Adapton (2014) - Demand-driven incrementalization
- Coeffects (2014) - Semiring-annotated types
- Granule (2019) - Graded necessity/possibility
- NeRF (2020) - Volume rendering equation
- 3D Gaussian Splatting (2023) - Anisotropic gaussians, rasterization
- Instant NGP (2022) - Multiresolution hash encoding
- DDIM (2020) - Non-Markovian sampling
- DPM-Solver (2022) - Analytical linear solution
- EDM/Karras (2022) - Noise schedule decoupling
- Consistency Models (2023) - ODE trajectory mapping
- Flow Matching (2022) - Simulation-free CNF
- Rectified Flow (2022) - Trajectory straightening
- Feature Visualization (2017) - Neural interpretability
- GPTQ (2022) - Hessian-based quantization
- AWQ (2023) - Activation-aware scaling
- QLoRA (2023) - NF4, double quantization
- World Models Ha/Schmidhuber (2018) - VAE + MDN-RNN
- DreamerV3 (2023) - General world model RL
- RIAL/DIAL (2016) - Emergent communication
- CommNet (2016) - Continuous communication
- TarMAC (2018) - Targeted attention communication
- Perfect Spatial Hashing (2006) - Offset tables
- Karras BVH (2012) - Morton codes, radix tree
- MatSeg (2024) - Zero-shot material states, pattern infusion (SUMMARIZED)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 5: GAPS - Papers NOT in Survey

You asked about networking and faster physics. The survey has gaps:

### Networking (NOT COVERED - Need to Find)
The survey has NO papers on:
- Zero-copy network transfer
- RDMA for GPU buffers
- Distributed rendering
- Agent state synchronization protocols
- CRDTs for distributed UI state

**Recommendation:** Search for:
- "RDMA GPU direct" papers
- "Distributed rendering synchronization"
- "CRDT for real-time collaboration"
- NVIDIA GPUDirect documentation

### Physics Optimization (PARTIALLY COVERED)
The survey has:
- PBD (2007) - Basic position-based dynamics
- XPBD (2016) - Extended with compliance

**Missing:**
- Parallel constraint solving on GPU
- Substepping strategies
- Broad-phase collision (only spatial hashing mentioned)
- Continuous collision detection

**Recommendation:** Search for:
- "GPU parallel constraint solver"
- "Speculative contacts physics"
- "Continuous collision detection GPU"
- Bullet Physics / PhysX papers

### WebGPU Specifics (BARELY COVERED)
Only paper: DarthShader (fuzzing)

**Missing:**
- WebGPU compute shader best practices
- WGSL optimization patterns
- WebGPU vs Vulkan performance analysis

**Recommendation:** 
- WebGPU spec itself
- Chromium Dawn implementation docs
- wgpu-rs documentation

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 6: Implementation Checklist (Ordered)

### Phase 1: Foundation (Weeks 1-4)
- [ ] 1.1 GPUStorable typeclass
- [ ] 1.2 Identified wrapper + UUID5
- [ ] 1.3 Patch/Diff system
- [ ] Read: Coeffects (2014), Granule (2019)
- [ ] Read: Cassowary (2001)
- [ ] Read: FRP Animation (1997), Adapton (2014)

### Phase 2: Interpreter (Weeks 5-8)
- [ ] 2.1 Minimal WebGPU pipeline dispatcher
- [ ] 2.2 Buffer pool (UUID5-keyed)
- [ ] 2.3 Diff applicator (in-place patches)
- [ ] 2.4 Frame scheduler skeleton
- [ ] Read: Perfect Spatial Hashing (2006)
- [ ] Read: Karras BVH (2012)

### Phase 3: Rendering Primitives (Weeks 9-12)
- [ ] 3.1 Rectangle/Shape pipeline
- [ ] 3.2 Text pipeline (glyph instancing)
- [ ] 3.3 Gaussian splatting pipeline
- [ ] Fetch & Read: 3DGS (2308.04079)
- [ ] Fetch & Read: Instant NGP (2201.05989)

### Phase 4: Diffusion Integration (Weeks 13-16)
- [ ] 4.1 Consistency model inference
- [ ] 4.2 StreamDiffusion pipeline batching
- [ ] 4.3 Temporal coherence (keyframes + interp)
- [ ] Fetch & Read: Consistency Models (2303.01469)
- [ ] Fetch & Read: StreamDiffusion (2312.12491)
- [ ] Fetch & Read: LCM (2310.04378)

### Phase 5: Swarm Scale (Weeks 17-20)
- [ ] 5.1 Hierarchical groups
- [ ] 5.2 Submodular frame allocation
- [ ] 5.3 Topological neighbor discovery
- [ ] Read: Boids (1987), Vicsek (1995)
- [ ] Read: Cucker-Smale (2007)
- [ ] Fetch & Read: FLAME GPU, TeraAgent

### Phase 6: Formal Verification (Ongoing)
- [ ] 6.1 Lean4: Serialization roundtrip
- [ ] 6.2 Lean4: UUID5 determinism
- [ ] 6.3 Lean4: Submodular guarantee
- [ ] 6.4 Lean4: Color conversion bounds
- [ ] Fetch & Read: NumFuzz (2405.04612)
- [ ] Fetch & Read: Bean (2501.14550)
- [ ] Read: Flocq (1106.3448)

### Phase 7: Voice & Interaction (Weeks 21-24)
- [ ] 7.1 Voice command parsing
- [ ] 7.2 MCP integration
- [ ] 7.3 Blank-screen-to-anything demo
- [ ] Fetch & Read: Multimodal GUI (2510.06223)
- [ ] Fetch & Read: CosyVoice 2 (2412.10117)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Section 7: Paper Count Summary

| Category | Total | To Implement | Done | Notes |
|----------|-------|--------------|------|-------|
| Real-time Diffusion | 24 | 12 | 0 | Core capability |
| NVFP4/Quantization | 14 | 3 | 3 | Quartet, Microscaling, FP4-All-Way |
| World Models | 14 | 4 | 4 | GAIA-2, PAN, GameFactory, WorldGen done |
| Agent Swarms | 8 | 6 | 0 | FLAME GPU critical |
| Formal Verification | 7 | 5 | 2 | NumFuzz, Bean done |
| Graded Monads | 12 | 6 | 0 | Granule critical |
| FRP | 9 | 5 | 0 | Adapton critical |
| WebGPU/GPU | 8 | 4 | 0 | Gap area |
| Generative UI | 16 | 4 | 0 | Design2Code |
| Voice/Multimodal | 14 | 6 | 4 | CosyVoice, Multimodal GUI, MinMo, Qwen2.5-Omni done |
| AI Self-Representation | 14 | 5 | 0 | Anthropic SAE |
| Noise Scheduling | 19 | 8 | 0 | DPM-Solver++ default |
| Submodular | 7 | 4 | 0 | Adaptive submodularity |
| Quantum-Inspired | 6 | 2 | 0 | Dequantization |
| Scene Graphs | 8 | 4 | 0 | Instant NGP |
| Color Science | 7 | 3 | 0 | Oklab |
| 3D Neural | 12 | 6 | 0 | 3DGS critical |
| Emergent Comm | 9 | 4 | 0 | TarMAC |
| Murmuration | 12 | 6 | 0 | Topological critical |
| Constraint Solving | 4 | 4 | 0 | All critical |
| Material Segmentation | 3 | 1 | 1 | MatSeg done |
| **TOTAL** | **190+** | **~96** | **15** | **~55% coverage** |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                                                               — TODO v1.0
                                                                  2026-02-26
