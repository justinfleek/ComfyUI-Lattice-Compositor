# Comprehensive paper survey for a universal WebGPU rendering engine

This survey identifies **190+ papers** across all 20 research domains relevant to building a Haskell/PureScript universal rendering engine with real-time diffusion, formally verified pipelines, billion-agent swarms, and voice-driven AI interaction. Papers span foundational works through cutting-edge 2025–2026 research, organized by domain with cross-disciplinary bridges noted.

---

## 1. Real-time neural rendering and diffusion models

- **"Consistency Models"** — arXiv:2303.01469 — Maps any point on a diffusion ODE trajectory to its origin, enabling **one-step or few-step generation** without iterative sampling. Foundational for the consistency model family.

- **"Improved Techniques for Training Consistency Models"** — arXiv:2310.14189 — Introduces Pseudo-Huber losses and lognormal noise schedules, achieving state-of-the-art FID for single-step generation directly from data (improved Consistency Training).

- **"Latent Consistency Models: Synthesizing High-Resolution Images with Few-Step Inference"** — arXiv:2310.04378 — Extends consistency models to latent space of Stable Diffusion, enabling **2–4 step** high-resolution text-to-image generation.

- **"LCM-LoRA: A Universal Stable-Diffusion Acceleration Module"** — arXiv:2311.05556 — Distills LCMs into LoRA parameters, creating a plug-and-play acceleration module compatible with SD1.5, SDXL, and SSD-1B for fast few-step inference.

- **"Trajectory Consistency Distillation"** — arXiv:2402.19159 — Improves upon LCM with a trajectory consistency function and strategic stochastic sampling, yielding higher quality at low NFEs.

- **"Phased Consistency Model"** — arXiv:2405.18407 — Divides ODE trajectories into sub-trajectory phases for consistency distillation, reducing learning difficulty. Outperforms LCM on high-resolution text-to-image and video.

- **"Consistency Trajectory Models: Learning Probability Flow ODE Trajectory of Diffusion"** — arXiv:2310.02279 — Generalizes consistency models to unrestricted traversal between any two time points. Achieves **1.73 FID on CIFAR-10** in a single step.

- **"Adversarial Diffusion Distillation (SDXL Turbo)"** — arXiv:2311.17042 — Combines score distillation and adversarial loss for **real-time single-step 512×512** image synthesis. First method achieving real-time one-step generation.

- **"SDXL-Lightning: Progressive Adversarial Diffusion Distillation"** — arXiv:2402.13929 — Combines progressive distillation with adversarial training for 1–4 step SDXL generation with improved mode coverage.

- **"Fast High-Resolution Image Synthesis with Latent Adversarial Diffusion Distillation (LADD)"** — arXiv:2403.12015 — Extends ADD to latent space for SD3-Turbo, enabling high-resolution multi-aspect-ratio synthesis.

- **"Hyper-SD: Trajectory Segmented Consistency Model for Efficient Image Synthesis"** — arXiv:2404.13686 — Combines trajectory-segmented consistency distillation with human feedback learning, achieving SOTA in aggressive step compression.

- **"One-step Diffusion with Distribution Matching Distillation (DMD)"** — arXiv:2311.18828 — Distills diffusion models into one-step generators by minimizing KL divergence using score function differences.

- **"Improved Distribution Matching Distillation (DMD2)"** — arXiv:2405.14867 — Removes regression loss, integrates GAN loss, and enables multi-step sampling for one-step megapixel generation with SDXL.

- **"Distilling Diffusion Models into Conditional GANs"** — arXiv:2405.05967 — Distills multi-step diffusion into single-step conditional GAN using ODE trajectory pairs and E-LatentLPIPS.

- **"Progressive Distillation for Fast Sampling of Diffusion Models"** — arXiv:2202.00512 — Foundational work progressively halving sampling steps by training students to match two teacher steps in one.

- **"On Distillation of Guided Diffusion Models"** — arXiv:2210.03142 — Extends progressive distillation to classifier-free guided models, first consolidating two evaluations into one.

- **"Flow Straight and Fast: Learning to Generate and Transfer Data with Rectified Flow"** — arXiv:2209.03003 — Foundational rectified flows paper: ODE transport learned via regression that straightens trajectories through iterative reflow.

- **"InstaFlow: One Step is Enough for High-Quality Diffusion-Based Text-to-Image Generation"** — arXiv:2309.06380 — Applies rectified flow reflow + distillation to SD for **one-step text-to-image in 0.09s** (23.3 FID on MS COCO).

- **"Improving the Training of Rectified Flows"** — arXiv:2405.20320 — U-shaped timestep distribution and LPIPS-Huber premetric for improved one-round rectified flow training.

- **"StreamDiffusion: A Pipeline-level Solution for Real-time Interactive Generation"** — arXiv:2312.12491 — Pipeline-level optimization with Stream Batch denoising, residual CFG, and stochastic similarity filtering for **100+ FPS throughput**.

- **"StreamMultiDiffusion: Real-Time Interactive Generation with Region-Based Semantic Control"** — arXiv:2403.09055 — Extends StreamDiffusion with multi-prompt stream batch for real-time region-based semantic control.

- **"SDXS: Real-Time One-Step Latent Diffusion Models with Image Conditions"** — arXiv:2403.16627 — Combines architecture distillation with sampling-step reduction for extremely fast one-step models at 512 and 1024 resolution.

- **"PIXART-δ: Fast and Controllable Image Generation with Latent Consistency Models"** — arXiv:2401.05252 — Integrates LCM and ControlNet into the efficient PIXART-α transformer for fast controllable generation.

- **"MLCM: Multistep Consistency Distillation of Latent Diffusion Model"** — arXiv:2406.05768 — Extends multistep consistency distillation to latent diffusion with progressive training and preference learning.

---

## 2. NVFP4 and low-precision inference

- **"Four Over Six: More Accurate NVFP4 Quantization with Adaptive Block Scaling"** — arXiv:2512.02010 — Adaptive block scaling modification to NVFP4 reducing quantization error on **NVIDIA Blackwell GPUs**.

- **"Pretraining Large Language Models with NVFP4"** — arXiv:2509.25149 — NVIDIA's paper training a 12B-parameter model on 10T tokens with NVFP4 precision on Blackwell. Shows NVFP4 reaches comparable loss with fewer tokens than MXFP4.

- **"Bridging the Gap Between Promise and Performance for Microscaling FP4"** — arXiv:2509.23202 — First thorough study of NVFP4 and MXFP4 accuracy/performance, achieving **3.6× speedup on B200** and **6× on RTX 5090**.

- **"FP4 All the Way: Fully Quantized Training of LLMs"** — arXiv:2505.19115 — First fully quantized FP4 training (weights, activations, gradients) at scale. Validates Blackwell's NVFP4 (E4M3, block size 16) hardware design.

- **"Quartet: Native FP4 Training Can Be Optimal for Large Language Models"** — arXiv:2505.14669 — Systematic study of hardware-supported MXFP4 training achieving **~2× speedup over FP8** on Blackwell RTX 5090.

- **"Optimizing Large Language Model Training Using FP4 Quantization"** — arXiv:2501.17116 — FP4 training framework with Differentiable Gradient Estimator achieving accuracy comparable to BF16 and FP8.

- **"LLM-FP4: 4-Bit Floating-Point Quantized Transformers"** — arXiv:2310.16836 — Post-training quantization of both weights and activations to 4-bit FP, achieving near full-precision on LLaMA-13B.

- **"GPTQ: Accurate Post-Training Quantization for Generative Pre-trained Transformers"** — arXiv:2210.17323 — Seminal layer-wise quantization using second-order Hessian information. Quantizes 175B models on a single GPU.

- **"AWQ: Activation-aware Weight Quantization for LLM Compression and Acceleration"** — arXiv:2306.00978 — Hardware-friendly weight-only quantization protecting 1% salient weights via equivalent scaling. **3× speedup** over FP16.

- **"SqueezeLLM: Dense-and-Sparse Quantization"** — arXiv:2306.07629 — Sensitivity-based non-uniform quantization enabling lossless compression to 3-bit with 2.3× inference speedup.

- **"QLoRA: Efficient Finetuning of Quantized LLMs"** — arXiv:2305.14314 — Introduces **NF4 data type** (information-theoretically optimal for normal distributions), double quantization, and paged optimizers for 65B model finetuning on 48GB.

- **"FP8-LM: Training FP8 Large Language Models"** — arXiv:2310.18313 — FP8 automatic mixed-precision framework for training up to GPT-175B on H100 with reduced memory and increased speed.

- **"Q-Diffusion: Quantizing Diffusion Models"** — arXiv:2302.04304 — First post-training quantization designed specifically for diffusion models with timestep-aware calibration.

- **"EfficientDM: Efficient Quantization-Aware Fine-Tuning of Low-Bit Diffusion Models"** — arXiv:2310.03270 — Data-free QAT-level quality via QALoRA and temporal learned step-size quantization for diffusion models.

- **"BitsFusion: 1.99 bits Weight Quantization of Diffusion Model"** — arXiv:2406.04333 — Achieves extreme **~2-bit weight quantization** of Stable Diffusion UNet while improving generation quality.

---

## 3. World models and generative environments

- **"World Models"** (Ha & Schmidhuber) — arXiv:1803.10122 — Foundational generative RNN-based world models (VAE + MDN-RNN). Agents train entirely inside hallucinated dreams and transfer policies to real environments.

- **"GAIA-1: A Generative World Model for Autonomous Driving"** — arXiv:2309.17080 — Generative world model using video, text, and action inputs for predicting realistic future driving scenarios.

- **"GAIA-2: A Controllable Multi-View Generative World Model for Autonomous Driving"** — arXiv:2503.20523 — Latent diffusion world model generating high-resolution, spatiotemporally consistent multi-camera driving videos.

- **"DreamerV3: Mastering Diverse Domains through World Models"** — arXiv:2301.04104 — General-purpose world-model RL mastering diverse domains (including Minecraft diamond collection) with fixed hyperparameters.

- **"Dreamer 4: Training Agents Inside of Scalable World Models"** — arXiv:2509.24527 — Scales world model RL to complex tasks using efficient transformer architecture with action conditioning.

- **"Genie: Generative Interactive Environments"** — arXiv:2402.15391 — **11B parameter** unsupervised foundation world model creating action-controllable virtual worlds from unlabelled Internet videos.

- **"GameNGen: Diffusion Models Are Real-Time Game Engines"** — arXiv:2408.14837 — First neural model simulating DOOM at **20+ FPS** on a single TPU. Human raters cannot distinguish real vs. simulated gameplay.

- **"DIAMOND: Diffusion for World Modeling"** — arXiv:2405.12399 — RL agent trained entirely in a diffusion world model achieving 1.46 mean human-normalized score on Atari 100k. Scaled to CS:GO.

- **"UniSim: Learning Interactive Real-World Simulators"** — arXiv:2310.06114 — Universal simulator learning real-world interactions through generative modeling of diverse actions for zero-shot transfer.

- **"GenEx: Generating an Explorable World"** — arXiv:2412.09624 — Generates consistent, expansive 3D environments from a single image using panoramic video streams and guided imagination.

- **"Is Sora a World Simulator? A Comprehensive Survey on General World Models and Beyond"** — arXiv:2405.03520 — Comprehensive survey examining world models' role in video generation, autonomous driving, and autonomous agents.

- **"PAN: A World Model for General, Interactable, and Long-Horizon World Simulation"** — arXiv:2511.09057 — Combines autoregressive latent dynamics with video diffusion decoder for long-horizon interactive simulation.

- **"GameFactory: Creating New Games with Generative Interactive Videos"** — arXiv:2501.08325 — Uses pre-trained video diffusion models to generate diverse, action-controllable game videos.

- **"WorldGen: From Text to Traversable and Interactive 3D Worlds"** — arXiv:2511.16825 — Converts text prompts into interactive 3D environments using LLM-driven scene layout and diffusion-based 3D generation.

- **"Position: Interactive Generative Video as Next-Generation Game Engine"** — arXiv:2503.17359 — Framework for generative game engines enabling physics-aware modeling and unlimited virtual world creation.

---

## 4. Agent swarm visualization and multi-agent systems

- **"Very Large-Scale Multi-Agent Simulation in AgentScope"** — arXiv:2407.17789 — Distributed actor-based mechanisms for scaling multi-agent simulations to very large numbers with web-based visualization.

- **"Large Population Models (AgentTorch)"** — arXiv:2507.09901 — Framework for simulating large populations of agents with privacy-preserving communication for understanding emergent behaviors.

- **"On the limits of agency in agent-based models (AgentTorch)"** — arXiv:2409.10568 — Scales LLM-powered agent-based modeling to **millions of agents** for complex system simulations like pandemic modeling.

- **"Towards Simulating Billions of Agents in Thousands of Seconds"** — ResearchGate publication 221455601 — DMASF distributed simulator targeting **one billion agents** using distributed computing.

- **"TeraAgent: A Distributed Agent-Based Simulation Engine"** — arXiv:2509.24063 — Simulates **250× more agents** than BioDynaMo with 8× higher update rates per core and 39× visualization improvement.

- **"FLAME GPU: Complex System Simulation Framework"** — https://flamegpu.com — Flexible Large-scale Agent Modelling Environment enabling **massively parallel GPU agent simulation** with real-time visualization.

- **"A Framework for Megascale Agent Based Model Simulations on Graphics Processing Units"** — JASSS 11(4):10, 2008 — Data-parallel GPU algorithms for megascale spatial agent-based simulations.

- **"Learning Collective Dynamics of Multi-Agent Systems using Event-based Vision"** — arXiv:2411.07039 — Event-based vision architecture for real-time prediction of interaction strength in multi-agent collective behavior.

- **"LLM-Empowered Agent-based Modeling and Simulation: A Survey"** — arXiv:2312.11970 — Comprehensive survey on integrating LLMs into agent-based modeling across cyber, physical, and social domains.

---

## 5. Formally verified graphics and functional rendering

- **"The Design and Implementation of a Verification Technique for GPU Kernels"** — ACM TOPLAS 37(3), 2015 — Formal technique verifying race-freedom and barrier-divergence correctness of GPU kernels via synchronous delayed visibility semantics.

- **"Automated Testing of Graphics Shader Compilers (GLFuzz)"** — OOPSLA 2017 — Metamorphic testing tool for GLSL/OpenGL shader compilers, finding **60+ bugs** across 17 GPU/driver configurations.

- **"Futhark: Purely Functional GPU-Programming with Nested Parallelism and In-Place Array Updates"** — PLDI 2017 — Purely functional data-parallel array language with uniqueness types compiling to efficient GPU code via OpenCL. Performance competitive with hand-written CUDA.

- **"Flocq: A Unified Library for Proving Floating-Point Algorithms in Coq"** — arXiv:1106.3448 — Unified Coq formalization of multi-radix, multi-precision floating-point arithmetic for proving FP algorithm correctness.

- **"Enabling Floating-Point Arithmetic in the Coq Proof Assistant"** — hal-04114233 — Hardware FP numbers for numerically intensive Coq proofs, achieving **10× speedup** while maintaining proof trust.

- **"Numerical Fuzz: A Type System for Rounding Error Analysis (NumFuzz)"** — arXiv:2405.04612 — Functional language using a **graded monad ("neighborhood monad")** to express and infer quantitative floating-point roundoff error bounds. Bridges formal verification and graded type theory.

- **"Type-Based Approaches to Rounding Error Analysis"** — arXiv:2501.14598 — Dissertation exploring graded monadic types for forward error (NumFuzz) and graded coeffect types for backward error (Bean) analysis.

---

## 6. Graded monads, co-effects, and algebraic effects

- **"Coeffects: A Calculus of Context-Dependent Computation"** — ICFP 2014 / ICALP 2013 — Introduces **coeffects** as the formal dual to effects, capturing context-dependence via semiring-annotated type systems using graded comonads.

- **"Quantitative Program Reasoning with Graded Modal Types (Granule)"** — ICFP 2019 — Presents the **Granule language** with graded modal types encompassing coeffect types (graded necessity) and effect types (graded possibility/monads) with SMT-backed type checking.

- **"Combining Effects and Coeffects via Grading"** — ICFP 2016 — Unified calculus with combined effect-coeffect types via graded monads and graded comonads with novel graded distributive laws.

- **"Towards a Formal Theory of Graded Monads"** — FOSSACS 2016 — Category-theoretic foundations for graded monads establishing graded Eilenberg-Moore and Kleisli constructions.

- **"Syntax and Semantics of Quantitative Type Theory (QTT)"** — LICS 2018 — Records **semiring-indexed usage** for each variable, combining dependent types with linear/substructural types via Quantitative Categories with Families.

- **"Unifying Graded and Parameterised Monads"** — arXiv:2001.10274 — Unifies graded monads and Atkey-style parameterised/indexed monads under category-graded monads as lax functors.

- **"An Introduction to Algebraic Effects and Handlers"** — Pretnar, 2015 — Tutorial defining algebraic effects with operational semantics and a type-and-effect system covering state, exceptions, I/O, nondeterminism, and cooperative multithreading.

- **"Programming with Algebraic Effects and Handlers (Eff)"** — Bauer & Pretnar, 2015 — The **Eff language** with first-class algebraic effects, domain-theoretic semantics, delimited continuations, and probabilistic choice.

- **"Algebraic Effects for Functional Programming (Koka)"** — MSR-TR-2016-29 — Koka language with row-polymorphic effect types and algebraic effect handlers; proves effect types guarantee behavioral properties.

- **"Bean: A Language for Backward Error Analysis"** — arXiv:2501.14550 — Uses **graded coeffect types** with strict linearity to soundly track backward error flow through numerical programs.

- **"A Framework for Higher-Order Effects & Handlers"** — Science of Computer Programming, 2024 — Unified Haskell framework for algebraic, scoped, parallel, and latent effects using a single free monad definition.

- **"Deciding not to Decide: Sound and Complete Effect Inference"** — arXiv:2510.20532 — Sound and complete effect inference for type-and-effect systems with subtyping and higher-rank polymorphism, mechanized in Rocq.

---

## 7. Functional reactive programming for UI

- **"Functional Reactive Animation"** (Elliott & Hudak) — ICFP 1997 — **The foundational FRP paper.** Introduces behaviors (continuous time-varying values) and events (discrete occurrences) with denotational semantics for interactive multimedia.

- **"Push-Pull Functional Reactive Programming"** (Elliott) — Haskell Symposium 2009 — Efficient FRP combining data-driven (push) and demand-driven (pull) evaluation with reactive normal form and functional future values.

- **"Functional Reactive Programming, Refactored"** (Perez, Bärenz, Nilsson) — Haskell Symposium 2016 — Introduces **Monadic Stream Functions** (MSFs) unifying Classic FRP, Arrowized FRP, and other paradigms. The Dunai/BearRiver libraries.

- **"Testing and Debugging Functional Reactive Programming"** — ICFP 2017 — Extends arrowized FRP (Yampa) with temporal predicates based on Linear Temporal Logic for systematic testing and debugging.

- **"Arrows, Robots, and Functional Reactive Programming (Yampa)"** — AFP 2002 — Comprehensive tutorial on **Yampa's arrowized FRP** for robotics and games: signal functions, arrow combinators, switching, parallel composition.

- **"Asynchronous Functional Reactive Programming for GUIs (Elm)"** — PLDI 2013 — Introduces Elm with asynchronous FRP where global event ordering can be relaxed for concurrent execution. Foundation for the **Elm Architecture (Model-View-Update)**.

- **"Adapton: Composable, Demand-Driven Incremental Computation"** — PLDI 2014 — Demand-driven incremental computation via λ_ic^dd combining lazy evaluation with change propagation. Relevant to incremental UI frameworks.

- **"Incremental Computation with Names (Nominal Adapton)"** — OOPSLA 2015 — Extends Adapton with first-class names for computation reuse across runs. Efficient incrementalization of maps, folds, and unfolds.

- **"Self-Adjusting Computation"** (Acar) — CMU PhD Thesis 2005 — Foundational work on programs automatically responding to input changes via change propagation through dynamic dependence graphs.

---

## 8. WebGPU compute and GPU programming from functional languages

- **"Accelerating Haskell Array Codes with Multicore GPUs (Accelerate)"** — DAMP 2011 — Foundational **Accelerate** paper: DSL embedded in Haskell for collective array operations compiled to NVIDIA CUDA GPUs.

- **"Optimising Purely Functional GPU Programs (Accelerate)"** — ICFP 2013 — Array fusion, sharing recovery, and code generation for Accelerate achieving performance competitive with hand-written CUDA.

- **"Obsidian: A Domain Specific Embedded Language for Parallel Programming of Graphics Processors"** — IFL 2008 — Haskell-embedded DSL generating CUDA code using Lava-inspired combinators for compositional GPU programming.

- **"GPGPU Kernel Implementation and Refinement Using Obsidian"** — ICCS 2010 — Demonstrates progressive refinement from high-level correct descriptions to efficient CUDA in Obsidian.

- **"Getting to the Point: Index Sets and Parallelism-Preserving Autodiff for Pointful Array Programming (Dex)"** — arXiv:2104.05372 — Typed functional array language with **first-class index types, effect system exposing parallelism, and built-in AD** compiling to CPU/GPU.

- **"Compiling Embedded Languages"** (Elliott, Finne, de Moor) — JFP 2003 — Techniques for compiling functional DSELs in Haskell via program generation. Applied to Pan (image synthesis compiled to GPU). Underpins DSL-to-shader compilation.

- **"Efficient Differentiable Programming in a Functional Array-Processing Language"** — arXiv:1806.02136 — Source-to-source AD in a functional array language with global optimizations (loop fusion), outperforming state-of-the-art AD tools.

- **"DarthShader: Fuzzing WebGPU Shader Translators & Compilers"** — arXiv:2409.01824 — Fuzzing framework for the **WebGPU/WGSL shader compilation pipeline** (Tint, dxc, etc.), one of the few academic papers targeting WebGPU/WGSL specifically.

---

## 9. Parameterized design systems and generative UI

- **"Design2Code: Benchmarking Multimodal Code Generation for Automated Front-End Engineering"** — arXiv:2403.03163 — First real-world benchmark (484 webpages) for evaluating how multimodal LLMs convert visual designs into code.

- **"ScreenCoder: Advancing Visual-to-Code Generation via Modular Multimodal Agents"** — arXiv:2507.22827 — Multi-agent framework for UI-to-code with hierarchical layout planning and adaptive prompt synthesis.

- **"UI2Code^N: A Visual Language Model for Test-Time Scalable Interactive UI-to-Code Generation"** — arXiv:2511.08195 — VLM enhanced through staged pretraining, fine-tuning, and RL for superior UI-to-code generation with iterative feedback.

- **"UICoder: Finetuning Large Language Models to Generate User Interface Code"** — arXiv:2406.07739 — Uses automated compiler/multimodal feedback and synthetic dataset refinement for high-quality UI code generation.

- **"pix2code: Generating Code from a Graphical User Interface Screenshot"** — arXiv:1705.07962 — Seminal deep learning model automatically generating code from GUI screenshots across iOS, Android, and web.

- **"PLay: Parametrically Conditioned Layout Generation using Latent Diffusion"** — arXiv:2301.11529 — Conditional **latent diffusion model** generating vector graphic layouts from parametric user guidelines/constraints.

- **"Constrained Graphic Layout Generation via Latent Optimization"** — arXiv:2108.00871 — Transformer architecture with constrained latent optimization generating layouts aligned with user constraints.

- **"PosterLLaVa: Constructing a Unified Multi-modal Layout Generator with LLM"** — arXiv:2406.02884 — Multi-modal LLM framework for layout generation from visual and textual inputs with natural language specifications.

- **"A Parse-Then-Place Approach for Generating Graphic Layouts from Textual Descriptions"** — arXiv:2308.12700 — Two-stage Transformer decomposing layout generation into constraint parsing and element placement.

- **"UIClip: A Data-driven Model for Assessing User Interface Design"** — arXiv:2404.12500 — Machine-learned model assessing UI design quality from screenshots and text descriptions, providing scores and suggestions.

- **"UI Layout Generation with LLMs Guided by UI Grammar"** — arXiv:2310.15455 — LLMs (GPT-4) generating UI layouts guided by formal grammar specifications via in-context learning.

- **"OmniParser for Pure Vision Based GUI Agent"** — arXiv:2408.00203 — Parses GUI screenshots into structured actionable elements to enhance GPT-4V's screen interaction.

- **"GUI Agents: A Survey"** — arXiv:2412.13501 — Comprehensive survey of foundation-model-powered GUI agents for autonomous interface interaction.

- **"Sketch2Code: Evaluating Vision-Language Models for Interactive Web Design Prototyping"** — arXiv:2410.16232 — Evaluates VLMs converting hand-drawn sketches into webpage prototypes with multi-turn design iteration.

---

## 10. Voice-driven interaction and multimodal AI

- **"VALL-E: Neural Codec Language Models are Zero-Shot Text to Speech Synthesizers"** — arXiv:2301.02111 — Foundational neural codec TTS treating speech synthesis as conditional language modeling on discrete audio codes. **Zero-shot from 3 seconds**.

- **"VALL-E 2: Neural Codec Language Models are Human Parity Zero-Shot TTS"** — arXiv:2406.05370 — Achieves **human parity** in zero-shot TTS via Repetition Aware Sampling and Grouped Code Modeling.

- **"Voicebox: Text-Guided Multilingual Universal Speech Generation at Scale"** — arXiv:2306.15687 — Non-autoregressive **flow-matching** model for versatile speech generation: zero-shot TTS, noise removal, style conversion. Outperforms VALL-E.

- **"F5-TTS: A Fairytaler that Fakes Fluent and Faithful Speech with Flow Matching"** — arXiv:2410.06885 — Fully non-autoregressive TTS using flow matching with DiT, supporting multilingual capability, code-switching, and speed control.

- **"CosyVoice: A Scalable Multilingual Zero-shot TTS based on Supervised Semantic Tokens"** — arXiv:2407.05407 — Zero-shot TTS using supervised semantic tokens from ASR with conditional flow matching for voice cloning.

- **"CosyVoice 2: Scalable Streaming Speech Synthesis with LLMs"** — arXiv:2412.10117 — Streaming TTS with finite-scalar quantization and chunk-aware causal flow matching achieving **human-parity naturalness with low latency**.

- **"Qwen2-Audio Technical Report"** — arXiv:2407.10759 — Large-scale audio-language model supporting voice chat and audio analysis with DPO optimization for multi-speaker conversations.

- **"Qwen-Audio: Advancing Universal Audio Understanding"** — arXiv:2311.07919 — Multi-task audio-language training with hierarchical tags for universal audio understanding across speech recognition and emotion detection.

- **"Qwen2.5-Omni Technical Report"** — arXiv:2503.20215 — Multimodal model processing text, images, audio, and video with novel **dual-track Thinker-Talker architecture** generating both text and speech.

- **"Mini-Omni: Language Models Can Hear, Talk While Thinking in Streaming"** — arXiv:2408.16725 — End-to-end audio conversational model enabling **real-time speech interaction** with batch-parallel streaming.

- **"MinMo: A Multimodal Large Language Model for Seamless Voice Interaction"** — arXiv:2501.06282 — 8B-parameter model trained on 1.4M hours achieving **~100ms speech-to-text latency** with emotion/dialect control.

- **"FunAudioLLM: Voice Understanding and Generation Foundation Models"** — arXiv:2407.04051 — Integrates SenseVoice (recognition, emotion, events) with CosyVoice for speech-to-speech translation and expressive voice chat.

- **"PromptTTS: Controllable Text-to-Speech with Text Descriptions"** — arXiv:2211.12171 — Uses natural language descriptions to control TTS style including prosody and pitch.

- **"A Multimodal GUI Architecture for Interfacing with LLM-Based Conversational Assistants"** — arXiv:2510.06223 — Architecture enabling GUIs to interface with speech-enabled LLM assistants via MCP, ensuring every GUI action is achievable through **voice commands**.

- **"Large Language User Interfaces: Voice Interactive User Interfaces Powered by LLMs"** — arXiv:2402.07938 — Framework textually modeling UI component semantics for LLM-driven voice control of complex tasks.

---

## 11. AI self-representation and internal state visualization

- **"Feature Visualization"** (Olah, Mordvintsev, Schubert) — Distill 2017 — Seminal work generating images that maximally activate specific neurons, revealing learned visual abstractions across network layers.

- **"The Building Blocks of Interpretability"** (Olah et al.) — Distill 2018 — Combines feature visualization with attribution for rich human-interpretable explanations of neural network decisions.

- **"Scaling Monosemanticity: Extracting Interpretable Features from Claude 3 Sonnet"** — Anthropic, 2024 — Scales sparse autoencoders to extract **millions of interpretable features** that are multilingual, multimodal, and can steer model behavior.

- **"Towards Monosemanticity: Decomposing Language Models With Dictionary Learning"** — Anthropic, 2023 — Demonstrates sparse autoencoders decomposing transformer activations into interpretable monosemantic features.

- **"Representation Engineering: A Top-Down Approach to AI Transparency"** — arXiv:2310.01405 — Introduces RepE for reading and **controlling high-level cognitive phenomena** (honesty, harmlessness, power-seeking) in LLMs via Linear Artificial Tomography.

- **"Open Problems in Mechanistic Interpretability"** — arXiv:2501.16496 — Major survey of open problems in understanding neural network mechanisms for AI assurance.

- **"Decoding Emotion in the Deep: How LLMs Represent, Retain, and Express Emotion"** — arXiv:2510.04064 — Reveals LLMs develop a well-defined internal **"emotional geometry"** that emerges early and persists over long sequences.

- **"From Imitation to Introspection: Probing Self-Consciousness in Language Models"** — arXiv:2410.18819 — Investigates emergence of self-consciousness in LLMs using causal structural games testing four stages of self-awareness.

- **"Consciousness in Artificial Intelligence: Insights from the Science of Consciousness"** — arXiv:2308.08708 — Assesses AI systems against neuroscientific consciousness theories. Finds no current AI is conscious but **no fundamental barriers exist**.

- **"Emergent Linear Representations in World Models of Self-Supervised Sequence Models"** — arXiv:2309.00941 — Shows sequence models develop **linear internal representations** of state that can be read and manipulated via vector arithmetic.

- **"Unlocking Feature Visualization for Deeper Networks with MACO"** — arXiv:2306.06805 — Scales feature visualization to modern networks (ResNet, ViT) by optimizing phase spectrum while keeping magnitude constant.

- **"Sparse Autoencoders Learn Monosemantic Features in Vision-Language Models"** — arXiv:2504.02821 — Extends SAE-based feature discovery to multimodal models (CLIP, LLaVA), revealing hierarchical visual-linguistic representations.

- **"Concept Bottleneck Models"** — arXiv:2007.04612 — Constrains neural predictions through human-interpretable concept activations, enabling concept-level intervention and debugging.

- **"Discover-then-Name: Task-Agnostic Concept Bottlenecks via Automated Concept Discovery"** — arXiv:2407.14499 — Uses sparse autoencoders to automatically discover and name visual concepts for concept bottleneck models.

---

## 12. Noise scheduling and sampling methods

- **"Denoising Diffusion Implicit Models (DDIM)"** — arXiv:2010.02502 — Foundational non-Markovian deterministic sampling for DDPMs enabling **10–50× faster** sampling and latent interpolation.

- **"DPM-Solver: A Fast ODE Solver for Diffusion Probabilistic Model Sampling in Around 10 Steps"** — arXiv:2206.00927 — Dedicated high-order ODE solver analytically computing the linear solution part, achieving quality sampling in **~10 NFEs**.

- **"DPM-Solver++: Fast Solver for Guided Sampling of Diffusion Probabilistic Models"** — arXiv:2211.01095 — Extends DPM-Solver with data-prediction parameterization and dynamic thresholding. **Default fast sampler** for Stable Diffusion.

- **"DPM-Solver-v3: Improved Diffusion ODE Solver with Empirical Model Statistics"** — arXiv:2310.13268 — Uses empirical model statistics to reduce discretization errors, improving FIDs at low NFEs for both pixel and latent models.

- **"UniPC: A Unified Predictor-Corrector Framework for Fast Sampling of Diffusion Models"** — arXiv:2302.04867 — Unifies predictor-corrector methods into a single framework achieving consistent quality across model types with few NFEs.

- **"Fast Sampling of Diffusion Models with Exponential Integrator (DEIS)"** — arXiv:2204.13902 — Exploits semilinear ODE structure for high-quality generation with fewer NFEs than DDIM and PNDM.

- **"SA-Solver: Stochastic Adams Solver for Fast Sampling of Diffusion Models"** — arXiv:2309.05019 — Stochastic Adams method with variance-controlled noise injection achieving SOTA FID through efficient multi-step sampling.

- **"Pseudo Numerical Methods for Diffusion Models on Manifolds (PNDM)"** — arXiv:2202.09778 — Reformulates DDPM/DDIM sampling as pseudo numerical methods on manifolds with pseudo linear multi-step methods.

- **"DC-Solver: Improving Predictor-Corrector Diffusion Sampler via Dynamic Compensation"** — arXiv:2409.03755 — Dynamically compensates for trajectory misalignment using cascade polynomial regression.

- **"Elucidating the Design Space of Diffusion-Based Generative Models (EDM)"** — arXiv:2206.00364 — Landmark paper decoupling diffusion design choices. Introduces the **Karras noise schedule**, Heun sampler, achieving **1.79 FID on CIFAR-10**.

- **"Analyzing and Improving the Training Dynamics of Diffusion Models (EDM2)"** — arXiv:2312.02696 — Magnitude-preserving network redesign and post-hoc EMA selection achieving **1.81 FID on ImageNet-512**.

- **"On the Importance of Noise Scheduling for Diffusion Models"** — arXiv:2301.10972 — Demonstrates optimal noise scheduling varies significantly with image resolution and proposes adaptation methods.

- **"Improved Noise Schedule for Diffusion Training"** — arXiv:2407.03297 — logSNR-based noise schedule improving training efficiency and surpassing the cosine schedule on ImageNet.

- **"Align Your Steps: Optimizing Sampling Schedules in Diffusion Models"** — arXiv:2404.14507 — Uses stochastic calculus to **automatically optimize** noise level schedules for any number of steps.

- **"Flow Matching for Generative Modeling"** — arXiv:2210.02747 — Foundational simulation-free method for training continuous normalizing flows using Gaussian conditional probability paths.

- **"Stochastic Interpolants: A Unifying Framework for Flows and Diffusions"** — arXiv:2303.08797 — Unifies flow-based and diffusion-based models through stochastic interpolants bridging arbitrary densities.

- **"Building Normalizing Flows with Stochastic Interpolants"** — arXiv:2209.15571 — Precursor simulation-free CNF training via interpolant probability currents.

- **"SiT: Exploring Flow and Diffusion-based Generative Models with Scalable Interpolant Transformers"** — arXiv:2401.08740 — DiT architecture using stochastic interpolant framework with tunable diffusion coefficients.

- **"Consistency Flow Matching: Defining Straight Flows with Velocity Consistency"** — arXiv:2407.02398 — Enforces self-consistency in velocity fields, unifying consistency models and rectified flows.

- **"Discrete Flow Matching"** — arXiv:2407.15595 — Extends flow matching to discrete data domains, achieving strong code generation without autoregression.

---

## 13. Submodular optimization applied to rendering and resource allocation

- **"Adaptive Submodularity: Theory and Applications in Active Learning and Stochastic Optimization"** — arXiv:1003.3967 — Foundational work generalizing submodular functions to adaptive policies with **greedy approximation guarantees**.

- **"Fairness in Streaming Submodular Maximization over a Matroid Constraint"** — arXiv:2305.15118 — Streaming algorithms for submodular maximization ensuring fairness in large-scale data selection.

- **"Dynamic Constrained Submodular Optimization with Polylogarithmic Update Time"** — arXiv:2305.15192 — Dynamic algorithm supporting insertions/deletions with polylogarithmic amortized update time.

- **"Streaming Non-monotone Submodular Maximization: Personalized Video Summarization on the Fly"** — arXiv:1706.03583 — First efficient single-pass streaming algorithm for non-monotone submodular maximization, **1700× faster** than prior work.

- **"Video Summarization by Learning Submodular Mixtures of Objectives"** — CVPR 2015 — Jointly optimizes multiple submodular objectives for video summarization with near-optimal greedy approximation.

- **"Stochastic Multi-round Submodular Optimization with Budget"** — arXiv:2404.13737 — Adaptive budget-constrained multi-round submodular maximization with ≈0.316-approximation algorithm.

- **"Fully Dynamic Submodular Maximization over Matroids"** — arXiv:2305.19918 — Randomized algorithm maintaining a 4-approximate solution under matroid constraints in fully dynamic settings.

---

## 14. Quantum-inspired classical algorithms

- **"A Quantum-Inspired Classical Algorithm for Recommendation Systems"** (Tang) — arXiv:1807.04271 — **Seminal dequantization** showing the quantum recommendation algorithm has a classical analog using ℓ²-norm sampling in O(poly(k)log(mn)) time.

- **"Sampling-based Sublinear Low-rank Matrix Arithmetic Framework for Dequantizing Quantum Machine Learning"** — arXiv:1910.06151 — Unified classical framework dequantizing essentially **all known quantum ML algorithms** including PCA, regression, and SDP solving.

- **"Dequantizing Algorithms to Understand Quantum Advantage in Machine Learning"** — Nature Reviews Physics 4, 2022 — Perspective explaining dequantization methods and when quantum ML provides genuine vs. illusory speedups.

- **"Tensor Networks in Machine Learning"** — arXiv:2207.02851 — Comprehensive survey on tensor network methods (MPS, PEPS, TTN) as ML models and for finding tensor decompositions.

- **"Towards Quantum Machine Learning with Tensor Networks"** — arXiv:1803.11537 — Quantum-classical unified framework with circuits based on tree and MPS tensor networks trainable classically then transferred to quantum hardware.

- **"Synergy Between Quantum Circuits and Tensor Networks"** — arXiv:2208.13673 — Uses tensor network simulations to pre-optimize parametrized quantum circuits, improving trainability and addressing barren plateaus.

---

## 15. Scene graphs and spatial data structures for rendering

- **"Instant Neural Graphics Primitives with a Multiresolution Hash Encoding"** — arXiv:2201.05989 — NVIDIA's breakthrough enabling **near-instant NeRF training** via multiresolution hash table encoding. Foundational for hash-grid neural representations.

- **"Maximizing Parallelism in the Construction of BVHs, Octrees, and k-d Trees"** (Karras) — HPG 2012 — Fully parallel GPU algorithm for constructing binary radix trees using **Morton codes and space-filling curves**. Seminal method for real-time BVH on GPUs.

- **"Fast Parallel Construction of High-Quality Bounding Volume Hierarchies"** — HPG 2013 — GPU BVH treelet restructuring achieving **~90% of offline SAH quality** while maintaining fast construction.

- **"A Survey on Bounding Volume Hierarchies for Ray Tracing"** — Computer Graphics Forum 40(2), 2021 — Comprehensive survey of BVH construction, traversal, and optimization for modern GPU ray tracing including hardware RT cores.

- **"Perfect Spatial Hashing"** — ACM TOG (SIGGRAPH) 2006 — Collision-free multidimensional hash for GPU-friendly packing of sparse spatial data preserving coherence.

- **"Optimized Spatial Hashing for Collision Detection of Deformable Objects"** — VMV 2003 — Seminal spatial hashing for real-time collision detection compressing infinite spatial grids.

- **"Real-time 3D Reconstruction at Scale using Voxel Hashing"** — ACM TOG (SIGGRAPH Asia) 2013 — Spatial hashing for volumetric TSDF sub-blocks enabling memory-efficient GPU-parallel surface reconstruction.

- **"Hardware Acceleration of Neural Graphics"** — arXiv:2303.05735 — Hardware-accelerated processing clusters for neural graphics (hash grid + MLP), achieving significant performance over GPU-only approaches.

---

## 16. Color science and perceptual rendering with formal guarantees

- **"A Perceptual Color Space for Image Processing (Oklab)"** — bottosson.github.io/posts/oklab — Perceptual color space predicting lightness, chroma, and hue. Uses IPT structure optimized against CAM16-UCS. Adopted by **CSS, Photoshop**, and numerous libraries.

- **"The CIECAM02 Color Appearance Model"** — IS&T Color Imaging Conference, 2002 — Defines CIECAM02 with CAT02 chromatic adaptation and correlates for brightness, lightness, colorfulness, chroma, saturation, and hue. De facto standard until CAM16.

- **"Good Colour Maps: How to Design Them"** — arXiv:1509.03700 — Designing perceptually uniform color maps using CIELAB ensuring uniform perceptual lightness changes.

- **"A Gamut-Mapping Framework for Color-Accurate Reproduction of HDR Images"** — arXiv:1711.08925 — Parameter-free gamut and tone management framework integrating luminance and chroma compression in perceptual color spaces.

- **"Tone Reproduction and Physically Based Spectral Rendering"** — Eurographics STAR, 2002 — Survey covering spectral rendering data structures and tone reproduction for replacing RGB with spectral representations.

- **"Towards Perceptual Control of Physically Based Spectral Rendering"** — Computers & Graphics 27(5), 2003 — Spectral rendering with **CIE LAB color distance** for adaptive computation accuracy.

- **"The Fundamentals of Gamut Mapping: A Survey"** — Color Research & Application, 2001 — Foundational taxonomy of gamut mapping algorithms covering clipping vs. compression, global vs. spatial.

---

## 17. 3D neural representations

- **"NeRF: Representing Scenes as Neural Radiance Fields for View Synthesis"** — arXiv:2003.08934 — **The original NeRF paper.** Continuous 5D neural radiance fields enabling photorealistic novel view synthesis via differentiable volume rendering.

- **"Mip-NeRF: A Multiscale Representation for Anti-Aliasing Neural Radiance Fields"** — arXiv:2103.13415 — Anti-aliased conical frustums instead of rays, reducing error **17–60%** while being faster and smaller than NeRF.

- **"Mip-NeRF 360: Unbounded Anti-Aliased Neural Radiance Fields"** — arXiv:2111.12077 — Non-linear scene parameterization and online distillation for unbounded 360° scenes. **57% MSE reduction**.

- **"Zip-NeRF: Anti-Aliased Grid-Based Neural Radiance Fields"** — arXiv:2304.06706 — Combines mip-NeRF 360's anti-aliasing with Instant NGP's speed. **8–77% lower error** while training 24× faster.

- **"3D Gaussian Splatting for Real-Time Radiance Field Rendering"** — arXiv:2308.04079 — Foundational 3DGS using anisotropic Gaussians with optimized rasterization for **real-time (≥30 fps) novel-view synthesis at 1080p**.

- **"2D Gaussian Splatting for Geometrically Accurate Radiance Fields"** — arXiv:2403.17888 — Oriented planar Gaussian disks for view-consistent geometry with perspective-correct splatting and accurate surface reconstruction.

- **"SuGaR: Surface-Aligned Gaussian Splatting for Efficient 3D Mesh Reconstruction"** — arXiv:2311.12775 — Aligns Gaussians with surfaces for high-quality textured mesh extraction, bridging Gaussians and mesh pipelines.

- **"4D Gaussian Splatting: Modeling Dynamic Scenes with Native 4D Primitives"** — arXiv:2412.20720 — Spatiotemporal 4D Gaussian primitives for real-time photorealistic dynamic scene rendering.

- **"DreamGaussian4D: Generative 4D Gaussian Splatting"** — arXiv:2312.17142 — Generates animated 4D content with Gaussians and spatial transformations at **~10× acceleration** over prior methods.

- **"EAGLES: Efficient Accelerated 3D Gaussians with Lightweight EncodingS"** — arXiv:2312.04564 — Quantized embeddings and coarse-to-fine training reducing memory while maintaining 3DGS quality.

- **"Compression in 3D Gaussian Splatting: A Survey"** — arXiv:2502.19457 — Survey of compression methods addressing 3DGS scalability/memory from topological, fidelity, and computational perspectives.

- **"GaussianDreamerPro: Text to Manipulable 3D Gaussians"** — arXiv:2406.18462 — Text-to-3D producing manipulable Gaussian assets for downstream animation, composition, and simulation.

---

## 18. Emergent communication and agent expression

- **"Learning to Communicate with Deep Multi-Agent Reinforcement Learning (RIAL/DIAL)"** — arXiv:1605.06676 — **Seminal work.** Two approaches for agents learning communication protocols end-to-end using deep RL.

- **"Emergence of Grounded Compositional Language in Multi-Agent Populations"** (Mordatch & Abbeel) — arXiv:1703.04908 — **Seminal.** Agents develop grounded compositional language exhibiting compositionality without predefined language.

- **"Learning Multiagent Communication with Backpropagation (CommNet)"** — arXiv:1605.07736 — **Foundational.** Continuous communication via averaged hidden states enabling end-to-end backpropagation through multi-agent communication.

- **"AI Mother Tongue: Self-Emergent Communication in MARL via Endogenous Symbol Systems"** — arXiv:2507.10566 — Agents develop effective symbolic communication through VQ-VAE-based endogenous symbol systems showing **power-law distribution and compositionality**.

- **"Visual Theory of Mind Enables the Invention of Writing Systems"** — arXiv:2502.01568 — Multi-agent RL framework simulating emergent pictographic communication connecting visual theory of mind to writing systems.

- **"From Grunts to Grammar: Emergent Language from Cooperative Foraging"** — arXiv:2505.12872 — Agents develop communication with natural language properties (arbitrariness, compositionality, displacement, cultural transmission).

- **"TarMAC: Targeted Multi-Agent Communication"** — arXiv:1810.11187 — Agents learn targeted communication via attention mechanisms with interpretable multi-round communication strategies.

- **"Emergent Multi-Agent Communication in the Deep Learning Era"** (Lazaridou & Baroni) — arXiv:2006.02419 — Comprehensive survey of emergent language in deep agent communities.

- **"A Survey of Multi-Agent Deep Reinforcement Learning with Communication"** — arXiv:2203.08975 — Reviews 41 Comm-MADRL models classifying system design dimensions.

---

## 19. Murmuration-inspired algorithms

- **"Flocks, Herds, and Schools: A Distributed Behavioral Model" (Boids)** (Reynolds) — SIGGRAPH 1987 — **The foundational paper.** Three simple rules (separation, alignment, cohesion) producing emergent flocking from independent agents.

- **"Novel Type of Phase Transition in a System of Self-Driven Particles" (Vicsek Model)** — Physical Review Letters 75, 1995 — **Foundational.** Self-propelled particles aligning with neighbors demonstrate a **phase transition** from disorder to collective motion.

- **"Emergent Behavior in Flocks" (Cucker-Smale Model)** — IEEE TAC 52, 2007 — **Foundational.** Mathematical flocking model with second-order dynamics proving emergent flocking under sufficient coupling.

- **"Interaction Ruling Animal Collective Behavior Depends on Topological Rather than Metric Distance"** — PNAS 105(4), 2008 — **Landmark empirical paper.** 3D reconstruction of starling flocks reveals each bird interacts with **~6–7 neighbors by rank**, not Euclidean distance.

- **"Scale-free Correlations in Starling Flocks"** — PNAS 107(26), 2010 — Velocity correlations in flocks are **scale-free**, suggesting flocks operate at criticality for maximal environmental response.

- **"Self-organized Aerial Displays of Thousands of Starlings (StarDisplay)"** — Behavioral Ecology 21(6), 2010 — Combines standard rules with starling-specific aerodynamics and topological interaction, generating patterns matching empirical Rome flock data.

- **"Statistical Mechanics for Natural Flocks of Birds"** — PNAS 109(13), 2012 — Maximum entropy models from experimental correlations confirm local pairwise interactions predict whole-flock order propagation.

- **"Emergent Dynamics of the Cucker-Smale Flocking Model and Its Variants"** — arXiv:1604.04887 — Comprehensive review of Cucker-Smale variants with flocking theorems, convergence proofs, and interaction topologies.

- **"Modeling Collective Motion: Variations on the Vicsek Model"** — EPJ B 64, 2008 — Reviews Vicsek model variations showing how different universality classes emerge from symmetry arguments.

- **"Flocks, Herds, and Schools: A Quantitative Theory of Flocking" (Toner-Tu Theory)** — Physical Review E 58, 1998 — **Foundational hydrodynamic theory.** Proves existence of long-range order in 2D flocking systems (unlike equilibrium), establishing field-theoretic framework.

- **"Self-Organized Criticality: An Explanation of 1/f Noise" (BTW Sandpile)** — Physical Review Letters 59(4), 1987 — **Foundational SOC paper.** Large dissipative systems naturally evolve to critical states with scale-invariant structures, explaining why swarms operate near phase transitions.

- **"Starling Flock Networks Manage Uncertainty in Consensus at Low Cost"** — PLoS Computational Biology, 2013 — Explains why starlings interact with **~7 neighbors**: optimizes balance between group cohesion and individual effort under sensing uncertainty.

---

## 20. Real-time constraint solving

- **"The Cassowary Linear Arithmetic Constraint Solving Algorithm"** — ACM TOCHI 8(4), 2001 — **Seminal paper.** Incremental constraint solver based on dual simplex for linear equalities/inequalities with required and preferred constraints. Basis of **Apple Auto Layout**.

- **"Position Based Dynamics"** (Müller et al.) — JVCIR 18(2), 2007 — **Foundational.** Directly manipulates positions to satisfy geometric constraints in real time. Standard for game physics (cloth, soft bodies, deformables).

- **"XPBD: Position-Based Simulation of Compliant Constrained Dynamics"** — MIG 2016 — Resolves PBD's iteration/timestep stiffness issues, enabling accurate elastic simulation with **physically meaningful material parameters and constraint force estimates** for haptics.

- **"Compositional Diffusion-Based Continuous Constraint Solvers"** — arXiv:2309.00966 — Learns to solve continuous constraint satisfaction by composing diffusion model energies via factor graphs, generalizing to novel constraint combinations.

---

## Cross-domain bridges worth highlighting

Several papers above bridge multiple domains simultaneously and are especially valuable for this system:

- **"NumFuzz / Bean" (Kellison)** — arXiv:2405.04612 / arXiv:2501.14550 — Bridges **formal verification + graded monads + numerical computing**. Uses the neighborhood monad for float error bounds — directly applicable to verified color bounds and animation constraints.

- **"Dex"** — arXiv:2104.05372 — Bridges **functional programming + GPU + automatic differentiation**. Dependent types for safe array indexing with an effect system exposing parallelism, compiling to CPU/GPU.

- **"Granule"** — ICFP 2019 — Bridges **graded monads + coeffects + quantitative reasoning**. A practical language demonstrating how graded modal types track resources — the theoretical backbone for co-effect equations in a rendering pipeline.

- **"GameNGen"** — arXiv:2408.14837 — Bridges **real-time diffusion + world models**. Proves diffusion can run a game engine at 20+ FPS, directly validating the real-time diffusion rendering concept.

- **"StreamDiffusion"** — arXiv:2312.12491 — Bridges **real-time diffusion + pipeline optimization**. The 100+ FPS throughput via batched denoising is the closest existing work to the res4lyf-style real-time rendering pipeline.

- **"XPBD"** — MIG 2016 — Bridges **constraint solving + haptics + real-time physics**. Constraint force estimates enable haptic feedback, directly applicable to the haptic-parameterized system.

- **"FLAME GPU"** — flamegpu.com — Bridges **massive agent simulation + GPU + visualization**. The most directly relevant framework for rendering 1 billion agent states as visual outputs on GPUs.

- **"Multimodal GUI Architecture for LLM Assistants"** — arXiv:2510.06223 — Bridges **voice interaction + UI generation + MCP protocol**. Exactly the voice-driven blank-screen-to-anything architecture being built.

---

## Conclusion

This survey maps **190+ papers** onto the 20 research domains required for a universal WebGPU rendering engine. The densest clusters of directly applicable work are in **real-time diffusion acceleration** (consistency models, adversarial distillation, and StreamDiffusion provide a clear path to 60fps diffusion rendering), **3D Gaussian Splatting** (the fastest path to real-time neural 3D), and **graded monads/coeffects** (Granule and NumFuzz provide the type-theoretic foundation for effect-tracked rendering pipelines with formal guarantees).

The most significant gaps in existing literature are in **WebGPU-specific academic work** (only the DarthShader fuzzing paper directly targets WGSL), **Haskell-to-WebGPU compilation** (no existing paper addresses this directly — Accelerate, Futhark, and Obsidian target CUDA/OpenCL), and **AI self-representation visualization** (the interpretability tools exist but no paper proposes letting AI choose its own visual representation as a first-class design goal). These gaps represent the genuinely novel contributions this system would make to the field.