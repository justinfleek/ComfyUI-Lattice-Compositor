# Design2GarmentCode: Turning Design Concepts to Tangible Garments Through Program Synthesis

────────────────────────────────────────────────────────────────────────────────

**Source**: garmentstocode.pdf
**Authors**: Feng Zhou et al. (Style3D Research, Zhejiang University, SJTU)
**Published**: arXiv:2412.08603v3, April 2025
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This paper presents a **neurosymbolic approach** to garment design: instead of training
neural networks to directly output sewing patterns (which fail at precision), use Large
Multimodal Models to generate **parametric programs** in a domain-specific language
(GarmentCode) that execute to produce exact patterns.

**Key Innovation**: Treat sewing pattern generation as **program synthesis**, not
image generation. LMMs understand design intent; DSL execution guarantees precision.

**Results**:
- 100% simulation success rate (vs 84% DressCode, 65% SewFormer)
- 80% user agreement on design fidelity (vs 7% baselines)
- Works with text, images, sketches, or combinations
- 10× more compact representation than vector-quantized methods
- Generates novel garment components as reusable parametric code

**Core Insight**: Neural networks provide statistical approximations — fine for images,
fatal for sewing patterns that need centimeter-level precision. Programs are exact.

**Practical Impact**: Democratizes parametric pattern-making by removing need for
coding skills. Designers describe; system synthesizes code.

────────────────────────────────────────────────────────────────────────────────

## 1. The Problem

### The Gap Between Design and Production

Sewing patterns are the **essential bridge** between design concepts and producible
garments. They specify exact shapes and dimensions of fabric pieces for assembly.

**Traditional Approach**: Manual drafting by professionals with years of practice
- Inefficient, error-prone
- Can't meet demand for personalization
- High barrier to entry

### Why Neural Networks Fail

Existing learning-based approaches (DressCode, SewFormer, NeuralTailor) have
fundamental problems:

| Problem | Consequence |
|---------|-------------|
| **Statistical approximation** | Centimeter precision impossible |
| **Oversimplified outputs** | Miss design details (necklines, cuffs, asymmetry) |
| **Wrong stitches** | Panels sewn incorrectly → draping failure |
| **Self-intersecting panels** | Geometrically invalid patterns |
| **Limited diversity** | Default to simple shapes regardless of prompt |
| **Data hungry** | Need massive paired datasets |

**Example failures** (Figure 2 in paper):
- DressCode: Always outputs V-neck regardless of prompt specifying other necklines
- SewFormer: Pant side seam stitched to shirt shoulder seam

### The Precision Problem

> "Sewing patterns require centimeter-level precision to ensure proper garment fit,
> which presents a significant challenge for neural networks that only provide
> statistical approximations."

A 2cm error in a bodice pattern means the garment won't fit. Neural networks
cannot guarantee this precision — but symbolic programs can.

────────────────────────────────────────────────────────────────────────────────

## 2. The Solution: Program Synthesis via LMMs

### Core Insight

Instead of training networks to output patterns directly, use LMMs to generate
**parametric programs** that execute to produce patterns:

```
Traditional:  Design Image → Neural Network → Vector Pattern (imprecise)
This paper:   Design Image → LMM → GarmentCode Program → Exact Pattern
```

### Why Programs?

1. **Precision**: Programs execute deterministically with exact arithmetic
2. **Interpretability**: Human-readable code, not opaque vectors
3. **Editability**: Modify parameters, not retrain models
4. **Reusability**: Generated components become library functions
5. **Compactness**: 122 parameters vs 1500+ tokens in DressCode

### The Neurosymbolic Pipeline

```
┌─────────────────────────────────────────────────────────────────────┐
│  MULTIMODAL INPUT                                                   │
│  (text + image + sketch)                                           │
└────────────────────────────────┬────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────┐
│  MMUA (Pre-trained LMM)                                             │
│  - Interprets design intent                                         │
│  - Answers questions about topology and geometry                   │
└────────────────────────────────┬────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────┐
│  DSL-GA (Fine-tuned LLM)                                           │
│  - Generates GarmentCode syntax                                     │
│  - Produces design configuration                                   │
└────────────────────────────────┬────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────┐
│  GarmentCode Execution Engine                                       │
│  - Executes parametric programs                                     │
│  - Outputs precise 2D sewing patterns                              │
│  - Runs cloth simulation → 3D garment                              │
└─────────────────────────────────────────────────────────────────────┘
```

### Leveraging Pre-trained Knowledge

LLMs already contain pattern-making knowledge:

> "When prompted with 'How to draft a basic upper body bodice?', LLMs can produce
> drafting instructions that align with conventional practices."

The system **aligns** this embedded knowledge with GarmentCode's specific syntax
via LoRA fine-tuning — no massive paired datasets needed.

────────────────────────────────────────────────────────────────────────────────

## 3. GarmentCode DSL

### What is GarmentCode?

A domain-specific language for parametric sewing patterns. Each garment is specified as:

```
S = ⟨F, D, B⟩ = ∪_{fi∈F, di∈D} fi(di, B)
```

Where:
- **F** = Set of symbolic programs (component functions)
- **D** = Design configurations (topological + geometrical parameters)
- **B** = Body measurements

### Hierarchical Component Structure

```
Garment
├── Bodice
│   ├── Front Panel (parametric curves)
│   ├── Back Panel
│   └── Darts
├── Sleeves
│   ├── Sleeve Panel
│   └── Cuff
├── Collar
│   └── Collar Panel
└── Skirt
    ├── Front Panel
    └── Back Panel
```

### Parameter Types

| Type | Example | Encoding |
|------|---------|----------|
| **Boolean** | has_collar | 0 or 1 |
| **Integer** | num_layers | Direct value |
| **Float** | sleeve_length | λ × Norm(value), λ=100 for cm precision |
| **Selective** | neckline_type | Index into option list |

### Design Configuration

Fixed 122 parameters regardless of complexity:
- **Topological (DT)**: Which components exist, how many
- **Geometrical (DG)**: Dimensions when combined with body measurements

This fixed-length representation is **10× more compact** than DressCode's
variable-length 1500+ token sequences.

────────────────────────────────────────────────────────────────────────────────

## 4. System Architecture

### Two-Agent Design

**1. DSL Generation Agent (DSL-GA)**
- Base: Pre-trained LLM (e.g., LLaMA)
- Fine-tuned via LoRA on GarmentCode examples
- Responsibilities:
  - Generate prompts for MMUA
  - Synthesize GarmentCode programs
  - Output design configurations

**2. Multi-Modal Understanding Agent (MMUA)**
- Base: Pre-trained LMM (e.g., GPT-4V)
- NOT fine-tuned — uses zero-shot capabilities
- Responsibilities:
  - Interpret multimodal design inputs
  - Answer questions about design features
  - Compare generated vs. input for refinement

### Training Pipeline

**Program Learning** (One-time fine-tuning):

```
1. Take existing GarmentCode programs F
2. Use DSL-GA to generate natural language comments
3. Create pairs: (comment, code)
4. Fine-tune DSL-GA via LoRA: given comment → predict code
```

Result: DSL-GA learns GarmentCode syntax and parameter semantics.

### Inference Pipeline

```
1. PROMPT SYNTHESIS
   DSL-GA analyzes design config D
   Generates structured questions for each parameter
   Questions are multiple-choice (better MMUA accuracy)

2. DESIGN UNDERSTANDING  
   MMUA receives: questions + multimodal input
   Returns: descriptive answers ("full length", "crew neck", etc.)

3. PROGRAM SYNTHESIS
   DSL-GA encodes MMUA answers
   Lightweight projector Ψ maps to precise parameters
   Output: GarmentCode program + config file

4. EXECUTION
   GarmentCode engine runs program
   Outputs: 2D sewing patterns + 3D draped simulation

5. VALIDATION (Optional)
   MMUA compares generated vs. input
   Suggests corrections ("make sleeve longer")
   Loop back to step 3
```

### The Projector Ψ

A lightweight text-conditioned decoder-only transformer:
- Input: DSL-GA embeddings of MMUA answers
- Output: Quantized parameter tokens

Quantization function Q:
```
Q(d) = 
  0/1           if boolean
  d             if integer  
  100×Norm(d)   if float (centimeter precision)
  Index(d, L)   if selective (from option list)
```

────────────────────────────────────────────────────────────────────────────────

## 5. Results

### Quantitative Comparison

| Metric | DressCode | Ours (Text) | SewFormer | Ours (Image) |
|--------|-----------|-------------|-----------|--------------|
| **SSR** (Simulation Success Rate) | 84% | **100%** | 65% | **94%** |
| **Agreement** (user study) | 7% | **80%** | 3% | **89%** |
| **Aesthetic** (user study) | 10% | **68%** | 5% | **77%** |
| **Avg Panels** | 5.1 | 6.9 | 10.1 | 11.0 |
| **Avg Stitches** | 10.1 | **18.7** | 15.8 | **27.9** |

### Why 100% Simulation Success?

Because programs execute exactly. No self-intersecting panels, no wrong stitches.
The GarmentCode DSL is **correct by construction** for valid parameters.

### Qualitative Results

**Text-guided**: Captures neckline types (crew, boat, turtle), asymmetry, layered skirts
**Image-guided**: Reproduces cuffs, hoods, darts, asymmetric features
**Sketch-based**: Works with both technical sketches and artistic drawings

### Applications Beyond Generation

**1. Instruction-Based Editing**
```
"CHANGE THE PANT TO SKIRT" → Only pants modified
"MAKE THE SLEEVE SHORTER" → Only sleeves modified
```

**2. Physics-Based Editing**
Use cloth simulation pressure maps to identify tight areas → automatically
adjust patterns for comfort while preserving design.

**3. Generating New Components**
DSL-GA can synthesize entirely new GarmentCode functions (e.g., layered-skirt
component with parameters for layer count, length difference, ruffling factor).

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: Program Learning (Fine-tuning DSL-GA)

```
Input: GarmentCode program corpus F, base LLM Γ
Output: Fine-tuned DSL-GA Γft

1. For each program fi ∈ F:
   comment_i = Γ.generate_comment(fi)  # LLM explains the code
   
2. Create dataset D = {(comment_i, fi) | fi ∈ F}

3. Fine-tune Γ on D using LoRA:
   Objective: Γft(comment) → code
   
4. Validate: Γft should generate syntactically valid GarmentCode

Return Γft
```

### Algorithm 2: Prompt Synthesis

```
Input: Design configuration D, fine-tuned DSL-GA Γft
Output: Structured prompt P for MMUA

1. For each parameter di ∈ D:
   # DSL-GA generates question based on parameter semantics
   qi = Γft.generate_question(di)
   
   # Convert numerical questions to multiple-choice
   if di.type == 'float':
     qi = convert_to_choices(qi, ["short", "medium", "long", ...])

2. P = concatenate([qi for di in D])

3. Prepend analysis instructions to P

Return P
```

### Algorithm 3: Design Understanding

```
Input: Prompt P, multimodal input x, MMUA
Output: Design feature answers τ

1. For each question qi ∈ P:
   τi = MMUA(qi, x)  # Zero-shot inference
   
   # Rule-based validation
   if not valid(τi, qi.expected_type):
     τi = MMUA(qi + clarification, x)  # Retry with clarification

2. τ = {τi | qi ∈ P}

Return τ
```

### Algorithm 4: Program Synthesis

```
Input: Answers τ, fine-tuned DSL-GA Γft, projector Ψ
Output: GarmentCode program + design config

1. # Encode answers
   embeddings = Γft.encode(τ)

2. # Project to precise parameters
   D = Ψ(embeddings)  # Uses type-based quantization Q

3. # Generate program
   program = Γft.synthesize(D)

4. # Validate
   if not GarmentCode.validate(program):
     program = Γft.fix_syntax(program)

Return program, D
```

### Algorithm 5: Quantization Function Q

```
Input: Parameter value d, parameter type
Output: Quantized token t

switch(type):
  case 'boolean':
    return 1 if d else 0
    
  case 'integer':
    return d
    
  case 'float':
    # Normalize to [0,1], scale for cm precision
    return round(100 * normalize(d, d.min, d.max))
    
  case 'selective':
    return index_of(d, d.options)
```

### Algorithm 6: Validation Loop

```
Input: Generated garment G, original input x, MMUA
Output: Refined garment G'

1. comparison = MMUA.compare(render(G), x)

2. if comparison.discrepancy > threshold:
   corrections = MMUA.suggest_corrections(comparison)
   # e.g., "sleeve should be longer", "add collar"
   
   τ' = update_answers(τ, corrections)
   G' = resynthesize(τ')
   
   return validate(G', x, MMUA)  # Recurse

Return G
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Direct Parallels

**GarmentCode ↔ Hydrogen Schema**

Both are DSLs for precise specification of complex outputs:

| GarmentCode | Hydrogen Schema |
|-------------|-----------------|
| Parametric sewing patterns | Parametric UI components |
| Bounded measurements (cm) | Bounded design tokens (px, rem) |
| Component hierarchy | Atom → Molecule → Compound |
| Deterministic execution | Deterministic rendering |

### Implementation Opportunities

**1. GarmentCode-like DSL for UI**

```purescript
-- Hydrogen "pattern" for a Button component
type ButtonPattern =
  { variant :: SelectiveParam ["primary", "secondary", "ghost"]
  , size :: SelectiveParam ["sm", "md", "lg"]
  , cornerRadius :: BoundedFloat 0.0 24.0
  , hasIcon :: Boolean
  , iconPosition :: SelectiveParam ["left", "right"]
  }

-- Execute pattern to Element
executeButton :: ButtonPattern -> Element Msg
executeButton pattern = 
  -- Deterministic rendering, no approximation
```

**2. LMM-to-Hydrogen Pipeline**

Following Design2GarmentCode's architecture:

```
User: "Create a dashboard with a sidebar and three chart panels"
         ↓
MMUA: Extracts layout topology, component types, styling intent
         ↓
DSL-GA: Generates Hydrogen Element code
         ↓
Execution: Deterministic render to DOM/Canvas/WebGL
```

**3. Instruction-Based UI Editing**

```purescript
-- Same pattern as garment editing
editUI :: Element Msg -> Instruction -> Element Msg
editUI ui "make the header smaller" = 
  -- Modify only header components, preserve rest
```

### Why This Matters

**The Precision Problem Applies to UI**

Just as sewing patterns need cm precision, UI needs px precision. Neural
networks generating layouts will always have alignment errors. Programs
don't.

**Multi-Modal Design Input**

Designers provide:
- Text: "A clean dashboard with blue accents"
- Images: Reference screenshots
- Sketches: Wireframes

Design2GarmentCode shows how to unify these modalities via LMM interpretation
+ DSL synthesis. Hydrogen could use the same pattern.

### Schema Completeness

The paper's 122-parameter fixed representation mirrors Hydrogen's goal of
a **complete atomic vocabulary**:

> If we enumerate all meaningful design parameters, any garment can be
> specified. If we enumerate all design atoms, any UI can be specified.

Both require completeness analysis: what parameters/atoms are necessary
and sufficient for the domain?

────────────────────────────────────────────────────────────────────────────────

## References

### Key Papers Cited

**Garment Generation**:
- Korosteleva & Sorkine-Hornung (2023) — GarmentCode DSL
- He et al. (2024) — DressCode (text-to-sewing, vector-quantized)
- Liu et al. (2023) — SewFormer (image-to-sewing)
- Korosteleva & Lee (2022) — NeuralTailor (point cloud to pattern)

**Program Synthesis**:
- Chen et al. (2021) — Codex (code generation from NL)
- Li et al. (2022) — AlphaCode (competition-level code)
- Ritchie et al. (2023) — Neurosymbolic models survey

**LLM Fine-tuning**:
- Hu et al. (2021) — LoRA (parameter-efficient fine-tuning)

### Full Citation

Zhou, F., Liu, R., Liu, C., He, G., Li, Y.-L., Jin, X., Wang, H. (2025).
"Design2GarmentCode: Turning Design Concepts to Tangible Garments Through
Program Synthesis." arXiv:2412.08603v3.
https://arxiv.org/abs/2412.08603

Project page: https://style3d.github.io/design2garmentcode

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
