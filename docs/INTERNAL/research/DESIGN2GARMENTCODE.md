# Design2GarmentCode: Turning Design Concepts to Tangible Garments Through Program Synthesis

**arXiv:** 2412.08603  
**Authors:** Feng Zhou, Ruiyang Liu, Chen Liu, Gaofeng He, Yong-Lu Li, Xiaogang Jin, Huamin Wang  
**Institution:** Zhejiang Sci-Tech University, Style3D Research, Shanghai Jiao Tong University, Zhejiang University  
**Date:** April 9, 2025  
**Domain:** Computer Graphics / Program Synthesis / Fashion AI

---

## Abstract

Design2GarmentCode uses Large Multimodal Models (LMMs) to generate parametric sewing pattern programs from multi-modal design concepts (text, images, sketches). The key insight is representing sewing patterns as symbolic programs (GarmentCode DSL), enabling precise geometric control while leveraging LLM knowledge.

**Key Contributions:**
- Neurosymbolic approach: LLM + DSL program synthesis
- Multi-modal input: text, images, sketches
- Centimeter-level precision via parametric programs
- Minimal fine-tuning required

---

## 1. Problem: From Design to Garment

### 1.1 The Gap

Generative AI creates designs, but turning them into wearable garments requires:
- Precise geometric patterns
- Correct stitching relationships
- Centimeter-level accuracy

### 1.2 Prior Approaches

| Method | Problem |
|--------|---------|
| **Neural networks** | Statistical approximation loses precision |
| **Vector quantization** | Oversimplified patterns |
| **Direct generation** | Self-intersections, stitching errors |

### 1.3 Key Insight

> Use LLMs to generate **programs** (not patterns directly)

Programs provide:
- Precise geometric control
- Semantic meaning
- Editability
- Composability

---

## 2. Methodology: Neurosymbolic Pipeline

### 2.1 Architecture Overview

```
Multi-Modal Input (text/image/sketch)
           │
           ▼
   ┌───────────────┐
   │  LMM (MMUA)  │  ← Design Understanding
   └───────────────┘
           │
           ▼
   ┌───────────────┐
   │  DSL-GA      │  ← Program Synthesis
   │  (Fine-tuned)│
   └───────────────┘
           │
           ▼
   ┌───────────────┐
   │ GarmentCode   │  ← Program Execution
   │   Engine      │
   └───────────────┘
           │
           ▼
   Sewing Patterns + 3D Garments
```

### 2.2 GarmentCode DSL

Sewing patterns as symbolic programs:

```python
# Example GarmentCode program
Pattern:
  Bodice(
    neckline = V_neck,
    sleeve = short_sleeve,
    length = 45cm
  )
  
  Skirt(
    flare = A_line,
    pleats = box_pleats,
    length = 60cm
  )
  
  Sew(bodice, skirt)
```

**Mathematical Formulation:**
```
S = ⟨F, D, B⟩ = ∪_{fi∈F, di∈D} fi(di, B)
```

Where:
- F = symbolic programs
- D = design configurations
- B = body measurements

### 2.3 Two-Agent System

**1. DSL Generation Agent (DSL-GA)**
- Fine-tuned LLM
- Learns GarmentCode syntax and semantics
- Generates prompts and programs

**2. Multi-Modal Understanding Agent (MMUA)**
- Pre-trained LMM
- Interprets design inputs
- Extracts topological and geometric features

### 2.4 Training Process

**Step 1: Program Learning**
```
1. Provide GarmentCode examples to LLM
2. LLM comments on programs with drafting instructions
3. Fine-tune with LoRA: Γ_ft(Γ_cmt(fi)) → fi
```

**Step 2: Prompt Synthesis**
```
DSL-GA generates questions about design parameters:
  P = Γ_ft(D) = ∪_{di∈D} Γ_ft(di)
```

**Step 3: Program Synthesis**
```
1. MMUA answers questions about design input
2. Projector transforms answers to parameters
3. Generate GarmentCode program
```

### 2.5 Parameter Quantization

For numerical parameters:

```python
def quantize(di, precision=0.01):
    if isinstance(di, bool): return 0/1
    if isinstance(di, int): return di
    if isinstance(di, float): 
        return int(di * 100)  # centimeter precision
    # selective variables use index lookup
```

---

## 3. Technical Details

### 3.1 GarmentCode Syntax

**Hierarchical Structure:**
```
Garment
  ├── Component (panel)
  │     ├── Curve (parametric)
  │     ├── Point
  │     └── Sew relation
  ├── Assembly
  │     └── Interface functions
  └── Configuration
        ├── Topological (DT)
        └── Geometrical (DG)
```

### 3.2 Validation Loops

**Rule-based Validation:**
- Check completeness of generated parameters
- Verify geometric constraints
- Ensure valid panel connections

**Design Comparison:**
- Compare generated garment to input
- Generate correction instructions
- Iterative refinement

### 3.3 Precision Control

| Parameter Type | Precision | Method |
|---------------|-----------|--------|
| Boolean | Exact | 0/1 |
| Integer | Exact | Direct |
| Float (cm) | 0.01 | λ = 100 scaling |
| Selective | Discrete | Index lookup |

---

## 4. Experimental Results

### 4.1 Quality Metrics

| Method | SSR ↑ | Agreement ↑ | Aesthetic ↑ | F-Score ↑ | CD ↓ |
|--------|-------|-------------|--------------|------------|------|
| DressCode | 84% | 7.17% | 9.50% | 0.616 | 15.77 |
| **Ours** | **100%** | **79.83%** | **68.17%** | — | — |
| SewFormer | 65% | 3.33% | 5.33% | 0.708 | 9.7 |
| **Ours** | **94%** | **88.67%** | **77%** | **0.829** | **2.09** |

### 4.2 Key Improvements

1. **100% structurally valid patterns** (no self-intersections)
2. **Correct stitching** (proper panel connections)
3. **Centimeter-level precision**
4. **Multi-modal flexibility**

### 4.3 Training Efficiency

| Aspect | Previous Methods | Design2GarmentCode |
|--------|-----------------|-------------------|
| Training data | Large paired dataset | Minimal fine-tuning |
| Model size | Train from scratch | Pre-trained LLM + lightweight projector |
| Fine-tuning | N/A | LoRA on small dataset |

---

## 5. Relation to Hydrogen

### 5.1 Direct Mapping to Schema

This paper demonstrates the exact pattern Hydrogen needs for design systems:

| GarmentCode Concept | Hydrogen Schema |
|--------------------|-----------------|
| Symbolic programs | Schema atoms |
| Design parameters | Atom properties |
| Body measurements | Context/dimensions |
| Garment assembly | Compound elements |
| Precision (cm) | Bounded types |

### 5.2 Schema Generation Pipeline

```
User Intent (multi-modal)
           │
           ▼
   ┌───────────────┐
   │  LLM (LMM)   │  ← Understand design
   └───────────────┘
           │
           ▼
   ┌───────────────┐
   │ Program       │  ← Synthesize schema
   │ Synthesizer   │
   └───────────────┘
           │
           ▼
   Hydrogen Schema (PureScript)
           │
           ▼
   Element → GPU → Rendered UI
```

### 5.3 Bounded Type Implementation

```purescript
-- Hydrogen schema with precision bounds
type Pixel = Bounded 0 255  -- centimeter → pixel mapping
type Centimeter = Bounded 0 200  -- clothing dimensions
type Degree = Bounded 0 360  -- angles

-- GarmentCode-style parametric element
data GarmentComponent
  = Bodice BodiceConfig
  | Skirt SkirtConfig  
  | Sleeve SleeveConfig

-- Precision is guaranteed by type system
bodice :: BodiceConfig -> Element msg
bodice cfg = 
  E.path_ 
    [ E.strokeWidth (toPixel (length cfg)) ]
    (generateCurves cfg)
```

### 5.4 Multi-Modal Schema Input

```purescript
-- Generate schema from multiple inputs
generateSchema :: Input -> Schema
generateSchema input = case input of
  Text t -> llmInterpret t >>= synthesizeSchema
  Image i -> llmExtractFeatures i >>= synthesizeSchema  
  Sketch s -> llmParseVector s >>= synthesizeSchema
  Multi ts -> combineFeatures ts >>= synthesizeSchema
```

---

## 6. Key Insights for Hydrogen

### 6.1 Program Synthesis > Direct Generation

| Approach | Precision | Editability | Correctness |
|----------|-----------|-------------|--------------|
| Neural generation | Statistical | Limited | Errors common |
| Program synthesis | Exact | Full | Verified |

### 6.2 Domain-Specific Languages

GarmentCode shows DSLs work for design:
- **GarmentCode** → sewing patterns
- **Hydrogen Schema** → UI elements
- **WGSL** → GPU shaders

### 6.3 Compositional Semantics

Program synthesis provides:
- Hierarchical composition
- Parameterized components  
- Verified constraints
- Deterministic output

### 6.4 LLM + DSL Hybrid

```
LLM strengths:    Semantic understanding, generalization
DSL strengths:    Precision, verification, executability

Together:         Best of both worlds
```

---

## 7. Technical Specifications

### 7.1 Parameter Types

| Type | Representation | Range | Precision |
|------|---------------|-------|-----------|
| Boolean | 0/1 | {0, 1} | Exact |
| Integer | Direct | ℤ | Exact |
| Float | Scaled int | ℝ | 0.01 |
| Selective | Index | {L[i]} | Discrete |

### 7.2 Hierarchy Levels

```
Garment
  └── Component (Panel)
        └── Curve (Parametric)
              └── Control Points
                    
Component connections via:
  - Sew relations
  - Interface functions  
  - Topology parameters
```

### 7.3 Validation Rules

- **Completeness:** All required parameters present
- **Consistency:** Related parameters compatible
- **Geometric validity:** No self-intersections
- **Physical feasibility:** Valid garment structure

---

## 8. Citation

```bibtex
@article{zhou2024design2garmentcode,
  title={Design2GarmentCode: Turning Design Concepts to Tangible Garments Through Program Synthesis},
  author={Zhou, Feng and Liu, Ruiyang and Liu, Chen and He, Gaofeng and Li, Yong-Lu and Jin, Xiaogang and Wang, Huamin},
  year={2024},
  eprint={2412.08603},
  archivePrefix={arXiv},
  primaryClass={cs.GR}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
