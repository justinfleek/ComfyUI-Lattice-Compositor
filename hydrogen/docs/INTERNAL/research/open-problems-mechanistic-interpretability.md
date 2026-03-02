# Open Problems in Mechanistic Interpretability

**Attestation:** clarity

**Source:** Lee Sharkey et al. (Apollo Research, Anthropic, and collaborators)  
**Paper:** open-problems-in-mechanistic-interperability.pdf  
**arXiv:** 2501.16496

---

## Abstract

Mechanistic interpretability aims to understand the computational mechanisms underlying neural networks' capabilities. This forward-facing review discusses the current frontier of the field and identifies open problems that require solutions before scientific and engineering benefits can be realized. The paper covers methodological challenges, applications, and socio-technical considerations.

---

## 1. Introduction

### 1.1 What is Mechanistic Interpretability?

**Definition**: Understanding neural networks' decision-making processes by identifying the computational mechanisms underlying their capabilities.

### 1.2 Why 'Mechanistic'?

- Aims to understand the actual algorithms networks implement
- Not just input-output mappings, but internal computations
- Unlike traditional attribution methods (grad-CAM, SHAP, LIME)

### 1.3 Two Main Approaches

1. **Reverse Engineering**: Decompose network → describe components → validate
2. **Concept-based Interpretability**: Propose concepts → find corresponding components

---

## 2. Open Problems in Methods and Foundations

### 2.1 Reverse Engineering

**Goal**: Identify the functional roles of network components

#### Step 1: Neural Network Decomposition

**Problem**: Networks don't naturally decompose into architectural components (neurons, heads, layers)

**Current approaches:**
- **Dimensionality reduction**: PCA, SVD, NMF
- **Sparse Dictionary Learning (SDL)**: Based on superposition hypothesis

**Key insight - Superposition Hypothesis**:
Neural networks can represent more features than dimensions by using sparse, linear representations in activation space.

#### SDL Limitations

1. **Reconstruction errors too high**: 16M latent SAE inserted into GPT-4 caused loss equivalent to 10% compute
2. **Feature splitting**: With optimization pressure, features split into meaningless sub-features
3. **Sparsity not good proxy for interpretability**
4. **Depends on training data distribution**
5. **Assumes linear representation hypothesis** in non-linear models
6. **Feature geometry unexplained**

#### Step 2: Describing Functional Roles

**Two directions:**
- **Causes**: What makes components activate? (max activating examples, attribution)
- **Effects**: What downstream impact do components have? (logit lens, activation steering)

#### Step 3: Validation

- **Model organisms**: Small, well-understood networks (like Drosophila)
- **Ground truth testing**: Toy models with known algorithms
- **Engineering goals**: Use interpretations to modify behavior

### 2.2 Concept-Based Interpretability

**Goal**: Identify components for given roles (reverse of reverse engineering)

#### Probes

- Train classifier on hidden activations to detect concepts
- **Challenge**: Correlation vs. causation
- **Challenge**: Need well-defined concept labels

#### Open Problems

1. Need carefully chosen data for well-defined concepts
2. Probes detect correlations, not causal variables
3. Regularization for probe generalization unclear

---

## 3. Applications

### 3.1 Axes of Progress

| Axis | Description |
|------|-------------|
| Decomposition | Better network segmentation |
| Description Depth | Correlational → Causal |

### 3.2 Monitoring and Auditing

- Detect bias, deception, sycophancy
- White-box evaluations using internal representations
- **Challenge**: Distinguishing recognition vs. causation of behaviors

### 3.3 Control and Steering

- Activation steering to modify behavior
- **Challenge**: Precise, targeted control

### 3.4 Predicting Outcomes

- Use interpretability to predict model behavior on new inputs
- **Challenge**: Generalization beyond training distribution

### 3.5 Enhancing Capabilities

- Improve training, inference based on mechanistic insights

### 3.6 Extracting Knowledge

- Pull knowledge from models into human-understandable form

---

## 4. Socio-Technical Challenges

### 4.1 Current Initiatives

- Safety cases using SDL monitoring
- Interpretability for AI governance

### 4.2 Challenges

- Validating learned features capture all concerning patterns
- Human judgment required for relevance
- Risk of "interpretability illusions"

---

## 5. Key Research Questions

### 5.1 Foundational

1. **What are features?** - No satisfying formal definition
2. **What is the right decomposition?** - Still unclear
3. **Superposition** - Core hypothesis lacks conceptual clarity

### 5.2 Practical

1. **Scalability** - Methods expensive for large models
2. **Validation** - How to verify interpretations?
3. **Automation** - Circuit discovery pipelines need improvement

### 5.3 Applications

1. **Reliability** - Can we trust interpretations for safety?
2. **Generalization** - Interpretations transfer across tasks?
3. **Causality** - Correlation vs. causation in interpretations

---

## 6. Methodological Pipeline

### Circuit Discovery Pipeline

1. **Task Definition** → Select model behavior to study
2. **Identification** → Find relevant components (Ablation, activation patching)
3. **Validation** → Test if components cause behavior

### Problems with Current Pipeline

- Task definition is concept-based (human-defined tasks)
- Network decomposition methods flawed
- Circuit faithfulness low
- Measures depend on intervention implementation

---

## 7. Future Directions

### Intrinsic Interpretability

- Train models to be decomposable from start
- Sparse activation functions (TopK, SoLU)
- Mixture of experts (interpretable if sparse enough)
- Modular architectures

### Improved Validation

- Better benchmarks for interpretability methods
- Ground truth testing with toy models
- Cross-validation with model organisms

### Automation

- Automated circuit discovery (ACDC)
- LLM-based feature description
- Statistical hypothesis testing for circuits

---

## 8. Conclusion

Mechanistic interpretability offers pathways to:
- Better AI control and monitoring
- Scientific understanding of artificial minds
- Knowledge extraction from AI systems

**Key challenges:**
- Conceptual foundations unclear
- Methods have practical limitations
- Validation difficult
- Socio-technical considerations under-explored

The field requires both scientific and engineering progress, along with attention to societal implications.
