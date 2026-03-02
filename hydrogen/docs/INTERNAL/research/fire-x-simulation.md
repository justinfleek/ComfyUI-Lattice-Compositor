# Fire-X: Extinguishing Fire with Stoichiometric Heat Release

**Authors:** Helge Wrede, Anton R. Wagner, Sarker Miraz Mahfuz, Wojtek Pałubicki, Dominik L. Michels, Sören Pirk (Kiel University, Adam Mickiewicz University, KAUST)  
**Publication:** ACM Transactions on Graphics (SIGGRAPH Asia 2025)  
**Date:** December 2025  
**Domain:** Computer Graphics / Physical Simulation / Fluid Dynamics

---

## Abstract

Presents a **novel combustion simulation framework** for fire across solids, liquids, and gases with:

- Multi-species thermodynamics (fuel, oxygen, nitrogen, CO2, water vapor, residuals)
- Reactive transport
- Stoichiometry-dependent heat release
- Support for premixed and diffusive flames
- Extinguishing scenarios (water suppression, evaporation, starvation)

---

## 1. Problem: Fire Simulation Gaps

### 1.1 Previous Approaches

| Approach | Limitation |
|----------|------------|
| Visual flames only | No combustion chemistry |
| Gaseous flames only | Ignores phase transitions |
| Physics-based | Not interactive |
| Game fires | Simplified, not physically accurate |

### 1.2 Fire-X Goals

- Real-time/interactive fire simulation
- Multi-phase (solid, liquid, gas)
- Accurate combustion chemistry
- Extinguishing behaviors

---

## 2. Methodology

### 2.1 Multi-Species Thermodynamics

```
Species: {Fuel, O2, N2, CO2, H2O, Residuals}
```

Each species has:
- Mass fraction
- Temperature
- Velocity field

### 2.2 Stoichiometric Heat Release

```
Reaction: Fuel + ν_O2 O2 → Products + Heat

Heat release = stoichiometric_coefficient * heat_of_combustion
```

### 2.3 Hybrid SPH-Grid Representation

- **SPH (Smoothed Particle Hydrodynamics):** For free surfaces, splashing
- **Grid:** For pressure projection, diffusion

### 2.4 Extinguishing Mechanisms

| Mechanism | Implementation |
|-----------|---------------|
| **Water spray** | Particle-based, evaporative cooling |
| **Starvation** | Fuel depletion modeling |
| **Evaporation** | Phase transition model |
| **Cooling** | Heat transfer to water |

### 2.5 Rendering

- Laminar-to-turbulent transitions
- Blue-to-orange color shift (temperature-based)
- Smoke and vapor

---

## 3. Validation

### 3.1 Experiments

- Jet fires
- Water suppression (sprays, sprinklers)
- Fuel evaporation
- Starvation conditions

### 3.2 Scenarios

- Indoor fires
- Outdoor fires
- Vehicle fires
- Multi-species interactions

---

## 4. Relation to Hydrogen

### 4.1 Physical Simulation

For **billion-agent swarms** in physical environments:

| Need | Fire-X Solution |
|------|-----------------|
| **Real-time physics** | Interactive simulation |
| **Multi-phase fluids** | SPH-grid hybrid |
| **Chemical reactions** | Stoichiometric model |
| **Extinguishing** | Accurate suppression physics |

### 4.2 Game Engine Integration

Could integrate with:
- Interactive 3D worlds (WorldGen)
- Agent behavior in fire scenarios
- Emergency response simulations
- Training simulations

### 4.3 Rendering Pipeline

Complementary to:
- Gaussian splatting (3DGS)
- Path tracing (SDF grids)
- Material segmentation

---

## 5. References

1. SPH (Smoothed Particle Hydrodynamics)
2. Navier-Stokes fluid simulation
3. Combustion chemistry
4. ACM SIGGRAPH

---

## 6. Citation

```bibtex
@article{wrede2025firex,
  title={Fire-X: Extinguishing Fire with Stoichiometric Heat Release},
  author={Helge Wrede and Anton R. Wagner and Sarker Miraz Mahfuz and Wojtek Pałubicki and Dominik L. Michels and Sören Pirk},
  journal={ACM Transactions on Graphics},
  year={2025}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
