# Position: Interactive Generative Video as Next-Generation Game Engine

**arXiv:** 2503.17359  
**Authors:** Jiwen Yu, Yiran Qin, Haoxuan Che, Quande Liu, Xintao Wang, Pengfei Wan, Di Zhang, Xihui Liu (HKU, HKUST, Kuaishou)  
**Status:** IN_PROGRESS

---

## 1. Abstract

Position paper arguing that Interactive Generative Video (IGV) is the foundation for Generative Game Engines (GGE). Key arguments:
- Video generation models can create unlimited novel content
- Physics-aware world modeling
- User-controlled interactivity
- Causal reasoning

**Hierarchy Roadmap:** L0-L4 maturity levels for GGE development.

---

## 2. Why IGV for GGE?

### 2.1 Traditional Game Engine Problems

- Predetermined content (players exhaust)
- No personalization
- High development costs

### 2.2 IGV Solutions

| Advantage | Description |
|-----------|-------------|
| Generalizable generation | Transfer to unprecedented scenarios |
| Compositional creativity | Combine elements innovatively |
| Physics-aware | Understands physical laws |
| User control | Interactive gameplay |

---

## 3. Core IGV Capabilities

### 3.1 Four Key Characteristics

1. **User Control** - Actions affect generated content
2. **Memory** - Video context retention
3. **Physics** - World rule understanding
4. **Causal Reasoning** - Action-consequence understanding

### 3.2 Architecture

```
┌─────────────────────────────────────────┐
│         Interactive Generative Video     │
├─────────────────────────────────────────┤
│                                          │
│  ┌──────────┐    ┌──────────────────┐  │
│  │  User    │───▶│  Video Diffusion │  │
│  │  Action  │    │     Model         │  │
│  └──────────┘    └─────────┬─────────┘  │
│                            │              │
│         ┌─────────────────┘              │
│         ▼                                  │
│  ┌─────────────────────────────────────┐  │
│  │         World State                 │  │
│  │  - Memory                          │  │
│  │  - Physics Rules                   │  │
│  │  - Causal Model                   │  │
│  └─────────────────────────────────────┘  │
└─────────────────────────────────────────┘
```

---

## 4. Maturity Roadmap (L0-L4)

| Level | Description | Capability |
|-------|-------------|------------|
| L0 | Single prompt | Static generation |
| L1 | Multiple prompts | Sequential generation |
| L2 | Basic control | Action-conditioned |
| L3 | World model | Physics + memory |
| L4 | Full GGE | Reasoning + planning |

---

## 5. Related Work

| Project | Domain | Approach |
|---------|--------|----------|
| GameNGen | DOOM | Diffusion |
| DIAMOND | Atari | Diffusion |
| GAIA-2 | Driving | World model |
| GameFactory | Minecraft | Action control |

---

## 6. Key Definitions

1. **IGV:** Interactive Generative Video - video generation with interactive features
2. **GGE:** Generative Game Engine - game engine using generative AI
3. **Physics-aware:** Understanding physical laws in generation
4. **Full-duplex:** Simultaneous two-way interaction

---

## 7. Relation to Hydrogen

```purescript
-- Interactive video generation
data GameState
  = GameState
      { worldModel :: WorldModel
      , memory :: VideoMemory
      , physics :: PhysicsEngine
      , action :: PlayerAction
      }

-- Step game forward
stepGame ::
  GameState ->
  PlayerAction ->
  (VideoFrame, GameState)

-- Generate from action
generateFrame ::
  DiffusionModel ->
  GameState ->
  PlayerAction ->
  VideoFrame
```

---

## 8. Bibliography

1. Yu et al. "Position: Interactive Generative Video as Next-Generation Game Engine" 2025

---

*Document generated: 2026-02-26*
