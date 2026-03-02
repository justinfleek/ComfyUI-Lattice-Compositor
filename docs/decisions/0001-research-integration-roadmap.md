# ADR 0001: Research Integration Roadmap

## Status

**Proposed** - March 2026

## Context

Lattice needs real-time AI preview capabilities and formal type guarantees.

We have identified 190+ research papers and several implementation repositories.

## Decision

Implement a phased integration roadmap:

| Phase | Focus | Priority |
|-------|-------|----------|
| 1 | Real-time diffusion preview (LCM-LoRA, MonarchRT) | P0 |
| 2 | Type-safe animation engine (graded monads) | P1 |
| 3 | SAM 3 segmentation upgrade | P0 |
| 4 | Voice-driven animation | P2 |
| 5 | 3D Gaussian Splatting layers | P2 |
| 6 | World model preview | P1 |
| 7 | Billion-agent particles | P3 |
| 8 | Haskell-to-WGSL compilation | P3 |

## Staging Area

Research implementations are staged in `newfeatures/`:

- `MonarchRT/` - Monarch matrices for 16 FPS video DiT
- `ACE-Step/` - Music generation with LM+DiT hybrid
- `YUME/` - Interactive world generation
- `SAM3/` - Open-vocabulary segmentation (270K concepts)
- `RESEARCH_PAPERS.md` - Full 190+ paper survey

## References

- [newfeatures/README.md](../../newfeatures/README.md)
- [newfeatures/RESEARCH_PAPERS.md](../../newfeatures/RESEARCH_PAPERS.md)
