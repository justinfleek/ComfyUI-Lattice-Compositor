# Trade Dress Legal Audit Report

**Document ID**: TRADE_DRESS_AUDIT
**Version**: 2.0.0
**Last Updated**: December 20, 2024
**Status**: COMPLETE
**Purpose**: Document and track terminology changes for legal defensibility

---

## Executive Summary

This document tracks terminology used in the Weyl Compositor that may infringe on Adobe After Effects trade dress, copyrights, or patents. All identified high-risk terms have been catalogued, assessed, and mitigated.

**Total Terms Audited**: 15
**Critical Risk (Mitigated)**: 4
**High Risk (Mitigated)**: 2
**Medium Risk (Mitigated)**: 2
**All Trade Dress Violations**: RESOLVED

---

## Terminology Rename Map

### Completed Renames (All Done)

| Original Term | New Term | Status | Files Updated |
|---------------|----------|--------|---------------|
| AdjustmentLayer | EffectLayer | COMPLETE | EffectLayer.ts, types |
| loopOut() | repeatAfter() | COMPLETE | expressions.ts |
| loopIn() | repeatBefore() | COMPLETE | expressions.ts |
| Solo | Isolate | COMPLETE | LayerManager.ts, UI |
| Null (layer) | Control | COMPLETE | types (deprecated) |
| Pickwhip | PropertyLink | COMPLETE | PropertyLink.vue, PropertiesPanel.vue, CSS |
| Graph Editor | CurveEditor | COMPLETE | curve-editor/, CurveEditor.vue, WorkspaceLayout.vue |
| anchorPoint | origin | COMPLETE | project.ts, BaseLayer.ts, MotionEngine.ts, compositorStore.ts, etc. |
| inPoint/outPoint | startFrame/endFrame | COMPLETE | project.ts, MotionEngine.ts, all layer files, etc. |
| Time Remap | SpeedMap | COMPLETE | VideoProperties.vue, NestedCompProperties.vue, VideoLayer.ts, NestedCompLayer.ts, AI tools, types |
| Work Area | RenderRange | COMPLETE | PreviewPanel.vue |

### Deprecated Files Deleted

| File | Reason | Status |
|------|--------|--------|
| `components/controls/Pickwhip.vue` | Replaced by PropertyLink.vue | DELETED |
| `components/graph-editor/GraphEditor.vue` | Replaced by curve-editor/CurveEditor.vue | DELETED |
| `components/timeline/GraphEditorCanvas.vue` | Replaced by curve-editor/CurveEditorCanvas.vue | DELETED |

### Terms Kept (Industry Standard)

| Term | Reason Kept |
|------|-------------|
| Keyframe | Industry standard (predates AE) |
| Timeline | Industry standard |
| Layer | Industry standard |
| Composition | Generic term |
| Blend Mode | Generic term |
| Effect | Generic term |
| Expression | Generic programming term |

---

## Implementation Checklist

### Phase 1: High-Risk UI Terms (COMPLETE)
- [x] Rename Pickwhip → PropertyLink
- [x] Rename Graph Editor → CurveEditor
- [x] Update all CSS classes
- [x] Update all imports
- [x] Delete deprecated files (Pickwhip.vue, GraphEditor.vue, GraphEditorCanvas.vue)

### Phase 2: Core Property Terms (COMPLETE)
- [x] Add aliases for backwards compatibility
- [x] Rename anchorPoint → origin (with alias)
- [x] Rename inPoint/outPoint → startFrame/endFrame (with alias)
- [x] Update all type definitions
- [x] Update factory functions

### Phase 3: Feature Terms (COMPLETE)
- [x] Rename Time Remap → SpeedMap (with backwards compat)
- [x] Rename Work Area → RenderRange
- [x] Complete Precomp → NestedComp migration
- [x] Backwards compatibility for all deprecated terms

### Phase 4: Documentation (COMPLETE)
- [x] Update TRADE_DRESS_AUDIT.md
- [x] AI system prompts updated (systemPrompt.ts)
- [x] Tool definitions updated (actionExecutor.ts)

---

## Backwards Compatibility Strategy

All breaking property changes use TypeScript type aliases with runtime fallbacks:

```typescript
// types/project.ts - Layer timing
interface Layer {
  startFrame: number;  // New name
  endFrame: number;    // New name
  /** @deprecated Use 'startFrame' instead */
  inPoint?: number;    // Alias for migration
  /** @deprecated Use 'endFrame' instead */
  outPoint?: number;   // Alias for migration
}

// types/project.ts - Video/NestedComp data
interface VideoData {
  speedMapEnabled: boolean;  // New name
  speedMap?: AnimatableProperty<number>;
  /** @deprecated Use 'speedMapEnabled' instead */
  timeRemapEnabled?: boolean;
  /** @deprecated Use 'speedMap' instead */
  timeRemap?: AnimatableProperty<number>;
}
```

Runtime handling pattern used throughout:
```typescript
// Check new property first, fall back to legacy
const speedMapEnabled = data.speedMapEnabled ?? data.timeRemapEnabled ?? false;
const speedMapProp = data.speedMap ?? data.timeRemap;
```

---

## Legal Disclaimer

This audit is for internal reference only and does not constitute legal advice. Consult with intellectual property counsel before public release.

**Terms of art in motion graphics industry** (keyframe, timeline, layer, etc.) are generally considered generic and not protected. Adobe-specific **UI patterns and feature names** (Pickwhip, Graph Editor, Time Remap, Work Area) have been renamed to generic alternatives.

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2024-12-20 | Initial audit |
| 2.0.0 | 2024-12-20 | All trade dress violations resolved |

---

## References

- Adobe After Effects Feature List
- Industry Standard Motion Graphics Terminology
- Open Source Alternatives (Blender, Natron, OpenFX)
