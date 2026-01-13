# Phase 2 Lazy Code Pattern Audit

**Date:** 2026-01-12  
**Status:** ⏳ IN PROGRESS  
**Total Found:** ~126 instances

## Summary

| Category | Count | Files |
|----------|-------|-------|
| `|| 0` in expression services | 53 | `services/expressions/*.ts` |
| `: any\|as any` in expression services | 24 | `services/expressions/*.ts` |
| `: any\|as any\|Keyframe<any>` in consumer files | 42 | Phase 2 consumer components/composables |
| `Keyframe<any>` in keyframeStore | 7 | `stores/keyframeStore/*.ts` |
| **TOTAL** | **~126** | |

## Breakdown by File

### Expression Services (77 instances)

#### `services/expressions/vectorMath.ts` (20 instances)
- 20x `|| 0` patterns

#### `services/expressions/sesEvaluator.ts` (8 instances)
- 5x `|| 0` patterns
- 3x `: any|as any` patterns

#### `services/expressions/layerContentExpressions.ts` (10 instances)
- 2x `|| []` patterns
- 2x `|| 0` patterns
- 6x `: any` patterns

#### `services/expressions/coordinateConversion.ts` (30 instances)
- 30x `|| 0` patterns

#### `services/expressions/textAnimator.ts` (4 instances)
- 4x `|| 0` patterns

#### `services/expressions/motionExpressions.ts` (1 instance)
- 1x `|| 0` pattern

#### `services/expressions/types.ts` (2 instances)
- 2x `: any` patterns

#### `services/expressions/expressionEvaluator.ts` (2 instances)
- 2x `as any` patterns

#### `services/expressions/expressionHelpers.ts` (4 instances)
- 4x `: any` patterns

### Phase 2 Consumer Files (42 instances)

#### `components/panels/AudioPanel.vue` (2 instances)
- 2x `as any`

#### `components/panels/PropertiesPanel.vue` (3 instances)
- 1x `: any` (target parameter)
- 2x `as any` (audioPathAnimation)

#### `components/curve-editor/CurveEditor.vue` (8 instances)
- 5x `Keyframe<any>`
- 1x `: any` (getNumericValue parameter)

#### `components/timeline/PropertyTrack.vue` (11 instances)
- 2x `Keyframe<any>`
- 9x `: any` (keyframe callbacks)

#### `composables/useKeyboardShortcuts.ts` (11 instances)
- 1x `: any` (assetStore)
- 10x `as unknown as` (layer.data casts)

#### `composables/useCurveEditorInteraction.ts` (7 instances)
- 2x `Keyframe<any>`
- 2x `: any` (store, keyframeStore)
- 1x `: any` (getNumericValue parameter)

### KeyframeStore (7 instances)

#### `stores/keyframeStore/index.ts` (2 instances)
- 1x `Keyframe<any>` (getKeyframesAtFrame return type)
- 1x `: any` → Fixed to `PropertyValue` ✅

#### `stores/keyframeStore/expressions.ts` (1 instance)
- 1x `Keyframe<any>`

#### `stores/keyframeStore/property.ts` (1 instance)
- 1x `Keyframe<any>`

#### `stores/keyframeStore/query.ts` (2 instances)
- 2x `Keyframe<any>`

#### `stores/keyframeStore/autoBezier.ts` (2 instances)
- 2x `Keyframe<any>`

## Fix Strategy

### Priority 1: Type Safety (Keyframe<any>)
1. Replace `Keyframe<any>` with `Keyframe<PropertyValue>` where possible
2. Use generic constraints for type-safe keyframe operations

### Priority 2: Expression Services (|| 0)
1. Replace `|| 0` with proper null checks and default values
2. Use type guards and validation functions
3. Consider using `Number.isFinite()` checks

### Priority 3: Consumer Files (as any, : any)
1. Replace `as any` with proper type assertions
2. Replace `: any` parameters with specific types
3. Use proper type guards and validation

## Progress

- ✅ Fixed 7 `Keyframe<any>` in keyframeStore → `Keyframe<PropertyValue>`
- ✅ Fixed 2 `as any` in `AudioPanel.vue` → Proper types (`SplineData`, `AnimatableProperty<Vec3>`)
- ✅ Fixed 3 `as any` in `PropertiesPanel.vue` → Proper types (`AudioPathAnimation`, property link target)
- ⏳ Remaining: ~114 instances (37 consumer files + 53 `|| 0` + 24 expression services)

## Next Steps

1. Fix all `Keyframe<any>` → `Keyframe<PropertyValue>` (7 instances)
2. Fix expression service `|| 0` patterns (53 instances)
3. Fix expression service `: any|as any` (24 instances)
4. Fix consumer file lazy patterns (42 instances)
