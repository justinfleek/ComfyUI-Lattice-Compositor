# Cross-Domain Actions Inventory

> **Purpose:** Catalog every action that spans multiple domains and define coordination patterns
> **Generated:** 2026-01-10
> **Critical Actions:** 19
> **Pattern Required:** Store-to-store coordination without circular dependencies

---

## Why This Matters

Cross-domain actions are why the December 2025 refactor stalled. Example:

```typescript
// compositorStore.ts - convertAudioToKeyframes
// This single action needs:
// 1. Audio analysis data (audioStore)
// 2. Layer to add keyframes to (layerStore)
// 3. Keyframe creation (keyframeStore)
// 4. History snapshot (historyStore)
```

If we extract stores naively, we get circular imports:
- audioStore imports keyframeStore
- keyframeStore imports layerStore
- layerStore imports historyStore
- historyStore imports... everything?

**Solution:** Define clear ownership and call patterns.

---

## Cross-Domain Action Categories

### Category A: Action Needs Data From Other Store (READ)
Pattern: Call getter, don't import state

### Category B: Action Mutates Other Store (WRITE)
Pattern: Call other store's action method

### Category C: Action Needs Atomic Multi-Store Update
Pattern: Orchestration in calling component or dedicated service

---

## 1. Audio → Keyframe Actions

### convertAudioToKeyframes

**Current Location:** compositorStore via audioActions.ts

**Domains Touched:**
- Audio (READ): Get audio analysis, peak data
- Layer (READ): Get target layer
- Keyframe (WRITE): Create keyframes
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// audioStore.ts
convertAudioToKeyframes(
  layerId: string,
  propertyPath: string,
  options: AudioToKeyframeOptions
): void {
  // Read from self
  const analysis = this.audioAnalysis;
  const peaks = this.peakData;

  // Read from other store (allowed)
  const layer = useLayerStore().getLayerById(layerId);
  if (!layer) return;

  // Write to keyframeStore (via its public API)
  const keyframeStore = useKeyframeStore();
  peaks.forEach(peak => {
    keyframeStore.addKeyframe(layerId, propertyPath, peak.amplitude, peak.frame);
  });

  // Explicit history push
  useHistoryStore().pushState('Convert audio to keyframes');
}
```

**Owner:** audioStore
**Callers Update:** Components call `useAudioStore().convertAudioToKeyframes()`

---

### createAudioPropertyDriver

**Current Location:** compositorStore via audioActions.ts

**Domains Touched:**
- Audio (READ): Audio reactive mapper
- Expression (WRITE): Create driver
- Layer (READ): Get target layer

**Migration Strategy:**
```typescript
// audioStore.ts
createAudioPropertyDriver(layerId: string, propertyPath: string, mapping: AudioMapping): void {
  // Read self
  const mapper = this.audioReactiveMapper;

  // Write to expressionStore
  useExpressionStore().createDriver(layerId, propertyPath, {
    type: 'audio-reactive',
    source: mapping
  });
}
```

**Owner:** audioStore
**Callers Update:** Components call `useAudioStore().createAudioPropertyDriver()`

---

### getAudioReactiveValuesForLayer

**Current Location:** compositorStore via audioActions.ts

**Domains Touched:**
- Audio (READ): Audio reactive mappings
- Layer (READ): Layer properties

**Migration Strategy:**
```typescript
// audioStore.ts - This is just a read, no cross-store write
getAudioReactiveValuesForLayer(layerId: string, frame: number): AudioReactiveValues {
  const mappings = this.getActiveMappingsForLayer(layerId);
  return mappings.map(m => this.getMappedValueAtFrame(m, frame));
}
```

**Owner:** audioStore (no change needed, pure read)

---

## 2. Expression → Keyframe Actions

### convertExpressionToKeyframes

**Current Location:** compositorStore

**Domains Touched:**
- Expression (READ): Get expression
- Layer (READ): Get target layer
- Keyframe (WRITE): Create keyframes
- Animation (READ): Frame range
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// expressionStore.ts
convertExpressionToKeyframes(
  layerId: string,
  propertyPath: string,
  startFrame: number,
  endFrame: number
): void {
  const expression = this.getPropertyExpression(layerId, propertyPath);
  if (!expression) return;

  // Read animation state
  const animStore = useAnimationStore();
  const start = startFrame ?? 0;
  const end = endFrame ?? animStore.frameCount;

  // Evaluate expression at each frame and create keyframes
  const keyframeStore = useKeyframeStore();
  for (let frame = start; frame <= end; frame++) {
    const value = this.evaluateExpression(expression, frame);
    keyframeStore.addKeyframe(layerId, propertyPath, value, frame);
  }

  // Remove expression after baking
  this.disablePropertyExpression(layerId, propertyPath);

  useHistoryStore().pushState('Bake expression to keyframes');
}
```

**Owner:** expressionStore

---

## 3. Layer → Selection Actions

### nestSelectedLayers

**Current Location:** compositorStore via layerActions.ts

**Domains Touched:**
- Selection (READ): Get selected layer IDs
- Layer (WRITE): Create group, reparent layers
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// layerStore.ts
nestSelectedLayers(): void {
  // Read from selection
  const selectedIds = useSelectionStore().selectedLayerIds;
  if (selectedIds.length < 2) return;

  // Create group and reparent (own domain)
  const groupId = this.createLayer({ type: 'control', name: 'Group' });
  selectedIds.forEach(id => this.setLayerParent(id, groupId));

  useHistoryStore().pushState('Nest layers');
}
```

**Owner:** layerStore

---

### reverseSelectedLayers

**Domains Touched:**
- Selection (READ): Get selected layer IDs
- Layer (WRITE): Reverse layer order
- History (WRITE): Push state

**Migration Strategy:** Same pattern as nestSelectedLayers

**Owner:** layerStore

---

### duplicateSelectedLayers

**Domains Touched:**
- Selection (READ): Get selected layer IDs
- Layer (WRITE): Duplicate layers
- Selection (WRITE): Select new layers

**Migration Strategy:**
```typescript
// layerStore.ts
duplicateSelectedLayers(): string[] {
  const selectedIds = useSelectionStore().selectedLayerIds;
  const newIds = selectedIds.map(id => this.duplicateLayer(id));

  // Update selection to new layers
  useSelectionStore().selectLayers(newIds);

  useHistoryStore().pushState('Duplicate layers');
  return newIds;
}
```

**Owner:** layerStore (writes to selectionStore as side effect)

---

### deleteSelectedLayers

**Domains Touched:**
- Selection (READ + WRITE): Get selected, then clear selection
- Layer (WRITE): Delete layers
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// layerStore.ts
deleteSelectedLayers(): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;

  selectedIds.forEach(id => this.deleteLayer(id));
  selectionStore.clearSelection();

  useHistoryStore().pushState('Delete layers');
}
```

**Owner:** layerStore

---

### copySelectedLayers / cutSelectedLayers / pasteLayers

**Domains Touched:**
- Selection (READ): Get selected layer IDs
- Layer (READ/WRITE): Serialize/deserialize layers
- UI/Clipboard (WRITE): Store serialized data

**Migration Strategy:**
```typescript
// layerStore.ts
copySelectedLayers(): void {
  const selectedIds = useSelectionStore().selectedLayerIds;
  const serialized = selectedIds.map(id => this.serializeLayer(id));
  useUIStore().setClipboard({ type: 'layers', data: serialized });
}

pasteLayers(): string[] {
  const clipboard = useUIStore().clipboard;
  if (clipboard?.type !== 'layers') return [];

  const newIds = clipboard.data.map(data => this.deserializeLayer(data));
  useSelectionStore().selectLayers(newIds);
  useHistoryStore().pushState('Paste layers');
  return newIds;
}
```

**Owner:** layerStore (clipboard in uiStore)

---

## 4. Layer → Animation Actions

### splitLayerAtPlayhead

**Domains Touched:**
- Animation (READ): Current frame
- Layer (WRITE): Split layer
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// layerStore.ts
splitLayerAtPlayhead(layerId: string): [string, string] {
  const frame = useAnimationStore().currentFrame;
  const [leftId, rightId] = this.splitLayerAt(layerId, frame);

  useHistoryStore().pushState('Split layer');
  return [leftId, rightId];
}
```

**Owner:** layerStore

---

### freezeFrameAtPlayhead

**Domains Touched:**
- Animation (READ): Current frame
- Layer (WRITE): Set time remap
- History (WRITE): Push state

**Migration Strategy:** Same pattern

**Owner:** layerStore

---

### timeStretchLayer

**Domains Touched:**
- Animation (READ): Duration context
- Layer (WRITE): Adjust timing
- History (WRITE): Push state

**Migration Strategy:** Same pattern

**Owner:** layerStore

---

## 5. Keyframe → Selection Actions

### copyKeyframes / pasteKeyframes

**Domains Touched:**
- Selection (READ): Selected keyframe IDs
- Keyframe (READ/WRITE): Serialize/paste keyframes
- UI/Clipboard (WRITE): Store serialized data

**Migration Strategy:**
```typescript
// keyframeStore.ts
copyKeyframes(): void {
  const selectedIds = this.selectedKeyframeIds;
  const serialized = selectedIds.map(id => this.serializeKeyframe(id));
  useUIStore().setClipboard({ type: 'keyframes', data: serialized });
}

pasteKeyframes(targetFrame?: number): void {
  const clipboard = useUIStore().clipboard;
  if (clipboard?.type !== 'keyframes') return [];

  const frame = targetFrame ?? useAnimationStore().currentFrame;
  clipboard.data.forEach(kf => this.addKeyframe(kf.layerId, kf.propertyPath, kf.value, frame));

  useHistoryStore().pushState('Paste keyframes');
}
```

**Owner:** keyframeStore

---

### timeReverseKeyframes

**Domains Touched:**
- Selection (READ): Selected keyframe IDs
- Keyframe (WRITE): Reverse timing
- History (WRITE): Push state

**Migration Strategy:**
```typescript
// keyframeStore.ts
timeReverseKeyframes(): void {
  const selectedIds = this.selectedKeyframeIds;
  // ... reverse logic
  useHistoryStore().pushState('Reverse keyframes');
}
```

**Owner:** keyframeStore

---

## 6. Animation → Keyframe Actions

### jumpToNextKeyframe / jumpToPrevKeyframe

**Domains Touched:**
- Keyframe (READ): Get keyframe positions
- Animation (WRITE): Set current frame

**Migration Strategy:**
```typescript
// animationStore.ts
jumpToNextKeyframe(): void {
  const allFrames = useKeyframeStore().getAllKeyframeFrames();
  const nextFrame = allFrames.find(f => f > this.currentFrame);
  if (nextFrame !== undefined) {
    this.setFrame(nextFrame);
  }
}
```

**Owner:** animationStore (reads from keyframeStore)

---

## 7. Property Evaluation (Complex Cross-Domain)

### evaluatePropertyAtFrame

**Domains Touched:**
- Layer (READ): Get layer, property definition
- Keyframe (READ): Get keyframe values, interpolate
- Expression (READ): Evaluate expression if exists
- Audio (READ): Get audio-reactive value if mapped

**Migration Strategy:** This is complex. Options:

**Option A: Dedicated Evaluation Service**
```typescript
// services/propertyEvaluator.ts
export function evaluatePropertyAtFrame(
  layerId: string,
  propertyPath: string,
  frame: number
): number {
  // Check expression first
  const expressionStore = useExpressionStore();
  if (expressionStore.hasPropertyExpression(layerId, propertyPath)) {
    return expressionStore.evaluateExpression(layerId, propertyPath, frame);
  }

  // Check audio mapping
  const audioStore = useAudioStore();
  const audioValue = audioStore.getMappedValueAtFrame(layerId, propertyPath, frame);
  if (audioValue !== undefined) {
    return audioValue;
  }

  // Fall back to keyframe interpolation
  return useKeyframeStore().interpolateValue(layerId, propertyPath, frame);
}
```

**Option B: Each Store Evaluates Its Domain**
```typescript
// layerStore.ts
getPropertyValue(layerId: string, propertyPath: string, frame: number): number {
  // Layer checks its own static value
  // If animated, delegates to keyframeStore
  // If expression, delegates to expressionStore
}
```

**Recommended:** Option A - Single service, clear ownership

---

## 8. Orchestration Actions (Component-Level)

Some actions are better orchestrated at the component level rather than in stores:

### Example: "Add Keyframe with Audio-Reactive Default"

```vue
<script setup lang="ts">
// Component orchestrates multiple stores
const addAudioReactiveKeyframe = () => {
  const layer = useSelectionStore().selectedLayer;
  const frame = useAnimationStore().currentFrame;
  const audioValue = useAudioStore().getAmplitudeAtFrame(frame);

  useKeyframeStore().addKeyframe(layer.id, 'opacity', audioValue, frame);
  useHistoryStore().pushState('Add audio-reactive keyframe');
};
</script>
```

This keeps stores focused on their domain while components handle orchestration.

---

## Cross-Domain Coordination Rules

### Rule 1: Stores Can Read Freely
Any store can call getters on other stores.
```typescript
// OK: keyframeStore reads from layerStore
const layer = useLayerStore().getLayerById(layerId);
```

### Rule 2: Stores Write to Own Domain
A store should only mutate its own state.
```typescript
// OK: keyframeStore mutates keyframes
this.keyframes[layerId][propertyPath].push(newKeyframe);

// NOT OK: keyframeStore mutates layers
layer.animated = true;  // Don't do this!
```

### Rule 3: Cross-Domain Writes Use Public API
When a store needs to trigger changes in another domain, call that store's action.
```typescript
// OK: audioStore triggers keyframe creation via API
useKeyframeStore().addKeyframe(layerId, propertyPath, value, frame);

// NOT OK: audioStore directly mutates keyframe state
useKeyframeStore().$patch({ keyframes: ... });  // Don't do this!
```

### Rule 4: History is Explicit
The store that initiates the user action pushes to history.
```typescript
// The "outer" action that the user triggered pushes history
deleteSelectedLayers(): void {
  // ... deletion logic
  useHistoryStore().pushState('Delete layers');
}
```

### Rule 5: No Circular Action Chains
If Store A calls Store B which calls Store A, you have a design problem.
```typescript
// BAD: Circular
// layerStore.deleteLayer() -> selectionStore.removeFromSelection() -> layerStore.onLayerRemoved()

// GOOD: Unidirectional
// layerStore.deleteLayer() -> clears own state -> done
// Component subscribes to layer changes, updates selection if needed
```

---

## Import Dependency Graph (Target)

```
                    historyStore
                         ↑
                         │ (pushState)
    ┌────────────────────┼────────────────────┐
    │                    │                    │
    │                    │                    │
layerStore ←──── keyframeStore ←──── audioStore
    ↑                    ↑                    ↑
    │                    │                    │
    └────────────────────┴────────────────────┘
                         │
                  expressionStore
                         │
                         ↓
              animationStore (currentFrame)
                         │
                         ↓
                selectionStore (read-only from others)
                         │
                         ↓
                    uiStore (clipboard, tools)
```

**Direction:** Arrows show "can call into"
- All stores can read from any other store
- Writes flow upward toward historyStore
- No cycles

---

## Verification Checklist

Before migrating each cross-domain action:

- [ ] Identify all domains touched (READ vs WRITE)
- [ ] Determine owner store
- [ ] Document the coordination pattern
- [ ] Verify no circular dependencies introduced
- [ ] Update all caller sites
- [ ] Test the action works end-to-end

---

*Document Version: 1.0*
*Generated: 2026-01-10*
