/**
 * Store Actions Index
 *
 * Action modules that extend compositorStore functionality.
 * These modules are being progressively migrated to domain-specific Pinia stores.
 *
 * Completed Migrations:
 * - audioActions → audioKeyframeStore.ts
 * - cacheActions → cacheStore.ts
 * - cameraActions → cameraStore.ts
 * - depthflowActions → depthflowStore.ts
 * - markerActions → markerStore.ts
 * - particleLayerActions → particleStore.ts
 * - physicsActions → physicsStore.ts
 * - playbackActions → playbackStore.ts (already existed)
 * - propertyDriverActions → expressionStore/drivers.ts (already existed)
 * - segmentationActions → segmentationStore.ts
 *
 * Remaining (to be migrated):
 * - compositionActions/ → compositionStore.ts
 * - effectActions.ts → effectStore/
 * - layerDecompositionActions.ts → (new store)
 * - layerStyleActions/ → (new store)
 * - projectActions/ → projectStore.ts
 * - textAnimatorActions/ → textAnimatorStore.ts
 * - videoActions/ → videoStore.ts
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

// Composition actions - MIGRATED to compositionStore.ts

// Effect actions - MIGRATED to effectStore/index.ts

// Layer decomposition - MIGRATED to decompositionStore.ts

// Layer style actions - MIGRATED to effectStore/index.ts

// Project actions - MIGRATED to projectStore.ts

// Text Animator actions - MIGRATED to textAnimatorStore.ts

// Video actions - MIGRATED to videoStore.ts
