-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // testing // algorithm // correctness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# ROUND 2: Algorithm Correctness Property Test Specifications

This document specifies property-based tests for all algorithms in Hydrogen.
Each algorithm section includes: correctness invariants, performance bounds,
edge cases, and regression test requirements.

---

## 1. CACHE ALGORITHMS (Composition/Cache.purs)

### 1.1 LRU Eviction Ordering

**Implementation**: `LRUTracker` with Map-based access time tracking

**Correctness Invariants**:

```purescript
-- INV-LRU-1: Oldest entry has minimum access time
prop_lruOldestIsMinimum :: LRUTracker -> Boolean
prop_lruOldestIsMinimum tracker =
  case lruOldest tracker of
    Nothing -> Map.isEmpty tracker.entries
    Just oldestKey -> 
      let oldestTime = Map.lookup oldestKey tracker.entries
          allTimes = Map.values tracker.entries
      in all (\t -> oldestTime <= Just t) allTimes

-- INV-LRU-2: Add increases size by exactly 1 (for new keys)
prop_lruAddIncreasesSize :: String -> LRUTracker -> Boolean
prop_lruAddIncreasesSize key tracker =
  let before = lruSize tracker
      after = lruSize (lruAdd key tracker)
  in if Map.member key tracker.entries
     then after == before  -- Update existing
     else after == before + 1  -- Add new

-- INV-LRU-3: Touch updates access time to current
prop_lruTouchUpdatesTime :: String -> LRUTracker -> Boolean
prop_lruTouchUpdatesTime key tracker =
  case Map.lookup key tracker.entries of
    Nothing -> lruTouch key tracker == tracker  -- No change if not present
    Just _ ->
      let touched = lruTouch key tracker
          newTime = Map.lookup key touched.entries
      in newTime == Just (tracker.currentTime)  -- Gets current time

-- INV-LRU-4: Remove decreases size by exactly 1 (for existing keys)
prop_lruRemoveDecreasesSize :: String -> LRUTracker -> Boolean
prop_lruRemoveDecreasesSize key tracker =
  let before = lruSize tracker
      after = lruSize (lruRemove key tracker)
  in if Map.member key tracker.entries
     then after == before - 1
     else after == before

-- INV-LRU-5: Current time is monotonically increasing
prop_lruTimeMonotonic :: Array String -> Boolean
prop_lruTimeMonotonic keys =
  let ops = foldl lruAdd emptyLRU keys
  in ops.currentTime >= 0.0 && ops.currentTime == toNumber (Array.length keys)
```

**Performance Bounds**:
- `lruAdd`: O(log n) - Map.insert
- `lruTouch`: O(log n) - Map.insert
- `lruRemove`: O(log n) - Map.delete
- `lruOldest`: O(n log n) - sortBy + head (NEEDS OPTIMIZATION for billion-agent)

**Edge Cases**:
- Empty tracker: `lruOldest emptyLRU` returns `Nothing`
- Single entry: oldest is that entry
- Duplicate adds: updates time, doesn't add duplicate
- Remove non-existent key: no-op

**Regression Tests Needed**:
```purescript
spec_lruRegressions :: Spec Unit
spec_lruRegressions = describe "LRU Regressions" do
  it "handles rapid add/remove cycles" do
    -- Add 1000 keys, remove 500, add 500 more
    -- Verify size correctness
    
  it "oldest after many touches is still oldest" do
    -- Add A, B, C
    -- Touch A, B, C in various orders
    -- Verify oldest is updated correctly
    
  it "handles empty string keys" do
    -- Edge case: key = ""
```

---

### 1.2 TTL Expiration Correctness

**Implementation**: `expiresAt :: Maybe Number` in `EntryMetadata`

**Correctness Invariants**:

```purescript
-- INV-TTL-1: Expired entries are not returned
prop_expiredNotReturned :: String -> Number -> CacheEntry a -> Boolean
prop_expiredNotReturned key now entry =
  case entry.metadata.expiresAt of
    Nothing -> true  -- No TTL means never expires
    Just exp -> 
      if now >= exp
      then cacheGet key now cache produces Nothing
      else cacheGet key now cache produces Just entry.value

-- INV-TTL-2: Entry with no TTL never expires
prop_noTtlNeverExpires :: String -> Number -> a -> Boolean
prop_noTtlNeverExpires key anyTime value =
  let entry = makeEntry value (metadata { expiresAt = Nothing })
  in forall t. cacheGet key t (cachePut key entry cache) produces Just value

-- INV-TTL-3: cachePruneExpired removes only expired entries
prop_pruneOnlyExpired :: Number -> CompositionCache a -> Boolean
prop_pruneOnlyExpired now cache =
  let pruned = cachePruneExpired now cache
      remaining = Map.toUnfoldable pruned.entries
  in all (\(Tuple _ entry) -> not (isExpired entry.metadata now)) remaining

-- INV-TTL-4: Expiration is deterministic (same time = same result)
prop_expirationDeterministic :: String -> Number -> CompositionCache a -> Boolean
prop_expirationDeterministic key now cache =
  cacheGet key now cache == cacheGet key now cache
```

**Performance Bounds**:
- Expiration check: O(1) per entry
- `cachePruneExpired`: O(n) where n = entry count

**Edge Cases**:
- `expiresAt = Just 0.0` with `now = 0.0`: edge of expiration
- `expiresAt = Just (-1.0)`: already expired at creation
- Large TTL values near Number.MAX_VALUE

---

### 1.3 Tag Invalidation Completeness

**Implementation**: `tagIndex :: Map CacheTag (Set String)`

**Correctness Invariants**:

```purescript
-- INV-TAG-1: Invalidating a tag removes ALL entries with that tag
prop_tagInvalidationComplete :: CacheTag -> CompositionCache a -> Boolean
prop_tagInvalidationComplete tag cache =
  let invalidated = cacheInvalidateByTag tag cache
      taggedKeys = fromMaybe Set.empty (Map.lookup tag cache.tagIndex)
  in all (\key -> not (cacheContains key invalidated)) (Set.toUnfoldable taggedKeys)

-- INV-TAG-2: Tag index is consistent with entry metadata
prop_tagIndexConsistent :: CompositionCache a -> Boolean
prop_tagIndexConsistent cache =
  let allEntries = Map.toUnfoldable cache.entries
  in all (\(Tuple key entry) ->
    let entryTags = entry.metadata.tags
    in all (\tag -> 
      case Map.lookup tag cache.tagIndex of
        Nothing -> false  -- Tag should exist in index
        Just keys -> Set.member key keys
    ) (Set.toUnfoldable entryTags)
  ) allEntries

-- INV-TAG-3: Removing entry removes it from all tag indices
prop_removeUpdatesTagIndex :: String -> CompositionCache a -> Boolean
prop_removeUpdatesTagIndex key cache =
  let removed = cacheInvalidate key cache
  in all (\(Tuple tag keys) -> not (Set.member key keys)) 
         (Map.toUnfoldable removed.tagIndex)

-- INV-TAG-4: Tag invalidation is idempotent
prop_tagInvalidationIdempotent :: CacheTag -> CompositionCache a -> Boolean
prop_tagInvalidationIdempotent tag cache =
  let once = cacheInvalidateByTag tag cache
      twice = cacheInvalidateByTag tag once
  in cacheSize once == cacheSize twice
```

**Performance Bounds**:
- `cacheInvalidateByTag`: O(k * log n) where k = entries with tag

**Edge Cases**:
- Tag with no entries: no-op
- Entry with multiple tags: removed from all tag indices
- Circular tag dependencies (if tags can reference each other)

---

### 1.4 Generation Monotonicity

**Implementation**: `Generation` from `Hydrogen.Schema.Identity.Temporal`

**Correctness Invariants**:

```purescript
-- INV-GEN-1: Generations are strictly increasing
prop_generationMonotonic :: Generation -> Boolean
prop_generationMonotonic gen =
  let next = nextGeneration gen
  in unwrapGeneration next > unwrapGeneration gen

-- INV-GEN-2: Initial generation is the minimum
prop_initialIsMinimum :: Generation -> Boolean
prop_initialIsMinimum gen =
  unwrapGeneration initialGeneration <= unwrapGeneration gen

-- INV-GEN-3: Cache miss on generation mismatch
prop_generationMismatchMiss :: Identified a -> CompositionCache b -> Boolean
prop_generationMismatchMiss identified cache =
  let cached = cachePutIdentified identified value metadata cache
      bumpedId = identified { generation = nextGeneration identified.generation }
      result = cacheGetIdentified bumpedId now cached
  in result.result == Nothing  -- Generation changed = cache miss
```

**Performance Bounds**:
- `nextGeneration`: O(1)
- Generation comparison: O(1)

---

## 2. FLATTEN ALGORITHMS

### 2.1 Element.Flatten (Element.Core -> DrawCommand)

**Implementation**: `Hydrogen.Element.Flatten`

**Correctness Invariants**:

```purescript
-- INV-FLAT-1: Empty element produces empty commands
prop_emptyProducesEmpty :: Boolean
prop_emptyProducesEmpty =
  Array.null (flatten Empty).commands

-- INV-FLAT-2: Depth is monotonically increasing through traversal
prop_depthMonotonic :: Element -> Boolean
prop_depthMonotonic element =
  let result = flattenWithState initialState element
      depths = map getDepth result.commands
  in isSorted depths  -- Each element gets depth >= previous

-- INV-FLAT-3: PickId assignment is sequential and unique
prop_pickIdSequential :: Element -> Boolean
prop_pickIdSequential element =
  let result = flattenWithState initialState element
      pickIds = catMaybes (map getPickId result.commands)
  in isSequentialFrom 1 pickIds

-- INV-FLAT-4: State threading preserves consistency
prop_stateThreading :: Element -> Element -> Boolean
prop_stateThreading e1 e2 =
  let r1 = flattenWithState initialState e1
      r2 = flattenWithState r1.state e2
  in r2.state.nextPickId >= r1.state.nextPickId
     && r2.state.depth >= r1.state.depth

-- INV-FLAT-5: Group children are flattened in order
prop_groupChildOrder :: Array Element -> Boolean
prop_groupChildOrder children =
  let group = Group { children }
      result = flatten group
      -- Commands should reflect tree traversal order
  in verifyOrderPreservation children result.commands

-- INV-FLAT-6: Center-to-topleft conversion is correct
prop_centerToTopleft :: PixelPoint2D -> Pixel -> Pixel -> Boolean
prop_centerToTopleft center width height =
  let (Tuple x y) = centerToTopLeft center width height
      Pixel cx = center.x
      Pixel cy = center.y
      Pixel w = width
      Pixel h = height
      Pixel expectedX = cx - (w / 2.0)
      Pixel expectedY = cy - (h / 2.0)
  in x == Device.px expectedX && y == Device.px expectedY

-- INV-FLAT-7: Fill produces RGBA in valid range
prop_fillToRgbaValid :: Fill -> Opacity -> Boolean
prop_fillToRgbaValid fill opacity =
  let rgba = fillToRGBA fill opacity
      rec = RGB.rgbaToRecord rgba
  in rec.r >= 0 && rec.r <= 255
     && rec.g >= 0 && rec.g <= 255
     && rec.b >= 0 && rec.b <= 255
     && rec.a >= 0 && rec.a <= 255
```

**Performance Bounds**:
- Tree traversal: O(n) where n = total element count
- Per-element processing: O(1)
- Total: O(n)

**Edge Cases**:
- Deeply nested groups (>100 levels)
- Empty groups
- Transform with identity matrix
- Text with no glyphs
- Path with single MoveTo command

---

### 2.2 GPU.Flatten (Element -> CommandBuffer)

**Implementation**: `Hydrogen.GPU.Flatten`

**Correctness Invariants**:

```purescript
-- INV-GPU-1: PickMap contains all interactive elements
prop_pickMapComplete :: Element msg -> Boolean
prop_pickMapComplete element =
  let result = flatten element
      interactiveCount = countInteractive element
  in Map.size result.pickMap == interactiveCount

-- INV-GPU-2: Every pickId in commands exists in pickMap
prop_pickMapConsistent :: Element msg -> Boolean
prop_pickMapConsistent element =
  let result = flatten element
      commandPickIds = catMaybes (map getCommandPickId result.commands)
  in all (\pid -> Map.member pid result.pickMap) commandPickIds

-- INV-GPU-3: Font configuration propagates to children
prop_fontConfigPropagates :: Element msg -> Boolean
prop_fontConfigPropagates element =
  -- Parent font-size affects child text rendering
  -- Verify through command parameters

-- INV-GPU-4: Layout box extraction is correct
prop_layoutBoxExtraction :: Array (Attribute msg) -> LayoutBox -> Boolean
prop_layoutBoxExtraction attrs parentBox =
  let extracted = extractBox attrs parentBox
  in verifyBoxInheritance attrs parentBox extracted

-- INV-GPU-5: Hex color parsing roundtrips
prop_hexColorRoundtrip :: Int -> Int -> Int -> Boolean
prop_hexColorRoundtrip r g b =
  let hex = "#" <> toHex r <> toHex g <> toHex b
      parsed = parseColorString hex
  in case parsed of
       Just rgba -> 
         let rec = RGB.rgbaToRecord rgba
         in rec.r == r && rec.g == g && rec.b == b
       Nothing -> false
```

**Performance Bounds**:
- Element traversal: O(n)
- Style extraction: O(k) per element where k = attribute count
- Total: O(n * k)

**Edge Cases**:
- Nested Lazy elements
- Keyed elements with duplicate keys
- Style strings with invalid values
- Mixed CSS units (px, rem, %)

---

### 2.3 Scene3D Flatten (Scene3D -> SceneBuffer)

**Implementation**: `Hydrogen.GPU.Scene3D.Core.flattenScene`

**Correctness Invariants**:

```purescript
-- INV-S3D-1: Buffer length = 1 + 1 + |lights| + |meshes|
prop_bufferLength :: Scene3D msg -> Boolean
prop_bufferLength scene =
  let buffer = flattenScene scene
      expected = 1 + 1 + Array.length scene.lights + Array.length scene.meshes
  in Array.length buffer == expected

-- INV-S3D-2: First command is always SetCamera
prop_firstIsCamera :: Scene3D msg -> Boolean
prop_firstIsCamera scene =
  case Array.head (flattenScene scene) of
    Just (SetCamera _) -> true
    _ -> false

-- INV-S3D-3: Second command is always SetBackground
prop_secondIsBackground :: Scene3D msg -> Boolean
prop_secondIsBackground scene =
  case Array.index (flattenScene scene) 1 of
    Just (SetBackground _) -> true
    _ -> false

-- INV-S3D-4: Lights appear before meshes
prop_lightsBeforeMeshes :: Scene3D msg -> Boolean
prop_lightsBeforeMeshes scene =
  let buffer = flattenScene scene
      lightIndices = findIndices isAddLight buffer
      meshIndices = findIndices isDrawMesh buffer
      maxLight = maximum lightIndices
      minMesh = minimum meshIndices
  in case maxLight, minMesh of
       Just ml, Just mm -> ml < mm
       _, _ -> true  -- No lights or no meshes

-- INV-S3D-5: Deterministic output (same scene = same buffer)
prop_flattenDeterministic :: Scene3D msg -> Boolean
prop_flattenDeterministic scene =
  flattenScene scene == flattenScene scene

-- INV-S3D-6: All scene elements appear in buffer
prop_allElementsPresent :: Scene3D msg -> Boolean
prop_allElementsPresent scene =
  let buffer = flattenScene scene
      lightCount = Array.length (Array.filter isAddLight buffer)
      meshCount = Array.length (Array.filter isDrawMesh buffer)
  in lightCount == Array.length scene.lights
     && meshCount == Array.length scene.meshes
```

**Performance Bounds**:
- flattenScene: O(lights + meshes)
- All map operations: O(n)

**Edge Cases**:
- Empty scene (no lights, no meshes)
- Scene with only lights
- Scene with only meshes
- Large scene (1000+ meshes)

---

## 3. LAYOUT ALGORITHMS

### 3.1 Tensor Layout (Stride Computation)

**Implementation**: `Hydrogen.Schema.Tensor.Layout`

**Correctness Invariants**:

```purescript
-- INV-LAY-1: Row-major last dimension has stride 1
prop_rowMajorLastStride :: Array Dim -> Boolean
prop_rowMajorLastStride shape =
  let strides = computeStridesRowMajor shape
  in Array.last strides == Just (Stride 1)

-- INV-LAY-2: Column-major first dimension has stride 1
prop_colMajorFirstStride :: Array Dim -> Boolean
prop_colMajorFirstStride shape =
  let strides = computeStridesColumnMajor shape
  in Array.head strides == Just (Stride 1)

-- INV-LAY-3: Offset calculation is correct
prop_offsetCorrect :: Layout -> Array Int -> Boolean
prop_offsetCorrect layout indices =
  let strides = stridesFor layout
      computed = offsetAt layout indices
      expected = sum (zipWith (*) indices (map unwrapStride strides))
  in computed == expected

-- INV-LAY-4: Contiguous layout has no gaps
prop_contiguousNoGaps :: Array Dim -> MemoryOrder -> Boolean
prop_contiguousNoGaps shape order =
  let layout = contiguous shape order
  in minBufferSize layout == unwrapDim (totalElements layout)

-- INV-LAY-5: Transpose swaps last two dimensions
prop_transposeSwaps :: Layout -> Boolean
prop_transposeSwaps layout =
  case transpose layout of
    Nothing -> Array.length (effectiveShape layout) < 2
    Just transposed ->
      let origShape = effectiveShape layout
          transShape = effectiveShape transposed
          n = Array.length origShape
      in Array.index transShape (n - 1) == Array.index origShape (n - 2)
         && Array.index transShape (n - 2) == Array.index origShape (n - 1)

-- INV-LAY-6: Memory efficiency is <= 1.0 for valid layouts
prop_memoryEfficiencyBounded :: Layout -> Boolean
prop_memoryEfficiencyBounded layout =
  let eff = memoryEfficiency layout
  in eff <= 1.0 && eff >= 0.0

-- INV-LAY-7: Broadcasting stride 0 for expanded dims
prop_broadcastStrideZero :: Array Dim -> Array Dim -> Boolean
prop_broadcastStrideZero original target =
  let layout = broadcasted original target
      strides = stridesFor layout
  in all (\(Tuple o t s) -> 
    if unwrapDim o == 1 && unwrapDim t > 1
    then unwrapStride s == 0
    else true
  ) (zip3 (padLeft original target) target strides)
```

**Performance Bounds**:
- `computeStrides`: O(n) where n = rank
- `offsetAt`: O(n)
- `transpose`: O(n)
- `permute`: O(n)

**Edge Cases**:
- Empty shape: []
- Scalar: [1]
- 1D: [n]
- Large rank: 8+ dimensions
- Shape with dim = 0 (degenerate)
- Negative strides (reverse iteration)

---

### 3.2 Graph Layout (Force-Directed, Treemap, etc.)

**Implementation**: `Hydrogen.Schema.Graph.Layout`

**Correctness Invariants**:

```purescript
-- INV-GRAPH-1: ForceParams damping in [0, 1]
prop_dampingBounded :: ForceParams -> Boolean
prop_dampingBounded params =
  params.damping >= 0.0 && params.damping <= 1.0

-- INV-GRAPH-2: RadialParams angles define valid arc
prop_radialAnglesValid :: RadialParams -> Boolean
prop_radialAnglesValid params =
  params.endAngle >= params.startAngle
  || (params.clockwise && params.startAngle > params.endAngle)  -- Wraparound allowed

-- INV-GRAPH-3: TreemapParams ratio is positive
prop_treemapRatioPositive :: TreemapParams -> Boolean
prop_treemapRatioPositive params =
  params.ratio > 0.0

-- INV-GRAPH-4: NodePosition dimensions are non-negative
prop_nodePositionValid :: NodePosition -> Boolean
prop_nodePositionValid pos =
  pos.width >= 0.0 && pos.height >= 0.0

-- INV-GRAPH-5: Layout configuration is self-consistent
prop_layoutConfigConsistent :: LayoutConfig -> Boolean
prop_layoutConfigConsistent config =
  case config.algorithm of
    Treemap -> isJust config.treemapParams
    Sunburst -> isJust config.radialParams
    Radial -> isJust config.radialParams
    Force -> isJust config.forceParams
    HierarchicalForce -> isJust config.forceParams
    _ -> true  -- No specific params required
```

**Performance Bounds**:
- Treemap Squarify: O(n log n)
- Force-directed: O(n^2) per iteration, O(k * n^2) total
- Radial/Sunburst: O(n)

---

## 4. BINARY SERIALIZATION (GPU/Binary.purs)

### 4.1 Serialization Correctness

**Implementation**: `Hydrogen.GPU.Binary`

**Correctness Invariants**:

```purescript
-- INV-BIN-1: Magic number is correct
prop_magicCorrect :: Boolean
prop_magicCorrect = magic == 0x48594447

-- INV-BIN-2: Header is exactly 16 bytes
prop_headerSize :: Boolean
prop_headerSize =
  Array.length (serializeHeader { magic, version: 1, count: 0, flags: 0 }) == 16

-- INV-BIN-3: F32 roundtrip preserves value (within precision)
prop_f32Roundtrip :: Number -> Boolean
prop_f32Roundtrip n =
  case readF32 (writeF32 n) 0 of
    Nothing -> false
    Just read -> abs (read - n) < 0.0001 || n == read

-- INV-BIN-4: U32 roundtrip is exact
prop_u32Roundtrip :: Int -> Boolean
prop_u32Roundtrip n =
  let bytes = writeU32 n
  in readU32 bytes 0 == Just n

-- INV-BIN-5: Command type byte is correct
prop_commandTypeByte :: DrawCommand msg -> Boolean
prop_commandTypeByte cmd =
  let serialized = serializeCommand cmd
  in case cmd of
       DC.Noop -> Array.head serialized == Just 0x00
       DC.DrawRect _ -> Array.head serialized == Just 0x01
       DC.DrawQuad _ -> Array.head serialized == Just 0x02
       DC.DrawGlyph _ -> Array.head serialized == Just 0x03
       DC.DrawPath _ -> Array.head serialized == Just 0x04
       DC.DrawParticle _ -> Array.head serialized == Just 0x05
       DC.PushClip _ -> Array.head serialized == Just 0x10
       DC.PopClip -> Array.head serialized == Just 0x11
       DC.DrawGlyphPath _ -> Array.head serialized == Just 0x20
       DC.DrawGlyphInstance _ -> Array.head serialized == Just 0x21
       DC.DrawWord _ -> Array.head serialized == Just 0x22
       DC.DefinePathData _ -> Array.head serialized == Just 0x23
       DC.UpdateAnimationState _ -> Array.head serialized == Just 0x24

-- INV-BIN-6: Payload sizes match constants
prop_payloadSizes :: Boolean
prop_payloadSizes =
  rectPayloadSize == 56
  && quadPayloadSize == 56
  && glyphPayloadSize == 44
  && particlePayloadSize == 36
  && glyphInstancePayloadSize == 76

-- INV-BIN-7: Serialization is deterministic
prop_serializationDeterministic :: CommandBuffer msg -> Boolean
prop_serializationDeterministic buffer =
  serialize buffer == serialize buffer

-- INV-BIN-8: All bytes are in valid range [0, 255]
prop_bytesInRange :: CommandBuffer msg -> Boolean
prop_bytesInRange buffer =
  let Bytes arr = serialize buffer
  in all (\b -> b >= 0 && b <= 255) arr
```

**Performance Bounds**:
- Serialize single command: O(payload_size)
- Serialize buffer: O(sum of payload sizes)
- Deserialize: O(buffer_size)

**Edge Cases**:
- Empty command buffer
- Maximum depth value (Number.MAX_VALUE)
- Negative coordinates
- Zero-length paths
- Large contour counts
- Unicode in path segment (should not happen, but test)

---

## 5. UUID5 IDENTITY (Scene3D/Identity.purs)

### 5.1 Determinism and Collision Resistance

**Implementation**: `Hydrogen.GPU.Scene3D.Identity`

**Correctness Invariants**:

```purescript
-- INV-UUID-1: Same input always produces same UUID
prop_uuid5Deterministic :: Position3D -> Boolean
prop_uuid5Deterministic pos =
  positionId pos == positionId pos

-- INV-UUID-2: Different inputs produce different UUIDs (high probability)
prop_uuid5CollisionResistant :: Position3D -> Position3D -> Boolean
prop_uuid5CollisionResistant p1 p2 =
  if p1 == p2
  then positionId p1 == positionId p2
  else positionId p1 /= positionId p2  -- With overwhelming probability

-- INV-UUID-3: Canonical string is unique per type
prop_canonicalUnique :: BoxMeshParams -> SphereMeshParams -> Boolean
prop_canonicalUnique box sphere =
  boxMeshId box /= sphereMeshId sphere  -- Different namespaces

-- INV-UUID-4: meshId dispatches correctly
prop_meshIdDispatch :: Mesh3D -> Boolean
prop_meshIdDispatch mesh =
  let uuid = meshId mesh
  in uuid == case mesh of
       BoxMesh3D params -> boxMeshId params
       SphereMesh3D params -> sphereMeshId params
       -- etc.

-- INV-UUID-5: Material identity includes all parameters
prop_materialIdComplete :: StandardMaterialParams -> StandardMaterialParams -> Boolean
prop_materialIdComplete m1 m2 =
  if m1 == m2
  then standardMaterialId m1 == standardMaterialId m2
  else standardMaterialId m1 /= standardMaterialId m2
```

**Performance Bounds**:
- UUID5 generation: O(canonical_string_length)
- All identity functions: O(parameter_count)

**Edge Cases**:
- Zero values for all parameters
- Maximum float values
- Negative values
- Very long parameter strings

---

## 6. DEPTH SORTING AND BATCHING (DrawCommand.purs)

### 6.1 Depth Sorting Stability

**Implementation**: `Hydrogen.GPU.DrawCommand.sortByDepth`

**Correctness Invariants**:

```purescript
-- INV-DEPTH-1: Sorted buffer is actually sorted by depth
prop_sortedByDepth :: CommandBuffer msg -> Boolean
prop_sortedByDepth buffer =
  let sorted = sortByDepth buffer
      depths = map getDepth sorted
  in isSorted depths

-- INV-DEPTH-2: Sort preserves all commands
prop_sortPreservesCommands :: CommandBuffer msg -> Boolean
prop_sortPreservesCommands buffer =
  Array.length (sortByDepth buffer) == Array.length buffer

-- INV-DEPTH-3: Sort is stable (equal depths maintain order)
prop_sortIsStable :: CommandBuffer msg -> Boolean
prop_sortIsStable buffer =
  let indexed = Array.mapWithIndex Tuple buffer
      sorted = sortByDepth buffer
      indexedSorted = sortByDepthIndexed indexed
  in all (\((Tuple i1 _), (Tuple i2 _)) -> 
    if getDepth (snd (Tuple i1)) == getDepth (snd (Tuple i2))
    then i1 < i2  -- Original order preserved
    else true
  ) (pairs indexedSorted)

-- INV-DEPTH-4: Clip commands maintain depth 0.0
prop_clipDepthZero :: ClipRegion -> Boolean
prop_clipDepthZero region =
  getDepth (PushClip region) == 0.0
  && getDepth PopClip == 0.0
```

**Performance Bounds**:
- `sortByDepth`: O(n log n)
- `batchByMaterial`: O(n log n) for sort + O(n) for grouping

---

### 6.2 Clip Stack Balance

**Implementation**: `PushClip` / `PopClip` commands

**Correctness Invariants**:

```purescript
-- INV-CLIP-1: Clip stack is balanced
prop_clipStackBalanced :: CommandBuffer msg -> Boolean
prop_clipStackBalanced buffer =
  let pushCount = Array.length (Array.filter isPushClip buffer)
      popCount = Array.length (Array.filter isPopClip buffer)
  in pushCount == popCount

-- INV-CLIP-2: Every Pop has a preceding Push
prop_popHasPush :: CommandBuffer msg -> Boolean
prop_popHasPush buffer =
  scanClipStack 0 buffer
  where
    scanClipStack depth [] = depth >= 0
    scanClipStack depth (cmd : rest) = case cmd of
      PushClip _ -> scanClipStack (depth + 1) rest
      PopClip -> depth > 0 && scanClipStack (depth - 1) rest
      _ -> scanClipStack depth rest

-- INV-CLIP-3: validateBuffer catches unbalanced clips
prop_validateCatchesUnbalanced :: CommandBuffer msg -> Boolean
prop_validateCatchesUnbalanced buffer =
  -- Currently validateBuffer returns Unit, but should detect issues
  true  -- Placeholder for when validation is implemented
```

---

## 7. PATH COMMAND VALIDITY (Element/Flatten, DrawCommand)

### 7.1 Path Segment Validity

**Correctness Invariants**:

```purescript
-- INV-PATH-1: Path starts with MoveTo
prop_pathStartsWithMove :: PathSpec -> Boolean
prop_pathStartsWithMove spec =
  case Array.head spec.shape.commands of
    Just (MoveTo _) -> true
    _ -> false

-- INV-PATH-2: ClosePath returns to last MoveTo position
prop_closePathReturns :: Array PathCommand -> Boolean
prop_closePathReturns commands =
  let moveToPositions = findMoveToPositions commands
      closePathPositions = findClosePathImpliedPositions commands
  in all (\cp -> elem cp moveToPositions) closePathPositions

-- INV-PATH-3: All coordinates are finite
prop_coordinatesFinite :: PathSegment -> Boolean
prop_coordinatesFinite seg = case seg of
  MoveTo pt -> isFinite pt.x && isFinite pt.y
  LineTo pt -> isFinite pt.x && isFinite pt.y
  QuadraticTo c e -> all isFinite [c.x, c.y, e.x, e.y]
  CubicTo c1 c2 e -> all isFinite [c1.x, c1.y, c2.x, c2.y, e.x, e.y]
  ClosePath -> true

-- INV-PATH-4: Contour winding is consistent
prop_contourWindingConsistent :: ContourData -> Boolean
prop_contourWindingConsistent contour =
  let winding = computeWinding contour.commands
  in (contour.isOuter && winding > 0) || (not contour.isOuter && winding < 0)

-- INV-PATH-5: Ellipse approximation uses correct kappa
prop_ellipseKappa :: Boolean
prop_ellipseKappa =
  let kappa = 0.5522847498
      -- 4 cubic beziers should approximate circle to <0.001% error
  in abs (kappa - (4.0/3.0) * tan (pi/8.0)) < 0.0000001
```

---

## 8. TEST IMPLEMENTATION PRIORITIES

### Phase 1: Critical Path (Week 1)
1. LRU eviction ordering (cache correctness)
2. TTL expiration (cache correctness)
3. Element.Flatten depth monotonicity
4. Scene3D flatten buffer structure
5. Binary serialization roundtrip

### Phase 2: Correctness (Week 2)
1. Tag invalidation completeness
2. Generation monotonicity
3. UUID5 determinism
4. Stride computation correctness
5. Path command validity

### Phase 3: Edge Cases (Week 3)
1. All empty/null/zero edge cases
2. Maximum value edge cases
3. Adversarial input testing
4. Performance regression tests

### Phase 4: Integration (Week 4)
1. Full pipeline tests (Element -> Binary)
2. Cross-module property tests
3. Stress tests (large inputs)
4. Memory efficiency validation

---

## 9. GENERATOR REQUIREMENTS

Each property test requires custom generators. Key generators needed:

```purescript
-- Cache generators
genLRUTracker :: Gen LRUTracker
genCacheEntry :: forall a. Gen a -> Gen (CacheEntry a)
genCompositionCache :: forall a. Gen a -> Gen (CompositionCache a)
genCacheTag :: Gen CacheTag

-- Element generators
genElement :: Gen Element
genRectangleSpec :: Gen RectangleSpec
genPathCommand :: Gen PathCommand
genGlyphSpec :: Gen GlyphSpec

-- Scene3D generators (EXISTING in Test.Scene3D)
genPosition3D :: Gen Position3D
genMesh3D :: Gen Mesh3D
genMaterial3D :: Gen Material3D
genScene3D :: forall msg. Gen (Scene3D msg)

-- Layout generators
genLayout :: Gen Layout
genDim :: Gen Dim
genStride :: Gen Stride
genMemoryOrder :: Gen MemoryOrder

-- DrawCommand generators
genDrawCommand :: forall msg. Gen msg -> Gen (DrawCommand msg)
genPathSegment :: Gen PathSegment
genClipRegion :: Gen ClipRegion
```

---

## 10. REGRESSION TEST CATALOG

| Bug ID | Algorithm | Description | Test |
|--------|-----------|-------------|------|
| REG-001 | LRU | Empty tracker crash | `lruOldest emptyLRU == Nothing` |
| REG-002 | TTL | Negative expiration | `expiresAt = Just (-1.0)` handled |
| REG-003 | Flatten | Infinite depth loop | Deeply nested groups terminate |
| REG-004 | Binary | NaN serialization | NaN produces valid bytes |
| REG-005 | UUID5 | Empty string canonical | Empty params produce valid UUID |
| REG-006 | Stride | Zero dimension | `dim 0` handled gracefully |
| REG-007 | Path | Empty path | `commands = []` doesn't crash |
| REG-008 | Clip | Pop without push | Detected by validation |

---

                                                           // end // round // 2
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
