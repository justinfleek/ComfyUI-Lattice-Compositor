# Precision Limits Specification

**Date:** 2025-01-20  
**Status:** ACTIVE - Enforced in CI/CD  
**Purpose:** Define domain-specific precision limits to prevent systemic precision issues

---

## Problem Statement

Different domains require different precision:
- **Physics forces**: Lower precision acceptable (simulation tolerance)
- **3D coordinates**: High precision required (exact positioning)
- **Data visualization**: Medium precision (human-readable)
- **UI display**: Lower precision (pixel-aligned)

Without systematic enforcement, precision issues become systemic:
- Forces stored with 15 decimal places (wasteful, unnecessary)
- 3D coordinates rounded to 1 decimal place (precision loss, visual artifacts)
- Export formats inconsistent precision (compatibility issues)

---

## Domain-Specific Precision Limits

| Domain | Decimal Places | Epsilon | Use Cases |
|--------|---------------|---------|-----------|
| **Physics Forces** | 3 | 0.001 | Force magnitudes, velocities, accelerations, particle forces |
| **3D Coordinates** | 6 | 0.000001 | Position.x/y/z, rotation angles, z-depth, camera positions |
| **Data Visualization** | 2 | 0.01 | Chart data points, statistics, percentages, data asset values |
| **UI Display** | 1 | 0.1 | Slider values, pixel positions, UI coordinates |
| **Export Formats** | 4 | 0.0001 | Export to external formats (ComfyUI, MotionCtrl, etc.) |

---

## Implementation

### Haskell Module: `Lattice.Types.PrecisionLimits`

```haskell
-- Validate and normalize physics force
validatePhysicsForce :: Double -> Either Text Double

-- Validate and normalize 3D coordinate
validate3DCoordinate :: Double -> Either Text Double

-- Validate and normalize data visualization value
validateDataVisualization :: Double -> Either Text Double

-- Validate and normalize UI display value
validateUIDisplay :: Double -> Either Text Double

-- Validate and normalize export format value
validateExportFormat :: Double -> Either Text Double
```

### TypeScript Module: `ui/src/utils/precisionLimits.ts` (TODO)

---

## Enforcement Points

### 1. Input Validation (Boundary Guards)

**Where:** All FFI boundaries, JSON deserialization, user input

**Example:**
```haskell
-- Physics force input
parsePhysicsForce :: Value -> Parser Double
parsePhysicsForce v = do
  d <- parseJSON v
  case validatePhysicsForce d of
    Left err -> fail err
    Right normalized -> return normalized
```

### 2. Export Serialization (Output Normalization)

**Where:** All export functions (ComfyUI, MotionCtrl, etc.)

**Example:**
```haskell
-- Export 3D coordinate
exportPosition :: Position2DOr3D -> Value
exportPosition (Position2DOr3D x y mz) =
  object
    [ "x" .= normalizePrecision PrecisionExportFormats x
    , "y" .= normalizePrecision PrecisionExportFormats y
    , "z" .= maybe [] (\z -> ["z" .= normalizePrecision PrecisionExportFormats z]) mz
    ]
```

### 3. Storage (Database/File Persistence)

**Where:** Project save/load, asset metadata

**Example:**
```haskell
-- Save 3D coordinate
savePosition :: Position2DOr3D -> Value
savePosition pos =
  -- Use 3D coordinate precision (6 decimals) for storage
  normalizePrecision Precision3DCoordinates pos
```

### 4. UI Display (Rendering)

**Where:** Slider values, property panels, tooltips

**Example:**
```haskell
-- Display physics force in UI
displayPhysicsForce :: Double -> Text
displayPhysicsForce value =
  let normalized = normalizePrecision PrecisionUIDisplay value
  in T.pack (show normalized)
```

---

## CI/CD Guardrails

### 1. Precision Validation Tests

**File:** `src/lattice/tests/test_precision_limits.hs`

**Checks:**
- All physics forces normalized to 3 decimals
- All 3D coordinates normalized to 6 decimals
- All data visualization values normalized to 2 decimals
- All UI display values normalized to 1 decimal
- All export values normalized to 4 decimals

### 2. Property Tests

**File:** `ui/src/__tests__/property/precision-limits.property.test.ts`

**Checks:**
- Random values are normalized correctly
- Precision limits are enforced
- No precision loss beyond acceptable epsilon

### 3. Export Format Validation

**File:** `scripts/validate-export-precision.sh`

**Checks:**
- All exported JSON files have correct precision
- No values exceed domain-specific limits
- Round-trip precision preserved

---

## Migration Plan

### Phase 1: Add Precision Limits Module (DONE)
- ✅ Created `Lattice.Types.PrecisionLimits`
- ✅ Defined domain-specific limits
- ✅ Created validation functions

### Phase 2: Add Validation at Boundaries (TODO)
- ⏳ Add precision validation to FFI boundaries
- ⏳ Add precision validation to JSON deserialization
- ⏳ Add precision normalization to export functions

### Phase 3: Add CI/CD Checks (TODO)
- ⏳ Create precision validation tests
- ⏳ Add export format validation script
- ⏳ Add pre-commit hook for precision checks

### Phase 4: Migrate Existing Code (TODO)
- ⏳ Update physics force handling
- ⏳ Update 3D coordinate handling
- ⏳ Update data visualization handling
- ⏳ Update UI display handling
- ⏳ Update export format handling

---

## Examples

### Physics Force (3 decimals)

```haskell
-- Input: 1.23456789
-- Normalized: 1.235
-- Epsilon: 0.001
validatePhysicsForce 1.23456789
-- Right 1.235
```

### 3D Coordinate (6 decimals)

```haskell
-- Input: 123.456789012345
-- Normalized: 123.456789
-- Epsilon: 0.000001
validate3DCoordinate 123.456789012345
-- Right 123.456789
```

### Data Visualization (2 decimals)

```haskell
-- Input: 99.999999
-- Normalized: 100.0
-- Epsilon: 0.01
validateDataVisualization 99.999999
-- Right 100.0
```

### UI Display (1 decimal)

```haskell
-- Input: 42.987654
-- Normalized: 43.0
-- Epsilon: 0.1
validateUIDisplay 42.987654
-- Right 43.0
```

### Export Format (4 decimals)

```haskell
-- Input: 0.123456789
-- Normalized: 0.1235
-- Epsilon: 0.0001
validateExportFormat 0.123456789
-- Right 0.1235
```

---

## Rationale

### Why Different Precision Per Domain?

1. **Physics Forces (3 decimals)**: Simulation doesn't need micrometer precision. Forces are approximate by nature.
2. **3D Coordinates (6 decimals)**: Need high precision for exact positioning, especially for camera exports to AI models.
3. **Data Visualization (2 decimals)**: Human-readable precision. Charts don't need 15 decimal places.
4. **UI Display (1 decimal)**: Pixel-aligned. UI sliders don't need sub-pixel precision.
5. **Export Formats (4 decimals)**: Balance between precision and compatibility with external formats.

### Why Enforce at Boundaries?

- **Input**: Normalize immediately to prevent precision creep
- **Export**: Ensure consistent precision for external formats
- **Storage**: Use appropriate precision for persistence
- **UI**: Display appropriate precision for user interaction

---

## References

- `src/lattice/Types/PrecisionLimits.hs` - Implementation
- `src/lattice/Utils/NumericSafety.hs` - Rounding functions
- `ui/src/services/math3d.ts` - Precision constants (documentation only)
- `ui/src/utils/numericSafety.ts` - TypeScript rounding functions
