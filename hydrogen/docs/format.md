# Hydrogen.Data.Format

Pure formatting functions for display.

## Byte Formatting

```purescript
import Hydrogen.Data.Format (formatBytes, formatBytesCompact, kb, mb, gb, tb)

formatBytes 500.0          -- "500 B"
formatBytes 1024.0         -- "1.0 KB"
formatBytes (1.5 * mb)     -- "1.5 MB"
formatBytes (2.5 * gb)     -- "2.5 GB"
formatBytes (1.2 * tb)     -- "1.2 TB"
formatBytes (-1024.0)      -- "-1.0 KB"

formatBytesCompact (1.5 * gb)  -- "1.5GB" (no space)
```

### Constants

```purescript
kb :: Number  -- 1024
mb :: Number  -- 1024^2
gb :: Number  -- 1024^3
tb :: Number  -- 1024^4
```

### Parsing

```purescript
parseBytes "1.5 GB"  -- Just 1610612736.0
parseBytes "500 B"   -- Just 500.0
parseBytes "invalid" -- Nothing
```

## Number Formatting

```purescript
import Hydrogen.Data.Format (formatNum, formatNumCompact, formatPercent, formatCount)

-- One decimal place
formatNum 3.14159      -- "3.1"

-- Compact with suffix
formatNumCompact 500.0      -- "500"
formatNumCompact 1500.0     -- "1.5k"
formatNumCompact 2500000.0  -- "2.5M"

-- Percentage (from 0-1 range)
formatPercent 0.874    -- "87.4%"

-- Count (alias for formatNumCompact on Int)
formatCount 45230      -- "45.2k"
```

## Duration Formatting

```purescript
import Hydrogen.Data.Format (formatDuration, formatDurationCompact, formatDurationMs)

-- Full format (from seconds)
formatDuration 45      -- "45s"
formatDuration 125     -- "2m 5s"
formatDuration 3661    -- "1h 1m 1s"
formatDuration 0       -- "-"

-- Compact (largest unit only)
formatDurationCompact 3661  -- "1h"

-- From milliseconds
formatDurationMs 125000     -- "2m 5s"
```

## Calculations

All calculations handle division by zero safely:

```purescript
import Hydrogen.Data.Format (percentage, rate, ratio)

-- Integer percentage
percentage 750.0 1000.0   -- 75
percentage 1.0 0.0        -- 0 (safe)

-- Rate (0-1 range)
rate 90 100    -- 0.9
rate 1 0       -- 0.0 (safe)

-- Ratio
ratio 3.0 4.0  -- 0.75
ratio 1.0 0.0  -- 0.0 (safe)
```

## Design

All functions are:

- **Pure** - No effects, easy to test
- **Total** - Handle edge cases (negatives, zero, etc.)
- **Consistent** - Same formatting rules across the app
