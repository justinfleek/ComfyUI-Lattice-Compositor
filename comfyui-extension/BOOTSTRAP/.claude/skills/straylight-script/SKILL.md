---
name: straylight-script
description: Write Haskell scripts using Straylight.Script instead of bash. Use when writing scripts, shell automation, bash replacement, command-line tools, or when the user mentions bash, shell, scripts, or command-line operations.
license: MIT
compatibility: opencode
---

# Straylight Script - Typed Unix

Write Haskell scripts using Straylight.Script instead of bash.

## Core Principle

**ALL scripts in Haskell. ZERO bash logic.**

If it has a branch, it's not bash. Rewrite in Haskell.

## Directory Structure

```
nix/scripts/
├── Straylight/
│   ├── Script.hs                 # Main prelude (1193 lines)
│   ├── Nix.hs                    # WASM plugin interface
│   ├── Config/                   # Dhall type definitions
│   │   ├── Base.dhall            # StorePath, MemMiB, CpuCount
│   │   ├── Firecracker.dhall     # VM config schema
│   │   └── NvidiaSdk.dhall       # NVIDIA extraction config
│   └── Script/
│       ├── Config.hs             # FromDhall instances
│       ├── Clap.hs               # Parser for clap-based CLI tools
│       ├── Getopt.hs             # Parser for GNU getopt_long tools
│       ├── Oci.hs                # OCI container operations
│       ├── Vm.hs                 # VM rootfs construction
│       ├── Vfio.hs               # GPU passthrough (VFIO/IOMMU)
│       └── Tools/                # 24 tool wrappers
│           ├── Rg.hs, Bwrap.hs, Crane.hs, Jq.hs, ...
├── nvidia-extract.hs             # NVIDIA SDK extraction
├── oci-gpu.hs                    # GPU container runner
├── fc-run.hs                     # Firecracker runner
└── vfio-bind.hs                  # GPU passthrough
```

## Writing a New Script

### Step 1: Create the Script

```haskell
-- nix/scripts/my-tool.hs
{-# LANGUAGE OverloadedStrings #-}

import Straylight.Script
import System.Environment (getArgs)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [arg1, arg2] -> script $ doThing (pack arg1) (pack arg2)
        _ -> script $ do
            echoErr "Usage: my-tool <arg1> <arg2>"
            exit 1

doThing :: Text -> Text -> Sh ()
doThing x y = do
    echoErr $ ":: Processing " <> x
    output <- run "echo" [x, y]
    echo output
```

### Step 2: Register in script.nix

```nix
compiled = {
  my-tool = mkCompiledScript {
    name = "my-tool";
    deps = [ final.jq final.crane ];
  };
};
```

### Step 3: Run It

```bash
# Compiled (production)
nix run .#straylight.script.compiled.my-tool -- arg1 arg2

# Interpreted (development)
nix run .#straylight.script.shell
runghc -i. my-tool.hs arg1 arg2
```

## API Reference

### Running Scripts
```haskell
script      :: Sh a -> IO a   -- Silent, errors on failure
scriptV     :: Sh a -> IO a   -- Verbose (shows commands)
scriptDebug :: Sh a -> IO a   -- Very verbose
```

### Running Commands
```haskell
run       :: FilePath -> [Text] -> Sh Text  -- Capture stdout
run_      :: FilePath -> [Text] -> Sh ()    -- Ignore stdout
bash      :: Text -> Sh Text                -- Run bash -c "..."
which     :: FilePath -> Sh (Maybe FilePath)
```

### Output
```haskell
echo      :: Text -> Sh ()       -- Print to stdout
echoErr   :: Text -> Sh ()       -- Print to stderr (USE THIS)
die       :: Text -> Sh a        -- Print error and exit
exit      :: Int -> Sh ()
```

### Filesystem
```haskell
ls, cp, mv, rm, mkdir, mkdirP
pwd, cd, home, withTmpDir
test_f, test_d, test_e         -- Existence tests
symlink, readlink, canonicalize
```

### Text (Data.Text)
```haskell
Text, pack, unpack
strip, lines, unlines, words, unwords
isPrefixOf, isSuffixOf, isInfixOf
replace, splitOn, breakOn
```

### Error Handling
```haskell
try, catch, bracket, finally
errExit :: Bool -> Sh a -> Sh a  -- Control error-on-failure
```

## Tool Wrappers

Import qualified to avoid name conflicts:

```haskell
import qualified Straylight.Script.Tools.Rg as Rg
import qualified Straylight.Script.Tools.Bwrap as Bwrap
import qualified Straylight.Script.Tools.Crane as Crane
import qualified Straylight.Script.Tools.Jq as Jq
```

### Available Tools
| Category | Tools |
|----------|-------|
| Clap (Rust) | rg, fd, bat, delta, dust, tokei, hyperfine, deadnix, statix |
| GNU | ls, grep, sed, find, xargs, tar, gzip, wget, rsync |
| Hand-crafted | jq, crane, bwrap |

### Bwrap Example (Builder Pattern)
```haskell
let sandbox = Bwrap.defaults
        & Bwrap.roBind "/nix/store" "/nix/store"
        & Bwrap.dev "/dev"
        & Bwrap.proc "/proc"
        & Bwrap.tmpfs "/tmp"
        & Bwrap.unshareAll
        & Bwrap.dieWithParent

Bwrap.exec sandbox ["./myprogram", "--flag"]
```

## Domain Modules

### Straylight.Script.Oci - Containers
```haskell
rootfs <- Oci.pullOrCache Oci.defaultConfig "alpine:latest"
let sandbox = Oci.baseSandbox rootfs & Oci.withGpuSupport env gpuBinds
```

### Straylight.Script.Vfio - GPU Passthrough
```haskell
gpus <- Vfio.listNvidiaGpus
devices <- Vfio.bindToVfio "0000:01:00.0"
```

### Straylight.Script.Vm - Virtual Machines
```haskell
Vm.buildExt4 "/tmp/rootfs-dir" "/tmp/rootfs.ext4"
Vm.runFirecracker config
```

## Dhall Configuration

For Nix -> Haskell value passing:

```dhall
-- nix/scripts/Straylight/Config/MyTool.dhall
let Base = ./Base.dhall

let Config =
    { Type =
        { inputPath : Base.StorePath
        , verbose : Bool
        }
    , default = { verbose = False }
    }

in { Config }
```

```haskell
-- Haskell side
data Config = Config
    { inputPath :: StorePath
    , verbose :: Bool
    } deriving (Generic)

instance FromDhall Config
```

## Best Practices

1. **Always use `echoErr`** for status messages (keeps stdout clean)
2. **Use `errExit False`** when command failure is acceptable
3. **Import tools qualified** to avoid name clashes
4. **Parse args early**, fail fast with clear usage
5. **Use `withTmpDir`** for intermediate files
6. **Use builder pattern** (`&`) for Bwrap sandboxes

## Generate Tool Wrappers

```bash
# Generate and print
nix run .#straylight.script.gen-wrapper -- rg

# Write to Tools/Fd.hs
nix run .#straylight.script.gen-wrapper -- fd --write

# Force GNU format
nix run .#straylight.script.gen-wrapper -- grep --gnu --write
```
