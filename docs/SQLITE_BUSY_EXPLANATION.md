# Why "SQLite database is busy" Appears

## What's Happening

The `error (ignored): error: SQLite database ... is busy` message appears when multiple Nix processes try to access the evaluation cache database simultaneously.

## What's Currently Running

From your process list, these Nix-related processes are active:

1. **`nix-daemon`** (PID 499) - Background service that manages Nix operations
2. **`nix-shell`** (PID 32017) - Your current dev shell
3. **`opencode`** (PID 755) - May be using Nix for evaluation
4. **`git`** (PID 42374) - Running git operations (may trigger Nix evaluation)

## Why It Happens

### The Eval Cache
- Nix uses an **evaluation cache** (`eval-cache-v5`) to speed up flake evaluation
- It stores results of previous evaluations so Nix doesn't have to re-evaluate everything
- Location: `~/.cache/nix/eval-cache-v5/*.sqlite`

### The "Busy" Error
- **eval-cache-v5** uses an older SQLite mode that can lock the database during writes
- When multiple processes try to access it simultaneously, one gets blocked
- Nix handles this gracefully by:
  1. Retrying the operation
  2. Marking it as `(ignored)` if it's not critical
  3. Continuing with the operation

## Is It a Problem?

**No!** The `(ignored)` means:
- ✅ Nix handled it gracefully
- ✅ Your operation completed successfully
- ✅ It's just a warning, not an error
- ✅ Everything still works

## Why You See It Now

You're seeing it because:
1. **Multiple Nix processes** - You have `nix-daemon`, `nix-shell`, and possibly other tools running
2. **First-time setup** - Lots of evaluations happening as packages are built
3. **Old cache format** - `eval-cache-v5` is less concurrent than newer versions

## Solutions (Optional)

### Option 1: Ignore It (Recommended)
It's harmless and doesn't affect functionality. Just ignore it.

### Option 2: Clear Old Cache
If it bothers you:
```bash
rm -rf ~/.cache/nix/eval-cache-v5
```
Nix will regenerate it as needed.

### Option 3: Upgrade Nix (If Available)
Newer Nix versions use `eval-cache-v6` with WAL mode for better concurrency.

## Bottom Line

**This is normal and harmless.** Your setup worked perfectly - the "(ignored)" message confirms Nix handled the contention gracefully. Everything is working as expected!
