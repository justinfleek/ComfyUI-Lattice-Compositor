# CLAUDE CODE — SESSION RESET & OPERATING CHARTER (v5)

You are operating **inside an active repo** for a **ComfyUI v2 toolbar extension with a pop-out Vue UI**.

---

## YOU ARE NOT HERE TO:
- Perform full codebase audits
- Speculate about architecture
- Guess file locations
- Reframe goals
- Suggest alternative approaches
- Optimize prematurely
- Rewrite large systems

## YOU ARE HERE TO:
- Stabilize lifecycle boundaries
- Eliminate cascading failures
- Enforce idempotence, teardown safety, and runtime correctness
- Make the extension safe to install, load, open, close, reload, and coexist with other ComfyUI extensions

---

## ABSOLUTE RULES (DO NOT VIOLATE)

1. **Do NOT guess file names or paths**
   - Only operate on files explicitly opened or referenced
   - If you need a file, ASK for it

2. **Do NOT do file-by-file audits**
   - Audits are scoped by *runtime surface*, not directories

3. **Do NOT output long explanations**
   - Prefer diffs, full corrected files, or bulletproof reasoning tied to concrete code

4. **Do NOT refactor architecture**
   - Guards > rewrites
   - Idempotence > redesign
   - Explicit teardown > abstraction

5. **Do NOT touch internal systems unless lifecycle-stable**
   - Particles, expressions, math, effects are downstream
   - Lifecycle stability comes first

6. **If you suggest a fix, you MUST output the full corrected file**
   - Granular suggestions without a reviewed full-file output are forbidden

7. **No auto-mounting, no implicit globals, no hidden side effects**
   - All lifecycle must be explicit and reversible

---

## CURRENT STRATEGY (NON-NEGOTIABLE)

We are performing a **Lifecycle Stability Pass**, NOT a full audit.

### The ONLY questions that matter:
- Can this extension be mounted twice safely?
- Can it be unmounted cleanly?
- Can it survive ComfyUI reloads?
- Can it coexist with other extensions?
- Can it fail without corrupting global state?

If a change does not directly improve one of these, do not propose it.

---

## DEFINITION OF DONE (FOR THIS PHASE)

A file is considered "done" ONLY if:
- All side effects are paired with teardown
- All entrypoints are idempotent
- All global state is owned and guarded
- No DOM, listener, worker, WebGL, or timer leaks are possible
- The file can be safely locked and not revisited

---

## PROCESS

1. Read this charter
2. Wait for explicit instruction or file reference
3. Do NOT start scanning the repo on your own
4. Operate ONLY on what is explicitly provided

---

## CURRENT STATUS

- This is a ComfyUI toolbar extension with a pop-out Vue UI
- Must install cleanly via pip and run inside ComfyUI
- Lifecycle bugs are more dangerous than logic bugs
- `compositor/ui/src/main.ts` was previously stabilized
- Further work proceeds file-by-file ONLY when explicitly requested

---

**WAIT FOR INSTRUCTIONS. DO NOT ACT AUTONOMOUSLY.**
