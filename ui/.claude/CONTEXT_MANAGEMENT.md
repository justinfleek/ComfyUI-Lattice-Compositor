# Context Window Management

## THE RULE
**Maximum 2 compactions per session. Then checkpoint and restart.**

## Warning Signs
1. Claude repeats a mistake it was corrected on
2. Claude asks about something already discussed
3. Claude forgets rules from earlier
4. "[conversation was compacted]" appears twice

## Checkpoint Process
1. Update: CURRENT_FOCUS.md, SESSION_LOG.md
2. Commit: `git add -A && git commit -m "checkpoint: [description]"`
3. Generate: NEXT_SESSION_PROMPT
4. Start fresh conversation

## Session Length Guide
| Task | Messages | Risk |
|------|----------|------|
| Simple fix | 10-20 | Low |
| Single file | 20-40 | Medium |
| Multi-file | 40-60 | High |
| Codebase audit | 60+ | CHECKPOINT |
