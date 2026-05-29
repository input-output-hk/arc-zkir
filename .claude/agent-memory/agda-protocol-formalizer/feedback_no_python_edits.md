---
name: feedback-no-python-edits
description: Never use python (or any script) to create/modify source files; Edit/Write tools only.
metadata:
  type: feedback
---

Never use python — no `python`/`python3`, no heredocs piping into files, no scripts — to
create or modify ANY file. Use the Edit / Write tools exclusively for all source edits.

**Why:** firm user requirement stated 2026-05-29 ("HARD METHOD CONSTRAINT … NO PYTHON FOR
EDITS").

**How to apply:** Bash is fine for read-only work — `agda` (typecheck), `grep`, `sed -n`
(viewing only), `ls`, `find`, `rm -rf _build` (clean builds). But any mutation of a `.agda`
/ `.md` / config file goes through Edit or Write. When a multi-occurrence mechanical change is
needed, use `Edit` with `replace_all: true` rather than reaching for a script.
