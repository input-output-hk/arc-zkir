---
name: user-mauro
description: Mauro Jaskelioff — works on the ZKIR v2 Agda formal spec; values faithful, postulate-free mechanization.
metadata:
  type: user
---

Mauro Jaskelioff (mauro.jaskelioff@iohk.io) is working on the ZKIR v2 formal specification in
Agda (`src/zkir-v2/`), mechanizing the Halo2 circuit-synthesis faithfulness theorem (P5):
`R src pre s ↔ satisfies (circuit src) (witness-of s pre)`.

Works incrementally and rigorously: keeps every module type-checking at all times, tracks each
postulate as debt with a discharge plan, forbids new postulates / TERMINATING pragmas / holes /
trustMe when discharging an obligation. Prefers concrete-first definitions and structural
recursion. Comments in the code are detailed phase/plan notes — he documents the intended
proof shape before filling it.

**How to apply:** When a stated target turns out to be false or under-specified, report it
precisely with a counterexample rather than fabricating a proof or silently weakening the spec.
He will want to decide on signature changes (e.g. adding a well-formedness hypothesis) himself.
