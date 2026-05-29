---
name: phase4d-wire-discipline-resolved
description: Phase 4d's wire-discipline blocker is RESOLVED.  `wire-disc` is a fourth producer obligation in `producer-safe`; its soundness chain (`Wire-Trace`, `wire-disc-sound`, `wire-trace-head`) gives the backward dispatcher the per-step `wire-check instr n ≡ true` premise needed to pull pre-state lookups via `lookup-shrink`.  The wire-disc INFRASTRUCTURE described here is current and load-bearing; the D1/D2 status and signature-recovery discussion below are HISTORICAL (D1 and D2 are now fully discharged).
type: project
---

# Phase 4d wire-discipline — RESOLVED

> **UPDATE (post-D2):** The wire-disc obligation + soundness chain (Piece A,
> `lookup-shrink`) remain exactly as described and are used by the finished D1/D2.
> But D1 and D2 are now FULLY DISCHARGED (postulate-free) — only D3
> (`circuit-faithful-bwd`) and the Phase-4e `circuit-faithful` remain.  D1's final
> signature is the **Σ-output / `op-side-data` form** (see `phase4d-D1-partial-progress.md`),
> NOT the awkward explicit-`s'` postulate shown in the "## What's NOT done",
> "## Suggested D1 case skeleton", and "## Recovery from a bad signature" sections
> below — treat those three sections as obsolete.

## What's done this turn

### Piece A — wire-disc obligation

`zkir-v2/Obligations.agda` (lines 95–104, 305–386):

- `_<ᵇ_ : ℕ → ℕ → Bool` (defined as `suc m ≤ᵇ n`).
- `guard-ok? : Maybe Index → ℕ → Bool` — `nothing` is trivially OK; `just g` requires `g < n`.
- `all-lt? : List Index → ℕ → Bool` — every element `< n`.
- `wire-check : Instruction → ℕ → Bool` — per-instruction check, one
  pattern per Instruction constructor.  Enumerates the operand wire
  indices and applies `_<ᵇ_` / `all-lt?` / `guard-ok?`.
- `wire-step instr n`: uses `with wire-check instr n` (NOT
  `if_then_else_` — see "gotcha" below) to return `just (n + Δmem instr)`
  or `nothing`.
- `wire-scan`, `wire-disc src : Bool`, `Wire-Trace`, `Wire-Runs`
  (mirror the O2/O3 trace structure).
- `producer-safe src = O1 src ∧ O2 src ∧ O3 src ∧ wire-disc src`
  (4-way conjunction).

### Piece A — soundness

`zkir-v2/ObligationsSoundness.agda` lines 1607–1629:

- `producer-safe-O{1,2,3,wire-disc}` all updated to the 4-conjunct
  pattern: `with O1 src | O2 src | O3 src | wire-disc src | eq`.

`zkir-v2/CircuitProof.agda` lines 2131–2185 (private section):

- `wire-scan→trace` — mirror of `O2-scan→trace`.
- `wire-bool→trace` — Bool ⇒ ∃-Wire-Trace.
- `wire-disc-sound` — top-level: `producer-safe → ∃-Wire-Trace`.
- `wire-trace-head-aux` + `wire-step-defn` + `wire-trace-head` —
  the per-step extractor that gives `wire-check instr n ≡ true` and
  the residual trace at `n + Δmem instr` from a `Wire-Trace (instr ∷
  is) n final`.

### Piece A — `lookup-shrink`

`zkir-v2/CircuitFaithfulness.agda` lines 320–332 (public):

```agda
lookup-shrink : ∀ (mem suffix : List Fr) i {v}
  → mem-lookup (mem ++ suffix) i ≡ just v
  → suc i ≤ length mem
  → mem-lookup mem i ≡ just v
```

This is the bridge: given operand-bound (from wire-disc) + post-state
lookup (from satisfies-clauses), pull a pre-state lookup.

### D1 signature refinement

D1's postulate signature (CircuitProof.agda lines 2216–2238) now
carries `wire-check i (SynthState.nr-wires st) ≡ true` as a
premise.  Caller (D2) discharges this via `wire-trace-head` against
the threaded `Wire-Trace`.

## What's NOT done

- **D1 body** — the 26-case dispatcher itself.  Each case is ~25
  lines and follows the forward dispatcher template (CircuitProof.agda
  lines 638–...) inverted: take a post-state witness, extract pre-
  state lookups via `lookup-shrink` and the `wire-check`-derived
  bounds, call the corresponding `*-bwd` lemma.
- **D2** — multi-instruction iteration.  Like the forward D2 but
  threads the `Wire-Trace`, `O2-Trace`, `O3-Trace` simultaneously and
  destructures the per-step Σ to get intermediate states.
- **D3** — top-level backward.  Mirror of `circuit-faithful-fwd`.
- **Phase 4e** (not in scope this turn) — replace `circuit-faithful`
  postulate in Properties.agda.

## Key gotcha — `wire-step` must use `with`, not `if`

Initially I wrote `wire-step instr n = if wire-check instr n then ...
else nothing`.  This typechecks but `wire-trace-head` can't extract
the `chk-eq : wire-check instr n ≡ true` from the bool-matched branch
because Agda doesn't reduce the `if` under abstraction.

**Fix**: change `wire-step` to use `with wire-check instr n` /
`... | true = just (n + Δmem instr) | false = nothing`.  This makes
the underlying definition pattern-match the way `with` clauses
expect.

## Suggested D1 case skeleton (for next agent)

The signature is:

```agda
satisfies→R-instr-step
  : ∀ {hc} (pre : ProofPreimage) (s s' : Preprocessed) (i : Instruction)
    (st : SynthState)
  → mem-inv s st
  → pi-inv  hc s st
  → wire-check i (SynthState.nr-wires st) ≡ true
  → satisfies-clauses
      (SynthState.clauses (circuit-instr hc i st))
      (mk-witness (Preprocessed.memory s')
                  (Preprocessed.pis    s')
                  (comm-rand-of pre))
  → R-instr pre s i s'
```

For `add a b` case:

```agda
satisfies→R-instr-step {hc} pre s s' (add a b) st mi pi wc sat = ...
  let mem = Preprocessed.memory s
      -- new clauses for this instruction
      -- from `wc : wire-check (add a b) (nr-wires st) ≡ true`
      -- pattern match to extract (a <ᵇ n) ≡ true and (b <ᵇ n) ≡ true
      -- combined with `mi : nr-wires st ≡ length mem`, this gives
      -- suc a ≤ length mem and suc b ≤ length mem.
      ...
      -- need to extract suffix from `mem-extends-R-instr`-style fact
      -- on s' — but the postulate doesn't give us that.  Need to
      -- either:
      --   (a) refine the signature to take Σ s' (suf such that
      --       memory s' ≡ memory s ++ suf)
      --   (b) extract the post-state structure from the satisfies-
      --       clauses witness (peek at clause-copy's output index =
      --       length mem, then mem s' ≡ mem ++ suf for the
      --       one-cell suf at length mem).
      ...
  in add-bwd la lb sat-shifted
```

The cleanest path is option (a): refine D1 to also take a
`mem-suffix-extends : ∃ suf → memory s' ≡ memory s ++ suf` premise.
D2 discharges this directly from `mem-extends-R-instr` if it had an
R-instr — but in the backward direction it doesn't.

Alternative: the existential `s'` form.  Each `*-bwd` lemma already
returns a *concrete* post-state (e.g. `push-mem s v`), so D1 could
have shape:

```agda
satisfies→R-instr-step
  : ... → satisfies-clauses ... (mk-witness ??? ...)
  → ∃-syntax λ s' →
      satisfies-clauses (...) (mk-witness (memory s') (pis s') rand)
      × R-instr pre s i s'
```

— but then the input witness's memory is also `???`.  Resolution:
take a witness *over s* (pre-state) of the cumulative-up-to-i clauses,
and have D1 produce both the post-state and the witness over the post-
state.  D2 chains these.  This is the dual of the forward direction's
contract.

## Recovery from a bad signature

The current postulate signature (post-state `s'` explicit) is awkward
for the backward proof because the dispatcher needs to *produce* `s'`,
not consume it.  When filling D1, the next agent should refine to one
of:
  (1) Σ-form output, witness over `s` input (cumulative-up-to-i style)
  (2) Add an explicit `mem-extends : ∃ suf → memory s' ≡ memory s ++ suf`
      premise.

## Trust base unchanged

Zero new axioms.  Final line counts:
- Obligations.agda 466 (was 376; +90 for wire-disc)
- ObligationsSoundness.agda 1659 (was 1663; −4 due to cleaner extractor)
- CircuitProof.agda 2297 (was 2210; +87 for wire-disc-sound infrastructure)
- CircuitFaithfulness.agda 1984 (was 1970; +14 for `lookup-shrink`)

All 8 modules typecheck cleanly.
