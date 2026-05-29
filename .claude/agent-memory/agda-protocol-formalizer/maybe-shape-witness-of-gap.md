---
name: maybe-shape-witness-of-gap
description: A genuine soundness gap discovered in Phase 4b — `Maybe-shape false (just _) = ⊥` is unprovable when the operational `init-state` accepts a non-comm circuit with a spurious commitment.
type: project
---

# Witness-of comm-rand vs Maybe-shape: a structural gap

## Discovery

When attempting to discharge `circuit-faithful-fwd` for the case `hc = false`:

- `init-state src pre` with `do-comm src ≡ false` SUCCEEDS regardless of whether `comm-commitment pre` is `nothing` or `just (c, r)`.  (See `Semantics.agda`'s `init-state`.)
- `witness-of` computes `comm-rand-of pre`, which IS `just r` when `comm-commitment pre ≡ just (c, r)`, irrespective of `do-comm`.
- The circuit's `satisfies` requires `Maybe-shape false (Witness.comm-rand w)`, which is:
  - `⊤` when `comm-rand w ≡ nothing`,
  - `⊥` when `comm-rand w ≡ just _`.

Therefore: when `do-comm src ≡ false` and `comm-commitment pre ≡ just _`,
`satisfies (circuit src) (witness-of s pre)` is FALSE.  But `R src pre s`
can still hold (the relational rules + `comm-ok src pre s` care only about
the matched case).

## Same hits BACKWARD

`circuit-faithful-bwd` symmetrically: from a satisfying assignment with
shape `false × nothing`, recovering a preimage with `comm-commitment ≡ nothing`
is direct — but the ↔ then forces `comm-commitment ≡ nothing` in *every* preimage,
contradicting the `R`-side's permissiveness.

## Fix options (spec-level)

1. **Gate `witness-of`'s comm-rand on `do-comm src`:**
   ```
   witness-of src s pre =
     mk-witness (memory s) (pis s)
       (if do-comm src then comm-rand-of pre else nothing)
   ```
   Simplest fix.  Breaks the current `witness-of`'s source-independence
   (note in `CircuitProof.agda` says it doesn't depend on src — that's now wrong).

2. **Strengthen `R src pre s`:** require `do-comm src ≡ true ⇔ ∃ c r → comm-commitment pre ≡ just (c , r)`.
   More semantically faithful (the preimage shape is part of the protocol
   state) but adds a non-obvious precondition.

3. **Strengthen `init-state`:** fail when `do-comm = false ∧ comm-commitment ≡ just _`.
   Less compatible with the Rust VM (which silently ignores spurious commitments
   when do-comm is unset).

Option 1 is cleanest for the formalization; option 2 is most faithful to
the operational semantics' intent.

## Sister issue: `init-mem-length`

`mem-inv s₀ st₀` requires `num-inputs src ≡ length (memory s₀)`.  `init-state-memory`
says `memory s₀ ≡ inputs pre`, so this reduces to `num-inputs src ≡ length (inputs pre)`.

`init-state` does not enforce this length check.  Fix: either enforce in
`init-state`, or treat as a precondition of `R src pre s`.

## Status (end Phase 4b)

`circuit-faithful-fwd` remains a postulate, flagged with TODO referencing
this memory.  Phase 4d will hit the same wall; resolving these issues
before continuing is recommended.

## RESOLVED (Phase 4b follow-up)

Both gaps were resolved by spec-level amendments:

- **Maybe-shape weakened.**  `Circuit.agda` now defines
  `Maybe-shape false _ = ⊤` (was: `⊥` when `just _`).  Semantically
  fine because the comm-commitment clause is the only consumer of
  comm-rand and isn't emitted when `has-comm = false`.

- **WF1 enforced in init-state.**  `Semantics.agda`'s `init-state` now
  returns `nothing` when `length (inputs pre) ≢ num-inputs src`.

With both fixes, `circuit-faithful-fwd` has a concrete proof (no
postulate, no new axioms).  See `phase4b-forward-discharged.md`.