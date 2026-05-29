---
name: phase4b-forward-discharged
description: Phase 4b's forward direction is now fully discharged in CircuitProof.agda. The three remaining postulates (output-wires-coincide, inputs-lookup-init, circuit-faithful-fwd) have concrete proofs, with no new trust-base axioms.
type: project
---

# Phase 4b forward direction: discharged

All three forward postulates in `CircuitProof.agda` now have concrete
bodies.  No new trust-base axioms were introduced.

## `output-wires-coincide` — discharged via generalized IH

The signature was extended with an extra hypothesis (`outputs s₀ ≡ []`),
which holds at init-state.  A general lemma `output-wires-coincide-gen`
threads the IH `mem-lookups (memory s) (output-wires st) ≡ just (outputs s)`
along the trace.  The dispatcher case-splits on the R-instr constructor:

- 30 non-output cases: lift via `mem-lookups-extends` (memory extends, output-wires
  and outputs unchanged).  Common helper `output-wires-non-output-step` takes
  the memory extension plus an `outputs s₁ ≡ outputs s` witness (refl for most
  cases; small lemma for consume-pub-out/consume-priv that record-extends
  preserve `outputs`).
- 1 output case: emit `mem-lookups-snoc` to append `var → v`.

Required two new private list helpers:

- `mem-lookups-snoc` — distributivity of `mem-lookups` over snoc.
- `mem-lookups-nat-range : ∀ xs → mem-lookups xs (nat-range (length xs)) ≡ just xs`.
  Proved via `mem-lookups-nat-range-len` by induction on length, using
  `snoc-of-length` to decompose `xs` as `xs' ⊕ y` at each step.

## `inputs-lookup-init` — discharged

Composes `mem-lookups-nat-range` + `init-state-memory'` (replicated from
Properties.agda's `private` block) + `init-state-inputs-length` (new
helper extracting WF1 from `init-state ≡ just s₀`).  WF1 is enforced
by init-state's `length (inputs pre) ≡ᵇ num-inputs src` check; we
convert `≡ᵇ ≡ true` to `≡` via stdlib's `Data.Nat.Properties.≡ᵇ⇒≡`.

## `circuit-faithful-fwd` — discharged

The proof dispatches on `do-comm src` (boolean cases via a small `bool-cases`
helper) and `comm-commitment pre` (a small `maybe-cases` helper),
delegating to:

- `circuit-faithful-fwd-false` (hc=false branch).
- `circuit-faithful-fwd-true` (hc=true + comm-commitment=just (c, r) branch).
- A contradiction at hc=true + comm-commitment=nothing (`comm-ok ≡ false`,
  contradicts the R-side hypothesis).

The hc=true branch invokes `pi-lookup-mono-R-instrs` (a new helper
analogous to `mem-lookups-mono-R-instrs`) to lift `pi-lookup (pis s₀) 1
≡ just c` (from the initial `pis = [binding-input, c]`) along the trace.
The `c ≡ transient-commit ...` bridge uses `≡ᶠ?-true` (already postulated
in CircuitFaithfulness).

Both helpers thread through a `circuit-eq : circuit src ≡ <expanded form>`
to bridge between the abstract `circuit src` (in the goal) and the
hc-specific form (where `if hc then ...` has reduced).

## Trust-base impact

Zero new postulates / axioms.  The existing trust base (`≡ᶠ?-true`,
field axioms, EC axioms, hash function postulates) is unchanged.

## Remaining postulates (Phase 4d / 4e)

- `satisfies→R-instr-step` (backward per-step dispatcher).
- `satisfies-clauses→R-instrs` (backward iteration).
- `circuit-faithful-bwd` (top-level backward).
- `circuit-faithful` (the iff that replaces Properties.agda's postulate).

Phase 4d will need to discharge these.  The same structural amendments
(Maybe-shape weakening; WF1 enforcement) should make the backward
direction tractable.