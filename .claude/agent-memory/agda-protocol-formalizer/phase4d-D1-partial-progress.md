---
name: phase4d-D1-partial-progress
description: Phase 4d D1 (per-step backward dispatcher) is fully mechanised — all 26 instruction cases discharged concretely, with NO postulated fallback (deleted once coverage was complete).  `op-side-data` is shape-constraining for every instruction.
type: project
---

# Phase 4d D1 — 26 / 26 cases discharged

> **UPDATE (post-D2):** The defensive postulate `satisfies→R-instr-step-postulated`
> and its unreachable fallback clause have been **deleted** — the 26 concrete
> clauses are exhaustive, so D1 is total and postulate-free.  Also `op-side-data`
> is now shape-CONSTRAINING for *all 26* instructions (each clause is a `Σ`/`×`
> carrying the suffix-shape equality, e.g. `op-side-data (add _ _) _ _ ms ps =
> Σ Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])`); there is no `⊤` catch-all.  The
> "`⊤` for 22 cases" / "defensive hatch postulate" notes below are HISTORICAL.

## What's done

### Refined D1 signature  (extended in batch 5 with op-side-data)

`zkir-v2/CircuitProof.agda`:

```agda
satisfies→R-instr-step
  : ∀ {hc} (pre : ProofPreimage) (s : Preprocessed) (i : Instruction)
    (st : SynthState) (mem-suf : List Fr) (pis-suf : List Fr)
  → mem-inv s st
  → pi-inv  hc s st
  → wire-check i (SynthState.nr-wires st) ≡ true
  → ∀ {bk : IndexSet} {bm : PartialMap}
  → O2-Inv (SynthState.nr-wires st , bk) s
  → O3-Inv (SynthState.nr-wires st , bm) s
  → O2-check i bk ≡ just bk
  → O3-check i bm ≡ true
  → op-side-data i pre s mem-suf pis-suf      -- NEW (batch 5)
  → satisfies-clauses
      (SynthState.clauses (circuit-instr hc i st))
      (mk-witness (Preprocessed.memory s ++ mem-suf)
                  (Preprocessed.pis    s ++ pis-suf)
                  (comm-rand-of pre))
  → Σ-syntax Preprocessed (λ s' →
        (Preprocessed.memory s' ≡ Preprocessed.memory s ++ mem-suf)
      × (Preprocessed.pis    s' ≡ Preprocessed.pis    s ++ pis-suf)
      × R-instr pre s i s')
```

### Per-instruction operational side data ADT  (new, batch 5)

```agda
op-side-data : Instruction → ProofPreimage → Preprocessed
             → (mem-suf pis-suf : List Fr) → Set
op-side-data (output v)        _   s [] [] =
  Σ-syntax Fr (λ val → mem-lookup (Preprocessed.memory s) v ≡ just val)
op-side-data (pi-skip g count) pre s [] [] =
  Σ-syntax Bool (λ active →
      eval-guard (Preprocessed.memory s) g ≡ just active
    × (if active
       then (transcript-prefix-match ≡ true)
       else ⊤))
op-side-data (public-input g)  pre s (w ∷ []) [] =
  Σ-syntax Bool (λ active →
      eval-guard (Preprocessed.memory s) g ≡ just active
    × (if active
       then Σ-syntax Preprocessed (λ s₁ → consume-pub-out s ≡ just (w , s₁))
       else (w ≡ 0ᶠ)))
op-side-data (private-input g) pre s (w ∷ []) [] = ... symmetric ...
op-side-data _ _ _ _ _ = ⊤
```

For the 22 cases discharged before batch 5, `op-side-data` is `⊤`; the dispatcher patterns receive it as `_`.  For the 4 batch-5 cases, the side-data is destructured at the pattern level.

Crucially, the side-data is parameterised by `mem-suf` so that the witness's memory cell `w` (in public/private-input) is unified with the consumed transcript value (active case) or with `0ᶠ` (inactive case).  This eliminates the otherwise-needed "agreement" equation between witness and operational state.

### Helpers in place

- `<ᵇ-to-≤`, `≤ᵇ-to-≤`, `∧-≡-true-split`, `push-mem2-assoc`, `o2-check-mem?` (private, CircuitProof.agda).
- `satisfies-clauses-split` (CircuitProof.agda).
- `lookup-shrink`, `mem-lookups-shrink` (public, CircuitFaithfulness.agda).
- `_≡ᶠ-list?_` is now **public** in `Semantics.agda` (was private; un-private justified by D1's reference inside `op-side-data` for the pi-skip active branch — same pattern as the prior `bits-lt` / `from-bool` exposures).

### Batch 5 cases — 4 side-data instructions discharged

**`output v`** — Δmem = 0, pis unchanged.  Emits no clauses (the wire index goes to `output-wires` for the comm-commitment).  Side data carries `(val , mem-lookup mem v ≡ just val)`.  Dispatcher calls `r-output` directly; post-state is `record s { outputs = outputs s ++ [val] }`.

**`pi-skip g count`** — Δmem = 0, pis unchanged.  Emits no clauses.  Side-data carries `(active , ev-guard , prefix-match)`.  Two sub-cases:
- `active = true`: post-state `record s { pi-skips = pi-skips s ++ [nothing] }`; fire `r-pi-skip-active` with the prefix-match equation.
- `active = false`: post-state `record s { pi-skips = pi-skips s ++ [just count], pub-in-idx = pub-in-idx s ∸ count }`; fire `r-pi-skip-inactive`.

**`public-input g`** — Δmem = 1, pis unchanged.  Either no clauses (`g = nothing`) or one `clause-guard-disj` (`g = just _`).  Side-data carries `(active , ev-guard , active-evidence)`.  Two sub-cases:
- `active = true`: side-data gives `Σ Preprocessed (λ s₁ → consume-pub-out s ≡ just (w , s₁))`.  Post-state `record s₁ { memory = memory s₁ ++ [w] }` (= `push-mem s₁ w`).  `mem-eq` uses local lemma `consume-pub-out-mem-eq` (consume-pub-out preserves memory).
- `active = false`: side-data gives `w ≡ 0ᶠ`.  Post-state `push-mem s w`; fire `r-public-input-inactive` (which gives R-instr to `push-mem s 0ᶠ`) and `subst` with `w ≡ 0ᶠ`.

**`private-input g`** — symmetric to `public-input` using `consume-priv` and `r-private-input-{active,inactive}`.

### All 26 cases discharged concretely

**Δmem=0 / pis unchanged**: `constrain-eq`, `constrain-bits`, `constrain-to-boolean`, `assert`, **`output`**, **`pi-skip`**.

**Δmem=1 / pis unchanged**: `add`, `mul`, `neg`, `copy`, `load-imm`, `test-eq`, `transient-hash`, `cond-select`, `not`, `less-than`, `reconstitute-field`, **`public-input`**, **`private-input`**.

**Δmem=2 / pis unchanged**: `ec-add`, `ec-mul`, `ec-mul-generator`, `hash-to-curve`, `persistent-hash`, `div-mod-power-of-two`.

**Δmem=0 / pis-suf = wv ∷ []**: `declare-pub-input`.

## Postulate accounting

**0 internal postulates.**  (The former `satisfies→R-instr-step-postulated`
defensive hatch was deleted — the 26 explicit clauses are exhaustive, confirmed
by Agda's coverage checker.)

**Trust-base axioms** (unchanged since batch 4):
- 2 batch-4 axioms (`fits-in-mono`, `bits-in-field-from-strict-bound`) in `CircuitFaithfulness.agda`.
- No new axioms in batch 5.

## File state (post-batch-5)

- `CircuitProof.agda`: **3524 lines** (was 3347; +177 for the `op-side-data` ADT, 4 new dispatcher cases, and updated signature/22-case patterns).
- `CircuitFaithfulness.agda`: 2059 lines (unchanged).
- `ObligationsSoundness.agda`: 1659 lines (unchanged).
- `Semantics.agda`: 633 lines (was ~628; +5 for un-privating `_≡ᶠ-list?_` with explanatory comment).
- All 8 modules typecheck cleanly.

## Notable subtleties (batch 5)

- **`_≡ᶠ-list?_` exposed**: previously private in `Semantics.agda`.  Un-privated because D1's `op-side-data` for `pi-skip` references it.  Same justification pattern as the existing `bits-lt` / `from-bool` exposures.  Documented inline.

- **Side-data depends on suffixes**: `op-side-data i pre s mem-suf pis-suf` lets `public-input`/`private-input` constrain the witness's allocated cell `w` (sole element of `mem-suf`) to equal either the consumed transcript value or `0ᶠ`.  Without this, the dispatcher would need to either (a) prove `w ≡ v` from circuit-level reasoning (impossible — `public-input nothing` emits no clauses!) or (b) carry a separate agreement equation as a second parameter.  Threading it through `mem-suf` is cleaner.

- **`push-mem`, `push-mem2` are public** in `Semantics.agda`, but `push-pi`, `push-skip`, `push-output` remain private.  All four new cases sidestep this by constructing the post-state directly via `record s { ... }`, which Agda accepts as definitionally equal to the corresponding `push-*` form (so `r-pi-skip-active`, `r-output`, etc. type-check).

- **`consume-pub-out` / `consume-priv` preserve memory & pis**: local `where`-block helpers (`consume-pub-out-mem-eq`, etc.) prove these by `with`-matching on the relevant `*-rem` field (the lemmas are 2-line case splits).

- **Inactive `r-public-input` / `r-private-input`**: the constructor produces R-instr to `push-mem s 0ᶠ`, but the witness commits to `push-mem s w`.  We bridge via `w ≡ 0ᶠ` (from side data) and `subst`.

- **`pi-skip` post-state for inactive branch**: `record s { pi-skips = ... ; pub-in-idx = pub-in-idx s ∸ count }` matches `push-skip (record s { pub-in-idx = ... }) (just count)` by inlining `push-skip`'s definition.

## Suggested next steps

1. **D2 mechanization** — D1's signature is now stable and fully discharged.  Next major step: mechanize `satisfies-clauses→R-instrs` that iterates D1 per instruction, threading:
   - `mem-inv` / `pi-inv` (already proven preserved per step via existing helpers),
   - `O2-Trace` / `O3-Trace` via `o2-preserve` / `o3-preserve` and `o2-inv-mid` / `o3-inv-mid`,
   - `op-side-data i pre s mem-suf pis-suf` per instruction — D2 will need to extract this from the operational rule's premises (which is precisely what D2's induction gives: an `R-instr` for each step encodes exactly the side-data fields).

   Note: D2 will likely walk the instructions in source order, generating side-data witnesses from the corresponding `R-instr` constructor's premises.  Side data and `R-instr` are isomorphic for the 4 side-data instructions.

2. **D3** (the top-level circuit-faithful theorem) wires D2 to `Properties.agda`'s postulate.

## Trust base

- No additions in batch 5.
- The two batch-4 axioms (`fits-in-mono`, `bits-in-field-from-strict-bound`) remain the sole new additions during Phase 4d D1.  Both are siblings of the existing bit-decomposition family in `CircuitFaithfulness.agda` and are flagged inline.