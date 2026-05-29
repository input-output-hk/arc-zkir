---
name: phase4d-D2-cons-discharged
description: Phase 4d's list-level backward direction D2 (`satisfies-clauses→R-instrs`, incl. the former `satisfies-clauses→R-instrs-cons` postulate) is FULLY discharged in CircuitProof.agda with zero new postulates. Records the proof structure, the two added D2 preconditions, the new helper lemmas, and the circular-let / pair-η / with|eq pitfalls hit along the way.
metadata:
  type: project
---

# Phase 4d D2 cons-case — DISCHARGED (no new postulates)

`satisfies-clauses→R-instrs` in `zkir-v2/CircuitProof.agda` is now a real
inductive definition (nil + cons). The old `satisfies-clauses→R-instrs-cons`
postulate is deleted. Remaining P5 postulates: only **D3**
`circuit-faithful-bwd` and the Phase-4e `circuit-faithful` (both pre-existing).

## Two preconditions added to D2 (trivial at the top-level call site)
After `pi-inv`, D2 now takes:
- `clauses-mem-fit (clauses st₀) (nr-wires st₀) ≡ true`
- `clauses-pis-fit (clauses st₀) (length (pis s₀)) ≡ true`
Both are `refl` when `st₀` is the initial synth state (`clauses ≡ []`), so
`circuit-faithful-bwd` (the sole caller, still a postulate) discharges them
for free. They are re-established at each recursive step from
`clauses-st-fit-invariant` (mem) and `clauses-pis-fit-instr`+`-mono`+`-++` (pis).

## New helper lemmas (all in a `private` block just before D2)
- `osd-mem-len` / `osd-pis-len` : 26-case extractors giving
  `length mem-step ≡ Δmem i` / `length pis-step ≡ Δpis-of i` from the
  per-step `op-side-data` payload (match `i`, then `sd` with embedded
  equalities as `refl`). Feed `mem-inv-next`/`pi-inv-next`/`clauses-pis-fit-instr`.
- `clause-pis-fit-mono` / `clauses-pis-fit-mono` : pis-fit is monotone in the
  length bound (only `clause-pi-from-wire` and `clause-comm-commitment` are
  non-trivial; uses an inline `<ᵇ-≤-trans` via `Data.Nat.Properties.≤-trans`).
- `clauses-pis-fit-++` : list-append distributes pis-fit.
- `len-≤-++`, `len-++` : `length xs ≤ length (xs ++ ys)` and the `+` form.
- `o2-step-fst` / `o3-step-fst` / `wire-step-fst` : the per-step accumulator's
  first (nat) component bumps by `Δmem i`. **Must use `with O2-check i bk | eq`
  (joint with on the equation), not `with O2-check i bk` then `just-injective eq`**
  — the latter fails with UnequalTerms because `O2-step`/`O3-step`/`wire-step`
  are themselves `with`/`if` on the check and don't reduce under a bare `with`.

## Cons-case proof shape (the 5 steps)
1. Pattern-match the three traces by constructor: `o2-step o2se o2-tail`,
   `o3-step o3se o3-tail`, `wire-cons wse w-tail`. Match `osd` as
   `osd-cons {mem-step}{pis-step}{mem-tail}{pis-tail} sd osd-tail`; this
   refines `mem-suf := mem-step ++ mem-tail`, `pis-suf := pis-step ++ pis-tail`
   (so the D2 mem-suf/pis-suf args become `._`).
2. Build the head clause-fits **stated at `mem₀ ++ mem-step` / `pis₀ ++ pis-step`,
   NOT at `memory s₁` / `pis s₁`** — this is the key to avoiding a circular
   `let`. (`s₁`'s fields are only known *after* D1 runs, but D1 needs the
   shrunk witness, which needs the fit.) mem-fit via
   `clauses-st-fit-invariant st₀ (i ∷ []) fit-mem (wire-cons wse wire-done)`
   then subst `len-mem-eq : length (mem₀ ++ mem-step) ≡ n₁`. pis-fit via
   `clauses-after-instr-eq` + `clauses-pis-fit-++`.
   Then shrink: `satisfies-clauses-mem-shrink` (drop `mem-tail`) and
   `satisfies-clauses-pis-shrink` (drop `pis-tail`). To split off the tail
   clauses first, use `clauses-after-instrs-extends is' st₁` to get the
   explicit `tail` and `subst` `sat`'s clause list to `clauses st₁ ++ tail`
   before `satisfies-clauses-split` (Agda can't infer the `ys`).
3. Call D1 `satisfies→R-instr-step` on the shrunk witness → `s₁`, `mem-eq₁`,
   `pis-eq₁`, `r-head`.
4. `mem-inv-next`/`pi-inv-next` → post-state invariants. Advance O2/O3 via
   `o2-preserve`/`o3-preserve` (give `O2-Inv acc' s₁`). Re-index acc' from
   `(n₀+Δmem i , bk')` to `(n₁ , bk')` using **pair η** (`cong (_, proj₂ acc')
   (trans (o2-step-fst …) (sym (nr-wires-step …)))` — `×` has definitional η so
   `acc' ≡ (proj₁ acc' , proj₂ acc')` is just the substitution target). subst
   the residual traces likewise. Reassociate `sat` via `++-assoc` to feed the
   recursion the witness over `memory s₁ ++ mem-tail` / `pis s₁ ++ pis-tail`.
5. `r-step r-head r-tail`; chain mem/pis equations through `++-assoc`.

## Gotchas that cost iterations
- **Circular `let`**: D1's `s₁` cannot appear in the fit lemmas used to build
  D1's own input witness. State fits at the `mem₀++mem-step` form instead.
- **`subst₂` orientation**: for `sat-rec`, the equation must go
  `(mem₀ ++ (mem-step ++ mem-tail)) ≡ (memory s₁ ++ mem-tail)`, i.e.
  `sym (trans (cong (_++ mem-tail) mem-eq₁) (++-assoc mem₀ mem-step mem-tail))`.
  Note `sat`'s memory is RIGHT-associated (`mem₀ ++ (mem-step ++ mem-tail)`).
- `agda -W error` falsely fails here only because it tries to recompile the
  read-only nix-store stdlib; plain `agda CircuitProof.agda` is clean (no
  warnings, empty output on re-touch, exit 0).
