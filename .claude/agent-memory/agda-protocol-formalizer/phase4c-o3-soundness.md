---
name: phase4c-o3-soundness
description: Phase 4c's O3 soundness (`o3-preserve`, `o3-preserve*`, `O3-sound`, `o3-known-fits`) discharged with zero new postulates.  Structure mirrors O2 side.
type: project
---

# Phase 4c O3 soundness — discharged

`zkir-v2/ObligationsSoundness.agda` now contains the full O3 soundness
chain alongside O2's:

1. `O3-Inv` record (idx-sync + bm-bound + bits-known fields)
2. `o3-inv-init` — initial state satisfies invariant
3. ~15 frame lemmas (`o3-frame-no-grow`, `o3-frame-push-mem`,
   `o3-frame-push-mem-2`, `o3-frame-push-mem-push-mem`,
   `o3-frame-no-grow-insert-v`, `o3-frame-push-mem-2-insert-2`,
   `o3-frame-push-mem-copy`)
4. `o3-preserve` — 26-case dispatcher on `R-instr`
5. `o3-preserve*` — multi-step preservation indexed by `O3-Trace`
6. `O3-sound` — whole-program soundness
7. `o3-known-fits` — integration extractor for Phase 4d (mirrors
   `o2-known-is-bit`)
8. `o3-inv-mid` — mid-trace invariant lift
9. `producer-safe-O{1,2,3}` — extract Bool conjuncts
10. `O2-bool→Runs` / `O3-bool→Runs` — Bool → witness conversion via
    `O{2,3}-scan→trace` helpers (eta-expand the `with O{2,3}-scan ...
    | just final` pattern from the Bool definition).

## Key pitfall — `subst (λ k → O3-Inv (k , _) _)` causes meta hell

The natural shape

```
subst (λ k → O3-Inv (k , _) _) (sym (+-2-r i)) (o3-frame-push-mem-2 inv)
```

leaves `_` metas in the lambda body that Agda cannot resolve, because
the `bm` and `s'` aren't constrained backwards from the result type
(they appear inside an opaque record).  Symptom: dozens of
`UnsolvedConstraints` of the form `_s_4454 (k = (suc (suc i))) =
push-mem2 s x y`.

**Fix** — define an `o3-inv-coerce-idx : i ≡ i' → O3-Inv (i, bm) s →
O3-Inv (i', bm) s` that does *not* mention `bm`/`s` as variables in a
lambda.  All 26 cases of `o3-preserve` then use the coerce helper
instead of `subst (λ k → O3-Inv (k , _) _) ...`.  Mirror of O2's
`inv-coerce-idx` (line 648).

## Key pitfall — `O3-check`-guarded cases need a `false | ()` arm

For `less-than` and `reconstitute-field`, `O3-step` is

```
O3-step instr (i , bm) = if O3-check instr bm then just ... else nothing
```

So when we case-split with `with O3-check instr bm | step-eq`, the
`false | refl` arm must be absurd-matched: `step-eq` would have type
`nothing ≡ just acc'`, hence `... | false | ()`.  Without the absurd
arm Agda reports `CoverageIssue`.

For all other instructions where `O3-check _ _ = true` definitionally,
drop the `with O3-check` entirely and match `step-eq = refl` directly.

## producer-safe ↦ Boolean extraction

`producer-safe src = O1 src ∧ O2 src ∧ O3 src`.  Direct pattern
matching on the ∧-conjunction fails because `O1`/`O2`/`O3` are
`with`-defined and don't reduce.  Workaround: `with O1 src | O2 src |
O3 src | eq` and match the all-`true` branch with `refl`.

## Scan → Trace

To recover an `O{2,3}-Runs src` from `O{2,3} src ≡ true`, walk the
list:

```
O3-scan→trace : ∀ is acc {final}
  → O3-scan is acc ≡ just final
  → O3-Trace is acc final
O3-scan→trace []       acc refl = o3-done
O3-scan→trace (i ∷ is) acc eq
  with O3-step i acc in step-eq
... | just acc' = o3-step step-eq (O3-scan→trace is acc' eq)
```

The `with ... in step-eq` binds the `O3-step` result for the
`o3-step` constructor's first argument.

## Integration shape for Phase 4d

`o3-known-fits` is the per-instruction obligation extractor:

```
o3-known-fits : ∀ {i bm s a n v}
  → O3-Inv (i , bm) s
  → lookupᵐ a bm ≡ just n
  → mem-lookup (Preprocessed.memory s) a ≡ just v
  → fits-in v n ≡ true
```

To use it in a backward direction lemma in CircuitFaithfulness (e.g.
`reconstitute-field-bwd`, `less-than-bwd`):

1. Thread an O3-Trace prefix alongside R-instrs via `o3-inv-mid`.
2. At the obligation-bearing instruction, the `O3-check` premise
   gives `lookupᵐ a bm ≡ just n`.
3. Compose with the mem-lookup proof (from the R-instr's
   constructor) to obtain `fits-in v n ≡ true`.

No new trust-base axioms were needed.  Final
`ObligationsSoundness.agda` is 1663 lines, all 8 modules typecheck.