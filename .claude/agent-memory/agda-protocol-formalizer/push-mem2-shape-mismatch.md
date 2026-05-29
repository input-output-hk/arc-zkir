---
name: push-mem2-shape-mismatch
description: push-mem2 vs iterated push-mem produce propositionally-equal but definitionally-distinct memory shapes; bridging requires explicit associativity lemma + subst.
type: project
---

# push-mem2 vs push-mem ∘ push-mem

Two ways instructions appending two cells are modelled in `Semantics.agda`:

| instruction              | function call               | resulting memory             |
|--------------------------|-----------------------------|------------------------------|
| `div-mod-power-of-two`   | `push-mem (push-mem s x) y` | `(mem ++ x ∷ []) ++ y ∷ []` |
| `persistent-hash`, `hash-to-curve`, `ec-add`, `ec-mul`, `ec-mul-generator` | `push-mem2 s x y` | `mem ++ x ∷ y ∷ []` |

These shapes are propositionally equal (via `++`-associativity) but **not** definitionally equal.

## Symptom

When proving forward faithfulness for a `push-mem2`-using instruction, the goal type
unfolds to `mem ++ (x ∷ y ∷ [])` while the available `lookup-new-fst` /
`lookup-new-snd` helpers expect `(mem ++ x ∷ []) ++ y ∷ []`. Direct construction
fails with `mem ++ x ∷ [] != mem`.

## Fix (used in `CircuitFaithfulness.agda`'s cryptographic cluster)

Add a one-line helper:

```agda
push-mem2-assoc : ∀ (mem : List Fr) x y
  → mem ++ (x ∷ y ∷ []) ≡ (mem ++ (x ∷ [])) ++ (y ∷ [])
push-mem2-assoc []       x y = refl
push-mem2-assoc (z ∷ zs) x y = cong (z ∷_) (push-mem2-assoc zs x y)
```

…then wrap each forward proof's result tuple in
`subst (λ m → satisfies-clauses … (mk-witness m … …)) (sym assoc) (…)`.

Backward proofs are unaffected — their hypothesis already mentions
`(mem ++ x ∷ []) ++ y ∷ []` explicitly (so the caller is responsible for
threading the right shape).

## Why two shapes?

Historical asymmetry: `div-mod-power-of-two` predates the `push-mem2`
abbreviation. Could be reconciled at the source by either
- rewriting `r-div-mod-power-of-two` to use `push-mem2`, or
- inlining `push-mem2 s v₁ v₂ = push-mem (push-mem s v₁) v₂`.

Either change would invalidate other proofs and isn't worth it for one
helper lemma.