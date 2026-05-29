---
name: guarded-input-backward-split
description: Why guarded public/private input backward lemmas are split into two (active / inactive) rather than one clause-driven case-split.
type: project
---

# Guarded-input backward direction: two lemmas, not one

`public-input (just g)` and `private-input (just g)` each have *two* operational rules: active (guard true ⇒ consume from transcript) and inactive (guard false ⇒ output = 0ᶠ). They each emit *one* clause: `clause-guard-disj out g`, satisfied by `(out ≡ 0ᶠ) ∨ (g ≡ 1ᶠ)`.

The two operational rules and the two disjuncts *almost* line up, but not at the level the backward lemma operates:

- The disjunct in the clause is part of the **clause witness** — chosen by the prover.
- Which operational rule fires is determined by the **`consume-pub-out` / guard shape** of the prior state — that's source-side, not witness-side.

So you can have witness `inj₂ gv≡1ᶠ` (proving the guard is 1) but the operational state's `consume-pub-out` returns nothing — the clause is satisfied but the active rule cannot fire. Phase 4's program-level induction will rule that out via well-formedness/producer-safety, but at the per-instruction level the clause witness does NOT determine the operational rule.

## Consequence for the API

We expose two backward lemmas, parameterized on the operational pre-state's shape:

```agda
public-input-just-bwd-inactive
  : eval-guard mem (just g) ≡ just false
  → R-instr pre s (public-input (just g)) (push-mem s 0ᶠ)

public-input-just-bwd-active
  : eval-guard mem (just g) ≡ just true
  → consume-pub-out s ≡ just (v , s₁)
  → R-instr pre s (public-input (just g)) (push-mem s₁ v)
```

These are *trivial* given the operational rules already cover the case-split. The reason we even ship them: they document the right contract for Phase 4 to invoke, and they don't pretend the clause itself drives the disambiguation.

## When you *would* want a clause-driven backward

If we had no transcript / no operational state and only the clause witness, then yes — we'd case-split on `inj₁ | inj₂` and produce different post-states. But that's the situation Phase 4 has *after* applying well-formedness, not the situation at the per-instruction level. Keep the backward lemmas thin.