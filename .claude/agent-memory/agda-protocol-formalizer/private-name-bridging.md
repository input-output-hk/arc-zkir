---
name: private-name-bridging
description: When `Circuit` and `Semantics` independently define the same helper (e.g. `bits-lt`), Agda treats them as distinct even if syntactically identical. Bridging in faithfulness proofs requires making the helper public (or postulating an equality).
type: project
---

# Private-name bridging in CircuitFaithfulness

## Problem

`Semantics.agda` originally declared `bits-lt` (used in `r-less-than`'s output expression) in a `private` block.  `Circuit.agda` re-declared `bits-lt` locally because the private one was inaccessible.  In `CircuitFaithfulness`, proving `less-than-fwd` requires bridging:

- the operational rule outputs `from-bool (Semantics.bits-lt ...)`,
- the clause uses `from-bool (Circuit.bits-lt ...)`.

Agda does NOT see the two as definitionally equal even when defined by structurally identical equations.  Trying to construct the existential witness or unify it against the post-state shape will fail with mismatches like

```
Circuit.cmp ... != Semantics.go ...
```

## Resolution

Move the shared helper out of `private` in `Semantics.agda` and re-export it explicitly in `Circuit.agda`'s `Semantics` `using`-list.  Then delete the redundant local definition in `Circuit.agda`.

The change is non-breaking — `private` simply hides the name from importers; the name was already in use internally.

## When to expect this

Any time a proof needs to relate an operational rule's output (which closes over `Semantics`'s helpers) to a clause shape (which uses `Circuit`'s helpers) of the same name.  Candidates among current `private` names in `Semantics.agda`:

- `all-false`  (used inside `fits-in`)
- `_≡ᶠ-list?_` (used inside `r-pi-skip-active`)
- `is-empty`

If a faithfulness proof for `pi-skip` materialises, expect the same pattern with `_≡ᶠ-list?_`.

## Lesson

When declaring helpers in `Semantics.agda` whose results appear in `R-instr` constructors, keep them public from the start — `Circuit` and `CircuitFaithfulness` will both need to refer to them by name to bridge.