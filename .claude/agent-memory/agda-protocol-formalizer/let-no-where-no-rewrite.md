---
name: let-no-where-no-rewrite
description: `let`-bindings in Agda cannot contain `where` clauses or `rewrite`; both must be hoisted out as module-level helpers (or `private` helpers).
type: project
---

# `let` in Agda: no `where`, no `rewrite`

## Problem

In Agda, a `let`-binding is a single equation; it admits NO

- `where` clauses (parse error: "where clauses not allowed in let bindings")
- `rewrite` directives (silently doesn't work; the bound term is a type
  signature for an expression, not a clause-LHS)

This bit me twice while writing the Phase 3 backward proofs:

1. `not-bwd` — I tried to write
   ```agda
   let r-fired = aux is-bit-av
         where aux ((inj₁ ...)) = ...
               aux ((inj₂ ...)) = ...
   in v≡target , r-fired
   ```
   Parse error.

2. `reconstitute-field-bwd` — I tried to write
   ```agda
   let conj : (fmv ∧ fdv ∧ inf) ≡ true
       conj rewrite fmv | fdv | inf = refl
   in ...
   ```
   Unsolved-metas error: `rewrite` outside of a clause doesn't elaborate.

## Fix

Hoist the helper out of the `let` into a module-level `private` block
(or a top-level helper).  The two refactorings:

```agda
private
  not-fire : ... (av : Fr) → is-bit av → R-instr ...
  not-fire ... la (inj₁ av≡0) = ...
  not-fire ... la (inj₂ av≡1) = ...

private
  reconstitute-conj : ∀ mv dv bits → ... → ... ≡ true
  reconstitute-conj mv dv bits fmv fdv inf
    rewrite fmv | fdv | inf = refl
```

The main lemma then `let`-binds the result of calling the helper, no
`where`/`rewrite` needed inside the `let`.

## Note on `rewrite` helpers

If the helper takes the rewrite hypotheses as positional arguments,
the *implicit* parameters often can't be inferred (the goal type at
the call site only mentions the rewritten form).  Make `mv`, `dv`, etc.
*explicit* in the helper signature:

```agda
reconstitute-conj : ∀ mv dv bits → fits-in mv bits ≡ true → ...
                  --   ^ explicit; otherwise unsolved metas.
```

This is annoying but small.

## When to expect this

Any time a backward proof needs to:

- case-split on a witness fragment (e.g. `is-bit av`) inside an
  otherwise large `let`-block of equalities;
- assemble a boolean conjunction `_∧_` from three component
  equalities to `true` — `rewrite` is the only clean approach;
  hoist to a helper.