---
name: phase4b-dispatcher-template
description: Template for Phase 4b's R-instr→satisfies-step dispatcher cases — bridging an arbitrary synth state to the fresh-state per-instruction lemmas in CircuitFaithfulness.
type: project
---

# R-instr→satisfies-step dispatcher: per-case template

Phase 4b's dispatcher takes an arbitrary `st : SynthState` (not fresh!) and
needs to invoke the corresponding `*-fwd` lemma in `CircuitFaithfulness.agda`,
which is stated for `mk-synth (length mem) [] 0 []`.

## The bridge

For non-`declare-pub-input` instructions, by *definition* of `circuit-instr`:
```
clauses (circuit-instr hc i st) = clauses st ++ single-instr-clauses hc (nr-wires st) i
```

This is `refl`! Each `circuit-instr` clause uses `push-clause`, which only appends.

## Per-case skeleton (Δmem = 1, no special state)

```agda
R-instr→satisfies-step {hc} pre s s' i st mi pi prior-sat r@(r-i {...} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      ov   = ⟨ instruction's computed output ⟩
      mem' = mem ++ (ov ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (nr-wires st) i
                ≡ single-instr-clauses hc (length mem) i
      newcls-eq = cong (λ k → single-instr-clauses hc k i) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (i-fwd {pre} {s} {s'} {…} {hc} {rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {ov} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new
```

## Helper lemmas needed (private)

- `mem-inv-step-1 : nr-wires st ≡ length mem → nr-wires st + 1 ≡ length (mem ++ v ∷ [])`
- `mem-inv-step-2 : nr-wires st ≡ length mem → nr-wires st + 2 ≡ length (mem ++ x ∷ y ∷ [])`
- `mem-inv-step-2' : same but for `(mem ++ x ∷ []) ++ y ∷ []` (used by `div-mod-power-of-two`)
- `holds-mem-extends`, `satisfies-clauses-mem-extends` (by clause-case-split)
- `holds-pis-extends`, `satisfies-clauses-pis-extends` (only `clause-pi-from-wire` and `clause-comm-commitment` are non-trivial)
- `satisfies-clauses-++` (distributes satisfies over `_++_`)

## Special cases

- **declare-pub-input**: pis grows (not mem); needs `single-instr-clauses-with-decl` and `pi-len → pi-len + 1`.
- **output, pi-skip**: no clauses emitted; `satisfies-clauses-++ … [] = prior-sat` and the synth state's `clauses` field is unchanged.
- **public-input/private-input nothing**: Δmem=1, no clauses.  R-instr can only fire as `*-active` (since `eval-guard _ nothing ≡ just true` definitionally).
- **public-input/private-input (just g)**: Δmem=1, one clause.  Two R-instr cases (active, inactive); both subst-bridge mem from `s₁` (where applicable) back to `s`.

## "Missing prior-sat" gotcha

The original 4a postulate signature lacked the `prior-sat` hypothesis.  The dispatcher CANNOT prove cumulative satisfies-clauses without it (previously-emitted clauses don't witness themselves).  This is a real signature refinement, not an oversight: phase 4a's scaffolding postulate is technically *false* without this hypothesis.

Add as the 5th argument (between `pi-inv` and `R-instr`).