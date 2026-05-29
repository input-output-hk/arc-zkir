---
name: state-dependent-clauses
description: How to phrase per-instruction lemmas when the emitted clauses depend on a synth-state field other than nr-wires.
type: project
---

# State-dependent clause emission

Most instructions in the P5 slice emit clauses that only depend on `SynthState.nr-wires`. For them, `single-instr-clauses : Bool → ℕ → Instruction → List Clause` is enough — it pins `(clauses, nr-declared-pi, output-wires) = ([], 0, [])`.

`declare-pub-input v` is different: it emits `clause-pi-from-wire entry v` where `entry = preamble-pi-count hc + nr-declared-pi`. So the per-instruction lemma needs to know `nr-declared-pi`.

## Solution: a parallel definition, not a refactor

```agda
single-instr-clauses-with-decl : Bool → ℕ → ℕ → Instruction → List Clause
single-instr-clauses-with-decl hc n d i =
  SynthState.clauses (circuit-instr hc i (mk-synth n [] d []))
```

This is used *only* by `declare-pub-input-{fwd,bwd}`. The existing 13 instructions keep using `single-instr-clauses`. Don't fold them into one; the two-arg version is easier to read for instructions that don't care about `d`.

## Consistency precondition on `pis` length

The forward lemma needs an *additional* hypothesis that the operational `Preprocessed.pis` length matches the synth-state's PI count:

```
length (Preprocessed.pis s) ≡ preamble-pi-count hc + d
```

This is what lets `pi-lookup-new` line up with the `entry` index in the emitted clause. Phase 4's program-level induction will discharge it from the global invariant relating operational and synth state.

## Don't generalize further (yet)

The task spec was explicit: lifting from one to two specializations is fine; don't introduce a general "synth-context-respecting" framework. That would be premature; only the next instruction-shape pattern (if any) earns it.