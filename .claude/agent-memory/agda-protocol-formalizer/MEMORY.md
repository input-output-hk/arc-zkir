# agda-protocol-formalizer memory index

Single-purpose memory files. Add new entries with frontmatter:
`name:`, `description:`, `type: {user|feedback|project|reference}`.

| File | Type | Topic |
|------|------|-------|
| `state-dependent-clauses.md` | project | Pattern for instructions whose clauses depend on a synth-state field beyond `nr-wires` (e.g. `declare-pub-input`'s `nr-declared-pi`). |
| `guarded-input-backward-split.md` | project | Why `public-input (just g)` and `private-input (just g)` ship two backward lemmas (active/inactive) rather than one with a clause-side case-split. |
| `private-name-bridging.md` | project | Helpers shared between `Semantics` and `Circuit` (e.g. `bits-lt`) must be public in `Semantics`; otherwise the duplicate `Circuit`-local copy creates a definitional mismatch in `CircuitFaithfulness`. |
| `push-mem2-shape-mismatch.md` | project | `push-mem2 s x y` and `push-mem (push-mem s x) y` give propositionally-equal but definitionally-distinct memory shapes; forward proofs need a `push-mem2-assoc` bridge and `subst`. |
| `let-no-where-no-rewrite.md` | project | `let`-bindings can't contain `where` or `rewrite`; backward-proof helpers needing either must be hoisted to module-level `private`, with rewrite-arg ℕ/Fr made explicit. |
| `phase4b-dispatcher-template.md` | project | Template for the 26-case dispatcher in `R-instr→satisfies-step` — how to bridge arbitrary synth states to fresh-state per-instruction lemmas via `mi : nr-wires st ≡ length mem`. |
| `maybe-shape-witness-of-gap.md` | project | (RESOLVED) Original Phase 4b spec gap.  Fixed by weakening `Maybe-shape false _ = ⊤` in `Circuit.agda` and enforcing WF1 in `init-state` (`Semantics.agda`).  Kept for historical record. |
| `phase4b-forward-discharged.md` | project | Phase 4b's forward direction now fully discharged (no postulates).  Documents the proof strategy for `output-wires-coincide`, `inputs-lookup-init`, and `circuit-faithful-fwd`. |
| `phase4c-o3-soundness.md` | project | Phase 4c's O3 soundness (`o3-preserve`, `o3-preserve*`, `O3-sound`, `o3-known-fits`) discharged with zero new postulates.  Includes the `o3-inv-coerce-idx` workaround for the `subst (λ k → O3-Inv (k , _) _)` meta-inference pitfall and the `false | ()` absurd-arm requirement for `O3-check`-guarded cases. |
| `phase4d-wire-discipline-resolved.md` | project | `wire-disc` (4th producer obligation in `producer-safe`) + `wire-disc-sound`/`Wire-Trace`/`wire-trace-head`/`lookup-shrink` infrastructure — current & load-bearing. NB: the D1/D2-status and signature-recovery sections in the file are HISTORICAL (D1/D2 now discharged). |
| `phase4d-D1-partial-progress.md` | project | Per-step backward dispatcher D1 (`satisfies→R-instr-step`): all 26 instruction cases discharged concretely, postulate-free, `op-side-data` shape-constraining for every instruction. Per-instruction case catalogue + side-data design. (Filename says "partial" but D1 is complete.) |
| `phase4d-D2-cons-discharged.md` | project | D2 (`satisfies-clauses→R-instrs`, incl. the former `-cons` postulate) fully discharged, zero new postulates.  Records the 5-step cons proof, two trivial D2 fit-preconditions, new helpers (`osd-mem-len`/`osd-pis-len`, `clauses-pis-fit-mono`/`-++`, `*-step-fst`), and the circular-let / pair-η / `with…|eq` pitfalls.  Only D3 + Phase-4e postulates remain for P5. |
| `p5_d3_blocker.md` | project | P5 status (CLOSED) — P5 fully mechanised 2026-05-29; the 3 hypotheses, `osd-fold` s'≡s trick, ⇔-not-↔ decision. |
| `p5_module_map.md` | project | Where the key P5 definitions/lemmas live and how they relate. |
| `user_mauro.md` | user | Mauro — formal-methods engineer on the ZKIR v2 Agda spec. |
| `feedback_no_python_edits.md` | feedback | Use Edit/Write tools only; never python/scripts to mutate files. |