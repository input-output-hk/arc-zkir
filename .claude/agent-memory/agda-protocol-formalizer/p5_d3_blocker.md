---
name: p5-d3-blocker
description: P5 fully CLOSED (2026-05-29). circuit-faithful-bwd + bundled ⇔ discharged; the three hypotheses and the ⇔-not-↔ decision.
metadata:
  type: project
---

**P5 is FULLY MECHANISED and CLOSED (2026-05-29).** No postulates remain in
`CircuitProof.agda` or the P5 path of `Properties.agda`. All 8 modules build clean
(`agda <M>.agda` exit 0, warning-free under `-W all`). The only axioms P5 rests on are
the pre-existing field/crypto postulates in `CircuitFaithfulness.agda` (`≡ᶠ?-refl`,
`≡ᶠ?-true`, `transient-commit` props, BLS arithmetic, etc.).

**`circuit-faithful-bwd` (D3) needed THREE extra hypotheses to be TRUE; all in the sig:**
1. WF1: `length (inputs pre) ≡ num-inputs src` (§3.4) — input arity.
2. `preprocess-shaped src pre s` (§5.4) — fixes `satisfies`-blindness to transcript-read
   wires (public/private-input active emit no clause; pi-skip active has no in-circuit shadow).
3. `transcripts-consumed pre s ≡ true` — FOLDED INTO `preprocess-shaped` as a 3rd conjunct.
   THIRD BLOCKER (discovered this session): `R` carries `transcripts-consumed` as a top-level
   conjunct (Semantics.agda:632) but it is NOT derivable from satisfies + the trace +
   producer-safety — no obligation (O1/O2/O3/wire-disc) constrains the transcript cursors; an
   all-inactive walk consumes nothing. Faithful to §5.4 (states reached by a SUCCESSFUL
   preprocess, which passed `transcripts-consumed`). `comm-ok` is NOT folded in — it IS
   recoverable from the comm clause, so it stays derived (keeps satisfies load-bearing).

**`preprocess-shaped` (final form):** `Σ s₀, init-state src pre ≡ just s₀ × Σ ms ps,
Tr-shaped pre s₀ instrs s ms ps × transcripts-consumed pre s ≡ true`. `R⇒preprocess-shaped`
supplies the `transcripts-consumed` conjunct from R's `tc`.

**The s'≡s crux (part 6) — solved via osd-fold:** D2 (`satisfies-clauses→R-instrs`) already
returns a 4th component `s' ≡ osd-fold osd`. New lemma `Tr-shaped→osd-list-fold` (induction
on Tr-shaped, ~30 cases, each = the recursive call; nil = refl) proves
`osd-fold (Tr-shaped→osd-list … tr) ≡ s`. So `s' ≡ osd-fold osd ≡ s`, then
`subst (R-instrs pre s₀ instrs) s'≡s Rs'`. NO per-field state reasoning needed — osd-fold
captures all 7 Preprocessed fields because next-state-from-osd updates them all.

**New private lemmas (all in CircuitProof, in the `Tr-shaped→osd-list` private block or just
after D3 doc):**
- `Tr-shaped→osd-list-fold` — the fold endpoint = endpoint index.
- `tr-step-mem` / `tr-step-pis` (per-step, mirror tr-next's cases) + `Tr-shaped→mem` /
  `Tr-shaped→pis` (fold) — reshape `memory s`→`memory s₀ ++ ms` to feed D2. GOTCHA: no-op
  cases (ms≡[] / ps≡[]) need `sym (trans (cong (m ++_) eq) (++-identityʳ _))`, NOT just
  `sym (cong (m ++_) eq)` (target is `m ≡ m ++ ms`, not `m ++ [] ≡ m ++ ms`).
- `bwd-body-trace` (packages D2: invariants via o2/o3-inv-init, traces via
  O2/O3-bool→Runs∘producer-safe-O2/O3 and wire-disc-sound, fits=refl since clauses st₀≡[],
  bk₀=bm₀=[]; returns R-instrs ending at s). D2's result tuple is 4-deep: s' then
  (mem-eq, pis-eq, R-instrs, fold-eq) — projections `proj₁(proj₂(proj₂(proj₂ d2)))` for Rs',
  `proj₂(proj₂(proj₂(proj₂ d2)))` for fold-eq.
- `bwd-comm-ok-true` (inverts the comm clause `holds`: ivs≡inputs via inputs-lookup-init+
  mem-lookups-mono, ovs≡outputs via output-wires-coincide, rv≡r via comm-rand-of-just,
  pv≡c via init-state-pi-1+pi-lookup-mono, then `subst (λ x→(c ≡ᶠ? x)≡true) c≡tc ≡ᶠ?-refl`).
- `bwd-no-comm-contra` (hc=true/cc=nothing ruled out by satisfies rand-shape = Maybe-shape
  true nothing = ⊥; has-comm (circuit src) ≡ do-comm src definitionally).
- `comm-rand-of-just`, `circuit-eq-false`, `circuit-eq-true`, `comm-ok-false` (top-level
  private helpers — needed because `where` is ILLEGAL inside a `let` binding; lift any helper
  with a dependent `refl` match out of the body's `let`).

**KEY DESIGN DECISION — bundle is `_⇔_` NOT `_↔_`.** The spec §6.2 states P5 as an *iff*
of propositions = logical equivalence. `Function.Bundles._⇔_` (built by `mk⇔ to from`,
needs ONLY the two implications) renders this faithfully and is fully constructible.
`_↔_` (type isomorphism) additionally demands the inverse laws `to(from x)≡x` — propositional
equality between PROOFS of the Set-valued R/satisfies, which are not unique, so `↔` is NOT
dischargeable without a proof-irrelevance postulate. Changed both `circuit-faithful` (here)
and the Properties re-export to `_⇔_`. The OLD postulate used `↔`; this is a faithful,
postulate-free correction.

**Properties.agda:** the old `postulate ConstraintSystem/circuit/satisfies/circuit-faithful`
block (opaque model, `↔`) is REPLACED by re-exporting the real `circuit`/`satisfies` (Circuit),
`witness-of`/`preprocess-shaped`/`circuit-faithful` (CircuitProof), `producer-safe`
(Obligations). Nothing in zkir-v2 or the wider arc-zkir repo consumed the old postulates.
No import cycle: CircuitProof does NOT import Properties; Properties imports CircuitProof.

**HARD CONSTRAINT this session (user):** NO python for edits — Edit/Write tools only.
