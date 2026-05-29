---
name: p5-module-map
description: Where the key ZKIR v2 P5 definitions and lemmas live across the 8 modules.
metadata:
  type: project
---

ZKIR v2 P5 lives in `src/zkir-v2/` (8 modules). Build: `agda CircuitProof.agda` (~5-12s, must
be warning-free). Pre-commit: `agda Main.lagda.md` from `agda-src/` (not present in this dir —
verify the actual pre-commit target before relying on it).

**Module roles**
- `Syntax.agda` — `Instruction` (26 variants), `IrSource` (num-inputs, do-communications-commitment, instructions). `Fr`, `Alignment` postulated (primitive).
- `Semantics.agda` — operational/computational semantics: `init-state` (158, fails on WF1 length mismatch or hc∧no-commitment), `preprocess-instr`/`preprocess-instrs`/`preprocess`, `transcripts-consumed` (428), `comm-ok` (435), relational `R-instr`/`R-instrs` (464/618), top-level `R` (627).
- `Circuit.agda` — `circuit : IrSource → Circuit` (399), `Witness`/`mk-witness` (430), `holds` per clause (458+; comm-commitment at 625), `satisfies`/`mk-sat` record (652), `Maybe-shape` (642), `nat-range`.
- `Obligations.agda` — producer obligations O1/O2/O3 + `wire-disc`; `producer-safe` = their conjunction. `Δmem` (107), `wire-check` (349). No input-arity check anywhere.
- `ObligationsSoundness.agda` — soundness of the Bool obligation scans (O2/O3/wire → Trace predicates).
- `Properties.agda` — computational↔relational faithfulness: `preprocess→R` (911), `R→preprocess` (927), `preprocess-instrs→R-instrs` (892), `R-instrs→preprocess-instrs` (902), per-instruction `preprocess-instr→R-instr` (713). NOTE its `circuit`/`satisfies`/`circuit-faithful` (938-946) are the OLD postulated placeholders using `circuit : IrSource → ProofPreimage → ConstraintSystem` — different signature from the real `circuit src` / `witness-of s pre` in Circuit/CircuitProof. Closing P5 means replacing this whole postulate block.
- `CircuitFaithfulness.agda` — per-instruction backward `*-bwd` lemmas (lookup extraction from the witness, `lookup-shrink`, etc.).
- `CircuitProof.agda` — the P5 proof. `witness-of` (98), `comm-rand-of` (93). Forward: `circuit-faithful-fwd` (2516) + `-false`/`-true` (2289/2362) + helpers `init-state-*` (1937-2010), `no-comm-contra`/`extract-comm-ok-eq` (2480+), `bool-cases`/`maybe-cases` (2505+). Backward: D1 `satisfies→R-instr-step` (2942, 26 cases, DISCHARGED), `op-side-data` (2766), `next-state-from-osd` (2866), `op-side-data-list` data (5370), D2 `satisfies-clauses→R-instrs` (5395, DISCHARGED). Postulates remaining: `circuit-faithful-bwd` (~5656, D3) and `circuit-faithful` (~5683, Phase-4e bundle).

**Producer-safe trace extractors (for threading into D2):** `wire-disc-sound` (2574),
`o2-trace-head`/`o3-trace-head` (2621/2628), `wire-trace-head` (2605). Forward direction at
2392-2413 shows the O2/O3/Wire/output-wires/inputs-lookup extraction pattern to mirror.

**Key invariants:** `mem-inv`, `pi-inv` (state↔synth length linkage), `O2-Inv`/`O3-Inv`,
`mem-inv-next`/`pi-inv-next` (4496/4593), `clauses-st-fit-invariant`, `clauses-pis-fit-instr`.
At the top-level call site `st₀ = mk-synth num-inputs [] 0 []` so the two D2 fit-preconditions
are `refl` (clauses ≡ []).
