# ZKIR v2 — Agda formalization

This directory contains the Agda mechanization of **ZKIR major version 2**
(minor version V1, the canonical lowering). It formalizes the abstract
syntax of the IR, its two semantics — the *preprocess* (witness-population)
semantics and the Halo2 PLONKish *circuit* semantics — and the central
correctness theorem connecting them, together with the producer obligations
the prover must satisfy.

The companion textual specification is [`docs/zkir-v2-spec.md`](../../docs/zkir-v2-spec.md);
section references below (e.g. §5.2, §6.2) point into it. The ultimate
source of truth is the Rust implementation referenced from that spec.

## Headline result

The development discharges **P5** (spec §6.2): *circuit faithfulness*. For a
well-formed source, the operational relation `R src pre s` holds **iff** the
synthesized circuit is satisfied by the canonical witness:

```
R src pre s  ⇔  satisfies (circuit src) (witness-of s pre)
```

This was previously a postulate in the spec; it is now fully mechanized
(`circuit-faithful` in [`CircuitProof.agda`](CircuitProof.agda), re-exported
from [`Properties.agda`](Properties.agda)). No axioms are introduced by the
proof itself — it rests only on the cryptographic trust base collected in
the [`Assumptions`](Assumptions.agda) record described below.

The development contains **no `postulate`s**: the trust base is a structured
record taken as a module parameter, so every module type-checks under Agda's
`--safe` flag.

## Modules

Import [`Main.agda`](Main.agda) to type-check the entire development at once.
Every module takes the [`Assumptions`](Assumptions.agda) record as a module
parameter (`module M (⋯ : _) (open Assumptions ⋯) where`), so `Assumptions`
sits at the root of the dependency layering:

```
Assumptions → Syntax → Semantics → { Properties, Circuit, Obligations }
                                       Circuit → CircuitFaithfulness → CircuitProof
                                       Obligations → ObligationsSoundness
```

| Module | Contents |
| --- | --- |
| [`Assumptions.agda`](Assumptions.agda) | The entire trust base as one record: carrier types (`Fr`, `Alignment`), field/curve/hash/commitment operations, derived helpers (`to-bool`, `fits-in`, `bits-lt`, `pow2-fr`, `lt-bits`), and the field- and bit-arithmetic axioms. Downstream modules take it as a parameter; nothing is `postulate`d. |
| [`Syntax.agda`](Syntax.agda) | Abstract syntax (spec §3): the 26-variant `Instruction` datatype, `Index` operands, IR minor versions, and an `IrSource`. Mirrors the Rust `ir.rs` in source order. |
| [`Semantics.agda`](Semantics.agda) | Preprocess / operational semantics (spec §4): the small-step relation over the witness-population state. The field, Jubjub-curve, hashing, and commitment operations come from the `Assumptions` parameter. |
| [`Properties.agda`](Properties.agda) | Top-level correctness properties (spec §6). Re-exports the now-discharged `circuit-faithful` (P5) and bundles the spec's stated guarantees. |
| [`Circuit.agda`](Circuit.agda) | Halo2 PLONKish circuit semantics (spec §5, P5 Phase 1). Defines `Clause`/`Circuit`, the deterministic synthesis function `circuit` (§5.2 emission contracts), the `Witness` assignment model, and the `satisfies` relation. Chip behaviour is interpreted via the same canonical functions used by the preprocess semantics. |
| [`CircuitFaithfulness.agda`](CircuitFaithfulness.agda) | Per-instruction faithfulness lemmas (P5 Phase 2): forward and backward bridging between `R-instr` and the emitted clauses, instruction by instruction. |
| [`CircuitProof.agda`](CircuitProof.agda) | Program-level induction (P5 Phase 4, **complete**) that assembles the per-instruction lemmas into the full `circuit-faithful` equivalence. Contains no postulates. |
| [`Obligations.agda`](Obligations.agda) | Producer obligations (spec §6.4) as linear-scan checker functions: O1 (PiSkip discipline), O2 (Boolean-UB freedom), O3 (ReconstituteField / no field overflow). `producer-safe` is their conjunction. |
| [`ObligationsSoundness.agda`](ObligationsSoundness.agda) | Soundness of the obligation checkers: connects the static scans (`O2`/`O3`) to the dynamic relational semantics, by induction along the `R-instrs` trace. Feeds the backward bridging proofs. |
| [`Main.agda`](Main.agda) | Aggregator that imports every module above; type-checking it verifies the whole development. |

## Trust base (`Assumptions`)

The mechanization is parametric in the underlying cryptography. Rather than
`postulate`s, the trust base is a single structured record,
[`Assumptions`](Assumptions.agda), threaded through every module as a
parameter. It collects:

- field types and arithmetic over the BLS12-381 scalar field `Fr`,
- bit decomposition and in-field range predicates,
- Jubjub elliptic-curve operations,
- the Poseidon / persistent hash and commitment functions,
- byte-`Alignment` descriptors,
- the field- and bit-arithmetic *axioms* the proofs rely on.

No concrete instantiation of `Assumptions` is provided yet; the development
is intentionally abstract over this interface. Because nothing is
`postulate`d, the whole development type-checks under `--safe`. All other
results — including P5 — are proved, not assumed.

## Type-checking

From the [`src/`](..) directory, using the project's nix toolchain:

```sh
cd src
nix run .#agda -- zkir-v2/Main.agda
```

This type-checks the entire `--safe` development. It requires the standard
library and the dependencies declared in
[`../zkir-formal-spec.agda-lib`](../zkir-formal-spec.agda-lib). Note that
`CircuitProof.agda` is large; a cold check can take several minutes.
