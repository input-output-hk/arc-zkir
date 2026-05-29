ARC-ZKIR workstream plan
========================
*Date:*  29 May 2026
*Author:* James Chapman, Mauro Jaskelioff

We identify two directions for this work.

1. Specification/Verficiation of ZKIR (v2 and v3)
2. Soudness via transpiliation to LLZK/Picus (Veridise).

In the first instance we will focus on 1 due to resource constraints.

Goals:

1. Specification for ZKIR Syntax
2. Specification for ZKIR computational semantics (cmp. `preprocess`)
3. Specification for ZKIR circuit semantics (cmp. `circuit`)
4. Verification that semantics agree.
5. Type system for ZKIR v3.
6. Test oracle/reference spec for one semantics (eg., preprocess).
7. Identify key properties that ZKIR guarantees and their connection
   with key properties of circuits.
8. Verification of composition of circuits via LLZK/Picus [optional].
9. Investigate compilation of ZKIR -> a zkVM

Resources:

Work package 1 [30 day]:
------------------------
This work package addresses items 1-4 above. Completion of item 4 will
likely introduce changes to 1-3 so they can not be considered done
until 4 is complete.

For the purposes of this work package we take v2 to be the versions
implemented in the midnight-ledger code base at the beginning of the
work package. At the time of writing the rust implementation of v3 is
small initial extension of v2 that is long way away from the full v3
proposal. Settling on a spec for v3 will require collaboration with
Shielded.

*Key question to address:*

How detailed does the treatment of the circuit semantics need to be
to address meaningful properties.

What is v3?


*Resources:*
1. Senior FM Engineer - 1 FTE
2. Head of FM - 0.2 FTE
3. Midnight/PL contributor - 0.2 FTE
4. Midnight/Cryptography contributor - 0.1 FTE

*Inputs:*
1. midnight-ledger rust implementation of v2
2. v3 draft proposal

*Deliverables:*
1. Markdown spec v2
2. Formal spec v2 + proofs
3. Markdown spec v3 (current prototype/current design)
4. Refined plan for WP2

Work package 2 [60 days]:
-------------------------

This work package addresses items 5-9 above. The type system is still
in development and not implemented. This work is partly design effort.
The compiliation of the preprocess semantics should be
achievable in haskell or another language such as rust or wasm as a
stretch goal. We would also carry out an initial investigation of
compilation to an identified zkVM

This workpackage is subject to change based on the findings of WP1 and
a refined plan for WP2 is a deliverable for WP1.

*Key question to address:*

"Well typed programs don't get ..."?

*Resources:*
1. Senior FM Engineer - 1 FTE
2. Head of FM - 0.2 FTE
3. Midnight/PL contributor - 0.4 FTE

*Inputs:*
1. v3 markdown spec
2. which zkVM(s) to target

*Deliverables:*
1. Formal spec v3 + proofs
2. Type system + type checker prototype
3. prototype reference implementation of/test oracle for preprocess semantics.
4. report on viability of compilation from ZKIR to a zkVM. (1 week spike).

Work package 3 [0 days]:
------------------------
We do not intend to address the LLZK/Picus at this stage. This work is
independent but would address key security properties of Midnight.

References:
-----------
1. "Proving Nothing"
2. ZKIR v3 proposal
3. Veridise report
4. FM review of Veridise report
