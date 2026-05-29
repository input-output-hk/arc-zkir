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
3. Specification for ZKIR relational semantics (cmp. `circuit`)
4. Verification that semantics agree.
5. Type system for ZKIR v3.
6. Test oracle/reference spec for one semantics (eg., preprocess).
7. Identify key properties that ZKIR guarantees and their connection with key properties of circuits.
8. Verification of composition of circuits [optional].

Resources:

Work package 1 [30 day]:
------------------------
This work package addresses items 1-4 above. Completion of item 4 will
likely introduce changes to 1-3 so they can not be considered done
until 4 is complete.

*Key question to address:*

How detailed does the treatment of the relational semantics need to be
to address soundess/completeness of circuits?

*Resources:*
1. Senior FM Engineer - 1 FTE
2. Head of FM - 0.2 FTE
3. Midnight/PL contributor - 0.1 FTE
4. Midnight/Cryptography contributor - 0.1 FTE


Work package 2 [60 days]:
-------------------------

This work package addresses items 5-7 above. The type system is still
in development and not implemented. This work is partly design effort.
The compiliation to of one version of the semantics should be
achievable in haskell or another language such as rust or wasm as a
stretch goal.

*Key question to address:*

"Well typed programs don't get ..."?

*Resources:*
1. Senior FM Engineer - 1 FTE
2. Head of FM - 0.2 FTE
3. Midnight/PL contributor - 0.4 FTE

Work package 3 [0 days]:
------------------------
We do not intend to address the LLZK/Picus at this stage.

Notes:
------
An older version of the plan is here: https://docs.google.com/document/d/1M46ELcVkgdgtRoXzMjnpTl_9aSsq1uge8jjZCuiBCI8

References:
-----------
1. "Proving Nothing"
2. ZKIR v3 proposal
3. Veridise report
4. FM review of Veridise report
