{-# OPTIONS --safe #-}
open import zkir-v2.Assumptions

module zkir-v2.Circuit (⋯ : _) (open Assumptions ⋯) where

------------------------------------------------------------------------
-- Circuit (Halo2 PLONKish) semantics for ZKIR v2 (V1 lowerings).
--
-- This module is Phase 1 of the P5 proof effort (spec §6.5):
--
--   • Section A defines the syntax of an in-circuit constraint system
--     (`Clause`, `Circuit`) and the structural synthesis function
--     (`circuit-instr`, `circuit`) that mirrors §5.2's emission
--     contracts.  Synthesis is a *deterministic function of the source*
--     alone — independent of the prover's preimage (§5.5).
--
--   • Section B defines a wire-assignment model (`Witness`) and the
--     satisfaction relation (`holds`, `satisfies`) that interprets
--     clauses against an assignment.  Chip behaviour (Poseidon,
--     Jubjub, SHA-256, range checks) is interpreted via the same
--     canonical functions postulated in `zkir-v2.Semantics`; this
--     makes the chip "perfectly sound" by construction and is the
--     axiomatic interface to Halo2's chip layer for Phase 2.
--
-- This module establishes no theorems.  The bridging claim
-- `R src pre s ↔ satisfies (circuit src) (witness-of s pre)`
-- (which is P5) is the goal of Phases 2-4.
------------------------------------------------------------------------

-- Field/curve operations and the `fits-in`/`bits-lt`/`to-bool`/`pow2-fr`/
-- `lt-bits` helpers come from the `Assumptions` parameter (opened by the
-- module telescope).  Only the genuinely Semantics-level definitions are
-- imported here.
open import zkir-v2.Syntax ⋯
open import zkir-v2.Semantics ⋯
  using ( mem-lookup; mem-lookups; eval-guard; from-bool
        ; ProofPreimage; Preprocessed; mk-state )

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
import Data.Bool as Bool
open import Data.List    using (List; []; _∷_; _++_; length; map; drop; take)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; suc; zero; _∸_; _+_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Local helpers
--
-- These helpers are exported because `holds` (Section B) refers to them
-- in its result types, and downstream proofs need to construct/destruct
-- those types.  `from-bool`, `pow2-fr` and `lt-bits` are re-used from
-- `Semantics`/`Assumptions` so that references here and in `R-instr`
-- constructors are the same names.
------------------------------------------------------------------------

-- "Wire bound to memory cell i has value v" — phrased as a
-- propositional equality, for readability in clause definitions.
_at_↦_ : List Fr → Index → Fr → Set
mem at i ↦ v = mem-lookup mem i ≡ just v

infix 1 _at_↦_

-- A bit predicate: v ∈ {0, 1}.  Encoded as a sum.
is-bit : Fr → Set
is-bit v = (v ≡ 0ᶠ) ⊎ (v ≡ 1ᶠ)

------------------------------------------------------------------------
-- Section A.  Circuit syntax
------------------------------------------------------------------------


-- Clauses
--
-- One constructor per emission shape in §5.2 (V1).  Wire references are
-- by `Index`; constants are inline.  PI-vector positions (`entry-idx`)
-- count from zero across the *entire* PI vector, including the
-- structural preamble (binding-input, optional comm.0).

data Clause : Set where

  -- assert(c): ⟦c⟧ ≠ 0
  clause-assert-non-zero
    : (c : Index) → Clause

  -- cond_select(b, a, c): ⟦b⟧ ∈ {0,1} ∧ out = ⟦b⟧·⟦a⟧ + (1−⟦b⟧)·⟦c⟧
  clause-cond-select
    : (out b a c : Index) → Clause

  -- constrain_bits(v, n): ⟦v⟧ < 2^n  (only when n < FR_BITS)
  clause-range-bits
    : (v : Index) → (bits : ℕ) → Clause

  -- constrain_eq(a, b): ⟦a⟧ = ⟦b⟧
  clause-eq
    : (a b : Index) → Clause

  -- constrain_to_boolean(v): ⟦v⟧ ∈ {0, 1}
  clause-bool
    : (v : Index) → Clause

  -- copy(v): out = ⟦v⟧
  clause-copy
    : (out v : Index) → Clause

  -- ec_add: (⟦aₓ⟧,⟦aᵧ⟧) ∈ J ∧ (⟦bₓ⟧,⟦bᵧ⟧) ∈ J ∧ (cₓ,cᵧ) = sum
  clause-ec-add
    : (c-x c-y a-x a-y b-x b-y : Index) → Clause

  -- ec_mul: (⟦aₓ⟧,⟦aᵧ⟧) ∈ J ∧ (cₓ,cᵧ) = ⟦s⟧ · (⟦aₓ⟧,⟦aᵧ⟧)
  clause-ec-mul
    : (c-x c-y a-x a-y scalar : Index) → Clause

  -- ec_mul_generator: (cₓ,cᵧ) = ⟦s⟧ · G
  clause-ec-mul-generator
    : (c-x c-y scalar : Index) → Clause

  -- hash_to_curve: (cₓ,cᵧ) = H2C(⟦I⟧)
  clause-hash-to-curve
    : (c-x c-y : Index) → (inputs : List Index) → Clause

  -- load_imm(k): out = k
  clause-load-imm
    : (out : Index) → (imm : Fr) → Clause

  -- div_mod_power_of_two(v, n):
  --   ⟦v⟧ = q · 2^n + r  ∧  r < 2^n  ∧  q < 2^(FR_BITS − n)
  clause-div-mod
    : (q r v : Index) → (bits : ℕ) → Clause

  -- reconstitute_field(d, m, n):
  --   ⟦d⟧ < 2^(FR_BITS − n)  ∧  ⟦m⟧ < 2^n  ∧  out = ⟦d⟧·2^n + ⟦m⟧  (in Fr)
  -- (No overflow check — see §6.3 and obligation O3.)
  clause-reconstitute
    : (out d m : Index) → (bits : ℕ) → Clause

  -- transient_hash(I): out = Poseidon(⟦I⟧)
  clause-transient-hash
    : (out : Index) → (inputs : List Index) → Clause

  -- persistent_hash(α, I):
  --   (h₁, h₂) is the SHA-256 decomposition (high byte / low 31 bytes)
  --   of the FAB byte encoding of ⟦I⟧ under α.
  clause-persistent-hash
    : (h₁ h₂ : Index) → (alignment : Alignment)
    → (inputs : List Index) → Clause

  -- test_eq(a, b): out = 1 iff ⟦a⟧ = ⟦b⟧
  clause-test-eq
    : (out a b : Index) → Clause

  -- add(a, b): out = ⟦a⟧ + ⟦b⟧
  clause-add
    : (out a b : Index) → Clause

  -- mul(a, b): out = ⟦a⟧ · ⟦b⟧
  clause-mul
    : (out a b : Index) → Clause

  -- neg(a): out = − ⟦a⟧
  clause-neg
    : (out a : Index) → Clause

  -- not(a): out = is_zero(⟦a⟧)
  -- (= 1 − ⟦a⟧ exactly when ⟦a⟧ ∈ {0,1}; producer obligation O2 closes
  -- the gap to the operational `not`.)
  clause-not
    : (out a : Index) → Clause

  -- less_than(a, b, n): out = 1 iff ⟦a⟧ < ⟦b⟧
  -- using a range-check chip with padded bit-bound `lt-bits n`.
  clause-less-than
    : (out a b : Index) → (bits : ℕ) → Clause

  -- Guarded input cell: (out = 0) ∨ (⟦i⟧ = 1)
  -- Emitted when public/private_input has a guard.
  clause-guard-disj
    : (out i : Index) → Clause

  -- Declared PI binding: pis[entry] = ⟦wire⟧
  clause-pi-from-wire
    : (entry : ℕ) → (wire : Index) → Clause

  -- Communications-commitment clause (§5.4):
  --   pis[1] = Poseidon(comm-rand ‖ inputs ‖ outputs)
  -- where `inputs = [0 .. num_inputs)` and `outputs` are the args of
  -- `output(v)` instructions in source order.
  clause-comm-commitment
    : (inputs outputs : List Index) → Clause

-- The constraint system: structurally a list of clauses, plus the
-- structural shape (number of wires, PI-vector length, comm-commitment
-- flag).  Determined by the source alone.
record Circuit : Set where
  constructor mk-circuit
  field
    nr-wires : ℕ
    clauses  : List Clause
    pi-len   : ℕ          -- expected length of the verifier's PI vector
    has-comm : Bool

------------------------------------------------------------------------
-- Synthesis
--
-- `circuit-instr` processes one instruction, growing the wire count and
-- appending clauses.  It mirrors the shape of `preprocess-instr` but
-- is total (synthesis cannot fail; §5.5).
--
-- The synthesis state additionally tracks the count of `DeclarePubInput`
-- emitted (for PI-entry indexing) and the indices of `output(v)`
-- arguments (in source order; consumed by the comm-commitment clause).
------------------------------------------------------------------------

record SynthState : Set where
  constructor mk-synth
  field
    nr-wires       : ℕ           -- next wire to be allocated
    clauses        : List Clause  -- in emission order
    nr-declared-pi : ℕ           -- # DeclarePubInput processed
    output-wires   : List Index   -- args of `output(v)` in order

-- Number of "preamble" PI entries (binding-input + optional comm.0).
preamble-pi-count : Bool → ℕ
preamble-pi-count true  = 2
preamble-pi-count false = 1

-- Append helper.
_⊕_ : ∀ {A : Set} → List A → A → List A
xs ⊕ x = xs ++ (x ∷ [])

infixl 5 _⊕_

-- Update helpers.

private
  push-clause : SynthState → Clause → SynthState
  push-clause st cl = record st { clauses = SynthState.clauses st ⊕ cl }

  push-clauses : SynthState → List Clause → SynthState
  push-clauses st cls = record st { clauses = SynthState.clauses st ++ cls }

  bump-wires : SynthState → ℕ → SynthState
  bump-wires st n = record st { nr-wires = SynthState.nr-wires st + n }

-- One instruction's worth of synthesis.  `has-comm` is the source-level
-- flag, threaded in because `declare-pub-input` needs the PI-entry
-- offset.
circuit-instr : Bool → Instruction → SynthState → SynthState

circuit-instr _ (assert c) st =
  push-clause st (clause-assert-non-zero c)

circuit-instr _ (cond-select b a c) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-cond-select out b a c)

circuit-instr _ (constrain-bits v bits) st =
  -- WF2 forbids bits ≥ FR_BITS; for bits ≥ FR_BITS the lowering would
  -- emit no clause.  We unconditionally emit the range clause and let
  -- WF2 guarantee its existence in the model.
  push-clause st (clause-range-bits v bits)

circuit-instr _ (constrain-eq a b) st =
  push-clause st (clause-eq a b)

circuit-instr _ (constrain-to-boolean v) st =
  push-clause st (clause-bool v)

circuit-instr _ (copy v) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-copy out v)

circuit-instr has-comm (declare-pub-input v) st =
  let entry = preamble-pi-count has-comm + SynthState.nr-declared-pi st
      st'   = record st { nr-declared-pi = suc (SynthState.nr-declared-pi st) }
  in push-clause st' (clause-pi-from-wire entry v)

circuit-instr _ (pi-skip _ _) st =
  st  -- no in-circuit constraints

circuit-instr _ (ec-add a-x a-y b-x b-y) st =
  let cx = SynthState.nr-wires st
      cy = suc cx
  in push-clause (bump-wires st 2) (clause-ec-add cx cy a-x a-y b-x b-y)

circuit-instr _ (ec-mul a-x a-y scalar) st =
  let cx = SynthState.nr-wires st
      cy = suc cx
  in push-clause (bump-wires st 2) (clause-ec-mul cx cy a-x a-y scalar)

circuit-instr _ (ec-mul-generator scalar) st =
  let cx = SynthState.nr-wires st
      cy = suc cx
  in push-clause (bump-wires st 2) (clause-ec-mul-generator cx cy scalar)

circuit-instr _ (hash-to-curve inputs) st =
  let cx = SynthState.nr-wires st
      cy = suc cx
  in push-clause (bump-wires st 2) (clause-hash-to-curve cx cy inputs)

circuit-instr _ (load-imm imm) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-load-imm out imm)

circuit-instr _ (div-mod-power-of-two v bits) st =
  let q = SynthState.nr-wires st
      r = suc q
  in push-clause (bump-wires st 2) (clause-div-mod q r v bits)

circuit-instr _ (reconstitute-field d m bits) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-reconstitute out d m bits)

circuit-instr _ (output v) st =
  -- No clauses; the wire index is recorded for the comm-commitment
  -- clause emitted at the end of synthesis (if has-comm).
  record st { output-wires = SynthState.output-wires st ⊕ v }

circuit-instr _ (transient-hash inputs) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-transient-hash out inputs)

circuit-instr _ (persistent-hash alignment inputs) st =
  let h₁ = SynthState.nr-wires st
      h₂ = suc h₁
  in push-clause (bump-wires st 2) (clause-persistent-hash h₁ h₂ alignment inputs)

circuit-instr _ (test-eq a b) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-test-eq out a b)

circuit-instr _ (add a b) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-add out a b)

circuit-instr _ (mul a b) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-mul out a b)

circuit-instr _ (neg a) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-neg out a)

circuit-instr _ (not a) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-not out a)

circuit-instr _ (less-than a b bits) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-less-than out a b bits)

circuit-instr _ (public-input nothing) st =
  let out = SynthState.nr-wires st in
  bump-wires st 1                      -- a free witness wire, no clause
circuit-instr _ (public-input (just g)) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-guard-disj out g)

circuit-instr _ (private-input nothing) st =
  let out = SynthState.nr-wires st in
  bump-wires st 1
circuit-instr _ (private-input (just g)) st =
  let out = SynthState.nr-wires st in
  push-clause (bump-wires st 1) (clause-guard-disj out g)

-- Fold over an instruction list.

circuit-instrs : Bool → List Instruction → SynthState → SynthState
circuit-instrs _        []       st = st
circuit-instrs has-comm (i ∷ is) st =
  circuit-instrs has-comm is (circuit-instr has-comm i st)

-- Top-level synthesis.  Wires `[0 .. num_inputs)` are the
-- circuit-input wires (no clauses bind them; their values are part of
-- the witness).  After processing the instruction list, if has-comm,
-- append the comm-commitment clause.

-- Natural-number range [0, 1, …, n-1].  Used both as `cm-inputs`
-- inside `circuit`'s comm-commitment clause and (re-imported by
-- `CircuitProof.input-wires`) by the bridging proofs in Phase 4.
nat-range : ℕ → List Index
nat-range zero    = []
nat-range (suc k) = nat-range k ⊕ k

circuit : IrSource → Circuit
circuit src =
  let n   = IrSource.num-inputs src
      hc  = IrSource.do-communications-commitment src
      st₀ = mk-synth n [] 0 []
      st  = circuit-instrs hc (IrSource.instructions src) st₀
      cls = SynthState.clauses st
      -- Built-in inputs to the comm-commitment: [0 .. n).
      cm-inputs = nat-range n
      cls' = if hc
        then cls ⊕ clause-comm-commitment cm-inputs (SynthState.output-wires st)
        else cls
      pi-len = preamble-pi-count hc + SynthState.nr-declared-pi st
  in mk-circuit (SynthState.nr-wires st) cls' pi-len hc

------------------------------------------------------------------------
-- Section B.  Wire assignments and satisfaction
------------------------------------------------------------------------

-- Witness for a circuit
--
-- The Halo2 prover commits to:
--   • `mem` — values of the witness wires (one per allocated cell).
--   • `pis` — values of the public-input wires (verifier-supplied).
--   • `comm-rand` — the randomness `comm_commitment.1`, allocated as
--     an additional witness wire iff the circuit has-comm.
--
-- Phase 4 will define `witness-of : Preprocessed → ProofPreimage →
-- Witness`, the bridging function that builds a `Witness` from the
-- operational state and the preimage.

record Witness : Set where
  constructor mk-witness
  field
    mem       : List Fr
    pis       : List Fr
    comm-rand : Maybe Fr

------------------------------------------------------------------------
-- Clause satisfaction
--
-- `holds w cl` is the proposition "wire assignment `w` satisfies
-- clause `cl`".  We express constraints as propositional equations on
-- looked-up wire values, using the canonical chip primitives postulated
-- in zkir-v2.Semantics.
--
-- Treating chip primitives as canonical functions (rather than as
-- separate axiomatic relations) implicitly bakes in the chips'
-- soundness.  This is the trust boundary established in Phase 0:
-- in-circuit equality with the function = the chip's soundness
-- guarantee, taken on faith.
------------------------------------------------------------------------

-- Look up the i-th PI entry.  Returns `nothing` if out of range.
pi-lookup : List Fr → ℕ → Maybe Fr
pi-lookup []       _       = nothing
pi-lookup (x ∷ _)  zero    = just x
pi-lookup (_ ∷ xs) (suc n) = pi-lookup xs n

holds : Witness → Clause → Set

holds w (clause-assert-non-zero c) =
  ∃-syntax (λ v →
    (Witness.mem w at c ↦ v) × (¬ (v ≡ 0ᶠ)))

holds w (clause-cond-select out b a c) =
  ∃-syntax (λ bv → ∃-syntax (λ av → ∃-syntax (λ cv → ∃-syntax (λ ov →
      (Witness.mem w at b ↦ bv)
    × (Witness.mem w at a ↦ av)
    × (Witness.mem w at c ↦ cv)
    × (Witness.mem w at out ↦ ov)
    × is-bit bv
    × (ov ≡ (bv *ᶠ av) +ᶠ ((1ᶠ +ᶠ (-ᶠ bv)) *ᶠ cv))))))

holds w (clause-range-bits v bits) =
  ∃-syntax (λ vv →
      (Witness.mem w at v ↦ vv)
    × (fits-in vv bits ≡ true))

holds w (clause-eq a b) =
  ∃-syntax (λ av → ∃-syntax (λ bv →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at b ↦ bv)
    × (av ≡ bv)))

holds w (clause-bool v) =
  ∃-syntax (λ vv →
    (Witness.mem w at v ↦ vv) × is-bit vv)

holds w (clause-copy out v) =
  ∃-syntax (λ vv → ∃-syntax (λ ov →
      (Witness.mem w at v ↦ vv)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ vv)))

holds w (clause-ec-add c-x c-y a-x a-y b-x b-y) =
  ∃-syntax (λ ax → ∃-syntax (λ ay → ∃-syntax (λ bx → ∃-syntax (λ by →
   ∃-syntax (λ cx → ∃-syntax (λ cy →
        (Witness.mem w at a-x ↦ ax)
      × (Witness.mem w at a-y ↦ ay)
      × (Witness.mem w at b-x ↦ bx)
      × (Witness.mem w at b-y ↦ by)
      × (Witness.mem w at c-x ↦ cx)
      × (Witness.mem w at c-y ↦ cy)
      × (ec-add-pts ax ay bx by ≡ just (cx , cy))))))))

holds w (clause-ec-mul c-x c-y a-x a-y scalar) =
  ∃-syntax (λ ax → ∃-syntax (λ ay → ∃-syntax (λ sc →
   ∃-syntax (λ cx → ∃-syntax (λ cy →
        (Witness.mem w at a-x ↦ ax)
      × (Witness.mem w at a-y ↦ ay)
      × (Witness.mem w at scalar ↦ sc)
      × (Witness.mem w at c-x ↦ cx)
      × (Witness.mem w at c-y ↦ cy)
      × (ec-mul-pt ax ay sc ≡ just (cx , cy)))))))

holds w (clause-ec-mul-generator c-x c-y scalar) =
  ∃-syntax (λ sc → ∃-syntax (λ cx → ∃-syntax (λ cy →
      (Witness.mem w at scalar ↦ sc)
    × (Witness.mem w at c-x ↦ cx)
    × (Witness.mem w at c-y ↦ cy)
    × (ec-mul-gen sc ≡ (cx , cy)))))

holds w (clause-hash-to-curve c-x c-y inputs) =
  ∃-syntax (λ vs → ∃-syntax (λ cx → ∃-syntax (λ cy →
      (mem-lookups (Witness.mem w) inputs ≡ just vs)
    × (Witness.mem w at c-x ↦ cx)
    × (Witness.mem w at c-y ↦ cy)
    × (hash-to-curve-fn vs ≡ (cx , cy)))))

holds w (clause-load-imm out imm) =
  ∃-syntax (λ ov →
    (Witness.mem w at out ↦ ov) × (ov ≡ imm))

holds w (clause-div-mod q r v bits) =
  ∃-syntax (λ qv → ∃-syntax (λ rv → ∃-syntax (λ vv →
      (Witness.mem w at q ↦ qv)
    × (Witness.mem w at r ↦ rv)
    × (Witness.mem w at v ↦ vv)
    × (fits-in rv bits ≡ true)
    × (fits-in qv (FR-BITS ∸ bits) ≡ true)
    × (vv ≡ (qv *ᶠ pow2-fr bits) +ᶠ rv))))

holds w (clause-reconstitute out d m bits) =
  ∃-syntax (λ dv → ∃-syntax (λ mv → ∃-syntax (λ ov →
      (Witness.mem w at d ↦ dv)
    × (Witness.mem w at m ↦ mv)
    × (Witness.mem w at out ↦ ov)
    × (fits-in dv (FR-BITS ∸ bits) ≡ true)
    × (fits-in mv bits ≡ true)
    × (ov ≡ (dv *ᶠ pow2-fr bits) +ᶠ mv))))
  -- N.B.: no overflow check.  Per §6.3 a witness with
  --   dv · 2^bits + mv ≥ |Fr|  and  ov = field-reduced value
  -- satisfies this clause but not the operational rule.  Producer
  -- obligation O3 closes the gap.

holds w (clause-transient-hash out inputs) =
  ∃-syntax (λ vs → ∃-syntax (λ ov →
      (mem-lookups (Witness.mem w) inputs ≡ just vs)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ transient-hash-fn vs)))

holds w (clause-persistent-hash h₁ h₂ alignment inputs) =
  ∃-syntax (λ vs → ∃-syntax (λ v1 → ∃-syntax (λ v2 →
      (mem-lookups (Witness.mem w) inputs ≡ just vs)
    × (Witness.mem w at h₁ ↦ v1)
    × (Witness.mem w at h₂ ↦ v2)
    × (persistent-hash-fn alignment vs ≡ (v1 , v2)))))

holds w (clause-test-eq out a b) =
  ∃-syntax (λ av → ∃-syntax (λ bv → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at b ↦ bv)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ from-bool (av ≡ᶠ? bv)))))

holds w (clause-add out a b) =
  ∃-syntax (λ av → ∃-syntax (λ bv → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at b ↦ bv)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ av +ᶠ bv))))

holds w (clause-mul out a b) =
  ∃-syntax (λ av → ∃-syntax (λ bv → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at b ↦ bv)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ av *ᶠ bv))))

holds w (clause-neg out a) =
  ∃-syntax (λ av → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ -ᶠ av)))

holds w (clause-not out a) =
  -- is_zero(a): returns 1 iff a = 0, else 0.
  ∃-syntax (λ av → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at out ↦ ov)
    × (ov ≡ from-bool (av ≡ᶠ? 0ᶠ))))

holds w (clause-less-than out a b bits) =
  -- Range checks use the *padded* bit count (cf. §5.2 footnote).
  ∃-syntax (λ av → ∃-syntax (λ bv → ∃-syntax (λ ov →
      (Witness.mem w at a ↦ av)
    × (Witness.mem w at b ↦ bv)
    × (Witness.mem w at out ↦ ov)
    × (fits-in av (lt-bits bits) ≡ true)
    × (fits-in bv (lt-bits bits) ≡ true)
    × (ov ≡ from-bool (bits-lt (take (lt-bits bits) (to-le-bits av))
                               (take (lt-bits bits) (to-le-bits bv)))))))

holds w (clause-guard-disj out i) =
  ∃-syntax (λ ov → ∃-syntax (λ iv →
      (Witness.mem w at out ↦ ov)
    × (Witness.mem w at i ↦ iv)
    × ((ov ≡ 0ᶠ) ⊎ (iv ≡ 1ᶠ))))

holds w (clause-pi-from-wire entry wire) =
  ∃-syntax (λ wv → ∃-syntax (λ pv →
      (Witness.mem w at wire ↦ wv)
    × (pi-lookup (Witness.pis w) entry ≡ just pv)
    × (pv ≡ wv)))

holds w (clause-comm-commitment inputs outputs) =
  ∃-syntax (λ ivs → ∃-syntax (λ ovs → ∃-syntax (λ rv → ∃-syntax (λ pv →
      (mem-lookups (Witness.mem w) inputs ≡ just ivs)
    × (mem-lookups (Witness.mem w) outputs ≡ just ovs)
    × (Witness.comm-rand w ≡ just rv)
    × (pi-lookup (Witness.pis w) 1 ≡ just pv)
    × (pv ≡ transient-commit (ivs ++ ovs) rv)))))

-- Conjunctive satisfaction of a clause list.
satisfies-clauses : List Clause → Witness → Set
satisfies-clauses []       _ = ⊤
satisfies-clauses (k ∷ ks) w = holds w k × satisfies-clauses ks w

-- "If the circuit uses a comm-commitment, the witness must carry the
-- randomness; otherwise the witness's comm-rand is unconstrained
-- (the clause that would consume it is not emitted, and the prover
-- may carry a spurious randomness that is simply ignored)."
Maybe-shape : Bool → Maybe Fr → Set
Maybe-shape true  (just _) = ⊤
Maybe-shape true  nothing  = ⊥
Maybe-shape false _        = ⊤

-- Top-level satisfaction.  An assignment satisfies a circuit when:
--   • all clauses hold;
--   • the witness has comm-rand iff the circuit has-comm;
--   • the PI vector has the structural length recorded in the circuit
--     (= preamble + #declared-PIs).
record satisfies (c : Circuit) (w : Witness) : Set where
  constructor mk-sat
  field
    pi-length  : length (Witness.pis w) ≡ Circuit.pi-len c
    rand-shape : Maybe-shape (Circuit.has-comm c) (Witness.comm-rand w)
    clause-ok  : satisfies-clauses (Circuit.clauses c) w

------------------------------------------------------------------------
-- Roadmap
--
-- The Phase 2 work plan, for each instruction `i`:
--
--   • State a *per-instruction faithfulness* lemma:
--
--       per-instr-faithful : ∀ pre s s' i
--         → (well-formedness, producer-safety hypotheses)
--         → R-instr pre s i s'
--         ↔ (∃ extension `w` of `wires-of s` to `wires-of s'`
--              such that  satisfies-clauses (clauses-of i) w)
--
--   • Discharge it by case analysis on `i`.  The three §6.5 cases —
--     `not`, `reconstitute-field`, `less-than` (also `assert` for the
--     bit-known side) — must thread a producer-obligation premise.
--
-- The bridging function `witness-of : Preprocessed → ProofPreimage →
-- Witness` is to be defined as follows:
--
--   witness-of s pre =
--     mk-witness (Preprocessed.memory s)
--                (Preprocessed.pis    s)
--                (case (do-comm src , comm-commitment pre) of …)
--
-- The top-level theorem to be discharged in Phase 4:
--
--   P5 : ∀ src pre s
--       → well-formed src
--       → producer-safe src
--       → R src pre s ↔ satisfies (circuit src) (witness-of s pre)
--
-- which then replaces the postulate `circuit-faithful` in
-- zkir-v2.Properties.
------------------------------------------------------------------------
