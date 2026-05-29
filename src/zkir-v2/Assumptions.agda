{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Assumptions of the zkir-v2 formalization
--
-- The entire trust base of the development, collected into a single
-- structured record.  Downstream modules take an `Assumptions` value as
-- a module parameter (`module M (⋯ : _) (open Assumptions ⋯) where`),
-- so the whole development typechecks under `--safe` with no
-- `postulate`s.  No concrete BLS12-381 instantiation is provided yet;
-- the development is intentionally abstract over this interface.
--
-- Structure.  Agda forbids pattern-matching definitions between `field`
-- blocks, so the trust base is assembled in three pieces, all re-exported
-- from `Assumptions` (consumers see a single flat namespace):
--
--   1. `FieldOps`  — carrier types and field/curve/hash/commitment
--      operations (the genuine primitives, formerly postulated in
--      `Syntax`/`Semantics`).
--   2. `Derived`   — helper definitions over those operations that the
--      axiom statements refer to (formerly defined in `Semantics`/
--      `Circuit`: `to-bool`, `fits-in`, `bits-lt`, `pow2-fr`, `lt-bits`).
--   3. `Assumptions` — bundles `FieldOps`, opens `Derived`, and adds the
--      field- and bit-arithmetic axioms (formerly postulated in
--      `CircuitFaithfulness`).
------------------------------------------------------------------------

module zkir-v2.Assumptions where

open import Data.Bool  using (Bool; true; false; if_then_else_; _∧_)
import Data.Bool as Bool
open import Data.List  using (List; []; _∷_; _++_; take; drop; reverse)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat   using (ℕ; zero; suc; _+_; _∸_; _%_; _⊔_; _≤_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- (1) Primitive carrier types and operations
------------------------------------------------------------------------

record FieldOps : Set₁ where
  field
    -- Carrier types (formerly postulated in `Syntax`).
    Fr        : Set
    -- ^ BLS12-381 scalar field element (transient_crypto::curve::Fr).
    Alignment : Set
    -- ^ Byte-alignment descriptor (base_crypto::fab::Alignment).

    -- Field constants
    0ᶠ 1ᶠ : Fr

    -- Field arithmetic
    _+ᶠ_ _*ᶠ_ : Fr → Fr → Fr
    -ᶠ_       : Fr → Fr

    -- Decidable field equality
    _≡ᶠ?_ : Fr → Fr → Bool

    -- Number of bits in a field element (255 for BLS12-381 scalar field)
    FR-BITS : ℕ

    -- Little-endian bit decomposition: to-le-bits x has exactly FR-BITS entries
    to-le-bits   : Fr → List Bool
    from-le-bits : List Bool → Fr

    -- True iff the LE bit pattern represents a valid (in-range) field element
    bits-in-field : List Bool → Bool

    -- Jubjub EC operations; nothing = invalid input point(s)
    ec-add-pts       : Fr → Fr → Fr → Fr → Maybe (Fr × Fr)
    ec-mul-pt        : Fr → Fr → Fr → Maybe (Fr × Fr)
    ec-mul-gen       : Fr → Fr × Fr
    hash-to-curve-fn : List Fr → Fr × Fr

    -- Hash functions
    transient-hash-fn  : List Fr → Fr
    persistent-hash-fn : Alignment → List Fr → Fr × Fr

    -- Communications commitment: transient_commit(inputs ++ outputs, randomness)
    transient-commit : List Fr → Fr → Fr

------------------------------------------------------------------------
-- (2) Derived definitions
--
-- Ordinary (non-postulated) functions of the operations above.  They are
-- defined here, rather than inline in the `Assumptions` record, because
-- Agda does not allow pattern-matching definitions between `field`
-- blocks.  They are referred to by the axiom statements in section (3)
-- and re-exported from `Assumptions`, so downstream modules see them
-- through `open Assumptions`.  (Formerly `to-bool`/`fits-in`/`bits-lt`
-- in `Semantics`, and `pow2-fr`/`lt-bits` in `Circuit`.)
------------------------------------------------------------------------

module Derived (O : FieldOps) where
  open FieldOps O

  -- Convert Fr to Bool; nothing if not in {0, 1} (UB in the IR)
  to-bool : Fr → Maybe Bool
  to-bool x with x ≡ᶠ? 0ᶠ
  ... | true  = just false
  ... | false with x ≡ᶠ? 1ᶠ
  ...   | true  = just true
  ...   | false = nothing

  private
    all-false : List Bool → Bool
    all-false []       = true
    all-false (b ∷ bs) = Bool.not b ∧ all-false bs

  -- True iff x has no bits set at positions ≥ n (i.e. x < 2^n)
  fits-in : Fr → ℕ → Bool
  fits-in x n = all-false (drop n (to-le-bits x))

  -- bits-lt as bs: true iff the natural number represented by as (LE) is
  -- < that of bs.  Assumes both lists have the same length.
  bits-lt : List Bool → List Bool → Bool
  bits-lt as bs = go (reverse as) (reverse bs)
    where
      go : List Bool → List Bool → Bool
      go []          _          = false
      go _           []         = false
      go (false ∷ _) (true ∷ _) = true
      go (true ∷ _)  (false ∷ _) = false
      go (_ ∷ as')   (_ ∷ bs')   = go as' bs'

  -- 2^n as a field element.
  pow2-fr : ℕ → Fr
  pow2-fr zero    = 1ᶠ
  pow2-fr (suc n) = pow2-fr n +ᶠ pow2-fr n

  -- Padded bit-count used by the range-check chip.
  lt-bits : ℕ → ℕ
  lt-bits n = (n + (n % 2)) ⊔ 4

------------------------------------------------------------------------
-- (3) Assumptions: operations + derived definitions + axioms
------------------------------------------------------------------------

record Assumptions : Set₁ where
  field ops : FieldOps
  open FieldOps ops public
  open Derived  ops public

  ----------------------------------------------------------------------
  -- Axioms.
  --
  -- Two groups, both honest extensions of the operations above that the
  -- operational properties P1–P4 did not need:
  --   (a) Reflection of boolean field-equality into propositional
  --       equality, and the corresponding characterization of `to-bool`.
  --   (b) BLS12-381 scalar-field arithmetic equations.
  --   (c) Bit-decomposition / bit-arithmetic facts.
  ----------------------------------------------------------------------

  field
    -- (a) Boolean field-equality reflection.
    ≡ᶠ?-refl  : ∀ {x}   → (x ≡ᶠ? x) ≡ true
    ≡ᶠ?-true  : ∀ {x y} → (x ≡ᶠ? y) ≡ true → x ≡ y
    ≡ᶠ?-false : ∀ {x y} → ¬ (x ≡ y) → (x ≡ᶠ? y) ≡ false

    -- 1 ≠ 0 — a property of any non-trivial field (and of BLS12-381 in
    -- particular).  Needed for `not-fwd` to discharge the `bv = 1ᶠ` case.
    1ᶠ≢0ᶠ : ¬ (1ᶠ ≡ 0ᶠ)

    -- Operational characterization of `to-bool`.  Provable from the
    -- `≡ᶠ?` axioms by case analysis on the underlying `with` clauses in
    -- `to-bool`; assumed for the validation slice.
    to-bool-true   : ∀ {v} → to-bool v ≡ just true  → v ≡ 1ᶠ
    to-bool-false  : ∀ {v} → to-bool v ≡ just false → v ≡ 0ᶠ
    to-bool-of-0ᶠ  : to-bool 0ᶠ ≡ just false
    to-bool-of-1ᶠ  : to-bool 1ᶠ ≡ just true

    -- (b) BLS12-381 scalar-field axioms.
    *-zero-l : ∀ x → 0ᶠ *ᶠ x ≡ 0ᶠ
    *-one-l  : ∀ x → 1ᶠ *ᶠ x ≡ x
    +-zero-l : ∀ x → 0ᶠ +ᶠ x ≡ x
    +-zero-r : ∀ x → x +ᶠ 0ᶠ ≡ x
    +-inv-r  : ∀ x → x +ᶠ (-ᶠ x) ≡ 0ᶠ
    -ᶠ-zero  : (-ᶠ 0ᶠ) ≡ 0ᶠ

    ------------------------------------------------------------------
    -- (c) Bit-decomposition / bit-arithmetic axioms.
    --
    -- These relate `to-le-bits`/`from-le-bits`/`fits-in`/`bits-in-field`
    -- to ordinary field arithmetic.  They are mechanically true given
    -- the standard BLS12-381 LE byte encoding but would require a fairly
    -- heavy combinatorial bit-arithmetic development to discharge.
    -- Assumed for the validation slice.
    ------------------------------------------------------------------

    -- Splitting a field element at position `bits` and rebuilding it as
    -- (high · 2^bits + low) recovers the original.  Used by
    -- `div-mod-power-of-two`.  Discharging it would require a
    -- bit-arithmetic library reasoning about `to-le-bits ∘ from-le-bits`
    -- on truncated prefixes.
    bits-decomp-split : ∀ v bits
      → v ≡ (from-le-bits (drop bits (to-le-bits v)) *ᶠ pow2-fr bits)
          +ᶠ from-le-bits (take bits (to-le-bits v))

    -- `from-le-bits (take n bs)` always fits in n bits — its drop-n
    -- prefix is empty modulo the padding behaviour of
    -- `to-le-bits ∘ from-le-bits`.
    fits-from-le-bits-take : ∀ bs n
      → fits-in (from-le-bits (take n bs)) n ≡ true

    -- `from-le-bits (drop n (to-le-bits v))` fits in (FR_BITS − n) bits.
    -- This uses the invariant that `to-le-bits` has length FR_BITS.
    fits-from-le-bits-drop : ∀ v n
      → fits-in (from-le-bits (drop n (to-le-bits v))) (FR-BITS ∸ n) ≡ true

    -- Uniqueness of division with remainder.  When two pairs `(q, r)` and
    -- `(q', r')` both fit in (FR_BITS − bits, bits) and yield the same
    -- field value `q · 2^bits + r`, the pairs are equal.  Needed for the
    -- backward direction of `div-mod-power-of-two` to identify the
    -- clause-provided values with the canonical bit-decomposition.
    -- Discharging would require integer-division uniqueness on the
    -- underlying nat encoding (a standard but non-trivial fact).
    div-mod-unique : ∀ q r q' r' bits
      → fits-in r bits ≡ true
      → fits-in q (FR-BITS ∸ bits) ≡ true
      → fits-in r' bits ≡ true
      → fits-in q' (FR-BITS ∸ bits) ≡ true
      → (q *ᶠ pow2-fr bits) +ᶠ r ≡ (q' *ᶠ pow2-fr bits) +ᶠ r'
      → (q ≡ q') × (r ≡ r')

    -- Reconstitute equation, given the no-overflow premise.  When the
    -- concatenated bit pattern is in-range, the field value is exactly
    -- the natural-number sum (no modular reduction).
    reconstitute-no-overflow : ∀ dv mv bits
      → fits-in mv bits ≡ true
      → fits-in dv (FR-BITS ∸ bits) ≡ true
      → bits-in-field
          (take bits (to-le-bits mv) ++ take (FR-BITS ∸ bits) (to-le-bits dv))
          ≡ true
      → from-le-bits
          (take bits (to-le-bits mv) ++ take (FR-BITS ∸ bits) (to-le-bits dv))
        ≡ (dv *ᶠ pow2-fr bits) +ᶠ mv

    -- `lt-bits n ≥ n`, so a value fitting in n bits also fits in
    -- `lt-bits n` bits.  Specialised here rather than going via a
    -- general `n ≤ m → fits-in v n → fits-in v m`, which would require
    -- additional natural-number machinery.
    fits-in-lt-bits : ∀ v n
      → fits-in v n ≡ true
      → fits-in v (lt-bits n) ≡ true

    -- Padding the bit-count from `n` to `lt-bits n` does not change the
    -- result of `bits-lt`, provided both inputs fit in n bits (so the
    -- padded high bits are all zero).  See §5.2 footnote.
    bits-lt-pad : ∀ av bv n
      → fits-in av n ≡ true
      → fits-in bv n ≡ true
      → bits-lt (take (lt-bits n) (to-le-bits av))
                (take (lt-bits n) (to-le-bits bv))
        ≡ bits-lt (take n (to-le-bits av))
                  (take n (to-le-bits bv))

    -- Monotonicity of `fits-in`: if v fits in m bits, it fits in any
    -- larger bit-count.  A direct property of the LE bit decomposition
    -- (extra high bits beyond m are zero, hence still in range).  This
    -- is a sibling of `fits-in-lt-bits` — the specialised n=>lt-bits n
    -- form is no longer adequate once O3 tracks a refined per-wire
    -- bit-count that may be strictly less than the operand bound used in
    -- the corresponding clause (see `less-than`, `reconstitute-field`
    -- backward dispatch in `CircuitProof.agda`).
    fits-in-mono : ∀ {v m n}
      → fits-in v m ≡ true
      → m ≤ n
      → fits-in v n ≡ true

    -- Combined natural-number value fits in the field, given O3's strict
    -- divisor bound.  Specifically: if mv fits in n bits and dv fits in
    -- (FR_BITS − n − 1) bits, the concatenated LE bit pattern represents
    -- a value < 2^(FR_BITS − 1) < |Fr| for BLS12-381.  This is a sibling
    -- of `reconstitute-no-overflow` (which is the operational equation
    -- once `bits-in-field` is known) — here we *establish* the
    -- `bits-in-field` premise from the strict bit-bound on the divisor
    -- that the producer obligation O3 supplies.  Used in the backward
    -- dispatcher for `reconstitute-field`.
    bits-in-field-from-strict-bound : ∀ {dv mv n}
      → fits-in mv n ≡ true
      → fits-in dv (FR-BITS ∸ n ∸ 1) ≡ true
      → bits-in-field
          (take n (to-le-bits mv) ++ take (FR-BITS ∸ n) (to-le-bits dv))
        ≡ true
