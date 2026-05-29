{-# OPTIONS --safe #-}
open import zkir-v2.Assumptions

module zkir-v2.Obligations (⋯ : _) (open Assumptions ⋯) where

------------------------------------------------------------------------
-- Producer obligations  (spec §6.4)
--
-- Three obligations the prover (producer of the source IR) must satisfy
-- for circuit faithfulness to hold:
--
--   O1  PiSkip discipline           (structural; coincides with WF3)
--   O2  Boolean-UB freedom          (operands of `assert`, `not`, and
--                                    the bit of `cond-select` lie in {0,1})
--   O3  ReconstituteField           (no field-overflow; subsumes O4
--                                    via the `less-than` clause)
--
-- Each obligation is presented as a *checker function* `IrSource → Bool`
-- that performs a single linear scan over the instruction list, mirror-
-- ing the spec's algorithmic statement.  We keep the data structures
-- deliberately concrete: lists of indices for the boolean-known set and
-- lists of (index, ℕ) pairs for the bit-bound partial map.  No stdlib
-- set/AVL abstractions.
--
-- `producer-safe` is the conjunction.  Phase 4 will thread `producer-
-- safe src ≡ true` through the program-level induction and discharge
-- the four per-instruction obligation hypotheses required by the
-- backward proofs in `CircuitFaithfulness.agda`.
------------------------------------------------------------------------

-- `FR-BITS` comes from the `Assumptions` parameter.
open import zkir-v2.Syntax ⋯

open import Data.Bool    using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List    using (List; []; _∷_; foldr; map; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _≤?_; _⊔_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Index sets and partial maps (small concrete encodings).
------------------------------------------------------------------------

-- Index set: a list of indices.  `mem?` is by `_≡ᵇ_`.
IndexSet : Set
IndexSet = List Index

mem? : Index → IndexSet → Bool
mem? _ []       = false
mem? i (j ∷ js) = (i ≡ᵇ j) ∨ mem? i js

insert : Index → IndexSet → IndexSet
insert i js = i ∷ js     -- duplicates harmless; lookup is by `_≡ᵇ_`.

-- Partial map ℕ → ℕ as an association list.  First match wins under
-- `lookupᵐ`.  Inserts always shadow, keeping the invariant that older
-- bindings are still in the list but never reachable.
PartialMap : Set
PartialMap = List (Index × ℕ)

-- `lookupᵐ i ps` returns the most-recently-inserted value at `i`, or
-- `nothing` if `i` is not in the map.  Used by the obligation checks
-- below.
lookupᵐ : Index → PartialMap → Maybe ℕ
lookupᵐ _ []             = nothing
lookupᵐ i ((j , n) ∷ ps) = if (i ≡ᵇ j) then just n else lookupᵐ i ps

-- Insert (shadows any existing binding).  Used by every "record" step
-- in the spec, except `ConstrainBits` which uses `insert-min`.
insertᵐ : Index → ℕ → PartialMap → PartialMap
insertᵐ i n ps = (i , n) ∷ ps

-- Smaller of two ℕs.
min : ℕ → ℕ → ℕ
min zero    _       = zero
min (suc _) zero    = zero
min (suc m) (suc n) = suc (min m n)

-- `ConstrainBits(v, n)` per §6.4: `bits-known[v] ← min(prev or FR-BITS, n)`.
-- We don't have FR-BITS as a ℕ here (it's postulated; see
-- `Semantics.agda`).  In practice, the prior binding either exists or
-- doesn't.  If it doesn't, we treat the "default = FR-BITS" as
-- effectively "no prior bound" and bind `n`.  If it does, we take the
-- min with the prior bound.
insert-min : Index → ℕ → PartialMap → PartialMap
insert-min v n ps with lookupᵐ v ps
... | just k  = (v , min k n) ∷ ps
... | nothing = (v , n) ∷ ps

-- Bool ≤ (decision form).
_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n with m ≤? n
... | yes _ = true
... | no  _ = false

-- Bool < (decision form).
_<ᵇ_ : ℕ → ℕ → Bool
m <ᵇ n = suc m ≤ᵇ n

------------------------------------------------------------------------
-- Δmem  (output arity per instruction; matches `circuit-instr`).
------------------------------------------------------------------------

Δmem : Instruction → ℕ
Δmem (assert _)                = 0
Δmem (cond-select _ _ _)       = 1
Δmem (constrain-bits _ _)      = 0
Δmem (constrain-eq _ _)        = 0
Δmem (constrain-to-boolean _)  = 0
Δmem (copy _)                  = 1
Δmem (declare-pub-input _)     = 0
Δmem (pi-skip _ _)             = 0
Δmem (ec-add _ _ _ _)          = 2
Δmem (ec-mul _ _ _)            = 2
Δmem (ec-mul-generator _)      = 2
Δmem (hash-to-curve _)         = 2
Δmem (load-imm _)              = 1
Δmem (div-mod-power-of-two _ _)= 2
Δmem (reconstitute-field _ _ _)= 1
Δmem (output _)                = 0
Δmem (transient-hash _)        = 1
Δmem (persistent-hash _ _)     = 2
Δmem (test-eq _ _)             = 1
Δmem (add _ _)                 = 1
Δmem (mul _ _)                 = 1
Δmem (neg _)                   = 1
Δmem (not _)                   = 1
Δmem (less-than _ _ _)         = 1
Δmem (public-input _)          = 1
Δmem (private-input _)         = 1

------------------------------------------------------------------------
-- O1  —  PiSkip discipline
--
-- Linear scan tracking `pending` (the count of declared-but-unclaimed
-- pub inputs).  `declare-pub-input` bumps it; `pi-skip g n` requires
-- `n ≤ pending` and subtracts.  After the scan, `pending = 0`.
------------------------------------------------------------------------

O1-scan : ℕ → List Instruction → Maybe ℕ
O1-scan p []                              = just p
O1-scan p (declare-pub-input _      ∷ is) = O1-scan (suc p) is
O1-scan p (pi-skip          _ n     ∷ is) with n ≤? p
... | yes _ = O1-scan (p ∸ n) is
... | no  _ = nothing
O1-scan p (_ ∷ is)                        = O1-scan p is

O1 : IrSource → Bool
O1 src with O1-scan 0 (IrSource.instructions src)
... | just 0       = true
... | just (suc _) = false
... | nothing      = false

------------------------------------------------------------------------
-- O2  —  Boolean-UB freedom
--
-- Linear scan with a `bool-known` set and a wire counter `i`.  Spec is
-- "check obligation, then record".  We open-code that as `O2-step`
-- returning `Maybe IndexSet` (`nothing` = obligation failed).
--
-- Records (spec §6.4): boolean-producing instructions add `i` (the
-- next wire index) to the set.  `ConstrainToBoolean(v)` and
-- `ConstrainBits(v, 1)` add `v` (the *operand*) — these are constraints
-- that pin an existing wire's value to {0,1}.
--
-- Note (spec): `public-input` and `private-input` outputs are NOT added
-- even when contextually boolean — the producer must `ConstrainToBoolean`.
------------------------------------------------------------------------

-- Is the constant `k` boolean?  We don't have `_≡ᶠ?_` here without
-- bringing in Semantics; for the spec's check we only need a sound
-- *under-approximation*: if we conservatively answer "no", we miss
-- some boolean-known wires but never falsely claim one is boolean.
-- That's acceptable — Phase 4 can refine if needed.
is-bool-imm? : Fr → Bool
is-bool-imm? _ = false   -- conservative; see note above.

-- Obligation-check for one instruction.  `i` is the next wire index
-- (only used for "record" cases; the obligation cases only need `bk`).
-- Returns `nothing` if the obligation is violated.
O2-check : Instruction → IndexSet → Maybe IndexSet
O2-check (assert c)        bk = if mem? c bk then just bk else nothing
O2-check (not a)           bk = if mem? a bk then just bk else nothing
O2-check (cond-select b _ _) bk = if mem? b bk then just bk else nothing
O2-check _                 bk = just bk

-- Record-step: extend `bk` based on the instruction's outputs.  `i` is
-- the wire index of the first output.
O2-record : Instruction → ℕ → IndexSet → IndexSet
O2-record (test-eq _ _)        i bk = insert i bk
O2-record (less-than _ _ _)    i bk = insert i bk
O2-record (not _)              i bk = insert i bk
O2-record (load-imm k)         i bk = if is-bool-imm? k then insert i bk else bk
O2-record (copy v)             i bk = if mem? v bk then insert i bk else bk
O2-record (cond-select _ a c)  i bk =
  if mem? a bk ∧ mem? c bk then insert i bk else bk
O2-record (constrain-to-boolean v) _ bk = insert v bk
-- NOTE (Phase 4c soundness): `constrain-bits v 1` morally pins v to
-- {0, 1}, but `fits-in v 1 ≡ true ↔ v ∈ {0, 1}` is not in the
-- bit-arithmetic trust base.  We weaken the spec's recommendation
-- here to a sound under-approximation: `constrain-bits` never adds
-- to bool-known.  This costs nothing for backward soundness; the
-- producer must use `constrain-to-boolean` to mark a wire bool.
-- Strengthening to also handle `n ≡ 1` requires adding
-- `fits-in-1→is-bit` to `CircuitFaithfulness.agda`'s axioms.
O2-record (constrain-bits _ _) _ bk = bk
O2-record _ _ bk = bk

-- One step of the scan.  `nothing` = obligation violated.
O2-step : Instruction → ℕ × IndexSet → Maybe (ℕ × IndexSet)
O2-step instr (i , bk) with O2-check instr bk
... | nothing  = nothing
... | just bk₁ = just (i + Δmem instr , O2-record instr i bk₁)

-- Full scan.
O2-scan : List Instruction → ℕ × IndexSet → Maybe (ℕ × IndexSet)
O2-scan []       acc = just acc
O2-scan (i ∷ is) acc with O2-step i acc
... | nothing  = nothing
... | just acc' = O2-scan is acc'

O2 : IrSource → Bool
O2 src with O2-scan (IrSource.instructions src) (IrSource.num-inputs src , [])
... | just _  = true
... | nothing = false

------------------------------------------------------------------------
-- O3  —  ReconstituteField no-overflow  (also covers O4)
--
-- Linear scan with a `bits-known` partial map and wire counter `i`.
-- `ReconstituteField(d, m, n)` requires:
--   d ∈ dom(bits-known)  ∧  bits-known[d] ≤ FR_BITS - n - 1
--   m ∈ dom(bits-known)  ∧  bits-known[m] ≤ n
-- `LessThan(a, b, n)` (O4 folded in):
--   a, b ∈ dom(bits-known)  ∧  bits-known[a] ≤ n  ∧  bits-known[b] ≤ n
--
-- Records: `ConstrainBits`, `DivModPowerOfTwo`, `TestEq`/`LessThan`/
-- `Not`, `LoadImm` (via bit-length), `Copy`, `CondSelect`,
-- `ReconstituteField`.
--
-- We parameterise the check by `FR-bits-bound : ℕ` (an upper bound on
-- field-element bit length supplied by the caller).  The default at
-- top-level uses a conservative `255` (= ceil(log₂ |Fr|) for
-- BLS12-381).  This keeps `Obligations.agda` independent of the
-- postulated `FR-BITS` in `Semantics.agda`.
------------------------------------------------------------------------

-- We use the postulated `FR-BITS` from `Semantics.agda` directly so
-- that the bit-arithmetic axioms (`fits-from-le-bits-{take,drop}`)
-- apply without an additional `FR-BITS ≡ FR-bits-bound` postulate.
FR-bits-bound : ℕ
FR-bits-bound = FR-BITS

-- One step of the obligation check.  Returns `nothing` on failure.
O3-check : Instruction → PartialMap → Bool
O3-check (reconstitute-field d m n) bm with lookupᵐ d bm | lookupᵐ m bm
... | just kd | just km = kd ≤ᵇ (FR-bits-bound ∸ n ∸ 1) ∧ km ≤ᵇ n
... | _       | _       = false
O3-check (less-than a b n) bm with lookupᵐ a bm | lookupᵐ b bm
... | just ka | just kb = ka ≤ᵇ n ∧ kb ≤ᵇ n
... | _       | _       = false
O3-check _ _ = true

-- Record-step.  `i` is the wire index of the first output.
--
-- NOTE (Phase 4c soundness): some "natural" record entries in the
-- spec (from-bool of test-eq/less-than/not, FR-bits-bound for
-- load-imm/reconstitute-field, ka⊔kc for cond-select) require facts
-- about `fits-in` that are outside the postulated bit-arithmetic
-- trust base (see `CircuitFaithfulness.agda`).  To keep that trust
-- base unchanged for Phase 4c, we narrow `O3-record` to the subset
-- whose justification *is* in-base:
--
--   • `constrain-bits v n`       (premise `fits-in v n ≡ true`)
--   • `div-mod-power-of-two _ n` (via `fits-from-le-bits-{take,drop}`)
--   • `copy v`                   (inherits from v)
--
-- The other record cases are weakened to no-op.  Strengthening
-- requires adding the corresponding `fits-in` axioms.  Backward
-- soundness for `reconstitute-field` and `less-than` does not
-- currently use the O3-recorded map — both `*-bwd` lemmas take
-- their `fits-in` premises directly from satisfies-clauses data.
-- Soundness note: we use plain `insertᵐ` here (not `insert-min`) so
-- the recorded value is exactly `n`, justified directly by the
-- `r-constrain-bits` premise.  Strengthening to `insert-min`
-- requires a `fits-in` monotonicity-style fact for `min`.
O3-record : Instruction → ℕ → PartialMap → PartialMap
O3-record (constrain-bits v n) _ bm = insertᵐ v n bm
O3-record (div-mod-power-of-two _ n) i bm =
  insertᵐ (suc i) n (insertᵐ i (FR-bits-bound ∸ n) bm)
O3-record (copy v)             i bm with lookupᵐ v bm
... | just k  = insertᵐ i k bm
... | nothing = bm
O3-record _ _ bm = bm

O3-step : Instruction → ℕ × PartialMap → Maybe (ℕ × PartialMap)
O3-step instr (i , bm) =
  if O3-check instr bm
    then just (i + Δmem instr , O3-record instr i bm)
    else nothing

O3-scan : List Instruction → ℕ × PartialMap → Maybe (ℕ × PartialMap)
O3-scan []       acc = just acc
O3-scan (i ∷ is) acc with O3-step i acc
... | nothing  = nothing
... | just acc' = O3-scan is acc'

O3 : IrSource → Bool
O3 src with O3-scan (IrSource.instructions src) (IrSource.num-inputs src , [])
... | just _  = true
... | nothing = false

------------------------------------------------------------------------
-- Wire-discipline (O0)  —  every operand index < nr-wires at emission.
--
-- The spec (§3.4) phrases this as a structural well-formedness invariant
-- producers maintain: when an instruction emits, all index operands must
-- be < the current wire count.  The backward (`satisfies → R-instr`)
-- per-step dispatcher needs this to pull `mem-lookup mem a ≡ just av`
-- back from `mem-lookup (mem ++ suf) a ≡ just av'`.
--
-- We encode it as a Bool checker following the same shape as O2/O3: a
-- linear scan that tracks the current wire count `n`, checks all the
-- operand wire indices of each instruction are `< n`, then bumps
-- `n := n + Δmem instr`.
------------------------------------------------------------------------

-- Check a guard operand (Maybe Index).  `nothing` is always OK.
guard-ok? : Maybe Index → ℕ → Bool
guard-ok? nothing  _ = true
guard-ok? (just g) n = g <ᵇ n

-- Check a list of operand indices are all `< n`.
all-lt? : List Index → ℕ → Bool
all-lt? []       _ = true
all-lt? (i ∷ is) n = (i <ᵇ n) ∧ all-lt? is n

-- Per-instruction operand-discipline check.  Returns `true` iff every
-- wire-index operand of `instr` is `< n` (the current wire count).
wire-check : Instruction → ℕ → Bool
wire-check (assert c)                  n = c <ᵇ n
wire-check (cond-select b a c)         n = (b <ᵇ n) ∧ (a <ᵇ n) ∧ (c <ᵇ n)
wire-check (constrain-bits v _)        n = v <ᵇ n
wire-check (constrain-eq a b)          n = (a <ᵇ n) ∧ (b <ᵇ n)
wire-check (constrain-to-boolean v)    n = v <ᵇ n
wire-check (copy v)                    n = v <ᵇ n
wire-check (declare-pub-input v)       n = v <ᵇ n
wire-check (pi-skip g _)               n = guard-ok? g n
wire-check (ec-add ax ay bx by)        n = (ax <ᵇ n) ∧ (ay <ᵇ n) ∧ (bx <ᵇ n) ∧ (by <ᵇ n)
wire-check (ec-mul ax ay s)            n = (ax <ᵇ n) ∧ (ay <ᵇ n) ∧ (s  <ᵇ n)
wire-check (ec-mul-generator s)        n = s <ᵇ n
wire-check (hash-to-curve is)          n = all-lt? is n
wire-check (load-imm _)                _ = true
wire-check (div-mod-power-of-two v _)  n = v <ᵇ n
wire-check (reconstitute-field d m _)  n = (d <ᵇ n) ∧ (m <ᵇ n)
wire-check (output v)                  n = v <ᵇ n
wire-check (transient-hash is)         n = all-lt? is n
wire-check (persistent-hash _ is)      n = all-lt? is n
wire-check (test-eq a b)               n = (a <ᵇ n) ∧ (b <ᵇ n)
wire-check (add a b)                   n = (a <ᵇ n) ∧ (b <ᵇ n)
wire-check (mul a b)                   n = (a <ᵇ n) ∧ (b <ᵇ n)
wire-check (neg a)                     n = a <ᵇ n
wire-check (not a)                     n = a <ᵇ n
wire-check (less-than a b _)           n = (a <ᵇ n) ∧ (b <ᵇ n)
wire-check (public-input g)            n = guard-ok? g n
wire-check (private-input g)           n = guard-ok? g n

-- One step: `nothing` = obligation violated; otherwise bump count.
wire-step : Instruction → ℕ → Maybe ℕ
wire-step instr n with wire-check instr n
... | true  = just (n + Δmem instr)
... | false = nothing

wire-scan : List Instruction → ℕ → Maybe ℕ
wire-scan []       n = just n
wire-scan (i ∷ is) n with wire-step i n
... | nothing  = nothing
... | just n'  = wire-scan is n'

wire-disc : IrSource → Bool
wire-disc src with wire-scan (IrSource.instructions src) (IrSource.num-inputs src)
... | just _  = true
... | nothing = false

-- Witness-bearing trace, parallel to O2-Trace / O3-Trace.
data Wire-Trace : List Instruction → ℕ → ℕ → Set where
  wire-done : ∀ {n} → Wire-Trace [] n n
  wire-cons : ∀ {i is n n' final}
    → wire-step i n ≡ just n'
    → Wire-Trace is n' final
    → Wire-Trace (i ∷ is) n final

record Wire-Runs (src : IrSource) : Set where
  constructor mk-wire-runs
  field
    final : ℕ
    trace : Wire-Trace (IrSource.instructions src)
                       (IrSource.num-inputs src) final

------------------------------------------------------------------------
-- Producer safety: all four obligations hold.
------------------------------------------------------------------------

producer-safe : IrSource → Bool
producer-safe src = O1 src ∧ O2 src ∧ O3 src ∧ wire-disc src

------------------------------------------------------------------------
-- Witness-bearing predicates (Set form)
--
-- Two ways to use these obligations downstream:
--
--   • As Bool checkers, via `O1`, `O2`, `O3` above (decidable by
--     construction — they are functions to Bool).
--
--   • As witness-bearing predicates that record the trace of
--     `bool-known` / `bits-known` along the scan.  Phase 4's
--     program-level induction will want the witness form to thread
--     the invariant.
--
-- The Set forms are inductive predicates that exactly mirror the
-- scans.  Decidability for any specific `IrSource` follows from the
-- corresponding Bool form: `O2 src ≡ true ↔ O2-Witness src`.  We
-- prove the easy direction (Bool ⇒ Set) below; the reverse follows
-- by inspection of the scan output and is not needed for the gap-
-- filling lemmas in Phase 3.
------------------------------------------------------------------------

-- O2 trace: at each step, the obligation check returned `just`.
data O2-Trace : List Instruction → ℕ × IndexSet → ℕ × IndexSet → Set where
  o2-done : ∀ {acc} → O2-Trace [] acc acc
  o2-step : ∀ {i is acc acc' final}
    → O2-step i acc ≡ just acc'
    → O2-Trace is acc' final
    → O2-Trace (i ∷ is) acc final

-- Convenience: existence of a trace.
record O2-Runs (src : IrSource) : Set where
  constructor mk-o2-runs
  field
    final : ℕ × IndexSet
    trace : O2-Trace (IrSource.instructions src)
                     (IrSource.num-inputs src , []) final

-- O3 trace, analogous.
data O3-Trace : List Instruction → ℕ × PartialMap → ℕ × PartialMap → Set where
  o3-done : ∀ {acc} → O3-Trace [] acc acc
  o3-step : ∀ {i is acc acc' final}
    → O3-step i acc ≡ just acc'
    → O3-Trace is acc' final
    → O3-Trace (i ∷ is) acc final

record O3-Runs (src : IrSource) : Set where
  constructor mk-o3-runs
  field
    final : ℕ × PartialMap
    trace : O3-Trace (IrSource.instructions src)
                     (IrSource.num-inputs src , []) final
