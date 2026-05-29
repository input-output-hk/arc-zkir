{-# OPTIONS --safe #-}
open import zkir-v2.Assumptions

module zkir-v2.ObligationsSoundness (⋯ : _) (open Assumptions ⋯) where

------------------------------------------------------------------------
-- Soundness of producer obligations
--
-- For each obligation we have a static scan (in `Obligations.agda`) and
-- a witness-bearing trace predicate (`O2-Trace`/`O3-Trace`).  This
-- module proves the *connection* between those static facts and the
-- dynamic relational semantics `R-instr`/`R-instrs`:
--
--   • O2-sound  — if the scan adds `i` to bool-known, then for every
--                 reachable state with `mem-lookup mem i ≡ just v`, the
--                 value `v` is in {0, 1} (`is-bit v`).
--
--   • O3-sound  — analogous for the bits-known partial map: if the scan
--                 has `lookupᵐ bm i ≡ just n`, then `fits-in v n ≡ true`.
--
--   • integration lemma — `producer-safe-bit-evidence` extracts an
--                 `is-bit` witness for a specific operand of the next
--                 instruction in a prefix.  Phase 4d feeds this directly
--                 to the per-instruction backward lemmas in
--                 `CircuitFaithfulness.agda`.
--
-- The proof is by induction along the `R-instrs` trace, threading an
-- invariant `O2-Inv (i, bk) s` saying:
--
--   • `i ≡ length (Preprocessed.memory s)`     (index alignment)
--   • every wire in `bk` is bound to an `is-bit` value in `mem s`.
--
-- The 26-constructor case analysis on `R-instr` mirrors the 26-case
-- `O2-record` / `O3-record` discriminations.
------------------------------------------------------------------------

-- The `to-bool-*` and `fits-from-le-bits-*` axioms come from the
-- `Assumptions` parameter.
open import zkir-v2.Syntax ⋯
open import zkir-v2.Semantics ⋯
open import zkir-v2.Circuit ⋯ using (is-bit)
open import zkir-v2.Obligations ⋯

open import Data.Bool      using (Bool; true; false; _∧_; _∨_; if_then_else_)
import Data.Bool as Bool
open import Data.List      using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (length-++)
open import Data.Maybe     using (Maybe; nothing; just; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat       using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm)
open import Data.Product   using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum       using (_⊎_; inj₁; inj₂)
open import Data.Empty     using (⊥; ⊥-elim)
open import Data.Unit      using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Common helpers
------------------------------------------------------------------------

private

  -- Length of an "appended ∷[]" memory.
  length-++-one : ∀ {A : Set} (xs : List A) (y : A)
    → length (xs ++ (y ∷ [])) ≡ suc (length xs)
  length-++-one [] y = refl
  length-++-one (x ∷ xs) y = cong suc (length-++-one xs y)

  length-++-two : ∀ {A : Set} (xs : List A) (y z : A)
    → length (xs ++ (y ∷ z ∷ [])) ≡ suc (suc (length xs))
  length-++-two [] y z = refl
  length-++-two (x ∷ xs) y z = cong suc (length-++-two xs y z)

  -- Lookup at exactly `length mem` returns the appended value.
  lookup-new : ∀ (mem : List Fr) v
    → mem-lookup (mem ++ (v ∷ [])) (length mem) ≡ just v
  lookup-new []       v = refl
  lookup-new (x ∷ xs) v = lookup-new xs v

  -- Lookup at i < length mem is unchanged by appending.
  lookup-extends : ∀ (mem suffix : List Fr) i {v}
    → mem-lookup mem i ≡ just v
    → mem-lookup (mem ++ suffix) i ≡ just v
  lookup-extends []       _ _       ()
  lookup-extends (x ∷ xs) _ zero    eq = eq
  lookup-extends (x ∷ xs) s (suc i) eq = lookup-extends xs s i eq

  -- Two cells.
  lookup-new-fst : ∀ (mem : List Fr) x y
    → mem-lookup (mem ++ (x ∷ y ∷ [])) (length mem) ≡ just x
  lookup-new-fst []       x y = refl
  lookup-new-fst (z ∷ zs) x y = lookup-new-fst zs x y

  lookup-new-snd : ∀ (mem : List Fr) x y
    → mem-lookup (mem ++ (x ∷ y ∷ [])) (suc (length mem)) ≡ just y
  lookup-new-snd []       x y = refl
  lookup-new-snd (z ∷ zs) x y = lookup-new-snd zs x y

  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj = just-injective

  lookup-uniq : ∀ (mem : List Fr) (i : Index) {v w}
    → mem-lookup mem i ≡ just v
    → mem-lookup mem i ≡ just w
    → v ≡ w
  lookup-uniq _ _ p q = just-injective (trans (sym p) q)

  ------------------------------------------------------------------
  -- Bool reasoning lemmas
  ------------------------------------------------------------------

  ∧-true : ∀ {a b : Bool} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true}  {true}  refl = refl , refl
  ∧-true {true}  {false} ()
  ∧-true {false} {_}     ()

  ∨-true : ∀ {a b : Bool} → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
  ∨-true {true}  _    = inj₁ refl
  ∨-true {false} {b} eq = inj₂ eq

  ≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  ≡ᵇ-true : ∀ {m n : ℕ} → (m ≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ-true {zero}  {zero}  _    = refl
  ≡ᵇ-true {zero}  {suc _} ()
  ≡ᵇ-true {suc _} {zero}  ()
  ≡ᵇ-true {suc m} {suc n} eq   = cong suc (≡ᵇ-true {m} {n} eq)

  if-true : ∀ {A : Set} (b : Bool) {x y : A}
    → b ≡ true → (if b then x else y) ≡ x
  if-true _ refl = refl

------------------------------------------------------------------------
-- Set membership: `mem? i bk ≡ true ↔ i ∈ bk` (small-step view)
------------------------------------------------------------------------

private

  -- "Was i found in bk by the lookup?" — propositional form.
  data _∈bk_ : Index → IndexSet → Set where
    here  : ∀ {i j js} → (i ≡ᵇ j) ≡ true → i ∈bk (j ∷ js)
    there : ∀ {i j js} → i ∈bk js → i ∈bk (j ∷ js)

  mem?-true : ∀ {i bk} → mem? i bk ≡ true → i ∈bk bk
  mem?-true {i} {[]}     ()
  mem?-true {i} {j ∷ js} eq with ∨-true {i ≡ᵇ j} {mem? i js} eq
  ... | inj₁ eq1 = here  eq1
  ... | inj₂ eq2 = there (mem?-true eq2)

  ∈bk-insert-keep : ∀ {i j bk} → i ∈bk bk → i ∈bk insert j bk
  ∈bk-insert-keep = there

  ∈bk-insert-new : ∀ i bk → i ∈bk insert i bk
  ∈bk-insert-new i bk = here (≡ᵇ-refl i)

------------------------------------------------------------------------
-- O2 step invariant
--
-- `O2-Inv (i, bk) s` says:
--   • `i ≡ length (memory s)`              — the scan's wire counter is
--                                            in sync with the program
--                                            memory length.
--   • every `j ∈ bk` looks up to an
--     `is-bit` value in `memory s`.
------------------------------------------------------------------------

-- Strict ordering on ℕ (small reflective definition local to this
-- module to avoid stdlib `_<_` proof-shape friction).
private
  data _ℕ<_ : ℕ → ℕ → Set where
    z<s : ∀ {n} → zero ℕ< suc n
    s<s : ∀ {m n} → m ℕ< n → suc m ℕ< suc n

  ℕ<-suc : ∀ {m n} → m ℕ< n → m ℕ< suc n
  ℕ<-suc z<s        = z<s
  ℕ<-suc (s<s p)    = s<s (ℕ<-suc p)

  ℕ<-self-suc : ∀ n → n ℕ< suc n
  ℕ<-self-suc zero    = z<s
  ℕ<-self-suc (suc n) = s<s (ℕ<-self-suc n)

  -- Length of `mem ++ (v ∷ [])` is `suc (length mem)` — already
  -- proven as `length-++-one`; we re-use that here.
  ℕ<-step-of-record : ∀ {j i} → j ℕ< i → j ℕ< suc i
  ℕ<-step-of-record = ℕ<-suc

  ℕ<-step-of-record-2 : ∀ {j i} → j ℕ< i → j ℕ< suc (suc i)
  ℕ<-step-of-record-2 p = ℕ<-suc (ℕ<-suc p)

record O2-Inv (acc : ℕ × IndexSet) (s : Preprocessed) : Set where
  constructor mk-o2-inv
  field
    idx-sync  : proj₁ acc ≡ length (Preprocessed.memory s)
    bk-bound  : ∀ {j} → j ∈bk (proj₂ acc) → j ℕ< proj₁ acc
    bit-known : ∀ {j v}
      → j ∈bk (proj₂ acc)
      → mem-lookup (Preprocessed.memory s) j ≡ just v
      → is-bit v

open O2-Inv public

------------------------------------------------------------------------
-- Base case: at the initial state with `acc = (num-inputs src, [])` the
-- invariant holds vacuously.
------------------------------------------------------------------------

init-mem : ∀ {src pre s₀}
  → init-state src pre ≡ just s₀
  → Preprocessed.memory s₀ ≡ ProofPreimage.inputs pre
init-mem {src} {pre} {s₀} eq
  with length (ProofPreimage.inputs pre) ≡ᵇ IrSource.num-inputs src
     | IrSource.do-communications-commitment src
     | ProofPreimage.comm-commitment pre
     | eq
... | true  | false | _       | refl = refl
... | true  | true  | just _  | refl = refl

o2-inv-init : ∀ {src pre s₀}
  → init-state src pre ≡ just s₀
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → O2-Inv (IrSource.num-inputs src , []) s₀
o2-inv-init {src} {pre} {s₀} eq lenEq =
  mk-o2-inv idx-eq empty-bk-bound empty-bk-bits
  where
    mem-eq : Preprocessed.memory s₀ ≡ ProofPreimage.inputs pre
    mem-eq = init-mem {src} {pre} {s₀} eq

    len-eq : length (Preprocessed.memory s₀) ≡ length (ProofPreimage.inputs pre)
    len-eq = cong length mem-eq

    idx-eq : IrSource.num-inputs src ≡ length (Preprocessed.memory s₀)
    idx-eq = trans (sym lenEq) (sym len-eq)

    empty-bk-bound : ∀ {j} → j ∈bk [] → j ℕ< IrSource.num-inputs src
    empty-bk-bound ()

    empty-bk-bits : ∀ {j v}
      → j ∈bk []
      → mem-lookup (Preprocessed.memory s₀) j ≡ just v
      → is-bit v
    empty-bk-bits ()

------------------------------------------------------------------------
-- Per-step preservation
--
-- The workhorse:  if `R-instr pre s instr s'` and `O2-step instr acc ≡
-- just acc'` and the invariant held at `(acc, s)`, then it holds at
-- `(acc', s')`.
--
-- We case-split on `instr`.  For each case we know the shape of `s'`
-- (from the R-instr constructor) and the shape of `acc'` (from
-- `O2-step`).  Memory-preserving cases inherit the invariant; memory-
-- extending cases need a fresh witness for the new wire index when
-- the scan adds it to `bk`.
------------------------------------------------------------------------

private

  ------------------------------------------------------------------
  -- Push-mem and lookup helpers
  ------------------------------------------------------------------

  -- The "post" memory of push-mem s newv is mem s ++ (newv ∷ []).
  push-mem-mem : ∀ s newv
    → Preprocessed.memory (push-mem s newv) ≡ Preprocessed.memory s ++ (newv ∷ [])
  push-mem-mem s newv = refl

  -- Going from a lookup in mem ++ (newv ∷ []) back to mem, given j ≠ length mem.
  -- Equivalently: if `mem-lookup (mem ++ (newv ∷ [])) j ≡ just v` and
  -- the new-index value would have been `newv` (so v ≢ newv ∨ j ≠ length mem)…
  -- Simpler: we use a *positional* characterization.

  -- `mem-lookup (mem ++ (newv ∷ [])) j` returns:
  --   • the original `mem-lookup mem j` if defined,
  --   • else `just newv` at j = length mem,
  --   • else nothing.
  lookup-shrink-or-new : ∀ (mem : List Fr) newv j v
    → mem-lookup (mem ++ (newv ∷ [])) j ≡ just v
    → (mem-lookup mem j ≡ just v) ⊎ ((j ≡ length mem) × (v ≡ newv))
  lookup-shrink-or-new []       newv zero    .newv refl = inj₂ (refl , refl)
  lookup-shrink-or-new []       newv (suc j) v    ()
  lookup-shrink-or-new (x ∷ xs) newv zero    .x   refl = inj₁ refl
  lookup-shrink-or-new (x ∷ xs) newv (suc j) v    eq
    with lookup-shrink-or-new xs newv j v eq
  ... | inj₁ p        = inj₁ p
  ... | inj₂ (q , vr) = inj₂ (cong suc q , vr)

  -- Two-cell variant: lookup in mem ++ (x ∷ y ∷ []) decomposes into:
  --   • lookup mem j (if j < length mem)
  --   • j = length mem with value x
  --   • j = suc (length mem) with value y
  lookup-shrink-or-new-2 : ∀ (mem : List Fr) x y j v
    → mem-lookup (mem ++ (x ∷ y ∷ [])) j ≡ just v
    → (mem-lookup mem j ≡ just v)
    ⊎ ((j ≡ length mem) × (v ≡ x))
    ⊎ ((j ≡ suc (length mem)) × (v ≡ y))
  lookup-shrink-or-new-2 []       x y zero          .x refl = inj₂ (inj₁ (refl , refl))
  lookup-shrink-or-new-2 []       x y (suc zero)    .y refl = inj₂ (inj₂ (refl , refl))
  lookup-shrink-or-new-2 []       x y (suc (suc j)) v  ()
  lookup-shrink-or-new-2 (z ∷ zs) x y zero          .z refl = inj₁ refl
  lookup-shrink-or-new-2 (z ∷ zs) x y (suc j)       v  eq
    with lookup-shrink-or-new-2 zs x y j v eq
  ... | inj₁ p              = inj₁ p
  ... | inj₂ (inj₁ (q , vr)) = inj₂ (inj₁ (cong suc q , vr))
  ... | inj₂ (inj₂ (q , vr)) = inj₂ (inj₂ (cong suc q , vr))

  ------------------------------------------------------------------
  -- Convenience: `if b then just x else nothing ≡ just y` gives
  -- `b ≡ true × x ≡ y`.
  ------------------------------------------------------------------

  if-just-then-true : ∀ {A : Set} (b : Bool) {x y : A}
    → (if b then just x else nothing) ≡ just y
    → b ≡ true × x ≡ y
  if-just-then-true true  refl = refl , refl
  if-just-then-true false ()

------------------------------------------------------------------------
-- O2 step preservation
--
-- Given the invariant at (i, bk) and a successful one-step transition
-- `R-instr pre s instr s'` matched by `O2-step instr (i, bk) ≡ just
-- acc'`, the invariant holds at (acc', s').
--
-- The proof is a 26-case dispatch on `R-instr`.  Most cases are
-- trivial; the "boolean-producing" instructions (test-eq, less-than,
-- not, cond-select with both branches in bk, copy of bk member) need
-- the actual witness derivation.
------------------------------------------------------------------------

-- Witness lemma:  `from-bool b` is always is-bit.
from-bool-is-bit : ∀ (b : Bool) → is-bit (from-bool b)
from-bool-is-bit false = inj₁ refl
from-bool-is-bit true  = inj₂ refl

-- Witness lemma:  if `to-bool v ≡ just _`, then `is-bit v`.
to-bool→is-bit : ∀ {v sel} → to-bool v ≡ just sel → is-bit v
to-bool→is-bit {sel = true}  eq = inj₂ (to-bool-true  eq)
to-bool→is-bit {sel = false} eq = inj₁ (to-bool-false eq)

-- A `(mem-lookup mem a >>= to-bool) ≡ just sel` can be decomposed into
-- the underlying field value plus a `to-bool` evidence on it.
extract-to-bool : ∀ (mem : List Fr) (a : Index) {sel}
  → (mem-lookup mem a >>= to-bool) ≡ just sel
  → ∃-syntax λ av → mem-lookup mem a ≡ just av × to-bool av ≡ just sel
extract-to-bool mem a {sel} eq = aux (mem-lookup mem a) refl eq
  where
    aux : ∀ (m : Maybe Fr)
        → mem-lookup mem a ≡ m
        → (m >>= to-bool) ≡ just sel
        → ∃-syntax λ av → mem-lookup mem a ≡ just av × to-bool av ≡ just sel
    aux nothing  _    ()
    aux (just x) m-eq eq' = x , m-eq , eq'

------------------------------------------------------------------------
-- Step-preservation helpers (frame lemmas)
--
-- We package the three classes of memory transitions:
--   • frame-no-grow         : memory unchanged.
--   • frame-push-mem        : memory grows by one cell.
--   • frame-push-mem-2      : memory grows by two cells.
-- Each takes the (i, bk)-side accumulator update and produces the
-- post-state O2-Inv.
------------------------------------------------------------------------

private

  ------------------------------------------------------------------
  -- (a) Memory unchanged, bk unchanged.
  ------------------------------------------------------------------
  frame-no-grow-no-record : ∀ {i bk s s'}
    → Preprocessed.memory s' ≡ Preprocessed.memory s
    → O2-Inv (i , bk) s
    → O2-Inv (i , bk) s'
  frame-no-grow-no-record {i = i} {bk = bk} {s = s} {s' = s'} mem-eq inv =
    mk-o2-inv
      (trans (idx-sync inv) (sym (cong length mem-eq)))
      (bk-bound inv)
      (λ j∈bk lookup-eq →
        bit-known inv j∈bk
          (trans (cong (λ m → mem-lookup m _) (sym mem-eq)) lookup-eq))

  ------------------------------------------------------------------
  -- (b) Memory unchanged, bk extended by `v` (constrain-* cases).
  --     Requires v ℕ< i (operand lookup-bound) and an is-bit witness
  --     for the value at v.
  ------------------------------------------------------------------
  frame-no-grow-add-v : ∀ {i bk s s' v vv}
    → Preprocessed.memory s' ≡ Preprocessed.memory s
    → mem-lookup (Preprocessed.memory s) v ≡ just vv
    → is-bit vv
    → O2-Inv (i , bk) s
    → O2-Inv (i , insert v bk) s'
  frame-no-grow-add-v {i = i} {bk = bk} {s = s} {s' = s'} {v = v} {vv = vv}
                       mem-eq lv vv-bit inv =
    mk-o2-inv idx-eq bnd bits
    where
      idx-eq : i ≡ length (Preprocessed.memory s')
      idx-eq = trans (idx-sync inv) (sym (cong length mem-eq))

      v<i : v ℕ< i
      v<i = lookup-< (Preprocessed.memory s) v vv lv (idx-sync inv)
        where
          -- A successful mem-lookup at index j proves j < length mem.
          lookup-< : ∀ (mem : List Fr) (j : Index) (val : Fr)
            → mem-lookup mem j ≡ just val
            → ∀ {i₀} → i₀ ≡ length mem
            → j ℕ< i₀
          lookup-< (x ∷ xs) zero    val refl refl = z<s
          lookup-< (x ∷ xs) (suc j) val eq   refl =
            s<s (lookup-< xs j val eq refl)
          lookup-< []       _       _   ()   _

      bnd : ∀ {j} → j ∈bk (insert v bk) → j ℕ< i
      bnd {j} (here eq) = subst (_ℕ< i) (sym (≡ᵇ-true eq)) v<i
      bnd (there p) = bk-bound inv p

      bits : ∀ {j w} → j ∈bk (insert v bk)
                     → mem-lookup (Preprocessed.memory s') j ≡ just w
                     → is-bit w
      bits {j} {w} (here eqj) lookup-eq =
        let j≡v : j ≡ v
            j≡v = ≡ᵇ-true eqj

            lookup-at-v : mem-lookup (Preprocessed.memory s) v ≡ just w
            lookup-at-v =
              subst (λ k → mem-lookup (Preprocessed.memory s) k ≡ just w)
                    j≡v
                    (trans (cong (λ m → mem-lookup m j) (sym mem-eq)) lookup-eq)

            vv≡w : vv ≡ w
            vv≡w = just-injective (trans (sym lv) lookup-at-v)
        in subst is-bit vv≡w vv-bit
      bits (there p) lookup-eq =
        bit-known inv p (trans (cong (λ m → mem-lookup m _) (sym mem-eq)) lookup-eq)

  ------------------------------------------------------------------
  -- (c) Memory grows by one cell (push-mem s newv), bk unchanged.
  ------------------------------------------------------------------
  frame-push-mem-no-record : ∀ {i bk s newv}
    → O2-Inv (i , bk) s
    → O2-Inv (suc i , bk) (push-mem s newv)
  frame-push-mem-no-record {i = i} {bk = bk} {s = s} {newv = newv} inv =
    mk-o2-inv idx-eq bnd bits
    where
      mem  = Preprocessed.memory s
      mem' = mem ++ (newv ∷ [])

      idx-eq : suc i ≡ length (Preprocessed.memory (push-mem s newv))
      idx-eq = trans (cong suc (idx-sync inv)) (sym (length-++-one mem newv))

      bnd : ∀ {j} → j ∈bk bk → j ℕ< suc i
      bnd p = ℕ<-suc (bk-bound inv p)

      bits : ∀ {j w} → j ∈bk bk
                     → mem-lookup (Preprocessed.memory (push-mem s newv)) j ≡ just w
                     → is-bit w
      bits {j} {w} j∈ lookup-eq
        with lookup-shrink-or-new mem newv j w lookup-eq
      ... | inj₁ p          = bit-known inv j∈ p
      ... | inj₂ (j≡L , w≡) =
        -- j = length mem ⇒ j ≡ i.  But bk-bound says j ℕ< i, i.e. j < i.
        -- Contradiction.
        ⊥-elim (ℕ<-irrefl (subst (_ℕ< i) j-is-i (bk-bound inv j∈)))
        where
          ℕ<-irrefl : ∀ {n} → ¬ (n ℕ< n)
          ℕ<-irrefl (s<s p) = ℕ<-irrefl p

          j-is-i : j ≡ i
          j-is-i = trans j≡L (sym (idx-sync inv))

  ------------------------------------------------------------------
  -- (d) Memory grows by one cell, bk records the new index.
  --     Requires an is-bit witness for the appended value.
  ------------------------------------------------------------------
  frame-push-mem-record : ∀ {i bk s newv}
    → is-bit newv
    → O2-Inv (i , bk) s
    → O2-Inv (suc i , insert i bk) (push-mem s newv)
  frame-push-mem-record {i = i} {bk = bk} {s = s} {newv = newv}
                         newv-bit inv =
    mk-o2-inv idx-eq bnd bits
    where
      mem  = Preprocessed.memory s
      mem' = mem ++ (newv ∷ [])

      idx-eq : suc i ≡ length (Preprocessed.memory (push-mem s newv))
      idx-eq = trans (cong suc (idx-sync inv)) (sym (length-++-one mem newv))

      bnd : ∀ {j} → j ∈bk (insert i bk) → j ℕ< suc i
      bnd {j} (here eq) = subst (_ℕ< suc i) (sym (≡ᵇ-true eq)) (ℕ<-self-suc i)
      bnd (there p) = ℕ<-suc (bk-bound inv p)

      bits : ∀ {j w} → j ∈bk (insert i bk)
                     → mem-lookup (Preprocessed.memory (push-mem s newv)) j ≡ just w
                     → is-bit w
      bits {j} {w} (here eqj) lookup-eq =
        let j≡i : j ≡ i
            j≡i = ≡ᵇ-true eqj

            lookup-at-i : mem-lookup (mem ++ (newv ∷ [])) i ≡ just w
            lookup-at-i =
              subst (λ k → mem-lookup (mem ++ (newv ∷ [])) k ≡ just w)
                    j≡i lookup-eq

            lookup-at-i-new : mem-lookup (mem ++ (newv ∷ [])) i ≡ just newv
            lookup-at-i-new =
              subst (λ k → mem-lookup (mem ++ (newv ∷ [])) k ≡ just newv)
                    (sym (idx-sync inv))
                    (lookup-new mem newv)

            newv≡w : newv ≡ w
            newv≡w = just-injective (trans (sym lookup-at-i-new) lookup-at-i)
        in subst is-bit newv≡w newv-bit
      bits {j} {w} (there p) lookup-eq
        with lookup-shrink-or-new mem newv j w lookup-eq
      ... | inj₁ q          = bit-known inv p q
      ... | inj₂ (j≡L , _)  =
        ⊥-elim (ℕ<-irrefl (subst (_ℕ< i) (trans j≡L (sym (idx-sync inv))) (bk-bound inv p)))
        where
          ℕ<-irrefl : ∀ {n} → ¬ (n ℕ< n)
          ℕ<-irrefl (s<s p') = ℕ<-irrefl p'

  ------------------------------------------------------------------
  -- (e) Memory grows by two cells (push-mem2 or iterated push-mem),
  --     bk unchanged.  Applies to ec-add, ec-mul, ec-mul-generator,
  --     hash-to-curve, div-mod-power-of-two, persistent-hash, etc.
  ------------------------------------------------------------------
  frame-push-mem-2-no-record-app : ∀ {i bk s x y}
    → O2-Inv (i , bk) s
    → O2-Inv (suc (suc i) , bk) (push-mem2 s x y)
  frame-push-mem-2-no-record-app {i = i} {bk = bk} {s = s} {x = x} {y = y} inv =
    mk-o2-inv idx-eq bnd bits
    where
      mem  = Preprocessed.memory s

      idx-eq : suc (suc i) ≡ length (Preprocessed.memory (push-mem2 s x y))
      idx-eq = trans (cong suc (cong suc (idx-sync inv)))
                     (sym (length-++-two mem x y))

      bnd : ∀ {j} → j ∈bk bk → j ℕ< suc (suc i)
      bnd p = ℕ<-suc (ℕ<-suc (bk-bound inv p))

      bits : ∀ {j w} → j ∈bk bk
                     → mem-lookup (Preprocessed.memory (push-mem2 s x y)) j ≡ just w
                     → is-bit w
      bits {j} {w} j∈ lookup-eq
        with lookup-shrink-or-new-2 mem x y j w lookup-eq
      ... | inj₁ p          = bit-known inv j∈ p
      ... | inj₂ (inj₁ (j≡L , _))      =
        ⊥-elim (ℕ<-irrefl
                  (subst (_ℕ< i) (trans j≡L (sym (idx-sync inv)))
                                 (bk-bound inv j∈)))
        where
          ℕ<-irrefl : ∀ {n} → ¬ (n ℕ< n)
          ℕ<-irrefl (s<s p') = ℕ<-irrefl p'
      ... | inj₂ (inj₂ (j≡sucL , _))  =
        ⊥-elim (ℕ<-strict-irrefl
                  (subst (_ℕ< i)
                         (trans j≡sucL (cong suc (sym (idx-sync inv))))
                         (bk-bound inv j∈)))
        where
          -- suc i ℕ< i is impossible.
          ℕ<-strict-irrefl : ∀ {n} → ¬ (suc n ℕ< n)
          ℕ<-strict-irrefl {suc n} (s<s p) = ℕ<-strict-irrefl p

------------------------------------------------------------------------
-- Main per-step preservation theorem (O2)
--
-- Threads the invariant across a single `R-instr` step matched by a
-- successful `O2-step`.  The proof is a 26-case `R-instr` dispatch.
--
-- The shape is:  given `O2-Inv (i, bk) s`, `R-instr pre s instr s'`,
-- and `O2-step instr (i, bk) ≡ just (i', bk')`, conclude `O2-Inv (i',
-- bk') s'`.
------------------------------------------------------------------------

-- Helper that pairs the post-state's memory equality with the iterated
-- push-mem shape used by `div-mod-power-of-two`.
private
  push-mem-push-mem-mem : ∀ s x y
    → Preprocessed.memory (push-mem (push-mem s x) y)
      ≡ (Preprocessed.memory s ++ (x ∷ [])) ++ (y ∷ [])
  push-mem-push-mem-mem s x y = refl

  -- Bridge between `mem ++ (x ∷ y ∷ [])` and `(mem ++ (x ∷ [])) ++ (y ∷ [])`.
  ++-assoc-2 : ∀ {A : Set} (mem : List A) (x y : A)
    → (mem ++ (x ∷ [])) ++ (y ∷ []) ≡ mem ++ (x ∷ y ∷ [])
  ++-assoc-2 []       x y = refl
  ++-assoc-2 (z ∷ zs) x y = cong (z ∷_) (++-assoc-2 zs x y)

  -- Apply the push-mem2 frame to a state shaped by iterated push-mem.
  frame-push-mem-push-mem-no-record : ∀ {i bk s x y}
    → O2-Inv (i , bk) s
    → O2-Inv (suc (suc i) , bk) (push-mem (push-mem s x) y)
  frame-push-mem-push-mem-no-record {i = i} {bk = bk} {s = s} {x = x} {y = y} inv =
    let mem    = Preprocessed.memory s
        mem-eq : Preprocessed.memory (push-mem (push-mem s x) y)
               ≡ Preprocessed.memory (push-mem2 s x y)
        mem-eq = ++-assoc-2 mem x y
        inv2 : O2-Inv (suc (suc i) , bk) (push-mem2 s x y)
        inv2 = frame-push-mem-2-no-record-app inv
    in mk-o2-inv
         (trans (idx-sync inv2) (sym (cong length mem-eq)))
         (bk-bound inv2)
         (λ j∈ lookup-eq → bit-known inv2 j∈
                                     (trans (cong (λ m → mem-lookup m _) (sym mem-eq))
                                            lookup-eq))

------------------------------------------------------------------------
-- consume-pub-out / consume-priv preserve memory (re-exported here).
------------------------------------------------------------------------

private
  consume-pub-out-mem-eq : ∀ s {v s'}
    → consume-pub-out s ≡ just (v , s')
    → Preprocessed.memory s' ≡ Preprocessed.memory s
  consume-pub-out-mem-eq s eq with Preprocessed.pub-out-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))

  consume-priv-mem-eq : ∀ s {v s'}
    → consume-priv s ≡ just (v , s')
    → Preprocessed.memory s' ≡ Preprocessed.memory s
  consume-priv-mem-eq s eq with Preprocessed.priv-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))

  -- Sugar:  i + 0 ≡ i  and  i + 1 ≡ suc i  and  i + 2 ≡ suc (suc i).
  +-0-r : ∀ i → i + 0 ≡ i
  +-0-r = +-identityʳ

  +-1-r : ∀ i → i + 1 ≡ suc i
  +-1-r i = trans (+-suc i 0) (cong suc (+-identityʳ i))

  +-2-r : ∀ i → i + 2 ≡ suc (suc i)
  +-2-r i = trans (+-suc i 1) (cong suc (+-1-r i))

  -- Coerce an O2-Inv along an idx-counter equality.
  inv-coerce-idx : ∀ {i i' bk s}
    → i ≡ i'
    → O2-Inv (i , bk) s
    → O2-Inv (i' , bk) s
  inv-coerce-idx refl inv = inv

------------------------------------------------------------------------
-- Main per-step preservation theorem (O2)
--
-- The result `O2-step instr (i, bk) ≡ just acc'` constrains `acc'` to
-- be `(i + Δmem instr , O2-record instr i bk₁)` where `bk₁` comes from
-- `O2-check`.  By case analysis on the constructor of `R-instr`, we
-- unfold `O2-step` and apply the matching frame helper.
--
-- We split the 26 cases across two private lemmas for readability:
--   • `o2-preserve-mem-equal`  — instructions with Δmem = 0
--   • `o2-preserve-mem-grow1`  — instructions with Δmem = 1
--   • `o2-preserve-mem-grow2`  — instructions with Δmem = 2
------------------------------------------------------------------------

o2-preserve : ∀ {pre s s' instr i bk acc'}
  → O2-Inv (i , bk) s
  → R-instr pre s instr s'
  → O2-step instr (i , bk) ≡ just acc'
  → O2-Inv acc' s'
-- ============================================================
-- Δmem = 0 instructions
-- ============================================================

-- assert: bk-check requires `c ∈ bk`; record is a no-op.
o2-preserve {instr = assert c} {i = i} {bk = bk} inv
            (r-assert lookup-c-bool) step-eq
  with mem? c bk | step-eq
... | true  | refl = inv-coerce-idx (sym (+-0-r i))
                                    (frame-no-grow-no-record refl inv)
-- (the `mem? c bk ≡ false` case is excluded because step-eq would be nothing)

-- constrain-eq: record is a no-op.
o2-preserve {instr = constrain-eq a b} {i = i} inv
            (r-constrain-eq _ _ _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)

-- constrain-bits: record is a no-op under our conservative under-
-- approximation (see Obligations.agda; we don't add v to bool-known
-- even when bits ≡ 1, because `fits-in v 1 ≡ true → is-bit v` is
-- outside the postulated bit-arithmetic trust base).
o2-preserve {instr = constrain-bits v bits} {i = i} inv
            (r-constrain-bits _ _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)

-- constrain-to-boolean v: record adds `v` to bk.
o2-preserve {s = s} {instr = constrain-to-boolean v} {i = i} {bk = bk} inv
            (r-constrain-to-boolean {b = b} lookup-bool) refl =
  let av , lv , to-eq = extract-to-bool (Preprocessed.memory s) v lookup-bool
  in inv-coerce-idx (sym (+-0-r i))
       (frame-no-grow-add-v refl lv (to-bool→is-bit to-eq) inv)

-- declare-pub-input: memory unchanged (push-pi), record is a no-op.
o2-preserve {instr = declare-pub-input v} {i = i} inv
            (r-declare-pub-input _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)

-- pi-skip active / inactive: memory unchanged (push-skip; pi-skip
-- inactive additionally modifies pub-in-idx, which doesn't touch
-- memory), no record.
o2-preserve {instr = pi-skip g n} {i = i} inv
            (r-pi-skip-active _ _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)
o2-preserve {instr = pi-skip g n} {i = i} inv
            (r-pi-skip-inactive _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)

-- output: memory unchanged (push-output), record is a no-op.
o2-preserve {instr = output v} {i = i} inv
            (r-output _) refl =
  inv-coerce-idx (sym (+-0-r i)) (frame-no-grow-no-record refl inv)

-- ============================================================
-- Δmem = 1 instructions
-- ============================================================

-- cond-select bit a b: check requires `bit ∈ bk`; record adds new
-- index `i` to bk if BOTH `a ∈ bk` AND `b ∈ bk` (else no record).
o2-preserve {instr = cond-select bit a b} {i = i} {bk = bk} inv
            (r-cond-select {sel = sel} {av = av} {bv = bv}
                           lookup-bit la lb) step-eq
  with mem? bit bk in bit-eq | step-eq
... | true  | step-eq'
  with mem? a bk in a-eq | mem? b bk in b-eq | step-eq'
... | true  | true  | refl =
  inv-coerce-idx (sym (+-1-r i))
    (frame-push-mem-record (if-sel-bit sel) inv)
  where
    av-bit : is-bit av
    av-bit = bit-known inv (mem?-true {bk = bk} a-eq) la

    bv-bit : is-bit bv
    bv-bit = bit-known inv (mem?-true {bk = bk} b-eq) lb

    if-sel-bit : ∀ (s : Bool) → is-bit (if s then av else bv)
    if-sel-bit true  = av-bit
    if-sel-bit false = bv-bit
... | true  | false | refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)
... | false | _     | refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- copy v: record adds new index `i` to bk if `v ∈ bk`.
o2-preserve {instr = copy v} {i = i} {bk = bk} inv
            (r-copy {v = vv} lv) refl
  with mem? v bk in v-eq
... | true  =
  let vv-bit : is-bit vv
      vv-bit = bit-known inv (mem?-true {bk = bk} v-eq) lv
  in inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-record vv-bit inv)
... | false =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- load-imm k: under our conservative `is-bool-imm? _ = false`,
-- O2-record never adds for load-imm.  (See Obligations.agda.)
o2-preserve {instr = load-imm k} {i = i} inv r-load-imm refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- add / mul / neg: push-mem, never record.
o2-preserve {instr = add a b} {i = i} inv (r-add _ _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)
o2-preserve {instr = mul a b} {i = i} inv (r-mul _ _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)
o2-preserve {instr = neg a} {i = i} inv (r-neg _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- test-eq: push-mem (from-bool (av ≡ᶠ? bv)) — always records, value
-- is from-bool of a Bool, hence is-bit.
o2-preserve {instr = test-eq a b} {i = i} inv (r-test-eq {av = av} {bv = bv} _ _) refl =
  inv-coerce-idx (sym (+-1-r i))
    (frame-push-mem-record (from-bool-is-bit (av ≡ᶠ? bv)) inv)

-- not: check requires `a ∈ bk`; always records (from-bool (Bool.not b)).
o2-preserve {instr = not a} {i = i} {bk = bk} inv (r-not {b = b} _) step-eq
  with mem? a bk | step-eq
... | true  | refl =
  inv-coerce-idx (sym (+-1-r i))
    (frame-push-mem-record (from-bool-is-bit (Bool.not b)) inv)

-- less-than: push-mem (from-bool (bits-lt …)) — always records.
o2-preserve {instr = less-than a b bits} {i = i} inv
            (r-less-than {av = av} {bv = bv} _ _ _) refl =
  inv-coerce-idx (sym (+-1-r i))
    (frame-push-mem-record
      (from-bool-is-bit
        (bits-lt (take bits (to-le-bits av)) (take bits (to-le-bits bv)))) inv)

-- reconstitute-field: push-mem of a single combined value; Δmem = 1.
-- No record.
o2-preserve {instr = reconstitute-field d m bits} {i = i} inv
            (r-reconstitute-field _ _ _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- public-input inactive: push-mem s 0ᶠ.  No record.
o2-preserve {instr = public-input g} {i = i} inv
            (r-public-input-inactive _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- public-input active: push-mem s₁ v where s₁ has same memory as s.
-- After push, memory grows by one.  No record.
o2-preserve {s = s} {instr = public-input g} {i = i} inv
            (r-public-input-active {s₁ = s₁} _ s₁-eq) refl =
  let mem-s₁ : Preprocessed.memory s₁ ≡ Preprocessed.memory s
      mem-s₁ = consume-pub-out-mem-eq s s₁-eq
      -- inv at s₁ (memory equal):
      inv-s₁ : O2-Inv (i , _) s₁
      inv-s₁ = frame-no-grow-no-record mem-s₁ inv
  in inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv-s₁)

-- private-input inactive / active: same shape as public-input.
o2-preserve {instr = private-input g} {i = i} inv
            (r-private-input-inactive _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)
o2-preserve {s = s} {instr = private-input g} {i = i} inv
            (r-private-input-active {s₁ = s₁} _ s₁-eq) refl =
  let mem-s₁ : Preprocessed.memory s₁ ≡ Preprocessed.memory s
      mem-s₁ = consume-priv-mem-eq s s₁-eq
      inv-s₁ : O2-Inv (i , _) s₁
      inv-s₁ = frame-no-grow-no-record mem-s₁ inv
  in inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv-s₁)

-- transient-hash: push-mem (transient-hash-fn vs).  No record.
o2-preserve {instr = transient-hash xs} {i = i} inv
            (r-transient-hash _) refl =
  inv-coerce-idx (sym (+-1-r i)) (frame-push-mem-no-record inv)

-- ============================================================
-- Δmem = 2 instructions
-- ============================================================

-- ec-add, ec-mul, ec-mul-generator, hash-to-curve, persistent-hash:
-- push-mem2 s x y.  No record.
o2-preserve {instr = ec-add a_x a_y b_x b_y} {i = i} inv
            (r-ec-add _ _ _ _ _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-2-no-record-app inv)
o2-preserve {instr = ec-mul a_x a_y scalar} {i = i} inv
            (r-ec-mul _ _ _ _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-2-no-record-app inv)
o2-preserve {instr = ec-mul-generator scalar} {i = i} inv
            (r-ec-mul-generator _ _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-2-no-record-app inv)
o2-preserve {instr = hash-to-curve xs} {i = i} inv
            (r-hash-to-curve _ _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-2-no-record-app inv)
o2-preserve {instr = persistent-hash a xs} {i = i} inv
            (r-persistent-hash _ _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-2-no-record-app inv)

-- div-mod-power-of-two: push-mem (push-mem s x) y — iterated.  No
-- record.  Uses the special frame for iterated push-mem.
o2-preserve {instr = div-mod-power-of-two v bits} {i = i} inv
            (r-div-mod-power-of-two _) refl =
  inv-coerce-idx (sym (+-2-r i)) (frame-push-mem-push-mem-no-record inv)

------------------------------------------------------------------------
-- Multi-step preservation, indexed by O2-Trace
--
-- Given the invariant at (acc, s) and a parallel run of R-instrs and
-- O2-Trace, conclude the invariant at (final, s').
------------------------------------------------------------------------

o2-preserve* : ∀ {pre s s' acc final is}
  → O2-Inv acc s
  → R-instrs pre s is s'
  → O2-Trace is acc final
  → O2-Inv final s'
o2-preserve* inv r-done o2-done = inv
o2-preserve* inv (r-step r rs) (o2-step step-eq tr) =
  o2-preserve* (o2-preserve inv r step-eq) rs tr

------------------------------------------------------------------------
-- Whole-program O2 soundness
--
-- Given:
--   • `R src pre s` (the source is faithfully realised by state s),
--     which packages an initial state s₀ and an `R-instrs pre s₀ … s`
--     run;
--   • `O2-Runs src` (the O2 scan completed with final = (i, bk));
--   • the WF1 hypothesis `length inputs ≡ num-inputs src`
-- conclude: for every wire `j` in the final `bk`, looking up `j` in
-- `mem s` yields an `is-bit` value.
--
-- The hypothesis `length inputs ≡ num-inputs src` is automatic at the
-- top level (it follows from `R src pre s` via `init-state` which
-- enforces it), but threading it explicitly keeps the proof local.
------------------------------------------------------------------------

O2-sound : ∀ {src pre s}
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → R src pre s
  → (run : O2-Runs src)
  → ∀ {j v}
  → j ∈bk (proj₂ (O2-Runs.final run))
  → mem-lookup (Preprocessed.memory s) j ≡ just v
  → is-bit v
O2-sound {src} {pre} {s} lenEq (s₀ , init-eq , r-instrs , _ , _)
         (mk-o2-runs final trace) =
  let inv₀ : O2-Inv (IrSource.num-inputs src , []) s₀
      inv₀ = o2-inv-init {src} {pre} {s₀} init-eq lenEq

      inv-final : O2-Inv final s
      inv-final = o2-preserve* inv₀ r-instrs trace
  in bit-known inv-final

------------------------------------------------------------------------
-- Integration lemma for Phase 4d
--
-- Phase 4d's program-level induction (`satisfies-clauses→R-instrs`)
-- iterates over the instruction list, threading a "current synth
-- state" and a "current preprocess state".  At each obligation-
-- bearing instruction (`assert`, `not`, `cond-select`'s bit operand),
-- it needs an `is-bit` witness for the operand.
--
-- The shape we expose is parametric in *position-in-the-trace*:
-- given the invariant at some `(i, bk)` paired with state `s`, and
-- the fact that the O2-check for the next instruction passes (i.e.
-- the relevant operand is `mem? c bk ≡ true`), produce the `is-bit`
-- witness.
--
-- Three specialisations (for the three boolean-obligation cases in
-- §5.2):  assert, not, cond-select-bit.  All share the same proof:
-- `mem?-true → ∈bk → bit-known inv`.
------------------------------------------------------------------------

-- Extract `is-bit v` for an operand `c` known to be in bool-known.
o2-known-is-bit : ∀ {i bk s c v}
  → O2-Inv (i , bk) s
  → mem? c bk ≡ true
  → mem-lookup (Preprocessed.memory s) c ≡ just v
  → is-bit v
o2-known-is-bit {bk = bk} inv mem-eq lookup-eq =
  bit-known inv (mem?-true {bk = bk} mem-eq) lookup-eq

-- O2's whole-program scan, decomposed: any non-failing prefix
-- (`O2-Trace prefix-is start acc-mid`) yields an intermediate scan
-- state.  Phase 4d will thread this alongside `R-instrs`.
--
-- More directly: given an `R-instrs pre s₀ prefix-is s` trace plus a
-- matched O2-Trace, the invariant holds at `s` with accumulator
-- `acc-mid`.  Then for the *next* instruction, if its O2-check
-- succeeds with operand in bk, we get the is-bit witness.

-- Whole-program O2-Inv at an intermediate state.
o2-inv-mid : ∀ {src pre s₀ s prefix-is acc-mid}
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → init-state src pre ≡ just s₀
  → R-instrs pre s₀ prefix-is s
  → O2-Trace prefix-is (IrSource.num-inputs src , []) acc-mid
  → O2-Inv acc-mid s
o2-inv-mid {src} {pre} {s₀ = s₀} lenEq init-eq r-instrs trace =
  o2-preserve* (o2-inv-init {src} {pre} {s₀} init-eq lenEq) r-instrs trace

------------------------------------------------------------------------
-- O3 soundness
--
-- O3 tracks a `bits-known` partial map.  Per the spec, several
-- O3-record cases require facts about `fits-in` that are outside the
-- current bit-arithmetic trust base (e.g., `fits-in (from-bool b) 1
-- ≡ true`, `fits-in v FR-bits-bound ≡ true` for arbitrary v).  To
-- keep the trust base unchanged for Phase 4c, we narrow `O3-record`
-- to the subset whose justification *is* in the trust base:
--
--   • `constrain-bits v n`            (premise `fits-in v n ≡ true`)
--   • `div-mod-power-of-two _ n`     (via `fits-from-le-bits-{take,drop}`)
--   • `copy v`                       (inherits from v)
--
-- The other record cases (test-eq, less-than, not, load-imm,
-- cond-select, reconstitute-field) are weakened to no-op.  This
-- costs nothing for backward soundness — Phase 4d's
-- `reconstitute-field-bwd` and `less-than-bwd` already take the
-- relevant `fits-in` premises directly from the satisfies-clauses
-- data, so they don't need O3 evidence externally.
--
-- The invariant is analogous to O2's:
--   • i ≡ length mem
--   • for each (j, n) in the map (via lookupᵐ), the lookup at j
--     yields a value v with `fits-in v n ≡ true`.
------------------------------------------------------------------------

-- NOTE: O3 soundness is left as a future deliverable (Phase 4c').
-- The invariant, framework, and easy cases are stated below; the
-- 26-constructor dispatch is identical in structure to o2-preserve.
-- See `o2-preserve` for the template.
--
-- For Phase 4d we postulate the integration lemma in the *unused*
-- direction (`O3-sound` is not needed by current backward proofs in
-- CircuitFaithfulness.agda — they take `fits-in` premises directly).
--
-- If a future revision starts using O3 to discharge gap-filling
-- premises (e.g., for an as-yet-unwritten `less-than-bwd` variant
-- that does need O3 evidence), the framework here is ready to be
-- extended.

-- O3 step invariant: pairs (i, bm) where i = length mem, and for
-- every (j, n) in bm (via lookupᵐ), the memory entry at j fits in n
-- bits.  Also tracks bm-bound: every domain element is `< i`.
record O3-Inv (acc : ℕ × PartialMap) (s : Preprocessed) : Set where
  constructor mk-o3-inv
  field
    idx-sync   : proj₁ acc ≡ length (Preprocessed.memory s)
    bm-bound   : ∀ {j n}
      → lookupᵐ j (proj₂ acc) ≡ just n
      → j ℕ< proj₁ acc
    bits-known : ∀ {j n v}
      → lookupᵐ j (proj₂ acc) ≡ just n
      → mem-lookup (Preprocessed.memory s) j ≡ just v
      → fits-in v n ≡ true

open O3-Inv public

-- Initial state: empty map vacuously satisfies the invariant.
o3-inv-init : ∀ {src pre s₀}
  → init-state src pre ≡ just s₀
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → O3-Inv (IrSource.num-inputs src , []) s₀
o3-inv-init {src} {pre} {s₀} eq lenEq =
  mk-o3-inv idx-eq empty-bound empty
  where
    mem-eq : Preprocessed.memory s₀ ≡ ProofPreimage.inputs pre
    mem-eq = init-mem {src} {pre} {s₀} eq

    idx-eq : IrSource.num-inputs src ≡ length (Preprocessed.memory s₀)
    idx-eq = trans (sym lenEq) (sym (cong length mem-eq))

    empty-bound : ∀ {j n} → lookupᵐ j [] ≡ just n → j ℕ< IrSource.num-inputs src
    empty-bound ()

    empty : ∀ {j n v}
          → lookupᵐ j [] ≡ just n
          → mem-lookup (Preprocessed.memory s₀) j ≡ just v
          → fits-in v n ≡ true
    empty ()

------------------------------------------------------------------------
-- O3 helpers for lookupᵐ / insertᵐ.
------------------------------------------------------------------------

private

  -- Coerce an O3-Inv along an idx-counter equality.  Mirrors
  -- inv-coerce-idx on the O2 side; avoids the underscore-laden
  -- `subst (λ k → O3-Inv (k , _) _)` shape that confuses meta inference.
  o3-inv-coerce-idx : ∀ {i i' bm s}
    → i ≡ i'
    → O3-Inv (i , bm) s
    → O3-Inv (i' , bm) s
  o3-inv-coerce-idx refl inv = inv

  -- lookupᵐ on insertᵐ: at the same key, returns the new value; at a
  -- different key, falls through.  (Note: insertᵐ shadows old bindings.)
  lookupᵐ-insertᵐ-eq : ∀ (k : Index) n bm
    → lookupᵐ k (insertᵐ k n bm) ≡ just n
  lookupᵐ-insertᵐ-eq k n bm rewrite ≡ᵇ-refl k = refl

  -- lookupᵐ on insertᵐ at a different key: pure fall-through.  We
  -- characterise via the boolean condition.
  lookupᵐ-insertᵐ-shape : ∀ (j k : Index) n bm
    → lookupᵐ j (insertᵐ k n bm) ≡
        (if j ≡ᵇ k then just n else lookupᵐ j bm)
  lookupᵐ-insertᵐ-shape j k n bm = refl

  -- An `n ℕ< i` follows from a successful mem-lookup at index n in a
  -- memory of length matching i.
  lookup-bound : ∀ (mem : List Fr) (j : Index) {val : Fr}
    → mem-lookup mem j ≡ just val
    → ∀ {i₀} → i₀ ≡ length mem
    → j ℕ< i₀
  lookup-bound (x ∷ xs) zero    eq   refl = z<s
  lookup-bound (x ∷ xs) (suc j) eq   refl =
    s<s (lookup-bound xs j eq refl)
  lookup-bound []       _       ()   _

  ℕ<-irrefl-base : ∀ {n} → ¬ (n ℕ< n)
  ℕ<-irrefl-base (s<s p') = ℕ<-irrefl-base p'

  ℕ<-strict-irrefl-base : ∀ {n} → ¬ (suc n ℕ< n)
  ℕ<-strict-irrefl-base {suc n} (s<s p) = ℕ<-strict-irrefl-base p

  -- Frame for O3: memory unchanged, map unchanged.
  o3-frame-no-grow : ∀ {i bm s s'}
    → Preprocessed.memory s' ≡ Preprocessed.memory s
    → O3-Inv (i , bm) s
    → O3-Inv (i , bm) s'
  o3-frame-no-grow {i = i} {bm = bm} {s = s} {s' = s'} mem-eq inv =
    mk-o3-inv
      (trans (idx-sync inv) (sym (cong length mem-eq)))
      (bm-bound inv)
      (λ look lookup-eq →
        bits-known inv look
          (trans (cong (λ m → mem-lookup m _) (sym mem-eq)) lookup-eq))

  -- Frame for O3: memory grows by one cell (push-mem), map unchanged.
  o3-frame-push-mem : ∀ {i bm s newv}
    → O3-Inv (i , bm) s
    → O3-Inv (suc i , bm) (push-mem s newv)
  o3-frame-push-mem {i = i} {bm = bm} {s = s} {newv = newv} inv =
    mk-o3-inv idx-eq bnd bits
    where
      mem  = Preprocessed.memory s
      idx-eq : suc i ≡ length (Preprocessed.memory (push-mem s newv))
      idx-eq = trans (cong suc (idx-sync inv)) (sym (length-++-one mem newv))

      bnd : ∀ {j n} → lookupᵐ j bm ≡ just n → j ℕ< suc i
      bnd look = ℕ<-suc (bm-bound inv look)

      bits : ∀ {j n v} → lookupᵐ j bm ≡ just n
                       → mem-lookup (Preprocessed.memory (push-mem s newv)) j ≡ just v
                       → fits-in v n ≡ true
      bits {j} {n} {v} look lookup-eq
        with lookup-shrink-or-new mem newv j v lookup-eq
      ... | inj₁ p           = bits-known inv look p
      ... | inj₂ (j≡L , _)   =
        ⊥-elim (ℕ<-irrefl-base (subst (_ℕ< i)
                                       (trans j≡L (sym (idx-sync inv)))
                                       (bm-bound inv look)))

  -- Frame for O3: memory grows by two cells (push-mem2), map unchanged.
  o3-frame-push-mem-2 : ∀ {i bm s x y}
    → O3-Inv (i , bm) s
    → O3-Inv (suc (suc i) , bm) (push-mem2 s x y)
  o3-frame-push-mem-2 {i = i} {bm = bm} {s = s} {x = x} {y = y} inv =
    mk-o3-inv idx-eq bnd bits
    where
      mem = Preprocessed.memory s
      idx-eq : suc (suc i) ≡ length (Preprocessed.memory (push-mem2 s x y))
      idx-eq = trans (cong suc (cong suc (idx-sync inv)))
                     (sym (length-++-two mem x y))

      bnd : ∀ {j n} → lookupᵐ j bm ≡ just n → j ℕ< suc (suc i)
      bnd look = ℕ<-suc (ℕ<-suc (bm-bound inv look))

      bits : ∀ {j n v} → lookupᵐ j bm ≡ just n
                       → mem-lookup (Preprocessed.memory (push-mem2 s x y)) j ≡ just v
                       → fits-in v n ≡ true
      bits {j} {n} {v} look lookup-eq
        with lookup-shrink-or-new-2 mem x y j v lookup-eq
      ... | inj₁ p                  = bits-known inv look p
      ... | inj₂ (inj₁ (j≡L , _))   =
        ⊥-elim (ℕ<-irrefl-base (subst (_ℕ< i)
                                       (trans j≡L (sym (idx-sync inv)))
                                       (bm-bound inv look)))
      ... | inj₂ (inj₂ (j≡sL , _))  =
        ⊥-elim (ℕ<-strict-irrefl-base
                  (subst (_ℕ< i)
                         (trans j≡sL (cong suc (sym (idx-sync inv))))
                         (bm-bound inv look)))

  -- Frame for O3: iterated push-mem (for div-mod-power-of-two).
  o3-frame-push-mem-push-mem : ∀ {i bm s x y}
    → O3-Inv (i , bm) s
    → O3-Inv (suc (suc i) , bm) (push-mem (push-mem s x) y)
  o3-frame-push-mem-push-mem {i = i} {bm = bm} {s = s} {x = x} {y = y} inv =
    let mem    = Preprocessed.memory s
        mem-eq : Preprocessed.memory (push-mem (push-mem s x) y)
               ≡ Preprocessed.memory (push-mem2 s x y)
        mem-eq = ++-assoc-2 mem x y
        inv2 : O3-Inv (suc (suc i) , bm) (push-mem2 s x y)
        inv2 = o3-frame-push-mem-2 inv
    in mk-o3-inv
         (trans (idx-sync inv2) (sym (cong length mem-eq)))
         (bm-bound inv2)
         (λ look lookup-eq → bits-known inv2 look
                              (trans (cong (λ m → mem-lookup m _) (sym mem-eq))
                                     lookup-eq))

  ------------------------------------------------------------------
  -- O3-record-supporting helpers
  ------------------------------------------------------------------

  -- After insertᵐ k n bm, a lookup at k returns n; at j ≠ k, it
  -- falls through to lookupᵐ j bm.
  -- Combined with the boolean condition, this gives a decomposition.
  lookupᵐ-insertᵐ-cases : ∀ (j k : Index) n bm {m}
    → lookupᵐ j (insertᵐ k n bm) ≡ just m
    → ((j ≡ k) × (m ≡ n)) ⊎ (lookupᵐ j bm ≡ just m)
  lookupᵐ-insertᵐ-cases j k n bm eq with j ≡ᵇ k in jk-eq
  ... | true  = inj₁ (≡ᵇ-true jk-eq , sym (just-injective eq))
  ... | false = inj₂ eq

  -- insert-min v n bm: if old binding exists, it's now (v, min k n);
  -- otherwise (v, n).  We simplify by splitting into two cases.
  -- For now, expose only the *easy* case: when the lookup falls
  -- through to lookupᵐ j bm (no new binding consulted).  The
  -- substantive case (j ≡ v) is handled by direct case analysis on
  -- `lookupᵐ v bm` in the caller.

  -- Simplified shape used by the constrain-bits case: prove that
  -- after `insertᵐ v n bm`, a lookup at v gives n directly (no min
  -- machinery needed under the conservative O3-record).

  -- Frame: memory unchanged, map extended with `(v, n)`.  Requires:
  --   • v ℕ< i  (operand bound from a successful mem-lookup),
  --   • fits-in vv n ≡ true  (witness from the R-instr premise),
  --   • mem-lookup s v ≡ just vv.
  o3-frame-no-grow-insert-v : ∀ {i bm s s' v n vv}
    → Preprocessed.memory s' ≡ Preprocessed.memory s
    → mem-lookup (Preprocessed.memory s) v ≡ just vv
    → fits-in vv n ≡ true
    → O3-Inv (i , bm) s
    → O3-Inv (i , insertᵐ v n bm) s'
  o3-frame-no-grow-insert-v {i = i} {bm = bm} {s = s} {s' = s'}
                              {v = v} {n = n} {vv = vv}
                              mem-eq lv fits-vv inv =
    mk-o3-inv idx-eq bnd bits
    where
      idx-eq : i ≡ length (Preprocessed.memory s')
      idx-eq = trans (idx-sync inv) (sym (cong length mem-eq))

      v<i : v ℕ< i
      v<i = lookup-bound (Preprocessed.memory s) v lv (idx-sync inv)

      bnd : ∀ {j n'} → lookupᵐ j (insertᵐ v n bm) ≡ just n' → j ℕ< i
      bnd {j} look with lookupᵐ-insertᵐ-cases j v n bm look
      ... | inj₁ (j≡v , _)  = subst (_ℕ< i) (sym j≡v) v<i
      ... | inj₂ fall       = bm-bound inv fall

      bits : ∀ {j n' v'} → lookupᵐ j (insertᵐ v n bm) ≡ just n'
                         → mem-lookup (Preprocessed.memory s') j ≡ just v'
                         → fits-in v' n' ≡ true
      bits {j} {n'} {v'} look lookup-eq
        with lookupᵐ-insertᵐ-cases j v n bm look
      ... | inj₁ (j≡v , n'≡n) =
        let lookup-at-v : mem-lookup (Preprocessed.memory s) v ≡ just v'
            lookup-at-v =
              subst (λ k → mem-lookup (Preprocessed.memory s) k ≡ just v')
                    j≡v
                    (trans (cong (λ m → mem-lookup m j) (sym mem-eq)) lookup-eq)
            vv≡v' : vv ≡ v'
            vv≡v' = just-injective (trans (sym lv) lookup-at-v)
        in subst (λ z → fits-in z n' ≡ true) vv≡v'
                 (subst (λ z → fits-in vv z ≡ true) (sym n'≡n) fits-vv)
      ... | inj₂ fall =
        bits-known inv fall
          (trans (cong (λ m → mem-lookup m _) (sym mem-eq)) lookup-eq)

  -- Frame for div-mod-power-of-two: memory grows by two cells (via
  -- iterated push-mem), and the map gets two new entries.  Requires
  -- `fits-in` witnesses for the two appended values.
  o3-frame-push-mem-2-insert-2 : ∀ {i bm s x y nx ny}
    → fits-in x nx ≡ true
    → fits-in y ny ≡ true
    → O3-Inv (i , bm) s
    → O3-Inv (suc (suc i) , insertᵐ (suc i) ny (insertᵐ i nx bm))
             (push-mem (push-mem s x) y)
  o3-frame-push-mem-2-insert-2 {i = i} {bm = bm} {s = s}
                                 {x = x} {y = y} {nx = nx} {ny = ny}
                                 fx fy inv =
    mk-o3-inv idx-eq bnd bits
    where
      mem    = Preprocessed.memory s
      mem-eq : Preprocessed.memory (push-mem (push-mem s x) y)
             ≡ mem ++ (x ∷ y ∷ [])
      mem-eq = ++-assoc-2 mem x y

      idx-eq : suc (suc i)
             ≡ length (Preprocessed.memory (push-mem (push-mem s x) y))
      idx-eq = trans (cong suc (cong suc (idx-sync inv)))
                     (trans (sym (length-++-two mem x y))
                            (sym (cong length mem-eq)))

      bnd : ∀ {j n'} → lookupᵐ j (insertᵐ (suc i) ny (insertᵐ i nx bm)) ≡ just n'
                     → j ℕ< suc (suc i)
      bnd {j} look with lookupᵐ-insertᵐ-cases j (suc i) ny (insertᵐ i nx bm) look
      ... | inj₁ (j≡sucI , _) =
        subst (_ℕ< suc (suc i)) (sym j≡sucI) (ℕ<-self-suc (suc i))
      ... | inj₂ fall1 with lookupᵐ-insertᵐ-cases j i nx bm fall1
      ...   | inj₁ (j≡i , _) =
        subst (_ℕ< suc (suc i)) (sym j≡i) (ℕ<-suc (ℕ<-self-suc i))
      ...   | inj₂ fall2     = ℕ<-suc (ℕ<-suc (bm-bound inv fall2))

      bits : ∀ {j n' v'}
           → lookupᵐ j (insertᵐ (suc i) ny (insertᵐ i nx bm)) ≡ just n'
           → mem-lookup (Preprocessed.memory (push-mem (push-mem s x) y)) j
              ≡ just v'
           → fits-in v' n' ≡ true
      bits {j} {n'} {v'} look lookup-eq =
        let lookup-eq' : mem-lookup (mem ++ (x ∷ y ∷ [])) j ≡ just v'
            lookup-eq' = trans (cong (λ m → mem-lookup m j) (sym mem-eq))
                                lookup-eq
        in aux look lookup-eq'
        where
          aux : lookupᵐ j (insertᵐ (suc i) ny (insertᵐ i nx bm)) ≡ just n'
              → mem-lookup (mem ++ (x ∷ y ∷ [])) j ≡ just v'
              → fits-in v' n' ≡ true
          aux look' lookup-eq''
            with lookupᵐ-insertᵐ-cases j (suc i) ny (insertᵐ i nx bm) look'
          ... | inj₁ (j≡sucI , n'≡ny) =
            let -- lookup at suc i ≡ just y in mem ++ (x ∷ y ∷ [])
                lookup-at-sucI : mem-lookup (mem ++ (x ∷ y ∷ [])) (suc i) ≡ just y
                lookup-at-sucI =
                  subst (λ k → mem-lookup (mem ++ (x ∷ y ∷ [])) (suc k) ≡ just y)
                        (sym (idx-sync inv))
                        (lookup-new-snd mem x y)
                v'≡y : v' ≡ y
                v'≡y = just-injective
                         (trans (sym
                                  (subst (λ k → mem-lookup (mem ++ (x ∷ y ∷ [])) k
                                                ≡ just v')
                                          j≡sucI lookup-eq''))
                                lookup-at-sucI)
            in subst (λ z → fits-in z n' ≡ true) (sym v'≡y)
                     (subst (λ z → fits-in y z ≡ true) (sym n'≡ny) fy)
          ... | inj₂ fall1 with lookupᵐ-insertᵐ-cases j i nx bm fall1
          ...   | inj₁ (j≡i , n'≡nx) =
            let lookup-at-i : mem-lookup (mem ++ (x ∷ y ∷ [])) i ≡ just x
                lookup-at-i =
                  subst (λ k → mem-lookup (mem ++ (x ∷ y ∷ [])) k ≡ just x)
                        (sym (idx-sync inv))
                        (lookup-new-fst mem x y)
                v'≡x : v' ≡ x
                v'≡x = just-injective
                         (trans (sym
                                  (subst (λ k → mem-lookup (mem ++ (x ∷ y ∷ [])) k
                                                ≡ just v')
                                          j≡i lookup-eq''))
                                lookup-at-i)
            in subst (λ z → fits-in z n' ≡ true) (sym v'≡x)
                     (subst (λ z → fits-in x z ≡ true) (sym n'≡nx) fx)
          ...   | inj₂ fall2 with lookup-shrink-or-new-2 mem x y j v' lookup-eq''
          ...     | inj₁ p              = bits-known inv fall2 p
          ...     | inj₂ (inj₁ (j≡L , _)) =
            ⊥-elim (ℕ<-irrefl-base
                     (subst (_ℕ< i) (trans j≡L (sym (idx-sync inv)))
                            (bm-bound inv fall2)))
          ...     | inj₂ (inj₂ (j≡sL , _)) =
            ⊥-elim (ℕ<-strict-irrefl-base
                     (subst (_ℕ< i)
                            (trans j≡sL (cong suc (sym (idx-sync inv))))
                            (bm-bound inv fall2)))

  -- Frame for copy v when `v ∈ dom(bm)`: memory grows by one cell;
  -- the appended value is `vv` (the value at v); the map gets a new
  -- entry `(i, k)` where k is the previous bound on v.  The witness:
  -- by IH, `fits-in vv k`.
  o3-frame-push-mem-copy : ∀ {i bm s v vv k}
    → lookupᵐ v bm ≡ just k
    → mem-lookup (Preprocessed.memory s) v ≡ just vv
    → O3-Inv (i , bm) s
    → O3-Inv (suc i , insertᵐ i k bm) (push-mem s vv)
  o3-frame-push-mem-copy {i = i} {bm = bm} {s = s} {v = v} {vv = vv} {k = k}
                           look-v lv inv =
    mk-o3-inv idx-eq bnd bits
    where
      mem  = Preprocessed.memory s
      idx-eq : suc i ≡ length (Preprocessed.memory (push-mem s vv))
      idx-eq = trans (cong suc (idx-sync inv)) (sym (length-++-one mem vv))

      fits-vv-k : fits-in vv k ≡ true
      fits-vv-k = bits-known inv look-v lv

      bnd : ∀ {j n'} → lookupᵐ j (insertᵐ i k bm) ≡ just n' → j ℕ< suc i
      bnd {j} look with lookupᵐ-insertᵐ-cases j i k bm look
      ... | inj₁ (j≡i , _) = subst (_ℕ< suc i) (sym j≡i) (ℕ<-self-suc i)
      ... | inj₂ fall      = ℕ<-suc (bm-bound inv fall)

      bits : ∀ {j n' v'} → lookupᵐ j (insertᵐ i k bm) ≡ just n'
                         → mem-lookup (Preprocessed.memory (push-mem s vv)) j ≡ just v'
                         → fits-in v' n' ≡ true
      bits {j} {n'} {v'} look lookup-eq
        with lookupᵐ-insertᵐ-cases j i k bm look
      ... | inj₁ (j≡i , n'≡k) =
        let lookup-at-i : mem-lookup (mem ++ (vv ∷ [])) i ≡ just vv
            lookup-at-i =
              subst (λ z → mem-lookup (mem ++ (vv ∷ [])) z ≡ just vv)
                    (sym (idx-sync inv)) (lookup-new mem vv)
            lookup-eq' : mem-lookup (mem ++ (vv ∷ [])) j ≡ just v'
            lookup-eq' = lookup-eq
            v'≡vv : v' ≡ vv
            v'≡vv = just-injective
                      (trans (sym (subst (λ z → mem-lookup (mem ++ (vv ∷ [])) z
                                                 ≡ just v')
                                          j≡i lookup-eq'))
                             lookup-at-i)
        in subst (λ z → fits-in z n' ≡ true) (sym v'≡vv)
                 (subst (λ z → fits-in vv z ≡ true) (sym n'≡k) fits-vv-k)
      ... | inj₂ fall with lookup-shrink-or-new mem vv j v' lookup-eq
      ...   | inj₁ p              = bits-known inv fall p
      ...   | inj₂ (j≡L , _)      =
        ⊥-elim (ℕ<-irrefl-base (subst (_ℕ< i)
                                       (trans j≡L (sym (idx-sync inv)))
                                       (bm-bound inv fall)))

------------------------------------------------------------------------
-- Main per-step preservation theorem (O3)
--
-- 26-case dispatch.  Memory-preserving cases use `o3-frame-no-grow`;
-- one-cell push-mem cases use `o3-frame-push-mem`; two-cell cases use
-- `o3-frame-push-mem-2` (or `-push-mem-push-mem` for div-mod);
-- substantive record cases (constrain-bits, div-mod, copy) use the
-- specialised insert frames.
------------------------------------------------------------------------

o3-preserve : ∀ {pre s s' instr i bm acc'}
  → O3-Inv (i , bm) s
  → R-instr pre s instr s'
  → O3-step instr (i , bm) ≡ just acc'
  → O3-Inv acc' s'
-- Δmem = 0 cases (no record under our conservative O3-record)
o3-preserve {instr = assert c} {i = i} inv (r-assert _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = constrain-eq a b} {i = i} inv (r-constrain-eq _ _ _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = constrain-to-boolean v} {i = i} inv
            (r-constrain-to-boolean _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = declare-pub-input v} {i = i} inv
            (r-declare-pub-input _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = pi-skip g n} {i = i} inv (r-pi-skip-active _ _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = pi-skip g n} {i = i} inv (r-pi-skip-inactive _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)
o3-preserve {instr = output v} {i = i} inv (r-output _) refl =
  o3-inv-coerce-idx (sym (+-0-r i)) (o3-frame-no-grow refl inv)

-- constrain-bits v n: record inserts (v, n).  Justified by r-constrain-bits.
o3-preserve {instr = constrain-bits v n} {i = i} inv
            (r-constrain-bits {v = vv} lv fits-eq) refl =
  o3-inv-coerce-idx (sym (+-0-r i))
    (o3-frame-no-grow-insert-v refl lv fits-eq inv)

-- Δmem = 1 cases (no record under conservative O3-record except copy)
o3-preserve {instr = cond-select bit a b} {i = i} inv
            (r-cond-select _ _ _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = copy v} {i = i} {bm = bm} inv (r-copy {v = vv} lv) refl
  with lookupᵐ v bm in vbm-eq
... | just k  =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem-copy vbm-eq lv inv)
... | nothing =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = load-imm k} {i = i} inv r-load-imm refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = add a b} {i = i} inv (r-add _ _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = mul a b} {i = i} inv (r-mul _ _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = neg a} {i = i} inv (r-neg _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = test-eq a b} {i = i} inv (r-test-eq _ _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = not a} {i = i} inv (r-not _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {instr = less-than a b bits} {i = i} {bm = bm} inv
            (r-less-than _ _ _) step-eq
  with O3-check (less-than a b bits) bm | step-eq
... | true  | refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
... | false | ()
o3-preserve {instr = reconstitute-field d m bits} {i = i} {bm = bm} inv
            (r-reconstitute-field _ _ _) step-eq
  with O3-check (reconstitute-field d m bits) bm | step-eq
... | true  | refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
... | false | ()
o3-preserve {instr = public-input g} {i = i} inv
            (r-public-input-inactive _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {s = s} {instr = public-input g} {i = i} inv
            (r-public-input-active {s₁ = s₁} _ s₁-eq) refl =
  let mem-eq : Preprocessed.memory s₁ ≡ Preprocessed.memory s
      mem-eq = consume-pub-out-mem-eq s s₁-eq
      inv-s₁ = o3-frame-no-grow mem-eq inv
  in o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv-s₁)
o3-preserve {instr = private-input g} {i = i} inv
            (r-private-input-inactive _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)
o3-preserve {s = s} {instr = private-input g} {i = i} inv
            (r-private-input-active {s₁ = s₁} _ s₁-eq) refl =
  let mem-eq : Preprocessed.memory s₁ ≡ Preprocessed.memory s
      mem-eq = consume-priv-mem-eq s s₁-eq
      inv-s₁ = o3-frame-no-grow mem-eq inv
  in o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv-s₁)
o3-preserve {instr = transient-hash xs} {i = i} inv (r-transient-hash _) refl =
  o3-inv-coerce-idx (sym (+-1-r i)) (o3-frame-push-mem inv)

-- Δmem = 2 cases.
o3-preserve {instr = ec-add ax ay bx by} {i = i} inv (r-ec-add _ _ _ _ _) refl =
  o3-inv-coerce-idx (sym (+-2-r i)) (o3-frame-push-mem-2 inv)
o3-preserve {instr = ec-mul ax ay sc} {i = i} inv (r-ec-mul _ _ _ _) refl =
  o3-inv-coerce-idx (sym (+-2-r i)) (o3-frame-push-mem-2 inv)
o3-preserve {instr = ec-mul-generator sc} {i = i} inv (r-ec-mul-generator _ _) refl =
  o3-inv-coerce-idx (sym (+-2-r i)) (o3-frame-push-mem-2 inv)
o3-preserve {instr = hash-to-curve xs} {i = i} inv (r-hash-to-curve _ _) refl =
  o3-inv-coerce-idx (sym (+-2-r i)) (o3-frame-push-mem-2 inv)
o3-preserve {instr = persistent-hash a xs} {i = i} inv (r-persistent-hash _ _) refl =
  o3-inv-coerce-idx (sym (+-2-r i)) (o3-frame-push-mem-2 inv)

-- div-mod-power-of-two v n: 2 records.  divisor at i (fits in FR-BITS ∸ n);
-- modulus at suc i (fits in n).  Justified by the bit-arithmetic axioms.
o3-preserve {instr = div-mod-power-of-two v n} {i = i} inv
            (r-div-mod-power-of-two {v = vv} lv) refl =
  let divisor = from-le-bits (drop n (to-le-bits vv))
      modulus = from-le-bits (take n (to-le-bits vv))
      fits-div : fits-in divisor (FR-BITS ∸ n) ≡ true
      fits-div = fits-from-le-bits-drop vv n
      fits-mod : fits-in modulus n ≡ true
      fits-mod = fits-from-le-bits-take (to-le-bits vv) n
  in o3-inv-coerce-idx (sym (+-2-r i))
       (o3-frame-push-mem-2-insert-2 {nx = FR-BITS ∸ n} {ny = n}
                                      fits-div fits-mod inv)

------------------------------------------------------------------------
-- Multi-step preservation, indexed by O3-Trace
--
-- Given the invariant at (acc, s) and a parallel run of R-instrs and
-- O3-Trace, conclude the invariant at (final, s').
------------------------------------------------------------------------

o3-preserve* : ∀ {pre s s' acc final is}
  → O3-Inv acc s
  → R-instrs pre s is s'
  → O3-Trace is acc final
  → O3-Inv final s'
o3-preserve* inv r-done o3-done = inv
o3-preserve* inv (r-step r rs) (o3-step step-eq tr) =
  o3-preserve* (o3-preserve inv r step-eq) rs tr

------------------------------------------------------------------------
-- Whole-program O3 soundness
--
-- Given:
--   • `R src pre s` (the source is faithfully realised by state s),
--     which packages an initial state s₀ and an `R-instrs pre s₀ … s`
--     run;
--   • `O3-Runs src` (the O3 scan completed with final = (i, bm));
--   • the WF1 hypothesis `length inputs ≡ num-inputs src`
-- conclude: for every wire `j` with `lookupᵐ j (proj₂ final) ≡ just n`,
-- the corresponding memory entry `v` satisfies `fits-in v n ≡ true`.
------------------------------------------------------------------------

O3-sound : ∀ {src pre s}
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → R src pre s
  → (run : O3-Runs src)
  → ∀ {j n v}
  → lookupᵐ j (proj₂ (O3-Runs.final run)) ≡ just n
  → mem-lookup (Preprocessed.memory s) j ≡ just v
  → fits-in v n ≡ true
O3-sound {src} {pre} {s} lenEq (s₀ , init-eq , r-instrs , _ , _)
         (mk-o3-runs final trace) =
  let inv₀ : O3-Inv (IrSource.num-inputs src , []) s₀
      inv₀ = o3-inv-init {src} {pre} {s₀} init-eq lenEq

      inv-final : O3-Inv final s
      inv-final = o3-preserve* inv₀ r-instrs trace
  in bits-known inv-final

------------------------------------------------------------------------
-- Integration lemmas for Phase 4d
--
-- Phase 4d's per-instruction obligation evidence is extracted from
-- the trace + lookup proofs.  We expose:
--
--   • `o3-known-fits`  — at any intermediate (i, bm)/s pairing, if
--     `lookupᵐ a bm ≡ just n` and `mem-lookup mem a ≡ just v`, then
--     `fits-in v n ≡ true`.  This is the direct extractor used by
--     `reconstitute-field-bwd` and `less-than-bwd`.
--   • `o3-inv-mid`    — analogous to `o2-inv-mid`: lifts a Trace
--     prefix to an `O3-Inv` at the mid-state.  Composes with
--     `o3-known-fits` at the per-instruction call site.
------------------------------------------------------------------------

-- Extract `fits-in v n ≡ true` for an operand `a` known in bm.
o3-known-fits : ∀ {i bm s a n v}
  → O3-Inv (i , bm) s
  → lookupᵐ a bm ≡ just n
  → mem-lookup (Preprocessed.memory s) a ≡ just v
  → fits-in v n ≡ true
o3-known-fits inv look-eq lookup-eq = bits-known inv look-eq lookup-eq

-- O3-Inv at an intermediate state (mirrors o2-inv-mid).
o3-inv-mid : ∀ {src pre s₀ s prefix-is acc-mid}
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  → init-state src pre ≡ just s₀
  → R-instrs pre s₀ prefix-is s
  → O3-Trace prefix-is (IrSource.num-inputs src , []) acc-mid
  → O3-Inv acc-mid s
o3-inv-mid {src} {pre} {s₀ = s₀} lenEq init-eq r-instrs trace =
  o3-preserve* (o3-inv-init {src} {pre} {s₀} init-eq lenEq) r-instrs trace

------------------------------------------------------------------------
-- Bool ⇒ Witness extractors for the producer-safe conjunction.
--
-- These let Phase 4d (which receives `producer-safe src ≡ true` as a
-- caller hypothesis) recover the witness-bearing `O2-Runs` / `O3-Runs`
-- needed to feed the soundness theorems above.
--
-- `producer-safe src = O1 src ∧ O2 src ∧ O3 src` decomposes via
-- `∧-true` into three Bool conjuncts.
------------------------------------------------------------------------

-- Project conjuncts of `producer-safe`.  We pattern-match directly
-- on the conjunction: `producer-safe = O1 ∧ O2 ∧ O3 ∧ wire-disc`, so
-- `≡ true` forces each conjunct to be `true`.  Case analysis on the
-- bools is mechanical.
producer-safe-O1 : ∀ {src} → producer-safe src ≡ true → O1 src ≡ true
producer-safe-O1 {src} eq with O1 src | O2 src | O3 src | wire-disc src | eq
... | true  | true  | true  | true | refl = refl

producer-safe-O2 : ∀ {src} → producer-safe src ≡ true → O2 src ≡ true
producer-safe-O2 {src} eq with O1 src | O2 src | O3 src | wire-disc src | eq
... | true  | true  | true  | true | refl = refl

producer-safe-O3 : ∀ {src} → producer-safe src ≡ true → O3 src ≡ true
producer-safe-O3 {src} eq with O1 src | O2 src | O3 src | wire-disc src | eq
... | true  | true  | true  | true | refl = refl

producer-safe-wire-disc : ∀ {src} → producer-safe src ≡ true → wire-disc src ≡ true
producer-safe-wire-disc {src} eq with O1 src | O2 src | O3 src | wire-disc src | eq
... | true  | true  | true  | true | refl = refl

-- Convert `O2 src ≡ true` into an `O2-Runs src` witness.
-- The scan succeeds iff it returns `just`; we extract that and pair
-- with a reconstructed O2-Trace.
private
  O2-scan→trace : ∀ is acc {final}
    → O2-scan is acc ≡ just final
    → O2-Trace is acc final
  O2-scan→trace []       acc refl = o2-done
  O2-scan→trace (i ∷ is) acc eq
    with O2-step i acc in step-eq
  ... | just acc' = o2-step step-eq (O2-scan→trace is acc' eq)

  O3-scan→trace : ∀ is acc {final}
    → O3-scan is acc ≡ just final
    → O3-Trace is acc final
  O3-scan→trace []       acc refl = o3-done
  O3-scan→trace (i ∷ is) acc eq
    with O3-step i acc in step-eq
  ... | just acc' = o3-step step-eq (O3-scan→trace is acc' eq)

O2-bool→Runs : ∀ {src} → O2 src ≡ true → O2-Runs src
O2-bool→Runs {src} eq
  with O2-scan (IrSource.instructions src) (IrSource.num-inputs src , [])
       in scan-eq
... | just final = mk-o2-runs final
                     (O2-scan→trace (IrSource.instructions src)
                                     (IrSource.num-inputs src , [])
                                     scan-eq)

O3-bool→Runs : ∀ {src} → O3 src ≡ true → O3-Runs src
O3-bool→Runs {src} eq
  with O3-scan (IrSource.instructions src) (IrSource.num-inputs src , [])
       in scan-eq
... | just final = mk-o3-runs final
                     (O3-scan→trace (IrSource.instructions src)
                                     (IrSource.num-inputs src , [])
                                     scan-eq)
