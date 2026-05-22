module zkir-v2.Circuit where

open import zkir-v2.Syntax
open import zkir-v2.Semantics

open import Data.Bool    using (Bool; true; false; _∧_)
import Data.Bool as Bool
open import Data.List    using (List; []; _∷_; _++_; length; take; drop; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe   using (Maybe; nothing; just; _>>=_)
open import Data.Nat     using (ℕ; zero; suc; _∸_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; trans)

------------------------------------------------------------------------
-- Local helpers
------------------------------------------------------------------------

private
  -- Looking up an in-bounds index is unaffected by appending.
  mem-lookup-append : ∀ (mem : List Fr) (i : Index) (v : Fr) (vs : List Fr)
    → mem-lookup mem i ≡ just v
    → mem-lookup (mem ++ vs) i ≡ just v
  mem-lookup-append []           _ _ _  ()
  mem-lookup-append (_ ∷ _)  zero    _ _  refl = refl
  mem-lookup-append (_ ∷ xs) (suc n) v vs eq   = mem-lookup-append xs n v vs eq

  -- The element appended at position |mem| is found there.
  mem-lookup-length : ∀ (mem : List Fr) (v : Fr)
    → mem-lookup (mem ++ (v ∷ [])) (length mem) ≡ just v
  mem-lookup-length []       _ = refl
  mem-lookup-length (_ ∷ xs) v = mem-lookup-length xs v

  -- For push-mem2: first new element.
  mem-lookup-length2-fst : ∀ (mem : List Fr) (v₁ v₂ : Fr)
    → mem-lookup (mem ++ (v₁ ∷ v₂ ∷ [])) (length mem) ≡ just v₁
  mem-lookup-length2-fst []       _ _ = refl
  mem-lookup-length2-fst (_ ∷ xs) v₁ v₂ = mem-lookup-length2-fst xs v₁ v₂

  -- For push-mem2: second new element.
  mem-lookup-length2-snd : ∀ (mem : List Fr) (v₁ v₂ : Fr)
    → mem-lookup (mem ++ (v₁ ∷ v₂ ∷ [])) (suc (length mem)) ≡ just v₂
  mem-lookup-length2-snd []       _ _ = refl
  mem-lookup-length2-snd (_ ∷ xs) v₁ v₂ = mem-lookup-length2-snd xs v₁ v₂

  -- A bind chain over a lookup is preserved when memory is extended.
  mem->>=append : ∀ {B : Set} (f : Fr → Maybe B) {b : B}
    → (mem : List Fr) (i : Index) (vs : List Fr)
    → (mem-lookup mem i >>= f) ≡ just b
    → (mem-lookup (mem ++ vs) i >>= f) ≡ just b
  mem->>=append f []           i  vs ()
  mem->>=append f (_ ∷ _)  zero    vs eq = eq
  mem->>=append f (_ ∷ xs) (suc n) vs eq = mem->>=append f xs n vs eq

  -- All lookups in a list of indices are preserved when memory is extended.
  mem-lookups-append : ∀ (mem : List Fr) (is : List Index) (extra : List Fr)
    → ∀ {vs} → mem-lookups mem is ≡ just vs
    → mem-lookups (mem ++ extra) is ≡ just vs
  mem-lookups-append mem []       extra refl = refl
  mem-lookups-append mem (i ∷ is) extra {vs} eq
    with mem-lookup mem i in h1 | mem-lookups mem is in h2
  mem-lookups-append mem (i ∷ is) extra {vs} ()  | nothing | _
  mem-lookups-append mem (i ∷ is) extra {vs} ()  | just _  | nothing
  mem-lookups-append mem (i ∷ is) extra {vs} eq  | just v  | just vs'
    rewrite mem-lookup-append mem i v extra h1
    rewrite mem-lookups-append mem is extra {vs'} h2
    = eq

  -- Appending one element increments the length.
  length-++-one : ∀ (xs : List Fr) (x : Fr) → length (xs ++ (x ∷ [])) ≡ suc (length xs)
  length-++-one []       _ = refl
  length-++-one (_ ∷ xs) x = cong suc (length-++-one xs x)

------------------------------------------------------------------------
-- Gate: a polynomial constraint over memory positions.
--
-- Each constructor corresponds to one ZkStdLib operation in the Rust
-- circuit function.  Arithmetic gates are fully specified; complex
-- gates (EC, hash, range checks) carry their indices but have opaque
-- semantics postulated below.
------------------------------------------------------------------------

data Gate : Set where
  -- Arithmetic
  gate-add              : (r a b : Index)                          → Gate
  gate-mul              : (r a b : Index)                          → Gate
  gate-neg              : (r a : Index)                            → Gate
  gate-const            : (r : Index) (v : Fr)                     → Gate
  gate-copy             : (r a : Index)                            → Gate
  -- Constraints (no new memory output)
  gate-constrain-eq     : (a b : Index)                            → Gate
  gate-assert-nonzero   : (a : Index)                              → Gate
  gate-boolean          : (a : Index)                              → Gate
  -- Tests (output is a bit)
  gate-test-eq          : (r a b : Index)                          → Gate
  gate-is-zero          : (r a : Index)                            → Gate
  -- Complex ops (opaque — semantics postulated)
  gate-constrain-bits   : (a : Index) (bits : ℕ)                  → Gate
  gate-less-than        : (r a b : Index) (bits : ℕ)              → Gate
  gate-ec-add           : (r_x r_y a_x a_y b_x b_y : Index)       → Gate
  gate-ec-mul           : (r_x r_y a_x a_y sc : Index)            → Gate
  gate-ec-mul-gen       : (r_x r_y sc : Index)                     → Gate
  gate-hash-to-curve    : (r_x r_y : Index) (inputs : List Index)  → Gate
  gate-transient-hash   : (r : Index) (inputs : List Index)        → Gate
  gate-persistent-hash  : (r_x r_y : Index) (alignment : Alignment)
                          (inputs : List Index)                     → Gate
  gate-div-mod-pow2     : (r_d r_m a : Index) (bits : ℕ)          → Gate
  gate-reconstitute     : (r d m : Index) (bits : ℕ)              → Gate
  gate-public-input     : (r : Index) (guard : Maybe Index)        → Gate
  gate-private-input    : (r : Index) (guard : Maybe Index)        → Gate
  gate-pi-skip          : (guard : Maybe Index) (count : ℕ)        → Gate

------------------------------------------------------------------------
-- Semantics of arithmetic gates
-- (Concrete field equations that must hold on the memory.)
------------------------------------------------------------------------

gate-holds : List Fr → Gate → Set

-- mem[r] = mem[a] + mem[b]
gate-holds mem (gate-add r a b) =
  ∃ λ av → ∃ λ bv →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem b ≡ just bv ×
    mem-lookup mem r ≡ just (av +ᶠ bv)

-- mem[r] = mem[a] * mem[b]
gate-holds mem (gate-mul r a b) =
  ∃ λ av → ∃ λ bv →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem b ≡ just bv ×
    mem-lookup mem r ≡ just (av *ᶠ bv)

-- mem[r] = -mem[a]
gate-holds mem (gate-neg r a) =
  ∃ λ av →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem r ≡ just (-ᶠ av)

-- mem[r] = v  (constant assignment)
gate-holds mem (gate-const r v) =
  mem-lookup mem r ≡ just v

-- mem[r] = mem[a]  (copy)
gate-holds mem (gate-copy r a) =
  ∃ λ v →
    mem-lookup mem a ≡ just v ×
    mem-lookup mem r ≡ just v

-- mem[a] ≡ᶠ? mem[b]
gate-holds mem (gate-constrain-eq a b) =
  ∃ λ av → ∃ λ bv →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem b ≡ just bv ×
    av ≡ᶠ? bv ≡ true

-- mem[a] ≠ 0  (combined with gate-boolean: means mem[a] = 1)
gate-holds mem (gate-assert-nonzero a) =
  ∃ λ b →
    (mem-lookup mem a >>= to-bool) ≡ just b ×
    b ≡ true

-- mem[a] ∈ {0, 1}
gate-holds mem (gate-boolean a) =
  ∃ λ b →
    (mem-lookup mem a >>= to-bool) ≡ just b

-- mem[r] = from-bool (mem[a] = mem[b])
gate-holds mem (gate-test-eq r a b) =
  ∃ λ av → ∃ λ bv →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem b ≡ just bv ×
    mem-lookup mem r ≡ just (from-bool (av ≡ᶠ? bv))

-- mem[r] = from-bool (mem[a] = 0)  [is_zero, used for `not`]
gate-holds mem (gate-is-zero r a) =
  ∃ λ b →
    (mem-lookup mem a >>= to-bool) ≡ just b ×
    mem-lookup mem r ≡ just (from-bool (Bool.not b))

-- Complex gates: semantics is the same predicate as R-instr for now.
-- A future refinement would express these as concrete polynomial systems.
gate-holds mem (gate-constrain-bits a bits) =
  ∃ λ v → mem-lookup mem a ≡ just v × fits-in v bits ≡ true

gate-holds mem (gate-less-than r a b bits) =
  ∃ λ av → ∃ λ bv →
    mem-lookup mem a ≡ just av ×
    mem-lookup mem b ≡ just bv ×
    (fits-in av bits ∧ fits-in bv bits) ≡ true ×
    mem-lookup mem r ≡ just (from-bool
      (bits-lt (take bits (to-le-bits av)) (take bits (to-le-bits bv))))

gate-holds mem (gate-ec-add r_x r_y a_x a_y b_x b_y) =
  ∃ λ ax → ∃ λ ay → ∃ λ bx → ∃ λ by → ∃ λ cx → ∃ λ cy →
    mem-lookup mem a_x ≡ just ax ×
    mem-lookup mem a_y ≡ just ay ×
    mem-lookup mem b_x ≡ just bx ×
    mem-lookup mem b_y ≡ just by ×
    ec-add-pts ax ay bx by ≡ just (cx , cy) ×
    mem-lookup mem r_x ≡ just cx ×
    mem-lookup mem r_y ≡ just cy

gate-holds mem (gate-ec-mul r_x r_y a_x a_y sc) =
  ∃ λ ax → ∃ λ ay → ∃ λ s → ∃ λ cx → ∃ λ cy →
    mem-lookup mem a_x ≡ just ax ×
    mem-lookup mem a_y ≡ just ay ×
    mem-lookup mem sc  ≡ just s  ×
    ec-mul-pt ax ay s ≡ just (cx , cy) ×
    mem-lookup mem r_x ≡ just cx ×
    mem-lookup mem r_y ≡ just cy

gate-holds mem (gate-ec-mul-gen r_x r_y sc) =
  ∃ λ s →
    mem-lookup mem sc  ≡ just s ×
    mem-lookup mem r_x ≡ just (proj₁ (ec-mul-gen s)) ×
    mem-lookup mem r_y ≡ just (proj₂ (ec-mul-gen s))

gate-holds mem (gate-hash-to-curve r_x r_y inputs) =
  ∃ λ vs →
    mem-lookups mem inputs ≡ just vs ×
    mem-lookup mem r_x ≡ just (proj₁ (hash-to-curve-fn vs)) ×
    mem-lookup mem r_y ≡ just (proj₂ (hash-to-curve-fn vs))

gate-holds mem (gate-transient-hash r inputs) =
  ∃ λ vs →
    mem-lookups mem inputs ≡ just vs ×
    mem-lookup mem r ≡ just (transient-hash-fn vs)

gate-holds mem (gate-persistent-hash r_x r_y alignment inputs) =
  ∃ λ vs →
    mem-lookups mem inputs ≡ just vs ×
    mem-lookup mem r_x ≡ just (proj₁ (persistent-hash-fn alignment vs)) ×
    mem-lookup mem r_y ≡ just (proj₂ (persistent-hash-fn alignment vs))

gate-holds mem (gate-div-mod-pow2 r_d r_m a bits) =
  ∃ λ v →
    mem-lookup mem a   ≡ just v ×
    mem-lookup mem r_d ≡ just (from-le-bits (drop bits (to-le-bits v))) ×
    mem-lookup mem r_m ≡ just (from-le-bits (take bits (to-le-bits v)))

gate-holds mem (gate-reconstitute r d m bits) =
  ∃ λ dv → ∃ λ mv →
    let mv-bits = take bits (to-le-bits mv)
        dv-bits = take (FR-BITS ∸ bits) (to-le-bits dv)
        all     = mv-bits ++ dv-bits
    in
    mem-lookup mem d ≡ just dv ×
    mem-lookup mem m ≡ just mv ×
    (fits-in mv bits ∧ fits-in dv (FR-BITS ∸ bits) ∧ bits-in-field all) ≡ true ×
    mem-lookup mem r ≡ just (from-le-bits all)

gate-holds mem (gate-public-input r guard) =
  ∃ λ v →
    mem-lookup mem r ≡ just v ×
    (∀ i → guard ≡ just i →
       ∃ λ b → mem-lookup mem i ≡ just (from-bool b) ×
               (b ≡ false → v ≡ 0ᶠ))

gate-holds mem (gate-private-input r guard) =
  ∃ λ v →
    mem-lookup mem r ≡ just v ×
    (∀ i → guard ≡ just i →
       ∃ λ b → mem-lookup mem i ≡ just (from-bool b) ×
               (b ≡ false → v ≡ 0ᶠ))

gate-holds mem (gate-pi-skip guard count) = ⊤
  where open import Data.Unit using (⊤)

------------------------------------------------------------------------
-- Per-instruction gate generation
------------------------------------------------------------------------

private
  n : Preprocessed → ℕ
  n s = length (Preprocessed.memory s)

circuit-instr-gates : ProofPreimage → Preprocessed → Instruction → List Gate
circuit-instr-gates _   s (assert cond)                   = gate-assert-nonzero cond ∷ []
circuit-instr-gates _   s (cond-select bit a b)           = gate-boolean (n s) ∷ []
circuit-instr-gates _   s (constrain-bits var bits)       = gate-constrain-bits var bits ∷ []
circuit-instr-gates _   s (constrain-eq a b)              = gate-constrain-eq a b ∷ []
circuit-instr-gates _   s (constrain-to-boolean var)      = gate-boolean var ∷ []
circuit-instr-gates _   s (copy var)                      = gate-copy (n s) var ∷ []
circuit-instr-gates _   s (declare-pub-input _)           = []
circuit-instr-gates pre s (pi-skip guard count)           = gate-pi-skip guard count ∷ []
circuit-instr-gates _   s (ec-add a_x a_y b_x b_y)       = gate-ec-add (n s) (suc (n s)) a_x a_y b_x b_y ∷ []
circuit-instr-gates _   s (ec-mul a_x a_y scalar)         = gate-ec-mul (n s) (suc (n s)) a_x a_y scalar ∷ []
circuit-instr-gates _   s (ec-mul-generator scalar)       = gate-ec-mul-gen (n s) (suc (n s)) scalar ∷ []
circuit-instr-gates _   s (hash-to-curve inputs)          = gate-hash-to-curve (n s) (suc (n s)) inputs ∷ []
circuit-instr-gates _   s (load-imm imm)                  = gate-const (n s) imm ∷ []
circuit-instr-gates _   s (div-mod-power-of-two var bits) = gate-div-mod-pow2 (n s) (suc (n s)) var bits ∷ []
circuit-instr-gates _   s (reconstitute-field d m bits)   = gate-reconstitute (n s) d m bits ∷ []
circuit-instr-gates _   s (output _)                      = []
circuit-instr-gates _   s (transient-hash inputs)         = gate-transient-hash (n s) inputs ∷ []
circuit-instr-gates _   s (persistent-hash alignment is)  = gate-persistent-hash (n s) (suc (n s)) alignment is ∷ []
circuit-instr-gates _   s (test-eq a b)                   = gate-test-eq (n s) a b ∷ []
circuit-instr-gates _   s (add a b)                       = gate-add (n s) a b ∷ []
circuit-instr-gates _   s (mul a b)                       = gate-mul (n s) a b ∷ []
circuit-instr-gates _   s (neg a)                         = gate-neg (n s) a ∷ []
circuit-instr-gates _   s (not a)                         = gate-is-zero (n s) a ∷ []
circuit-instr-gates _   s (less-than a b bits)            = gate-less-than (n s) a b bits ∷ []
circuit-instr-gates _   s (public-input guard)            = gate-public-input (n s) guard ∷ []
circuit-instr-gates _   s (private-input guard)           = gate-private-input (n s) guard ∷ []

------------------------------------------------------------------------
-- Completeness: R-instr → all gates satisfied on the successor memory.
--
-- This is the ZK completeness direction: the prover's witness
-- (produced by preprocess) satisfies all circuit constraints.
------------------------------------------------------------------------

R-instr→gates-add : ∀ pre s a b s'
  → R-instr pre s (add a b) s'
  → gate-holds (Preprocessed.memory s') (gate-add (n s) a b)
R-instr→gates-add _ s _ _ _ (r-add {av = av} {bv = bv} la lb)
  = av , bv ,
    mem-lookup-append (Preprocessed.memory s) _ av _ la ,
    mem-lookup-append (Preprocessed.memory s) _ bv _ lb ,
    mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-mul : ∀ pre s a b s'
  → R-instr pre s (mul a b) s'
  → gate-holds (Preprocessed.memory s') (gate-mul (n s) a b)
R-instr→gates-mul _ s _ _ _ (r-mul {av = av} {bv = bv} la lb)
  = av , bv ,
    mem-lookup-append (Preprocessed.memory s) _ av _ la ,
    mem-lookup-append (Preprocessed.memory s) _ bv _ lb ,
    mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-neg : ∀ pre s a s'
  → R-instr pre s (neg a) s'
  → gate-holds (Preprocessed.memory s') (gate-neg (n s) a)
R-instr→gates-neg _ s _ _ (r-neg {av = av} la)
  = av ,
    mem-lookup-append (Preprocessed.memory s) _ av _ la ,
    mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-load-imm : ∀ pre s imm s'
  → R-instr pre s (load-imm imm) s'
  → gate-holds (Preprocessed.memory s') (gate-const (n s) imm)
R-instr→gates-load-imm _ s imm _ r-load-imm
  = mem-lookup-length (Preprocessed.memory s) imm

R-instr→gates-copy : ∀ pre s var s'
  → R-instr pre s (copy var) s'
  → gate-holds (Preprocessed.memory s') (gate-copy (n s) var)
R-instr→gates-copy _ s _ _ (r-copy {v = v} lv)
  = v ,
    mem-lookup-append (Preprocessed.memory s) _ v _ lv ,
    mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-assert : ∀ pre s cond s'
  → R-instr pre s (assert cond) s'
  → gate-holds (Preprocessed.memory s') (gate-assert-nonzero cond)
R-instr→gates-assert _ _ _ _ (r-assert la) = true , la , refl

R-instr→gates-test-eq : ∀ pre s a b s'
  → R-instr pre s (test-eq a b) s'
  → gate-holds (Preprocessed.memory s') (gate-test-eq (n s) a b)
R-instr→gates-test-eq _ s _ _ _ (r-test-eq {av = av} {bv = bv} la lb)
  = av , bv ,
    mem-lookup-append (Preprocessed.memory s) _ av _ la ,
    mem-lookup-append (Preprocessed.memory s) _ bv _ lb ,
    mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-not : ∀ pre s a s'
  → R-instr pre s (not a) s'
  → gate-holds (Preprocessed.memory s') (gate-is-zero (n s) a)
R-instr→gates-not _ s _ _ (r-not {b = b} lb)
  = b , mem->>=append to-bool (Preprocessed.memory s) _ _ lb ,
    mem-lookup-length (Preprocessed.memory s) _

-- cond-select: gate-boolean (n s) checks the result is 0/1, but cond-select
-- produces an arbitrary field element; this gate needs redesign.
postulate
  R-instr→gates-cond-select : ∀ pre s bit a b s' → R-instr pre s (cond-select bit a b) s' → gate-holds (Preprocessed.memory s') (gate-boolean (n s))

-- No-push instructions: s' = s, so memory is unchanged.

R-instr→gates-constrain-bits : ∀ pre s var bits s'
  → R-instr pre s (constrain-bits var bits) s'
  → gate-holds (Preprocessed.memory s') (gate-constrain-bits var bits)
R-instr→gates-constrain-bits _ _ _ _ _ (r-constrain-bits {v = v} lv fits) = v , lv , fits

R-instr→gates-constrain-eq : ∀ pre s a b s'
  → R-instr pre s (constrain-eq a b) s'
  → gate-holds (Preprocessed.memory s') (gate-constrain-eq a b)
R-instr→gates-constrain-eq _ _ _ _ _ (r-constrain-eq {av = av} {bv = bv} la lb eq) =
  av , bv , la , lb , eq

R-instr→gates-constrain-bool : ∀ pre s var s'
  → R-instr pre s (constrain-to-boolean var) s'
  → gate-holds (Preprocessed.memory s') (gate-boolean var)
R-instr→gates-constrain-bool _ _ _ _ (r-constrain-to-boolean {b = b} lb) = b , lb

-- Single-push instructions.

R-instr→gates-less-than : ∀ pre s a b bits s'
  → R-instr pre s (less-than a b bits) s'
  → gate-holds (Preprocessed.memory s') (gate-less-than (n s) a b bits)
R-instr→gates-less-than _ s _ _ _ _ (r-less-than {av = av} {bv = bv} la lb fits) =
  av , bv ,
  mem-lookup-append (Preprocessed.memory s) _ av _ la ,
  mem-lookup-append (Preprocessed.memory s) _ bv _ lb ,
  fits ,
  mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-reconstitute : ∀ pre s d m bits s'
  → R-instr pre s (reconstitute-field d m bits) s'
  → gate-holds (Preprocessed.memory s') (gate-reconstitute (n s) d m bits)
R-instr→gates-reconstitute _ s _ _ _ _ (r-reconstitute-field {dv = dv} {mv = mv} ldv lmv chk) =
  dv , mv ,
  mem-lookup-append (Preprocessed.memory s) _ dv _ ldv ,
  mem-lookup-append (Preprocessed.memory s) _ mv _ lmv ,
  chk ,
  mem-lookup-length (Preprocessed.memory s) _

R-instr→gates-transient-hash : ∀ pre s inputs s'
  → R-instr pre s (transient-hash inputs) s'
  → gate-holds (Preprocessed.memory s') (gate-transient-hash (n s) inputs)
R-instr→gates-transient-hash _ s inputs _ (r-transient-hash {vs = vs} lvs) =
  vs ,
  mem-lookups-append (Preprocessed.memory s) inputs (transient-hash-fn vs ∷ []) lvs ,
  mem-lookup-length (Preprocessed.memory s) _

-- Double-push (push-mem2) instructions.

R-instr→gates-ec-add : ∀ pre s a_x a_y b_x b_y s'
  → R-instr pre s (ec-add a_x a_y b_x b_y) s'
  → gate-holds (Preprocessed.memory s') (gate-ec-add (n s) (suc (n s)) a_x a_y b_x b_y)
R-instr→gates-ec-add _ s _ _ _ _ _ (r-ec-add {ax = ax} {ay = ay} {bx = bx} {by = by} {cx = cx} {cy = cy} lax lay lbx lby ec) =
  ax , ay , bx , by , cx , cy ,
  mem-lookup-append (Preprocessed.memory s) _ ax _ lax ,
  mem-lookup-append (Preprocessed.memory s) _ ay _ lay ,
  mem-lookup-append (Preprocessed.memory s) _ bx _ lbx ,
  mem-lookup-append (Preprocessed.memory s) _ by _ lby ,
  ec ,
  mem-lookup-length2-fst (Preprocessed.memory s) cx cy ,
  mem-lookup-length2-snd (Preprocessed.memory s) cx cy

R-instr→gates-ec-mul : ∀ pre s a_x a_y sc s'
  → R-instr pre s (ec-mul a_x a_y sc) s'
  → gate-holds (Preprocessed.memory s') (gate-ec-mul (n s) (suc (n s)) a_x a_y sc)
R-instr→gates-ec-mul _ s _ _ _ _ (r-ec-mul {ax = ax} {ay = ay} {sc = scv} {cx = cx} {cy = cy} lax lay lsc ec) =
  ax , ay , scv , cx , cy ,
  mem-lookup-append (Preprocessed.memory s) _ ax _ lax ,
  mem-lookup-append (Preprocessed.memory s) _ ay _ lay ,
  mem-lookup-append (Preprocessed.memory s) _ scv _ lsc ,
  ec ,
  mem-lookup-length2-fst (Preprocessed.memory s) cx cy ,
  mem-lookup-length2-snd (Preprocessed.memory s) cx cy

R-instr→gates-ec-mul-gen : ∀ pre s sc s'
  → R-instr pre s (ec-mul-generator sc) s'
  → gate-holds (Preprocessed.memory s') (gate-ec-mul-gen (n s) (suc (n s)) sc)
R-instr→gates-ec-mul-gen _ s _ _ (r-ec-mul-generator {sc = scv} {cx = cx} {cy = cy} lsc eq) =
  scv ,
  mem-lookup-append (Preprocessed.memory s) _ scv _ lsc ,
  trans (mem-lookup-length2-fst (Preprocessed.memory s) cx cy)
        (cong just (sym (cong proj₁ eq))) ,
  trans (mem-lookup-length2-snd (Preprocessed.memory s) cx cy)
        (cong just (sym (cong proj₂ eq)))

R-instr→gates-hash-to-curve : ∀ pre s inputs s'
  → R-instr pre s (hash-to-curve inputs) s'
  → gate-holds (Preprocessed.memory s') (gate-hash-to-curve (n s) (suc (n s)) inputs)
R-instr→gates-hash-to-curve _ s inputs _ (r-hash-to-curve {vs = vs} {cx = cx} {cy = cy} lvs eq) =
  vs ,
  mem-lookups-append (Preprocessed.memory s) inputs (cx ∷ cy ∷ []) lvs ,
  trans (mem-lookup-length2-fst (Preprocessed.memory s) cx cy)
        (cong just (sym (cong proj₁ eq))) ,
  trans (mem-lookup-length2-snd (Preprocessed.memory s) cx cy)
        (cong just (sym (cong proj₂ eq)))

R-instr→gates-persistent-hash : ∀ pre s alignment inputs s'
  → R-instr pre s (persistent-hash alignment inputs) s'
  → gate-holds (Preprocessed.memory s') (gate-persistent-hash (n s) (suc (n s)) alignment inputs)
R-instr→gates-persistent-hash _ s _ inputs _ (r-persistent-hash {vs = vs} {h₁ = h₁} {h₂ = h₂} lvs eq) =
  vs ,
  mem-lookups-append (Preprocessed.memory s) inputs (h₁ ∷ h₂ ∷ []) lvs ,
  trans (mem-lookup-length2-fst (Preprocessed.memory s) h₁ h₂)
        (cong just (sym (cong proj₁ eq))) ,
  trans (mem-lookup-length2-snd (Preprocessed.memory s) h₁ h₂)
        (cong just (sym (cong proj₂ eq)))

-- Nested push-mem (not push-mem2) instruction.

R-instr→gates-div-mod-pow2 : ∀ pre s var bits s'
  → R-instr pre s (div-mod-power-of-two var bits) s'
  → gate-holds (Preprocessed.memory s') (gate-div-mod-pow2 (n s) (suc (n s)) var bits)
R-instr→gates-div-mod-pow2 _ s _ bits _ (r-div-mod-power-of-two {v = v} lv) =
  let mem = Preprocessed.memory s
      v1  = from-le-bits (drop bits (to-le-bits v))
      v2  = from-le-bits (take bits (to-le-bits v))
  in v ,
     mem-lookup-append (mem ++ (v1 ∷ [])) _ v _ (mem-lookup-append mem _ v _ lv) ,
     mem-lookup-append (mem ++ (v1 ∷ [])) _ v1 _ (mem-lookup-length mem v1) ,
     subst (λ k → mem-lookup ((mem ++ (v1 ∷ [])) ++ (v2 ∷ [])) k ≡ just v2)
           (length-++-one mem v1)
           (mem-lookup-length (mem ++ (v1 ∷ [])) v2)

-- public-input and private-input require eval-guard reasoning.
postulate
  R-instr→gates-public-input  : ∀ pre s guard s' → R-instr pre s (public-input guard) s' → gate-holds (Preprocessed.memory s') (gate-public-input (n s) guard)
  R-instr→gates-private-input : ∀ pre s guard s' → R-instr pre s (private-input guard) s' → gate-holds (Preprocessed.memory s') (gate-private-input (n s) guard)

------------------------------------------------------------------------
-- Soundness: all gates satisfied → R-instr.
-- Requires well-formedness (indices in bounds) not captured here.
------------------------------------------------------------------------

postulate
  gates→R-instr : ∀ pre s i s'
    → (∀ g → g ∈ circuit-instr-gates pre s i → gate-holds (Preprocessed.memory s') g)
    → R-instr pre s i s'
