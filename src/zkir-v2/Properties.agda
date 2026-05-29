{-# OPTIONS --safe #-}
open import zkir-v2.Assumptions

module zkir-v2.Properties (⋯ : _) (open Assumptions ⋯) where

open import zkir-v2.Syntax ⋯
open import zkir-v2.Semantics ⋯

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.List    using (List; []; _∷_; length)
open import Data.List.Properties using (length-++-≤ˡ)
open import Data.Maybe   using (Maybe; nothing; just; _>>=_)
open import Data.Nat     using (ℕ; _≤_; _≡ᵇ_)
open import Data.Nat.Properties  using (≤-trans; ≤-reflexive)
open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
-- P5 (circuit faithfulness) is now fully discharged in `CircuitProof`;
-- we re-export it here (where the spec's §6.2 postulate used to live).
open import zkir-v2.Circuit ⋯      using (circuit; satisfies)
open import zkir-v2.Obligations ⋯  using (producer-safe)
open import zkir-v2.CircuitProof ⋯ using (witness-of; preprocess-shaped; circuit-faithful)

------------------------------------------------------------------------
-- Local proof helpers
------------------------------------------------------------------------

private

  >>=-just : ∀ {A B : Set} {f : A → Maybe B} {y : B}
    → (m : Maybe A) → (m >>= f) ≡ just y
    → ∃ λ x → m ≡ just x × f x ≡ just y
  >>=-just (just x) p = x , refl , p
  >>=-just nothing  ()

  if-just : ∀ {A : Set} (b : Bool) {x y : A}
    → (if b then just x else nothing) ≡ just y
    → b ≡ true × x ≡ y
  if-just true  refl = refl , refl
  if-just false ()

  ∧-true-left : ∀ (a b : Bool) → a ∧ b ≡ true → a ≡ true
  ∧-true-left true  _ _ = refl
  ∧-true-left false _ ()

  -- The initial state always places ProofPreimage.inputs in memory,
  -- regardless of the communications-commitment flag.
  init-state-memory : ∀ src pre s₀
    → init-state src pre ≡ just s₀
    → Preprocessed.memory s₀ ≡ ProofPreimage.inputs pre
  init-state-memory src pre s₀ eq
    with length (ProofPreimage.inputs pre) ≡ᵇ IrSource.num-inputs src
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _     | _      with eq
  ...   | ()
  init-state-memory src pre s₀ eq
       | true  | false | _      = sym (cong Preprocessed.memory (just-injective eq))
  init-state-memory src pre s₀ eq
       | true  | true  | just _ = sym (cong Preprocessed.memory (just-injective eq))
  init-state-memory src pre s₀ eq
       | true  | true  | nothing with eq
  ...   | ()

  mem-refl : ∀ {s s' : Preprocessed}
    → s ≡ s'
    → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
  mem-refl s-eq = ≤-reflexive (cong length (cong Preprocessed.memory s-eq))

  push-mem-≤ : ∀ s v
    → length (Preprocessed.memory s) ≤ length (Preprocessed.memory (push-mem s v))
  push-mem-≤ s _ = length-++-≤ˡ (Preprocessed.memory s)

  push-mem2-≤ : ∀ s v₁ v₂
    → length (Preprocessed.memory s) ≤ length (Preprocessed.memory (push-mem2 s v₁ v₂))
  push-mem2-≤ s _ _ = length-++-≤ˡ (Preprocessed.memory s)

  -- Transport a memory-length bound along the post-state equality the
  -- mem-≤ clauses recover from `preprocess-instr`.  Replaces the
  -- per-clause `subst (λ x → length (memory s) ≤ length (memory x)) …`.
  mem-≤-by : ∀ (s : Preprocessed) {t s'} → t ≡ s'
    → length (Preprocessed.memory s) ≤ length (Preprocessed.memory t)
    → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
  mem-≤-by _ refl le = le

  consume-pub-out-mem : ∀ s v s'
    → consume-pub-out s ≡ just (v , s')
    → Preprocessed.memory s' ≡ Preprocessed.memory s
  consume-pub-out-mem s v s' eq
    with Preprocessed.pub-out-rem s | eq
  ... | []     | ()
  ... | _ ∷ _  | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))

  consume-priv-mem : ∀ s v s'
    → consume-priv s ≡ just (v , s')
    → Preprocessed.memory s' ≡ Preprocessed.memory s
  consume-priv-mem s v s' eq
    with Preprocessed.priv-rem s | eq
  ... | []     | ()
  ... | _ ∷ _  | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))

  from-just-R : ∀ {pre s i t s'} → R-instr pre s i t → just t ≡ just s' → R-instr pre s i s'
  from-just-R r refl = r

  ∧-true-right : ∀ (a b : Bool) → a ∧ b ≡ true → b ≡ true
  ∧-true-right true  _ eq = eq
  ∧-true-right false _ ()

------------------------------------------------------------------------
-- 1. Transcript consumption
-- A successful preprocessing fully consumes all three transcript streams.
------------------------------------------------------------------------

preprocess-transcripts-consumed : ∀ src pre s
  → preprocess src pre ≡ just s
  → transcripts-consumed pre s ≡ true
preprocess-transcripts-consumed src pre s eq
  with >>=-just (init-state src pre) eq
... | s₀ , _ , eq₁
  with >>=-just (preprocess-instrs pre s₀ (IrSource.instructions src)) eq₁
... | s' , _ , eq₂
  with if-just _ eq₂
... | b-true , s'-eq
  = subst (λ x → transcripts-consumed pre x ≡ true) s'-eq
      (∧-true-left _ _ b-true)

------------------------------------------------------------------------
-- 3. Memory monotonicity
------------------------------------------------------------------------

-- Per-instruction lemmas: assert, constrain-*, declare-pub-input,
-- pi-skip, output leave memory unchanged; all others grow it.

preprocess-instr-mem-≤ : ∀ pre s i s'
  → preprocess-instr pre s i ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤ _ s (assert cond) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) cond >>= to-bool) eq
... | b , _ , eq₁
  with if-just b eq₁
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤ _ s (constrain-bits var bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , _ , eq₁
  with if-just (fits-in v bits) eq₁
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤ _ s (constrain-eq a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , _ , eq₂
  with if-just (av ≡ᶠ? bv) eq₂
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤ _ s (constrain-to-boolean var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var >>= to-bool) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤ _ s (declare-pub-input var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤ pre s (pi-skip guard count) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | false , _ , eq₁ = mem-refl (just-injective eq₁)
... | true  , _ , eq₁
  with if-just _ eq₁
... | _ , ps-eq = mem-refl ps-eq

preprocess-instr-mem-≤ _ s (output var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤ _ s (cond-select bit a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) bit >>= to-bool) eq
... | bv , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq₁
... | av , _ , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₂
... | _ , _ , eq₃
  = mem-≤-by s (just-injective eq₃) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (copy var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁
  = mem-≤-by s (just-injective eq₁) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (ec-add a_x a_y b_x b_y) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a_x) eq
... | ax , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a_y) eq₁
... | ay , _ , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) b_x) eq₂
... | bx , _ , eq₃
  with >>=-just (mem-lookup (Preprocessed.memory s) b_y) eq₃
... | by , _ , eq₄
  with >>=-just (ec-add-pts ax ay bx by) eq₄
... | (cx , cy) , _ , eq₅
  = mem-≤-by s (just-injective eq₅) (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤ _ s (ec-mul a_x a_y scalar) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a_x) eq
... | ax , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a_y) eq₁
... | ay , _ , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq₂
... | sc , _ , eq₃
  with >>=-just (ec-mul-pt ax ay sc) eq₃
... | (cx , cy) , _ , eq₄
  = mem-≤-by s (just-injective eq₄) (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤ _ s (ec-mul-generator scalar) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq
... | sc , _ , eq₁
  with ec-mul-gen sc
... | (cx , cy)
  = mem-≤-by s (just-injective eq₁) (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤ _ s (hash-to-curve inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , _ , eq₁
  with hash-to-curve-fn vs
... | (cx , cy)
  = mem-≤-by s (just-injective eq₁) (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤ _ s (load-imm imm) s' eq
  = mem-≤-by s (just-injective eq) (push-mem-≤ s imm)

preprocess-instr-mem-≤ _ s (div-mod-power-of-two var bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁
  = mem-≤-by s (just-injective eq₁) (≤-trans (push-mem-≤ s _) (push-mem-≤ (push-mem s _) _))

preprocess-instr-mem-≤ _ s (reconstitute-field d m bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) d) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) m) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = mem-≤-by s s-eq (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (transient-hash inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | _ , _ , eq₁
  = mem-≤-by s (just-injective eq₁) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (persistent-hash alignment inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , _ , eq₁
  with persistent-hash-fn alignment vs
... | (h₁ , h₂)
  = mem-≤-by s (just-injective eq₁) (push-mem2-≤ s h₁ h₂)

preprocess-instr-mem-≤ _ s (test-eq a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = mem-≤-by s (just-injective eq₂) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (add a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = mem-≤-by s (just-injective eq₂) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (mul a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = mem-≤-by s (just-injective eq₂) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (neg a) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  = mem-≤-by s (just-injective eq₁) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (not a) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a >>= to-bool) eq
... | _ , _ , eq₁
  = mem-≤-by s (just-injective eq₁) (push-mem-≤ s _)

preprocess-instr-mem-≤ _ s (less-than a b bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = mem-≤-by s s-eq (push-mem-≤ s _)

preprocess-instr-mem-≤ pre s (public-input guard) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = mem-≤-by s (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-pub-out s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = mem-≤-by s (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-pub-out-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))

preprocess-instr-mem-≤ pre s (private-input guard) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = mem-≤-by s (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-priv s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = mem-≤-by s (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-priv-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))


-- Executing a sequence of instructions does not shrink the memory.
preprocess-instrs-mono : ∀ pre s is s'
  → preprocess-instrs pre s is ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instrs-mono _ s [] s' eq
  = ≤-reflexive (cong length (cong Preprocessed.memory (just-injective eq)))
preprocess-instrs-mono pre s (i ∷ is) s' eq
  with >>=-just (preprocess-instr pre s i) eq
... | s₁ , eq₁ , eq₂
  = ≤-trans
      (preprocess-instr-mem-≤ pre s i s₁ eq₁)
      (preprocess-instrs-mono pre s₁ is s' eq₂)

-- A successful top-level preprocessing grows (or preserves) the initial memory.
preprocess-memory-mono : ∀ src pre s
  → preprocess src pre ≡ just s
  → length (ProofPreimage.inputs pre) ≤ length (Preprocessed.memory s)
preprocess-memory-mono src pre s eq
  with >>=-just (init-state src pre) eq
... | s₀ , eq₀ , eq₁
  with >>=-just (preprocess-instrs pre s₀ (IrSource.instructions src)) eq₁
... | s' , eq₂ , eq₃
  with if-just _ eq₃
... | _ , s'-eq
  = ≤-trans
      (≤-reflexive (sym (cong length (init-state-memory src pre s₀ eq₀))))
      (preprocess-instrs-mono pre s₀ (IrSource.instructions src) s
        (subst (λ x → preprocess-instrs pre s₀ (IrSource.instructions src) ≡ just x) s'-eq eq₂))

------------------------------------------------------------------------
-- 4. Faithfulness
-- The computational and relational semantics agree.
------------------------------------------------------------------------

-- Per-instruction: computational → relational

preprocess-instr→R-instr : ∀ pre s i s'
  → preprocess-instr pre s i ≡ just s' → R-instr pre s i s'
preprocess-instr→R-instr _ s (assert cond) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) cond >>= to-bool) eq
... | b , lb , eq₁
  with if-just b eq₁
... | b-true , s-eq
  = subst (R-instr _ s (assert cond)) s-eq
      (r-assert (subst (λ x → _ ≡ just x) b-true lb))

preprocess-instr→R-instr _ s (cond-select bit a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) bit >>= to-bool) eq
... | sel , lsel , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq₁
... | av , la , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₂
... | bv , lb , eq₃
  = from-just-R (r-cond-select lsel la lb) eq₃

preprocess-instr→R-instr _ s (constrain-bits var bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , lv , eq₁
  with if-just (fits-in v bits) eq₁
... | fits , s-eq
  = subst (R-instr _ s (constrain-bits var bits)) s-eq (r-constrain-bits lv fits)

preprocess-instr→R-instr _ s (constrain-eq a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , lb , eq₂
  with if-just (av ≡ᶠ? bv) eq₂
... | eq? , s-eq
  = subst (R-instr _ s (constrain-eq a b)) s-eq (r-constrain-eq la lb eq?)

preprocess-instr→R-instr _ s (constrain-to-boolean var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var >>= to-bool) eq
... | b , lb , eq₁
  = subst (R-instr _ s (constrain-to-boolean var)) (just-injective eq₁) (r-constrain-to-boolean lb)

preprocess-instr→R-instr _ s (copy var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , lv , eq₁ = from-just-R (r-copy lv) eq₁

preprocess-instr→R-instr _ s (declare-pub-input var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , lv , eq₁ = from-just-R (r-declare-pub-input lv) eq₁

preprocess-instr→R-instr pre s (pi-skip guard count) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | false , gf , eq₁ = from-just-R (r-pi-skip-inactive gf) eq₁
... | true  , gt , eq₁
  with if-just _ eq₁
... | chk , s-eq
  = subst (R-instr pre s (pi-skip guard count)) s-eq (r-pi-skip-active gt chk)

preprocess-instr→R-instr _ s (ec-add a_x a_y b_x b_y) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a_x) eq
... | ax , lax , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a_y) eq₁
... | ay , lay , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) b_x) eq₂
... | bx , lbx , eq₃
  with >>=-just (mem-lookup (Preprocessed.memory s) b_y) eq₃
... | by , lby , eq₄
  with >>=-just (ec-add-pts ax ay bx by) eq₄
... | (cx , cy) , add-eq , eq₅ = from-just-R (r-ec-add lax lay lbx lby add-eq) eq₅

preprocess-instr→R-instr _ s (ec-mul a_x a_y scalar) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a_x) eq
... | ax , lax , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a_y) eq₁
... | ay , lay , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq₂
... | sc , lsc , eq₃
  with >>=-just (ec-mul-pt ax ay sc) eq₃
... | (cx , cy) , mul-eq , eq₄ = from-just-R (r-ec-mul lax lay lsc mul-eq) eq₄

preprocess-instr→R-instr _ s (ec-mul-generator scalar) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq
... | sc , lsc , eq₁
  = subst (R-instr _ s (ec-mul-generator scalar)) (just-injective eq₁) (r-ec-mul-generator lsc refl)

preprocess-instr→R-instr _ s (hash-to-curve inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , lvs , eq₁
  = subst (R-instr _ s (hash-to-curve inputs)) (just-injective eq₁) (r-hash-to-curve lvs refl)

preprocess-instr→R-instr _ s (load-imm imm) s' eq = from-just-R r-load-imm eq

preprocess-instr→R-instr _ s (div-mod-power-of-two var bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , lv , eq₁ = from-just-R (r-div-mod-power-of-two lv) eq₁

preprocess-instr→R-instr _ s (reconstitute-field divisor modulus bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) divisor) eq
... | dv , ldv , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) modulus) eq₁
... | mv , lmv , eq₂
  with if-just _ eq₂
... | cond , s-eq
  = subst (R-instr _ s (reconstitute-field divisor modulus bits)) s-eq
      (r-reconstitute-field ldv lmv cond)

preprocess-instr→R-instr _ s (output var) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , lv , eq₁ = from-just-R (r-output lv) eq₁

preprocess-instr→R-instr _ s (transient-hash inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , lvs , eq₁ = from-just-R (r-transient-hash lvs) eq₁

preprocess-instr→R-instr _ s (persistent-hash alignment inputs) s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , lvs , eq₁
  = subst (R-instr _ s (persistent-hash alignment inputs)) (just-injective eq₁) (r-persistent-hash lvs refl)

preprocess-instr→R-instr _ s (test-eq a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , lb , eq₂ = from-just-R (r-test-eq la lb) eq₂

preprocess-instr→R-instr _ s (add a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , lb , eq₂ = from-just-R (r-add la lb) eq₂

preprocess-instr→R-instr _ s (mul a b) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , lb , eq₂ = from-just-R (r-mul la lb) eq₂

preprocess-instr→R-instr _ s (neg a) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁ = from-just-R (r-neg la) eq₁

preprocess-instr→R-instr _ s (not a) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a >>= to-bool) eq
... | b , lb , eq₁ = from-just-R (r-not lb) eq₁

preprocess-instr→R-instr _ s (less-than a b bits) s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , la , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , lb , eq₂
  with if-just _ eq₂
... | fits , s-eq
  = subst (R-instr _ s (less-than a b bits)) s-eq (r-less-than la lb fits)

preprocess-instr→R-instr _ s (public-input guard) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | false , gf , eq₁ = from-just-R (r-public-input-inactive gf) eq₁
... | true  , gt , eq₁
  with >>=-just (consume-pub-out s) eq₁
... | (v , s₁) , cp , eq₂ = from-just-R (r-public-input-active gt cp) eq₂

preprocess-instr→R-instr _ s (private-input guard) s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | false , gf , eq₁ = from-just-R (r-private-input-inactive gf) eq₁
... | true  , gt , eq₁
  with >>=-just (consume-priv s) eq₁
... | (v , s₁) , cp , eq₂ = from-just-R (r-private-input-active gt cp) eq₂


-- Per-instruction: relational → computational

R-instr→preprocess-instr : ∀ pre s i s'
  → R-instr pre s i s' → preprocess-instr pre s i ≡ just s'
R-instr→preprocess-instr _ s (assert cond) _ (r-assert la) rewrite la = refl

R-instr→preprocess-instr _ s (cond-select bit a b) _ (r-cond-select lsel la lb) rewrite lsel | la | lb = refl

R-instr→preprocess-instr _ s (constrain-bits var bits) _ (r-constrain-bits lv fits) rewrite lv | fits = refl

R-instr→preprocess-instr _ s (constrain-eq a b) _ (r-constrain-eq la lb eq?) rewrite la | lb | eq? = refl

R-instr→preprocess-instr _ s (constrain-to-boolean var) _ (r-constrain-to-boolean lb) rewrite lb = refl

R-instr→preprocess-instr _ s (copy var) _ (r-copy lv) rewrite lv = refl

R-instr→preprocess-instr _ s (declare-pub-input var) _ (r-declare-pub-input lv) rewrite lv = refl

R-instr→preprocess-instr pre s (pi-skip guard count) _ (r-pi-skip-active gt chk) rewrite gt | chk = refl
R-instr→preprocess-instr pre s (pi-skip guard count) _ (r-pi-skip-inactive gf)   rewrite gf       = refl

R-instr→preprocess-instr _ s (ec-add a_x a_y b_x b_y) _ (r-ec-add lax lay lbx lby add-eq)
  rewrite lax | lay | lbx | lby | add-eq = refl

R-instr→preprocess-instr _ s (ec-mul a_x a_y scalar) _ (r-ec-mul lax lay lsc mul-eq)
  rewrite lax | lay | lsc | mul-eq = refl

R-instr→preprocess-instr _ s (ec-mul-generator scalar) _ (r-ec-mul-generator lsc gen-eq)
  rewrite lsc | gen-eq = refl

R-instr→preprocess-instr _ s (hash-to-curve inputs) _ (r-hash-to-curve lvs htc-eq)
  rewrite lvs | htc-eq = refl

R-instr→preprocess-instr _ s (load-imm imm) _ r-load-imm = refl

R-instr→preprocess-instr _ s (div-mod-power-of-two var bits) _ (r-div-mod-power-of-two lv) rewrite lv = refl

R-instr→preprocess-instr _ s (reconstitute-field divisor modulus bits) _ (r-reconstitute-field ldv lmv cond)
  rewrite ldv | lmv | cond = refl

R-instr→preprocess-instr _ s (output var) _ (r-output lv) rewrite lv = refl

R-instr→preprocess-instr _ s (transient-hash inputs) _ (r-transient-hash lvs) rewrite lvs = refl

R-instr→preprocess-instr _ s (persistent-hash alignment inputs) _ (r-persistent-hash lvs ph-eq)
  rewrite lvs | ph-eq = refl

R-instr→preprocess-instr _ s (test-eq a b) _ (r-test-eq la lb) rewrite la | lb = refl

R-instr→preprocess-instr _ s (add a b) _ (r-add la lb) rewrite la | lb = refl

R-instr→preprocess-instr _ s (mul a b) _ (r-mul la lb) rewrite la | lb = refl

R-instr→preprocess-instr _ s (neg a) _ (r-neg la) rewrite la = refl

R-instr→preprocess-instr _ s (not a) _ (r-not lb) rewrite lb = refl

R-instr→preprocess-instr _ s (less-than a b bits) _ (r-less-than la lb fits) rewrite la | lb | fits = refl

R-instr→preprocess-instr _ s (public-input guard) _ (r-public-input-inactive gf) rewrite gf       = refl
R-instr→preprocess-instr _ s (public-input guard) _ (r-public-input-active gt cp) rewrite gt | cp = refl

R-instr→preprocess-instr _ s (private-input guard) _ (r-private-input-inactive gf) rewrite gf       = refl
R-instr→preprocess-instr _ s (private-input guard) _ (r-private-input-active gt cp) rewrite gt | cp = refl


-- Lift faithfulness from instructions to instruction sequences.

preprocess-instrs→R-instrs : ∀ pre s is s'
  → preprocess-instrs pre s is ≡ just s' → R-instrs pre s is s'
preprocess-instrs→R-instrs _ s [] s' eq
  = subst (R-instrs _ s []) (just-injective eq) r-done
preprocess-instrs→R-instrs pre s (i ∷ is) s' eq
  with >>=-just (preprocess-instr pre s i) eq
... | s₁ , eq₁ , eq₂
  = r-step (preprocess-instr→R-instr pre s i s₁ eq₁)
           (preprocess-instrs→R-instrs pre s₁ is s' eq₂)

R-instrs→preprocess-instrs : ∀ pre s is s'
  → R-instrs pre s is s' → preprocess-instrs pre s is ≡ just s'
R-instrs→preprocess-instrs _ _ [] _ r-done = refl
R-instrs→preprocess-instrs pre s (i ∷ is) s' (r-step ri ris)
  with R-instr→preprocess-instr pre s i _ ri
... | eq₁ rewrite eq₁ = R-instrs→preprocess-instrs pre _ is s' ris

-- Top-level faithfulness.

preprocess→R : ∀ src pre s → preprocess src pre ≡ just s → R src pre s
preprocess→R src pre s eq
  with >>=-just (init-state src pre) eq
... | s₀ , eq₀ , eq₁
  with >>=-just (preprocess-instrs pre s₀ (IrSource.instructions src)) eq₁
... | s' , eq₂ , eq₃
  with if-just _ eq₃
... | tc-co , s'-eq
  = s₀ , eq₀ ,
    subst (R-instrs pre s₀ (IrSource.instructions src)) s'-eq
      (preprocess-instrs→R-instrs pre s₀ (IrSource.instructions src) s' eq₂) ,
    subst (λ x → transcripts-consumed pre x ≡ true) s'-eq
      (∧-true-left _ _ tc-co) ,
    subst (λ x → comm-ok src pre x ≡ true) s'-eq
      (∧-true-right _ _ tc-co)

R→preprocess : ∀ src pre s → R src pre s → preprocess src pre ≡ just s
R→preprocess src pre s (s₀ , init-eq , ris , tc , co)
  with R-instrs→preprocess-instrs pre s₀ (IrSource.instructions src) s ris
... | instrs-eq rewrite init-eq | instrs-eq | tc | co = refl

------------------------------------------------------------------------
-- 5. Circuit correctness (Property P5, spec §6.2)
--
-- The Halo2 constraint-synthesis function `circuit` is faithful to the
-- relational semantics `R`.  This was formerly postulated against an
-- *opaque* constraint-system model; it is now fully MECHANISED in
-- `CircuitProof` against the concrete `Circuit` / `satisfies` model and
-- re-exported here.
--
-- The faithful statement carries the two preconditions established
-- during the mechanisation (both genuinely required — see CircuitProof):
--
--   • producer-safety  `producer-safe src ≡ true`               (§6.4)
--   • input arity      `length (inputs pre) ≡ num-inputs src`    (§3.4, WF1)
--   • shape            `preprocess-shaped src pre s`             (§5.4)
--
-- and concludes the spec's biconditional as a logical equivalence
-- (`_⇔_`):  `R src pre s ⇔ satisfies (circuit src) (witness-of s pre)`.
--
-- `circuit-faithful` is re-exported from `CircuitProof` (see the import
-- list above); its full statement is:
--
--   circuit-faithful : ∀ src pre s
--     → producer-safe src ≡ true
--     → length (inputs pre) ≡ num-inputs src
--     → preprocess-shaped src pre s
--     → R src pre s ⇔ satisfies (circuit src) (witness-of s pre)
------------------------------------------------------------------------
