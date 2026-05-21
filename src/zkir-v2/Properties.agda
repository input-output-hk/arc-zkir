module zkir-v2.Properties where

open import zkir-v2.Syntax
open import zkir-v2.Semantics

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.List    using (List; []; _∷_; length)
open import Data.List.Properties using (length-++-≤ˡ)
open import Data.Maybe   using (Maybe; nothing; just; _>>=_)
open import Data.Nat     using (ℕ; _≤_)
open import Data.Nat.Properties  using (≤-trans; ≤-reflexive)
open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

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
    with IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _      = sym (cong Preprocessed.memory (just-injective eq))
  ... | true  | just _ = sym (cong Preprocessed.memory (just-injective eq))
  ... | true  | nothing with eq
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

preprocess-instr-mem-≤-assert : ∀ pre s cond s'
  → preprocess-instr pre s (assert cond) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-assert _ s cond s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) cond >>= to-bool) eq
... | b , _ , eq₁
  with if-just b eq₁
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤-constrain-bits : ∀ pre s var bits s'
  → preprocess-instr pre s (constrain-bits var bits) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-constrain-bits _ s var bits s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | v , _ , eq₁
  with if-just (fits-in v bits) eq₁
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤-constrain-eq : ∀ pre s a b s'
  → preprocess-instr pre s (constrain-eq a b) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-constrain-eq _ s a b s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | av , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | bv , _ , eq₂
  with if-just (av ≡ᶠ? bv) eq₂
... | _ , s-eq = mem-refl s-eq

preprocess-instr-mem-≤-constrain-to-boolean : ∀ pre s var s'
  → preprocess-instr pre s (constrain-to-boolean var) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-constrain-to-boolean _ s var s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var >>= to-bool) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤-declare-pub-input : ∀ pre s var s'
  → preprocess-instr pre s (declare-pub-input var) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-declare-pub-input _ s var s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤-pi-skip : ∀ pre s guard count s'
  → preprocess-instr pre s (pi-skip guard count) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-pi-skip pre s guard count s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | false , _ , eq₁ = mem-refl (just-injective eq₁)
... | true  , _ , eq₁
  with if-just _ eq₁
... | _ , ps-eq = mem-refl ps-eq

preprocess-instr-mem-≤-output : ∀ pre s var s'
  → preprocess-instr pre s (output var) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-output _ s var s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

preprocess-instr-mem-≤-cond-select : ∀ pre s bit a b s'
  → preprocess-instr pre s (cond-select bit a b) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-cond-select _ s bit a b s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) bit >>= to-bool) eq
... | bv , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq₁
... | av , _ , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₂
... | _ , _ , eq₃
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₃)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-copy : ∀ pre s var s'
  → preprocess-instr pre s (copy var) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-copy _ s var s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-ec-add : ∀ pre s a_x a_y b_x b_y s'
  → preprocess-instr pre s (ec-add a_x a_y b_x b_y) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-ec-add _ s a_x a_y b_x b_y s' eq
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
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₅)
      (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤-ec-mul : ∀ pre s a_x a_y scalar s'
  → preprocess-instr pre s (ec-mul a_x a_y scalar) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-ec-mul _ s a_x a_y scalar s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a_x) eq
... | ax , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) a_y) eq₁
... | ay , _ , eq₂
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq₂
... | sc , _ , eq₃
  with >>=-just (ec-mul-pt ax ay sc) eq₃
... | (cx , cy) , _ , eq₄
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₄)
      (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤-ec-mul-generator : ∀ pre s scalar s'
  → preprocess-instr pre s (ec-mul-generator scalar) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-ec-mul-generator _ s scalar s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) scalar) eq
... | sc , _ , eq₁
  with ec-mul-gen sc
... | (cx , cy)
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤-hash-to-curve : ∀ pre s inputs s'
  → preprocess-instr pre s (hash-to-curve inputs) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-hash-to-curve _ s inputs s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , _ , eq₁
  with hash-to-curve-fn vs
... | (cx , cy)
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s cx cy)

preprocess-instr-mem-≤-load-imm : ∀ pre s imm s'
  → preprocess-instr pre s (load-imm imm) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-load-imm _ s imm s' eq
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq)
      (push-mem-≤ s imm)

preprocess-instr-mem-≤-div-mod-power-of-two : ∀ pre s var bits s'
  → preprocess-instr pre s (div-mod-power-of-two var bits) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-div-mod-power-of-two _ s var bits s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) var) eq
... | _ , _ , eq₁
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (≤-trans (push-mem-≤ s _) (push-mem-≤ (push-mem s _) _))

preprocess-instr-mem-≤-reconstitute-field : ∀ pre s d m bits s'
  → preprocess-instr pre s (reconstitute-field d m bits) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-reconstitute-field _ s d m bits s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) d) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) m) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      s-eq
      (push-mem-≤ s _)

preprocess-instr-mem-≤-transient-hash : ∀ pre s inputs s'
  → preprocess-instr pre s (transient-hash inputs) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-transient-hash _ s inputs s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | _ , _ , eq₁
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-persistent-hash : ∀ pre s alignment inputs s'
  → preprocess-instr pre s (persistent-hash alignment inputs) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-persistent-hash _ s alignment inputs s' eq
  with >>=-just (mem-lookups (Preprocessed.memory s) inputs) eq
... | vs , _ , eq₁
  with persistent-hash-fn alignment vs
... | (h₁ , h₂)
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s h₁ h₂)

preprocess-instr-mem-≤-test-eq : ∀ pre s a b s'
  → preprocess-instr pre s (test-eq a b) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-test-eq _ s a b s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-add : ∀ pre s a b s'
  → preprocess-instr pre s (add a b) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-add _ s a b s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-mul : ∀ pre s a b s'
  → preprocess-instr pre s (mul a b) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-mul _ s a b s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-neg : ∀ pre s a s'
  → preprocess-instr pre s (neg a) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-neg _ s a s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-not : ∀ pre s a s'
  → preprocess-instr pre s (not a) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-not _ s a s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a >>= to-bool) eq
... | _ , _ , eq₁
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

preprocess-instr-mem-≤-less-than : ∀ pre s a b bits s'
  → preprocess-instr pre s (less-than a b bits) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-less-than _ s a b bits s' eq
  with >>=-just (mem-lookup (Preprocessed.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (Preprocessed.memory s) b) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      s-eq
      (push-mem-≤ s _)

preprocess-instr-mem-≤-public-input : ∀ pre s guard s'
  → preprocess-instr pre s (public-input guard) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-public-input pre s guard s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-pub-out s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-pub-out-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))

preprocess-instr-mem-≤-private-input : ∀ pre s guard s'
  → preprocess-instr pre s (private-input guard) ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤-private-input pre s guard s' eq
  with >>=-just (eval-guard (Preprocessed.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-priv s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = subst (λ x → length (Preprocessed.memory s) ≤ length (Preprocessed.memory x))
      (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-priv-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))

-- Combine the 26 per-instruction lemmas into the general statement.
preprocess-instr-mem-≤ : ∀ pre s i s'
  → preprocess-instr pre s i ≡ just s'
  → length (Preprocessed.memory s) ≤ length (Preprocessed.memory s')
preprocess-instr-mem-≤ pre s (assert cond)                   = preprocess-instr-mem-≤-assert                pre s cond
preprocess-instr-mem-≤ pre s (cond-select bit a b)           = preprocess-instr-mem-≤-cond-select            pre s bit a b
preprocess-instr-mem-≤ pre s (constrain-bits var bits)       = preprocess-instr-mem-≤-constrain-bits         pre s var bits
preprocess-instr-mem-≤ pre s (constrain-eq a b)              = preprocess-instr-mem-≤-constrain-eq           pre s a b
preprocess-instr-mem-≤ pre s (constrain-to-boolean var)      = preprocess-instr-mem-≤-constrain-to-boolean   pre s var
preprocess-instr-mem-≤ pre s (copy var)                      = preprocess-instr-mem-≤-copy                   pre s var
preprocess-instr-mem-≤ pre s (declare-pub-input var)         = preprocess-instr-mem-≤-declare-pub-input      pre s var
preprocess-instr-mem-≤ pre s (pi-skip guard count)           = preprocess-instr-mem-≤-pi-skip                pre s guard count
preprocess-instr-mem-≤ pre s (ec-add a_x a_y b_x b_y)       = preprocess-instr-mem-≤-ec-add                 pre s a_x a_y b_x b_y
preprocess-instr-mem-≤ pre s (ec-mul a_x a_y scalar)         = preprocess-instr-mem-≤-ec-mul                 pre s a_x a_y scalar
preprocess-instr-mem-≤ pre s (ec-mul-generator scalar)       = preprocess-instr-mem-≤-ec-mul-generator       pre s scalar
preprocess-instr-mem-≤ pre s (hash-to-curve inputs)          = preprocess-instr-mem-≤-hash-to-curve          pre s inputs
preprocess-instr-mem-≤ pre s (load-imm imm)                  = preprocess-instr-mem-≤-load-imm               pre s imm
preprocess-instr-mem-≤ pre s (div-mod-power-of-two var bits) = preprocess-instr-mem-≤-div-mod-power-of-two   pre s var bits
preprocess-instr-mem-≤ pre s (reconstitute-field d m bits)   = preprocess-instr-mem-≤-reconstitute-field     pre s d m bits
preprocess-instr-mem-≤ pre s (output var)                    = preprocess-instr-mem-≤-output                 pre s var
preprocess-instr-mem-≤ pre s (transient-hash inputs)         = preprocess-instr-mem-≤-transient-hash         pre s inputs
preprocess-instr-mem-≤ pre s (persistent-hash alignment is)  = preprocess-instr-mem-≤-persistent-hash        pre s alignment is
preprocess-instr-mem-≤ pre s (test-eq a b)                   = preprocess-instr-mem-≤-test-eq                pre s a b
preprocess-instr-mem-≤ pre s (add a b)                       = preprocess-instr-mem-≤-add                    pre s a b
preprocess-instr-mem-≤ pre s (mul a b)                       = preprocess-instr-mem-≤-mul                    pre s a b
preprocess-instr-mem-≤ pre s (neg a)                         = preprocess-instr-mem-≤-neg                    pre s a
preprocess-instr-mem-≤ pre s (not a)                         = preprocess-instr-mem-≤-not                    pre s a
preprocess-instr-mem-≤ pre s (less-than a b bits)            = preprocess-instr-mem-≤-less-than              pre s a b bits
preprocess-instr-mem-≤ pre s (public-input guard)            = preprocess-instr-mem-≤-public-input           pre s guard
preprocess-instr-mem-≤ pre s (private-input guard)           = preprocess-instr-mem-≤-private-input          pre s guard

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
