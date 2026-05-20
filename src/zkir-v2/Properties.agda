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
    → ExecState.memory s₀ ≡ ProofPreimage.inputs pre
  init-state-memory src pre s₀ eq
    with IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _      = sym (cong ExecState.memory (just-injective eq))
  ... | true  | just _ = sym (cong ExecState.memory (just-injective eq))
  ... | true  | nothing with eq
  ...   | ()

  mem-refl : ∀ {s s' : ExecState}
    → s ≡ s'
    → length (ExecState.memory s) ≤ length (ExecState.memory s')
  mem-refl s-eq = ≤-reflexive (cong length (cong ExecState.memory s-eq))

  push-mem-≤ : ∀ s v
    → length (ExecState.memory s) ≤ length (ExecState.memory (push-mem s v))
  push-mem-≤ s _ = length-++-≤ˡ (ExecState.memory s)

  push-mem2-≤ : ∀ s v₁ v₂
    → length (ExecState.memory s) ≤ length (ExecState.memory (push-mem2 s v₁ v₂))
  push-mem2-≤ s _ _ = length-++-≤ˡ (ExecState.memory s)

  consume-pub-out-mem : ∀ s v s'
    → consume-pub-out s ≡ just (v , s')
    → ExecState.memory s' ≡ ExecState.memory s
  consume-pub-out-mem s v s' eq
    with ExecState.pub-out-rem s | eq
  ... | []     | ()
  ... | _ ∷ _  | p = sym (cong ExecState.memory (cong proj₂ (just-injective p)))

  consume-priv-mem : ∀ s v s'
    → consume-priv s ≡ just (v , s')
    → ExecState.memory s' ≡ ExecState.memory s
  consume-priv-mem s v s' eq
    with ExecState.priv-rem s | eq
  ... | []     | ()
  ... | _ ∷ _  | p = sym (cong ExecState.memory (cong proj₂ (just-injective p)))

------------------------------------------------------------------------
-- 1. Transcript consumption
-- A successful execution fully consumes all three transcript streams.
------------------------------------------------------------------------

exec-transcripts-consumed : ∀ src pre s
  → exec src pre ≡ just s
  → transcripts-consumed pre s ≡ true
exec-transcripts-consumed src pre s eq
  with >>=-just (init-state src pre) eq
... | s₀ , _ , eq₁
  with >>=-just (exec-instrs pre s₀ (IrSource.instructions src)) eq₁
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

exec-instr-mem-≤-assert : ∀ pre s cond s'
  → exec-instr pre s (assert cond) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-assert _ s cond s' eq
  with >>=-just (mem-lookup (ExecState.memory s) cond >>= to-bool) eq
... | b , _ , eq₁
  with if-just b eq₁
... | _ , s-eq = mem-refl s-eq

exec-instr-mem-≤-constrain-bits : ∀ pre s var bits s'
  → exec-instr pre s (constrain-bits var bits) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-constrain-bits _ s var bits s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var) eq
... | v , _ , eq₁
  with if-just (fits-in v bits) eq₁
... | _ , s-eq = mem-refl s-eq

exec-instr-mem-≤-constrain-eq : ∀ pre s a b s'
  → exec-instr pre s (constrain-eq a b) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-constrain-eq _ s a b s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | av , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₁
... | bv , _ , eq₂
  with if-just (av ≡ᶠ? bv) eq₂
... | _ , s-eq = mem-refl s-eq

exec-instr-mem-≤-constrain-to-boolean : ∀ pre s var s'
  → exec-instr pre s (constrain-to-boolean var) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-constrain-to-boolean _ s var s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var >>= to-bool) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

exec-instr-mem-≤-declare-pub-input : ∀ pre s var s'
  → exec-instr pre s (declare-pub-input var) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-declare-pub-input _ s var s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

exec-instr-mem-≤-pi-skip : ∀ pre s guard count s'
  → exec-instr pre s (pi-skip guard count) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-pi-skip pre s guard count s' eq
  with >>=-just (eval-guard (ExecState.memory s) guard) eq
... | false , _ , eq₁ = mem-refl (just-injective eq₁)
... | true  , _ , eq₁
  with if-just _ eq₁
... | _ , ps-eq = mem-refl ps-eq

exec-instr-mem-≤-output : ∀ pre s var s'
  → exec-instr pre s (output var) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-output _ s var s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var) eq
... | _ , _ , eq₁ = mem-refl (just-injective eq₁)

exec-instr-mem-≤-cond-select : ∀ pre s bit a b s'
  → exec-instr pre s (cond-select bit a b) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-cond-select _ s bit a b s' eq
  with >>=-just (mem-lookup (ExecState.memory s) bit >>= to-bool) eq
... | bv , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) a) eq₁
... | av , _ , eq₂
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₂
... | _ , _ , eq₃
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₃)
      (push-mem-≤ s _)

exec-instr-mem-≤-copy : ∀ pre s var s'
  → exec-instr pre s (copy var) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-copy _ s var s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var) eq
... | _ , _ , eq₁
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

exec-instr-mem-≤-ec-add : ∀ pre s a_x a_y b_x b_y s'
  → exec-instr pre s (ec-add a_x a_y b_x b_y) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-ec-add _ s a_x a_y b_x b_y s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a_x) eq
... | ax , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) a_y) eq₁
... | ay , _ , eq₂
  with >>=-just (mem-lookup (ExecState.memory s) b_x) eq₂
... | bx , _ , eq₃
  with >>=-just (mem-lookup (ExecState.memory s) b_y) eq₃
... | by , _ , eq₄
  with >>=-just (ec-add-pts ax ay bx by) eq₄
... | (cx , cy) , _ , eq₅
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₅)
      (push-mem2-≤ s cx cy)

exec-instr-mem-≤-ec-mul : ∀ pre s a_x a_y scalar s'
  → exec-instr pre s (ec-mul a_x a_y scalar) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-ec-mul _ s a_x a_y scalar s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a_x) eq
... | ax , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) a_y) eq₁
... | ay , _ , eq₂
  with >>=-just (mem-lookup (ExecState.memory s) scalar) eq₂
... | sc , _ , eq₃
  with >>=-just (ec-mul-pt ax ay sc) eq₃
... | (cx , cy) , _ , eq₄
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₄)
      (push-mem2-≤ s cx cy)

exec-instr-mem-≤-ec-mul-generator : ∀ pre s scalar s'
  → exec-instr pre s (ec-mul-generator scalar) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-ec-mul-generator _ s scalar s' eq
  with >>=-just (mem-lookup (ExecState.memory s) scalar) eq
... | sc , _ , eq₁
  with ec-mul-gen sc
... | (cx , cy)
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s cx cy)

exec-instr-mem-≤-hash-to-curve : ∀ pre s inputs s'
  → exec-instr pre s (hash-to-curve inputs) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-hash-to-curve _ s inputs s' eq
  with >>=-just (mem-lookups (ExecState.memory s) inputs) eq
... | vs , _ , eq₁
  with hash-to-curve-fn vs
... | (cx , cy)
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s cx cy)

exec-instr-mem-≤-load-imm : ∀ pre s imm s'
  → exec-instr pre s (load-imm imm) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-load-imm _ s imm s' eq
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq)
      (push-mem-≤ s imm)

exec-instr-mem-≤-div-mod-power-of-two : ∀ pre s var bits s'
  → exec-instr pre s (div-mod-power-of-two var bits) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-div-mod-power-of-two _ s var bits s' eq
  with >>=-just (mem-lookup (ExecState.memory s) var) eq
... | _ , _ , eq₁
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (≤-trans (push-mem-≤ s _) (push-mem-≤ (push-mem s _) _))

exec-instr-mem-≤-reconstitute-field : ∀ pre s d m bits s'
  → exec-instr pre s (reconstitute-field d m bits) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-reconstitute-field _ s d m bits s' eq
  with >>=-just (mem-lookup (ExecState.memory s) d) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) m) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      s-eq
      (push-mem-≤ s _)

exec-instr-mem-≤-transient-hash : ∀ pre s inputs s'
  → exec-instr pre s (transient-hash inputs) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-transient-hash _ s inputs s' eq
  with >>=-just (mem-lookups (ExecState.memory s) inputs) eq
... | _ , _ , eq₁
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

exec-instr-mem-≤-persistent-hash : ∀ pre s alignment inputs s'
  → exec-instr pre s (persistent-hash alignment inputs) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-persistent-hash _ s alignment inputs s' eq
  with >>=-just (mem-lookups (ExecState.memory s) inputs) eq
... | vs , _ , eq₁
  with persistent-hash-fn alignment vs
... | (h₁ , h₂)
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem2-≤ s h₁ h₂)

exec-instr-mem-≤-test-eq : ∀ pre s a b s'
  → exec-instr pre s (test-eq a b) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-test-eq _ s a b s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

exec-instr-mem-≤-add : ∀ pre s a b s'
  → exec-instr pre s (add a b) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-add _ s a b s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

exec-instr-mem-≤-mul : ∀ pre s a b s'
  → exec-instr pre s (mul a b) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-mul _ s a b s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₁
... | _ , _ , eq₂
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₂)
      (push-mem-≤ s _)

exec-instr-mem-≤-neg : ∀ pre s a s'
  → exec-instr pre s (neg a) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-neg _ s a s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | _ , _ , eq₁
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

exec-instr-mem-≤-not : ∀ pre s a s'
  → exec-instr pre s (not a) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-not _ s a s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a >>= to-bool) eq
... | _ , _ , eq₁
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s _)

exec-instr-mem-≤-less-than : ∀ pre s a b bits s'
  → exec-instr pre s (less-than a b bits) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-less-than _ s a b bits s' eq
  with >>=-just (mem-lookup (ExecState.memory s) a) eq
... | _ , _ , eq₁
  with >>=-just (mem-lookup (ExecState.memory s) b) eq₁
... | _ , _ , eq₂
  with if-just _ eq₂
... | _ , s-eq
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      s-eq
      (push-mem-≤ s _)

exec-instr-mem-≤-public-input : ∀ pre s guard s'
  → exec-instr pre s (public-input guard) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-public-input pre s guard s' eq
  with >>=-just (eval-guard (ExecState.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-pub-out s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-pub-out-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))

exec-instr-mem-≤-private-input : ∀ pre s guard s'
  → exec-instr pre s (private-input guard) ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤-private-input pre s guard s' eq
  with >>=-just (eval-guard (ExecState.memory s) guard) eq
... | active , _ , eq₁
  with active
... | false
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₁)
      (push-mem-≤ s 0ᶠ)
... | true
  with >>=-just (consume-priv s) eq₁
... | (v , s₁) , eq₂ , eq₃
  = subst (λ x → length (ExecState.memory s) ≤ length (ExecState.memory x))
      (just-injective eq₃)
      (≤-trans
        (≤-reflexive (sym (cong length (consume-priv-mem s v s₁ eq₂))))
        (push-mem-≤ s₁ v))

-- Combine the 26 per-instruction lemmas into the general statement.
exec-instr-mem-≤ : ∀ pre s i s'
  → exec-instr pre s i ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instr-mem-≤ pre s (assert cond)                   = exec-instr-mem-≤-assert                pre s cond
exec-instr-mem-≤ pre s (cond-select bit a b)           = exec-instr-mem-≤-cond-select            pre s bit a b
exec-instr-mem-≤ pre s (constrain-bits var bits)       = exec-instr-mem-≤-constrain-bits         pre s var bits
exec-instr-mem-≤ pre s (constrain-eq a b)              = exec-instr-mem-≤-constrain-eq           pre s a b
exec-instr-mem-≤ pre s (constrain-to-boolean var)      = exec-instr-mem-≤-constrain-to-boolean   pre s var
exec-instr-mem-≤ pre s (copy var)                      = exec-instr-mem-≤-copy                   pre s var
exec-instr-mem-≤ pre s (declare-pub-input var)         = exec-instr-mem-≤-declare-pub-input      pre s var
exec-instr-mem-≤ pre s (pi-skip guard count)           = exec-instr-mem-≤-pi-skip                pre s guard count
exec-instr-mem-≤ pre s (ec-add a_x a_y b_x b_y)       = exec-instr-mem-≤-ec-add                 pre s a_x a_y b_x b_y
exec-instr-mem-≤ pre s (ec-mul a_x a_y scalar)         = exec-instr-mem-≤-ec-mul                 pre s a_x a_y scalar
exec-instr-mem-≤ pre s (ec-mul-generator scalar)       = exec-instr-mem-≤-ec-mul-generator       pre s scalar
exec-instr-mem-≤ pre s (hash-to-curve inputs)          = exec-instr-mem-≤-hash-to-curve          pre s inputs
exec-instr-mem-≤ pre s (load-imm imm)                  = exec-instr-mem-≤-load-imm               pre s imm
exec-instr-mem-≤ pre s (div-mod-power-of-two var bits) = exec-instr-mem-≤-div-mod-power-of-two   pre s var bits
exec-instr-mem-≤ pre s (reconstitute-field d m bits)   = exec-instr-mem-≤-reconstitute-field     pre s d m bits
exec-instr-mem-≤ pre s (output var)                    = exec-instr-mem-≤-output                 pre s var
exec-instr-mem-≤ pre s (transient-hash inputs)         = exec-instr-mem-≤-transient-hash         pre s inputs
exec-instr-mem-≤ pre s (persistent-hash alignment is)  = exec-instr-mem-≤-persistent-hash        pre s alignment is
exec-instr-mem-≤ pre s (test-eq a b)                   = exec-instr-mem-≤-test-eq                pre s a b
exec-instr-mem-≤ pre s (add a b)                       = exec-instr-mem-≤-add                    pre s a b
exec-instr-mem-≤ pre s (mul a b)                       = exec-instr-mem-≤-mul                    pre s a b
exec-instr-mem-≤ pre s (neg a)                         = exec-instr-mem-≤-neg                    pre s a
exec-instr-mem-≤ pre s (not a)                         = exec-instr-mem-≤-not                    pre s a
exec-instr-mem-≤ pre s (less-than a b bits)            = exec-instr-mem-≤-less-than              pre s a b bits
exec-instr-mem-≤ pre s (public-input guard)            = exec-instr-mem-≤-public-input           pre s guard
exec-instr-mem-≤ pre s (private-input guard)           = exec-instr-mem-≤-private-input          pre s guard

-- Executing a sequence of instructions does not shrink the memory.
exec-instrs-mono : ∀ pre s is s'
  → exec-instrs pre s is ≡ just s'
  → length (ExecState.memory s) ≤ length (ExecState.memory s')
exec-instrs-mono _ s [] s' eq
  = ≤-reflexive (cong length (cong ExecState.memory (just-injective eq)))
exec-instrs-mono pre s (i ∷ is) s' eq
  with >>=-just (exec-instr pre s i) eq
... | s₁ , eq₁ , eq₂
  = ≤-trans
      (exec-instr-mem-≤ pre s i s₁ eq₁)
      (exec-instrs-mono pre s₁ is s' eq₂)

-- A successful top-level execution grows (or preserves) the initial memory.
exec-memory-mono : ∀ src pre s
  → exec src pre ≡ just s
  → length (ProofPreimage.inputs pre) ≤ length (ExecState.memory s)
exec-memory-mono src pre s eq
  with >>=-just (init-state src pre) eq
... | s₀ , eq₀ , eq₁
  with >>=-just (exec-instrs pre s₀ (IrSource.instructions src)) eq₁
... | s' , eq₂ , eq₃
  with if-just _ eq₃
... | _ , s'-eq
  = ≤-trans
      (≤-reflexive (sym (cong length (init-state-memory src pre s₀ eq₀))))
      (exec-instrs-mono pre s₀ (IrSource.instructions src) s
        (subst (λ x → exec-instrs pre s₀ (IrSource.instructions src) ≡ just x) s'-eq eq₂))
