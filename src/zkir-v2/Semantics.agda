module zkir-v2.Semantics where

open import zkir-v2.Syntax

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool as Bool
open import Data.List    using (List; []; _∷_; _++_; length; drop; take; reverse)
open import Data.Maybe   using (Maybe; nothing; just; _>>=_; maybe)
open import Data.Product using (_×_; _,_)
open import Data.Nat     using (ℕ; zero; suc; _∸_; _≡ᵇ_)

------------------------------------------------------------------------
-- Postulated field and curve operations
------------------------------------------------------------------------

postulate
  -- Field constants
  0ᶠ 1ᶠ : Fr

  -- Field arithmetic
  _+ᶠ_ _*ᶠ_ : Fr → Fr → Fr
  -ᶠ_         : Fr → Fr

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
-- Utilities
------------------------------------------------------------------------

private
  from-bool : Bool → Fr
  from-bool false = 0ᶠ
  from-bool true  = 1ᶠ

  all-false : List Bool → Bool
  all-false []       = true
  all-false (b ∷ bs) = Bool.not b ∧ all-false bs

  _≡ᶠ-list?_ : List Fr → List Fr → Bool
  []       ≡ᶠ-list? []       = true
  (x ∷ xs) ≡ᶠ-list? (y ∷ ys) = x ≡ᶠ? y ∧ xs ≡ᶠ-list? ys
  _        ≡ᶠ-list? _        = false

  -- bits-lt as bs: true iff the natural number represented by as (LE) is < that
  -- of bs.  Assumes both lists have the same length.
  bits-lt : List Bool → List Bool → Bool
  bits-lt as bs = go (reverse as) (reverse bs)
    where
      go : List Bool → List Bool → Bool
      go []          _           = false
      go _           []          = false
      go (false ∷ _) (true ∷ _) = true
      go (true ∷ _)  (false ∷ _) = false
      go (_ ∷ as')   (_ ∷ bs')  = go as' bs'

  is-empty : {A : Set} → List A → Bool
  is-empty []      = true
  is-empty (_ ∷ _) = false

-- Convert Fr to Bool; nothing if not in {0, 1} (UB in the IR)
to-bool : Fr → Maybe Bool
to-bool x with x ≡ᶠ? 0ᶠ
... | true  = just false
... | false with x ≡ᶠ? 1ᶠ
...   | true  = just true
...   | false = nothing

mem-lookup : List Fr → Index → Maybe Fr
mem-lookup []       _       = nothing
mem-lookup (x ∷ _)  zero    = just x
mem-lookup (_ ∷ xs) (suc n) = mem-lookup xs n

mem-lookups : List Fr → List Index → Maybe (List Fr)
mem-lookups _   []       = just []
mem-lookups mem (i ∷ is) =
  mem-lookup mem i  >>= λ v  →
  mem-lookups mem is >>= λ vs →
  just (v ∷ vs)

-- True iff x has no bits set at positions ≥ n (i.e. x < 2^n)
fits-in : Fr → ℕ → Bool
fits-in x n = all-false (drop n (to-le-bits x))

------------------------------------------------------------------------
-- Proof preimage
-- Mirrors ProofPreimage in transient_crypto::proofs
------------------------------------------------------------------------

record ProofPreimage : Set where
  constructor mk-preimage
  field
    inputs                 : List Fr
    binding-input          : Fr
    comm-commitment        : Maybe (Fr × Fr)  -- (commitment, randomness)
    pub-transcript-inputs  : List Fr
    pub-transcript-outputs : List Fr
    priv-transcript        : List Fr

------------------------------------------------------------------------
-- Execution state
------------------------------------------------------------------------

record ExecState : Set where
  constructor mk-state
  field
    memory      : List Fr
    pis         : List Fr         -- public inputs: binding-input first, then
                                  --   DeclarePubInput values
    pi-skips    : List (Maybe ℕ)  -- nothing = active group, just n = skipped
    pub-in-idx  : ℕ               -- count of DeclarePubInput processed
    pub-out-rem : List Fr         -- remaining pub-transcript-outputs
    priv-rem    : List Fr         -- remaining priv-transcript
    outputs     : List Fr         -- values written by Output instructions

------------------------------------------------------------------------
-- Initial state from preimage
-- Fails if do-communications-commitment is set but no commitment is provided.
------------------------------------------------------------------------

init-state : IrSource → ProofPreimage → Maybe ExecState
init-state src pre
  with IrSource.do-communications-commitment src
     | ProofPreimage.comm-commitment pre
... | false | _            = just (mk-state
      (ProofPreimage.inputs pre)
      (ProofPreimage.binding-input pre ∷ [])
      [] 0
      (ProofPreimage.pub-transcript-outputs pre)
      (ProofPreimage.priv-transcript pre)
      [])
... | true  | just (c , _) = just (mk-state
      (ProofPreimage.inputs pre)
      (ProofPreimage.binding-input pre ∷ c ∷ [])
      [] 0
      (ProofPreimage.pub-transcript-outputs pre)
      (ProofPreimage.priv-transcript pre)
      [])
... | true  | nothing      = nothing

------------------------------------------------------------------------
-- State helpers
------------------------------------------------------------------------

push-mem : ExecState → Fr → ExecState
push-mem s v = record s { memory = ExecState.memory s ++ (v ∷ []) }

push-mem2 : ExecState → Fr → Fr → ExecState
push-mem2 s v₁ v₂ = record s { memory = ExecState.memory s ++ (v₁ ∷ v₂ ∷ []) }

consume-pub-out : ExecState → Maybe (Fr × ExecState)
consume-pub-out s with ExecState.pub-out-rem s
... | []       = nothing
... | v ∷ rest = just (v , record s { pub-out-rem = rest })

consume-priv : ExecState → Maybe (Fr × ExecState)
consume-priv s with ExecState.priv-rem s
... | []       = nothing
... | v ∷ rest = just (v , record s { priv-rem = rest })

private
  push-pi : ExecState → Fr → ExecState
  push-pi s v = record s
    { pis        = ExecState.pis s ++ (v ∷ [])
    ; pub-in-idx = suc (ExecState.pub-in-idx s) }

  push-skip : ExecState → Maybe ℕ → ExecState
  push-skip s sk = record s { pi-skips = ExecState.pi-skips s ++ (sk ∷ []) }

  push-output : ExecState → Fr → ExecState
  push-output s v = record s { outputs = ExecState.outputs s ++ (v ∷ []) }

------------------------------------------------------------------------
-- Guard evaluation
-- nothing  → always active (true)
-- just idx → evaluate memory[idx] as a boolean
------------------------------------------------------------------------

eval-guard : List Fr → Maybe Index → Maybe Bool
eval-guard _   nothing    = just true
eval-guard mem (just idx) = mem-lookup mem idx >>= to-bool

------------------------------------------------------------------------
-- PiSkip
--
-- Active guard (true): validate the last `count` declared pub inputs
--   match the corresponding entries in the pub-transcript-inputs, then
--   record nothing (group is live).
-- Inactive guard (false): decrement pub-in-idx by count and record
--   just count (group is skipped).
------------------------------------------------------------------------

private
  exec-pi-skip : ProofPreimage → ExecState → Maybe Index → ℕ → Maybe ExecState
  exec-pi-skip pre s guard count =
    eval-guard (ExecState.memory s) guard >>= λ active →
    if active then validate else skip
    where
      validate : Maybe ExecState
      validate =
        let
          pis      = ExecState.pis s
          recent   = drop (length pis ∸ count) pis
          start    = ExecState.pub-in-idx s ∸ count
          expected = take count (drop start (ProofPreimage.pub-transcript-inputs pre))
        in
        if recent ≡ᶠ-list? expected
          then just (push-skip s nothing)
          else nothing

      skip : Maybe ExecState
      skip = just (push-skip
        (record s { pub-in-idx = ExecState.pub-in-idx s ∸ count })
        (just count))

------------------------------------------------------------------------
-- Single-instruction execution
-- Returns nothing on out-of-bounds access, UB, or constraint failure.
------------------------------------------------------------------------

exec-instr : ProofPreimage → ExecState → Instruction → Maybe ExecState

exec-instr _ s (assert cond) =
  mem-lookup (ExecState.memory s) cond >>= to-bool >>= λ b →
  if b then just s else nothing

exec-instr _ s (cond-select bit a b) =
  let mem = ExecState.memory s in
  mem-lookup mem bit >>= to-bool >>= λ bv →
  mem-lookup mem a   >>= λ av   →
  mem-lookup mem b   >>= λ bv'  →
  just (push-mem s (if bv then av else bv'))

exec-instr _ s (constrain-bits var bits) =
  mem-lookup (ExecState.memory s) var >>= λ v →
  if fits-in v bits then just s else nothing

exec-instr _ s (constrain-eq a b) =
  let mem = ExecState.memory s in
  mem-lookup mem a >>= λ av →
  mem-lookup mem b >>= λ bv →
  if av ≡ᶠ? bv then just s else nothing

exec-instr _ s (constrain-to-boolean var) =
  mem-lookup (ExecState.memory s) var >>= to-bool >>= λ _ →
  just s

exec-instr _ s (copy var) =
  mem-lookup (ExecState.memory s) var >>= λ v →
  just (push-mem s v)

exec-instr _ s (declare-pub-input var) =
  mem-lookup (ExecState.memory s) var >>= λ v →
  just (push-pi s v)

exec-instr pre s (pi-skip guard count) =
  exec-pi-skip pre s guard count

exec-instr _ s (ec-add a_x a_y b_x b_y) =
  let mem = ExecState.memory s in
  mem-lookup mem a_x >>= λ ax →
  mem-lookup mem a_y >>= λ ay →
  mem-lookup mem b_x >>= λ bx →
  mem-lookup mem b_y >>= λ by →
  ec-add-pts ax ay bx by >>= λ { (cx , cy) →
  just (push-mem2 s cx cy) }

exec-instr _ s (ec-mul a_x a_y scalar) =
  let mem = ExecState.memory s in
  mem-lookup mem a_x    >>= λ ax →
  mem-lookup mem a_y    >>= λ ay →
  mem-lookup mem scalar >>= λ sc →
  ec-mul-pt ax ay sc >>= λ { (cx , cy) →
  just (push-mem2 s cx cy) }

exec-instr _ s (ec-mul-generator scalar) =
  mem-lookup (ExecState.memory s) scalar >>= λ sc →
  let (cx , cy) = ec-mul-gen sc in
  just (push-mem2 s cx cy)

exec-instr _ s (hash-to-curve inputs) =
  mem-lookups (ExecState.memory s) inputs >>= λ vs →
  let (cx , cy) = hash-to-curve-fn vs in
  just (push-mem2 s cx cy)

exec-instr _ s (load-imm imm) =
  just (push-mem s imm)

exec-instr _ s (div-mod-power-of-two var bits) =
  mem-lookup (ExecState.memory s) var >>= λ v →
  let
    all-bits = to-le-bits v
    divisor  = from-le-bits (drop bits all-bits)
    modulus  = from-le-bits (take bits all-bits)
  in
  just (push-mem (push-mem s divisor) modulus)

-- NB: the comment in Syntax.agda says "1 output" but persistent-hash produces
-- 2 field elements, consistent with zkir-v3.Syntax and the Rust VM.
exec-instr _ s (persistent-hash alignment inputs) =
  mem-lookups (ExecState.memory s) inputs >>= λ vs →
  let (h₁ , h₂) = persistent-hash-fn alignment vs in
  just (push-mem2 s h₁ h₂)

exec-instr _ s (reconstitute-field divisor modulus bits) =
  let mem = ExecState.memory s in
  mem-lookup mem divisor >>= λ dv →
  mem-lookup mem modulus >>= λ mv →
  let
    mv-bits  = take bits             (to-le-bits mv)
    dv-bits  = take (FR-BITS ∸ bits) (to-le-bits dv)
    all-bits = mv-bits ++ dv-bits
  in
  if fits-in mv bits ∧ fits-in dv (FR-BITS ∸ bits) ∧ bits-in-field all-bits
    then just (push-mem s (from-le-bits all-bits))
    else nothing

exec-instr _ s (output var) =
  mem-lookup (ExecState.memory s) var >>= λ v →
  just (push-output s v)

exec-instr _ s (transient-hash inputs) =
  mem-lookups (ExecState.memory s) inputs >>= λ vs →
  just (push-mem s (transient-hash-fn vs))

exec-instr _ s (test-eq a b) =
  let mem = ExecState.memory s in
  mem-lookup mem a >>= λ av →
  mem-lookup mem b >>= λ bv →
  just (push-mem s (from-bool (av ≡ᶠ? bv)))

exec-instr _ s (add a b) =
  let mem = ExecState.memory s in
  mem-lookup mem a >>= λ av →
  mem-lookup mem b >>= λ bv →
  just (push-mem s (av +ᶠ bv))

exec-instr _ s (mul a b) =
  let mem = ExecState.memory s in
  mem-lookup mem a >>= λ av →
  mem-lookup mem b >>= λ bv →
  just (push-mem s (av *ᶠ bv))

exec-instr _ s (neg a) =
  mem-lookup (ExecState.memory s) a >>= λ av →
  just (push-mem s (-ᶠ av))

exec-instr _ s (not a) =
  mem-lookup (ExecState.memory s) a >>= to-bool >>= λ b →
  just (push-mem s (from-bool (Bool.not b)))

exec-instr _ s (less-than a b bits) =
  let mem = ExecState.memory s in
  mem-lookup mem a >>= λ av →
  mem-lookup mem b >>= λ bv →
  if fits-in av bits ∧ fits-in bv bits
    then just (push-mem s (from-bool
           (bits-lt (take bits (to-le-bits av))
                    (take bits (to-le-bits bv)))))
    else nothing

exec-instr pre s (public-input guard) =
  eval-guard (ExecState.memory s) guard >>= λ active →
  if Bool.not active
    then just (push-mem s 0ᶠ)
    else consume-pub-out s >>= λ { (v , s') → just (push-mem s' v) }

exec-instr pre s (private-input guard) =
  eval-guard (ExecState.memory s) guard >>= λ active →
  if Bool.not active
    then just (push-mem s 0ᶠ)
    else consume-priv s >>= λ { (v , s') → just (push-mem s' v) }

------------------------------------------------------------------------
-- Circuit execution: fold exec-instr over the instruction list
------------------------------------------------------------------------

exec-instrs : ProofPreimage → ExecState → List Instruction → Maybe ExecState
exec-instrs _   s []       = just s
exec-instrs pre s (i ∷ is) =
  exec-instr pre s i >>= λ s' →
  exec-instrs pre s' is

------------------------------------------------------------------------
-- Post-execution validation
------------------------------------------------------------------------

-- All three transcripts must be fully consumed.
transcripts-consumed : ProofPreimage → ExecState → Bool
transcripts-consumed pre s =
  (length (ProofPreimage.pub-transcript-inputs pre) ≡ᵇ ExecState.pub-in-idx s)
  ∧ is-empty (ExecState.pub-out-rem s)
  ∧ is-empty (ExecState.priv-rem s)

-- If do-communications-commitment is set, verify the commitment.
comm-ok : IrSource → ProofPreimage → ExecState → Bool
comm-ok src pre s
  with IrSource.do-communications-commitment src
     | ProofPreimage.comm-commitment pre
... | false | _            = true
... | true  | nothing      = false
... | true  | just (c , r) =
  c ≡ᶠ? transient-commit (ProofPreimage.inputs pre ++ ExecState.outputs s) r

------------------------------------------------------------------------
-- Top-level: run the circuit and validate
------------------------------------------------------------------------

exec : IrSource → ProofPreimage → Maybe ExecState
exec src pre =
  init-state src pre                           >>= λ s  →
  exec-instrs pre s (IrSource.instructions src) >>= λ s' →
  if transcripts-consumed pre s' ∧ comm-ok src pre s'
    then just s'
    else nothing
