{-# OPTIONS --safe #-}
open import zkir-v2.Assumptions

module zkir-v2.CircuitProof (⋯ : _) (open Assumptions ⋯) where

------------------------------------------------------------------------
-- Circuit-faithfulness bridging (Phase 4 — COMPLETE).
--
-- This module carries the program-level induction that connects the
-- operational relation `R src pre s` to the in-circuit satisfaction
-- relation `satisfies (circuit src) (witness-of s pre)` — discharging
-- the former `circuit-faithful` postulate in `Properties.agda` (spec
-- §6.2, P5).  P5 is now fully mechanised; `circuit-faithful` is exported
-- as a logical equivalence (`_⇔_`) and re-exported from `Properties`.
--
-- Phase 4 decomposition (all DONE):
--
--   • 4b   Forward direction: R-instrs ⇒ satisfies-clauses.
--   • 4c   Soundness of O2 / O3 over R-instrs traces.
--   • 4d   Backward direction: satisfies-clauses ⇒ R-instrs (D1/D2),
--          and the top-level backward `circuit-faithful-bwd` (D3),
--          quantified over the §5.4 `preprocess-shaped` states with the
--          §3.4 WF1 arity hypothesis and a `transcripts-consumed` shape
--          conjunct (both genuinely required — see notes at D3).
--   • 4e   The bundled `_⇔_` `circuit-faithful`, re-exported from
--          `Properties`.
--
-- IMPORTANT.  NO axioms are introduced here.  There are no `postulate`
-- blocks in this module; every lemma is discharged by an inductive or
-- equational proof.  (The only postulates P5 rests on are the pre-
-- existing field/crypto axioms in `CircuitFaithfulness.agda`.)
------------------------------------------------------------------------

open import zkir-v2.Syntax ⋯
open import zkir-v2.Semantics ⋯
open import zkir-v2.Circuit ⋯
open import zkir-v2.CircuitFaithfulness ⋯
open import zkir-v2.Obligations ⋯
  using ( producer-safe
        ; wire-disc; wire-check; wire-step; wire-scan
        ; Wire-Trace; wire-done; wire-cons
        ; Δmem; _<ᵇ_; _≤ᵇ_; guard-ok?; all-lt?
        ; IndexSet; PartialMap; lookupᵐ
        ; O2-check; O3-check; mem?
        ; O2-step; O3-step
        ; O2-Trace; o2-done; o2-step
        ; O3-Trace; o3-done; o3-step
        ; O2-Runs; O3-Runs
        ; FR-bits-bound
        )
open import zkir-v2.ObligationsSoundness ⋯
  using ( producer-safe-wire-disc
        ; producer-safe-O2; producer-safe-O3
        ; O2-bool→Runs; O3-bool→Runs
        ; o2-inv-init; o3-inv-init
        ; O2-Inv; O3-Inv
        ; o2-known-is-bit; o3-known-fits
        ; o2-preserve; o3-preserve
        )

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
import Data.Bool as Bool
import Data.Bool.Properties
open import Data.List    using (List; []; _∷_; _++_; length; map; take; drop)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe   using (Maybe; nothing; just; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (ℕ; suc; zero; _+_; _∸_; _≡ᵇ_)
import Data.Nat
open import Data.Nat.Properties using (+-suc; +-identityʳ)
import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥; ⊥-elim)
open import Function.Bundles using (_⇔_; mk⇔)
import Function.Bundles
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)

------------------------------------------------------------------------
-- Section A.  Witness-of:  Preprocessed × ProofPreimage  →  Witness.
--
-- The witness assignment produced by an operational execution.  Three
-- fields:
--
--   • mem        : Preprocessed.memory s    (all allocated wire values)
--   • pis        : Preprocessed.pis    s    (verifier-supplied entries)
--   • comm-rand  : the randomness portion of the optional commitment.
--
-- Note: `witness-of` does NOT depend on the `IrSource`.  The
-- *circuit*'s `has-comm` flag determines the expected shape of
-- `comm-rand`, and the `Maybe-shape` predicate in `satisfies` enforces
-- the match.  Producer-safety (+ the operational `init-state`
-- precondition) is what guarantees the shapes line up at the top level.
------------------------------------------------------------------------

-- The randomness component of a preimage's optional commitment.
comm-rand-of : ProofPreimage → Maybe Fr
comm-rand-of pre with ProofPreimage.comm-commitment pre
... | just (_ , r) = just r
... | nothing      = nothing

witness-of : Preprocessed → ProofPreimage → Witness
witness-of s pre = mk-witness
  (Preprocessed.memory s)
  (Preprocessed.pis    s)
  (comm-rand-of pre)

------------------------------------------------------------------------
-- Section B.  Synth-state invariants.
--
-- During the induction along an `R-instrs pre s₀ is s_end` trace, we
-- maintain a *parallel* synth-state evolved by `circuit-instrs hc`.
-- The forward lemma asserts that the synth-state's accumulated clauses
-- are all satisfied by the assignment derived from the *post*-trace
-- preprocessed state.
--
-- Two structural invariants get threaded:
--
--   I-mem  :  SynthState.nr-wires   ≡  length (Preprocessed.memory)
--   I-pi   :  preamble-pi-count hc + SynthState.nr-declared-pi
--             ≡  length (Preprocessed.pis)
--
-- I-mem says every wire allocated by synthesis corresponds to a memory
-- cell in the operational state; I-pi is the consistency precondition
-- documented in `state-dependent-clauses.md` — needed so that
-- `clause-pi-from-wire` references a valid PI entry.
--
-- Phase 4b's job is to discharge these inductively from the per-
-- instruction faithfulness lemmas in `CircuitFaithfulness.agda`.
------------------------------------------------------------------------

-- Memory-length invariant.
mem-inv : Preprocessed → SynthState → Set
mem-inv s st = SynthState.nr-wires st ≡ length (Preprocessed.memory s)

-- PI-length invariant.  Parameterized on `has-comm`.
pi-inv : Bool → Preprocessed → SynthState → Set
pi-inv hc s st =
  length (Preprocessed.pis s) ≡ preamble-pi-count hc + SynthState.nr-declared-pi st

------------------------------------------------------------------------
-- Section B.5.  Memory/PI monotonicity along R-instrs.
--
-- Auxiliary lemmas used by both the forward dispatcher and the
-- top-level comm-commitment gluing.
------------------------------------------------------------------------

private

  -- Memory lookup is preserved by appending a suffix.  Mirrors
  -- `lookup-extends` from `CircuitFaithfulness.agda` (private there).
  lookup-extends : ∀ (mem suffix : List Fr) i {v}
    → mem-lookup mem i ≡ just v
    → mem-lookup (mem ++ suffix) i ≡ just v
  lookup-extends []       _ _       ()
  lookup-extends (x ∷ xs) _ zero    eq = eq
  lookup-extends (x ∷ xs) s (suc i) eq = lookup-extends xs s i eq

  -- `mem-lookup mem n ≡ just v` when `mem ! n = v` and `n < length mem`.
  -- Specialised form for the initial-state input wires.
  lookup-at : ∀ (mem : List Fr) (n : ℕ) {v}
    → mem-lookup mem n ≡ just v
    → mem-lookup mem n ≡ just v
  lookup-at _ _ eq = eq

  -- Multi-index analogue of `lookup-extends`.
  mem-lookups-extends : ∀ (mem suffix : List Fr) (is : List Index) {vs}
    → mem-lookups mem is ≡ just vs
    → mem-lookups (mem ++ suffix) is ≡ just vs
  mem-lookups-extends mem suffix []       refl = refl
  mem-lookups-extends mem suffix (i ∷ is) eq   =
    aux (mem-lookup mem i)      refl
        (mem-lookups mem is)    refl
        eq
    where
      aux : ∀ (m : Maybe Fr) → mem-lookup mem i ≡ m
          → (ms : Maybe (List Fr)) → mem-lookups mem is ≡ ms
          → ∀ {vs} → (m >>= λ v → ms >>= λ vs' → just (v ∷ vs')) ≡ just vs
          → mem-lookups (mem ++ suffix) (i ∷ is) ≡ just vs
      aux nothing   _    _          _    ()
      aux (just _)  _    nothing    _    ()
      aux (just v)  m-eq (just vs') ms-eq refl
        rewrite lookup-extends mem suffix i {v} m-eq
              | mem-lookups-extends mem suffix is {vs'} ms-eq
        = refl

  -- pi-lookup analogue of `lookup-extends`.
  pi-lookup-extends : ∀ (pis suffix : List Fr) i {v}
    → pi-lookup pis i ≡ just v
    → pi-lookup (pis ++ suffix) i ≡ just v
  pi-lookup-extends []       _ _       ()
  pi-lookup-extends (x ∷ xs) _ zero    eq = eq
  pi-lookup-extends (x ∷ xs) s (suc i) eq = pi-lookup-extends xs s i eq

  -- One R-instr step's memory only grows: post-mem = pre-mem ++ suffix
  -- for some suffix.  This is a single existential lemma; we package
  -- the suffix as a List Fr.
  mem-extends-R-instr : ∀ {pre s i s'}
    → R-instr pre s i s'
    → Σ-syntax (List Fr) λ suf →
        Preprocessed.memory s' ≡ Preprocessed.memory s ++ suf
  mem-extends-R-instr (r-assert _)                       = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-cond-select {av = av} {bv = bv} _ _ _) =
    _ ∷ [] , refl
  mem-extends-R-instr (r-constrain-bits _ _)             = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-constrain-eq _ _ _)             = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-constrain-to-boolean _)         = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-copy {v = v} _)                 = v ∷ [] , refl
  mem-extends-R-instr (r-declare-pub-input _)            = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-pi-skip-active _ _)             = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-pi-skip-inactive _)             = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-ec-add {cx = cx} {cy = cy} _ _ _ _ _) =
    cx ∷ cy ∷ [] , refl
  mem-extends-R-instr (r-ec-mul {cx = cx} {cy = cy} _ _ _ _) =
    cx ∷ cy ∷ [] , refl
  mem-extends-R-instr (r-ec-mul-generator {cx = cx} {cy = cy} _ _) =
    cx ∷ cy ∷ [] , refl
  mem-extends-R-instr (r-hash-to-curve {cx = cx} {cy = cy} _ _) =
    cx ∷ cy ∷ [] , refl
  mem-extends-R-instr (r-load-imm {imm = imm})          = imm ∷ [] , refl
  mem-extends-R-instr {s = s} (r-div-mod-power-of-two {bits = bits} {v = vv} _) =
    let mem = Preprocessed.memory s
        divisor = from-le-bits (drop bits (to-le-bits vv))
        modulus = from-le-bits (take bits (to-le-bits vv))
    in divisor ∷ modulus ∷ [] , ++-assoc mem (divisor ∷ []) (modulus ∷ [])
  mem-extends-R-instr (r-reconstitute-field _ _ _)       = _ ∷ [] , refl
  mem-extends-R-instr (r-output _)                       = [] , sym (++-identityʳ _)
  mem-extends-R-instr (r-transient-hash {vs = vs} _)     = transient-hash-fn vs ∷ [] , refl
  mem-extends-R-instr (r-persistent-hash {h₁ = h₁} {h₂ = h₂} _ _) =
    h₁ ∷ h₂ ∷ [] , refl
  mem-extends-R-instr (r-test-eq _ _)                    = _ ∷ [] , refl
  mem-extends-R-instr (r-add _ _)                        = _ ∷ [] , refl
  mem-extends-R-instr (r-mul _ _)                        = _ ∷ [] , refl
  mem-extends-R-instr (r-neg _)                          = _ ∷ [] , refl
  mem-extends-R-instr (r-not _)                          = _ ∷ [] , refl
  mem-extends-R-instr (r-less-than _ _ _)                = _ ∷ [] , refl
  mem-extends-R-instr (r-public-input-inactive _)        = 0ᶠ ∷ [] , refl
  mem-extends-R-instr {s = s} (r-public-input-active {v = v} {s₁ = s₁} _ cp) =
    v ∷ [] , cong (_++ (v ∷ [])) (sym (consume-pub-out-mem-aux s cp))
    where
      consume-pub-out-mem-aux : ∀ s {v s'}
        → consume-pub-out s ≡ just (v , s')
        → Preprocessed.memory s ≡ Preprocessed.memory s'
      consume-pub-out-mem-aux s eq with Preprocessed.pub-out-rem s | eq
      ... | []    | ()
      ... | _ ∷ _ | p = cong Preprocessed.memory (cong proj₂ (just-injective p))
  mem-extends-R-instr (r-private-input-inactive _)       = 0ᶠ ∷ [] , refl
  mem-extends-R-instr {s = s} (r-private-input-active {v = v} {s₁ = s₁} _ cp) =
    v ∷ [] , cong (_++ (v ∷ [])) (sym (consume-priv-mem-aux s cp))
    where
      consume-priv-mem-aux : ∀ s {v s'}
        → consume-priv s ≡ just (v , s')
        → Preprocessed.memory s ≡ Preprocessed.memory s'
      consume-priv-mem-aux s eq with Preprocessed.priv-rem s | eq
      ... | []    | ()
      ... | _ ∷ _ | p = cong Preprocessed.memory (cong proj₂ (just-injective p))

  -- Holds is preserved by extending the witness's memory with a suffix.
  -- The pis and comm-rand fields are unchanged.  By case analysis on the
  -- clause: every clause uses `mem-lookup` (or `mem-lookups`) on the
  -- witness's memory, and these are monotone.
  holds-mem-extends : ∀ {mem suffix pis rand} (cl : Clause)
    → holds (mk-witness mem pis rand) cl
    → holds (mk-witness (mem ++ suffix) pis rand) cl
  holds-mem-extends {mem} {suffix} (clause-assert-non-zero c)
    (v , lv , v≢0) =
    v , lookup-extends mem suffix c lv , v≢0
  holds-mem-extends {mem} {suffix} (clause-cond-select out b a c)
    (bv , av , cv , ov , lb , la , lc , lout , bit , eq) =
    bv , av , cv , ov
    , lookup-extends mem suffix b lb
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix c lc
    , lookup-extends mem suffix out lout
    , bit , eq
  holds-mem-extends {mem} {suffix} (clause-range-bits v bits)
    (vv , lv , fits) =
    vv , lookup-extends mem suffix v lv , fits
  holds-mem-extends {mem} {suffix} (clause-eq a b)
    (av , bv , la , lb , eq) =
    av , bv , lookup-extends mem suffix a la , lookup-extends mem suffix b lb , eq
  holds-mem-extends {mem} {suffix} (clause-bool v)
    (vv , lv , bit) =
    vv , lookup-extends mem suffix v lv , bit
  holds-mem-extends {mem} {suffix} (clause-copy out v)
    (vv , ov , lv , lout , eq) =
    vv , ov , lookup-extends mem suffix v lv , lookup-extends mem suffix out lout , eq
  holds-mem-extends {mem} {suffix} (clause-ec-add c-x c-y a-x a-y b-x b-y)
    (ax , ay , bx , by , cx , cy , lax , lay , lbx , lby , lcx , lcy , add-eq) =
    ax , ay , bx , by , cx , cy
    , lookup-extends mem suffix a-x lax
    , lookup-extends mem suffix a-y lay
    , lookup-extends mem suffix b-x lbx
    , lookup-extends mem suffix b-y lby
    , lookup-extends mem suffix c-x lcx
    , lookup-extends mem suffix c-y lcy
    , add-eq
  holds-mem-extends {mem} {suffix} (clause-ec-mul c-x c-y a-x a-y scalar)
    (ax , ay , sc , cx , cy , lax , lay , lsc , lcx , lcy , mul-eq) =
    ax , ay , sc , cx , cy
    , lookup-extends mem suffix a-x lax
    , lookup-extends mem suffix a-y lay
    , lookup-extends mem suffix scalar lsc
    , lookup-extends mem suffix c-x lcx
    , lookup-extends mem suffix c-y lcy
    , mul-eq
  holds-mem-extends {mem} {suffix} (clause-ec-mul-generator c-x c-y scalar)
    (sc , cx , cy , lsc , lcx , lcy , gen-eq) =
    sc , cx , cy
    , lookup-extends mem suffix scalar lsc
    , lookup-extends mem suffix c-x lcx
    , lookup-extends mem suffix c-y lcy
    , gen-eq
  holds-mem-extends {mem} {suffix} (clause-hash-to-curve c-x c-y inputs)
    (vs , cx , cy , lvs , lcx , lcy , hash-eq) =
    vs , cx , cy
    , mem-lookups-extends mem suffix inputs lvs
    , lookup-extends mem suffix c-x lcx
    , lookup-extends mem suffix c-y lcy
    , hash-eq
  holds-mem-extends {mem} {suffix} (clause-load-imm out imm)
    (ov , lout , eq) =
    ov , lookup-extends mem suffix out lout , eq
  holds-mem-extends {mem} {suffix} (clause-div-mod q r v bits)
    (qv , rv , vv , lq , lr , lv , fr , fq , eq) =
    qv , rv , vv
    , lookup-extends mem suffix q lq
    , lookup-extends mem suffix r lr
    , lookup-extends mem suffix v lv
    , fr , fq , eq
  holds-mem-extends {mem} {suffix} (clause-reconstitute out d m bits)
    (dv , mv , ov , ld , lm , lout , fd , fm , eq) =
    dv , mv , ov
    , lookup-extends mem suffix d ld
    , lookup-extends mem suffix m lm
    , lookup-extends mem suffix out lout
    , fd , fm , eq
  holds-mem-extends {mem} {suffix} (clause-transient-hash out inputs)
    (vs , ov , lvs , lout , eq) =
    vs , ov
    , mem-lookups-extends mem suffix inputs lvs
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-persistent-hash h₁ h₂ alignment inputs)
    (vs , v1 , v2 , lvs , lh₁ , lh₂ , hash-eq) =
    vs , v1 , v2
    , mem-lookups-extends mem suffix inputs lvs
    , lookup-extends mem suffix h₁ lh₁
    , lookup-extends mem suffix h₂ lh₂
    , hash-eq
  holds-mem-extends {mem} {suffix} (clause-test-eq out a b)
    (av , bv , ov , la , lb , lout , eq) =
    av , bv , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix b lb
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-add out a b)
    (av , bv , ov , la , lb , lout , eq) =
    av , bv , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix b lb
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-mul out a b)
    (av , bv , ov , la , lb , lout , eq) =
    av , bv , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix b lb
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-neg out a)
    (av , ov , la , lout , eq) =
    av , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-not out a)
    (av , ov , la , lout , eq) =
    av , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix out lout
    , eq
  holds-mem-extends {mem} {suffix} (clause-less-than out a b bits)
    (av , bv , ov , la , lb , lout , fa , fb , eq) =
    av , bv , ov
    , lookup-extends mem suffix a la
    , lookup-extends mem suffix b lb
    , lookup-extends mem suffix out lout
    , fa , fb , eq
  holds-mem-extends {mem} {suffix} (clause-guard-disj out i)
    (ov , iv , lout , li , disj) =
    ov , iv
    , lookup-extends mem suffix out lout
    , lookup-extends mem suffix i li
    , disj
  holds-mem-extends {mem} {suffix} (clause-pi-from-wire entry wire)
    (wv , pv , lw , lpi , eq) =
    wv , pv , lookup-extends mem suffix wire lw , lpi , eq
  holds-mem-extends {mem} {suffix} (clause-comm-commitment inputs outputs)
    (ivs , ovs , rv , pv , livs , lovs , crv , lpv , eq) =
    ivs , ovs , rv , pv
    , mem-lookups-extends mem suffix inputs livs
    , mem-lookups-extends mem suffix outputs lovs
    , crv , lpv , eq

  -- Satisfaction of a list of clauses is preserved under mem extension.
  satisfies-clauses-mem-extends : ∀ {mem suffix pis rand} (cls : List Clause)
    → satisfies-clauses cls (mk-witness mem pis rand)
    → satisfies-clauses cls (mk-witness (mem ++ suffix) pis rand)
  satisfies-clauses-mem-extends []         _              = tt
  satisfies-clauses-mem-extends (cl ∷ cls) (hold , sats)  =
    holds-mem-extends cl hold , satisfies-clauses-mem-extends cls sats

  -- Holds is preserved by extending the witness's pis with a suffix.
  -- Only `clause-pi-from-wire` and `clause-comm-commitment` mention pis.
  holds-pis-extends : ∀ {mem pis suffix rand} (cl : Clause)
    → holds (mk-witness mem pis rand) cl
    → holds (mk-witness mem (pis ++ suffix) rand) cl
  holds-pis-extends (clause-assert-non-zero c) h = h
  holds-pis-extends (clause-cond-select _ _ _ _) h = h
  holds-pis-extends (clause-range-bits _ _) h = h
  holds-pis-extends (clause-eq _ _) h = h
  holds-pis-extends (clause-bool _) h = h
  holds-pis-extends (clause-copy _ _) h = h
  holds-pis-extends (clause-ec-add _ _ _ _ _ _) h = h
  holds-pis-extends (clause-ec-mul _ _ _ _ _) h = h
  holds-pis-extends (clause-ec-mul-generator _ _ _) h = h
  holds-pis-extends (clause-hash-to-curve _ _ _) h = h
  holds-pis-extends (clause-load-imm _ _) h = h
  holds-pis-extends (clause-div-mod _ _ _ _) h = h
  holds-pis-extends (clause-reconstitute _ _ _ _) h = h
  holds-pis-extends (clause-transient-hash _ _) h = h
  holds-pis-extends (clause-persistent-hash _ _ _ _) h = h
  holds-pis-extends (clause-test-eq _ _ _) h = h
  holds-pis-extends (clause-add _ _ _) h = h
  holds-pis-extends (clause-mul _ _ _) h = h
  holds-pis-extends (clause-neg _ _) h = h
  holds-pis-extends (clause-not _ _) h = h
  holds-pis-extends (clause-less-than _ _ _ _) h = h
  holds-pis-extends (clause-guard-disj _ _) h = h
  holds-pis-extends {pis = pis} {suffix = suffix} (clause-pi-from-wire entry wire)
    (wv , pv , lw , lpi , eq) =
    wv , pv , lw , pi-lookup-extends pis suffix entry lpi , eq
  holds-pis-extends {pis = pis} {suffix = suffix} (clause-comm-commitment inputs outputs)
    (ivs , ovs , rv , pv , livs , lovs , crv , lpv , eq) =
    ivs , ovs , rv , pv
    , livs , lovs , crv
    , pi-lookup-extends pis suffix 1 lpv
    , eq

  satisfies-clauses-pis-extends : ∀ {mem pis suffix rand} (cls : List Clause)
    → satisfies-clauses cls (mk-witness mem pis rand)
    → satisfies-clauses cls (mk-witness mem (pis ++ suffix) rand)
  satisfies-clauses-pis-extends []         _              = tt
  satisfies-clauses-pis-extends (cl ∷ cls) (hold , sats)  =
    holds-pis-extends cl hold , satisfies-clauses-pis-extends cls sats

  ------------------------------------------------------------------------
  -- Mem / pis SHRINK direction.
  --
  -- `holds-mem-shrink`/`-pis-shrink` are the duals of `-extends`.  Given
  -- a clause whose referenced indices all fit within `length mem`
  -- (resp. `length pis`), and a `holds` at the extended witness, derive
  -- `holds` at the pre-extension witness.  Used by D2 (the per-list
  -- backward dispatcher) to peel off the satisfies-clauses for the
  -- head instruction from the satisfies-clauses over the *full*
  -- accumulated extension.
  ------------------------------------------------------------------------

  -- Boolean helpers (local copies — the canonical versions also live in
  -- a later private block; replicated here to keep this block self-
  -- contained).
  <ᵇ-to-≤ : ∀ m n → (m <ᵇ n) ≡ true → suc m Data.Nat.≤ n
  <ᵇ-to-≤ m n eq with suc m Data.Nat.≤? n
  ... | yes p = p
  ... | no  _ with eq
  ...           | ()

  ∧-≡-true-split : ∀ {x y} → (x ∧ y) ≡ true → x ≡ true × y ≡ true
  ∧-≡-true-split {true}  {true}  refl = refl , refl
  ∧-≡-true-split {true}  {false} ()
  ∧-≡-true-split {false} {_}     ()

  -- Boolean predicate: every index referenced by `cl` is strictly less
  -- than `n`.  For clauses with PI references (pi-from-wire,
  -- comm-commitment), this is only about memory indices.
  clause-mem-fits : Clause → ℕ → Bool
  clause-mem-fits (clause-assert-non-zero c)               n = c <ᵇ n
  clause-mem-fits (clause-cond-select out b a c)           n =
    (out <ᵇ n) ∧ (b <ᵇ n) ∧ (a <ᵇ n) ∧ (c <ᵇ n)
  clause-mem-fits (clause-range-bits v _)                  n = v <ᵇ n
  clause-mem-fits (clause-eq a b)                          n = (a <ᵇ n) ∧ (b <ᵇ n)
  clause-mem-fits (clause-bool v)                          n = v <ᵇ n
  clause-mem-fits (clause-copy out v)                      n = (out <ᵇ n) ∧ (v <ᵇ n)
  clause-mem-fits (clause-ec-add cx cy ax ay bx by)        n =
    (cx <ᵇ n) ∧ (cy <ᵇ n) ∧ (ax <ᵇ n) ∧ (ay <ᵇ n) ∧ (bx <ᵇ n) ∧ (by <ᵇ n)
  clause-mem-fits (clause-ec-mul cx cy ax ay s)            n =
    (cx <ᵇ n) ∧ (cy <ᵇ n) ∧ (ax <ᵇ n) ∧ (ay <ᵇ n) ∧ (s <ᵇ n)
  clause-mem-fits (clause-ec-mul-generator cx cy s)        n =
    (cx <ᵇ n) ∧ (cy <ᵇ n) ∧ (s <ᵇ n)
  clause-mem-fits (clause-hash-to-curve cx cy inputs)      n =
    (cx <ᵇ n) ∧ (cy <ᵇ n) ∧ all-lt? inputs n
  clause-mem-fits (clause-load-imm out _)                  n = out <ᵇ n
  clause-mem-fits (clause-div-mod q r v _)                 n =
    (q <ᵇ n) ∧ (r <ᵇ n) ∧ (v <ᵇ n)
  clause-mem-fits (clause-reconstitute out d m _)          n =
    (out <ᵇ n) ∧ (d <ᵇ n) ∧ (m <ᵇ n)
  clause-mem-fits (clause-transient-hash out inputs)       n =
    (out <ᵇ n) ∧ all-lt? inputs n
  clause-mem-fits (clause-persistent-hash h₁ h₂ _ inputs)  n =
    (h₁ <ᵇ n) ∧ (h₂ <ᵇ n) ∧ all-lt? inputs n
  clause-mem-fits (clause-test-eq out a b)                 n =
    (out <ᵇ n) ∧ (a <ᵇ n) ∧ (b <ᵇ n)
  clause-mem-fits (clause-add out a b)                     n =
    (out <ᵇ n) ∧ (a <ᵇ n) ∧ (b <ᵇ n)
  clause-mem-fits (clause-mul out a b)                     n =
    (out <ᵇ n) ∧ (a <ᵇ n) ∧ (b <ᵇ n)
  clause-mem-fits (clause-neg out a)                       n =
    (out <ᵇ n) ∧ (a <ᵇ n)
  clause-mem-fits (clause-not out a)                       n =
    (out <ᵇ n) ∧ (a <ᵇ n)
  clause-mem-fits (clause-less-than out a b _)             n =
    (out <ᵇ n) ∧ (a <ᵇ n) ∧ (b <ᵇ n)
  clause-mem-fits (clause-guard-disj out i)                n =
    (out <ᵇ n) ∧ (i <ᵇ n)
  clause-mem-fits (clause-pi-from-wire _ wire)             n = wire <ᵇ n
  clause-mem-fits (clause-comm-commitment inputs outputs)  n =
    all-lt? inputs n ∧ all-lt? outputs n

  -- The dual of `holds-mem-extends`.  All lookups in `cl` are at indices
  -- `< length mem` (encoded as `clause-mem-fits cl (length mem) ≡ true`),
  -- so they pull back from `mem ++ suffix` to `mem`.
  --
  -- Implementation note:  each case mirrors `holds-mem-extends`, except
  -- it calls `lookup-shrink` (not `lookup-extends`) and threads the
  -- bound premise extracted from `clause-mem-fits cl (length mem) ≡ true`.
  holds-mem-shrink : ∀ {pis rand} (mem suffix : List Fr) (cl : Clause)
    → clause-mem-fits cl (length mem) ≡ true
    → holds (mk-witness (mem ++ suffix) pis rand) cl
    → holds (mk-witness mem pis rand) cl
  holds-mem-shrink mem suf (clause-assert-non-zero c) fits
    (v , lv , v≢0) =
    v , lookup-shrink mem suf c lv (<ᵇ-to-≤ c (length mem) fits) , v≢0
  holds-mem-shrink mem suf (clause-cond-select out b a c) fits
    (bv , av , cv , ov , lb , la , lc , lout , bit , eq)
    with ∧-≡-true-split fits
  ... | out< , fits1 with ∧-≡-true-split fits1
  ... | b< , fits2 with ∧-≡-true-split fits2
  ... | a< , c< =
    bv , av , cv , ov
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf c lc (<ᵇ-to-≤ c (length mem) c<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , bit , eq
  holds-mem-shrink mem suf (clause-range-bits v _) fits
    (vv , lv , fits-eq) =
    vv , lookup-shrink mem suf v lv (<ᵇ-to-≤ v (length mem) fits) , fits-eq
  holds-mem-shrink mem suf (clause-eq a b) fits
    (av , bv , la , lb , eq)
    with ∧-≡-true-split fits
  ... | a< , b< =
    av , bv
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , eq
  holds-mem-shrink mem suf (clause-bool v) fits
    (vv , lv , bit) =
    vv , lookup-shrink mem suf v lv (<ᵇ-to-≤ v (length mem) fits) , bit
  holds-mem-shrink mem suf (clause-copy out v) fits
    (vv , ov , lv , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , v< =
    vv , ov
    , lookup-shrink mem suf v lv (<ᵇ-to-≤ v (length mem) v<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-ec-add cx cy ax ay bx by) fits
    (axv , ayv , bxv , byv , cxv , cyv ,
     lax , lay , lbx , lby , lcx , lcy , add-eq)
    with ∧-≡-true-split fits
  ... | cx< , f1 with ∧-≡-true-split f1
  ... | cy< , f2 with ∧-≡-true-split f2
  ... | ax< , f3 with ∧-≡-true-split f3
  ... | ay< , f4 with ∧-≡-true-split f4
  ... | bx< , by< =
    axv , ayv , bxv , byv , cxv , cyv
    , lookup-shrink mem suf ax lax (<ᵇ-to-≤ ax (length mem) ax<)
    , lookup-shrink mem suf ay lay (<ᵇ-to-≤ ay (length mem) ay<)
    , lookup-shrink mem suf bx lbx (<ᵇ-to-≤ bx (length mem) bx<)
    , lookup-shrink mem suf by lby (<ᵇ-to-≤ by (length mem) by<)
    , lookup-shrink mem suf cx lcx (<ᵇ-to-≤ cx (length mem) cx<)
    , lookup-shrink mem suf cy lcy (<ᵇ-to-≤ cy (length mem) cy<)
    , add-eq
  holds-mem-shrink mem suf (clause-ec-mul cx cy ax ay sc) fits
    (axv , ayv , scv , cxv , cyv ,
     lax , lay , lsc , lcx , lcy , mul-eq)
    with ∧-≡-true-split fits
  ... | cx< , f1 with ∧-≡-true-split f1
  ... | cy< , f2 with ∧-≡-true-split f2
  ... | ax< , f3 with ∧-≡-true-split f3
  ... | ay< , sc< =
    axv , ayv , scv , cxv , cyv
    , lookup-shrink mem suf ax lax (<ᵇ-to-≤ ax (length mem) ax<)
    , lookup-shrink mem suf ay lay (<ᵇ-to-≤ ay (length mem) ay<)
    , lookup-shrink mem suf sc lsc (<ᵇ-to-≤ sc (length mem) sc<)
    , lookup-shrink mem suf cx lcx (<ᵇ-to-≤ cx (length mem) cx<)
    , lookup-shrink mem suf cy lcy (<ᵇ-to-≤ cy (length mem) cy<)
    , mul-eq
  holds-mem-shrink mem suf (clause-ec-mul-generator cx cy sc) fits
    (scv , cxv , cyv , lsc , lcx , lcy , gen-eq)
    with ∧-≡-true-split fits
  ... | cx< , f1 with ∧-≡-true-split f1
  ... | cy< , sc< =
    scv , cxv , cyv
    , lookup-shrink mem suf sc lsc (<ᵇ-to-≤ sc (length mem) sc<)
    , lookup-shrink mem suf cx lcx (<ᵇ-to-≤ cx (length mem) cx<)
    , lookup-shrink mem suf cy lcy (<ᵇ-to-≤ cy (length mem) cy<)
    , gen-eq
  holds-mem-shrink mem suf (clause-hash-to-curve cx cy inputs) fits
    (vs , cxv , cyv , lvs , lcx , lcy , hash-eq)
    with ∧-≡-true-split fits
  ... | cx< , f1 with ∧-≡-true-split f1
  ... | cy< , in< =
    vs , cxv , cyv
    , mem-lookups-shrink mem suf inputs in< lvs
    , lookup-shrink mem suf cx lcx (<ᵇ-to-≤ cx (length mem) cx<)
    , lookup-shrink mem suf cy lcy (<ᵇ-to-≤ cy (length mem) cy<)
    , hash-eq
  holds-mem-shrink mem suf (clause-load-imm out _) fits
    (ov , lout , eq) =
    ov , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) fits) , eq
  holds-mem-shrink mem suf (clause-div-mod q r v _) fits
    (qv , rv , vv , lq , lr , lv , fr , fq , eq)
    with ∧-≡-true-split fits
  ... | q< , f1 with ∧-≡-true-split f1
  ... | r< , v< =
    qv , rv , vv
    , lookup-shrink mem suf q lq (<ᵇ-to-≤ q (length mem) q<)
    , lookup-shrink mem suf r lr (<ᵇ-to-≤ r (length mem) r<)
    , lookup-shrink mem suf v lv (<ᵇ-to-≤ v (length mem) v<)
    , fr , fq , eq
  holds-mem-shrink mem suf (clause-reconstitute out d m _) fits
    (dv , mv , ov , ld , lm , lout , fd , fm , eq)
    with ∧-≡-true-split fits
  ... | out< , f1 with ∧-≡-true-split f1
  ... | d< , m< =
    dv , mv , ov
    , lookup-shrink mem suf d ld (<ᵇ-to-≤ d (length mem) d<)
    , lookup-shrink mem suf m lm (<ᵇ-to-≤ m (length mem) m<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , fd , fm , eq
  holds-mem-shrink mem suf (clause-transient-hash out inputs) fits
    (vs , ov , lvs , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , in< =
    vs , ov
    , mem-lookups-shrink mem suf inputs in< lvs
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-persistent-hash h₁ h₂ _ inputs) fits
    (vs , v1 , v2 , lvs , lh₁ , lh₂ , hash-eq)
    with ∧-≡-true-split fits
  ... | h1< , f1 with ∧-≡-true-split f1
  ... | h2< , in< =
    vs , v1 , v2
    , mem-lookups-shrink mem suf inputs in< lvs
    , lookup-shrink mem suf h₁ lh₁ (<ᵇ-to-≤ h₁ (length mem) h1<)
    , lookup-shrink mem suf h₂ lh₂ (<ᵇ-to-≤ h₂ (length mem) h2<)
    , hash-eq
  holds-mem-shrink mem suf (clause-test-eq out a b) fits
    (av , bv , ov , la , lb , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , f1 with ∧-≡-true-split f1
  ... | a< , b< =
    av , bv , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-add out a b) fits
    (av , bv , ov , la , lb , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , f1 with ∧-≡-true-split f1
  ... | a< , b< =
    av , bv , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-mul out a b) fits
    (av , bv , ov , la , lb , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , f1 with ∧-≡-true-split f1
  ... | a< , b< =
    av , bv , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-neg out a) fits
    (av , ov , la , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , a< =
    av , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-not out a) fits
    (av , ov , la , lout , eq)
    with ∧-≡-true-split fits
  ... | out< , a< =
    av , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , eq
  holds-mem-shrink mem suf (clause-less-than out a b _) fits
    (av , bv , ov , la , lb , lout , fa , fb , eq)
    with ∧-≡-true-split fits
  ... | out< , f1 with ∧-≡-true-split f1
  ... | a< , b< =
    av , bv , ov
    , lookup-shrink mem suf a la (<ᵇ-to-≤ a (length mem) a<)
    , lookup-shrink mem suf b lb (<ᵇ-to-≤ b (length mem) b<)
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , fa , fb , eq
  holds-mem-shrink mem suf (clause-guard-disj out i) fits
    (ov , iv , lout , li , disj)
    with ∧-≡-true-split fits
  ... | out< , i< =
    ov , iv
    , lookup-shrink mem suf out lout (<ᵇ-to-≤ out (length mem) out<)
    , lookup-shrink mem suf i li (<ᵇ-to-≤ i (length mem) i<)
    , disj
  holds-mem-shrink mem suf (clause-pi-from-wire entry wire) fits
    (wv , pv , lw , lpi , eq) =
    wv , pv
    , lookup-shrink mem suf wire lw (<ᵇ-to-≤ wire (length mem) fits)
    , lpi , eq
  holds-mem-shrink mem suf (clause-comm-commitment inputs outputs) fits
    (ivs , ovs , rv , pv , livs , lovs , crv , lpv , eq)
    with ∧-≡-true-split fits
  ... | in< , out< =
    ivs , ovs , rv , pv
    , mem-lookups-shrink mem suf inputs in< livs
    , mem-lookups-shrink mem suf outputs out< lovs
    , crv , lpv , eq

  -- All clauses fit: pointwise predicate, AND'd over the list.
  clauses-mem-fit : List Clause → ℕ → Bool
  clauses-mem-fit []       _ = true
  clauses-mem-fit (c ∷ cs) n = clause-mem-fits c n ∧ clauses-mem-fit cs n

  -- Satisfaction shrinks under suffix removal, given pointwise bounds.
  satisfies-clauses-mem-shrink : ∀ {pis rand}
    (cls : List Clause) (mem suf : List Fr)
    → clauses-mem-fit cls (length mem) ≡ true
    → satisfies-clauses cls (mk-witness (mem ++ suf) pis rand)
    → satisfies-clauses cls (mk-witness mem pis rand)
  satisfies-clauses-mem-shrink []       _   _   _    _            = tt
  satisfies-clauses-mem-shrink (c ∷ cs) mem suf fit (hd-h , tl-s)
    with ∧-≡-true-split fit
  ... | hd-fit , tl-fit =
    holds-mem-shrink mem suf c hd-fit hd-h
    , satisfies-clauses-mem-shrink cs mem suf tl-fit tl-s

  ------------------------------------------------------------------------
  -- H4 — pis shrink direction.
  --
  -- Dual of `satisfies-clauses-mem-shrink`.  Only `clause-pi-from-wire`
  -- and `clause-comm-commitment` mention pis; for all others the
  -- "fit" predicate is trivially `true` and the shrink is the identity.
  ------------------------------------------------------------------------

  -- pi-lookup analogue of `lookup-shrink`.  Mirrors the mem version.
  pi-lookup-shrink : ∀ (pis suffix : List Fr) i {v}
    → pi-lookup (pis ++ suffix) i ≡ just v
    → suc i Data.Nat.≤ length pis
    → pi-lookup pis i ≡ just v
  pi-lookup-shrink []        _ _       _  ()
  pi-lookup-shrink (x ∷ xs)  _ zero    eq _ = eq
  pi-lookup-shrink (x ∷ xs)  s (suc i) eq (Data.Nat.s≤s lt) =
    pi-lookup-shrink xs s i eq lt

  -- Per-clause "fits in pis of length n" predicate.  Only the two
  -- pis-referencing clauses are non-trivial; all others are `true`.
  clause-pis-fit : Clause → ℕ → Bool
  clause-pis-fit (clause-assert-non-zero _)              _ = true
  clause-pis-fit (clause-cond-select _ _ _ _)            _ = true
  clause-pis-fit (clause-range-bits _ _)                 _ = true
  clause-pis-fit (clause-eq _ _)                         _ = true
  clause-pis-fit (clause-bool _)                         _ = true
  clause-pis-fit (clause-copy _ _)                       _ = true
  clause-pis-fit (clause-ec-add _ _ _ _ _ _)             _ = true
  clause-pis-fit (clause-ec-mul _ _ _ _ _)               _ = true
  clause-pis-fit (clause-ec-mul-generator _ _ _)         _ = true
  clause-pis-fit (clause-hash-to-curve _ _ _)            _ = true
  clause-pis-fit (clause-load-imm _ _)                   _ = true
  clause-pis-fit (clause-div-mod _ _ _ _)                _ = true
  clause-pis-fit (clause-reconstitute _ _ _ _)           _ = true
  clause-pis-fit (clause-transient-hash _ _)             _ = true
  clause-pis-fit (clause-persistent-hash _ _ _ _)        _ = true
  clause-pis-fit (clause-test-eq _ _ _)                  _ = true
  clause-pis-fit (clause-add _ _ _)                      _ = true
  clause-pis-fit (clause-mul _ _ _)                      _ = true
  clause-pis-fit (clause-neg _ _)                        _ = true
  clause-pis-fit (clause-not _ _)                        _ = true
  clause-pis-fit (clause-less-than _ _ _ _)              _ = true
  clause-pis-fit (clause-guard-disj _ _)                 _ = true
  clause-pis-fit (clause-pi-from-wire entry _)           n = entry <ᵇ n
  clause-pis-fit (clause-comm-commitment _ _)            n = 1 <ᵇ n

  -- Shrink direction for `holds`:  if all pi-references in `cl` are
  -- < length pis, then `holds (mem, pis ++ suf, rand) cl` implies
  -- `holds (mem, pis, rand) cl`.
  holds-pis-shrink : ∀ {mem rand} (pis suf : List Fr) (cl : Clause)
    → clause-pis-fit cl (length pis) ≡ true
    → holds (mk-witness mem (pis ++ suf) rand) cl
    → holds (mk-witness mem pis            rand) cl
  holds-pis-shrink _ _ (clause-assert-non-zero _) _ h = h
  holds-pis-shrink _ _ (clause-cond-select _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-range-bits _ _) _ h = h
  holds-pis-shrink _ _ (clause-eq _ _) _ h = h
  holds-pis-shrink _ _ (clause-bool _) _ h = h
  holds-pis-shrink _ _ (clause-copy _ _) _ h = h
  holds-pis-shrink _ _ (clause-ec-add _ _ _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-ec-mul _ _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-ec-mul-generator _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-hash-to-curve _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-load-imm _ _) _ h = h
  holds-pis-shrink _ _ (clause-div-mod _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-reconstitute _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-transient-hash _ _) _ h = h
  holds-pis-shrink _ _ (clause-persistent-hash _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-test-eq _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-add _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-mul _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-neg _ _) _ h = h
  holds-pis-shrink _ _ (clause-not _ _) _ h = h
  holds-pis-shrink _ _ (clause-less-than _ _ _ _) _ h = h
  holds-pis-shrink _ _ (clause-guard-disj _ _) _ h = h
  holds-pis-shrink pis suf (clause-pi-from-wire entry wire) fits
    (wv , pv , lw , lpi , eq) =
    wv , pv , lw
    , pi-lookup-shrink pis suf entry lpi (<ᵇ-to-≤ entry (length pis) fits)
    , eq
  holds-pis-shrink pis suf (clause-comm-commitment inputs outputs) fits
    (ivs , ovs , rv , pv , livs , lovs , crv , lpv , eq) =
    ivs , ovs , rv , pv , livs , lovs , crv
    , pi-lookup-shrink pis suf 1 lpv (<ᵇ-to-≤ 1 (length pis) fits)
    , eq

  -- All clauses fit (pis-side): pointwise predicate AND'd over the list.
  clauses-pis-fit : List Clause → ℕ → Bool
  clauses-pis-fit []       _ = true
  clauses-pis-fit (c ∷ cs) n = clause-pis-fit c n ∧ clauses-pis-fit cs n

  -- List-level shrink for pis suffix.
  satisfies-clauses-pis-shrink : ∀ {mem rand}
    (cls : List Clause) (pis suf : List Fr)
    → clauses-pis-fit cls (length pis) ≡ true
    → satisfies-clauses cls (mk-witness mem (pis ++ suf) rand)
    → satisfies-clauses cls (mk-witness mem pis            rand)
  satisfies-clauses-pis-shrink []       _   _   _    _            = tt
  satisfies-clauses-pis-shrink (c ∷ cs) pis suf fit (hd-h , tl-s)
    with ∧-≡-true-split fit
  ... | hd-fit , tl-fit =
    holds-pis-shrink pis suf c hd-fit hd-h
    , satisfies-clauses-pis-shrink cs pis suf tl-fit tl-s

  -- Distributivity of satisfies-clauses over list concatenation.
  satisfies-clauses-++ : ∀ {w} (xs ys : List Clause)
    → satisfies-clauses xs w
    → satisfies-clauses ys w
    → satisfies-clauses (xs ++ ys) w
  satisfies-clauses-++ []       ys _            sy = sy
  satisfies-clauses-++ (x ∷ xs) ys (hx , sxs) sy =
    hx , satisfies-clauses-++ xs ys sxs sy

  -- Splitting direction of `satisfies-clauses-++`.  Used by the
  -- backward dispatcher D1 to peel off the prior clauses (which are
  -- satisfied at the post-state witness as a consequence of monotonicity)
  -- from the new clauses (which the dispatcher actually inverts).
  satisfies-clauses-split : ∀ {w} (xs ys : List Clause)
    → satisfies-clauses (xs ++ ys) w
    → satisfies-clauses xs w × satisfies-clauses ys w
  satisfies-clauses-split []       ys sat        = tt , sat
  satisfies-clauses-split (x ∷ xs) ys (hx , rest) =
    let sx , sy = satisfies-clauses-split xs ys rest
    in (hx , sx) , sy

  -- length-of-append for explicit nat arithmetic on mem-inv.
  length-++-1 : ∀ (xs : List Fr) y → length (xs ++ (y ∷ [])) ≡ suc (length xs)
  length-++-1 []       y = refl
  length-++-1 (x ∷ xs) y = cong suc (length-++-1 xs y)

  length-++-2 : ∀ (xs : List Fr) y z → length (xs ++ (y ∷ z ∷ [])) ≡ suc (suc (length xs))
  length-++-2 []       y z = refl
  length-++-2 (x ∷ xs) y z = cong suc (length-++-2 xs y z)

  -- n + 1 ≡ suc n
  +1-suc : ∀ n → n + 1 ≡ suc n
  +1-suc zero    = refl
  +1-suc (suc n) = cong suc (+1-suc n)

  -- n + 2 ≡ suc (suc n)
  +2-ss : ∀ n → n + 2 ≡ suc (suc n)
  +2-ss zero    = refl
  +2-ss (suc n) = cong suc (+2-ss n)

  -- Build the post-state mem-inv from the pre-state one for a Δmem = 1 instruction.
  mem-inv-step-1 : ∀ {st : SynthState} {mem : List Fr} {v : Fr}
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 1 ≡ length (mem ++ (v ∷ []))
  mem-inv-step-1 {st} {mem} {v} mi =
    trans (+1-suc (SynthState.nr-wires st))
          (trans (cong suc mi) (sym (length-++-1 mem v)))

  -- Δmem = 2 instruction (push-mem2 form: mem ++ (x ∷ y ∷ [])).
  mem-inv-step-2 : ∀ {st : SynthState} {mem : List Fr} {x y : Fr}
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 2 ≡ length (mem ++ (x ∷ y ∷ []))
  mem-inv-step-2 {st} {mem} {x} {y} mi =
    trans (+2-ss (SynthState.nr-wires st))
          (trans (cong (suc ∘ suc) mi) (sym (length-++-2 mem x y)))
    where open import Function using (_∘_)

  -- Δmem = 2 instruction (iterated push-mem form: (mem ++ (x ∷ [])) ++ (y ∷ [])).
  mem-inv-step-2' : ∀ {st : SynthState} {mem : List Fr} {x y : Fr}
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 2 ≡ length ((mem ++ (x ∷ [])) ++ (y ∷ []))
  mem-inv-step-2' {st} {mem} {x} {y} mi =
    trans (mem-inv-step-2 {st} {mem} {x} {y} mi)
          (cong length (push-mem2-assoc-local mem x y))
    where
      push-mem2-assoc-local : ∀ (m : List Fr) x y
        → m ++ (x ∷ y ∷ []) ≡ (m ++ (x ∷ [])) ++ (y ∷ [])
      push-mem2-assoc-local []       x y = refl
      push-mem2-assoc-local (z ∷ zs) x y = cong (z ∷_) (push-mem2-assoc-local zs x y)

  -- Uniform dispatcher helper for the "memory-only-extends" cases.
  -- An instruction `i` whose `R-instr` evidence yields a memory
  -- suffix `suf` and whose `circuit-instr hc i st` only appends new
  -- clauses (no `nr-declared-pi` or `output-wires` change) and whose
  -- per-instruction forward lemma is `i-fwd` can be discharged via
  -- this template:
  --
  --   1. Lift prior-sat to (mem ++ suf, pis, rand) via mem-extends.
  --   2. Apply `i-fwd` to get satisfaction of the *new* clauses at
  --      (mem ++ suf, pis, rand).
  --   3. Concatenate via `satisfies-clauses-++`.
  --
  -- This template's preconditions ensure
  -- `clauses (circuit-instr hc i st) = clauses st ++ newcls`, which
  -- holds by definition for all instructions except `pi-skip` and
  -- `output` (which emit no clauses) and `public-input nothing` and
  -- `private-input nothing` (which also emit no clauses but still
  -- bump `nr-wires`).

  -- The PI vector along an R-instr step extends pre-pis with a suffix.
  -- Only `declare-pub-input` extends the pis (with one cell); all others
  -- leave them unchanged.
  pis-extends-R-instr : ∀ {pre s i s'}
    → R-instr pre s i s'
    → Σ-syntax (List Fr) λ suf →
        Preprocessed.pis s' ≡ Preprocessed.pis s ++ suf
  pis-extends-R-instr (r-assert _)                   = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-cond-select _ _ _)          = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-constrain-bits _ _)         = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-constrain-eq _ _ _)         = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-constrain-to-boolean _)     = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-copy _)                     = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-declare-pub-input {v = v} _) = v ∷ [] , refl
  pis-extends-R-instr (r-pi-skip-active _ _)         = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-pi-skip-inactive _)         = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-ec-add _ _ _ _ _)           = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-ec-mul _ _ _ _)             = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-ec-mul-generator _ _)       = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-hash-to-curve _ _)          = [] , sym (++-identityʳ _)
  pis-extends-R-instr r-load-imm                     = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-div-mod-power-of-two _)     = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-reconstitute-field _ _ _)   = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-output _)                   = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-transient-hash _)           = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-persistent-hash _ _)        = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-test-eq _ _)                = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-add _ _)                    = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-mul _ _)                    = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-neg _)                      = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-not _)                      = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-less-than _ _ _)            = [] , sym (++-identityʳ _)
  pis-extends-R-instr (r-public-input-inactive _)    = [] , sym (++-identityʳ _)
  pis-extends-R-instr {s = s} (r-public-input-active {s₁ = s₁} _ cp) =
    [] , trans (consume-pub-out-pis-aux s cp) (sym (++-identityʳ _))
    where
      consume-pub-out-pis-aux : ∀ s {v s'}
        → consume-pub-out s ≡ just (v , s')
        → Preprocessed.pis s' ≡ Preprocessed.pis s
      consume-pub-out-pis-aux s eq with Preprocessed.pub-out-rem s | eq
      ... | []    | ()
      ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))
  pis-extends-R-instr (r-private-input-inactive _)   = [] , sym (++-identityʳ _)
  pis-extends-R-instr {s = s} (r-private-input-active {s₁ = s₁} _ cp) =
    [] , trans (consume-priv-pis-aux s cp) (sym (++-identityʳ _))
    where
      consume-priv-pis-aux : ∀ s {v s'}
        → consume-priv s ≡ just (v , s')
        → Preprocessed.pis s' ≡ Preprocessed.pis s
      consume-priv-pis-aux s eq with Preprocessed.priv-rem s | eq
      ... | []    | ()
      ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))

------------------------------------------------------------------------
-- Section C.  Forward direction (statements only).
--
-- Two layers:
--
--   • `R-instrs→satisfies-clauses`     instruction-list induction
--   • `circuit-faithful-fwd`           top-level (incl. comm-commitment)
--
-- Phase 4b will fill the bodies.
------------------------------------------------------------------------

-- Sub-lemma 1: a single R-instr step preserves the satisfaction of any
-- prior clause list, and the new clauses emitted by `circuit-instr` for
-- that step are satisfied by the post-state assignment.
--
-- This is essentially the conjunction of the 26 forward lemmas in
-- `CircuitFaithfulness.agda`, generalized to thread:
--
--   • the previously-accumulated clauses (they stay satisfied because
--     they only mention indices < length pre-mem, and pre-mem is a
--     prefix of post-mem);
--   • the invariants I-mem and I-pi (which the synthesis-state record
--     also obeys clause-by-clause).
--
-- Note (Phase 4b refinement): the 4a signature was missing the
-- `prior-sat` hypothesis.  Without it the per-step proof cannot lift the
-- previously-emitted clauses to the post-state's larger memory.  Added
-- as `prior-sat` below.
--
-- N.B.: the four §6.5 cases (assert, not, reconstitute-field,
-- less-than) reqire a producer-obligation hypothesis to discharge
-- their BACKWARD direction.  Forward direction is gap-free for all
-- four — Phase 4b can land without obligations.

-- Concrete-state version of `single-instr-clauses-with-decl`: applies
-- the synthesis function to an arbitrary `st`, returning the *new*
-- clauses emitted (i.e. `clauses st`-suffix).  Definitionally equal to
-- `single-instr-clauses-with-decl hc (nr-wires st) (nr-declared-pi st) i`
-- (this is what `circuit-instr` does, up to the prior clauses prefix).
--
-- The actual proof discharges via direct case analysis on `i`.
R-instr→satisfies-step
  : ∀ {hc} (pre : ProofPreimage) (s s' : Preprocessed) (i : Instruction)
  → (st : SynthState)
  → mem-inv s st
  → pi-inv  hc s st
  → satisfies-clauses (SynthState.clauses st)
      (mk-witness (Preprocessed.memory s)
                  (Preprocessed.pis    s)
                  (comm-rand-of pre))
  → R-instr pre s i s'
  →   mem-inv s' (circuit-instr hc i st)
    × pi-inv  hc s' (circuit-instr hc i st)
    × satisfies-clauses
        (SynthState.clauses (circuit-instr hc i st))
        (mk-witness (Preprocessed.memory s')
                    (Preprocessed.pis    s')
                    (comm-rand-of pre))
-- For each case, we use the helpers built up above:
--   • `mem-extends-R-instr` to identify the suffix appended to memory;
--   • `pis-extends-R-instr` for the (zero-or-one-cell) pis suffix;
--   • the corresponding `*-fwd` lemma from CircuitFaithfulness;
--   • `satisfies-clauses-mem-extends` / `-pis-extends` to lift prior-sat;
--   • `satisfies-clauses-++` to combine.

-- Pattern-matching helper: each case applies the appropriate forward
-- lemma to the new clauses and concatenates with the lifted prior-sat.

-- assert(c): mem and pis unchanged.  newcls = [clause-assert-non-zero c].
R-instr→satisfies-step {hc} pre s .s (assert c) st mi pi prior-sat r@(r-assert _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre      ; w   = mk-witness mem pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (assert c)
                 ≡ single-instr-clauses hc (length mem) (assert c)
      newcls-eq = cong (λ n → single-instr-clauses hc n (assert c)) mi
      sat-new : satisfies-clauses
                  (single-instr-clauses hc (SynthState.nr-wires st) (assert c)) w
      sat-new = subst (λ cls → satisfies-clauses cls w) (sym newcls-eq)
                       (assert-fwd {pre = pre} {s = s} {s' = s} {c = c} {hc = hc}
                                    {rand = rand} r)
  in mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ prior-sat sat-new

-- constrain-bits(v, n): mem and pis unchanged.
R-instr→satisfies-step {hc} pre s .s (constrain-bits v n) st mi pi prior-sat r@(r-constrain-bits _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre      ; w   = mk-witness mem pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (constrain-bits v n)
                 ≡ single-instr-clauses hc (length mem) (constrain-bits v n)
      newcls-eq = cong (λ k → single-instr-clauses hc k (constrain-bits v n)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w) (sym newcls-eq)
                       (constrain-bits-fwd {pre = pre} {s = s} {s' = s}
                                            {v = v} {n = n} {hc = hc} {rand = rand} r)
  in mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ prior-sat sat-new

-- constrain-eq(a, b): mem and pis unchanged.
R-instr→satisfies-step {hc} pre s .s (constrain-eq a b) st mi pi prior-sat r@(r-constrain-eq _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre      ; w   = mk-witness mem pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (constrain-eq a b)
                 ≡ single-instr-clauses hc (length mem) (constrain-eq a b)
      newcls-eq = cong (λ k → single-instr-clauses hc k (constrain-eq a b)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w) (sym newcls-eq)
                       (constrain-eq-fwd {pre = pre} {s = s} {s' = s}
                                          {a = a} {b = b} {hc = hc} {rand = rand} r)
  in mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ prior-sat sat-new

-- constrain-to-boolean(v): mem and pis unchanged.
R-instr→satisfies-step {hc} pre s .s (constrain-to-boolean v) st mi pi prior-sat r@(r-constrain-to-boolean _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre      ; w   = mk-witness mem pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (constrain-to-boolean v)
                 ≡ single-instr-clauses hc (length mem) (constrain-to-boolean v)
      newcls-eq = cong (λ k → single-instr-clauses hc k (constrain-to-boolean v)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w) (sym newcls-eq)
                       (constrain-to-boolean-fwd {pre = pre} {s = s} {s' = s}
                                                  {v = v} {hc = hc} {rand = rand} r)
  in mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ prior-sat sat-new

-- copy(v): Δmem = 1, pis unchanged.
R-instr→satisfies-step {hc} pre s s' (copy v) st mi pi prior-sat r@(r-copy {v = v0} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (v0 ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (copy v)
                 ≡ single-instr-clauses hc (length mem) (copy v)
      newcls-eq = cong (λ k → single-instr-clauses hc k (copy v)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (copy-fwd {pre = pre} {s = s} {s' = s'}
                                  {v = v} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {v0} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- load-imm(imm): Δmem = 1, pis unchanged.
R-instr→satisfies-step {hc} pre s s' (load-imm imm) st mi pi prior-sat r@r-load-imm =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (imm ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (load-imm imm)
                 ≡ single-instr-clauses hc (length mem) (load-imm imm)
      newcls-eq = cong (λ k → single-instr-clauses hc k (load-imm imm)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (load-imm-fwd {pre = pre} {s = s} {s' = s'}
                                      {k = imm} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {imm} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- add(a, b): Δmem = 1, pis unchanged.
R-instr→satisfies-step {hc} pre s s' (add a b) st mi pi prior-sat r@(r-add {av = av} {bv = bv} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ ((av +ᶠ bv) ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (add a b)
                 ≡ single-instr-clauses hc (length mem) (add a b)
      newcls-eq = cong (λ k → single-instr-clauses hc k (add a b)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (add-fwd {pre = pre} {s = s} {s' = s'}
                                 {a = a} {b = b} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {av +ᶠ bv} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- mul(a, b)
R-instr→satisfies-step {hc} pre s s' (mul a b) st mi pi prior-sat r@(r-mul {av = av} {bv = bv} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ ((av *ᶠ bv) ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (mul a b)
                 ≡ single-instr-clauses hc (length mem) (mul a b)
      newcls-eq = cong (λ k → single-instr-clauses hc k (mul a b)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (mul-fwd {pre = pre} {s = s} {s' = s'}
                                 {a = a} {b = b} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {av *ᶠ bv} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- neg(a)
R-instr→satisfies-step {hc} pre s s' (neg a) st mi pi prior-sat r@(r-neg {av = av} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ ((-ᶠ av) ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (neg a)
                 ≡ single-instr-clauses hc (length mem) (neg a)
      newcls-eq = cong (λ k → single-instr-clauses hc k (neg a)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (neg-fwd {pre = pre} {s = s} {s' = s'}
                                 {a = a} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} { -ᶠ av } mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- test-eq(a, b)
R-instr→satisfies-step {hc} pre s s' (test-eq a b) st mi pi prior-sat r@(r-test-eq {av = av} {bv = bv} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (from-bool (av ≡ᶠ? bv) ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (test-eq a b)
                 ≡ single-instr-clauses hc (length mem) (test-eq a b)
      newcls-eq = cong (λ k → single-instr-clauses hc k (test-eq a b)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (test-eq-fwd {pre = pre} {s = s} {s' = s'}
                                     {a = a} {b = b} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {from-bool (av ≡ᶠ? bv)} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- not(a)
R-instr→satisfies-step {hc} pre s s' (not a) st mi pi prior-sat r@(r-not {b = b0} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (from-bool (Bool.not b0) ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (not a)
                 ≡ single-instr-clauses hc (length mem) (not a)
      newcls-eq = cong (λ k → single-instr-clauses hc k (not a)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (not-fwd {pre = pre} {s = s} {s' = s'}
                                 {a = a} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {from-bool (Bool.not b0)} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- cond-select(b, a, c): Δmem = 1.  Output value is `if sel then av else bv`.
R-instr→satisfies-step {hc} pre s s' (cond-select b a c) st mi pi prior-sat
  r@(r-cond-select {sel = sel} {av = av} {bv = bv} _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      ov   = if sel then av else bv
      mem' = mem ++ (ov ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (cond-select b a c)
                 ≡ single-instr-clauses hc (length mem) (cond-select b a c)
      newcls-eq = cong (λ k → single-instr-clauses hc k (cond-select b a c)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (cond-select-fwd {pre = pre} {s = s} {s' = s'}
                                         {b = b} {a = a} {c = c} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {ov} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- less-than(a, b, n): Δmem = 1.  Output value: `from-bool (bits-lt ...)`.
R-instr→satisfies-step {hc} pre s s' (less-than a b bits) st mi pi prior-sat
  r@(r-less-than {av = av} {bv = bv} _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      ov   = from-bool (bits-lt (take bits (to-le-bits av)) (take bits (to-le-bits bv)))
      mem' = mem ++ (ov ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (less-than a b bits)
                 ≡ single-instr-clauses hc (length mem) (less-than a b bits)
      newcls-eq = cong (λ k → single-instr-clauses hc k (less-than a b bits)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (less-than-fwd {pre = pre} {s = s} {s' = s'}
                                       {a = a} {b = b} {bits = bits} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {ov} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- transient-hash(inputs): Δmem = 1.  Output value: transient-hash-fn vs.
R-instr→satisfies-step {hc} pre s s' (transient-hash inputs) st mi pi prior-sat
  r@(r-transient-hash {vs = vs} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      ov   = transient-hash-fn vs
      mem' = mem ++ (ov ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (transient-hash inputs)
                 ≡ single-instr-clauses hc (length mem) (transient-hash inputs)
      newcls-eq = cong (λ k → single-instr-clauses hc k (transient-hash inputs)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (transient-hash-fwd {pre = pre} {s = s} {s' = s'}
                                            {inputs = inputs} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {ov} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- reconstitute-field(d, m, bits): Δmem = 1.
R-instr→satisfies-step {hc} pre s s' (reconstitute-field d m bits) st mi pi prior-sat
  r@(r-reconstitute-field {dv = dv} {mv = mv} _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      ov   = from-le-bits (take bits (to-le-bits mv) ++ take (FR-BITS ∸ bits) (to-le-bits dv))
      mem' = mem ++ (ov ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (reconstitute-field d m bits)
                 ≡ single-instr-clauses hc (length mem) (reconstitute-field d m bits)
      newcls-eq = cong (λ k → single-instr-clauses hc k (reconstitute-field d m bits)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (reconstitute-field-fwd {pre = pre} {s = s} {s' = s'}
                                                {d = d} {m = m} {bits = bits} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {ov} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- ec-add: Δmem = 2 (push-mem2 form, mem ++ x ∷ y ∷ []).
R-instr→satisfies-step {hc} pre s s' (ec-add a-x a-y b-x b-y) st mi pi prior-sat
  r@(r-ec-add {cx = cx} {cy = cy} _ _ _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (cx ∷ cy ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (ec-add a-x a-y b-x b-y)
                 ≡ single-instr-clauses hc (length mem) (ec-add a-x a-y b-x b-y)
      newcls-eq = cong (λ k → single-instr-clauses hc k (ec-add a-x a-y b-x b-y)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (ec-add-fwd {pre = pre} {s = s} {s' = s'}
                                    {a-x = a-x} {a-y = a-y} {b-x = b-x} {b-y = b-y}
                                    {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-2 {st} {mem} {cx} {cy} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- ec-mul
R-instr→satisfies-step {hc} pre s s' (ec-mul a-x a-y scalar) st mi pi prior-sat
  r@(r-ec-mul {cx = cx} {cy = cy} _ _ _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (cx ∷ cy ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (ec-mul a-x a-y scalar)
                 ≡ single-instr-clauses hc (length mem) (ec-mul a-x a-y scalar)
      newcls-eq = cong (λ k → single-instr-clauses hc k (ec-mul a-x a-y scalar)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (ec-mul-fwd {pre = pre} {s = s} {s' = s'}
                                    {a-x = a-x} {a-y = a-y} {scalar = scalar}
                                    {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-2 {st} {mem} {cx} {cy} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- ec-mul-generator
R-instr→satisfies-step {hc} pre s s' (ec-mul-generator scalar) st mi pi prior-sat
  r@(r-ec-mul-generator {cx = cx} {cy = cy} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (cx ∷ cy ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (ec-mul-generator scalar)
                 ≡ single-instr-clauses hc (length mem) (ec-mul-generator scalar)
      newcls-eq = cong (λ k → single-instr-clauses hc k (ec-mul-generator scalar)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (ec-mul-generator-fwd {pre = pre} {s = s} {s' = s'}
                                              {scalar = scalar} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-2 {st} {mem} {cx} {cy} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- hash-to-curve
R-instr→satisfies-step {hc} pre s s' (hash-to-curve inputs) st mi pi prior-sat
  r@(r-hash-to-curve {cx = cx} {cy = cy} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (cx ∷ cy ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (hash-to-curve inputs)
                 ≡ single-instr-clauses hc (length mem) (hash-to-curve inputs)
      newcls-eq = cong (λ k → single-instr-clauses hc k (hash-to-curve inputs)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (hash-to-curve-fwd {pre = pre} {s = s} {s' = s'}
                                           {inputs = inputs} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-2 {st} {mem} {cx} {cy} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- persistent-hash
R-instr→satisfies-step {hc} pre s s' (persistent-hash alignment inputs) st mi pi prior-sat
  r@(r-persistent-hash {h₁ = h₁} {h₂ = h₂} _ _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (h₁ ∷ h₂ ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (persistent-hash alignment inputs)
                 ≡ single-instr-clauses hc (length mem) (persistent-hash alignment inputs)
      newcls-eq = cong (λ k → single-instr-clauses hc k (persistent-hash alignment inputs)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (persistent-hash-fwd {pre = pre} {s = s} {s' = s'}
                                             {α = alignment} {inputs = inputs}
                                             {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-2 {st} {mem} {h₁} {h₂} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- div-mod-power-of-two: Δmem = 2, iterated push-mem form.  The
-- post-state's memory is (mem ++ (divisor ∷ [])) ++ (modulus ∷ []) per
-- `r-div-mod-power-of-two`.  The forward lemma matches that shape.
R-instr→satisfies-step {hc} pre s s' (div-mod-power-of-two var bits) st mi pi prior-sat
  r@(r-div-mod-power-of-two {v = vv} _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      divisor = from-le-bits (drop bits (to-le-bits vv))
      modulus = from-le-bits (take bits (to-le-bits vv))
      mem' = (mem ++ (divisor ∷ [])) ++ (modulus ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (div-mod-power-of-two var bits)
                 ≡ single-instr-clauses hc (length mem) (div-mod-power-of-two var bits)
      newcls-eq = cong (λ k → single-instr-clauses hc k (div-mod-power-of-two var bits)) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (div-mod-power-of-two-fwd {pre = pre} {s = s} {s' = s'}
                                                  {var = var} {bits = bits}
                                                  {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends
                       {suffix = modulus ∷ []}
                       (SynthState.clauses st)
                       (satisfies-clauses-mem-extends
                          {suffix = divisor ∷ []}
                          (SynthState.clauses st) prior-sat)
  in mem-inv-step-2' {st} {mem} {divisor} {modulus} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- output(v): no clauses.  push-output appends to s.outputs but leaves
-- memory and pis unchanged.  Only `output-wires` changes in the synth
-- state — irrelevant to `clauses`/`nr-wires`/`nr-declared-pi`.
R-instr→satisfies-step {hc} pre s s' (output v) st mi pi prior-sat r@(r-output _) =
  -- s' = push-output s _, whose memory ≡ memory s and pis ≡ pis s
  -- (push-output only modifies the `outputs` field).
  -- circuit-instr _ (output v) st = record st { output-wires = … },
  -- so its clauses ≡ st.clauses, nr-wires ≡ st.nr-wires, nr-declared-pi ≡ st.nr-declared-pi.
  mi , pi , prior-sat

-- pi-skip(guard, count): no clauses, no Δmem.  But the operational rule
-- does change the synth state's record (pi-skips, possibly pub-in-idx).
-- All effects on `Preprocessed` happen via `push-skip` which doesn't
-- change `memory` or `pis`.  The synth state is left entirely untouched
-- by `circuit-instr _ (pi-skip _ _) st = st`.
R-instr→satisfies-step {hc} pre s s' (pi-skip g n) st mi pi prior-sat
  (r-pi-skip-active _ _) =
  -- Post-state: push-skip s nothing.  push-skip leaves memory/pis unchanged.
  -- nr-wires st unchanged ≡ length (push-skip-memory) = length mem.
  mi , pi , prior-sat
R-instr→satisfies-step {hc} pre s s' (pi-skip g n) st mi pi prior-sat
  (r-pi-skip-inactive _) =
  mi , pi , prior-sat

-- public-input nothing: Δmem = 1, no clauses.  Fires r-public-input-active
-- since `eval-guard _ nothing ≡ just true` by definition.
R-instr→satisfies-step {hc} pre s s' (public-input nothing) st mi pi prior-sat
  (r-public-input-active {v = v} {s₁ = s₁} _ cp) =
  -- s' = push-mem s₁ v.  consume-pub-out leaves memory and pis unchanged.
  let mem  = Preprocessed.memory s
      mem-eq : Preprocessed.memory s₁ ≡ mem
      mem-eq = consume-pub-out-mem' s cp
      pis-eq : Preprocessed.pis s₁ ≡ Preprocessed.pis s
      pis-eq = consume-pub-out-pis' s cp
      mem-s' : Preprocessed.memory s' ≡ mem ++ (v ∷ [])
      mem-s' = cong (_++ (v ∷ [])) mem-eq
      pis-s' : Preprocessed.pis s' ≡ Preprocessed.pis s
      pis-s' = pis-eq
      rand = comm-rand-of pre
      lifted-mem : satisfies-clauses (SynthState.clauses st)
                     (mk-witness (mem ++ (v ∷ [])) (Preprocessed.pis s) rand)
      lifted-mem = satisfies-clauses-mem-extends {suffix = v ∷ []}
                     (SynthState.clauses st) prior-sat
      lifted : satisfies-clauses (SynthState.clauses st)
                 (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      lifted = subst (λ p → satisfies-clauses (SynthState.clauses st)
                              (mk-witness (Preprocessed.memory s') p rand))
                      (sym pis-s')
                      (subst (λ m → satisfies-clauses (SynthState.clauses st)
                                       (mk-witness m (Preprocessed.pis s) rand))
                              (sym mem-s')
                              lifted-mem)
      mi' = subst (λ m → SynthState.nr-wires st + 1 ≡ length m) (sym mem-s')
                  (mem-inv-step-1 {st} {mem} {v} mi)
      pi' = subst (λ p → length p ≡ preamble-pi-count hc + SynthState.nr-declared-pi st)
                  (sym pis-s') pi
  in mi' , pi' , lifted
  where
    consume-pub-out-mem' : ∀ s {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-pub-out-mem' s eq with Preprocessed.pub-out-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))
    consume-pub-out-pis' : ∀ s {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-pub-out-pis' s eq with Preprocessed.pub-out-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))

-- private-input nothing: identical pattern to public-input nothing.
R-instr→satisfies-step {hc} pre s s' (private-input nothing) st mi pi prior-sat
  (r-private-input-active {v = v} {s₁ = s₁} _ cp) =
  let mem  = Preprocessed.memory s
      mem-eq = consume-priv-mem' s cp
      pis-eq = consume-priv-pis' s cp
      mem-s' : Preprocessed.memory s' ≡ mem ++ (v ∷ [])
      mem-s' = cong (_++ (v ∷ [])) mem-eq
      pis-s' : Preprocessed.pis s' ≡ Preprocessed.pis s
      pis-s' = pis-eq
      rand = comm-rand-of pre
      lifted-mem : satisfies-clauses (SynthState.clauses st)
                     (mk-witness (mem ++ (v ∷ [])) (Preprocessed.pis s) rand)
      lifted-mem = satisfies-clauses-mem-extends {suffix = v ∷ []}
                     (SynthState.clauses st) prior-sat
      lifted : satisfies-clauses (SynthState.clauses st)
                 (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      lifted = subst (λ p → satisfies-clauses (SynthState.clauses st)
                              (mk-witness (Preprocessed.memory s') p rand))
                      (sym pis-s')
                      (subst (λ m → satisfies-clauses (SynthState.clauses st)
                                       (mk-witness m (Preprocessed.pis s) rand))
                              (sym mem-s')
                              lifted-mem)
      mi' = subst (λ m → SynthState.nr-wires st + 1 ≡ length m) (sym mem-s')
                  (mem-inv-step-1 {st} {mem} {v} mi)
      pi' = subst (λ p → length p ≡ preamble-pi-count hc + SynthState.nr-declared-pi st)
                  (sym pis-s') pi
  in mi' , pi' , lifted
  where
    consume-priv-mem' : ∀ s {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-priv-mem' s eq with Preprocessed.priv-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))
    consume-priv-pis' : ∀ s {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-priv-pis' s eq with Preprocessed.priv-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))

-- public-input (just g) — inactive: Δmem = 1, push-mem s 0ᶠ.
R-instr→satisfies-step {hc} pre s s' (public-input (just g)) st mi pi prior-sat
  r@(r-public-input-inactive _) =
  -- s' = push-mem s 0ᶠ.
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (0ᶠ ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (public-input (just g))
                 ≡ single-instr-clauses hc (length mem) (public-input (just g))
      newcls-eq = cong (λ k → single-instr-clauses hc k (public-input (just g))) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (public-input-just-fwd {pre = pre} {s = s} {s' = s'}
                                                {g = g} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {0ᶠ} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- public-input (just g) — active: Δmem = 1, push-mem s₁ v where s₁ shares mem/pis with s.
R-instr→satisfies-step {hc} pre s s' (public-input (just g)) st mi pi prior-sat
  r@(r-public-input-active {v = v} {s₁ = s₁} _ cp) =
  let mem  = Preprocessed.memory s
      mem-eq : Preprocessed.memory s₁ ≡ mem
      mem-eq = consume-pub-out-mem' s cp
      pis-eq : Preprocessed.pis s₁ ≡ Preprocessed.pis s
      pis-eq = consume-pub-out-pis' s cp
      mem-s' : Preprocessed.memory s' ≡ mem ++ (v ∷ [])
      mem-s' = cong (_++ (v ∷ [])) mem-eq
      pis-s' : Preprocessed.pis s' ≡ Preprocessed.pis s
      pis-s' = pis-eq
      rand = comm-rand-of pre
      cls-i = single-instr-clauses hc (length mem) (public-input (just g))
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (public-input (just g))
                 ≡ cls-i
      newcls-eq = cong (λ k → single-instr-clauses hc k (public-input (just g))) mi
      -- Direct: per-fwd gives us satisfaction at s'.
      sat-new-s' : satisfies-clauses cls-i
                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      sat-new-s' = public-input-just-fwd {pre = pre} {s = s} {s' = s'}
                                          {g = g} {hc = hc} {rand = rand} r
      sat-new-st : satisfies-clauses
                     (single-instr-clauses hc (SynthState.nr-wires st) (public-input (just g)))
                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      sat-new-st = subst (λ cls → satisfies-clauses cls
                                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand))
                          (sym newcls-eq) sat-new-s'
      -- Lift prior-sat to (mem (= memory s₁) ++ [v], pis (= pis s₁), rand).
      lifted-mem : satisfies-clauses (SynthState.clauses st)
                     (mk-witness (mem ++ (v ∷ [])) (Preprocessed.pis s) rand)
      lifted-mem = satisfies-clauses-mem-extends {suffix = v ∷ []}
                     (SynthState.clauses st) prior-sat
      -- Cast to (memory s', pis s', rand) via mem-s', pis-s'.
      lifted-prior : satisfies-clauses (SynthState.clauses st)
                       (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      lifted-prior = subst (λ p → satisfies-clauses (SynthState.clauses st)
                                     (mk-witness (Preprocessed.memory s') p rand))
                            (sym pis-s')
                            (subst (λ m → satisfies-clauses (SynthState.clauses st)
                                             (mk-witness m (Preprocessed.pis s) rand))
                                    (sym mem-s')
                                    lifted-mem)
      mi' = subst (λ m → SynthState.nr-wires st + 1 ≡ length m) (sym mem-s')
                  (mem-inv-step-1 {st} {mem} {v} mi)
      pi' = subst (λ p → length p ≡ preamble-pi-count hc + SynthState.nr-declared-pi st)
                  (sym pis-s') pi
  in mi' , pi' ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new-st
  where
    consume-pub-out-mem' : ∀ s {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-pub-out-mem' s eq with Preprocessed.pub-out-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))
    consume-pub-out-pis' : ∀ s {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-pub-out-pis' s eq with Preprocessed.pub-out-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))

-- private-input (just g) — inactive
R-instr→satisfies-step {hc} pre s s' (private-input (just g)) st mi pi prior-sat
  r@(r-private-input-inactive _) =
  let mem  = Preprocessed.memory s ; pis = Preprocessed.pis s
      rand = comm-rand-of pre
      mem' = mem ++ (0ᶠ ∷ [])
      w'   = mk-witness mem' pis rand
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (private-input (just g))
                 ≡ single-instr-clauses hc (length mem) (private-input (just g))
      newcls-eq = cong (λ k → single-instr-clauses hc k (private-input (just g))) mi
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq)
                       (private-input-just-fwd {pre = pre} {s = s} {s' = s'}
                                                 {g = g} {hc = hc} {rand = rand} r)
      lifted-prior = satisfies-clauses-mem-extends (SynthState.clauses st) prior-sat
  in mem-inv-step-1 {st} {mem} {0ᶠ} mi , pi ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new

-- private-input (just g) — active
R-instr→satisfies-step {hc} pre s s' (private-input (just g)) st mi pi prior-sat
  r@(r-private-input-active {v = v} {s₁ = s₁} _ cp) =
  let mem  = Preprocessed.memory s
      mem-eq = consume-priv-mem'' s cp
      pis-eq = consume-priv-pis'' s cp
      mem-s' : Preprocessed.memory s' ≡ mem ++ (v ∷ [])
      mem-s' = cong (_++ (v ∷ [])) mem-eq
      pis-s' : Preprocessed.pis s' ≡ Preprocessed.pis s
      pis-s' = pis-eq
      rand = comm-rand-of pre
      cls-i = single-instr-clauses hc (length mem) (private-input (just g))
      newcls-eq : single-instr-clauses hc (SynthState.nr-wires st) (private-input (just g))
                 ≡ cls-i
      newcls-eq = cong (λ k → single-instr-clauses hc k (private-input (just g))) mi
      sat-new-s' : satisfies-clauses cls-i
                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      sat-new-s' = private-input-just-fwd {pre = pre} {s = s} {s' = s'}
                                           {g = g} {hc = hc} {rand = rand} r
      sat-new-st : satisfies-clauses
                     (single-instr-clauses hc (SynthState.nr-wires st) (private-input (just g)))
                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      sat-new-st = subst (λ cls → satisfies-clauses cls
                                     (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand))
                          (sym newcls-eq) sat-new-s'
      lifted-mem : satisfies-clauses (SynthState.clauses st)
                     (mk-witness (mem ++ (v ∷ [])) (Preprocessed.pis s) rand)
      lifted-mem = satisfies-clauses-mem-extends {suffix = v ∷ []}
                     (SynthState.clauses st) prior-sat
      lifted-prior : satisfies-clauses (SynthState.clauses st)
                       (mk-witness (Preprocessed.memory s') (Preprocessed.pis s') rand)
      lifted-prior = subst (λ p → satisfies-clauses (SynthState.clauses st)
                                     (mk-witness (Preprocessed.memory s') p rand))
                            (sym pis-s')
                            (subst (λ m → satisfies-clauses (SynthState.clauses st)
                                             (mk-witness m (Preprocessed.pis s) rand))
                                    (sym mem-s')
                                    lifted-mem)
      mi' = subst (λ m → SynthState.nr-wires st + 1 ≡ length m) (sym mem-s')
                  (mem-inv-step-1 {st} {mem} {v} mi)
      pi' = subst (λ p → length p ≡ preamble-pi-count hc + SynthState.nr-declared-pi st)
                  (sym pis-s') pi
  in mi' , pi' ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new-st
  where
    consume-priv-mem'' : ∀ s {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-priv-mem'' s eq with Preprocessed.priv-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.memory (cong proj₂ (just-injective p)))
    consume-priv-pis'' : ∀ s {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-priv-pis'' s eq with Preprocessed.priv-rem s | eq
    ... | []    | ()
    ... | _ ∷ _ | p = sym (cong Preprocessed.pis (cong proj₂ (just-injective p)))

-- declare-pub-input(v): pis grows by 1 cell with the value of wire v.
-- Mem unchanged.  Uses `single-instr-clauses-with-decl`.  nr-declared-pi
-- in synth state increments by 1.
R-instr→satisfies-step {hc} pre s s' (declare-pub-input v) st mi pi prior-sat
  r@(r-declare-pub-input {v = wv} _) =
  -- s' = push-pi s wv, whose memory ≡ memory s, pis ≡ pis s ++ (wv ∷ []).
  let mem  = Preprocessed.memory s ; pis-s = Preprocessed.pis s
      rand = comm-rand-of pre
      pis' = pis-s ++ (wv ∷ [])
      w'   = mk-witness mem pis' rand
      newcls-st = single-instr-clauses-with-decl hc (SynthState.nr-wires st)
                    (SynthState.nr-declared-pi st) (declare-pub-input v)
      newcls'   = single-instr-clauses-with-decl hc (length mem)
                    (SynthState.nr-declared-pi st) (declare-pub-input v)
      newcls-eq : newcls-st ≡ newcls'
      newcls-eq = cong (λ k → single-instr-clauses-with-decl hc k
                                  (SynthState.nr-declared-pi st) (declare-pub-input v)) mi
      sat-new' = declare-pub-input-fwd {pre = pre} {s = s} {s' = s'} {v = v} {hc = hc}
                                        {d = SynthState.nr-declared-pi st} {rand = rand} pi r
      sat-new = subst (λ cls → satisfies-clauses cls w') (sym newcls-eq) sat-new'
      lifted-prior = satisfies-clauses-pis-extends {suffix = wv ∷ []}
                       (SynthState.clauses st) prior-sat
      -- mem unchanged so mem-inv straightforward.
      mi' : mem-inv s' (circuit-instr hc (declare-pub-input v) st)
      mi' = mi  -- nr-wires unchanged, mem unchanged
      -- pis grows by 1; nr-declared-pi grows by 1.
      -- length (pis ++ wv ∷ []) = suc (length pis)
      -- = suc (preamble-pi-count hc + nr-declared-pi st)
      -- = preamble-pi-count hc + suc (nr-declared-pi st)
      pi' : length (pis-s ++ (wv ∷ [])) ≡ preamble-pi-count hc + suc (SynthState.nr-declared-pi st)
      pi' = trans (length-++-1-fr pis-s wv)
                  (trans (cong suc pi) (sym (+-suc (preamble-pi-count hc) (SynthState.nr-declared-pi st))))
  in mi' , pi' ,
     satisfies-clauses-++ (SynthState.clauses st) _ lifted-prior sat-new
  where
    length-++-1-fr : ∀ (xs : List Fr) y → length (xs ++ (y ∷ [])) ≡ suc (length xs)
    length-++-1-fr []       y = refl
    length-++-1-fr (x ∷ xs) y = cong suc (length-++-1-fr xs y)

-- Sub-lemma 2: iteration of the per-step lemma along an `R-instrs` trace.
-- Yields satisfaction of *all* clauses accumulated by `circuit-instrs`
-- against the final state's assignment.  Straightforward induction on
-- the `R-instrs` derivation tree, calling `R-instr→satisfies-step` at
-- each `r-step`.
R-instrs→satisfies-clauses
  : ∀ {hc} (pre : ProofPreimage) (s₀ s : Preprocessed)
    (is : List Instruction) (st₀ : SynthState)
  → mem-inv s₀ st₀
  → pi-inv  hc s₀ st₀
  → satisfies-clauses (SynthState.clauses st₀)
      (mk-witness (Preprocessed.memory s₀)
                  (Preprocessed.pis    s₀)
                  (comm-rand-of pre))
  → R-instrs pre s₀ is s
  →   mem-inv s (circuit-instrs hc is st₀)
    × pi-inv  hc s (circuit-instrs hc is st₀)
    × satisfies-clauses
        (SynthState.clauses (circuit-instrs hc is st₀))
        (mk-witness (Preprocessed.memory s)
                    (Preprocessed.pis    s)
                    (comm-rand-of pre))
R-instrs→satisfies-clauses pre s₀ .s₀ [] st₀ mi pi sat r-done =
  mi , pi , sat
R-instrs→satisfies-clauses {hc} pre s₀ s (i ∷ is) st₀ mi pi sat (r-step {s₁ = s₁} r-head r-tail) =
  let step = R-instr→satisfies-step {hc = hc} pre s₀ s₁ i st₀ mi pi sat r-head
      mi₁  = proj₁ step
      pi₁  = proj₁ (proj₂ step)
      sat₁ = proj₂ (proj₂ step)
  in R-instrs→satisfies-clauses {hc = hc} pre s₁ s is
       (circuit-instr hc i st₀) mi₁ pi₁ sat₁ r-tail

------------------------------------------------------------------------
-- Top-level comm-commitment alignment.
--
-- If `do-communications-commitment src ≡ true`, then `R src pre s`
-- carries `comm-ok src pre s ≡ true`, i.e. the *operational*
-- commitment satisfies
--
--   pre.comm-commitment = just (c , r)
--   c ≡ transient-commit (pre.inputs ++ s.outputs) r
--
-- and `init-state` puts `c` at index 1 of `pis`.  The circuit's
-- `clause-comm-commitment cm-inputs out-wires` requires
--
--   pis[1] ≡ transient-commit (ivs ++ ovs) rv
--
-- where `ivs = lookup mem [0..num-inputs)` and
-- `ovs = lookup mem out-wires`.  Closing the gap needs three facts:
--
--   • `out-wires` (the indices recorded by `circuit-instr (output v)`)
--     evaluate via `mem-lookups` to exactly `Preprocessed.outputs s`;
--
--   • the wires `[0 .. num-inputs)` evaluate to `pre.inputs`
--     (consequence of `init-state-memory` + structure of `mem`);
--
--   • `transient-commit` and the in-circuit Poseidon are definitionally
--     the same canonical function (spec §5.4 trust boundary; already
--     baked in by `holds` using `transient-commit` directly).
--
-- Phase 4b will discharge the first two as auxiliary lemmas;
-- the third needs no proof obligation here.
------------------------------------------------------------------------

-- Helper alias: re-export `nat-range` from `Circuit` under the name
-- `input-wires` used by `inputs-lookup-init`.  They are identical
-- functions (definitionally equal).
input-wires : ℕ → List Index
input-wires = nat-range

-- Memory monotonicity for `mem-lookups` along R-instrs.  Discharged by
-- induction; each step's memory is a suffix extension of the prior.
mem-lookups-mono-R-instrs
  : ∀ (pre : ProofPreimage) (s s' : Preprocessed)
    (is : List Instruction) (xs : List Index) (vs : List Fr)
  → R-instrs pre s is s'
  → mem-lookups (Preprocessed.memory s)  xs ≡ just vs
  → mem-lookups (Preprocessed.memory s') xs ≡ just vs
mem-lookups-mono-R-instrs pre s .s [] xs vs r-done lookup-eq = lookup-eq
mem-lookups-mono-R-instrs pre s s' (i ∷ is) xs vs (r-step {s₁ = s₁} r-head r-tail) lookup-eq =
  let extn = mem-extends-R-instr r-head
      suf  = proj₁ extn
      eq   = proj₂ extn   -- mem s₁ ≡ mem s ++ suf
      lookup-s₁ : mem-lookups (Preprocessed.memory s₁) xs ≡ just vs
      lookup-s₁ = subst (λ m → mem-lookups m xs ≡ just vs)
                         (sym eq)
                         (mem-lookups-extends (Preprocessed.memory s) suf xs lookup-eq)
  in mem-lookups-mono-R-instrs pre s₁ s' is xs vs r-tail lookup-s₁

-- pi-lookup monotonicity along R-instrs.  Each step's `pis` is either
-- unchanged or extended (only `r-declare-pub-input` extends it).
pi-lookup-mono-R-instrs
  : ∀ (pre : ProofPreimage) (s s' : Preprocessed)
    (is : List Instruction) (idx : ℕ) (v : Fr)
  → R-instrs pre s is s'
  → pi-lookup (Preprocessed.pis s)  idx ≡ just v
  → pi-lookup (Preprocessed.pis s') idx ≡ just v
pi-lookup-mono-R-instrs pre s .s [] idx v r-done lk = lk
pi-lookup-mono-R-instrs pre s s' (i ∷ is) idx v
  (r-step {s₁ = s₁} r-head r-tail) lk =
  let extn = pis-extends-R-instr r-head
      suf  = proj₁ extn
      eq   = proj₂ extn   -- pis s₁ ≡ pis s ++ suf
      lk-s₁ : pi-lookup (Preprocessed.pis s₁) idx ≡ just v
      lk-s₁ = subst (λ p → pi-lookup p idx ≡ just v)
                     (sym eq)
                     (pi-lookup-extends (Preprocessed.pis s) suf idx lk)
  in pi-lookup-mono-R-instrs pre s₁ s' is idx v r-tail lk-s₁

------------------------------------------------------------------------
-- Section C.2.  Helpers for the top-level forward proof.
--
-- These bridge the per-step iteration result (`R-instrs→satisfies-clauses`)
-- with the top-level comm-commitment clause and the initial invariants.
------------------------------------------------------------------------

private

  -- mem-lookups distributes over snoc on the index list.
  mem-lookups-snoc : ∀ (mem : List Fr) (is : List Index) (i : Index) {vs v}
    → mem-lookups mem is ≡ just vs
    → mem-lookup mem i ≡ just v
    → mem-lookups mem (is ⊕ i) ≡ just (vs ⊕ v)
  mem-lookups-snoc mem [] i {vs} {v} lk lkv
    rewrite just-injective (sym lk) | lkv = refl
  mem-lookups-snoc mem (j ∷ js) i {vs} {v} lk lkv =
    aux (mem-lookup mem j)    refl
        (mem-lookups mem js)  refl
        lk
    where
      aux : ∀ (m : Maybe Fr) → mem-lookup mem j ≡ m
          → (ms : Maybe (List Fr)) → mem-lookups mem js ≡ ms
          → (m >>= λ v' → ms >>= λ vs' → just (v' ∷ vs')) ≡ just vs
          → mem-lookups mem ((j ∷ js) ⊕ i) ≡ just (vs ⊕ v)
      aux nothing   _    _          _    ()
      aux (just _)  _    nothing    _    ()
      aux (just w)  m-eq (just ws)  ms-eq refl
        rewrite m-eq | ms-eq
              | mem-lookups-snoc mem js i {ws} {v} ms-eq lkv
        = refl

  -- length-respecting decomposition of a non-empty list into snoc form.
  -- Used to enable snoc-induction over `nat-range`.
  suc-inj : ∀ {m k : ℕ} → suc m ≡ suc k → m ≡ k
  suc-inj refl = refl

  snoc-of-length : ∀ (xs : List Fr) (n : ℕ)
    → length xs ≡ suc n
    → Σ-syntax (List Fr) (λ xs' → Σ-syntax Fr (λ x →
        (length xs' ≡ n) × (xs ≡ xs' ⊕ x)))
  snoc-of-length []           n  ()
  snoc-of-length (x ∷ [])     zero    refl =
    [] , x , refl , refl
  snoc-of-length (x ∷ [])     (suc _) ()
  snoc-of-length (x ∷ y ∷ ys) zero    ()
  snoc-of-length (x ∷ y ∷ ys) (suc n) p =
    let rec = snoc-of-length (y ∷ ys) n (suc-inj p)
        xs' = proj₁ rec
        z   = proj₁ (proj₂ rec)
        q   = proj₁ (proj₂ (proj₂ rec))
        eq  = proj₂ (proj₂ (proj₂ rec))   -- y ∷ ys ≡ xs' ⊕ z
    in x ∷ xs' , z , cong suc q , cong (x ∷_) eq

  -- mem-lookup at exactly `length xs` in `xs ⊕ y` is `just y`.
  -- Used inductively to feed `mem-lookups-snoc`.
  mem-lookup-snoc-at-len : ∀ (xs : List Fr) (y : Fr)
    → mem-lookup (xs ⊕ y) (length xs) ≡ just y
  mem-lookup-snoc-at-len []       y = refl
  mem-lookup-snoc-at-len (x ∷ xs) y = mem-lookup-snoc-at-len xs y

  -- The wires `[0 .. length xs)` of `xs` look up to exactly `xs`.
  -- Proved by induction on `length xs`, decomposed via `snoc-of-length`.
  mem-lookups-nat-range-len : ∀ (n : ℕ) (xs : List Fr)
    → length xs ≡ n
    → mem-lookups xs (nat-range n) ≡ just xs
  mem-lookups-nat-range-len zero []       refl = refl
  mem-lookups-nat-range-len zero (_ ∷ _)  ()
  mem-lookups-nat-range-len (suc n) xs    p
    with snoc-of-length xs n p
  ... | xs' , y , len' , refl
    -- Goal: mem-lookups (xs' ⊕ y) (nat-range n ⊕ n) ≡ just (xs' ⊕ y)
    -- Use mem-lookups-nat-range-len n xs' len' (terminating: n < suc n).
    = mem-lookups-snoc (xs' ⊕ y) (nat-range n) n
        {vs = xs'} {v = y}
        (mem-lookups-extends xs' (y ∷ []) (nat-range n)
           {vs = xs'}
           (mem-lookups-nat-range-len n xs' len'))
        (subst (λ k → mem-lookup (xs' ⊕ y) k ≡ just y) len'
               (mem-lookup-snoc-at-len xs' y))

  -- Specialised: when `length xs ≡ n`, the wires `[0 .. n)` look up to `xs`.
  mem-lookups-nat-range : ∀ (xs : List Fr)
    → mem-lookups xs (nat-range (length xs)) ≡ just xs
  mem-lookups-nat-range xs = mem-lookups-nat-range-len (length xs) xs refl

  -- `init-state-memory` (re-stated locally).  Properties.agda's version is
  -- in a `private` block and not importable.  This is a faithful copy.
  init-state-memory' : ∀ src pre s₀
    → init-state src pre ≡ just s₀
    → Preprocessed.memory s₀ ≡ ProofPreimage.inputs pre
  init-state-memory' src pre s₀ eq
    with length (ProofPreimage.inputs pre) Data.Nat.≡ᵇ IrSource.num-inputs src
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _     | _      with eq
  ...   | ()
  init-state-memory' src pre s₀ eq
       | true  | false | _      = sym (cong Preprocessed.memory (just-injective eq))
  init-state-memory' src pre s₀ eq
       | true  | true  | just _ = sym (cong Preprocessed.memory (just-injective eq))
  init-state-memory' src pre s₀ eq
       | true  | true  | nothing with eq
  ...   | ()

  -- WF1 enforcement extracted from `init-state ≡ just s₀`: the preimage's
  -- inputs have exactly `num-inputs src` cells.  (Init-state checks this
  -- via `≡ᵇ`; the equation lets us convert the boolean check to a
  -- propositional equality.)
  init-state-inputs-length : ∀ src pre s₀
    → init-state src pre ≡ just s₀
    → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
  init-state-inputs-length src pre s₀ eq
    with length (ProofPreimage.inputs pre) Data.Nat.≡ᵇ IrSource.num-inputs src
       in b-eq
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _     | _      with eq
  ...   | ()
  init-state-inputs-length src pre s₀ eq
       | true  | false | _      =
         Data.Nat.Properties.≡ᵇ⇒≡ _ _ (Data.Bool.Properties.T-≡ .Function.Bundles.Equivalence.from b-eq)
  init-state-inputs-length src pre s₀ eq
       | true  | true  | just _ =
         Data.Nat.Properties.≡ᵇ⇒≡ _ _ (Data.Bool.Properties.T-≡ .Function.Bundles.Equivalence.from b-eq)
  init-state-inputs-length src pre s₀ eq
       | true  | true  | nothing with eq
  ...   | ()

  -- Initial `pis`: `[binding-input]` (hc=false) or `[binding-input, c]` (hc=true).
  init-state-pis-length : ∀ src pre s₀
    → init-state src pre ≡ just s₀
    → length (Preprocessed.pis s₀)
       ≡ preamble-pi-count (IrSource.do-communications-commitment src)
  init-state-pis-length src pre s₀ eq
    with length (ProofPreimage.inputs pre) Data.Nat.≡ᵇ IrSource.num-inputs src
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _     | _      with eq
  ...   | ()
  init-state-pis-length src pre s₀ eq
       | true  | false | _      =
         cong length (sym (cong Preprocessed.pis (just-injective eq)))
  init-state-pis-length src pre s₀ eq
       | true  | true  | just _ =
         cong length (sym (cong Preprocessed.pis (just-injective eq)))
  init-state-pis-length src pre s₀ eq
       | true  | true  | nothing with eq
  ...   | ()

  -- Outputs are empty at `init-state`.
  init-state-outputs : ∀ src pre s₀
    → init-state src pre ≡ just s₀
    → Preprocessed.outputs s₀ ≡ []
  init-state-outputs src pre s₀ eq
    with length (ProofPreimage.inputs pre) Data.Nat.≡ᵇ IrSource.num-inputs src
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
  ... | false | _     | _      with eq
  ...   | ()
  init-state-outputs src pre s₀ eq
       | true  | false | _      =
         sym (cong Preprocessed.outputs (just-injective eq))
  init-state-outputs src pre s₀ eq
       | true  | true  | just _ =
         sym (cong Preprocessed.outputs (just-injective eq))
  init-state-outputs src pre s₀ eq
       | true  | true  | nothing with eq
  ...   | ()

  -- For each R-instr step, the outputs grow by 0 (for non-output instructions)
  -- or by 1 (for output instructions).  We need a uniform lift of the
  -- IH from `s` to `s₁` when output-wires (and outputs) don't change.

  -- Specialised step lemma for the "non-output" cases.  The caller
  -- discharges `out-eq` (definitional for all but r-output) and uses the
  -- fact that, for non-output instructions, `circuit-instr` doesn't
  -- modify `output-wires` (so `output-wires (circuit-instr ...) ≡
  -- output-wires st` reduces definitionally to `refl`).
  --
  -- Both `i` and `st` are explicit so reduction of `circuit-instr` at the
  -- call site triggers normalisation of `output-wires (circuit-instr …)`.
  output-wires-non-output-step
    : ∀ {pre s s₁} (i : Instruction) (st : SynthState)
    → R-instr pre s i s₁
    → Preprocessed.outputs s₁ ≡ Preprocessed.outputs s
    → mem-lookups (Preprocessed.memory s) (SynthState.output-wires st)
        ≡ just (Preprocessed.outputs s)
    → mem-lookups (Preprocessed.memory s₁) (SynthState.output-wires st)
      ≡ just (Preprocessed.outputs s₁)
  output-wires-non-output-step {pre} {s} {s₁} i st r-head out-eq H =
    let extn = mem-extends-R-instr r-head
        suf  = proj₁ extn
        mem-eq : Preprocessed.memory s₁ ≡ Preprocessed.memory s ++ suf
        mem-eq = proj₂ extn
    in subst (λ m → mem-lookups m (SynthState.output-wires st)
                      ≡ just (Preprocessed.outputs s₁))
              (sym mem-eq)
              (subst (λ ov → mem-lookups (Preprocessed.memory s ++ suf)
                               (SynthState.output-wires st)
                               ≡ just ov)
                      (sym out-eq)
                      (mem-lookups-extends (Preprocessed.memory s) suf
                         (SynthState.output-wires st) H))

-- The generalized version of `output-wires-coincide`, allowing arbitrary
-- starting `output-wires st₀`.
output-wires-coincide-gen
  : ∀ {hc} (pre : ProofPreimage) (s₀ s : Preprocessed)
    (is : List Instruction) (st₀ : SynthState)
  → R-instrs pre s₀ is s
  → mem-lookups (Preprocessed.memory s₀) (SynthState.output-wires st₀)
      ≡ just (Preprocessed.outputs s₀)
  → mem-lookups (Preprocessed.memory s)
      (SynthState.output-wires (circuit-instrs hc is st₀))
    ≡ just (Preprocessed.outputs s)
output-wires-coincide-gen pre s₀ .s₀ [] st₀ r-done H = H
output-wires-coincide-gen {hc} pre s₀ s (i ∷ is) st₀
  (r-step {s₁ = s₁} r-head r-tail) H =
  output-wires-coincide-gen {hc} pre s₁ s is (circuit-instr hc i st₀) r-tail
    (step-IH i r-head)
  where
    -- For each non-output instruction, `circuit-instr hc i st₀`'s
    -- `output-wires` field reduces to `SynthState.output-wires st₀`
    -- definitionally; the helper's result is the IH at `s₁`.
    step-IH : ∀ (i : Instruction) {s₁} → R-instr pre s₀ i s₁
      → mem-lookups (Preprocessed.memory s₁)
          (SynthState.output-wires (circuit-instr hc i st₀))
        ≡ just (Preprocessed.outputs s₁)
    step-IH (assert cond)            r@(r-assert _)          =
      output-wires-non-output-step (assert cond) st₀ r refl H
    step-IH (cond-select b a c)      r@(r-cond-select _ _ _) =
      output-wires-non-output-step (cond-select b a c) st₀ r refl H
    step-IH (constrain-bits v n)     r@(r-constrain-bits _ _) =
      output-wires-non-output-step (constrain-bits v n) st₀ r refl H
    step-IH (constrain-eq a b)       r@(r-constrain-eq _ _ _) =
      output-wires-non-output-step (constrain-eq a b) st₀ r refl H
    step-IH (constrain-to-boolean v) r@(r-constrain-to-boolean _) =
      output-wires-non-output-step (constrain-to-boolean v) st₀ r refl H
    step-IH (copy v)                 r@(r-copy _)            =
      output-wires-non-output-step (copy v) st₀ r refl H
    step-IH (declare-pub-input v)    r@(r-declare-pub-input _) =
      output-wires-non-output-step (declare-pub-input v) st₀ r refl H
    step-IH (pi-skip g n)            r@(r-pi-skip-active _ _) =
      output-wires-non-output-step (pi-skip g n) st₀ r refl H
    step-IH (pi-skip g n)            r@(r-pi-skip-inactive _) =
      output-wires-non-output-step (pi-skip g n) st₀ r refl H
    step-IH (ec-add a-x a-y b-x b-y) r@(r-ec-add _ _ _ _ _)  =
      output-wires-non-output-step (ec-add a-x a-y b-x b-y) st₀ r refl H
    step-IH (ec-mul a-x a-y sc)      r@(r-ec-mul _ _ _ _)    =
      output-wires-non-output-step (ec-mul a-x a-y sc) st₀ r refl H
    step-IH (ec-mul-generator sc)    r@(r-ec-mul-generator _ _) =
      output-wires-non-output-step (ec-mul-generator sc) st₀ r refl H
    step-IH (hash-to-curve inputs)   r@(r-hash-to-curve _ _) =
      output-wires-non-output-step (hash-to-curve inputs) st₀ r refl H
    step-IH (load-imm imm)           r@r-load-imm            =
      output-wires-non-output-step (load-imm imm) st₀ r refl H
    step-IH (div-mod-power-of-two v bits) r@(r-div-mod-power-of-two _) =
      output-wires-non-output-step (div-mod-power-of-two v bits) st₀ r refl H
    step-IH (reconstitute-field d m bits) r@(r-reconstitute-field _ _ _) =
      output-wires-non-output-step (reconstitute-field d m bits) st₀ r refl H
    -- output v: the synth state pushes `v` to output-wires, the operational
    -- state pushes its value to outputs.  Combine via mem-lookups-snoc.
    step-IH (output var) (r-output {v = v} la) =
      -- circuit-instr _ (output var) st₀ = record st₀ { output-wires = ow ⊕ var }
      -- s₁ = push-output s₀ v, memory unchanged, outputs s₁ = outputs s₀ ⊕ v.
      mem-lookups-snoc (Preprocessed.memory s₀)
                        (SynthState.output-wires st₀) var
                        {vs = Preprocessed.outputs s₀} {v = v}
                        H la
    step-IH (transient-hash inputs)  r@(r-transient-hash _)  =
      output-wires-non-output-step (transient-hash inputs) st₀ r refl H
    step-IH (persistent-hash al inputs) r@(r-persistent-hash _ _) =
      output-wires-non-output-step (persistent-hash al inputs) st₀ r refl H
    step-IH (test-eq a b)            r@(r-test-eq _ _)       =
      output-wires-non-output-step (test-eq a b) st₀ r refl H
    step-IH (add a b)                r@(r-add _ _)           =
      output-wires-non-output-step (add a b) st₀ r refl H
    step-IH (mul a b)                r@(r-mul _ _)           =
      output-wires-non-output-step (mul a b) st₀ r refl H
    step-IH (neg a)                  r@(r-neg _)             =
      output-wires-non-output-step (neg a) st₀ r refl H
    step-IH (not a)                  r@(r-not _)             =
      output-wires-non-output-step (not a) st₀ r refl H
    step-IH (less-than a b bits)     r@(r-less-than _ _ _)   =
      output-wires-non-output-step (less-than a b bits) st₀ r refl H
    step-IH (public-input nothing)   r@(r-public-input-inactive _) =
      output-wires-non-output-step (public-input nothing) st₀ r refl H
    step-IH (public-input nothing)   r@(r-public-input-active _ cp) =
      output-wires-non-output-step (public-input nothing) st₀ r
        (consume-pub-out-outputs s₀ cp) H
      where
        consume-pub-out-outputs : ∀ s {v s'}
          → consume-pub-out s ≡ just (v , s')
          → Preprocessed.outputs (push-mem s' v) ≡ Preprocessed.outputs s
        consume-pub-out-outputs s eq with Preprocessed.pub-out-rem s | eq
        ... | []    | ()
        ... | _ ∷ _ | p =
          sym (cong Preprocessed.outputs (cong proj₂ (just-injective p)))
    step-IH (public-input (just g))  r@(r-public-input-inactive _) =
      output-wires-non-output-step (public-input (just g)) st₀ r refl H
    step-IH (public-input (just g))  r@(r-public-input-active _ cp) =
      output-wires-non-output-step (public-input (just g)) st₀ r
        (consume-pub-out-outputs' s₀ cp) H
      where
        consume-pub-out-outputs' : ∀ s {v s'}
          → consume-pub-out s ≡ just (v , s')
          → Preprocessed.outputs (push-mem s' v) ≡ Preprocessed.outputs s
        consume-pub-out-outputs' s eq with Preprocessed.pub-out-rem s | eq
        ... | []    | ()
        ... | _ ∷ _ | p =
          sym (cong Preprocessed.outputs (cong proj₂ (just-injective p)))
    step-IH (private-input nothing)  r@(r-private-input-inactive _) =
      output-wires-non-output-step (private-input nothing) st₀ r refl H
    step-IH (private-input nothing)  r@(r-private-input-active _ cp) =
      output-wires-non-output-step (private-input nothing) st₀ r
        (consume-priv-outputs s₀ cp) H
      where
        consume-priv-outputs : ∀ s {v s'}
          → consume-priv s ≡ just (v , s')
          → Preprocessed.outputs (push-mem s' v) ≡ Preprocessed.outputs s
        consume-priv-outputs s eq with Preprocessed.priv-rem s | eq
        ... | []    | ()
        ... | _ ∷ _ | p =
          sym (cong Preprocessed.outputs (cong proj₂ (just-injective p)))
    step-IH (private-input (just g)) r@(r-private-input-inactive _) =
      output-wires-non-output-step (private-input (just g)) st₀ r refl H
    step-IH (private-input (just g)) r@(r-private-input-active _ cp) =
      output-wires-non-output-step (private-input (just g)) st₀ r
        (consume-priv-outputs' s₀ cp) H
      where
        consume-priv-outputs' : ∀ s {v s'}
          → consume-priv s ≡ just (v , s')
          → Preprocessed.outputs (push-mem s' v) ≡ Preprocessed.outputs s
        consume-priv-outputs' s eq with Preprocessed.priv-rem s | eq
        ... | []    | ()
        ... | _ ∷ _ | p =
          sym (cong Preprocessed.outputs (cong proj₂ (just-injective p)))

-- Top-level specialisation: when synth state starts with no recorded
-- output wires, the looked-up output wires match the operational outputs.
output-wires-coincide
  : ∀ {hc} (pre : ProofPreimage) (s₀ s : Preprocessed)
    (is : List Instruction) (st₀ : SynthState)
  → R-instrs pre s₀ is s
  → SynthState.output-wires st₀ ≡ []
  → Preprocessed.outputs s₀ ≡ []
  → mem-lookups (Preprocessed.memory s)
      (SynthState.output-wires (circuit-instrs hc is st₀))
    ≡ just (Preprocessed.outputs s)
output-wires-coincide {hc} pre s₀ s is st₀ Rs ow-empty out-empty =
  output-wires-coincide-gen {hc} pre s₀ s is st₀ Rs
    (subst (λ ows → mem-lookups (Preprocessed.memory s₀) ows
                      ≡ just (Preprocessed.outputs s₀))
            (sym ow-empty)
            (subst (λ os → mem-lookups (Preprocessed.memory s₀) [] ≡ just os)
                    (sym out-empty)
                    refl))

-- Discharged: the wires `[0 .. n)` of the initial memory look up to
-- exactly `inputs pre`.  Uses `mem-lookups-nat-range` + `init-state-memory'`
-- + the WF1 length enforcement extracted by `init-state-inputs-length`.
inputs-lookup-init
  : ∀ (src : IrSource) (pre : ProofPreimage) (s₀ : Preprocessed)
  → init-state src pre ≡ just s₀
  → mem-lookups (Preprocessed.memory s₀) (input-wires (IrSource.num-inputs src))
    ≡ just (ProofPreimage.inputs pre)
inputs-lookup-init src pre s₀ eq =
  let mem≡       = init-state-memory' src pre s₀ eq
      len-eq     = init-state-inputs-length src pre s₀ eq  -- length inputs ≡ num-inputs
      -- Step 1: mem-lookups (inputs pre) (nat-range (length (inputs pre))) ≡ just (inputs pre)
      lk : mem-lookups (ProofPreimage.inputs pre)
                       (nat-range (length (ProofPreimage.inputs pre)))
           ≡ just (ProofPreimage.inputs pre)
      lk = mem-lookups-nat-range (ProofPreimage.inputs pre)
      -- Step 2: rewrite (length inputs) to (num-inputs src) via len-eq.
      lk' : mem-lookups (ProofPreimage.inputs pre)
                        (nat-range (IrSource.num-inputs src))
            ≡ just (ProofPreimage.inputs pre)
      lk' = subst (λ n → mem-lookups (ProofPreimage.inputs pre) (nat-range n)
                          ≡ just (ProofPreimage.inputs pre))
                   len-eq lk
      -- Step 3: rewrite (inputs pre) to (memory s₀) via mem≡.
  in subst (λ m → mem-lookups m (nat-range (IrSource.num-inputs src))
                    ≡ just (ProofPreimage.inputs pre))
            (sym mem≡) lk'

------------------------------------------------------------------------
-- Top-level forward.
--
-- Phase 4b status: DISCHARGED (no postulates).  The proof decomposes
-- `R src pre s` into its `init-eq`, body trace `Rs`, transcript-
-- consumption, and comm-ok components, runs `R-instrs→satisfies-clauses`
-- to discharge the bulk of the clauses, and glues in the top-level
-- `clause-comm-commitment` (when `has-comm = true`).
--
-- Resolved structural issues:
--
--   • Spec amendment: `Maybe-shape false _` weakened to ⊤ (in
--     `Circuit.agda`), allowing spurious comm-rand when has-comm=false.
--
--   • Spec amendment: `init-state` enforces WF1 (length-of-inputs
--     matches num-inputs) in `Semantics.agda`, giving the proof here
--     the missing length match.
------------------------------------------------------------------------

-- Helper: from `init-state src pre ≡ just s₀` with `hc = true` and
-- `comm-commitment pre ≡ just (c, r)`, the initial pis has `c` at index 1.
private
  init-state-pi-1 : ∀ src pre s₀ c r
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ just (c , r)
    → init-state src pre ≡ just s₀
    → pi-lookup (Preprocessed.pis s₀) 1 ≡ just c
  init-state-pi-1 src pre s₀ c r hc-true cc-just eq
    with length (ProofPreimage.inputs pre) Data.Nat.≡ᵇ IrSource.num-inputs src
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
       | hc-true | cc-just
  ... | false | _     | _      | _     | _    with eq
  ...   | ()
  init-state-pi-1 src pre s₀ c r hc-true cc-just eq
       | true  | false | _     | () | _
  init-state-pi-1 src pre s₀ c r hc-true cc-just eq
       | true  | true | just .(c , r) | _ | refl =
         -- s₀ = mk-state inputs [binding-input ∷ c ∷ []] ...
         sym (cong (λ s → pi-lookup (Preprocessed.pis s) 1) (just-injective eq))
  init-state-pi-1 src pre s₀ c r hc-true cc-just eq
       | true  | true | nothing | _ | ()

-- Local `satisfies-clauses-++` (the private version is in the private block).
private
  sats-++ : ∀ {w} (xs ys : List Clause)
    → satisfies-clauses xs w
    → satisfies-clauses ys w
    → satisfies-clauses (xs ++ ys) w
  sats-++ []       _  _            sy = sy
  sats-++ (x ∷ xs) ys (hx , sxs) sy =
    hx , sats-++ xs ys sxs sy

-- Forward direction, hc=false branch.
private
  circuit-faithful-fwd-false
    : ∀ (src : IrSource) (pre : ProofPreimage) (s s₀ : Preprocessed)
    → IrSource.do-communications-commitment src ≡ false
    → init-state src pre ≡ just s₀
    → R-instrs pre s₀ (IrSource.instructions src) s
    → satisfies (circuit src) (witness-of s pre)
  circuit-faithful-fwd-false src pre s s₀ hc-false init-eq Rs =
    mk-sat pi-length-eq rand-shape-eq clauses-ok
    where
      n  = IrSource.num-inputs src
      st₀ : SynthState
      st₀ = mk-synth n [] 0 []
      instrs = IrSource.instructions src
      mem≡    = init-state-memory' src pre s₀ init-eq
      len-eq  = init-state-inputs-length src pre s₀ init-eq
      mi₀ : SynthState.nr-wires st₀ ≡ length (Preprocessed.memory s₀)
      mi₀ = sym (trans (cong length mem≡) len-eq)
      -- pi₀: length (pis s₀) ≡ preamble + nr-declared-pi st₀.
      -- preamble false = 1, nr-declared-pi st₀ = 0.
      pi₀-pre : length (Preprocessed.pis s₀)
                  ≡ preamble-pi-count (IrSource.do-communications-commitment src)
      pi₀-pre = init-state-pis-length src pre s₀ init-eq
      pi₀ : length (Preprocessed.pis s₀)
              ≡ preamble-pi-count false + SynthState.nr-declared-pi st₀
      pi₀ = subst (λ b → length (Preprocessed.pis s₀) ≡ preamble-pi-count b + 0)
                   hc-false
                   (trans pi₀-pre
                          (sym (+-identityʳ (preamble-pi-count
                                  (IrSource.do-communications-commitment src)))))
      result = R-instrs→satisfies-clauses {hc = false} pre s₀ s instrs st₀
                 mi₀ pi₀ tt Rs
      pi-end  = proj₁ (proj₂ result)
      sat-end = proj₂ (proj₂ result)
      -- Now we need to transport pi-end and sat-end through the
      -- (currently-abstract) hc.  The `Circuit.pi-len (circuit src)` and
      -- `Circuit.clauses (circuit src)` both depend on hc; using `hc-false`
      -- we substitute.
      circuit-eq : circuit src ≡
        mk-circuit
          (SynthState.nr-wires (circuit-instrs false instrs st₀))
          (SynthState.clauses (circuit-instrs false instrs st₀))
          (1 + SynthState.nr-declared-pi (circuit-instrs false instrs st₀))
          false
      circuit-eq = circuit-instantiate-false hc-false
        where
          -- Substitute `hc = false` into `circuit src`'s definition.
          -- The `if false then ... else cls` reduces to `cls`,
          -- `preamble-pi-count false = 1`, so we get the matching record.
          circuit-instantiate-false :
            IrSource.do-communications-commitment src ≡ false
            → circuit src ≡
              mk-circuit
                (SynthState.nr-wires (circuit-instrs false instrs st₀))
                (SynthState.clauses (circuit-instrs false instrs st₀))
                (1 + SynthState.nr-declared-pi (circuit-instrs false instrs st₀))
                false
          circuit-instantiate-false refl = refl
      pi-length-eq : length (Preprocessed.pis s) ≡ Circuit.pi-len (circuit src)
      pi-length-eq = trans pi-end (cong Circuit.pi-len (sym circuit-eq))
      rand-shape-eq : Maybe-shape (Circuit.has-comm (circuit src))
                                   (Witness.comm-rand (witness-of s pre))
      rand-shape-eq =
        subst (λ c → Maybe-shape (Circuit.has-comm c) (comm-rand-of pre))
              (sym circuit-eq) tt
      clauses-ok : satisfies-clauses (Circuit.clauses (circuit src))
                                       (witness-of s pre)
      clauses-ok = subst (λ c → satisfies-clauses (Circuit.clauses c)
                                                    (witness-of s pre))
                         (sym circuit-eq) sat-end

-- Forward direction, hc=true branch with comm-commitment = just (c, r).
private
  circuit-faithful-fwd-true
    : ∀ (src : IrSource) (pre : ProofPreimage) (s s₀ : Preprocessed) c r
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ just (c , r)
    → init-state src pre ≡ just s₀
    → R-instrs pre s₀ (IrSource.instructions src) s
    → (c ≡ᶠ? transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r) ≡ true
    → satisfies (circuit src) (witness-of s pre)
  circuit-faithful-fwd-true src pre s s₀ c r hc-true cc-just init-eq Rs co-eq =
    mk-sat pi-length-eq rand-shape-eq clauses-ok
    where
      n  = IrSource.num-inputs src
      st₀ : SynthState
      st₀ = mk-synth n [] 0 []
      instrs = IrSource.instructions src
      mem≡    = init-state-memory' src pre s₀ init-eq
      len-eq  = init-state-inputs-length src pre s₀ init-eq
      mi₀ : SynthState.nr-wires st₀ ≡ length (Preprocessed.memory s₀)
      mi₀ = sym (trans (cong length mem≡) len-eq)
      pi₀-pre : length (Preprocessed.pis s₀)
                  ≡ preamble-pi-count (IrSource.do-communications-commitment src)
      pi₀-pre = init-state-pis-length src pre s₀ init-eq
      pi₀ : length (Preprocessed.pis s₀)
              ≡ preamble-pi-count true + SynthState.nr-declared-pi st₀
      pi₀ = subst (λ b → length (Preprocessed.pis s₀) ≡ preamble-pi-count b + 0)
                   hc-true
                   (trans pi₀-pre
                          (sym (+-identityʳ (preamble-pi-count
                                  (IrSource.do-communications-commitment src)))))
      result = R-instrs→satisfies-clauses {hc = true} pre s₀ s instrs st₀
                 mi₀ pi₀ tt Rs
      pi-end  = proj₁ (proj₂ result)
      sat-end = proj₂ (proj₂ result)
      st-end  = circuit-instrs true instrs st₀
      cm-inputs = nat-range n
      out-wires = SynthState.output-wires st-end
      -- The comm-clause witness:
      ivs-lookup : mem-lookups (Preprocessed.memory s) cm-inputs
                    ≡ just (ProofPreimage.inputs pre)
      ivs-lookup = mem-lookups-mono-R-instrs pre s₀ s instrs cm-inputs
                     (ProofPreimage.inputs pre) Rs
                     (inputs-lookup-init src pre s₀ init-eq)
      ovs-lookup : mem-lookups (Preprocessed.memory s) out-wires
                    ≡ just (Preprocessed.outputs s)
      ovs-lookup = output-wires-coincide {hc = true} pre s₀ s instrs st₀ Rs
                     refl
                     (init-state-outputs src pre s₀ init-eq)
      pi-1-init : pi-lookup (Preprocessed.pis s₀) 1 ≡ just c
      pi-1-init = init-state-pi-1 src pre s₀ c r hc-true cc-just init-eq
      pi-1-final : pi-lookup (Preprocessed.pis s) 1 ≡ just c
      pi-1-final = pi-lookup-mono-R-instrs pre s₀ s instrs 1 c Rs pi-1-init
      c≡tc : c ≡ transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r
      c≡tc = ≡ᶠ?-true co-eq
      w = witness-of s pre
      rand≡ : Witness.comm-rand w ≡ just r
      rand≡ = comm-rand-of-just-eq pre c r cc-just
        where
          -- `comm-rand-of pre` reduces to `just r` when
          -- `comm-commitment pre ≡ just (c, r)`.  We have to do
          -- the case-split explicitly because `comm-rand-of` is
          -- defined by `with`.
          comm-rand-of-just-eq : ∀ pre c r
            → ProofPreimage.comm-commitment pre ≡ just (c , r)
            → comm-rand-of pre ≡ just r
          comm-rand-of-just-eq pre c r eq
            with ProofPreimage.comm-commitment pre | eq
          ... | just .(c , r) | refl = refl
      holds-comm : holds w (clause-comm-commitment cm-inputs out-wires)
      holds-comm =
        ProofPreimage.inputs pre
        , Preprocessed.outputs s
        , r
        , c
        , ivs-lookup
        , ovs-lookup
        , rand≡
        , pi-1-final
        , c≡tc
      body-clauses = SynthState.clauses st-end
      -- circuit src reduces, under hc-true, to its hc=true shape.
      circuit-eq : circuit src ≡
        mk-circuit
          (SynthState.nr-wires st-end)
          (body-clauses ⊕ clause-comm-commitment cm-inputs out-wires)
          (2 + SynthState.nr-declared-pi st-end)
          true
      circuit-eq = circuit-instantiate-true hc-true
        where
          circuit-instantiate-true :
            IrSource.do-communications-commitment src ≡ true
            → circuit src ≡
              mk-circuit
                (SynthState.nr-wires st-end)
                (body-clauses ⊕ clause-comm-commitment cm-inputs out-wires)
                (2 + SynthState.nr-declared-pi st-end)
                true
          circuit-instantiate-true refl = refl
      pi-length-eq : length (Preprocessed.pis s) ≡ Circuit.pi-len (circuit src)
      pi-length-eq = trans pi-end (cong Circuit.pi-len (sym circuit-eq))
      rand-shape-eq : Maybe-shape (Circuit.has-comm (circuit src))
                                   (Witness.comm-rand w)
      rand-shape-eq =
        subst (λ cc → Maybe-shape (Circuit.has-comm cc) (Witness.comm-rand w))
              (sym circuit-eq)
              (subst (λ rd → Maybe-shape true rd) (sym rand≡) tt)
      clauses-ok-body++ : satisfies-clauses
        (body-clauses ⊕ clause-comm-commitment cm-inputs out-wires) w
      clauses-ok-body++ = sats-++ body-clauses
        (clause-comm-commitment cm-inputs out-wires ∷ [])
        sat-end
        (holds-comm , tt)
      clauses-ok : satisfies-clauses (Circuit.clauses (circuit src)) w
      clauses-ok = subst (λ c' → satisfies-clauses (Circuit.clauses c') w)
                          (sym circuit-eq) clauses-ok-body++

-- Reconstitute the comm-ok equality at the hc=true / just (c,r) branch.
private
  extract-comm-ok-eq : ∀ src pre s c r
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ just (c , r)
    → comm-ok src pre s ≡ true
    → (c ≡ᶠ? transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r) ≡ true
  extract-comm-ok-eq src pre s c r hc-eq cc-eq co
    with IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
       | hc-eq | cc-eq
  ... | true | just .(c , r) | _ | refl = co

  -- comm-ok with hc=true and comm-commitment=nothing is impossible.
  no-comm-contra : ∀ src pre s
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ nothing
    → comm-ok src pre s ≡ true
    → ⊥
  no-comm-contra src pre s hc-eq cc-eq co
    with IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
       | hc-eq | cc-eq
  ... | true | nothing | _ | _ with co
  ...   | ()

  -- Discriminate on Bool (for use after extracting `do-comm src`).
  bool-cases : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
  bool-cases true  = inj₁ refl
  bool-cases false = inj₂ refl

  -- Discriminate on Maybe (Fr × Fr).
  maybe-cases : (m : Maybe (Fr × Fr))
    → (m ≡ nothing) ⊎ (Σ-syntax Fr λ c → Σ-syntax Fr λ r → m ≡ just (c , r))
  maybe-cases nothing         = inj₁ refl
  maybe-cases (just (c , r))  = inj₂ (c , r , refl)

-- The top-level forward lemma.
circuit-faithful-fwd
  : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
  → producer-safe src ≡ true
  → R src pre s
  → satisfies (circuit src) (witness-of s pre)
circuit-faithful-fwd src pre s _ps (s₀ , init-eq , Rs , _tc , co)
  with bool-cases (IrSource.do-communications-commitment src)
... | inj₂ hc-false =
  circuit-faithful-fwd-false src pre s s₀ hc-false init-eq Rs
... | inj₁ hc-true with maybe-cases (ProofPreimage.comm-commitment pre)
...   | inj₁ cc-none =
        ⊥-elim (no-comm-contra src pre s hc-true cc-none co)
...   | inj₂ (c , r , cc-just) =
        circuit-faithful-fwd-true src pre s s₀ c r
          hc-true cc-just init-eq Rs
          (extract-comm-ok-eq src pre s c r hc-true cc-just co)

------------------------------------------------------------------------
-- Section C.5.  Wire-discipline soundness.
--
-- The backward dispatcher needs, for each per-instruction case, a bound
-- `operand < length (memory s)` to pull pre-state lookups back from
-- post-state lookups in the satisfies-clauses witness.  The producer
-- obligation `wire-disc` (Obligations.agda) supplies this as a static
-- linear scan: each instruction's operand indices are checked against
-- the current wire count, which is `length (memory s)` on the
-- operational side under `mem-inv`.
--
-- `wire-disc-sound` lifts `wire-disc src ≡ true` to a `Wire-Trace`
-- predicate threaded along the instruction list; pairing this with
-- `mem-inv` then gives per-step `wire-check instr (length mem) ≡ true`,
-- which `lookup-shrink` from CircuitFaithfulness then converts into the
-- needed pre-state lookups.
------------------------------------------------------------------------

private

  -- Reconstruct a Wire-Trace from the Bool scan.
  wire-scan→trace : ∀ is n {final}
    → wire-scan is n ≡ just final
    → Wire-Trace is n final
  wire-scan→trace []       n refl = wire-done
  wire-scan→trace (i ∷ is) n eq
    with wire-step i n in step-eq
  ... | just n' = wire-cons step-eq (wire-scan→trace is n' eq)

  -- Bool → Wire-Trace witness extractor (mirrors O2-bool→Runs).
  wire-bool→trace : ∀ {src} → wire-disc src ≡ true
    → ∃-syntax λ final →
        Wire-Trace (IrSource.instructions src) (IrSource.num-inputs src) final
  wire-bool→trace {src} eq
    with wire-scan (IrSource.instructions src) (IrSource.num-inputs src)
         in scan-eq
  ... | just final =
        final , wire-scan→trace (IrSource.instructions src)
                                 (IrSource.num-inputs src) scan-eq

  -- Soundness: `producer-safe` gives a Wire-Trace.
  wire-disc-sound : ∀ {src} → producer-safe src ≡ true
    → ∃-syntax λ final →
        Wire-Trace (IrSource.instructions src) (IrSource.num-inputs src) final
  wire-disc-sound {src} ps = wire-bool→trace {src} (producer-safe-wire-disc {src} ps)

  -- Per-step extractor: a Wire-Trace covering `instr ∷ rest` gives
  -- both the `wire-check instr n ≡ true` premise and the residual
  -- trace at the bumped counter.
  --
  -- Implementation: use a generalised auxiliary so the `with` on
  -- `wire-check instr n` reduces `wire-step instr n` and refines the
  -- type of the just-equation simultaneously.
  wire-trace-head-aux : ∀ {is final} (instr : Instruction) (n : ℕ)
                          (b : Bool) (_ : wire-check instr n ≡ b) {n''}
    → (if b then just (n + Δmem instr) else nothing) ≡ just n''
    → Wire-Trace is n'' final
    → wire-check instr n ≡ true
        × Wire-Trace is (n + Δmem instr) final
  wire-trace-head-aux instr n true  ch-eq eq t =
    ch-eq , subst (λ k → Wire-Trace _ k _) (sym (just-injective eq)) t
  wire-trace-head-aux instr n false ch-eq () _

  -- Bridge: `wire-step instr n` reduces (definitionally) to the
  -- `if (wire-check ...) then ... else ...` form, by the `with`-style
  -- definition of `wire-step`.  Use a small lemma to lift this.
  wire-step-defn : ∀ instr n
    → wire-step instr n ≡ (if wire-check instr n then just (n + Δmem instr) else nothing)
  wire-step-defn instr n with wire-check instr n
  ... | true  = refl
  ... | false = refl

  wire-trace-head : ∀ {instr is n final}
    → Wire-Trace (instr ∷ is) n final
    → wire-check instr n ≡ true
        × Wire-Trace is (n + Δmem instr) final
  wire-trace-head {instr} {is} {n} (wire-cons {n' = n'} step-eq tail) =
    wire-trace-head-aux instr n (wire-check instr n) refl
      (trans (sym (wire-step-defn instr n)) step-eq) tail

  ------------------------------------------------------------------------
  -- H7 — O2 / O3 trace head extraction.
  --
  -- Analogues of `wire-trace-head`.  From `O2-Trace (i ∷ is) acc final`
  -- extract the step's `O2-step i acc ≡ just acc'` witness and the
  -- residual trace at `acc'`.  Mirror for O3.
  ------------------------------------------------------------------------

  o2-trace-head : ∀ {i is acc final}
    → O2-Trace (i ∷ is) acc final
    → Σ-syntax (ℕ × IndexSet) (λ acc' →
          (O2-step i acc ≡ just acc')
        × O2-Trace is acc' final)
  o2-trace-head (o2-step {acc' = acc'} step rest) = acc' , step , rest

  o3-trace-head : ∀ {i is acc final}
    → O3-Trace (i ∷ is) acc final
    → Σ-syntax (ℕ × PartialMap) (λ acc' →
          (O3-step i acc ≡ just acc')
        × O3-Trace is acc' final)
  o3-trace-head (o3-step {acc' = acc'} step rest) = acc' , step , rest

------------------------------------------------------------------------
-- Section D.  Backward direction (statements only).
--
-- Phase 4d will fill these.  The backward direction needs the same
-- invariants threaded the other way: from a satisfying assignment +
-- `producer-safe src ≡ true`, recover an `R-instrs` derivation.
--
-- The four "gap-filler" backward proofs in `CircuitFaithfulness.agda`
-- (`assert-bwd`, `not-bwd`, `reconstitute-field-bwd`, `less-than-bwd`)
-- each currently take an obligation-evidence hypothesis explicitly.
-- Phase 4c provides those hypotheses by extracting per-step O2 / O3
-- evidence from `producer-safe src ≡ true`.
--
-- Phase 4d D1 status: DISCHARGED.  The wire-discipline obligation is
-- threaded in `Obligations.agda` and discharged by `wire-disc-sound`
-- above.  D1's signature takes `wire-check instr (nr-wires st) ≡ true`
-- as a per-step premise.  D1's body (`satisfies→R-instr-step` below) is
-- now fully concrete: all 26 instruction cases land directly, each
-- applying the corresponding `*-bwd` lemma in CircuitFaithfulness.agda
-- (no postulated fallback remains).  The signature uses explicit suffix
-- decomposition:
--   • `mem-suf : List Fr`  — memory extension
--   • `pis-suf : List Fr`  — pis extension (= [] for non-pi cases)
-- and outputs Σ s' with `memory s' ≡ memory s ++ mem-suf` and
-- `pis s' ≡ pis s ++ pis-suf`.
--
-- CircuitFaithfulness.agda ships backward lemmas for all 26
-- instructions:
--   * existing: add, constrain-eq, cond-select, declare-pub-input,
--     public-input (×3), private-input (×3), div-mod-power-of-two,
--     assert (gap), not (gap), reconstitute-field (gap), less-than (gap),
--     transient-hash, persistent-hash, hash-to-curve, ec-add, ec-mul,
--     ec-mul-generator
--   * mul, neg, copy, load-imm, test-eq,
--     constrain-bits, constrain-to-boolean, output
-- pi-skip's backward is inlined in the dispatcher (its premise uses a
-- private operator).
--
-- D2 (the list-level backward direction, incl. its cons step) is now
-- fully discharged below (`satisfies-clauses→R-instrs`), as is D3, the
-- top-level backward (`circuit-faithful-bwd`) and the bundled `_⇔_`
-- (`circuit-faithful`).  P5 is closed; no postulates remain.
------------------------------------------------------------------------

-- Phase 4d D1: per-step backward dispatcher.
--
-- Signature shape: the dispatcher *produces* the post-state `s'` rather
-- than consuming it.  The witness in the input satisfies-clauses is
-- over `(memory s ++ suf, pis')` — the suffix is the concrete memory
-- extension committed to by the satisfying witness.
--
-- Output Σ packages:
--   • `s'`              — the recovered post-state,
--   • `mem-eq`          — `memory s' ≡ memory s ++ suf`,
--   • `pis-eq`          — `pis s' ≡ pis'`,
--   • `R-instr pre s i s'`  — the operational reconstruction.
--
-- `wire-check i (nr-wires st) ≡ true` is the per-step consequence of
-- the producer's `wire-disc` obligation (threaded by D2 via
-- `wire-trace-head`).  Combined with `mem-inv : nr-wires st ≡ length
-- (memory s)` this lets each case extract pre-state lookups from
-- post-state ones via `lookup-shrink`.
--
-- The dispatcher discharges all 26 instruction cases directly, using
-- the corresponding `*-bwd` lemma in CircuitFaithfulness.agda.  The
-- obligation-bearing cases (assert, not, reconstitute-field, less-than)
-- consume the O2/O3 evidence threaded through the signature; the
-- side-data cases (output, pi-skip, public-input, private-input) read
-- the transcript/skip data off the `op-side-data` payload `sd`.

private
  -- (`<ᵇ-to-≤` and `∧-≡-true-split` are defined earlier in the file in
  -- the structural-extension private block; reused here for the D1
  -- dispatcher.)

  -- mem ++ (x ∷ y ∷ []) ≡ (mem ++ (x ∷ [])) ++ (y ∷ []).  Used by the
  -- Δmem = 2 dispatcher cases to convert from the push-mem2 form (which
  -- the satisfaction witness commits to) to the iterated push-mem form
  -- that the corresponding `*-bwd` lemmas expect.
  push-mem2-assoc : ∀ (m : List Fr) x y
    → m ++ (x ∷ y ∷ []) ≡ (m ++ (x ∷ [])) ++ (y ∷ [])
  push-mem2-assoc []       x y = refl
  push-mem2-assoc (z ∷ zs) x y = cong (z ∷_) (push-mem2-assoc zs x y)

  -- O2 obligation-check extraction.  For the obligation-bearing
  -- instructions (`assert`, `not`, `cond-select`), the check has the
  -- form `if mem? c bk then just bk else nothing`; a `≡ just bk`
  -- premise forces the membership.
  o2-check-mem? : ∀ (c : Index) (bk : IndexSet)
    → (if mem? c bk then just bk else nothing) ≡ just bk
    → mem? c bk ≡ true
  o2-check-mem? c bk eq with mem? c bk
  ... | true  = refl
  ... | false with eq
  ...           | ()

  -- Boolean `≤` to `≤` conversion.  `_≤ᵇ_` returns `true` iff the
  -- `Data.Nat._≤?_` decision says yes.
  ≤ᵇ-to-≤ : ∀ m n → (m ≤ᵇ n) ≡ true → m Data.Nat.≤ n
  ≤ᵇ-to-≤ m n eq with m Data.Nat.≤? n
  ... | yes p = p
  ... | no  _ with eq
  ...           | ()


-- Per-instruction operational side data supplied to the backward
-- dispatcher.  For most instructions this is `⊤` (no side data needed);
-- for the four "side-data instructions" (`output`, `pi-skip`,
-- `public-input`, `private-input`) it carries the per-step evidence
-- that the in-circuit witness alone doesn't determine — namely a
-- memory lookup (for `output`), a guard evaluation result (for
-- `pi-skip`, `public-input`, `private-input`), a transcript-prefix
-- match (for active `pi-skip`), and the consumed transcript entry
-- (for active `public-input` / `private-input`).
--
-- D2 will supply these from the operational rule fired at each step
-- (the rule's own premises are exactly the data here).  See D2.
--
-- Path B (refined):  ALL 26 cases now carry propositional shape Σ
-- evidence so that the cons body of D2 — which sees the head's
-- `mem-suf` and `pis-suf` as free variables — can refine them to their
-- canonical shapes by destructuring the side-data witness.
--
-- Shape encoding by instruction:
--   • Δmem=0, Δpis=0   →  (mem-suf ≡ []) × (pis-suf ≡ [])
--   • Δmem=1, Δpis=0   →  Σ Fr (λ w → mem-suf ≡ w ∷ []) × (pis-suf ≡ [])
--   • Δmem=2, Δpis=0   →  Σ Fr (λ x → Σ Fr (λ y → mem-suf ≡ x ∷ y ∷ [])) × (pis-suf ≡ [])
--   • Δmem=0, Δpis=1 (declare-pub-input)
--                      →  (mem-suf ≡ []) × Σ Fr (λ wv → pis-suf ≡ wv ∷ [])
-- For the four "side-data instructions" the shape Σ wraps the
-- operational payload (mem-lookup / eval-guard / consume-pub-out /
-- consume-priv).
op-side-data : Instruction → ProofPreimage → Preprocessed
             → (mem-suf pis-suf : List Fr) → Set
-- Δmem=0, Δpis=0 (no payload).
op-side-data (assert _)               _ _ ms ps = (ms ≡ []) × (ps ≡ [])
op-side-data (constrain-bits _ _)     _ _ ms ps = (ms ≡ []) × (ps ≡ [])
op-side-data (constrain-eq _ _)       _ _ ms ps = (ms ≡ []) × (ps ≡ [])
op-side-data (constrain-to-boolean _) _ _ ms ps = (ms ≡ []) × (ps ≡ [])
-- Δmem=1, Δpis=0 (push-mem cases).
op-side-data (add _ _)                _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (mul _ _)                _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (neg _)                  _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (copy _)                 _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (load-imm _)             _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (test-eq _ _)            _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (transient-hash _)       _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (cond-select _ _ _)      _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (not _)                  _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (less-than _ _ _)        _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
op-side-data (reconstitute-field _ _ _) _ _ ms ps =
  Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
-- Δmem=2, Δpis=0 (push-mem2 cases).
op-side-data (ec-add _ _ _ _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
op-side-data (ec-mul _ _ _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
op-side-data (ec-mul-generator _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
op-side-data (hash-to-curve _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
op-side-data (persistent-hash _ _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
op-side-data (div-mod-power-of-two _ _) _ _ ms ps =
  Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
-- Δmem=0, Δpis=1 (declare-pub-input).
op-side-data (declare-pub-input _) _ _ ms ps =
  (ms ≡ []) × Σ-syntax Fr (λ wv → ps ≡ wv ∷ [])
-- ── Four side-data instructions ──
-- output v: Δmem=0, Δpis=0; carries a mem-lookup proof producing `val`.
op-side-data (output v) _ s ms ps =
  Σ-syntax Fr (λ val → mem-lookup (Preprocessed.memory s) v ≡ just val)
  × (ms ≡ []) × (ps ≡ [])
-- pi-skip: Δmem=0, Δpis=0; payload = guard's truth value and
-- (if active) the transcript prefix-match check.
op-side-data (pi-skip g count) pre s ms ps =
  (ms ≡ []) × (ps ≡ [])
  × Σ-syntax Bool (λ active →
        eval-guard (Preprocessed.memory s) g ≡ just active
      × (if active
         then ((drop (length (Preprocessed.pis s) ∸ count) (Preprocessed.pis s)
                  ≡ᶠ-list?
                take count (drop (Preprocessed.pub-in-idx s ∸ count)
                                  (ProofPreimage.pub-transcript-inputs pre)))
                ≡ true)
         else ⊤))
-- public-input g: Δmem=1, Δpis=0; the single memory cell `w` is bound
-- by the outer Σ so the payload (consume-pub-out producing `w`) can
-- reference it.
op-side-data (public-input g) pre s ms ps =
  Σ-syntax Fr (λ w → (ms ≡ w ∷ []) × (ps ≡ [])
    × Σ-syntax Bool (λ active →
          eval-guard (Preprocessed.memory s) g ≡ just active
        × (if active
           then Σ-syntax Preprocessed (λ s₁ → consume-pub-out s ≡ just (w , s₁))
           else (w ≡ 0ᶠ))))
-- private-input g: symmetric to public-input.
op-side-data (private-input g) pre s ms ps =
  Σ-syntax Fr (λ w → (ms ≡ w ∷ []) × (ps ≡ [])
    × Σ-syntax Bool (λ active →
          eval-guard (Preprocessed.memory s) g ≡ just active
        × (if active
           then Σ-syntax Preprocessed (λ s₁ → consume-priv s ≡ just (w , s₁))
           else (w ≡ 0ᶠ))))

------------------------------------------------------------------------
-- `next-state-from-osd` — Path B (Option A).
--
-- Computes the canonical post-state produced by each D1 case directly
-- from the inputs (`i`, `pre`, `s`, `mem-suf`, `pis-suf`, `sd`).  This
-- is the post-state that the corresponding `satisfies→R-instr-step`
-- branch will return (as the existential `s'`).  By having
-- `op-side-data-list` thread the *computed* next state into the
-- recursive call (rather than carrying an arbitrary `s_mid` from the
-- caller), D2's cons-case reconciles `s_mid` with D1's output by
-- definitional equality.
--
-- The function pattern-matches on the same shape as D1 (instruction +
-- suffixes + side-data).  Ill-shaped inputs fall through to `s` (this
-- branch is never reached in practice — D2 only invokes it on the
-- shapes that `op-side-data-list` guarantees).
------------------------------------------------------------------------
next-state-from-osd
  : (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
    (mem-suf pis-suf : List Fr)
  → op-side-data i pre s mem-suf pis-suf
  → Preprocessed
-- Δmem=0, Δpis=0 cases (state unchanged).  The sd pattern carries
-- two `refl` equations that simultaneously refine `mem-suf := []` and
-- `pis-suf := []`.
next-state-from-osd (assert _)               _ s _ _ _ = s
next-state-from-osd (constrain-bits _ _)     _ s _ _ _ = s
next-state-from-osd (constrain-eq _ _)       _ s _ _ _ = s
next-state-from-osd (constrain-to-boolean _) _ s _ _ _ = s
-- Δmem=1, Δpis=0 (push-mem) cases.  Extract `w` from sd.
next-state-from-osd (add _ _)                _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (mul _ _)                _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (neg _)                  _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (copy _)                 _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (load-imm _)             _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (test-eq _ _)            _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (transient-hash _)       _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (cond-select _ _ _)      _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (not _)                  _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (less-than _ _ _)        _ s _ _ ((w , _) , _) = push-mem s w
next-state-from-osd (reconstitute-field _ _ _) _ s _ _ ((w , _) , _) = push-mem s w
-- Δmem=2 (push-mem2) cases.  Extract `x` and `y` from sd.
next-state-from-osd (ec-add _ _ _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
next-state-from-osd (ec-mul _ _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
next-state-from-osd (ec-mul-generator _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
next-state-from-osd (hash-to-curve _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
next-state-from-osd (persistent-hash _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
next-state-from-osd (div-mod-power-of-two _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
-- Δmem=0, Δpis=1 (declare-pub-input).  Extract `wv` from sd.
next-state-from-osd (declare-pub-input _) _ s _ _ (_ , wv , _) =
  record s
    { pis        = Preprocessed.pis s ++ (wv ∷ [])
    ; pub-in-idx = suc (Preprocessed.pub-in-idx s)
    }
-- ── Four side-data cases ──
-- output v: outputs += val.
next-state-from-osd (output v) _ s _ _ ((val , _) , _ , _) =
  record s { outputs = Preprocessed.outputs s ++ (val ∷ []) }
-- pi-skip g count: splits on `active`.
next-state-from-osd (pi-skip _ _) _ s _ _ (_ , _ , (true  , _ , _)) =
  record s { pi-skips = Preprocessed.pi-skips s ++ (nothing ∷ []) }
next-state-from-osd (pi-skip _ count) _ s _ _ (_ , _ , (false , _ , _)) =
  record s
    { pi-skips   = Preprocessed.pi-skips s ++ (just count ∷ [])
    ; pub-in-idx = Preprocessed.pub-in-idx s ∸ count
    }
-- public-input g: splits on `active`.
next-state-from-osd (public-input _) _ s _ _ (w , _ , _ , (true , _ , (s₁ , _))) =
  record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
next-state-from-osd (public-input _) _ s _ _ (w , _ , _ , (false , _ , _)) =
  record s { memory = Preprocessed.memory s ++ (w ∷ []) }
-- private-input g: symmetric.
next-state-from-osd (private-input _) _ s _ _ (w , _ , _ , (true , _ , (s₁ , _))) =
  record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
next-state-from-osd (private-input _) _ s _ _ (w , _ , _ , (false , _ , _)) =
  record s { memory = Preprocessed.memory s ++ (w ∷ []) }

-- Per-instruction backward step.  Returns a Σ existential because the
-- post-state `s'` is recovered from the satisfaction witness's memory
-- shape; each case applies the appropriate `*-bwd` lemma.
-- `mem-suf` and `pis-suf` are the memory/pis extensions committed to
-- by the witness; D2 threads them per-instruction.
--
-- The four extra premises `O2-Inv`, `O3-Inv`, `O2-check ≡ just bk`,
-- `O3-check ≡ true` are the per-step shadows of the producer-safety
-- conditions; D2 threads them via `o2-preserve` / `o3-preserve` and
-- extracts the `mem?` / `lookupᵐ` facts from the corresponding
-- `O2-Trace` / `O3-Trace` step.  For the 18 non-obligation-bearing
-- cases (arithmetic, EC, hashing, copy, declare-pub-input, etc.) the
-- premises are trivially `refl` and unused; the four obligation-
-- bearing cases (`assert`, `not`, `reconstitute-field`, `less-than`)
-- consume O2-Inv via `o2-known-is-bit` and / or O3-Inv via
-- `o3-known-fits`.
satisfies→R-instr-step
  : ∀ {hc} (pre : ProofPreimage) (s : Preprocessed) (i : Instruction)
    (st : SynthState) (mem-suf : List Fr) (pis-suf : List Fr)
  → mem-inv s st
  → pi-inv  hc s st
  → wire-check i (SynthState.nr-wires st) ≡ true
  → ∀ {bk : IndexSet} {bm : PartialMap}
  → O2-Inv (SynthState.nr-wires st , bk) s
  → O3-Inv (SynthState.nr-wires st , bm) s
  → O2-check i bk ≡ just bk
  → O3-check i bm ≡ true
  → (sd : op-side-data i pre s mem-suf pis-suf)
  → satisfies-clauses
      (SynthState.clauses (circuit-instr hc i st))
      (mk-witness (Preprocessed.memory s ++ mem-suf)
                  (Preprocessed.pis    s ++ pis-suf)
                  (comm-rand-of pre))
  → let s' = next-state-from-osd i pre s mem-suf pis-suf sd in
        (Preprocessed.memory s' ≡ Preprocessed.memory s ++ mem-suf)
      × (Preprocessed.pis    s' ≡ Preprocessed.pis    s ++ pis-suf)
      × R-instr pre s i s'
-- D1 dispatcher cases.  Each instruction's case follows this template:
--   1. Pattern-match `i` and `suf`; unfold `circuit-instr hc i st`.
--   2. Apply `satisfies-clauses-split` to peel off prior-clause sat.
--   3. Apply `<ᵇ-to-≤` + `mi` to convert `wc` into per-operand bounds
--      `suc operand ≤ length (memory s)`.
--   4. Destructure the new-clauses satisfaction; pull post-state
--      lookups via `lookup-shrink` to get pre-state lookups.
--   5. Call the `*-bwd` lemma to produce `R-instr pre s i s'`.
--   6. Package the Σ output (s', mem-eq, pis-eq, R-instr).
--
-- 17 "easy" cases (arithmetic + EC + hash, no transcript or output
-- side effects) follow this template.  9 cases need additional plumbing
-- (the four gap-filled cases need O2/O3 evidence; the five transcript-
-- consuming or push-skip/push-output cases need operational side data).

-- ─── add(a, b) ─────────────────────────────────────────────────────
-- Δmem = 1; pis unchanged.  Worked-example case.
satisfies→R-instr-step {hc} pre s (add a b) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat
  with ∧-≡-true-split wc
... | a<n , b<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      -- Peel the new clause off `sat`:  clauses (circuit-instr hc (add a b) st)
      -- = clauses st ++ [clause-add n a b].
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-add n a b ∷ [])
                      sat
      hold-add , _ = sat-new
      av      = proj₁ hold-add
      bv      = proj₁ (proj₂ hold-add)
      la-post = proj₁ (proj₂ (proj₂ (proj₂ hold-add)))
      lb-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-add))))
      la-pre  : mem-lookup mem a ≡ just av
      la-pre  = lookup-shrink mem (w ∷ []) a la-post a≤len
      lb-pre  : mem-lookup mem b ≡ just bv
      lb-pre  = lookup-shrink mem (w ∷ []) b lb-post b≤len
      -- Re-shape `sat-new` to use `length mem` (≡ n) for add-bwd.
      sat-shifted : satisfies-clauses
                      (single-instr-clauses hc (length mem) (add a b))
                      (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                  (comm-rand-of pre))
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-add k a b ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      _ , r-add-ev = add-bwd {pre = pre} {s = s} {a = a} {b = b}
                              {av = av} {bv = bv} {v = w} {hc = hc}
                              {rand = comm-rand-of pre}
                              la-pre lb-pre
                              (subst (λ p → satisfies-clauses
                                              (single-instr-clauses hc (length mem) (add a b))
                                              (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                                     (++-identityʳ (Preprocessed.pis s))
                                     sat-shifted)
      s' = push-mem s w
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-add-ev

-- ─── mul(a, b) ─────────────────────────────────────────────────────
satisfies→R-instr-step {hc} pre s (mul a b) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat
  with ∧-≡-true-split wc
... | a<n , b<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-mul n a b ∷ []) sat
      hold-mul , _ = sat-new
      av      = proj₁ hold-mul
      bv      = proj₁ (proj₂ hold-mul)
      la-post = proj₁ (proj₂ (proj₂ (proj₂ hold-mul)))
      lb-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-mul))))
      la-pre  = lookup-shrink mem (w ∷ []) a la-post a≤len
      lb-pre  = lookup-shrink mem (w ∷ []) b lb-post b≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-mul k a b ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (mul a b))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      _ , r-ev = mul-bwd {pre = pre} {s = s} {a = a} {b = b}
                          {av = av} {bv = bv} {v = w} {hc = hc}
                          {rand = comm-rand-of pre}
                          la-pre lb-pre sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── neg(a) ────────────────────────────────────────────────────────
satisfies→R-instr-step {hc} pre s (neg a) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-neg n a ∷ []) sat
      hold-neg , _ = sat-new
      av      = proj₁ hold-neg
      la-post = proj₁ (proj₂ (proj₂ hold-neg))
      la-pre  = lookup-shrink mem (w ∷ []) a la-post a≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-neg k a ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (neg a))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      _ , r-ev = neg-bwd {pre = pre} {s = s} {a = a}
                          {av = av} {v = w} {hc = hc}
                          {rand = comm-rand-of pre}
                          la-pre sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── test-eq(a, b) ─────────────────────────────────────────────────
satisfies→R-instr-step {hc} pre s (test-eq a b) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat
  with ∧-≡-true-split wc
... | a<n , b<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-test-eq n a b ∷ []) sat
      hold-te , _ = sat-new
      av      = proj₁ hold-te
      bv      = proj₁ (proj₂ hold-te)
      la-post = proj₁ (proj₂ (proj₂ (proj₂ hold-te)))
      lb-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-te))))
      la-pre  = lookup-shrink mem (w ∷ []) a la-post a≤len
      lb-pre  = lookup-shrink mem (w ∷ []) b lb-post b≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-test-eq k a b ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (test-eq a b))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      _ , r-ev = test-eq-bwd {pre = pre} {s = s} {a = a} {b = b}
                              {av = av} {bv = bv} {v = w} {hc = hc}
                              {rand = comm-rand-of pre}
                              la-pre lb-pre sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── copy(v) ───────────────────────────────────────────────────────
satisfies→R-instr-step {hc} pre s (copy v) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      v≤len  = subst (suc v Data.Nat.≤_) mi (<ᵇ-to-≤ v n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-copy n v ∷ []) sat
      hold-cp , _ = sat-new
      vv      = proj₁ hold-cp
      la-post = proj₁ (proj₂ (proj₂ hold-cp))
      la-pre  = lookup-shrink mem (w ∷ []) v la-post v≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-copy k v ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (copy v))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      _ , r-ev = copy-bwd {pre = pre} {s = s} {v = v} {vv = vv} {w = w} {hc = hc}
                           {rand = comm-rand-of pre}
                           la-pre sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── constrain-eq(a, b) ───────────────────────────────────────────
-- Δmem = 0; mem/pis unchanged.  Suffix is [].
satisfies→R-instr-step {hc} pre s (constrain-eq a b) st _ _ mi pii wc _ _ _ _ (refl , refl) sat
  with ∧-≡-true-split wc
... | a<n , b<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-eq a b ∷ []) sat
      hold-eq , _ = sat-new
      av      = proj₁ hold-eq
      bv      = proj₁ (proj₂ hold-eq)
      la-post = proj₁ (proj₂ (proj₂ hold-eq))
      lb-post = proj₁ (proj₂ (proj₂ (proj₂ hold-eq)))
      -- `mem ++ [] = mem` only via subst with ++-identityʳ.
      la-eq : mem-lookup mem a ≡ just av
      la-eq = subst (λ m → mem-lookup m a ≡ just av)
                    (++-identityʳ mem) la-post
      lb-eq : mem-lookup mem b ≡ just bv
      lb-eq = subst (λ m → mem-lookup m b ≡ just bv)
                    (++-identityʳ mem) lb-post
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-eq a b ∷ [])
                                    (mk-witness (mem ++ []) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-mem = subst (λ m → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-eq a b))
                                (mk-witness m (Preprocessed.pis s ++ []) (comm-rand-of pre)))
                      (++-identityʳ mem) sat-shifted
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-eq a b))
                                (mk-witness mem p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-mem
      r-ev = constrain-eq-bwd {pre = pre} {s = s} {a = a} {b = b}
                               {av = av} {bv = bv} {hc = hc}
                               {rand = comm-rand-of pre}
                               la-eq lb-eq sat-pis
      mem-eq : Preprocessed.memory s ≡ mem ++ []
      mem-eq = sym (++-identityʳ mem)
      pis-eq : Preprocessed.pis s ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── constrain-bits(v, n) ─────────────────────────────────────────
satisfies→R-instr-step {hc} pre s (constrain-bits v bits) st _ _ mi pii wc _ _ _ _ (refl , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      v≤len  = subst (suc v Data.Nat.≤_) mi (<ᵇ-to-≤ v n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-range-bits v bits ∷ []) sat
      hold-rb , _ = sat-new
      vv      = proj₁ hold-rb
      la-post = proj₁ (proj₂ hold-rb)
      la-eq : mem-lookup mem v ≡ just vv
      la-eq = subst (λ m → mem-lookup m v ≡ just vv)
                    (++-identityʳ mem) la-post
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-range-bits v bits ∷ [])
                                    (mk-witness (mem ++ []) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-mem = subst (λ m → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-bits v bits))
                                (mk-witness m (Preprocessed.pis s ++ []) (comm-rand-of pre)))
                      (++-identityʳ mem) sat-shifted
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-bits v bits))
                                (mk-witness mem p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-mem
      r-ev = constrain-bits-bwd {pre = pre} {s = s} {v = v} {n = bits}
                                 {vv = vv} {hc = hc} {rand = comm-rand-of pre}
                                 la-eq sat-pis
      mem-eq = sym (++-identityʳ mem)
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── constrain-to-boolean(v) ──────────────────────────────────────
satisfies→R-instr-step {hc} pre s (constrain-to-boolean v) st _ _ mi pii wc _ _ _ _ (refl , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-bool v ∷ []) sat
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-bool v ∷ [])
                                    (mk-witness (mem ++ []) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-mem = subst (λ m → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-to-boolean v))
                                (mk-witness m (Preprocessed.pis s ++ []) (comm-rand-of pre)))
                      (++-identityʳ mem) sat-shifted
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (constrain-to-boolean v))
                                (mk-witness mem p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-mem
      r-ev = constrain-to-boolean-bwd {pre = pre} {s = s} {v = v} {hc = hc}
                                       {rand = comm-rand-of pre} sat-pis
      mem-eq = sym (++-identityʳ mem)
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── load-imm(imm) ─────────────────────────────────────────────────
-- No operand wire-check; wire-check always = true for load-imm.
satisfies→R-instr-step {hc} pre s (load-imm imm) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st) (clause-load-imm n imm ∷ []) sat
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-load-imm k imm ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (load-imm imm))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      _ , r-ev = load-imm-bwd {pre = pre} {s = s} {k = imm} {w = w} {hc = hc}
                               {rand = comm-rand-of pre}
                               sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── transient-hash(inputs) ──────────────────────────────────────────
-- Δmem = 1; pis unchanged.  Inputs witnessed via `mem-lookups`.
satisfies→R-instr-step {hc} pre s (transient-hash inputs) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      -- `wc : all-lt? inputs n ≡ true`.  Convert to length-mem form.
      wc-len : all-lt? inputs (length mem) ≡ true
      wc-len = subst (λ k → all-lt? inputs k ≡ true) mi wc
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-transient-hash n inputs ∷ []) sat
      hold-th , _ = sat-new
      vs       = proj₁ hold-th
      ov       = proj₁ (proj₂ hold-th)
      lvs-post = proj₁ (proj₂ (proj₂ hold-th))
      -- Convert the input-vector lookup back to pre-state via mem-lookups-shrink.
      lvs-pre  : mem-lookups mem inputs ≡ just vs
      lvs-pre  = mem-lookups-shrink mem (w ∷ []) inputs wc-len lvs-post
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-transient-hash k inputs ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (transient-hash inputs))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      w≡hash , r-ev = transient-hash-bwd {pre = pre} {s = s} {inputs = inputs}
                                     {vs = vs} {v = w} {hc = hc}
                                     {rand = comm-rand-of pre}
                                     lvs-pre sat-pis
      r-ev' : R-instr pre s (transient-hash inputs) (push-mem s w)
      r-ev' = subst (λ z → R-instr pre s (transient-hash inputs) (push-mem s z))
                    (sym w≡hash) r-ev
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev'

-- ─── cond-select(b, a, c) ────────────────────────────────────────────
-- Δmem = 1; pis unchanged.  §6.5 gap-free.
satisfies→R-instr-step {hc} pre s (cond-select b a c) st _ _ mi pii wc _ _ _ _ ((w , refl) , refl) sat
  with ∧-≡-true-split wc
... | b<n , ac<n with ∧-≡-true-split ac<n
...   | a<n , c<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      c≤len  = subst (suc c Data.Nat.≤_) mi (<ᵇ-to-≤ c n c<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-cond-select n b a c ∷ []) sat
      hold-cs , _ = sat-new
      bv       = proj₁ hold-cs
      av       = proj₁ (proj₂ hold-cs)
      cv       = proj₁ (proj₂ (proj₂ hold-cs))
      lb-post  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-cs))))
      la-post  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-cs)))))
      lc-post  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-cs))))))
      lb-pre   = lookup-shrink mem (w ∷ []) b lb-post b≤len
      la-pre   = lookup-shrink mem (w ∷ []) a la-post a≤len
      lc-pre   = lookup-shrink mem (w ∷ []) c lc-post c≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-cond-select k b a c ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (cond-select b a c))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      r-ev = cond-select-bwd {pre = pre} {s = s} {b = b} {a = a} {c = c}
                              {bv = bv} {av = av} {cv = cv} {v = w} {hc = hc}
                              {rand = comm-rand-of pre}
                              lb-pre la-pre lc-pre sat-pis
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── hash-to-curve(inputs) ──────────────────────────────────────────
-- Δmem = 2; pis unchanged.  Inputs via `mem-lookups`; output 2 cells.
satisfies→R-instr-step {hc} pre s (hash-to-curve inputs) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      wc-len : all-lt? inputs (length mem) ≡ true
      wc-len = subst (λ k → all-lt? inputs k ≡ true) mi wc
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-hash-to-curve n (suc n) inputs ∷ []) sat
      hold-htc , _ = sat-new
      vs       = proj₁ hold-htc
      lvs-post = proj₁ (proj₂ (proj₂ (proj₂ hold-htc)))
      lvs-pre  : mem-lookups mem inputs ≡ just vs
      lvs-pre  = mem-lookups-shrink mem (x ∷ y ∷ []) inputs wc-len lvs-post
      -- Shift n → length mem in the clause.
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-hash-to-curve k (suc k) inputs ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      -- Drop the pis-suf = [].
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (hash-to-curve inputs))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      -- Convert push-mem2 form to iterated push-mem form for the bwd lemma.
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (hash-to-curve inputs))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      _ , r-ev = hash-to-curve-bwd {pre = pre} {s = s} {inputs = inputs}
                                    {vs = vs} {x = x} {y = y} {hc = hc}
                                    {rand = comm-rand-of pre}
                                    lvs-pre sat-assoc
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── persistent-hash(α, inputs) ─────────────────────────────────────
satisfies→R-instr-step {hc} pre s (persistent-hash α inputs) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      wc-len : all-lt? inputs (length mem) ≡ true
      wc-len = subst (λ k → all-lt? inputs k ≡ true) mi wc
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-persistent-hash n (suc n) α inputs ∷ []) sat
      hold-ph , _ = sat-new
      vs       = proj₁ hold-ph
      lvs-post = proj₁ (proj₂ (proj₂ (proj₂ hold-ph)))
      lvs-pre  : mem-lookups mem inputs ≡ just vs
      lvs-pre  = mem-lookups-shrink mem (x ∷ y ∷ []) inputs wc-len lvs-post
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-persistent-hash k (suc k) α inputs ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (persistent-hash α inputs))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (persistent-hash α inputs))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      _ , r-ev = persistent-hash-bwd {pre = pre} {s = s} {α = α} {inputs = inputs}
                                      {vs = vs} {x = x} {y = y} {hc = hc}
                                      {rand = comm-rand-of pre}
                                      lvs-pre sat-assoc
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── ec-add(a-x, a-y, b-x, b-y) ─────────────────────────────────────
satisfies→R-instr-step {hc} pre s (ec-add a-x a-y b-x b-y) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat
  with ∧-≡-true-split wc
... | ax<n , rest1 with ∧-≡-true-split rest1
...   | ay<n , rest2 with ∧-≡-true-split rest2
...     | bx<n , by<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      ax≤len = subst (suc a-x Data.Nat.≤_) mi (<ᵇ-to-≤ a-x n ax<n)
      ay≤len = subst (suc a-y Data.Nat.≤_) mi (<ᵇ-to-≤ a-y n ay<n)
      bx≤len = subst (suc b-x Data.Nat.≤_) mi (<ᵇ-to-≤ b-x n bx<n)
      by≤len = subst (suc b-y Data.Nat.≤_) mi (<ᵇ-to-≤ b-y n by<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-ec-add n (suc n) a-x a-y b-x b-y ∷ []) sat
      hold-ea , _ = sat-new
      ax = proj₁ hold-ea
      ay = proj₁ (proj₂ hold-ea)
      bx = proj₁ (proj₂ (proj₂ hold-ea))
      by = proj₁ (proj₂ (proj₂ (proj₂ hold-ea)))
      lax-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-ea))))))
      lay-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-ea)))))))
      lbx-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-ea))))))))
      lby-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-ea)))))))))
      lax-pre  = lookup-shrink mem (x ∷ y ∷ []) a-x lax-post ax≤len
      lay-pre  = lookup-shrink mem (x ∷ y ∷ []) a-y lay-post ay≤len
      lbx-pre  = lookup-shrink mem (x ∷ y ∷ []) b-x lbx-post bx≤len
      lby-pre  = lookup-shrink mem (x ∷ y ∷ []) b-y lby-post by≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-ec-add k (suc k) a-x a-y b-x b-y ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (ec-add a-x a-y b-x b-y))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (ec-add a-x a-y b-x b-y))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      _ , r-ev = ec-add-bwd {pre = pre} {s = s}
                             {a-x = a-x} {a-y = a-y} {b-x = b-x} {b-y = b-y}
                             {ax = ax} {ay = ay} {bx = bx} {by = by}
                             {x = x} {y = y} {hc = hc}
                             {rand = comm-rand-of pre}
                             lax-pre lay-pre lbx-pre lby-pre sat-assoc
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── ec-mul(a-x, a-y, scalar) ───────────────────────────────────────
satisfies→R-instr-step {hc} pre s (ec-mul a-x a-y scalar) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat
  with ∧-≡-true-split wc
... | ax<n , rest1 with ∧-≡-true-split rest1
...   | ay<n , sc<n =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      ax≤len = subst (suc a-x Data.Nat.≤_) mi (<ᵇ-to-≤ a-x n ax<n)
      ay≤len = subst (suc a-y Data.Nat.≤_) mi (<ᵇ-to-≤ a-y n ay<n)
      sc≤len = subst (suc scalar Data.Nat.≤_) mi (<ᵇ-to-≤ scalar n sc<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-ec-mul n (suc n) a-x a-y scalar ∷ []) sat
      hold-em , _ = sat-new
      ax = proj₁ hold-em
      ay = proj₁ (proj₂ hold-em)
      sc = proj₁ (proj₂ (proj₂ hold-em))
      lax-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-em)))))
      lay-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-em))))))
      lsc-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-em)))))))
      lax-pre  = lookup-shrink mem (x ∷ y ∷ []) a-x lax-post ax≤len
      lay-pre  = lookup-shrink mem (x ∷ y ∷ []) a-y lay-post ay≤len
      lsc-pre  = lookup-shrink mem (x ∷ y ∷ []) scalar lsc-post sc≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-ec-mul k (suc k) a-x a-y scalar ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (ec-mul a-x a-y scalar))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (ec-mul a-x a-y scalar))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      _ , r-ev = ec-mul-bwd {pre = pre} {s = s}
                             {a-x = a-x} {a-y = a-y} {scalar = scalar}
                             {ax = ax} {ay = ay} {sc = sc}
                             {x = x} {y = y} {hc = hc}
                             {rand = comm-rand-of pre}
                             lax-pre lay-pre lsc-pre sat-assoc
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── ec-mul-generator(scalar) ───────────────────────────────────────
satisfies→R-instr-step {hc} pre s (ec-mul-generator scalar) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      sc≤len = subst (suc scalar Data.Nat.≤_) mi (<ᵇ-to-≤ scalar n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-ec-mul-generator n (suc n) scalar ∷ []) sat
      hold-eg , _ = sat-new
      sc = proj₁ hold-eg
      lsc-post = proj₁ (proj₂ (proj₂ (proj₂ hold-eg)))
      lsc-pre  = lookup-shrink mem (x ∷ y ∷ []) scalar lsc-post sc≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-ec-mul-generator k (suc k) scalar ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (ec-mul-generator scalar))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (ec-mul-generator scalar))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      _ , r-ev = ec-mul-generator-bwd {pre = pre} {s = s} {scalar = scalar}
                                       {sc = sc} {x = x} {y = y} {hc = hc}
                                       {rand = comm-rand-of pre}
                                       lsc-pre sat-assoc
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev

-- ─── div-mod-power-of-two(var, bits) ────────────────────────────────
-- Δmem = 2.  Output = (q , r) from canonical bit decomposition.  The
-- bwd lemma returns `R-instr` to `push-mem (push-mem s canon-q) canon-r`
-- and equations `x ≡ canon-q`, `y ≡ canon-r`; we subst back to make the
-- output match `push-mem2 s x y`.
satisfies→R-instr-step {hc} pre s (div-mod-power-of-two var bits) st _ _ mi pii wc _ _ _ _ ((x , y , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      v≤len  = subst (suc var Data.Nat.≤_) mi (<ᵇ-to-≤ var n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-div-mod n (suc n) var bits ∷ []) sat
      hold-dm , _ = sat-new
      vv       = proj₁ (proj₂ (proj₂ hold-dm))
      la-post  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hold-dm)))))
      la-pre   = lookup-shrink mem (x ∷ y ∷ []) var la-post v≤len
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-div-mod k (suc k) var bits ∷ [])
                                    (mk-witness (mem ++ (x ∷ y ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (div-mod-power-of-two var bits))
                                (mk-witness (mem ++ (x ∷ y ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      sat-assoc = subst (λ m → satisfies-clauses
                                  (single-instr-clauses hc (length mem) (div-mod-power-of-two var bits))
                                  (mk-witness m (Preprocessed.pis s) (comm-rand-of pre)))
                        (push-mem2-assoc mem x y) sat-pis
      x≡cq , y≡cr , r-ev = div-mod-power-of-two-bwd
                              {pre = pre} {s = s} {var = var} {bits = bits}
                              {vv = vv} {x = x} {y = y} {hc = hc}
                              {rand = comm-rand-of pre}
                              la-pre sat-assoc
      -- r-ev : R-instr ... (push-mem (push-mem s canon-q) canon-r).
      -- We want : R-instr ... (push-mem2 s x y).  Subst x≡canon-q and y≡canon-r.
      r-ev1 : R-instr pre s (div-mod-power-of-two var bits)
                (push-mem (push-mem s x) (from-le-bits (take bits (to-le-bits vv))))
      r-ev1 = subst (λ z → R-instr pre s (div-mod-power-of-two var bits)
                              (push-mem (push-mem s z) (from-le-bits (take bits (to-le-bits vv)))))
                    (sym x≡cq) r-ev
      r-ev2 : R-instr pre s (div-mod-power-of-two var bits)
                (push-mem (push-mem s x) y)
      r-ev2 = subst (λ z → R-instr pre s (div-mod-power-of-two var bits)
                              (push-mem (push-mem s x) z))
                    (sym y≡cr) r-ev1
      -- push-mem (push-mem s x) y ≡ push-mem2 s x y propositionally —
      -- their memories differ only by `mem ++ (x ∷ []) ++ (y ∷ [])` vs
      -- `mem ++ (x ∷ y ∷ [])`.  Convert via cong on Preprocessed.
      pm-eq : push-mem (push-mem s x) y ≡ push-mem2 s x y
      pm-eq = cong (λ m → record s { memory = m }) (sym (push-mem2-assoc mem x y))
      r-ev3 : R-instr pre s (div-mod-power-of-two var bits) (push-mem2 s x y)
      r-ev3 = subst (R-instr pre s (div-mod-power-of-two var bits)) pm-eq r-ev2
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev3

-- ─── declare-pub-input(v) ───────────────────────────────────────────
-- Δmem = 0; pis grows by exactly one cell (wv).
satisfies→R-instr-step {hc} pre s (declare-pub-input v) st _ _ mi pii wc _ _ _ _ (refl , wv , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      v≤len  = subst (suc v Data.Nat.≤_) mi (<ᵇ-to-≤ v n wc)
      d      = SynthState.nr-declared-pi st
      -- The dispatcher emits clauses for declare-pub-input via
      -- `single-instr-clauses-with-decl hc (length mem) d`.  But
      -- `circuit-instr hc (declare-pub-input v) st` emits
      -- `clause-pi-from-wire (preamble-pi-count hc + d) v` at the synth
      -- state, where d = nr-declared-pi st.  Convert.
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-pi-from-wire (preamble-pi-count hc + d) v ∷ []) sat
      hold-pi , _ = sat-new
      wv'      = proj₁ hold-pi
      lv-post  = proj₁ (proj₂ (proj₂ hold-pi))
      -- Pre-state lookup: mem unchanged so mem-suf = [] gives `mem ++ [] = mem`.
      lv-pre : mem-lookup mem v ≡ just wv'
      lv-pre = subst (λ m → mem-lookup m v ≡ just wv')
                     (++-identityʳ mem) lv-post
      -- Reshape sat-new to use `length mem` for nr-wires.
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-pi-from-wire (preamble-pi-count hc + d) v ∷ [])
                                    (mk-witness (mem ++ []) (Preprocessed.pis s ++ (wv ∷ []))
                                                (comm-rand-of pre)))
                          mi sat-new
      -- Convert to single-instr-clauses-with-decl form (no wire-count
      -- subst needed since clause-pi-from-wire doesn't depend on n).
      sat-mem = subst (λ m → satisfies-clauses
                                (single-instr-clauses-with-decl hc (length mem) d
                                   (declare-pub-input v))
                                (mk-witness m (Preprocessed.pis s ++ (wv ∷ []))
                                            (comm-rand-of pre)))
                      (++-identityʳ mem) sat-shifted
      -- pi-inv : length (pis s) ≡ preamble-pi-count hc + nr-declared-pi st
      pi-len : length (Preprocessed.pis s) ≡ preamble-pi-count hc + d
      pi-len = pii
      ext≡wv , r-ev = declare-pub-input-bwd
                        {pre = pre} {s = s} {v = v} {wv = wv'} {hc = hc} {d = d}
                        {ext = wv} {rand = comm-rand-of pre}
                        pi-len lv-pre sat-mem
      mem-eq : Preprocessed.memory s ≡ mem ++ []
      mem-eq = sym (++-identityʳ mem)
      s' = record s
             { pis        = Preprocessed.pis s ++ (wv ∷ [])
             ; pub-in-idx = suc (Preprocessed.pub-in-idx s)
             }
  in mem-eq , refl , r-ev

-- ─── assert(c) ────────────────────────────────────────────────────
-- Δmem = 0; pis unchanged.  Gap-filled: needs `is-bit v` (O2-Inv) on
-- the operand.  The clause's `v ≢ 0ᶠ` combines with `is-bit v` (which
-- forces v ∈ {0, 1}) to imply v ≡ 1ᶠ; then `r-assert` fires.
satisfies→R-instr-step {hc} pre s (assert c) st _ _ mi pii wc
                       {bk = bk} o2-inv _ o2-chk _ (refl , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      c≤len  = subst (suc c Data.Nat.≤_) mi (<ᵇ-to-≤ c n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-assert-non-zero c ∷ []) sat
      hold-as , _ = sat-new
      v       = proj₁ hold-as
      lv-post = proj₁ (proj₂ hold-as)
      v≢0     = proj₂ (proj₂ hold-as)
      -- Pre-state lookup for `c`.
      lv-pre : mem-lookup mem c ≡ just v
      lv-pre = subst (λ m → mem-lookup m c ≡ just v)
                     (++-identityʳ mem) lv-post
      -- Extract `mem? c bk ≡ true` from `O2-check ≡ just bk`.
      mem?c : mem? c bk ≡ true
      mem?c = o2-check-mem? c bk o2-chk
      -- Apply `o2-known-is-bit`.
      is-bit-v = o2-known-is-bit {bk = bk} o2-inv mem?c lv-pre
      -- Build sat suitable for `assert-bwd`:  shape  (mem, pis, rand)
      -- with the clauses re-shaped to use `length mem`.
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-assert-non-zero c ∷ [])
                                    (mk-witness (mem ++ []) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-mem = subst (λ m → satisfies-clauses
                                (single-instr-clauses hc (length mem) (assert c))
                                (mk-witness m (Preprocessed.pis s ++ []) (comm-rand-of pre)))
                      (++-identityʳ mem) sat-shifted
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (assert c))
                                (mk-witness mem p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-mem
      r-ev = assert-bwd {pre = pre} {s = s} {c = c} {v = v} {hc = hc}
                         {rand = comm-rand-of pre}
                         lv-pre is-bit-v sat-pis
      mem-eq : Preprocessed.memory s ≡ mem ++ []
      mem-eq = sym (++-identityʳ mem)
      pis-eq : Preprocessed.pis s ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── not(a) ───────────────────────────────────────────────────────
-- Δmem = 1; pis unchanged.  Gap-filled: needs `is-bit av` (O2-Inv) on
-- the operand `a`.  `not-bwd` packages clause data into `r-not` once
-- the boolean precondition is satisfied.
satisfies→R-instr-step {hc} pre s (not a) st _ _ mi pii wc
                       {bk = bk} o2-inv _ o2-chk _ ((w , refl) , refl) sat =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n wc)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-not n a ∷ []) sat
      hold-not , _ = sat-new
      av        = proj₁ hold-not
      la-post   = proj₁ (proj₂ (proj₂ hold-not))
      la-pre    : mem-lookup mem a ≡ just av
      la-pre    = lookup-shrink mem (w ∷ []) a la-post a≤len
      -- Extract `mem? a bk ≡ true` from `O2-check ≡ just bk`.
      mem?a : mem? a bk ≡ true
      mem?a = o2-check-mem? a bk o2-chk
      -- Apply `o2-known-is-bit` to get `is-bit av`.
      is-bit-av = o2-known-is-bit {bk = bk} o2-inv mem?a la-pre
      -- Re-shape the new-clauses satisfaction for `not-bwd`.
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-not k a ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (not a))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      w≡target , r-ev = not-bwd {pre = pre} {s = s} {a = a} {av = av} {v = w} {hc = hc}
                          {rand = comm-rand-of pre}
                          la-pre is-bit-av sat-pis
      r-ev' : R-instr pre s (not a) (push-mem s w)
      r-ev' = subst (λ z → R-instr pre s (not a) (push-mem s z))
                    (sym w≡target) r-ev
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev'

-- ─── less-than(a, b, bits) ───────────────────────────────────────
-- Δmem = 1; pis unchanged.  Gap-filled: `less-than-bwd` needs
-- `fits-in av bits ≡ true` and `fits-in bv bits ≡ true`.  We extract
-- these via O3:
--   O3-check guarantees `lookupᵐ a bm ≡ just ka ∧ ka ≤ᵇ bits ≡ true`
--   (and similarly for b).  `o3-known-fits` lifts to
--   `fits-in av ka ≡ true`.  `fits-in-mono` then pads to
--   `fits-in av bits ≡ true`.
satisfies→R-instr-step {hc} pre s (less-than a b bits) st _ _ mi pii wc
                       {bm = bm} _ o3-inv _ o3-chk ((w , refl) , refl) sat
  with lookupᵐ a bm in eqa | lookupᵐ b bm in eqb
... | just ka | just kb
  with ∧-≡-true-split o3-chk | ∧-≡-true-split wc
... | (ka≤b , kb≤b) | (a<n , b<n) =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      a≤len  = subst (suc a Data.Nat.≤_) mi (<ᵇ-to-≤ a n a<n)
      b≤len  = subst (suc b Data.Nat.≤_) mi (<ᵇ-to-≤ b n b<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-less-than n a b bits ∷ []) sat
      hold-lt , _ = sat-new
      av      = proj₁ hold-lt
      bv      = proj₁ (proj₂ hold-lt)
      la-post = proj₁ (proj₂ (proj₂ (proj₂ hold-lt)))
      lb-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-lt))))
      la-pre  = lookup-shrink mem (w ∷ []) a la-post a≤len
      lb-pre  = lookup-shrink mem (w ∷ []) b lb-post b≤len
      -- Extract fits-in av ka via O3-Inv, then pad to fits-in av bits.
      fits-av-ka : fits-in av ka ≡ true
      fits-av-ka = o3-known-fits {bm = bm} o3-inv eqa la-pre
      fits-bv-kb : fits-in bv kb ≡ true
      fits-bv-kb = o3-known-fits {bm = bm} o3-inv eqb lb-pre
      fits-av : fits-in av bits ≡ true
      fits-av = fits-in-mono fits-av-ka (≤ᵇ-to-≤ ka bits ka≤b)
      fits-bv : fits-in bv bits ≡ true
      fits-bv = fits-in-mono fits-bv-kb (≤ᵇ-to-≤ kb bits kb≤b)
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-less-than k a b bits ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (less-than a b bits))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      w≡target , r-ev = less-than-bwd
                          {pre = pre} {s = s} {a = a} {b = b} {bits = bits}
                          {av = av} {bv = bv} {v = w} {hc = hc}
                          {rand = comm-rand-of pre}
                          la-pre lb-pre fits-av fits-bv sat-pis
      r-ev' : R-instr pre s (less-than a b bits) (push-mem s w)
      r-ev' = subst (λ z → R-instr pre s (less-than a b bits) (push-mem s z))
                    (sym w≡target) r-ev
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev'

-- ─── reconstitute-field(d, m, bits) ─────────────────────────────────
-- Δmem = 1; pis unchanged.  Gap-filled: `reconstitute-field-bwd` needs
-- `bits-in-field (mv-bits ++ dv-bits) ≡ true`.  We extract it via O3:
--   O3-check guarantees `lookupᵐ d bm ≡ just kd ∧ kd ≤ᵇ (FR-bits-bound ∸ bits ∸ 1)`
--   and `lookupᵐ m bm ≡ just km ∧ km ≤ᵇ bits`.  `o3-known-fits` gives
--   `fits-in dv kd` and `fits-in mv km`; `fits-in-mono` pads them to
--   the bounds expected by `bits-in-field-from-strict-bound`, which
--   then supplies the `bits-in-field` premise.
satisfies→R-instr-step {hc} pre s (reconstitute-field d m bits) st _ _ mi pii wc
                       {bm = bm} _ o3-inv _ o3-chk ((w , refl) , refl) sat
  with lookupᵐ d bm in eqd | lookupᵐ m bm in eqm
... | just kd | just km
  with ∧-≡-true-split o3-chk | ∧-≡-true-split wc
... | (kd≤ , km≤) | (d<n , m<n) =
  let mem    = Preprocessed.memory s
      n      = SynthState.nr-wires st
      d≤len  = subst (suc d Data.Nat.≤_) mi (<ᵇ-to-≤ d n d<n)
      m≤len  = subst (suc m Data.Nat.≤_) mi (<ᵇ-to-≤ m n m<n)
      _ , sat-new = satisfies-clauses-split
                      (SynthState.clauses st)
                      (clause-reconstitute n d m bits ∷ []) sat
      hold-rc , _ = sat-new
      dv      = proj₁ hold-rc
      mv      = proj₁ (proj₂ hold-rc)
      ld-post = proj₁ (proj₂ (proj₂ (proj₂ hold-rc)))
      lm-post = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hold-rc))))
      ld-pre  = lookup-shrink mem (w ∷ []) d ld-post d≤len
      lm-pre  = lookup-shrink mem (w ∷ []) m lm-post m≤len
      -- Extract fits-in dv kd and fits-in mv km via O3-Inv.
      fits-dv-kd : fits-in dv kd ≡ true
      fits-dv-kd = o3-known-fits {bm = bm} o3-inv eqd ld-pre
      fits-mv-km : fits-in mv km ≡ true
      fits-mv-km = o3-known-fits {bm = bm} o3-inv eqm lm-pre
      -- Pad to the bounds required by `bits-in-field-from-strict-bound`:
      --   fits-in mv bits        (from km ≤ bits)
      --   fits-in dv (FR-BITS ∸ bits ∸ 1)   (from kd ≤ FR-bits-bound ∸ bits ∸ 1
      --                                       and FR-bits-bound ≡ FR-BITS).
      fits-mv : fits-in mv bits ≡ true
      fits-mv = fits-in-mono fits-mv-km (≤ᵇ-to-≤ km bits km≤)
      fits-dv : fits-in dv (FR-BITS ∸ bits ∸ 1) ≡ true
      fits-dv = fits-in-mono fits-dv-kd
                  (≤ᵇ-to-≤ kd (FR-bits-bound ∸ bits ∸ 1) kd≤)
      -- bits-in-field premise.
      in-field : bits-in-field
                   (take bits (to-le-bits mv) ++ take (FR-BITS ∸ bits) (to-le-bits dv))
                   ≡ true
      in-field = bits-in-field-from-strict-bound {dv = dv} {mv = mv} {n = bits}
                   fits-mv fits-dv
      sat-shifted = subst (λ k → satisfies-clauses
                                    (clause-reconstitute k d m bits ∷ [])
                                    (mk-witness (mem ++ (w ∷ [])) (Preprocessed.pis s ++ [])
                                                (comm-rand-of pre)))
                          mi sat-new
      sat-pis = subst (λ p → satisfies-clauses
                                (single-instr-clauses hc (length mem) (reconstitute-field d m bits))
                                (mk-witness (mem ++ (w ∷ [])) p (comm-rand-of pre)))
                      (++-identityʳ (Preprocessed.pis s)) sat-shifted
      w≡target , r-ev = reconstitute-field-bwd
                          {pre = pre} {s = s} {d = d} {m = m} {bits = bits}
                          {dv = dv} {mv = mv} {v = w} {hc = hc}
                          {rand = comm-rand-of pre}
                          ld-pre lm-pre in-field sat-pis
      r-ev' : R-instr pre s (reconstitute-field d m bits) (push-mem s w)
      r-ev' = subst (λ z → R-instr pre s (reconstitute-field d m bits) (push-mem s z))
                    (sym w≡target) r-ev
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in refl , pis-eq , r-ev'

-- ─── output(v) ────────────────────────────────────────────────────
-- Δmem = 0; pis unchanged.  Emits no clauses (the wire index is
-- recorded for the comm-commitment clause emitted at end of synthesis
-- if has-comm).  Operational side data: `mem-lookup mem v ≡ just val`
-- — the value pushed onto `outputs`.
satisfies→R-instr-step {hc} pre s (output v) st _ _ mi pii wc _ _ _ _ ((val , lv-pre) , refl , refl) sat =
  let mem = Preprocessed.memory s
      s'  = record s { outputs = Preprocessed.outputs s ++ (val ∷ []) }
      r-ev : R-instr pre s (output v) s'
      r-ev = r-output {pre = pre} {s = s} {var = v} {v = val} lv-pre
      mem-eq : Preprocessed.memory s' ≡ mem ++ []
      mem-eq = sym (++-identityʳ mem)
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── pi-skip(g, count) ───────────────────────────────────────────
-- Δmem = 0; pis unchanged.  Emits no clauses (the pi-skip group is
-- pure side data for the verifier).  Operational side data: the
-- guard's evaluation and, if active, the transcript-prefix match.
satisfies→R-instr-step {hc} pre s (pi-skip g count) st _ _ mi pii wc _ _ _ _
                       (refl , refl , (true , ev-guard , prefix-match)) sat =
  let s' = record s { pi-skips = Preprocessed.pi-skips s ++ (nothing ∷ []) }
      r-ev : R-instr pre s (pi-skip g count) s'
      r-ev = r-pi-skip-active {pre = pre} {s = s} {guard = g} {count = count}
                              ev-guard prefix-match
      mem-eq = sym (++-identityʳ (Preprocessed.memory s))
      pis-eq = sym (++-identityʳ (Preprocessed.pis    s))
  in mem-eq , pis-eq , r-ev
satisfies→R-instr-step {hc} pre s (pi-skip g count) st _ _ mi pii wc _ _ _ _
                       (refl , refl , (false , ev-guard , _)) sat =
  let s' = record s
             { pi-skips    = Preprocessed.pi-skips s ++ (just count ∷ [])
             ; pub-in-idx  = Preprocessed.pub-in-idx s ∸ count
             }
      r-ev : R-instr pre s (pi-skip g count) s'
      r-ev = r-pi-skip-inactive {pre = pre} {s = s} {guard = g} {count = count}
                                ev-guard
      mem-eq = sym (++-identityʳ (Preprocessed.memory s))
      pis-eq = sym (++-identityʳ (Preprocessed.pis    s))
  in mem-eq , pis-eq , r-ev

-- ─── public-input(g) ─────────────────────────────────────────────
-- Δmem = 1; pis unchanged.  Either emits no clauses (`g = nothing`)
-- or a single guard-disj clause (`g = just _`).  Operational side
-- data fixes whether active (consume from `pub-out-rem`) or inactive
-- (push 0ᶠ).  The witness's memory cell `w` is reconciled to either
-- the consumed value (active) or 0ᶠ (inactive) via the side data.
satisfies→R-instr-step {hc} pre s (public-input g) st _ _ mi pii wc _ _ _ _
                       (w , refl , refl , (true , ev-guard , (s₁ , consume-eq))) sat =
  let s' = record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
      r-ev : R-instr pre s (public-input g) s'
      r-ev = r-public-input-active {pre = pre} {s = s} {guard = g}
                                   {v = w} {s₁ = s₁}
                                   ev-guard consume-eq
      -- memory s₁ ≡ memory s definitionally (consume-pub-out only
      -- touches pub-out-rem); but Agda needs a proof — pin it via the
      -- `consume-eq` premise's structure.
      mem-eq : Preprocessed.memory s' ≡ Preprocessed.memory s ++ (w ∷ [])
      mem-eq = cong (λ m → m ++ (w ∷ []))
                    (consume-pub-out-mem-eq s consume-eq)
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = trans (consume-pub-out-pis-eq s consume-eq)
                     (sym (++-identityʳ (Preprocessed.pis s)))
  in mem-eq , pis-eq , r-ev
  where
    -- Helper: consume-pub-out preserves memory.
    consume-pub-out-mem-eq : ∀ (s : Preprocessed) {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-pub-out-mem-eq s eq with Preprocessed.pub-out-rem s | eq
    ... | _ ∷ _ | refl = refl
    -- Helper: consume-pub-out preserves pis.
    consume-pub-out-pis-eq : ∀ (s : Preprocessed) {v s'}
      → consume-pub-out s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-pub-out-pis-eq s eq with Preprocessed.pub-out-rem s | eq
    ... | _ ∷ _ | refl = refl
satisfies→R-instr-step {hc} pre s (public-input g) st _ _ mi pii wc _ _ _ _
                       (w , refl , refl , (false , ev-guard , w≡0)) sat =
  let s' = record s { memory = Preprocessed.memory s ++ (w ∷ []) }
      r-ev₀ : R-instr pre s (public-input g) (record s { memory = Preprocessed.memory s ++ (0ᶠ ∷ []) })
      r-ev₀ = r-public-input-inactive {pre = pre} {s = s} {guard = g} ev-guard
      r-ev : R-instr pre s (public-input g) s'
      r-ev = subst (λ z → R-instr pre s (public-input g)
                              (record s { memory = Preprocessed.memory s ++ (z ∷ []) }))
                   (sym w≡0) r-ev₀
      mem-eq : Preprocessed.memory s' ≡ Preprocessed.memory s ++ (w ∷ [])
      mem-eq = refl
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev

-- ─── private-input(g) ────────────────────────────────────────────
-- Symmetric to public-input but consumes from `priv-rem`.
satisfies→R-instr-step {hc} pre s (private-input g) st _ _ mi pii wc _ _ _ _
                       (w , refl , refl , (true , ev-guard , (s₁ , consume-eq))) sat =
  let s' = record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
      r-ev : R-instr pre s (private-input g) s'
      r-ev = r-private-input-active {pre = pre} {s = s} {guard = g}
                                    {v = w} {s₁ = s₁}
                                    ev-guard consume-eq
      mem-eq : Preprocessed.memory s' ≡ Preprocessed.memory s ++ (w ∷ [])
      mem-eq = cong (λ m → m ++ (w ∷ []))
                    (consume-priv-mem-eq s consume-eq)
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = trans (consume-priv-pis-eq s consume-eq)
                     (sym (++-identityʳ (Preprocessed.pis s)))
  in mem-eq , pis-eq , r-ev
  where
    consume-priv-mem-eq : ∀ (s : Preprocessed) {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.memory s' ≡ Preprocessed.memory s
    consume-priv-mem-eq s eq with Preprocessed.priv-rem s | eq
    ... | _ ∷ _ | refl = refl
    consume-priv-pis-eq : ∀ (s : Preprocessed) {v s'}
      → consume-priv s ≡ just (v , s')
      → Preprocessed.pis s' ≡ Preprocessed.pis s
    consume-priv-pis-eq s eq with Preprocessed.priv-rem s | eq
    ... | _ ∷ _ | refl = refl
satisfies→R-instr-step {hc} pre s (private-input g) st _ _ mi pii wc _ _ _ _
                       (w , refl , refl , (false , ev-guard , w≡0)) sat =
  let s' = record s { memory = Preprocessed.memory s ++ (w ∷ []) }
      r-ev₀ : R-instr pre s (private-input g) (record s { memory = Preprocessed.memory s ++ (0ᶠ ∷ []) })
      r-ev₀ = r-private-input-inactive {pre = pre} {s = s} {guard = g} ev-guard
      r-ev : R-instr pre s (private-input g) s'
      r-ev = subst (λ z → R-instr pre s (private-input g)
                              (record s { memory = Preprocessed.memory s ++ (z ∷ []) }))
                   (sym w≡0) r-ev₀
      mem-eq : Preprocessed.memory s' ≡ Preprocessed.memory s ++ (w ∷ [])
      mem-eq = refl
      pis-eq : Preprocessed.pis s' ≡ Preprocessed.pis s ++ []
      pis-eq = sym (++-identityʳ (Preprocessed.pis s))
  in mem-eq , pis-eq , r-ev


------------------------------------------------------------------------
-- D2 helpers
--
-- Two structural facts about `circuit-instr` / `circuit-instrs`:
--   (a) one step extends `clauses` by appending a (possibly empty) list;
--   (b) iterated steps extend `clauses` by an appended list as well.
--
-- These are pure computations: (a) follows by case analysis on `i`,
-- (b) by induction.  Used by D2 to peel off the head step's clauses
-- from the accumulated clauses list.
------------------------------------------------------------------------

private
  -- Per-instruction clause delta.  Symbolically, the list of clauses
  -- that `circuit-instr hc i st` appends to `clauses st`.  We use the
  -- empty list for instructions that emit no clauses
  -- (output, pi-skip, public-input nothing, private-input nothing) and
  -- a one-element list for the rest.  `declare-pub-input` is the only
  -- instruction whose new clause's content depends on `nr-declared-pi
  -- st` (the PI-entry index), so the delta is parameterised by that
  -- field as well as `nr-wires st`.
  instr-new-clauses : Bool → SynthState → Instruction → List Clause
  instr-new-clauses _  st (assert c)               = clause-assert-non-zero c ∷ []
  instr-new-clauses _  st (cond-select b a c)      =
    clause-cond-select (SynthState.nr-wires st) b a c ∷ []
  instr-new-clauses _  st (constrain-bits v bits)  = clause-range-bits v bits ∷ []
  instr-new-clauses _  st (constrain-eq a b)       = clause-eq a b ∷ []
  instr-new-clauses _  st (constrain-to-boolean v) = clause-bool v ∷ []
  instr-new-clauses _  st (copy v)                 =
    clause-copy (SynthState.nr-wires st) v ∷ []
  instr-new-clauses hc st (declare-pub-input v)    =
    clause-pi-from-wire (preamble-pi-count hc + SynthState.nr-declared-pi st) v ∷ []
  instr-new-clauses _  st (pi-skip _ _)            = []
  instr-new-clauses _  st (ec-add ax ay bx by)     =
    clause-ec-add (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) ax ay bx by ∷ []
  instr-new-clauses _  st (ec-mul ax ay s)         =
    clause-ec-mul (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) ax ay s ∷ []
  instr-new-clauses _  st (ec-mul-generator s)     =
    clause-ec-mul-generator (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) s ∷ []
  instr-new-clauses _  st (hash-to-curve inputs)   =
    clause-hash-to-curve (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) inputs ∷ []
  instr-new-clauses _  st (load-imm imm)           =
    clause-load-imm (SynthState.nr-wires st) imm ∷ []
  instr-new-clauses _  st (div-mod-power-of-two v bits) =
    clause-div-mod (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) v bits ∷ []
  instr-new-clauses _  st (reconstitute-field d m bits) =
    clause-reconstitute (SynthState.nr-wires st) d m bits ∷ []
  instr-new-clauses _  st (output v)               = []
  instr-new-clauses _  st (transient-hash inputs)  =
    clause-transient-hash (SynthState.nr-wires st) inputs ∷ []
  instr-new-clauses _  st (persistent-hash α inputs) =
    clause-persistent-hash (SynthState.nr-wires st) (suc (SynthState.nr-wires st)) α inputs ∷ []
  instr-new-clauses _  st (test-eq a b)            =
    clause-test-eq (SynthState.nr-wires st) a b ∷ []
  instr-new-clauses _  st (add a b)                =
    clause-add (SynthState.nr-wires st) a b ∷ []
  instr-new-clauses _  st (mul a b)                =
    clause-mul (SynthState.nr-wires st) a b ∷ []
  instr-new-clauses _  st (neg a)                  =
    clause-neg (SynthState.nr-wires st) a ∷ []
  instr-new-clauses _  st (not a)                  =
    clause-not (SynthState.nr-wires st) a ∷ []
  instr-new-clauses _  st (less-than a b bits)     =
    clause-less-than (SynthState.nr-wires st) a b bits ∷ []
  instr-new-clauses _  st (public-input nothing)   = []
  instr-new-clauses _  st (public-input (just g))  =
    clause-guard-disj (SynthState.nr-wires st) g ∷ []
  instr-new-clauses _  st (private-input nothing)  = []
  instr-new-clauses _  st (private-input (just g)) =
    clause-guard-disj (SynthState.nr-wires st) g ∷ []

  -- Decomposition: `clauses (circuit-instr hc i st) ≡ clauses st ++
  -- instr-new-clauses hc st i`.  By case analysis on `i`.  The
  -- definition of `circuit-instr` makes each case definitionally
  -- equal to its push-clause form, so each case proof is `refl`.
  -- We use a single helper lemma `++-cl` that produces `xs ⊕ x ≡ xs ++ (x ∷ [])`
  -- (which is already definitional).
  clauses-after-instr-eq : ∀ {hc} (i : Instruction) (st : SynthState)
    → SynthState.clauses (circuit-instr hc i st)
      ≡ SynthState.clauses st ++ instr-new-clauses hc st i
  clauses-after-instr-eq (assert c) st                = refl
  clauses-after-instr-eq (cond-select b a c) st       = refl
  clauses-after-instr-eq (constrain-bits v bits) st   = refl
  clauses-after-instr-eq (constrain-eq a b) st        = refl
  clauses-after-instr-eq (constrain-to-boolean v) st  = refl
  clauses-after-instr-eq (copy v) st                  = refl
  clauses-after-instr-eq (declare-pub-input v) st     = refl
  clauses-after-instr-eq (pi-skip g count) st         = sym (++-identityʳ _)
  clauses-after-instr-eq (ec-add ax ay bx by) st      = refl
  clauses-after-instr-eq (ec-mul ax ay s) st          = refl
  clauses-after-instr-eq (ec-mul-generator s) st      = refl
  clauses-after-instr-eq (hash-to-curve inputs) st    = refl
  clauses-after-instr-eq (load-imm imm) st            = refl
  clauses-after-instr-eq (div-mod-power-of-two v bits) st = refl
  clauses-after-instr-eq (reconstitute-field d m bits) st = refl
  clauses-after-instr-eq (output v) st                = sym (++-identityʳ _)
  clauses-after-instr-eq (transient-hash inputs) st   = refl
  clauses-after-instr-eq (persistent-hash α inputs) st = refl
  clauses-after-instr-eq (test-eq a b) st             = refl
  clauses-after-instr-eq (add a b) st                 = refl
  clauses-after-instr-eq (mul a b) st                 = refl
  clauses-after-instr-eq (neg a) st                   = refl
  clauses-after-instr-eq (not a) st                   = refl
  clauses-after-instr-eq (less-than a b bits) st      = refl
  clauses-after-instr-eq (public-input nothing) st    = sym (++-identityʳ _)
  clauses-after-instr-eq (public-input (just g)) st   = refl
  clauses-after-instr-eq (private-input nothing) st   = sym (++-identityʳ _)
  clauses-after-instr-eq (private-input (just g)) st  = refl

  -- Iterated decomposition.  `clauses (circuit-instrs hc is st) ≡
  -- clauses st ++ <tail>` for some explicit tail computed by
  -- `instrs-new-clauses`.  We do not need the explicit form of `tail`;
  -- just its existence is enough for the satisfies-split.
  clauses-after-instrs-extends
    : ∀ {hc} (is : List Instruction) (st : SynthState)
    → Σ-syntax (List Clause) λ tail →
        SynthState.clauses (circuit-instrs hc is st)
          ≡ SynthState.clauses st ++ tail
  clauses-after-instrs-extends []       st =
    [] , sym (++-identityʳ _)
  clauses-after-instrs-extends {hc} (i ∷ is) st =
    let head-new      = instr-new-clauses hc st i
        st₁           = circuit-instr hc i st
        head-eq       = clauses-after-instr-eq {hc} i st
        tail , tl-eq  = clauses-after-instrs-extends {hc} is st₁
        combined-eq   : SynthState.clauses (circuit-instrs hc is st₁)
                      ≡ SynthState.clauses st ++ (head-new ++ tail)
        combined-eq   = trans tl-eq
                          (trans (cong (_++ tail) head-eq)
                                 (++-assoc (SynthState.clauses st) head-new tail))
    in head-new ++ tail , combined-eq

------------------------------------------------------------------------
-- Helpers for D2's cons-case discharge (Path B).
--
-- These are mechanical 26-case lemmas isolated from the cons-case body
-- to keep its presentation clean.  All proofs are concrete `refl`-
-- driven case analyses (no postulates).
------------------------------------------------------------------------

private
  -- nr-wires after a single instruction = nr-wires before + Δmem.
  -- Proved by case analysis on the instruction.  Each case is `refl`
  -- because `circuit-instr` updates `nr-wires` as exactly
  -- `nr-wires st + Δmem i`, but spelled with explicit `+1`/`+2`
  -- shorthands rather than `+ Δmem i`.  We bridge via `+1-suc`/`+2-ss`.
  nr-wires-step : ∀ {hc} (i : Instruction) (st : SynthState)
    → SynthState.nr-wires (circuit-instr hc i st)
      ≡ SynthState.nr-wires st + Δmem i
  nr-wires-step (assert _)                 st = sym (+-identityʳ _)
  nr-wires-step (constrain-bits _ _)       st = sym (+-identityʳ _)
  nr-wires-step (constrain-eq _ _)         st = sym (+-identityʳ _)
  nr-wires-step (constrain-to-boolean _)   st = sym (+-identityʳ _)
  nr-wires-step (declare-pub-input _)      st = sym (+-identityʳ _)
  nr-wires-step (pi-skip _ _)              st = sym (+-identityʳ _)
  nr-wires-step (output _)                 st = sym (+-identityʳ _)
  nr-wires-step (cond-select _ _ _)        st = refl
  nr-wires-step (copy _)                   st = refl
  nr-wires-step (load-imm _)               st = refl
  nr-wires-step (reconstitute-field _ _ _) st = refl
  nr-wires-step (transient-hash _)         st = refl
  nr-wires-step (test-eq _ _)              st = refl
  nr-wires-step (add _ _)                  st = refl
  nr-wires-step (mul _ _)                  st = refl
  nr-wires-step (neg _)                    st = refl
  nr-wires-step (not _)                    st = refl
  nr-wires-step (less-than _ _ _)          st = refl
  nr-wires-step (public-input nothing)     st = refl
  nr-wires-step (public-input (just _))    st = refl
  nr-wires-step (private-input nothing)    st = refl
  nr-wires-step (private-input (just _))   st = refl
  nr-wires-step (ec-add _ _ _ _)           st = refl
  nr-wires-step (ec-mul _ _ _)             st = refl
  nr-wires-step (ec-mul-generator _)       st = refl
  nr-wires-step (hash-to-curve _)          st = refl
  nr-wires-step (persistent-hash _ _)      st = refl
  nr-wires-step (div-mod-power-of-two _ _) st = refl

  -- O2-check extraction.  From `O2-step i (n , bk) ≡ just acc'`
  -- recover `O2-check i bk ≡ just bk`.  Mechanical case analysis on `i`.
  --
  -- The four obligation cases (`assert`, `not`, `cond-select`) split
  -- on `mem? c bk`:  the `true` branch gives `O2-check i bk ≡ just bk`
  -- directly; the `false` branch makes `O2-step ≡ nothing`, contradicting
  -- `eq`.  All other 23 cases unfold to `O2-check i bk = just bk` and
  -- the result is `refl`.
  o2-check-from-step
    : ∀ (i : Instruction) {n : ℕ} (bk : IndexSet) {acc'}
    → O2-step i (n , bk) ≡ just acc'
    → O2-check i bk ≡ just bk
  o2-check-from-step (assert c) {n} bk eq with mem? c bk
  ... | true  = refl
  ... | false with eq
  ...            | ()
  o2-check-from-step (not a) {n} bk eq with mem? a bk
  ... | true  = refl
  ... | false with eq
  ...            | ()
  o2-check-from-step (cond-select b _ _) {n} bk eq with mem? b bk
  ... | true  = refl
  ... | false with eq
  ...            | ()
  o2-check-from-step (constrain-bits _ _)     bk eq = refl
  o2-check-from-step (constrain-eq _ _)       bk eq = refl
  o2-check-from-step (constrain-to-boolean _) bk eq = refl
  o2-check-from-step (copy _)                 bk eq = refl
  o2-check-from-step (declare-pub-input _)    bk eq = refl
  o2-check-from-step (pi-skip _ _)            bk eq = refl
  o2-check-from-step (ec-add _ _ _ _)         bk eq = refl
  o2-check-from-step (ec-mul _ _ _)           bk eq = refl
  o2-check-from-step (ec-mul-generator _)     bk eq = refl
  o2-check-from-step (hash-to-curve _)        bk eq = refl
  o2-check-from-step (load-imm _)             bk eq = refl
  o2-check-from-step (div-mod-power-of-two _ _) bk eq = refl
  o2-check-from-step (reconstitute-field _ _ _) bk eq = refl
  o2-check-from-step (output _)               bk eq = refl
  o2-check-from-step (transient-hash _)       bk eq = refl
  o2-check-from-step (persistent-hash _ _)    bk eq = refl
  o2-check-from-step (test-eq _ _)            bk eq = refl
  o2-check-from-step (add _ _)                bk eq = refl
  o2-check-from-step (mul _ _)                bk eq = refl
  o2-check-from-step (neg _)                  bk eq = refl
  o2-check-from-step (less-than _ _ _)        bk eq = refl
  o2-check-from-step (public-input _)         bk eq = refl
  o2-check-from-step (private-input _)        bk eq = refl

  -- O3-check extraction:  from `O3-step i (n , bm) ≡ just acc'`
  -- derive `O3-check i bm ≡ true`.  `O3-step` is defined as
  -- `if O3-check i bm then just (...) else nothing`.
  o3-check-from-step
    : ∀ (i : Instruction) {n : ℕ} (bm : PartialMap) {acc'}
    → O3-step i (n , bm) ≡ just acc'
    → O3-check i bm ≡ true
  o3-check-from-step i bm eq with O3-check i bm
  ... | true  = refl
  ... | false with eq
  ...            | ()

  ------------------------------------------------------------------------
  -- H6 helpers — uniform length-based mem-inv builders.
  --
  -- Given `length mem-suf ≡ k`, refine the suffix into its canonical
  -- shape and produce the post-state mem-inv arithmetic.
  ------------------------------------------------------------------------

  -- Δmem = 0: mem-suf = [].
  mem-inv-add-0 : ∀ (st : SynthState) (mem : List Fr)
    → (mem-suf : List Fr)
    → length mem-suf ≡ 0
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 0 ≡ length (mem ++ mem-suf)
  mem-inv-add-0 st mem []        refl mi =
    trans (+-identityʳ (SynthState.nr-wires st))
          (trans mi (sym (cong length (++-identityʳ mem))))
  mem-inv-add-0 _  _  (_ ∷ _)    ()   _

  -- Δmem = 1: mem-suf = w ∷ [].
  mem-inv-add-1 : ∀ (st : SynthState) (mem : List Fr)
    → (mem-suf : List Fr)
    → length mem-suf ≡ 1
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 1 ≡ length (mem ++ mem-suf)
  mem-inv-add-1 _ _ []                       ()  _
  mem-inv-add-1 st mem (w ∷ [])              refl mi =
    mem-inv-step-1 {st = st} {mem = mem} {v = w} mi
  mem-inv-add-1 _ _ (_ ∷ _ ∷ _)              ()  _

  -- Δmem = 2: mem-suf = x ∷ y ∷ [].
  mem-inv-add-2 : ∀ (st : SynthState) (mem : List Fr)
    → (mem-suf : List Fr)
    → length mem-suf ≡ 2
    → SynthState.nr-wires st ≡ length mem
    → SynthState.nr-wires st + 2 ≡ length (mem ++ mem-suf)
  mem-inv-add-2 _ _ []                         ()  _
  mem-inv-add-2 _ _ (_ ∷ [])                   ()  _
  mem-inv-add-2 st mem (x ∷ y ∷ [])            refl mi =
    mem-inv-step-2 {st = st} {mem = mem} {x = x} {y = y} mi
  mem-inv-add-2 _ _ (_ ∷ _ ∷ _ ∷ _)            ()  _

  -- pis: pis-suf = [].
  pi-inv-add-0 : ∀ (hc : Bool) (st : SynthState) (pis : List Fr)
    → (pis-suf : List Fr)
    → length pis-suf ≡ 0
    → length pis ≡ preamble-pi-count hc + SynthState.nr-declared-pi st
    → length (pis ++ pis-suf) ≡ preamble-pi-count hc + SynthState.nr-declared-pi st
  pi-inv-add-0 _ _ pis []        refl pii =
    trans (cong length (++-identityʳ pis)) pii
  pi-inv-add-0 _ _ _   (_ ∷ _)   ()   _

  -- pis: pis-suf = wv ∷ []; account for the +1 in nr-declared-pi.
  pi-inv-add-1-declare : ∀ (hc : Bool) (st : SynthState) (pis : List Fr)
    → (pis-suf : List Fr)
    → length pis-suf ≡ 1
    → length pis ≡ preamble-pi-count hc + SynthState.nr-declared-pi st
    → length (pis ++ pis-suf)
      ≡ preamble-pi-count hc + suc (SynthState.nr-declared-pi st)
  pi-inv-add-1-declare _  _  _   []              ()   _
  pi-inv-add-1-declare hc st pis (wv ∷ [])       refl pii =
    trans (length-++-1 pis wv)
          (trans (cong suc pii)
                 (sym (+-suc (preamble-pi-count hc)
                              (SynthState.nr-declared-pi st))))
  pi-inv-add-1-declare _  _  _   (_ ∷ _ ∷ _)     ()   _

  ------------------------------------------------------------------------
  -- consume-pub-out / consume-priv preserve memory and pis fields.
  -- These are needed for the public-input/private-input active branches
  -- of `next-state-from-osd`.
  ------------------------------------------------------------------------

  consume-pub-out-mem : ∀ (s : Preprocessed) {v s₁}
    → consume-pub-out s ≡ just (v , s₁)
    → Preprocessed.memory s₁ ≡ Preprocessed.memory s
  consume-pub-out-mem s eq with Preprocessed.pub-out-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | refl = refl

  consume-pub-out-pis : ∀ (s : Preprocessed) {v s₁}
    → consume-pub-out s ≡ just (v , s₁)
    → Preprocessed.pis s₁ ≡ Preprocessed.pis s
  consume-pub-out-pis s eq with Preprocessed.pub-out-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | refl = refl

  consume-priv-mem : ∀ (s : Preprocessed) {v s₁}
    → consume-priv s ≡ just (v , s₁)
    → Preprocessed.memory s₁ ≡ Preprocessed.memory s
  consume-priv-mem s eq with Preprocessed.priv-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | refl = refl

  consume-priv-pis : ∀ (s : Preprocessed) {v s₁}
    → consume-priv s ≡ just (v , s₁)
    → Preprocessed.pis s₁ ≡ Preprocessed.pis s
  consume-priv-pis s eq with Preprocessed.priv-rem s | eq
  ... | []    | ()
  ... | _ ∷ _ | refl = refl

  ------------------------------------------------------------------------
  -- H6 (mem-inv-next): the memory-length invariant is preserved by one
  -- step of the operational/circuit composition, given a well-shaped
  -- memory suffix.
  --
  -- Each case mirrors the matching clause of `next-state-from-osd` (and
  -- of `circuit-instr`).  The "shape" hypothesis `length mem-suf ≡ Δmem i`
  -- forces the suffix into its canonical form via the H6-helper lemmas.
  --
  -- The "fallback" combinations (instruction with the wrong mem-suf
  -- length) are absurd by the shape hypothesis.
  ------------------------------------------------------------------------

  -- Δmem=1 standard "push-mem" cases (memory grows by 1 ∷ ; pis stays).
  mem-inv-next-push1 : ∀ (st : SynthState) (s : Preprocessed)
                          (mem-suf : List Fr)
    → length mem-suf ≡ 1
    → mem-inv s st
    → SynthState.nr-wires st + 1
      ≡ length (Preprocessed.memory s ++ mem-suf)
  mem-inv-next-push1 st s mem-suf lh mi =
    mem-inv-add-1 st (Preprocessed.memory s) mem-suf lh mi

  -- Δmem=2 standard "push-mem2" cases.
  mem-inv-next-push2 : ∀ (st : SynthState) (s : Preprocessed)
                          (mem-suf : List Fr)
    → length mem-suf ≡ 2
    → mem-inv s st
    → SynthState.nr-wires st + 2
      ≡ length (Preprocessed.memory s ++ mem-suf)
  mem-inv-next-push2 st s mem-suf lh mi =
    mem-inv-add-2 st (Preprocessed.memory s) mem-suf lh mi

  -- Δmem=0 with memory unchanged.
  mem-inv-next-noop : ∀ (st : SynthState) (s : Preprocessed)
                          (mem-suf : List Fr)
    → length mem-suf ≡ 0
    → mem-inv s st
    → SynthState.nr-wires st + 0
      ≡ length (Preprocessed.memory s ++ mem-suf)
  mem-inv-next-noop st s mem-suf lh mi =
    mem-inv-add-0 st (Preprocessed.memory s) mem-suf lh mi

  ------------------------------------------------------------------------
  -- H5  —  the new clauses emitted by `circuit-instr hc i st` fit
  -- in the post-state pis (`length pis-suf` cells extension).
  --
  -- For every instruction except `declare-pub-input`, the new clauses
  -- mention no pis (so `clauses-pis-fit` is trivially `true`).
  -- For `declare-pub-input v`, the only new clause is
  -- `clause-pi-from-wire (preamble-pi-count hc + nr-declared-pi st) v`;
  -- with `pi-inv`, the entry is `≡ length (pis s)`, hence
  -- `entry <ᵇ length (pis s ++ pis-suf)` once `length pis-suf ≡ 1`.
  ------------------------------------------------------------------------

  -- Inlined refl-on-ℕ-≤, since `≤-refl′` is defined in a later block.
  ≤-refl-loc : ∀ {m} → m Data.Nat.≤ m
  ≤-refl-loc {zero}  = Data.Nat.z≤n
  ≤-refl-loc {suc m} = Data.Nat.s≤s ≤-refl-loc

  -- Local ∧-combine.
  ∧tt-loc : ∀ {x y} → x ≡ true → y ≡ true → (x ∧ y) ≡ true
  ∧tt-loc refl refl = refl

  -- For any `n`, `n <ᵇ suc n ≡ true`.  (Equivalent to `n<ᵇn+1` but in
  -- the form that matches `length pis = entry` ⇒ `entry <ᵇ suc (length pis)`.)
  n<ᵇsucn : ∀ n → (n <ᵇ suc n) ≡ true
  n<ᵇsucn n with suc n Data.Nat.≤? suc n
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p ≤-refl-loc)

  -- Δpis is 1 for `declare-pub-input` and 0 for every other instruction.
  Δpis-of : Instruction → ℕ
  Δpis-of (declare-pub-input _) = 1
  Δpis-of _                     = 0

  -- Auxiliary:  if `length pis-s ≡ entry` and `length pis-suf ≡ 1`,
  -- then `length (pis-s ++ pis-suf) ≡ suc entry`.
  pis-len-succ
    : ∀ (pis-s : List Fr) (pis-suf : List Fr) (entry : ℕ)
    → length pis-suf ≡ 1
    → length pis-s ≡ entry
    → length (pis-s ++ pis-suf) ≡ suc entry
  pis-len-succ _      []              _     ()   _
  pis-len-succ pis-s  (w ∷ [])        entry refl eq =
    trans (length-++-1 pis-s w) (cong suc eq)
  pis-len-succ _      (_ ∷ _ ∷ _)     _     ()   _

  clauses-pis-fit-instr
    : ∀ (hc : Bool) (st : SynthState) (s : Preprocessed) (i : Instruction)
        (pis-suf : List Fr)
    → length pis-suf ≡ Δpis-of i
    → length (Preprocessed.pis s)
        ≡ preamble-pi-count hc + SynthState.nr-declared-pi st
    → clauses-pis-fit (instr-new-clauses hc st i)
                       (length (Preprocessed.pis s ++ pis-suf))
      ≡ true
  -- All but `declare-pub-input` emit clauses with no pi references.
  clauses-pis-fit-instr hc st s (assert c)               _ _ _ = refl
  clauses-pis-fit-instr hc st s (cond-select _ _ _)      _ _ _ = refl
  clauses-pis-fit-instr hc st s (constrain-bits _ _)     _ _ _ = refl
  clauses-pis-fit-instr hc st s (constrain-eq _ _)       _ _ _ = refl
  clauses-pis-fit-instr hc st s (constrain-to-boolean _) _ _ _ = refl
  clauses-pis-fit-instr hc st s (copy _)                 _ _ _ = refl
  clauses-pis-fit-instr hc st s (pi-skip _ _)            _ _ _ = refl
  clauses-pis-fit-instr hc st s (output _)               _ _ _ = refl
  clauses-pis-fit-instr hc st s (ec-add _ _ _ _)         _ _ _ = refl
  clauses-pis-fit-instr hc st s (ec-mul _ _ _)           _ _ _ = refl
  clauses-pis-fit-instr hc st s (ec-mul-generator _)     _ _ _ = refl
  clauses-pis-fit-instr hc st s (hash-to-curve _)        _ _ _ = refl
  clauses-pis-fit-instr hc st s (load-imm _)             _ _ _ = refl
  clauses-pis-fit-instr hc st s (div-mod-power-of-two _ _) _ _ _ = refl
  clauses-pis-fit-instr hc st s (reconstitute-field _ _ _) _ _ _ = refl
  clauses-pis-fit-instr hc st s (transient-hash _)       _ _ _ = refl
  clauses-pis-fit-instr hc st s (persistent-hash _ _)    _ _ _ = refl
  clauses-pis-fit-instr hc st s (test-eq _ _)            _ _ _ = refl
  clauses-pis-fit-instr hc st s (add _ _)                _ _ _ = refl
  clauses-pis-fit-instr hc st s (mul _ _)                _ _ _ = refl
  clauses-pis-fit-instr hc st s (neg _)                  _ _ _ = refl
  clauses-pis-fit-instr hc st s (not _)                  _ _ _ = refl
  clauses-pis-fit-instr hc st s (less-than _ _ _)        _ _ _ = refl
  clauses-pis-fit-instr hc st s (public-input nothing)   _ _ _ = refl
  clauses-pis-fit-instr hc st s (public-input (just _))  _ _ _ = refl
  clauses-pis-fit-instr hc st s (private-input nothing)  _ _ _ = refl
  clauses-pis-fit-instr hc st s (private-input (just _)) _ _ _ = refl
  -- declare-pub-input: the entry index is `preamble-pi-count hc +
  -- nr-declared-pi st`.  By `pi-inv`, this equals `length (pis s)`.
  -- The post-state pis has length `length (pis s) + 1 = suc (length pis s)`.
  -- So `entry <ᵇ length (pis s ++ pis-suf) = entry <ᵇ suc entry ≡ true`.
  clauses-pis-fit-instr hc st s (declare-pub-input v) pis-suf lh pii =
    let entry  = preamble-pi-count hc + SynthState.nr-declared-pi st
        pis-s  = Preprocessed.pis s
        len-eq : length (pis-s ++ pis-suf) ≡ suc entry
        len-eq = pis-len-succ pis-s pis-suf entry lh pii
        ent< : (entry <ᵇ length (pis-s ++ pis-suf)) ≡ true
        ent< = subst (λ m → (entry <ᵇ m) ≡ true) (sym len-eq) (n<ᵇsucn entry)
    in ∧tt-loc ent< refl

  ------------------------------------------------------------------------
  -- H6 — mem-inv-next / pi-inv-next.
  --
  -- For each of the 26 instructions, given:
  --   • the shape hypotheses on `mem-suf` and `pis-suf`
  --     (`length mem-suf ≡ Δmem i`, `length pis-suf ≡ Δpis-of i`),
  --   • the pre-state invariants (`mem-inv s st`, `pi-inv hc s st`),
  -- the post-state invariants hold for
  -- `next-state-from-osd i pre s mem-suf pis-suf sd` and
  -- `circuit-instr hc i st`.
  --
  -- Each case mirrors the corresponding clause of `next-state-from-osd`.
  -- Ill-shaped combinations are absurd by the shape hypotheses.
  ------------------------------------------------------------------------

  mem-inv-next
    : ∀ {hc} (i : Instruction) (pre : ProofPreimage)
        (s : Preprocessed) (st : SynthState)
        (mem-suf pis-suf : List Fr)
        (sd : op-side-data i pre s mem-suf pis-suf)
    → mem-inv s st
    → length mem-suf ≡ Δmem i
    → length pis-suf ≡ Δpis-of i
    → mem-inv (next-state-from-osd i pre s mem-suf pis-suf sd)
              (circuit-instr hc i st)
  -- Δmem = 1, "push-mem" cases.
  mem-inv-next (add _ _)             _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (mul _ _)             _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (neg _)               _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (copy _)              _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (load-imm _)          _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (test-eq _ _)         _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (transient-hash _)    _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (cond-select _ _ _)   _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (not _)               _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (less-than _ _ _)     _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (reconstitute-field _ _ _) _ s st (w ∷ []) [] ((_ , refl) , _) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  -- Δmem = 2, "push-mem2" cases.
  mem-inv-next (ec-add _ _ _ _)      _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  mem-inv-next (ec-mul _ _ _)        _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  mem-inv-next (ec-mul-generator _)  _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  mem-inv-next (hash-to-curve _)     _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  mem-inv-next (persistent-hash _ _) _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  mem-inv-next (div-mod-power-of-two _ _) _ s st (x ∷ y ∷ []) [] ((_ , _ , refl) , _) mi refl refl =
    mem-inv-step-2 {st = st} {mem = Preprocessed.memory s} {x = x} {y = y} mi
  -- Δmem = 0, state unchanged.  `circuit-instr` for these does not
  -- bump `nr-wires`; the `next-state` for these has memory unchanged.
  mem-inv-next (constrain-eq _ _)      _ s st [] [] _ mi refl refl = mi
  mem-inv-next (constrain-bits _ _)    _ s st [] [] _ mi refl refl = mi
  mem-inv-next (constrain-to-boolean _) _ s st [] [] _ mi refl refl = mi
  mem-inv-next (assert _)              _ s st [] [] _ mi refl refl = mi
  -- declare-pub-input:  Δmem = 0; pis += wv (handled via record-update;
  -- memory unchanged).
  mem-inv-next (declare-pub-input _) _ s st [] (wv ∷ []) _ mi refl refl = mi
  -- output v:  Δmem = 0; memory unchanged.
  mem-inv-next (output _)            _ s st [] [] _ mi refl refl = mi
  -- pi-skip:  Δmem = 0; memory unchanged (regardless of `active`).
  mem-inv-next (pi-skip _ _)         _ s st [] [] (_ , _ , (true  , _ , _)) mi refl refl = mi
  mem-inv-next (pi-skip _ _)         _ s st [] [] (_ , _ , (false , _ , _)) mi refl refl = mi
  -- public-input / private-input:  Δmem = 1.  Active branch:
  --   next-state = record s₁ { memory = memory s₁ ++ (w ∷ []) }
  -- with `consume-pub-out s ≡ just (w, s₁)`, so `memory s₁ ≡ memory s`.
  -- Inactive branch: memory ++ (w ∷ []) directly.
  mem-inv-next (public-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) mi refl refl =
    let mem-s₁≡mem-s = consume-pub-out-mem s {v = w} {s₁ = s₁} cp
        step₁ : SynthState.nr-wires st + 1 ≡ length (Preprocessed.memory s ++ (w ∷ []))
        step₁ = mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
    in subst (λ m → SynthState.nr-wires st + 1 ≡ length (m ++ (w ∷ [])))
             (sym mem-s₁≡mem-s) step₁
  mem-inv-next (public-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) mi refl refl =
    let mem-s₁≡mem-s = consume-pub-out-mem s {v = w} {s₁ = s₁} cp
        step₁ : SynthState.nr-wires st + 1 ≡ length (Preprocessed.memory s ++ (w ∷ []))
        step₁ = mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
    in subst (λ m → SynthState.nr-wires st + 1 ≡ length (m ++ (w ∷ [])))
             (sym mem-s₁≡mem-s) step₁
  mem-inv-next (public-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (public-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (private-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) mi refl refl =
    let mem-s₁≡mem-s = consume-priv-mem s {v = w} {s₁ = s₁} cp
        step₁ : SynthState.nr-wires st + 1 ≡ length (Preprocessed.memory s ++ (w ∷ []))
        step₁ = mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
    in subst (λ m → SynthState.nr-wires st + 1 ≡ length (m ++ (w ∷ [])))
             (sym mem-s₁≡mem-s) step₁
  mem-inv-next (private-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) mi refl refl =
    let mem-s₁≡mem-s = consume-priv-mem s {v = w} {s₁ = s₁} cp
        step₁ : SynthState.nr-wires st + 1 ≡ length (Preprocessed.memory s ++ (w ∷ []))
        step₁ = mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
    in subst (λ m → SynthState.nr-wires st + 1 ≡ length (m ++ (w ∷ [])))
             (sym mem-s₁≡mem-s) step₁
  mem-inv-next (private-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi
  mem-inv-next (private-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) mi refl refl =
    mem-inv-step-1 {st = st} {mem = Preprocessed.memory s} {v = w} mi

  pi-inv-next
    : ∀ {hc} (i : Instruction) (pre : ProofPreimage)
        (s : Preprocessed) (st : SynthState)
        (mem-suf pis-suf : List Fr)
        (sd : op-side-data i pre s mem-suf pis-suf)
    → pi-inv hc s st
    → length mem-suf ≡ Δmem i
    → length pis-suf ≡ Δpis-of i
    → pi-inv hc (next-state-from-osd i pre s mem-suf pis-suf sd)
                (circuit-instr hc i st)
  -- All non-pi instructions:  pis unchanged in both next-state-from-osd
  -- and circuit-instr.  We feed `pii` (or a small length-rewrite for
  -- record-update preservations) directly.
  pi-inv-next (add _ _)              _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (mul _ _)              _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (neg _)                _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (copy _)               _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (load-imm _)           _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (test-eq _ _)          _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (transient-hash _)     _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (cond-select _ _ _)    _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (not _)                _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (less-than _ _ _)      _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (reconstitute-field _ _ _) _ s st (w ∷ []) [] _ pii refl refl = pii
  pi-inv-next (ec-add _ _ _ _)       _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (ec-mul _ _ _)         _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (ec-mul-generator _)   _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (hash-to-curve _)      _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (persistent-hash _ _)  _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (div-mod-power-of-two _ _) _ s st (x ∷ y ∷ []) [] _ pii refl refl = pii
  pi-inv-next (constrain-eq _ _)      _ s st [] [] _ pii refl refl = pii
  pi-inv-next (constrain-bits _ _)    _ s st [] [] _ pii refl refl = pii
  pi-inv-next (constrain-to-boolean _) _ s st [] [] _ pii refl refl = pii
  pi-inv-next (assert _)              _ s st [] [] _ pii refl refl = pii
  pi-inv-next (output _)              _ s st [] [] _ pii refl refl = pii
  pi-inv-next (pi-skip _ _)           _ s st [] [] (_ , _ , (true  , _ , _)) pii refl refl = pii
  pi-inv-next (pi-skip _ _)           _ s st [] [] (_ , _ , (false , _ , _)) pii refl refl = pii
  -- public-input / private-input: pis unchanged.  Active branch
  -- requires `pis s₁ ≡ pis s`.
  pi-inv-next (public-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) pii refl refl =
    subst (λ p → length p ≡ _) (sym (consume-pub-out-pis s {v = w} {s₁ = s₁} cp)) pii
  pi-inv-next (public-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) pii refl refl =
    subst (λ p → length p ≡ _) (sym (consume-pub-out-pis s {v = w} {s₁ = s₁} cp)) pii
  pi-inv-next (public-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) pii refl refl = pii
  pi-inv-next (public-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) pii refl refl = pii
  pi-inv-next (private-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) pii refl refl =
    subst (λ p → length p ≡ _) (sym (consume-priv-pis s {v = w} {s₁ = s₁} cp)) pii
  pi-inv-next (private-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (true , _ , (s₁ , cp))) pii refl refl =
    subst (λ p → length p ≡ _) (sym (consume-priv-pis s {v = w} {s₁ = s₁} cp)) pii
  pi-inv-next (private-input nothing) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) pii refl refl = pii
  pi-inv-next (private-input (just _)) _ s st (w ∷ []) [] (_ , refl , _ , (false , _ , _)) pii refl refl = pii
  -- declare-pub-input:  Δpis = 1; the post-state's nr-declared-pi is
  -- `suc (nr-declared-pi st)`; the post-state pis is `pis s ++ (wv ∷ [])`.
  pi-inv-next {hc} (declare-pub-input _) _ s st [] (wv ∷ []) (_ , _ , refl) pii refl refl =
    pi-inv-add-1-declare hc st (Preprocessed.pis s) (wv ∷ []) refl pii

------------------------------------------------------------------------
-- H1 / H2 / H3 — clauses-fit invariant along `circuit-instrs`.
--
-- Three pieces of infrastructure that together establish:
--
--   `clauses-mem-fit (clauses (circuit-instrs hc is st₀))
--                    (nr-wires (circuit-instrs hc is st₀)) ≡ true`
--
-- given an analogous fact on `st₀` and a `Wire-Trace`.  This is the
-- invariant that lets D2's cons case shrink the satisfies-clauses
-- witness back to the operationally-relevant memory at each step.
------------------------------------------------------------------------

private
  ------------------------------------------------------------------------
  -- H2  —  monotonicity of `_<ᵇ_`, `guard-ok?`, `all-lt?`,
  -- `clause-mem-fits`, and `clauses-mem-fit` along `n ↦ n + k`.
  ------------------------------------------------------------------------

  -- Inline `≤`-monotonicity:  if `m ≤ n` then `m ≤ n + k`.
  ≤-mono-+ʳ : ∀ {m n} k → m Data.Nat.≤ n → m Data.Nat.≤ n + k
  ≤-mono-+ʳ {.zero}    {n}     k Data.Nat.z≤n        = Data.Nat.z≤n
  ≤-mono-+ʳ {.(suc _)} {.(suc _)} k (Data.Nat.s≤s p) = Data.Nat.s≤s (≤-mono-+ʳ k p)

  -- The base monotonicity fact:  `_≤ᵇ_` is monotone in the right
  -- argument under right-addition.
  ≤ᵇ-mono-+ : ∀ m n k → (m ≤ᵇ n) ≡ true → (m ≤ᵇ (n + k)) ≡ true
  ≤ᵇ-mono-+ m n k h with m Data.Nat.≤? n | h
  ... | yes p | _  with m Data.Nat.≤? (n + k)
  ...                 | yes _  = refl
  ...                 | no  ¬q = ⊥-elim (¬q (≤-mono-+ʳ k p))
  ≤ᵇ-mono-+ m n k h | no _ | ()

  -- `_<ᵇ_` monotonicity under right-addition.  Immediate from
  -- `≤ᵇ-mono-+` since `a <ᵇ n = suc a ≤ᵇ n`.
  <ᵇ-mono-+ : ∀ a n k → (a <ᵇ n) ≡ true → (a <ᵇ (n + k)) ≡ true
  <ᵇ-mono-+ a n k h = ≤ᵇ-mono-+ (suc a) n k h

  -- `guard-ok?` is monotone:  `guard-ok? g n ≡ true → guard-ok? g (n+k) ≡ true`.
  guard-ok?-mono : ∀ (g : Maybe Index) n k
    → guard-ok? g n ≡ true → guard-ok? g (n + k) ≡ true
  guard-ok?-mono nothing  n k _ = refl
  guard-ok?-mono (just g) n k h = <ᵇ-mono-+ g n k h

  -- `all-lt?` is monotone:  `all-lt? is n ≡ true → all-lt? is (n+k) ≡ true`.
  all-lt?-mono : ∀ (is : List Index) n k
    → all-lt? is n ≡ true → all-lt? is (n + k) ≡ true
  all-lt?-mono []       n k _  = refl
  all-lt?-mono (i ∷ is) n k h  with ∧-≡-true-split h
  ... | h₁ , h₂ =
    ∧-≡-true-combine (<ᵇ-mono-+ i n k h₁) (all-lt?-mono is n k h₂)
    where
      -- Inline combine (we only need it locally; the canonical version
      -- exists nearby but not at this scope).
      ∧-≡-true-combine : ∀ {x y} → x ≡ true → y ≡ true → (x ∧ y) ≡ true
      ∧-≡-true-combine refl refl = refl

  -- Local `∧-≡-true-combine` available for the rest of the block.
  ∧tt : ∀ {x y} → x ≡ true → y ≡ true → (x ∧ y) ≡ true
  ∧tt refl refl = refl

  -- `clause-mem-fits cl n ≡ true → clause-mem-fits cl (n+k) ≡ true`.
  -- Single inductive case-split on the clause.
  clause-mem-fits-mono : ∀ (cl : Clause) n k
    → clause-mem-fits cl n ≡ true → clause-mem-fits cl (n + k) ≡ true
  clause-mem-fits-mono (clause-assert-non-zero c) n k h =
    <ᵇ-mono-+ c n k h
  clause-mem-fits-mono (clause-cond-select out b a c) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | hb   , h2 with ∧-≡-true-split h2
  ... | ha   , hc =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ b n k hb)
             (∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ c n k hc)))
  clause-mem-fits-mono (clause-range-bits v _) n k h = <ᵇ-mono-+ v n k h
  clause-mem-fits-mono (clause-eq a b) n k h
    with ∧-≡-true-split h
  ... | ha , hb = ∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ b n k hb)
  clause-mem-fits-mono (clause-bool v) n k h = <ᵇ-mono-+ v n k h
  clause-mem-fits-mono (clause-copy out v) n k h
    with ∧-≡-true-split h
  ... | hout , hv = ∧tt (<ᵇ-mono-+ out n k hout) (<ᵇ-mono-+ v n k hv)
  clause-mem-fits-mono (clause-ec-add cx cy ax ay bx by) n k h
    with ∧-≡-true-split h
  ... | hcx , h1 with ∧-≡-true-split h1
  ... | hcy , h2 with ∧-≡-true-split h2
  ... | hax , h3 with ∧-≡-true-split h3
  ... | hay , h4 with ∧-≡-true-split h4
  ... | hbx , hby =
    ∧tt (<ᵇ-mono-+ cx n k hcx)
        (∧tt (<ᵇ-mono-+ cy n k hcy)
             (∧tt (<ᵇ-mono-+ ax n k hax)
                  (∧tt (<ᵇ-mono-+ ay n k hay)
                       (∧tt (<ᵇ-mono-+ bx n k hbx)
                            (<ᵇ-mono-+ by n k hby)))))
  clause-mem-fits-mono (clause-ec-mul cx cy ax ay s) n k h
    with ∧-≡-true-split h
  ... | hcx , h1 with ∧-≡-true-split h1
  ... | hcy , h2 with ∧-≡-true-split h2
  ... | hax , h3 with ∧-≡-true-split h3
  ... | hay , hs =
    ∧tt (<ᵇ-mono-+ cx n k hcx)
        (∧tt (<ᵇ-mono-+ cy n k hcy)
             (∧tt (<ᵇ-mono-+ ax n k hax)
                  (∧tt (<ᵇ-mono-+ ay n k hay) (<ᵇ-mono-+ s n k hs))))
  clause-mem-fits-mono (clause-ec-mul-generator cx cy s) n k h
    with ∧-≡-true-split h
  ... | hcx , h1 with ∧-≡-true-split h1
  ... | hcy , hs =
    ∧tt (<ᵇ-mono-+ cx n k hcx)
        (∧tt (<ᵇ-mono-+ cy n k hcy) (<ᵇ-mono-+ s n k hs))
  clause-mem-fits-mono (clause-hash-to-curve cx cy inputs) n k h
    with ∧-≡-true-split h
  ... | hcx , h1 with ∧-≡-true-split h1
  ... | hcy , hin =
    ∧tt (<ᵇ-mono-+ cx n k hcx)
        (∧tt (<ᵇ-mono-+ cy n k hcy) (all-lt?-mono inputs n k hin))
  clause-mem-fits-mono (clause-load-imm out _) n k h = <ᵇ-mono-+ out n k h
  clause-mem-fits-mono (clause-div-mod q r v _) n k h
    with ∧-≡-true-split h
  ... | hq , h1 with ∧-≡-true-split h1
  ... | hr , hv =
    ∧tt (<ᵇ-mono-+ q n k hq)
        (∧tt (<ᵇ-mono-+ r n k hr) (<ᵇ-mono-+ v n k hv))
  clause-mem-fits-mono (clause-reconstitute out d m _) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | hd , hm =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ d n k hd) (<ᵇ-mono-+ m n k hm))
  clause-mem-fits-mono (clause-transient-hash out inputs) n k h
    with ∧-≡-true-split h
  ... | hout , hin =
    ∧tt (<ᵇ-mono-+ out n k hout) (all-lt?-mono inputs n k hin)
  clause-mem-fits-mono (clause-persistent-hash h₁ h₂ _ inputs) n k h
    with ∧-≡-true-split h
  ... | hh1 , h1 with ∧-≡-true-split h1
  ... | hh2 , hin =
    ∧tt (<ᵇ-mono-+ h₁ n k hh1)
        (∧tt (<ᵇ-mono-+ h₂ n k hh2) (all-lt?-mono inputs n k hin))
  clause-mem-fits-mono (clause-test-eq out a b) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | ha , hb =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ b n k hb))
  clause-mem-fits-mono (clause-add out a b) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | ha , hb =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ b n k hb))
  clause-mem-fits-mono (clause-mul out a b) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | ha , hb =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ b n k hb))
  clause-mem-fits-mono (clause-neg out a) n k h
    with ∧-≡-true-split h
  ... | hout , ha = ∧tt (<ᵇ-mono-+ out n k hout) (<ᵇ-mono-+ a n k ha)
  clause-mem-fits-mono (clause-not out a) n k h
    with ∧-≡-true-split h
  ... | hout , ha = ∧tt (<ᵇ-mono-+ out n k hout) (<ᵇ-mono-+ a n k ha)
  clause-mem-fits-mono (clause-less-than out a b _) n k h
    with ∧-≡-true-split h
  ... | hout , h1 with ∧-≡-true-split h1
  ... | ha , hb =
    ∧tt (<ᵇ-mono-+ out n k hout)
        (∧tt (<ᵇ-mono-+ a n k ha) (<ᵇ-mono-+ b n k hb))
  clause-mem-fits-mono (clause-guard-disj out i) n k h
    with ∧-≡-true-split h
  ... | hout , hi = ∧tt (<ᵇ-mono-+ out n k hout) (<ᵇ-mono-+ i n k hi)
  clause-mem-fits-mono (clause-pi-from-wire _ wire) n k h =
    <ᵇ-mono-+ wire n k h
  clause-mem-fits-mono (clause-comm-commitment inputs outputs) n k h
    with ∧-≡-true-split h
  ... | hin , hout =
    ∧tt (all-lt?-mono inputs n k hin) (all-lt?-mono outputs n k hout)

  -- The list-level monotonicity:  pointwise from `clause-mem-fits-mono`.
  clauses-mem-fits-mono : ∀ (cs : List Clause) n k
    → clauses-mem-fit cs n ≡ true → clauses-mem-fit cs (n + k) ≡ true
  clauses-mem-fits-mono []       n k _ = refl
  clauses-mem-fits-mono (c ∷ cs) n k h with ∧-≡-true-split h
  ... | hc , htl =
    ∧tt (clause-mem-fits-mono c n k hc) (clauses-mem-fits-mono cs n k htl)

  ------------------------------------------------------------------------
  -- H1  —  the new clauses emitted by `circuit-instr hc i st` fit in
  -- `nr-wires st + Δmem i`.  26-case proof.
  --
  -- The basic strategy in each case is:
  --   • extract each operand's `_<ᵇ nr-wires st` bound from `wire-check`;
  --   • lift it via `<ᵇ-mono-+` to `_<ᵇ nr-wires st + Δmem i`;
  --   • for the "new output wire" cases (`nr-wires st`, `suc (nr-wires st)`),
  --     use the explicit `_n<ᵇn+k_` facts below.
  --
  -- The Δmem=0 cases use `+-identityʳ` only via the `<ᵇ-mono-+ _ n 0`
  -- specialisation (which works definitionally with `k = 0`).
  ------------------------------------------------------------------------

  -- Reflexivity for `_≤_` on ℕ; inlined to avoid stdlib name juggling.
  ≤-refl′ : ∀ {m} → m Data.Nat.≤ m
  ≤-refl′ {zero}  = Data.Nat.z≤n
  ≤-refl′ {suc m} = Data.Nat.s≤s ≤-refl′

  -- `m ≤ suc m` — one-step weakening.
  ≤-step′ : ∀ {m} → m Data.Nat.≤ suc m
  ≤-step′ {zero}  = Data.Nat.z≤n
  ≤-step′ {suc m} = Data.Nat.s≤s ≤-step′

  -- Output-wire fit facts.
  n<ᵇn+1 : ∀ n → (n <ᵇ (n + 1)) ≡ true
  n<ᵇn+1 n  rewrite +1-suc n  with suc n Data.Nat.≤? suc n
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p ≤-refl′)

  n<ᵇn+2 : ∀ n → (n <ᵇ (n + 2)) ≡ true
  n<ᵇn+2 n  rewrite +2-ss n  with suc n Data.Nat.≤? suc (suc n)
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p ≤-step′)

  sn<ᵇn+2 : ∀ n → (suc n <ᵇ (n + 2)) ≡ true
  sn<ᵇn+2 n  rewrite +2-ss n  with suc (suc n) Data.Nat.≤? suc (suc n)
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p ≤-refl′)

  clauses-new-fit-step
    : ∀ (hc : Bool) (st : SynthState) (i : Instruction)
    → wire-check i (SynthState.nr-wires st) ≡ true
    → clauses-mem-fit (instr-new-clauses hc st i)
                      (SynthState.nr-wires st + Δmem i)
      ≡ true
  -- Δmem=0 cases (clauses use only existing wires; sometimes empty).
  clauses-new-fit-step hc st (assert c) wc =
    ∧tt (<ᵇ-mono-+ c (SynthState.nr-wires st) 0 wc) refl
  clauses-new-fit-step hc st (constrain-bits v bits) wc =
    ∧tt (<ᵇ-mono-+ v (SynthState.nr-wires st) 0 wc) refl
  clauses-new-fit-step hc st (constrain-eq a b) wc
    with ∧-≡-true-split wc
  ... | ha , hb =
    ∧tt (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 0 ha)
              (<ᵇ-mono-+ b (SynthState.nr-wires st) 0 hb))
         refl
  clauses-new-fit-step hc st (constrain-to-boolean v) wc =
    ∧tt (<ᵇ-mono-+ v (SynthState.nr-wires st) 0 wc) refl
  clauses-new-fit-step hc st (declare-pub-input v) wc =
    ∧tt (<ᵇ-mono-+ v (SynthState.nr-wires st) 0 wc) refl
  clauses-new-fit-step hc st (pi-skip g count) wc = refl
  clauses-new-fit-step hc st (output v) wc = refl
  -- Δmem=1 cases that introduce a new output wire at `nr-wires st`.
  clauses-new-fit-step hc st (cond-select b a c) wc
    with ∧-≡-true-split wc
  ... | hb , h1 with ∧-≡-true-split h1
  ... | ha , hcw =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ b (SynthState.nr-wires st) 1 hb)
                   (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 ha)
                        (<ᵇ-mono-+ c (SynthState.nr-wires st) 1 hcw))))
         refl
  clauses-new-fit-step hc st (copy v) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (<ᵇ-mono-+ v (SynthState.nr-wires st) 1 wc))
         refl
  clauses-new-fit-step hc st (load-imm imm) wc =
    ∧tt (n<ᵇn+1 (SynthState.nr-wires st)) refl
  clauses-new-fit-step hc st (reconstitute-field d m bits) wc
    with ∧-≡-true-split wc
  ... | hd , hm =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ d (SynthState.nr-wires st) 1 hd)
                   (<ᵇ-mono-+ m (SynthState.nr-wires st) 1 hm)))
         refl
  clauses-new-fit-step hc st (transient-hash inputs) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (all-lt?-mono inputs (SynthState.nr-wires st) 1 wc))
         refl
  clauses-new-fit-step hc st (test-eq a b) wc
    with ∧-≡-true-split wc
  ... | ha , hb =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 ha)
                   (<ᵇ-mono-+ b (SynthState.nr-wires st) 1 hb)))
         refl
  clauses-new-fit-step hc st (add a b) wc
    with ∧-≡-true-split wc
  ... | ha , hb =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 ha)
                   (<ᵇ-mono-+ b (SynthState.nr-wires st) 1 hb)))
         refl
  clauses-new-fit-step hc st (mul a b) wc
    with ∧-≡-true-split wc
  ... | ha , hb =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 ha)
                   (<ᵇ-mono-+ b (SynthState.nr-wires st) 1 hb)))
         refl
  clauses-new-fit-step hc st (neg a) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 wc))
         refl
  clauses-new-fit-step hc st (not a) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 wc))
         refl
  clauses-new-fit-step hc st (less-than a b bits) wc
    with ∧-≡-true-split wc
  ... | ha , hb =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (∧tt (<ᵇ-mono-+ a (SynthState.nr-wires st) 1 ha)
                   (<ᵇ-mono-+ b (SynthState.nr-wires st) 1 hb)))
         refl
  -- Δmem=1 cases with optional guard:  `public-input` / `private-input`.
  clauses-new-fit-step hc st (public-input nothing) wc = refl
  clauses-new-fit-step hc st (public-input (just g)) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (<ᵇ-mono-+ g (SynthState.nr-wires st) 1 wc))
         refl
  clauses-new-fit-step hc st (private-input nothing) wc = refl
  clauses-new-fit-step hc st (private-input (just g)) wc =
    ∧tt (∧tt (n<ᵇn+1 (SynthState.nr-wires st))
              (<ᵇ-mono-+ g (SynthState.nr-wires st) 1 wc))
         refl
  -- Δmem=2 cases that introduce two new output wires.
  clauses-new-fit-step hc st (ec-add ax ay bx by) wc
    with ∧-≡-true-split wc
  ... | hax , h1 with ∧-≡-true-split h1
  ... | hay , h2 with ∧-≡-true-split h2
  ... | hbx , hby =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (∧tt (<ᵇ-mono-+ ax (SynthState.nr-wires st) 2 hax)
                        (∧tt (<ᵇ-mono-+ ay (SynthState.nr-wires st) 2 hay)
                             (∧tt (<ᵇ-mono-+ bx (SynthState.nr-wires st) 2 hbx)
                                  (<ᵇ-mono-+ by (SynthState.nr-wires st) 2 hby))))))
         refl
  clauses-new-fit-step hc st (ec-mul ax ay s) wc
    with ∧-≡-true-split wc
  ... | hax , h1 with ∧-≡-true-split h1
  ... | hay , hs =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (∧tt (<ᵇ-mono-+ ax (SynthState.nr-wires st) 2 hax)
                        (∧tt (<ᵇ-mono-+ ay (SynthState.nr-wires st) 2 hay)
                             (<ᵇ-mono-+ s (SynthState.nr-wires st) 2 hs)))))
         refl
  clauses-new-fit-step hc st (ec-mul-generator s) wc =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (<ᵇ-mono-+ s (SynthState.nr-wires st) 2 wc)))
         refl
  clauses-new-fit-step hc st (hash-to-curve inputs) wc =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (all-lt?-mono inputs (SynthState.nr-wires st) 2 wc)))
         refl
  clauses-new-fit-step hc st (persistent-hash α inputs) wc =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (all-lt?-mono inputs (SynthState.nr-wires st) 2 wc)))
         refl
  clauses-new-fit-step hc st (div-mod-power-of-two v bits) wc =
    ∧tt (∧tt (n<ᵇn+2 (SynthState.nr-wires st))
              (∧tt (sn<ᵇn+2 (SynthState.nr-wires st))
                   (<ᵇ-mono-+ v (SynthState.nr-wires st) 2 wc)))
         refl

  ------------------------------------------------------------------------
  -- H3  —  the iterated invariant.
  --
  -- Given:
  --   • `clauses-mem-fit (clauses st₀) (nr-wires st₀) ≡ true`;
  --   • a `Wire-Trace is (nr-wires st₀) final-w` (which witnesses that
  --     every prefix passes `wire-check`).
  --
  -- Conclude that
  --   `clauses-mem-fit (clauses (circuit-instrs hc is st₀))
  --                    (nr-wires (circuit-instrs hc is st₀)) ≡ true`.
  --
  -- The induction step combines `clauses-after-instr-eq` (decomposes
  -- the post-step clauses), `nr-wires-step` (relates post- and pre-step
  -- `nr-wires`), and the two monotonicity lemmas.
  ------------------------------------------------------------------------

  -- Extract the head step's `wire-check ≡ true` from a `Wire-Trace`.
  -- We split on `wire-check i n`:  the `true` branch gives `refl`; the
  -- `false` branch makes `step` absurd (`nothing ≡ just _`).
  wire-trace-head-ok : ∀ {i is n final}
    → Wire-Trace (i ∷ is) n final
    → wire-check i n ≡ true
  wire-trace-head-ok {i = i} {n = n} (wire-cons step _)
    with wire-check i n
  ... | true  = refl

  -- Extract the tail `Wire-Trace` from the cons.  When `wire-check i n
  -- ≡ true`, `wire-step i n = just (n + Δmem i)`, so the cons's
  -- `step` equation forces `n' = n + Δmem i`.
  wire-trace-tail : ∀ {i is n final}
    → (wt : Wire-Trace (i ∷ is) n final)
    → Wire-Trace is (n + Δmem i) final
  wire-trace-tail {i = i} {n = n} (wire-cons step rest)
    with wire-check i n | step
  ... | true  | refl = rest

  -- ∧ combiner concatenated with `clauses-mem-fit-++`:  the fit of
  -- `xs ++ ys` at `n` decomposes into fit of `xs` at `n` and fit of
  -- `ys` at `n`.
  clauses-mem-fit-++
    : ∀ (xs ys : List Clause) n
    → clauses-mem-fit xs n ≡ true
    → clauses-mem-fit ys n ≡ true
    → clauses-mem-fit (xs ++ ys) n ≡ true
  clauses-mem-fit-++ []       ys n _   hy = hy
  clauses-mem-fit-++ (x ∷ xs) ys n hxy hy
    with ∧-≡-true-split hxy
  ... | hx , htl =
    ∧tt hx (clauses-mem-fit-++ xs ys n htl hy)

  clauses-st-fit-invariant
    : ∀ {hc} (st₀ : SynthState) (is : List Instruction)
      {final-w : ℕ}
    → clauses-mem-fit (SynthState.clauses st₀) (SynthState.nr-wires st₀)
        ≡ true
    → Wire-Trace is (SynthState.nr-wires st₀) final-w
    → clauses-mem-fit
        (SynthState.clauses (circuit-instrs hc is st₀))
        (SynthState.nr-wires (circuit-instrs hc is st₀))
      ≡ true
  -- Empty list:  `circuit-instrs hc [] st₀ = st₀`.
  clauses-st-fit-invariant {hc} st₀ [] base _ = base
  -- Cons:  recurse on the post-step state `circuit-instr hc i st₀`,
  -- threading the lifted base via `clauses-after-instr-eq`,
  -- `nr-wires-step`, `clauses-mem-fits-mono`, and `clauses-new-fit-step`.
  clauses-st-fit-invariant {hc} st₀ (i ∷ is) {final-w} base wt =
    let n₀ = SynthState.nr-wires st₀
        st₁ = circuit-instr hc i st₀
        n₁ = SynthState.nr-wires st₁
        -- Head's wire-check ≡ true.
        wc-head = wire-trace-head-ok wt
        -- Tail's wire trace at `n₀ + Δmem i`.
        wt-tail : Wire-Trace is (n₀ + Δmem i) final-w
        wt-tail = wire-trace-tail wt
        -- Reshape the tail's wire trace from `n₀ + Δmem i` to
        -- `nr-wires st₁`, using `nr-wires-step`.
        nw-eq : n₁ ≡ n₀ + Δmem i
        nw-eq = nr-wires-step {hc} i st₀
        wt-tail' : Wire-Trace is n₁ final-w
        wt-tail' = subst (λ m → Wire-Trace is m final-w) (sym nw-eq) wt-tail
        -- Prior clauses lifted to `n₀ + Δmem i`.
        prior-lift : clauses-mem-fit (SynthState.clauses st₀)
                                     (n₀ + Δmem i) ≡ true
        prior-lift = clauses-mem-fits-mono (SynthState.clauses st₀) n₀
                                           (Δmem i) base
        -- New head clauses fit in `n₀ + Δmem i`.
        new-fit : clauses-mem-fit (instr-new-clauses hc st₀ i)
                                  (n₀ + Δmem i) ≡ true
        new-fit = clauses-new-fit-step hc st₀ i wc-head
        -- Combined fit at `n₀ + Δmem i`.
        combined-at-n0+ : clauses-mem-fit
                            (SynthState.clauses st₀ ++ instr-new-clauses hc st₀ i)
                            (n₀ + Δmem i) ≡ true
        combined-at-n0+ = clauses-mem-fit-++
                            (SynthState.clauses st₀)
                            (instr-new-clauses hc st₀ i)
                            (n₀ + Δmem i)
                            prior-lift new-fit
        -- Rewrite combined fit at `n₁` using `nw-eq`.
        combined-at-n1 : clauses-mem-fit
                            (SynthState.clauses st₀ ++ instr-new-clauses hc st₀ i)
                            n₁ ≡ true
        combined-at-n1 =
          subst (λ m → clauses-mem-fit
                         (SynthState.clauses st₀ ++ instr-new-clauses hc st₀ i)
                         m ≡ true)
                (sym nw-eq) combined-at-n0+
        -- Rewrite the clause list using `clauses-after-instr-eq`.
        post-eq : SynthState.clauses st₁
                  ≡ SynthState.clauses st₀ ++ instr-new-clauses hc st₀ i
        post-eq = clauses-after-instr-eq {hc} i st₀
        base-at-st1 : clauses-mem-fit (SynthState.clauses st₁) n₁ ≡ true
        base-at-st1 = subst (λ cs → clauses-mem-fit cs n₁ ≡ true)
                            (sym post-eq) combined-at-n1
    in clauses-st-fit-invariant {hc} st₁ is base-at-st1 wt-tail'

------------------------------------------------------------------------
-- Shape extractors and the pis-fit list invariant.
--
-- `osd-mem-len` / `osd-pis-len`:  from a per-step `op-side-data`
-- payload recover the canonical suffix lengths
-- `length mem-step ≡ Δmem i` and `length pis-step ≡ Δpis-of i`.
-- These feed `mem-inv-next` / `pi-inv-next` / `clauses-pis-fit-instr`
-- in the D2 cons-case.  Each clause matches the shape Σ that
-- `op-side-data` pins for the instruction; matching the embedded
-- equalities as `refl` collapses the suffix to its canonical form so
-- the length is `refl`.
--
-- `clauses-pis-fit-invariant`:  the pis-side dual of
-- `clauses-st-fit-invariant`, maintaining
-- `clauses-pis-fit (clauses (circuit-instrs hc is st₀))
--                  (length (pis s')) ≡ true` along the trace.  Unlike
-- the mem-side invariant (bounded by the synthesis `nr-wires`), the
-- pis bound is the *running* `length (pis s)` of the operational
-- state; only `declare-pub-input` emits a pi-referencing clause, and
-- `clauses-pis-fit-instr` shows it fits once the step has appended its
-- pis cell.  The invariant is threaded through the `op-side-data-list`
-- structure so the per-step `pi-inv` and the suffix lengths are
-- available at each node.
------------------------------------------------------------------------

private
  -- Δmem suffix length from the side data.
  osd-mem-len
    : ∀ (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
        (ms ps : List Fr)
    → op-side-data i pre s ms ps
    → length ms ≡ Δmem i
  osd-mem-len (assert _)               _ _ _ _ (refl , _) = refl
  osd-mem-len (constrain-bits _ _)     _ _ _ _ (refl , _) = refl
  osd-mem-len (constrain-eq _ _)       _ _ _ _ (refl , _) = refl
  osd-mem-len (constrain-to-boolean _) _ _ _ _ (refl , _) = refl
  osd-mem-len (add _ _)                _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (mul _ _)                _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (neg _)                  _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (copy _)                 _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (load-imm _)             _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (test-eq _ _)            _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (transient-hash _)       _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (cond-select _ _ _)      _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (not _)                  _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (less-than _ _ _)        _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (reconstitute-field _ _ _) _ _ _ _ ((_ , refl) , _) = refl
  osd-mem-len (ec-add _ _ _ _)         _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (ec-mul _ _ _)           _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (ec-mul-generator _)     _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (hash-to-curve _)        _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (persistent-hash _ _)    _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (div-mod-power-of-two _ _) _ _ _ _ ((_ , _ , refl) , _) = refl
  osd-mem-len (declare-pub-input _)    _ _ _ _ (refl , _) = refl
  osd-mem-len (output _)               _ _ _ _ (_ , refl , _) = refl
  osd-mem-len (pi-skip _ _)            _ _ _ _ (refl , _) = refl
  osd-mem-len (public-input _)         _ _ _ _ (_ , refl , _) = refl
  osd-mem-len (private-input _)        _ _ _ _ (_ , refl , _) = refl

  -- Δpis suffix length from the side data.
  osd-pis-len
    : ∀ (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
        (ms ps : List Fr)
    → op-side-data i pre s ms ps
    → length ps ≡ Δpis-of i
  osd-pis-len (assert _)               _ _ _ _ (_ , refl) = refl
  osd-pis-len (constrain-bits _ _)     _ _ _ _ (_ , refl) = refl
  osd-pis-len (constrain-eq _ _)       _ _ _ _ (_ , refl) = refl
  osd-pis-len (constrain-to-boolean _) _ _ _ _ (_ , refl) = refl
  osd-pis-len (add _ _)                _ _ _ _ (_ , refl) = refl
  osd-pis-len (mul _ _)                _ _ _ _ (_ , refl) = refl
  osd-pis-len (neg _)                  _ _ _ _ (_ , refl) = refl
  osd-pis-len (copy _)                 _ _ _ _ (_ , refl) = refl
  osd-pis-len (load-imm _)             _ _ _ _ (_ , refl) = refl
  osd-pis-len (test-eq _ _)            _ _ _ _ (_ , refl) = refl
  osd-pis-len (transient-hash _)       _ _ _ _ (_ , refl) = refl
  osd-pis-len (cond-select _ _ _)      _ _ _ _ (_ , refl) = refl
  osd-pis-len (not _)                  _ _ _ _ (_ , refl) = refl
  osd-pis-len (less-than _ _ _)        _ _ _ _ (_ , refl) = refl
  osd-pis-len (reconstitute-field _ _ _) _ _ _ _ (_ , refl) = refl
  osd-pis-len (ec-add _ _ _ _)         _ _ _ _ (_ , refl) = refl
  osd-pis-len (ec-mul _ _ _)           _ _ _ _ (_ , refl) = refl
  osd-pis-len (ec-mul-generator _)     _ _ _ _ (_ , refl) = refl
  osd-pis-len (hash-to-curve _)        _ _ _ _ (_ , refl) = refl
  osd-pis-len (persistent-hash _ _)    _ _ _ _ (_ , refl) = refl
  osd-pis-len (div-mod-power-of-two _ _) _ _ _ _ (_ , refl) = refl
  osd-pis-len (declare-pub-input _)    _ _ _ _ (_ , _ , refl) = refl
  osd-pis-len (output _)               _ _ _ _ (_ , _ , refl) = refl
  osd-pis-len (pi-skip _ _)            _ _ _ _ (_ , refl , _) = refl
  osd-pis-len (public-input _)         _ _ _ _ (_ , _ , refl , _) = refl
  osd-pis-len (private-input _)        _ _ _ _ (_ , _ , refl , _) = refl

  -- pis-side list-level fit invariant, threaded through the operational
  -- trace structure.  At each node, `pi-inv` supplies the base index
  -- `length (pis s) ≡ preamble-pi-count hc + nr-declared-pi st`, which
  -- `clauses-pis-fit-instr` turns into the head-step fit at the
  -- *post-step* pis length; the prior clauses' fit is preserved because
  -- pis only ever grows (so a `clause-pis-fit cl n ≡ true` stays true at
  -- the larger length — proved by `clauses-pis-fit-mono` below).
  clause-pis-fit-mono : ∀ (cl : Clause) m n
    → m Data.Nat.≤ n
    → clause-pis-fit cl m ≡ true → clause-pis-fit cl n ≡ true
  clause-pis-fit-mono (clause-assert-non-zero _)       _ _ _ h = h
  clause-pis-fit-mono (clause-cond-select _ _ _ _)     _ _ _ h = h
  clause-pis-fit-mono (clause-range-bits _ _)          _ _ _ h = h
  clause-pis-fit-mono (clause-eq _ _)                  _ _ _ h = h
  clause-pis-fit-mono (clause-bool _)                  _ _ _ h = h
  clause-pis-fit-mono (clause-copy _ _)                _ _ _ h = h
  clause-pis-fit-mono (clause-ec-add _ _ _ _ _ _)      _ _ _ h = h
  clause-pis-fit-mono (clause-ec-mul _ _ _ _ _)        _ _ _ h = h
  clause-pis-fit-mono (clause-ec-mul-generator _ _ _)  _ _ _ h = h
  clause-pis-fit-mono (clause-hash-to-curve _ _ _)     _ _ _ h = h
  clause-pis-fit-mono (clause-load-imm _ _)            _ _ _ h = h
  clause-pis-fit-mono (clause-div-mod _ _ _ _)         _ _ _ h = h
  clause-pis-fit-mono (clause-reconstitute _ _ _ _)    _ _ _ h = h
  clause-pis-fit-mono (clause-transient-hash _ _)      _ _ _ h = h
  clause-pis-fit-mono (clause-persistent-hash _ _ _ _) _ _ _ h = h
  clause-pis-fit-mono (clause-test-eq _ _ _)           _ _ _ h = h
  clause-pis-fit-mono (clause-add _ _ _)               _ _ _ h = h
  clause-pis-fit-mono (clause-mul _ _ _)               _ _ _ h = h
  clause-pis-fit-mono (clause-neg _ _)                 _ _ _ h = h
  clause-pis-fit-mono (clause-not _ _)                 _ _ _ h = h
  clause-pis-fit-mono (clause-less-than _ _ _ _)       _ _ _ h = h
  clause-pis-fit-mono (clause-guard-disj _ _)          _ _ _ h = h
  clause-pis-fit-mono (clause-pi-from-wire entry _)    m n m≤n h =
    <ᵇ-≤-trans entry m n h m≤n
    where
      -- `entry <ᵇ m ≡ true` and `m ≤ n` imply `entry <ᵇ n ≡ true`.
      <ᵇ-≤-trans : ∀ a p q → (a <ᵇ p) ≡ true → p Data.Nat.≤ q → (a <ᵇ q) ≡ true
      <ᵇ-≤-trans a p q ha p≤q with suc a Data.Nat.≤? p
      ... | yes sa≤p with suc a Data.Nat.≤? q
      ...               | yes _   = refl
      ...               | no ¬sa≤q = ⊥-elim (¬sa≤q (Data.Nat.Properties.≤-trans sa≤p p≤q))
      <ᵇ-≤-trans a p q () p≤q | no _
  clause-pis-fit-mono (clause-comm-commitment _ _)     m n m≤n h =
    <ᵇ-≤-trans 1 m n h m≤n
    where
      <ᵇ-≤-trans : ∀ a p q → (a <ᵇ p) ≡ true → p Data.Nat.≤ q → (a <ᵇ q) ≡ true
      <ᵇ-≤-trans a p q ha p≤q with suc a Data.Nat.≤? p
      ... | yes sa≤p with suc a Data.Nat.≤? q
      ...               | yes _   = refl
      ...               | no ¬sa≤q = ⊥-elim (¬sa≤q (Data.Nat.Properties.≤-trans sa≤p p≤q))
      <ᵇ-≤-trans a p q () p≤q | no _

  clauses-pis-fit-mono : ∀ (cs : List Clause) m n
    → m Data.Nat.≤ n
    → clauses-pis-fit cs m ≡ true → clauses-pis-fit cs n ≡ true
  clauses-pis-fit-mono []       _ _ _   _ = refl
  clauses-pis-fit-mono (c ∷ cs) m n m≤n h with ∧-≡-true-split h
  ... | hc , htl =
    ∧tt-pis (clause-pis-fit-mono c m n m≤n hc)
            (clauses-pis-fit-mono cs m n m≤n htl)
    where
      ∧tt-pis : ∀ {x y} → x ≡ true → y ≡ true → (x ∧ y) ≡ true
      ∧tt-pis refl refl = refl

  clauses-pis-fit-++
    : ∀ (xs ys : List Clause) n
    → clauses-pis-fit xs n ≡ true
    → clauses-pis-fit ys n ≡ true
    → clauses-pis-fit (xs ++ ys) n ≡ true
  clauses-pis-fit-++ []       ys n _   hy = hy
  clauses-pis-fit-++ (x ∷ xs) ys n hxy hy with ∧-≡-true-split hxy
  ... | hx , htl = ∧tt-pis hx (clauses-pis-fit-++ xs ys n htl hy)
    where
      ∧tt-pis : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
      ∧tt-pis refl refl = refl

  -- `length xs ≤ length (xs ++ ys)`.
  len-≤-++ : ∀ (xs ys : List Fr) → length xs Data.Nat.≤ length (xs ++ ys)
  len-≤-++ []       ys = Data.Nat.z≤n
  len-≤-++ (x ∷ xs) ys = Data.Nat.s≤s (len-≤-++ xs ys)

  -- `length (xs ++ ys) ≡ length xs + length ys`.
  len-++ : ∀ (xs ys : List Fr) → length (xs ++ ys) ≡ length xs + length ys
  len-++ []       ys = refl
  len-++ (x ∷ xs) ys = cong suc (len-++ xs ys)

  -- First components of the per-step accumulators bump by `Δmem i`.
  o2-step-fst : ∀ (i : Instruction) {n bk acc'}
    → O2-step i (n , bk) ≡ just acc'
    → proj₁ acc' ≡ n + Δmem i
  o2-step-fst i {n} {bk} eq with O2-check i bk | eq
  ... | just _  | refl = refl
  ... | nothing | ()

  o3-step-fst : ∀ (i : Instruction) {n bm acc'}
    → O3-step i (n , bm) ≡ just acc'
    → proj₁ acc' ≡ n + Δmem i
  o3-step-fst i {n} {bm} eq with O3-check i bm | eq
  ... | true  | refl = refl
  ... | false | ()

  wire-step-fst : ∀ (i : Instruction) (n : ℕ) {n'}
    → wire-step i n ≡ just n'
    → n' ≡ n + Δmem i
  wire-step-fst i n eq with wire-check i n | eq
  ... | true  | refl = refl
  ... | false | ()

------------------------------------------------------------------------
-- D2  —  per-list backward dispatcher.
--
-- Refined signature (vs. the original sketch in 4a):
--
--   • the post-state `s` is now *existential* (mirrors D1), so the
--     dispatcher can rebuild it from the witness's mem/pis decomposition;
--   • the witness's memory is `memory s₀ ++ mem-suf` for an explicit
--     suffix `mem-suf` (and analogously for pis);
--   • `O2-Inv`, `O3-Inv`, `O2-Trace`, `O3-Trace`, `Wire-Trace` are
--     threaded as separate hypotheses (D3 will derive them from
--     `producer-safe src ≡ true`);
--   • `op-side-data-list`  is the structural trace that supplies the
--     per-step side data D1 needs for the four "side-data instructions".
--
-- The side-data list also decomposes `mem-suf` and `pis-suf` into
-- per-step pieces.
------------------------------------------------------------------------

-- Trace of per-step operational side data, jointly threading the
-- preprocessed-state evolution.  Each `osd-cons` provides:
--   • the side-data for the head instruction;
--   • the tail side-data list at the computed next state
--     (`next-state-from-osd i pre s mem-step pis-step sd`).
--
-- Path B (Option A):  the "next state" is no longer supplied by the
-- caller as an arbitrary `s'` with separate mem/pis equations — instead
-- it is computed by `next-state-from-osd` from the head instruction
-- and its side data.  This eliminates the reconciliation step in D2's
-- cons-case: D1's output and `next-state-from-osd ...` are
-- definitionally equal for each of the 26 instructions.
--
-- The list "linearises" the operational trace structure without
-- carrying the `R-instr` constructors themselves (which D2 reconstructs).
data op-side-data-list (pre : ProofPreimage) :
       (s : Preprocessed) (is : List Instruction)
       (mem-suf pis-suf : List Fr) → Set where
  osd-nil  : ∀ {s} → op-side-data-list pre s [] [] []
  osd-cons : ∀ {s i is mem-step pis-step mem-tail pis-tail}
    → (sd : op-side-data i pre s mem-step pis-step)
    → op-side-data-list pre
        (next-state-from-osd i pre s mem-step pis-step sd)
        is mem-tail pis-tail
    → op-side-data-list pre s (i ∷ is) (mem-step ++ mem-tail) (pis-step ++ pis-tail)

-- The endpoint reached by folding `next-state-from-osd` along an
-- `op-side-data-list`.  D2's existential output `s'` is provably this
-- fold (see the `fold-eq` field added to D2's result below); and a
-- `Tr-shaped` trace's endpoint index coincides with it too (since
-- `tr-next ≡ next-state-from-osd`).  This is the bridge that pins D2's
-- `s'` to the GIVEN state `s` in `circuit-faithful-bwd`.
osd-fold : ∀ {pre s is ms ps} → op-side-data-list pre s is ms ps → Preprocessed
osd-fold {s = s} osd-nil = s
osd-fold (osd-cons {i = i} {mem-step = mem-step} {pis-step = pis-step} sd rest) =
  osd-fold rest

-- D2 itself.
--
-- The four bool-traces and `O2-Inv` / `O3-Inv` are explicit so the
-- inductive step can refine them via `o2-step ≡ just _` / `o3-step ≡ just _`
-- and `o2-preserve` / `o3-preserve` (already proven).
--
-- Two clause-fit preconditions (`fit-mem`, `fit-pis`) are added vs. the
-- earlier sketch.  They state that the synthesis state's *current*
-- clauses fit in the memory / pis lengths reached so far.  They are
-- threaded inductively (each step's post-state fit is re-established by
-- `clauses-st-fit-invariant` / `clauses-pis-fit-instr`) and are
-- discharged trivially at the top-level call site (`circuit-faithful-bwd`),
-- where `st₀` is the initial synthesis state with `clauses ≡ []` (so both
-- fits are `refl`).
satisfies-clauses→R-instrs
  : ∀ {hc} (pre : ProofPreimage) (s₀ : Preprocessed)
    (is : List Instruction) (st₀ : SynthState)
    (mem-suf pis-suf : List Fr)
  → mem-inv s₀ st₀
  → pi-inv  hc s₀ st₀
  → clauses-mem-fit (SynthState.clauses st₀) (SynthState.nr-wires st₀) ≡ true
  → clauses-pis-fit (SynthState.clauses st₀) (length (Preprocessed.pis s₀)) ≡ true
  → ∀ {bk₀ : IndexSet} {bm₀ : PartialMap}
  → O2-Inv (SynthState.nr-wires st₀ , bk₀) s₀
  → O3-Inv (SynthState.nr-wires st₀ , bm₀) s₀
  → ∀ {final-o2 : ℕ × IndexSet} {final-o3 : ℕ × PartialMap} {final-w : ℕ}
  → O2-Trace is (SynthState.nr-wires st₀ , bk₀) final-o2
  → O3-Trace is (SynthState.nr-wires st₀ , bm₀) final-o3
  → Wire-Trace is (SynthState.nr-wires st₀) final-w
  → (osd : op-side-data-list pre s₀ is mem-suf pis-suf)
  → satisfies-clauses
      (SynthState.clauses (circuit-instrs hc is st₀))
      (mk-witness (Preprocessed.memory s₀ ++ mem-suf)
                  (Preprocessed.pis    s₀ ++ pis-suf)
                  (comm-rand-of pre))
  → Σ-syntax Preprocessed (λ s' →
        (Preprocessed.memory s' ≡ Preprocessed.memory s₀ ++ mem-suf)
      × (Preprocessed.pis    s' ≡ Preprocessed.pis    s₀ ++ pis-suf)
      × R-instrs pre s₀ is s'
      × (s' ≡ osd-fold osd))

-- Path B, cons-case, discharged.  The body inducts on the
-- `op-side-data-list` structure.  For `i ∷ is'` with
-- `osd-cons sd osd-tail`:
--
--   1. Peel the head step from the O2 / O3 / wire traces (constructor
--      match), recovering each per-step `*-step ≡ just acc'` and the
--      residual tail trace.
--   2. Establish the head's clause-fit facts at the post-step memory /
--      pis lengths (`clauses-st-fit-invariant` for mem,
--      `clauses-pis-fit-instr` + `clauses-pis-fit-mono`/`-++` for pis)
--      and shrink the satisfaction witness from the full
--      `mem-step ++ mem-tail` / `pis-step ++ pis-tail` down to just the
--      head's `mem-step` / `pis-step` (`satisfies-clauses-mem-shrink`,
--      `satisfies-clauses-pis-shrink`).  These fits are stated purely in
--      terms of `mem₀ ++ mem-step` / `pis₀ ++ pis-step` (no reference to
--      D1's output `s₁`), so there is no circular dependency on D1.
--   3. Apply D1 (`satisfies→R-instr-step`) to the shrunk head witness,
--      obtaining `s₁ = next-state-from-osd …`, `memory s₁ ≡ memory s₀ ++
--      mem-step`, `pis s₁ ≡ pis s₀ ++ pis-step`, and `R-instr pre s₀ i s₁`.
--   4. Advance the invariants to `s₁` (`mem-inv-next`, `pi-inv-next`,
--      `o2-preserve`, `o3-preserve`) and recurse on `is'` from `st₁`,
--      feeding the residual traces (re-indexed by `nr-wires-step` and the
--      per-step first-component bumps) and the full witness rewritten by
--      `++-assoc` so its memory / pis read as `memory s₁ ++ mem-tail` /
--      `pis s₁ ++ pis-tail`.
--   5. Assemble `R-instrs pre s₀ (i ∷ is') s'` with `r-step`, chaining
--      the memory / pis equations through `++-assoc`.

-- Empty list:  the witness's mem-suf and pis-suf are forced by
-- `osd-nil` to be `[]`.  Produce `r-done` and the trivial equations.
satisfies-clauses→R-instrs pre s₀ [] st₀ .[] .[]
                            mi pii fit-mem fit-pis _ _ _ _ _ osd-nil _ =
  s₀ , sym (++-identityʳ _) , sym (++-identityʳ _) , r-done , refl

-- Cons case.
satisfies-clauses→R-instrs {hc} pre s₀ (i ∷ is') st₀ ._ ._
    mi pii fit-mem fit-pis {bk₀} {bm₀} o2-inv o3-inv {final-o2} {final-o3} {final-w}
    (o2-step {acc' = o2acc'} o2se o2-tail)
    (o3-step {acc' = o3acc'} o3se o3-tail)
    (wire-cons {n' = wn'} wse w-tail)
    (osd-cons {mem-step = mem-step} {pis-step = pis-step}
              {mem-tail = mem-tail} {pis-tail = pis-tail} sd osd-tail)
    sat =
  let
    n₀  = SynthState.nr-wires st₀
    st₁ = circuit-instr hc i st₀
    n₁  = SynthState.nr-wires st₁
    mem₀ = Preprocessed.memory s₀
    pis₀ = Preprocessed.pis s₀

    -- Suffix length facts from the side data.
    ms-len : length mem-step ≡ Δmem i
    ms-len = osd-mem-len i pre s₀ mem-step pis-step sd
    ps-len : length pis-step ≡ Δpis-of i
    ps-len = osd-pis-len i pre s₀ mem-step pis-step sd

    -- Per-step obligation premises for D1.
    o2chk : O2-check i bk₀ ≡ just bk₀
    o2chk = o2-check-from-step i {n = n₀} bk₀ o2se
    o3chk : O3-check i bm₀ ≡ true
    o3chk = o3-check-from-step i {n = n₀} bm₀ o3se

    -- Head's wire-check from `wse : wire-step i n₀ ≡ just wn'`.
    wc : wire-check i n₀ ≡ true
    wc = proj₁ (wire-trace-head (wire-cons wse wire-done))

    -- `nr-wires` after the head step.
    nw-eq : n₁ ≡ n₀ + Δmem i
    nw-eq = nr-wires-step {hc} i st₀

    -- `length (mem₀ ++ mem-step) ≡ n₁`.
    len-mem-eq : length (mem₀ ++ mem-step) ≡ n₁
    len-mem-eq =
      trans (len-++ mem₀ mem-step)
        (trans (cong₂ _+_ (sym mi) ms-len) (sym nw-eq))

    -- mem-fit for `clauses st₁`, stated at `length (mem₀ ++ mem-step)`.
    fit-mem-st₁-nw : clauses-mem-fit (SynthState.clauses st₁) n₁ ≡ true
    fit-mem-st₁-nw =
      clauses-st-fit-invariant {hc} st₀ (i ∷ []) fit-mem
        (wire-cons wse wire-done)
    fit-mem-head : clauses-mem-fit (SynthState.clauses st₁)
                                   (length (mem₀ ++ mem-step)) ≡ true
    fit-mem-head = subst (λ k → clauses-mem-fit (SynthState.clauses st₁) k ≡ true)
                         (sym len-mem-eq) fit-mem-st₁-nw

    -- pis-fit for `clauses st₁`, stated at `length (pis₀ ++ pis-step)`.
    pis-le : length pis₀ Data.Nat.≤ length (pis₀ ++ pis-step)
    pis-le = len-≤-++ pis₀ pis-step
    fit-pis-prior : clauses-pis-fit (SynthState.clauses st₀)
                                    (length (pis₀ ++ pis-step)) ≡ true
    fit-pis-prior = clauses-pis-fit-mono (SynthState.clauses st₀)
                      (length pis₀) (length (pis₀ ++ pis-step)) pis-le fit-pis
    fit-pis-new : clauses-pis-fit (instr-new-clauses hc st₀ i)
                                  (length (pis₀ ++ pis-step)) ≡ true
    fit-pis-new = clauses-pis-fit-instr hc st₀ s₀ i pis-step ps-len pii
    fit-pis-head : clauses-pis-fit (SynthState.clauses st₁)
                                   (length (pis₀ ++ pis-step)) ≡ true
    fit-pis-head =
      subst (λ cs → clauses-pis-fit cs (length (pis₀ ++ pis-step)) ≡ true)
            (sym (clauses-after-instr-eq {hc} i st₀))
            (clauses-pis-fit-++ (SynthState.clauses st₀)
              (instr-new-clauses hc st₀ i) (length (pis₀ ++ pis-step))
              fit-pis-prior fit-pis-new)

    -- The full witness satisfies `clauses st₁` (split off the tail
    -- clauses), re-associated so the head suffix is exposed.
    sat-full-st₁ : satisfies-clauses (SynthState.clauses st₁)
        (mk-witness ((mem₀ ++ mem-step) ++ mem-tail)
                    ((pis₀ ++ pis-step) ++ pis-tail)
                    (comm-rand-of pre))
    sat-full-st₁ =
      let tail , tl-eq = clauses-after-instrs-extends {hc} is' st₁
          sat-decomp : satisfies-clauses (SynthState.clauses st₁ ++ tail)
                         (mk-witness (mem₀ ++ (mem-step ++ mem-tail))
                                     (pis₀ ++ (pis-step ++ pis-tail))
                                     (comm-rand-of pre))
          sat-decomp = subst (λ cs → satisfies-clauses cs _) tl-eq sat
      in subst₂ (λ m p → satisfies-clauses (SynthState.clauses st₁)
                           (mk-witness m p (comm-rand-of pre)))
                (sym (++-assoc mem₀ mem-step mem-tail))
                (sym (++-assoc pis₀ pis-step pis-tail))
                (proj₁ (satisfies-clauses-split (SynthState.clauses st₁)
                          tail sat-decomp))

    -- Shrink off the tail suffixes to obtain the head witness D1 wants.
    sat-head-mem : satisfies-clauses (SynthState.clauses st₁)
        (mk-witness (mem₀ ++ mem-step) ((pis₀ ++ pis-step) ++ pis-tail)
                    (comm-rand-of pre))
    sat-head-mem =
      satisfies-clauses-mem-shrink (SynthState.clauses st₁)
        (mem₀ ++ mem-step) mem-tail fit-mem-head sat-full-st₁
    sat-head : satisfies-clauses (SynthState.clauses st₁)
        (mk-witness (mem₀ ++ mem-step) (pis₀ ++ pis-step) (comm-rand-of pre))
    sat-head =
      satisfies-clauses-pis-shrink (SynthState.clauses st₁)
        (pis₀ ++ pis-step) pis-tail fit-pis-head sat-head-mem

    -- D1 applied to the head.
    s₁ = next-state-from-osd i pre s₀ mem-step pis-step sd
    d1-out :
        (Preprocessed.memory s₁ ≡ mem₀ ++ mem-step)
      × (Preprocessed.pis    s₁ ≡ pis₀ ++ pis-step)
      × R-instr pre s₀ i s₁
    d1-out = satisfies→R-instr-step {hc} pre s₀ i st₀ mem-step pis-step
               mi pii wc {bk = bk₀} {bm = bm₀} o2-inv o3-inv o2chk o3chk sd
               sat-head

    mem-eq₁ = proj₁ d1-out
    pis-eq₁ = proj₁ (proj₂ d1-out)
    r-head  = proj₂ (proj₂ d1-out)

    -- Post-step invariants for the recursion.
    mi₁ : mem-inv s₁ st₁
    mi₁ = mem-inv-next {hc} i pre s₀ st₀ mem-step pis-step sd mi ms-len ps-len
    pii₁ : pi-inv hc s₁ st₁
    pii₁ = pi-inv-next {hc} i pre s₀ st₀ mem-step pis-step sd pii ms-len ps-len

    -- The recorded O2 / O3 accumulators after the step, transported to `s₁`
    -- and re-indexed so the first component reads `n₁`.
    o2-fst : proj₁ o2acc' ≡ n₀ + Δmem i
    o2-fst = o2-step-fst i {n = n₀} {bk = bk₀} o2se
    o3-fst : proj₁ o3acc' ≡ n₀ + Δmem i
    o3-fst = o3-step-fst i {n = n₀} {bm = bm₀} o3se
    o2acc-eq : o2acc' ≡ (n₁ , proj₂ o2acc')
    o2acc-eq = cong (_, proj₂ o2acc') (trans o2-fst (sym nw-eq))
    o3acc-eq : o3acc' ≡ (n₁ , proj₂ o3acc')
    o3acc-eq = cong (_, proj₂ o3acc') (trans o3-fst (sym nw-eq))

    o2-inv₁ : O2-Inv (n₁ , proj₂ o2acc') s₁
    o2-inv₁ = subst (λ a → O2-Inv a s₁) o2acc-eq (o2-preserve o2-inv r-head o2se)
    o3-inv₁ : O3-Inv (n₁ , proj₂ o3acc') s₁
    o3-inv₁ = subst (λ a → O3-Inv a s₁) o3acc-eq (o3-preserve o3-inv r-head o3se)

    o2-tail₁ : O2-Trace is' (n₁ , proj₂ o2acc') final-o2
    o2-tail₁ = subst (λ a → O2-Trace is' a final-o2) o2acc-eq o2-tail
    o3-tail₁ : O3-Trace is' (n₁ , proj₂ o3acc') final-o3
    o3-tail₁ = subst (λ a → O3-Trace is' a final-o3) o3acc-eq o3-tail
    w-tail₁ : Wire-Trace is' n₁ final-w
    w-tail₁ = subst (λ k → Wire-Trace is' k final-w)
                (trans (wire-step-fst i n₀ wse) (sym nw-eq)) w-tail

    -- The full witness over `s₁`'s mem / pis plus the tails.
    sat-rec : satisfies-clauses
        (SynthState.clauses (circuit-instrs hc is' st₁))
        (mk-witness (Preprocessed.memory s₁ ++ mem-tail)
                    (Preprocessed.pis    s₁ ++ pis-tail)
                    (comm-rand-of pre))
    sat-rec =
      subst₂ (λ m p → satisfies-clauses
                        (SynthState.clauses (circuit-instrs hc is' st₁))
                        (mk-witness m p (comm-rand-of pre)))
             (sym (trans (cong (_++ mem-tail) mem-eq₁)
                         (++-assoc mem₀ mem-step mem-tail)))
             (sym (trans (cong (_++ pis-tail) pis-eq₁)
                         (++-assoc pis₀ pis-step pis-tail)))
             sat

    -- Recurse.
    fit-pis-rec : clauses-pis-fit (SynthState.clauses st₁)
                                  (length (Preprocessed.pis s₁)) ≡ true
    fit-pis-rec = subst (λ p → clauses-pis-fit (SynthState.clauses st₁)
                                 (length p) ≡ true)
                        (sym pis-eq₁) fit-pis-head

    -- Recurse.
    rec = satisfies-clauses→R-instrs {hc} pre s₁ is' st₁ mem-tail pis-tail
            mi₁ pii₁ fit-mem-st₁-nw fit-pis-rec
            {bk₀ = proj₂ o2acc'} {bm₀ = proj₂ o3acc'}
            o2-inv₁ o3-inv₁ o2-tail₁ o3-tail₁ w-tail₁ osd-tail sat-rec

    s'        = proj₁ rec
    mem-eq'   = proj₁ (proj₂ rec)
    pis-eq'   = proj₁ (proj₂ (proj₂ rec))
    r-tail    = proj₁ (proj₂ (proj₂ (proj₂ rec)))
    fold-eq'  = proj₂ (proj₂ (proj₂ (proj₂ rec)))
  in
    s'
    , trans mem-eq'
        (trans (cong (_++ mem-tail) mem-eq₁)
               (++-assoc mem₀ mem-step mem-tail))
    , trans pis-eq'
        (trans (cong (_++ pis-tail) pis-eq₁)
               (++-assoc pis₀ pis-step pis-tail))
    , r-step r-head r-tail
    -- `osd-fold (osd-cons sd osd-tail)` reduces to `osd-fold osd-tail`,
    -- which is `rec`'s fold endpoint.  But `rec` was taken at `s₁ =
    -- next-state-from-osd i …` whereas the osd-tail in THIS list is
    -- rooted at the same `s₁` — the two `osd-fold`s coincide definitionally.
    , fold-eq'

------------------------------------------------------------------------
-- Part 2′.  The transcript-consistency predicate `preprocess-shaped`.
--
-- The backward direction (`circuit-faithful-bwd`) over an *arbitrary*
-- `s : Preprocessed` is unprovable (see the SECOND BLOCKER note below)
-- because in-circuit satisfaction (`satisfies`) is *blind* to the
-- transcript-read wires: `public-input` / `private-input` emit no
-- clause for the value read off the transcript, and `pi-skip`'s
-- transcript-match check has no in-circuit shadow.  The spec (§5.4,
-- line 809) sidesteps this by quantifying `Σ` over "preprocess-state-
-- shaped assignments"; the predicate below is the Agda rendering of
-- that quantifier restriction.
--
-- `preprocess-shaped src pre s` asserts the existence of an operational
-- *shape* trace from the initial state to `s` in which:
--
--   • transcript-read instructions (`public-input` / `private-input`
--     when active, `pi-skip` when active) consume the preimage
--     transcripts in order and pass their guard / prefix-match checks;
--   • EVERY OTHER instruction merely appends some *free* memory / pis
--     cells of the correct arity — their VALUES are left UNCONSTRAINED.
--
-- Design notes.
--
--   • NON-VACUOUS / NON-CIRCULAR.  This is strictly WEAKER than
--     `R-instrs pre s₀ instrs s`: a `tr-step` for `add` / `mul` /
--     `ec-add` / `hash` / `declare-pub-input` / … pins only the
--     *length* of the appended suffix (`w ∷ []`, `x ∷ y ∷ []`), NEVER
--     the computed value (`av +ᶠ bv`, `ec-add-pts …`, …).  Those values
--     are pinned by `satisfies` via D1/D2.  So `satisfies` remains fully
--     load-bearing.  It does NOT hand back an `R-instrs` trace.
--
--   • IMPLEMENTATION-INDEPENDENT.  The predicate is stated purely in
--     `Semantics` vocabulary (`Preprocessed`, `mem-lookup`, `eval-guard`,
--     `consume-pub-out`, `consume-priv`, `≡ᶠ-list?`).  It mentions no
--     in-circuit construct (`SynthState`, clauses, `op-side-data`).
--
--   • STRONG ENOUGH.  The per-step `tr-step` payloads are arranged to
--     coincide *definitionally* with the corresponding `op-side-data`
--     payloads and `tr-next` with `next-state-from-osd`, so the internal
--     bridge converts a `Tr-shaped` trace to an `op-side-data-list`
--     structurally (two cases), supplying exactly the transcript gaps
--     D2 needs.
------------------------------------------------------------------------

-- Per-step shape obligation.  Mirrors `op-side-data` *exactly* (same
-- payload, in the same `Semantics` vocabulary) so that the conversion
-- to `op-side-data` in the internal bridge is the identity.
tr-step : Instruction → ProofPreimage → Preprocessed
        → (mem-suf pis-suf : List Fr) → Set
-- Δmem=0, Δpis=0 (no payload).
tr-step (assert _)               _ _ ms ps = (ms ≡ []) × (ps ≡ [])
tr-step (constrain-bits _ _)     _ _ ms ps = (ms ≡ []) × (ps ≡ [])
tr-step (constrain-eq _ _)       _ _ ms ps = (ms ≡ []) × (ps ≡ [])
tr-step (constrain-to-boolean _) _ _ ms ps = (ms ≡ []) × (ps ≡ [])
-- Δmem=1, Δpis=0 (push-mem cases) — value `w` is FREE.
tr-step (add _ _)                _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (mul _ _)                _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (neg _)                  _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (copy _)                 _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (load-imm _)             _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (test-eq _ _)            _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (transient-hash _)       _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (cond-select _ _ _)      _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (not _)                  _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (less-than _ _ _)        _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
tr-step (reconstitute-field _ _ _) _ _ ms ps = Σ-syntax Fr (λ w → ms ≡ w ∷ []) × (ps ≡ [])
-- Δmem=2, Δpis=0 (push-mem2 cases) — values `x`,`y` FREE.
tr-step (ec-add _ _ _ _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
tr-step (ec-mul _ _ _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
tr-step (ec-mul-generator _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
tr-step (hash-to-curve _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
tr-step (persistent-hash _ _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
tr-step (div-mod-power-of-two _ _) _ _ ms ps = Σ-syntax Fr (λ x → Σ-syntax Fr (λ y → ms ≡ x ∷ y ∷ [])) × (ps ≡ [])
-- Δmem=0, Δpis=1 (declare-pub-input) — value `wv` FREE.
tr-step (declare-pub-input _) _ _ ms ps = (ms ≡ []) × Σ-syntax Fr (λ wv → ps ≡ wv ∷ [])
-- ── Four side-data instructions (transcript-bearing) ──
tr-step (output v) _ s ms ps =
  Σ-syntax Fr (λ val → mem-lookup (Preprocessed.memory s) v ≡ just val)
  × (ms ≡ []) × (ps ≡ [])
tr-step (pi-skip g count) pre s ms ps =
  (ms ≡ []) × (ps ≡ [])
  × Σ-syntax Bool (λ active →
        eval-guard (Preprocessed.memory s) g ≡ just active
      × (if active
         then ((drop (length (Preprocessed.pis s) ∸ count) (Preprocessed.pis s)
                  ≡ᶠ-list?
                take count (drop (Preprocessed.pub-in-idx s ∸ count)
                                  (ProofPreimage.pub-transcript-inputs pre)))
                ≡ true)
         else ⊤))
tr-step (public-input g) pre s ms ps =
  Σ-syntax Fr (λ w → (ms ≡ w ∷ []) × (ps ≡ [])
    × Σ-syntax Bool (λ active →
          eval-guard (Preprocessed.memory s) g ≡ just active
        × (if active
           then Σ-syntax Preprocessed (λ s₁ → consume-pub-out s ≡ just (w , s₁))
           else (w ≡ 0ᶠ))))
tr-step (private-input g) pre s ms ps =
  Σ-syntax Fr (λ w → (ms ≡ w ∷ []) × (ps ≡ [])
    × Σ-syntax Bool (λ active →
          eval-guard (Preprocessed.memory s) g ≡ just active
        × (if active
           then Σ-syntax Preprocessed (λ s₁ → consume-priv s ≡ just (w , s₁))
           else (w ≡ 0ᶠ))))

-- Post-state computed from the step shape.  Mirrors `next-state-from-osd`
-- exactly, so that the bridge's index expressions coincide definitionally.
tr-next : (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
          (mem-suf pis-suf : List Fr) → tr-step i pre s mem-suf pis-suf → Preprocessed
tr-next (assert _)               _ s _ _ _ = s
tr-next (constrain-bits _ _)     _ s _ _ _ = s
tr-next (constrain-eq _ _)       _ s _ _ _ = s
tr-next (constrain-to-boolean _) _ s _ _ _ = s
tr-next (add _ _)                _ s _ _ ((w , _) , _) = push-mem s w
tr-next (mul _ _)                _ s _ _ ((w , _) , _) = push-mem s w
tr-next (neg _)                  _ s _ _ ((w , _) , _) = push-mem s w
tr-next (copy _)                 _ s _ _ ((w , _) , _) = push-mem s w
tr-next (load-imm _)             _ s _ _ ((w , _) , _) = push-mem s w
tr-next (test-eq _ _)            _ s _ _ ((w , _) , _) = push-mem s w
tr-next (transient-hash _)       _ s _ _ ((w , _) , _) = push-mem s w
tr-next (cond-select _ _ _)      _ s _ _ ((w , _) , _) = push-mem s w
tr-next (not _)                  _ s _ _ ((w , _) , _) = push-mem s w
tr-next (less-than _ _ _)        _ s _ _ ((w , _) , _) = push-mem s w
tr-next (reconstitute-field _ _ _) _ s _ _ ((w , _) , _) = push-mem s w
tr-next (ec-add _ _ _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (ec-mul _ _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (ec-mul-generator _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (hash-to-curve _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (persistent-hash _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (div-mod-power-of-two _ _) _ s _ _ ((x , y , _) , _) = push-mem2 s x y
tr-next (declare-pub-input _) _ s _ _ (_ , wv , _) =
  record s { pis        = Preprocessed.pis s ++ (wv ∷ [])
           ; pub-in-idx = suc (Preprocessed.pub-in-idx s) }
tr-next (output v) _ s _ _ ((val , _) , _ , _) =
  record s { outputs = Preprocessed.outputs s ++ (val ∷ []) }
tr-next (pi-skip _ _) _ s _ _ (_ , _ , (true  , _ , _)) =
  record s { pi-skips = Preprocessed.pi-skips s ++ (nothing ∷ []) }
tr-next (pi-skip _ count) _ s _ _ (_ , _ , (false , _ , _)) =
  record s { pi-skips   = Preprocessed.pi-skips s ++ (just count ∷ [])
           ; pub-in-idx = Preprocessed.pub-in-idx s ∸ count }
tr-next (public-input _) _ s _ _ (w , _ , _ , (true , _ , (s₁ , _))) =
  record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
tr-next (public-input _) _ s _ _ (w , _ , _ , (false , _ , _)) =
  record s { memory = Preprocessed.memory s ++ (w ∷ []) }
tr-next (private-input _) _ s _ _ (w , _ , _ , (true , _ , (s₁ , _))) =
  record s₁ { memory = Preprocessed.memory s₁ ++ (w ∷ []) }
tr-next (private-input _) _ s _ _ (w , _ , _ , (false , _ , _)) =
  record s { memory = Preprocessed.memory s ++ (w ∷ []) }

-- The list closure.  Structurally identical to `op-side-data-list` but
-- built from the clean `tr-step` / `tr-next` (which coincide
-- definitionally with `op-side-data` / `next-state-from-osd`), and
-- additionally ENDPOINT-INDEXED: `Tr-shaped pre s₀ is s ms ps` says the
-- shape walk from `s₀` over `is`, appending `ms` / `ps`, ends exactly at
-- `s`.  The endpoint index pins ALL of `s`'s fields (memory, pis, and the
-- transcript bookkeeping) — this is what the backward direction needs to
-- recover `R src pre s` for the GIVEN `s` (not merely a state with the
-- same memory/pis prefix).
data Tr-shaped (pre : ProofPreimage) :
       (s₀ : Preprocessed) (is : List Instruction) (s : Preprocessed)
       (mem-suf pis-suf : List Fr) → Set where
  tr-nil  : ∀ {s} → Tr-shaped pre s [] s [] []
  tr-cons : ∀ {s₀ i is s mem-step pis-step mem-tail pis-tail}
    → (sd : tr-step i pre s₀ mem-step pis-step)
    → Tr-shaped pre (tr-next i pre s₀ mem-step pis-step sd) is s mem-tail pis-tail
    → Tr-shaped pre s₀ (i ∷ is) s (mem-step ++ mem-tail) (pis-step ++ pis-tail)

-- The user-facing predicate: there is an initial state `s₀` and a shape
-- walk from `s₀` over the instruction stream that ends EXACTLY at `s`,
-- consuming the transcripts.  The suffixes are existential.
--
-- THIRD COMPONENT: `transcripts-consumed pre s ≡ true`.  The `Tr-shaped`
-- walk alone does NOT force the three transcript cursors of `s` to be
-- fully consumed (a walk in which every `public-input` / `private-input`
-- / `pi-skip` guard is inactive consumes nothing), and `satisfies` is
-- blind to the cursors (THIRD BLOCKER below).  Yet `R src pre s` carries
-- `transcripts-consumed pre s ≡ true` as a top-level conjunct
-- (Semantics.agda:632), so the backward direction must reproduce it.  It
-- is not derivable from `satisfies` + the trace + producer-safety
-- (none of O1/O2/O3/wire-disc constrains the transcript cursors), so —
-- exactly as with WF1 (part 1) and the transcript-read-wire blindness
-- (the trace) — it must be supplied.  This is faithful to the spec §5.4
-- "preprocess-state-shaped Σ": those states are reached by a SUCCESSFUL
-- `preprocess`, which by definition passed `transcripts-consumed`
-- (Semantics.agda:452).  `comm-ok` is NOT folded in here: it is genuinely
-- recoverable from `satisfies` (the `clause-comm-commitment` clause; see
-- part 4 below), so we leave it derived to keep `satisfies` load-bearing.
preprocess-shaped : IrSource → ProofPreimage → Preprocessed → Set
preprocess-shaped src pre s =
  Σ-syntax Preprocessed (λ s₀ →
    init-state src pre ≡ just s₀
  × Σ-syntax (List Fr) (λ mem-suf → Σ-syntax (List Fr) (λ pis-suf →
        Tr-shaped pre s₀ (IrSource.instructions src) s mem-suf pis-suf))
  × transcripts-consumed pre s ≡ true)

------------------------------------------------------------------------
-- `R ⇒ preprocess-shaped`.
--
-- The forward field of the bundled `circuit-faithful` `↔` produces
-- `satisfies` from `R`; the extra `preprocess-shaped` hypothesis it is
-- handed is then redundant.  But the *bundle's* statement carries
-- `preprocess-shaped` as a top-level hypothesis (so the two directions
-- share preconditions), and we want it derivable from `R` directly so
-- callers in possession of `R` need not supply it separately.  This
-- lemma provides that: an `R-instrs` trace is a fortiori a `Tr-shaped`
-- trace (it pins strictly more — including the computed values).
------------------------------------------------------------------------

private
  -- `push-mem2 s x y ≡ push-mem (push-mem s x) y`.  Both set only the
  -- `memory` field; they differ by `++`-associativity on the suffix.
  push-mem2-iter : ∀ (s : Preprocessed) x y
    → push-mem2 s x y ≡ push-mem (push-mem s x) y
  push-mem2-iter s x y =
    cong (λ m → record s { memory = m })
         (push-mem2-assoc (Preprocessed.memory s) x y)

  -- Per-step conversion.  From `R-instr pre s i s'` build the shape
  -- payload `sd` plus the suffix decomposition and a proof that
  -- `tr-next … sd ≡ s'`.
  R-instr→tr-step
    : ∀ (pre : ProofPreimage) (s : Preprocessed) (i : Instruction) (s' : Preprocessed)
    → R-instr pre s i s'
    → Σ-syntax (List Fr) (λ ms → Σ-syntax (List Fr) (λ ps →
          (Preprocessed.memory s' ≡ Preprocessed.memory s ++ ms)
        × (Preprocessed.pis    s' ≡ Preprocessed.pis    s ++ ps)
        × Σ-syntax (tr-step i pre s ms ps) (λ sd →
            tr-next i pre s ms ps sd ≡ s')))
  R-instr→tr-step pre s .(assert _) .s (r-assert _) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _) , (refl , refl) , refl
  R-instr→tr-step pre s .(constrain-bits _ _) .s (r-constrain-bits _ _) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _) , (refl , refl) , refl
  R-instr→tr-step pre s .(constrain-eq _ _) .s (r-constrain-eq _ _ _) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _) , (refl , refl) , refl
  R-instr→tr-step pre s .(constrain-to-boolean _) .s (r-constrain-to-boolean _) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _) , (refl , refl) , refl
  -- push-mem cases (Δmem=1): ms = [the appended value], ps = [].
  R-instr→tr-step pre s (cond-select _ _ _) _ (r-cond-select {sel = sel} {av} {bv} _ _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (copy _) _ (r-copy {v = v} _) =
    v ∷ [] , [] , refl , sym (++-identityʳ _) , ((v , refl) , refl) , refl
  R-instr→tr-step pre s (load-imm _) _ (r-load-imm {imm = imm}) =
    imm ∷ [] , [] , refl , sym (++-identityʳ _) , ((imm , refl) , refl) , refl
  R-instr→tr-step pre s (test-eq _ _) _ (r-test-eq {av = av} {bv} _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (transient-hash _) _ (r-transient-hash {vs = vs} _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (add _ _) _ (r-add {av = av} {bv} _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (mul _ _) _ (r-mul {av = av} {bv} _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (neg _) _ (r-neg {av = av} _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (not _) _ (r-not {b = b} _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (less-than _ _ _) _ (r-less-than {av = av} {bv} _ _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  R-instr→tr-step pre s (reconstitute-field _ _ _) _ (r-reconstitute-field {dv = dv} {mv} _ _ _) =
    _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , refl) , refl) , refl
  -- push-mem2 cases (Δmem=2): ms = [x, y], ps = [].
  R-instr→tr-step pre s (ec-add _ _ _ _) _ (r-ec-add {cx = cx} {cy} _ _ _ _ _) =
    _ ∷ _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , _ , refl) , refl) , refl
  R-instr→tr-step pre s (ec-mul _ _ _) _ (r-ec-mul {cx = cx} {cy} _ _ _ _) =
    _ ∷ _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , _ , refl) , refl) , refl
  R-instr→tr-step pre s (ec-mul-generator _) _ (r-ec-mul-generator {cx = cx} {cy} _ _) =
    _ ∷ _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , _ , refl) , refl) , refl
  R-instr→tr-step pre s (hash-to-curve _) _ (r-hash-to-curve {cx = cx} {cy} _ _) =
    _ ∷ _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , _ , refl) , refl) , refl
  R-instr→tr-step pre s (persistent-hash _ _) _ (r-persistent-hash {h₁ = h₁} {h₂} _ _) =
    _ ∷ _ ∷ [] , [] , refl , sym (++-identityʳ _) , ((_ , _ , refl) , refl) , refl
  R-instr→tr-step pre s (div-mod-power-of-two _ _) _ (r-div-mod-power-of-two {bits = bits} {v = v} _) =
    let d = from-le-bits (drop bits (to-le-bits v))
        m = from-le-bits (take bits (to-le-bits v))
    in d ∷ m ∷ [] , []
       , sym (push-mem2-assoc (Preprocessed.memory s) d m)
       , sym (++-identityʳ _)
       , ((d , m , refl) , refl)
       , push-mem2-iter s d m
  -- declare-pub-input (Δpis=1): ms = [], ps = [the value].
  R-instr→tr-step pre s (declare-pub-input _) _ (r-declare-pub-input {v = v} _) =
    [] , v ∷ [] , sym (++-identityʳ _) , refl , (refl , v , refl) , refl
  -- output: no suffix; carry the lookup evidence.
  R-instr→tr-step pre s (output _) _ (r-output {v = v} lk) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _)
    , ((v , lk) , refl , refl) , refl
  -- pi-skip active / inactive.
  R-instr→tr-step pre s (pi-skip _ _) _ (r-pi-skip-active g-eq match) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _)
    , (refl , refl , (true , g-eq , match)) , refl
  R-instr→tr-step pre s (pi-skip _ count) _ (r-pi-skip-inactive g-eq) =
    [] , [] , sym (++-identityʳ _) , sym (++-identityʳ _)
    , (refl , refl , (false , g-eq , tt)) , refl
  -- public-input active / inactive.
  R-instr→tr-step pre s (public-input _) _ (r-public-input-active {v = v} {s₁} g-eq c-eq) =
    v ∷ [] , []
    , cong (_++ (v ∷ [])) (consume-pub-out-mem s c-eq)
    , trans (consume-pub-out-pis s c-eq) (sym (++-identityʳ _))
    , (v , refl , refl , (true , g-eq , (s₁ , c-eq))) , refl
  R-instr→tr-step pre s (public-input _) _ (r-public-input-inactive g-eq) =
    0ᶠ ∷ [] , [] , refl , sym (++-identityʳ _)
    , (0ᶠ , refl , refl , (false , g-eq , refl)) , refl
  -- private-input active / inactive.
  R-instr→tr-step pre s (private-input _) _ (r-private-input-active {v = v} {s₁} g-eq c-eq) =
    v ∷ [] , []
    , cong (_++ (v ∷ [])) (consume-priv-mem s c-eq)
    , trans (consume-priv-pis s c-eq) (sym (++-identityʳ _))
    , (v , refl , refl , (true , g-eq , (s₁ , c-eq))) , refl
  R-instr→tr-step pre s (private-input _) _ (r-private-input-inactive g-eq) =
    0ᶠ ∷ [] , [] , refl , sym (++-identityʳ _)
    , (0ᶠ , refl , refl , (false , g-eq , refl)) , refl

  -- Fold the per-step conversion along an `R-instrs` trace.  The
  -- endpoint `s` is pinned by the trace, so the result carries it as the
  -- `Tr-shaped` endpoint index (no memory/pis equations needed here).
  R-instrs→Tr-shaped
    : ∀ (pre : ProofPreimage) (s₀ s : Preprocessed) (is : List Instruction)
    → R-instrs pre s₀ is s
    → Σ-syntax (List Fr) (λ mem-suf → Σ-syntax (List Fr) (λ pis-suf →
          Tr-shaped pre s₀ is s mem-suf pis-suf))
  R-instrs→Tr-shaped pre s₀ .s₀ [] r-done = [] , [] , tr-nil
  R-instrs→Tr-shaped pre s₀ s (i ∷ is) (r-step {s₁ = s₁} r-head r-tail) =
    let ms , ps , _mem-eq₁ , _pis-eq₁ , sd , tn-eq = R-instr→tr-step pre s₀ i s₁ r-head
        -- The tail trace starts from `s₁`; rewrite it to start from
        -- `tr-next … sd` (which equals `s₁` by `tn-eq`).
        r-tail' : R-instrs pre (tr-next i pre s₀ ms ps sd) is s
        r-tail' = subst (λ z → R-instrs pre z is s) (sym tn-eq) r-tail
        ms-t , ps-t , tr-tail =
          R-instrs→Tr-shaped pre (tr-next i pre s₀ ms ps sd) s is r-tail'
    in ms ++ ms-t , ps ++ ps-t , tr-cons sd tr-tail

-- `R ⇒ preprocess-shaped`.
R⇒preprocess-shaped : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
  → R src pre s → preprocess-shaped src pre s
R⇒preprocess-shaped src pre s (s₀ , init-eq , Rs , tc , _co) =
  let ms , ps , tr =
        R-instrs→Tr-shaped pre s₀ s (IrSource.instructions src) Rs
  in s₀ , init-eq , (ms , ps , tr) , tc

------------------------------------------------------------------------
-- Internal bridge, step 0:  `Tr-shaped` ⇒ `op-side-data-list`.
--
-- Because `tr-step` / `tr-next` are verbatim copies of `op-side-data` /
-- `next-state-from-osd` (same body, same `Semantics` vocabulary), the
-- two relations have definitionally-equal index expressions.  The
-- conversion is therefore a trivial structural map (two cases): a
-- `tr-step` payload IS an `op-side-data` payload, and
-- `tr-next … sd` reduces to `next-state-from-osd … sd`.
------------------------------------------------------------------------

private
  -- After matching `i` to a concrete constructor, `tr-step i` and
  -- `op-side-data i` reduce to the SAME RHS (verbatim copies), and
  -- likewise `tr-next i` ≡ `next-state-from-osd i`.  So in each case the
  -- `tr-step` payload `sd` IS an `op-side-data` payload and the tail's
  -- start state coincides — `osd-cons sd (rec tr-tail)` typechecks
  -- directly with no transport (for `pi-skip` / `public-input` /
  -- `private-input` the recursion is transported by `tr-next≡nso`).
  Tr-shaped→osd-list
    : ∀ (pre : ProofPreimage) (s₀ : Preprocessed) (is : List Instruction)
        (s : Preprocessed) (mem-suf pis-suf : List Fr)
    → Tr-shaped pre s₀ is s mem-suf pis-suf
    → op-side-data-list pre s₀ is mem-suf pis-suf
  Tr-shaped→osd-list pre s₀ .[] .s₀ .[] .[] tr-nil = osd-nil
  Tr-shaped→osd-list pre s (assert _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (cond-select _ _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (constrain-bits _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (constrain-eq _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (constrain-to-boolean _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (copy _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (declare-pub-input _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (pi-skip g count ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (sm , sp , (true , gd , mt)) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (sm , sp , (true , gd , mt))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (pi-skip g count ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (sm , sp , (false , gd , u)) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (sm , sp , (false , gd , u))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (ec-add _ _ _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (ec-mul _ _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (ec-mul-generator _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (hash-to-curve _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (load-imm _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (div-mod-power-of-two _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (persistent-hash _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (reconstitute-field _ _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (output _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (transient-hash _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (test-eq _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (add _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (mul _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (neg _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (not _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (less-than _ _ _ ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} sd t) =
    osd-cons {mem-step = ms} {pis-step = ps} sd (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (public-input g ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (true , gd , (s₁ , ce))) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (true , gd , (s₁ , ce)))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (public-input g ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (false , gd , wz)) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (false , gd , wz))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (private-input g ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (true , gd , (s₁ , ce))) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (true , gd , (s₁ , ce)))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)
  Tr-shaped→osd-list pre s (private-input g ∷ is) s-end ._ ._
      (tr-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (false , gd , wz)) t) =
    osd-cons {mem-step = ms} {pis-step = ps} (w , em , ep , (false , gd , wz))
      (Tr-shaped→osd-list pre _ is s-end _ _ t)

  -- The fold endpoint of the bridged list equals the `Tr-shaped`
  -- endpoint index `s`.  This pins D2's existential `s'` (which D2 proves
  -- `≡ osd-fold osd`) to the GIVEN state `s` in `circuit-faithful-bwd`.
  --
  -- Proof by induction on `Tr-shaped`.  In each `tr-cons` case the bridge
  -- reduces to `osd-cons sd (rec t)` (matching the instruction), so
  -- `osd-fold` reduces to `osd-fold (rec t)`, discharged by the IH on
  -- `t`.  The endpoint index `s-end` is threaded unchanged, so the IH
  -- gives `osd-fold (rec t) ≡ s-end` directly.
  Tr-shaped→osd-list-fold
    : ∀ (pre : ProofPreimage) (s₀ : Preprocessed) (is : List Instruction)
        (s : Preprocessed) (mem-suf pis-suf : List Fr)
    → (tr : Tr-shaped pre s₀ is s mem-suf pis-suf)
    → osd-fold (Tr-shaped→osd-list pre s₀ is s mem-suf pis-suf tr) ≡ s
  Tr-shaped→osd-list-fold pre s₀ .[] .s₀ .[] .[] tr-nil = refl
  Tr-shaped→osd-list-fold pre s (assert _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (cond-select _ _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (constrain-bits _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (constrain-eq _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (constrain-to-boolean _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (copy _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (declare-pub-input _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (pi-skip g count ∷ is) s-end ._ ._
      (tr-cons (sm , sp , (true , gd , mt)) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (pi-skip g count ∷ is) s-end ._ ._
      (tr-cons (sm , sp , (false , gd , u)) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (ec-add _ _ _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (ec-mul _ _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (ec-mul-generator _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (hash-to-curve _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (load-imm _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (div-mod-power-of-two _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (persistent-hash _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (reconstitute-field _ _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (output _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (transient-hash _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (test-eq _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (add _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (mul _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (neg _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (not _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (less-than _ _ _ ∷ is) s-end ._ ._ (tr-cons sd t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (public-input g ∷ is) s-end ._ ._
      (tr-cons (w , em , ep , (true , gd , (s₁ , ce))) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (public-input g ∷ is) s-end ._ ._
      (tr-cons (w , em , ep , (false , gd , wz)) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (private-input g ∷ is) s-end ._ ._
      (tr-cons (w , em , ep , (true , gd , (s₁ , ce))) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t
  Tr-shaped→osd-list-fold pre s (private-input g ∷ is) s-end ._ ._
      (tr-cons (w , em , ep , (false , gd , wz)) t) =
    Tr-shaped→osd-list-fold pre _ is s-end _ _ t

  -- Per-step memory equation:  `memory (tr-next i …) ≡ memory s ++ ms`.
  -- Mirrors `tr-next`; the `sd` payload supplies `ms`'s shape, and for
  -- the transcript-active cases `consume-*-mem` shows the consumed state
  -- leaves memory unchanged.
  tr-step-mem
    : ∀ (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
        (ms ps : List Fr) (sd : tr-step i pre s ms ps)
    → Preprocessed.memory (tr-next i pre s ms ps sd)
        ≡ Preprocessed.memory s ++ ms
  tr-step-mem (assert _) _ s _ _ (mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (constrain-bits _ _) _ s _ _ (mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (constrain-eq _ _) _ s _ _ (mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (constrain-to-boolean _) _ s _ _ (mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (add _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (mul _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (neg _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (copy _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (load-imm _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (test-eq _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (transient-hash _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (cond-select _ _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (not _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (less-than _ _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (reconstitute-field _ _ _) _ s _ _ ((w , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (ec-add _ _ _ _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (ec-mul _ _ _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (ec-mul-generator _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (hash-to-curve _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (persistent-hash _ _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (div-mod-power-of-two _ _) _ s _ _ ((x , y , me) , _) = cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (declare-pub-input _) _ s _ _ (mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (output _) _ s _ _ ((_ , _) , mn , _) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (pi-skip _ _) _ s _ _ (mn , _ , (true , _ , _)) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (pi-skip _ _) _ s _ _ (mn , _ , (false , _ , _)) = sym (trans (cong (Preprocessed.memory s ++_) mn) (++-identityʳ _))
  tr-step-mem (public-input _) _ s _ _ (w , me , _ , (true , _ , (s₁ , ce))) =
    trans (cong (_++ (w ∷ [])) (consume-pub-out-mem s ce)) (cong (Preprocessed.memory s ++_) (sym me))
  tr-step-mem (public-input _) _ s _ _ (w , me , _ , (false , _ , _)) =
    cong (Preprocessed.memory s ++_) (sym me)
  tr-step-mem (private-input _) _ s _ _ (w , me , _ , (true , _ , (s₁ , ce))) =
    trans (cong (_++ (w ∷ [])) (consume-priv-mem s ce)) (cong (Preprocessed.memory s ++_) (sym me))
  tr-step-mem (private-input _) _ s _ _ (w , me , _ , (false , _ , _)) =
    cong (Preprocessed.memory s ++_) (sym me)

  -- Per-step pis equation:  `pis (tr-next i …) ≡ pis s ++ ps`.
  tr-step-pis
    : ∀ (i : Instruction) (pre : ProofPreimage) (s : Preprocessed)
        (ms ps : List Fr) (sd : tr-step i pre s ms ps)
    → Preprocessed.pis (tr-next i pre s ms ps sd)
        ≡ Preprocessed.pis s ++ ps
  tr-step-pis (assert _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (constrain-bits _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (constrain-eq _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (constrain-to-boolean _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (add _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (mul _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (neg _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (copy _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (load-imm _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (test-eq _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (transient-hash _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (cond-select _ _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (not _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (less-than _ _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (reconstitute-field _ _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (ec-add _ _ _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (ec-mul _ _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (ec-mul-generator _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (hash-to-curve _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (persistent-hash _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (div-mod-power-of-two _ _) _ s _ _ (_ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (declare-pub-input _) _ s _ _ (_ , wv , pe) = cong (Preprocessed.pis s ++_) (sym pe)
  tr-step-pis (output _) _ s _ _ ((_ , _) , _ , pn) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (pi-skip _ _) _ s _ _ (_ , pn , (true , _ , _)) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (pi-skip _ _) _ s _ _ (_ , pn , (false , _ , _)) = sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (public-input _) _ s _ _ (w , _ , pn , (true , _ , (s₁ , ce))) =
    trans (consume-pub-out-pis s ce) (sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _)))
  tr-step-pis (public-input _) _ s _ _ (w , _ , pn , (false , _ , _)) =
    sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))
  tr-step-pis (private-input _) _ s _ _ (w , _ , pn , (true , _ , (s₁ , ce))) =
    trans (consume-priv-pis s ce) (sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _)))
  tr-step-pis (private-input _) _ s _ _ (w , _ , pn , (false , _ , _)) =
    sym (trans (cong (Preprocessed.pis s ++_) pn) (++-identityʳ _))

  -- Fold the per-step memory / pis equations along a `Tr-shaped` trace.
  Tr-shaped→mem
    : ∀ (pre : ProofPreimage) (s₀ s : Preprocessed) (is : List Instruction)
        (ms ps : List Fr)
    → Tr-shaped pre s₀ is s ms ps
    → Preprocessed.memory s ≡ Preprocessed.memory s₀ ++ ms
  Tr-shaped→mem pre s₀ .s₀ .[] .[] .[] tr-nil = sym (++-identityʳ _)
  Tr-shaped→mem pre s₀ s (i ∷ is) ._ ._
      (tr-cons {mem-step = mst} {pis-step = pst} {mem-tail = mtl} sd t) =
    let s₁ = tr-next i pre s₀ mst pst sd in
    trans (Tr-shaped→mem pre s₁ s is mtl _ t)
      (trans (cong (_++ mtl) (tr-step-mem i pre s₀ mst pst sd))
             (++-assoc (Preprocessed.memory s₀) mst mtl))

  Tr-shaped→pis
    : ∀ (pre : ProofPreimage) (s₀ s : Preprocessed) (is : List Instruction)
        (ms ps : List Fr)
    → Tr-shaped pre s₀ is s ms ps
    → Preprocessed.pis s ≡ Preprocessed.pis s₀ ++ ps
  Tr-shaped→pis pre s₀ .s₀ .[] .[] .[] tr-nil = sym (++-identityʳ _)
  Tr-shaped→pis pre s₀ s (i ∷ is) ._ ._
      (tr-cons {mem-step = mst} {pis-step = pst} {pis-tail = ptl} sd t) =
    let s₁ = tr-next i pre s₀ mst pst sd in
    trans (Tr-shaped→pis pre s₁ s is _ ptl t)
      (trans (cong (_++ ptl) (tr-step-pis i pre s₀ mst pst sd))
             (++-assoc (Preprocessed.pis s₀) pst ptl))

------------------------------------------------------------------------
-- Part 1.  s₀-recovery.
--
-- From WF1 (`length (inputs pre) ≡ num-inputs src`) and the
-- `rand-shape` field of `satisfies` (which, when `do-comm ≡ true`,
-- forces `comm-rand-of pre ≢ nothing`, i.e. `comm-commitment pre ≢
-- nothing`), `init-state src pre` cannot land in either failure branch,
-- so it returns `just s₀` for the concrete `s₀`.  Mirrors the forward
-- `init-state-*` helpers (which run the other way, from `≡ just s₀`).
------------------------------------------------------------------------

private
  -- WF1 length equation ⇒ the `≡ᵇ` guard in `init-state` is `true`.
  wf1⇒guard-true : ∀ (src : IrSource) (pre : ProofPreimage)
    → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
    → (length (ProofPreimage.inputs pre) ≡ᵇ IrSource.num-inputs src) ≡ true
  wf1⇒guard-true src pre wf1 =
    Data.Bool.Properties.T-≡ .Function.Bundles.Equivalence.to
      (Data.Nat.Properties.≡⇒≡ᵇ _ _ wf1)

  -- `has-comm (circuit src)` is definitionally `do-comm src`.
  -- `comm-rand-of pre ≡ nothing` exactly when `comm-commitment pre ≡
  -- nothing`.  When `do-comm ≡ true`, `Maybe-shape true nothing ≡ ⊥`
  -- rules that case out.
  recover-init-state
    : ∀ (src : IrSource) (pre : ProofPreimage)
    → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
    → Maybe-shape (IrSource.do-communications-commitment src) (comm-rand-of pre)
    → Σ-syntax Preprocessed (λ s₀ → init-state src pre ≡ just s₀)
  recover-init-state src pre wf1 ms
    with (length (ProofPreimage.inputs pre) ≡ᵇ IrSource.num-inputs src)
       | wf1⇒guard-true src pre wf1
       | IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
       | ms
  ... | .true | refl | false | _            | _  = _ , refl
  ... | .true | refl | true  | just (c , r) | _  = _ , refl
  ... | .true | refl | true  | nothing      | ()

-- ───────────────────────────────────────────────────────────────────
-- The backward direction, DISCHARGED.
--
-- Two blockers (now resolved by the two extra hypotheses; see the design
-- history below) made `circuit-faithful-bwd` FALSE over an *arbitrary*
-- `s : Preprocessed`:
--
--   • SECOND BLOCKER — `satisfies` is blind to transcript-read wires
--     (`public-input` / `private-input` active emit no clause; `pi-skip`
--     active's transcript-match has no in-circuit shadow), so an arbitrary
--     `s` can satisfy the circuit while its transcript wires hold garbage.
--     RESOLVED by the `preprocess-shaped` hypothesis (§5.4), which pins
--     the operational shape walk ending exactly at `s`.
--
--   • THIRD BLOCKER — `transcripts-consumed pre s ≡ true` is a top-level
--     conjunct of `R` (Semantics.agda:632) yet is NOT entailed by
--     `satisfies` + the trace + producer-safety (no obligation constrains
--     the transcript cursors; an all-inactive walk consumes nothing).
--     RESOLVED by folding `transcripts-consumed pre s ≡ true` into
--     `preprocess-shaped` (faithful: §5.4 quantifies over states reached
--     by a SUCCESSFUL `preprocess`, which passed `transcripts-consumed`).
--
-- With those two and WF1 (§3.4, part 1) in hand the proof runs:
--   1. `preprocess-shaped` ⇒ `s₀`, `init-eq`, `(ms, ps, tr)`, `tc`.
--   2. `osd = Tr-shaped→osd-list … tr`;  memory / pis of `s` reshape as
--      `memory s₀ ++ ms` / `pis s₀ ++ ps` (`Tr-shaped→mem` / `→pis`).
--   3. invariants at the initial synth state `st₀` (mem-inv, pi-inv,
--      O2/O3-Inv via `o2/o3-inv-init`, the three traces via
--      `O2/O3-bool→Runs` ∘ `producer-safe-O2/-O3` and `wire-disc-sound`,
--      fits ≡ refl since `clauses st₀ ≡ []`).
--   4. invert `satisfies` (split off the comm clause when hc) to feed the
--      body `satisfies-clauses` to D2 (`satisfies-clauses→R-instrs`).
--   5. D2 ⇒ `s'`, mem/pis eqs, `R-instrs pre s₀ instrs s'`, `s' ≡ osd-fold osd`.
--   6. pin `s' ≡ s`: `s' ≡ osd-fold osd ≡ s` (`Tr-shaped→osd-list-fold`),
--      so `subst` the trace to end at `s`.
--   7. `transcripts-consumed pre s ≡ true` = the `tc` hypothesis.
--   8. `comm-ok src pre s ≡ true` by inverting the comm clause
--      (`inputs-lookup-init`, `output-wires-coincide`, `init-state-pi-1`,
--      `≡ᶠ?-refl`), mirroring the forward `circuit-faithful-fwd-true`.
-- ───────────────────────────────────────────────────────────────────

private
  -- D2 packaged for the body, returning the trace pinned to end at the
  -- GIVEN `s` (via `s' ≡ osd-fold osd ≡ s`).  Independent of `hc`'s comm
  -- clause: it consumes the *body* clause satisfaction only.
  bwd-body-trace
    : ∀ {hc} (pre : ProofPreimage) (src : IrSource) (s s₀ : Preprocessed)
        (ms ps : List Fr)
    → producer-safe src ≡ true
    → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src
    → init-state src pre ≡ just s₀
    → (tr : Tr-shaped pre s₀ (IrSource.instructions src) s ms ps)
    → IrSource.do-communications-commitment src ≡ hc
    → satisfies-clauses
        (SynthState.clauses
          (circuit-instrs hc (IrSource.instructions src) (mk-synth (IrSource.num-inputs src) [] 0 [])))
        (mk-witness (Preprocessed.memory s₀ ++ ms)
                    (Preprocessed.pis s₀ ++ ps)
                    (comm-rand-of pre))
    → R-instrs pre s₀ (IrSource.instructions src) s
  bwd-body-trace {hc} pre src s s₀ ms ps ps-safe wf1 init-eq tr hc-eq sat-body =
    let
      n   = IrSource.num-inputs src
      st₀ = mk-synth n [] 0 []
      instrs = IrSource.instructions src
      mem≡   = init-state-memory' src pre s₀ init-eq
      len-eq = init-state-inputs-length src pre s₀ init-eq
      mi₀ : mem-inv s₀ st₀
      mi₀ = sym (trans (cong length mem≡) len-eq)
      pi₀-pre : length (Preprocessed.pis s₀)
                  ≡ preamble-pi-count (IrSource.do-communications-commitment src)
      pi₀-pre = init-state-pis-length src pre s₀ init-eq
      pi₀ : pi-inv hc s₀ st₀
      pi₀ = subst (λ b → length (Preprocessed.pis s₀) ≡ preamble-pi-count b + 0)
                  hc-eq
                  (trans pi₀-pre
                         (sym (+-identityʳ (preamble-pi-count
                                 (IrSource.do-communications-commitment src)))))
      -- Initial obligation invariants at `s₀` (`bk₀ = bm₀ = []`).
      o2-inv₀ : O2-Inv (n , []) s₀
      o2-inv₀ = o2-inv-init {src} {pre} {s₀} init-eq wf1
      o3-inv₀ : O3-Inv (n , []) s₀
      o3-inv₀ = o3-inv-init {src} {pre} {s₀} init-eq wf1
      -- The three producer traces at `(n , [])` / `n`.
      o2-tr : O2-Trace instrs (n , []) (O2-Runs.final (O2-bool→Runs {src} (producer-safe-O2 {src} ps-safe)))
      o2-tr = O2-Runs.trace (O2-bool→Runs {src} (producer-safe-O2 {src} ps-safe))
      o3-tr : O3-Trace instrs (n , []) (O3-Runs.final (O3-bool→Runs {src} (producer-safe-O3 {src} ps-safe)))
      o3-tr = O3-Runs.trace (O3-bool→Runs {src} (producer-safe-O3 {src} ps-safe))
      w-tr : Wire-Trace instrs n (proj₁ (wire-disc-sound {src} ps-safe))
      w-tr = proj₂ (wire-disc-sound {src} ps-safe)
      -- The osd-list and the fold endpoint = `s`.
      osd : op-side-data-list pre s₀ instrs ms ps
      osd = Tr-shaped→osd-list pre s₀ instrs s ms ps tr
      fold≡s : osd-fold osd ≡ s
      fold≡s = Tr-shaped→osd-list-fold pre s₀ instrs s ms ps tr
      -- D2.
      d2 = satisfies-clauses→R-instrs {hc} pre s₀ instrs st₀ ms ps
             mi₀ pi₀ refl refl {bk₀ = []} {bm₀ = []} o2-inv₀ o3-inv₀
             o2-tr o3-tr w-tr osd sat-body
      s'      = proj₁ d2
      Rs'     = proj₁ (proj₂ (proj₂ (proj₂ d2)))
      fold-eq = proj₂ (proj₂ (proj₂ (proj₂ d2)))
      s'≡s : s' ≡ s
      s'≡s = trans fold-eq fold≡s
    in subst (R-instrs pre s₀ instrs) s'≡s Rs'

  -- `comm-rand-of pre ≡ just r` when `comm-commitment pre ≡ just (c, r)`.
  comm-rand-of-just : ∀ (pre : ProofPreimage) c r
    → ProofPreimage.comm-commitment pre ≡ just (c , r)
    → comm-rand-of pre ≡ just r
  comm-rand-of-just pre c r eq
    with ProofPreimage.comm-commitment pre | eq
  ... | just .(c , r) | refl = refl

  -- `circuit src` reduces to its hc-specific record shape.  (These are
  -- the backward-usable forms of the forward's `circuit-instantiate-*`,
  -- lifted out of the body's `let` since `where` is illegal there.)
  circuit-eq-false : ∀ (src : IrSource)
    → IrSource.do-communications-commitment src ≡ false
    → circuit src ≡
      mk-circuit
        (SynthState.nr-wires (circuit-instrs false (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 [])))
        (SynthState.clauses (circuit-instrs false (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 [])))
        (1 + SynthState.nr-declared-pi (circuit-instrs false (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 [])))
        false
  circuit-eq-false src refl = refl

  circuit-eq-true : ∀ (src : IrSource)
    → IrSource.do-communications-commitment src ≡ true
    → circuit src ≡
      mk-circuit
        (SynthState.nr-wires (circuit-instrs true (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 [])))
        (SynthState.clauses (circuit-instrs true (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 []))
          ⊕ clause-comm-commitment (nat-range (IrSource.num-inputs src))
              (SynthState.output-wires (circuit-instrs true (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 []))))
        (2 + SynthState.nr-declared-pi (circuit-instrs true (IrSource.instructions src)
                                (mk-synth (IrSource.num-inputs src) [] 0 [])))
        true
  circuit-eq-true src refl = refl

  -- `comm-ok` is `true` definitionally when `do-comm ≡ false`.
  comm-ok-false : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
    → IrSource.do-communications-commitment src ≡ false
    → comm-ok src pre s ≡ true
  comm-ok-false src pre s e with IrSource.do-communications-commitment src | e
  ... | false | refl = refl

  -- Invert the comm clause to recover `comm-ok src pre s ≡ true`.
  -- hc=false branch is `refl`; hc=true requires the `holds` witness.
  bwd-comm-ok-true
    : ∀ (src : IrSource) (pre : ProofPreimage) (s s₀ : Preprocessed) c r
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ just (c , r)
    → init-state src pre ≡ just s₀
    → R-instrs pre s₀ (IrSource.instructions src) s
    → holds (witness-of s pre)
        (clause-comm-commitment (nat-range (IrSource.num-inputs src))
          (SynthState.output-wires
            (circuit-instrs true (IrSource.instructions src)
              (mk-synth (IrSource.num-inputs src) [] 0 []))))
    → comm-ok src pre s ≡ true
  bwd-comm-ok-true src pre s s₀ c r hc-true cc-just init-eq Rs
      (ivs , ovs , rv , pv , ivs-lk , ovs-lk , rand≡ , pi1≡ , pv≡tc) =
    let
      n  = IrSource.num-inputs src
      st₀ = mk-synth n [] 0 []
      instrs = IrSource.instructions src
      cm-inputs = nat-range n
      out-wires = SynthState.output-wires (circuit-instrs true instrs st₀)
      -- `ivs ≡ inputs pre`.
      ivs-init : mem-lookups (Preprocessed.memory s) cm-inputs
                   ≡ just (ProofPreimage.inputs pre)
      ivs-init = mem-lookups-mono-R-instrs pre s₀ s instrs cm-inputs
                   (ProofPreimage.inputs pre) Rs (inputs-lookup-init src pre s₀ init-eq)
      ivs≡ : ivs ≡ ProofPreimage.inputs pre
      ivs≡ = just-injective (trans (sym ivs-lk) ivs-init)
      -- `ovs ≡ outputs s`.
      ovs-coin : mem-lookups (Preprocessed.memory s) out-wires
                   ≡ just (Preprocessed.outputs s)
      ovs-coin = output-wires-coincide {hc = true} pre s₀ s instrs st₀ Rs refl
                   (init-state-outputs src pre s₀ init-eq)
      ovs≡ : ovs ≡ Preprocessed.outputs s
      ovs≡ = just-injective (trans (sym ovs-lk) ovs-coin)
      -- `rv ≡ r`: `comm-rand-of pre ≡ just r` (cc-just) and `≡ just rv`.
      rof≡ : comm-rand-of pre ≡ just r
      rof≡ = comm-rand-of-just pre c r cc-just
      rv≡ : rv ≡ r
      rv≡ = just-injective (trans (sym rand≡) rof≡)
      -- `pv ≡ c`: `pi-lookup (pis s) 1 ≡ just c` and `≡ just pv`.
      pi1-init : pi-lookup (Preprocessed.pis s₀) 1 ≡ just c
      pi1-init = init-state-pi-1 src pre s₀ c r hc-true cc-just init-eq
      pi1-final : pi-lookup (Preprocessed.pis s) 1 ≡ just c
      pi1-final = pi-lookup-mono-R-instrs pre s₀ s instrs 1 c Rs pi1-init
      pv≡c : pv ≡ c
      pv≡c = just-injective (trans (sym pi1≡) pi1-final)
      -- `c ≡ transient-commit (inputs pre ++ outputs s) r`.
      c≡tc : c ≡ transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r
      c≡tc = trans (sym pv≡c)
               (trans pv≡tc
                 (cong₂ (λ vs rr → transient-commit vs rr)
                        (cong₂ _++_ ivs≡ ovs≡) rv≡))
      -- Reduce `comm-ok` under hc=true / cc=just to the `≡ᶠ?` check, true
      -- by reflexivity rewritten along `c≡tc`.
      goal : (c ≡ᶠ? transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r) ≡ true
      goal = subst (λ x → (c ≡ᶠ? x) ≡ true) c≡tc ≡ᶠ?-refl
    in comm-ok-reduce src pre s c r hc-true cc-just goal
    where
      -- `comm-ok src pre s` reduces to the `≡ᶠ?` check at hc=true/cc=just.
      comm-ok-reduce : ∀ src pre s c r
        → IrSource.do-communications-commitment src ≡ true
        → ProofPreimage.comm-commitment pre ≡ just (c , r)
        → (c ≡ᶠ? transient-commit (ProofPreimage.inputs pre ++ Preprocessed.outputs s) r) ≡ true
        → comm-ok src pre s ≡ true
      comm-ok-reduce src pre s c r hc-true cc-just chk
        with IrSource.do-communications-commitment src
           | ProofPreimage.comm-commitment pre
           | hc-true | cc-just
      ... | true | just .(c , r) | _ | refl = chk

  -- hc=true with comm-commitment=nothing is ruled out by `satisfies`'s
  -- rand-shape (`Maybe-shape true nothing ≡ ⊥`).
  bwd-no-comm-contra
    : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
    → IrSource.do-communications-commitment src ≡ true
    → ProofPreimage.comm-commitment pre ≡ nothing
    → Maybe-shape (IrSource.do-communications-commitment src) (comm-rand-of pre)
    → ⊥
  bwd-no-comm-contra src pre s hc-true cc-none msh
    with IrSource.do-communications-commitment src
       | ProofPreimage.comm-commitment pre
       | hc-true | cc-none
  ... | true | nothing | _ | refl = msh

circuit-faithful-bwd
  : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
  → producer-safe src ≡ true
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src   -- WF1 (§3.4)
  → preprocess-shaped src pre s                                   -- §5.4
  → satisfies (circuit src) (witness-of s pre)
  → R src pre s
circuit-faithful-bwd src pre s ps-safe wf1
    (s₀ , init-eq , (ms , ps , tr) , tc)
    (mk-sat _pi-len rand-shape clause-ok)
  with bool-cases (IrSource.do-communications-commitment src)
... | inj₂ hc-false =
  let
    n   = IrSource.num-inputs src
    st₀ = mk-synth n [] 0 []
    instrs = IrSource.instructions src
    mem-eq-s : Preprocessed.memory s ≡ Preprocessed.memory s₀ ++ ms
    mem-eq-s = Tr-shaped→mem pre s₀ s instrs ms ps tr
    pis-eq-s : Preprocessed.pis s ≡ Preprocessed.pis s₀ ++ ps
    pis-eq-s = Tr-shaped→pis pre s₀ s instrs ms ps tr
    -- `circuit src` reduces to its hc=false body clauses; clause-ok is
    -- satisfaction of exactly those clauses by `witness-of s pre`.
    circuit-eq : circuit src ≡
      mk-circuit (SynthState.nr-wires (circuit-instrs false instrs st₀))
                 (SynthState.clauses (circuit-instrs false instrs st₀))
                 (1 + SynthState.nr-declared-pi (circuit-instrs false instrs st₀))
                 false
    circuit-eq = circuit-eq-false src hc-false
    sat-body-s : satisfies-clauses
      (SynthState.clauses (circuit-instrs false instrs st₀))
      (mk-witness (Preprocessed.memory s) (Preprocessed.pis s) (comm-rand-of pre))
    sat-body-s = subst (λ c → satisfies-clauses (Circuit.clauses c)
                                 (witness-of s pre))
                       circuit-eq clause-ok
    sat-body : satisfies-clauses
      (SynthState.clauses (circuit-instrs false instrs st₀))
      (mk-witness (Preprocessed.memory s₀ ++ ms) (Preprocessed.pis s₀ ++ ps) (comm-rand-of pre))
    sat-body = subst₂ (λ m p → satisfies-clauses
                                  (SynthState.clauses (circuit-instrs false instrs st₀))
                                  (mk-witness m p (comm-rand-of pre)))
                      mem-eq-s pis-eq-s sat-body-s
    Rs : R-instrs pre s₀ instrs s
    Rs = bwd-body-trace {false} pre src s s₀ ms ps ps-safe wf1 init-eq tr hc-false sat-body
    co : comm-ok src pre s ≡ true
    co = comm-ok-false src pre s hc-false
  in s₀ , init-eq , Rs , tc , co
... | inj₁ hc-true with maybe-cases (ProofPreimage.comm-commitment pre)
...   | inj₁ cc-none =
        ⊥-elim (bwd-no-comm-contra src pre s hc-true cc-none rand-shape)
...   | inj₂ (c , r , cc-just) =
  let
    n   = IrSource.num-inputs src
    st₀ = mk-synth n [] 0 []
    instrs = IrSource.instructions src
    st-end = circuit-instrs true instrs st₀
    cm-inputs = nat-range n
    out-wires = SynthState.output-wires st-end
    body-clauses = SynthState.clauses st-end
    mem-eq-s : Preprocessed.memory s ≡ Preprocessed.memory s₀ ++ ms
    mem-eq-s = Tr-shaped→mem pre s₀ s instrs ms ps tr
    pis-eq-s : Preprocessed.pis s ≡ Preprocessed.pis s₀ ++ ps
    pis-eq-s = Tr-shaped→pis pre s₀ s instrs ms ps tr
    circuit-eq : circuit src ≡
      mk-circuit (SynthState.nr-wires st-end)
                 (body-clauses ⊕ clause-comm-commitment cm-inputs out-wires)
                 (2 + SynthState.nr-declared-pi st-end)
                 true
    circuit-eq = circuit-eq-true src hc-true
    -- Satisfaction of the FULL clause list (body ++ [comm]) by `witness-of s pre`.
    sat-full : satisfies-clauses
      (body-clauses ⊕ clause-comm-commitment cm-inputs out-wires)
      (mk-witness (Preprocessed.memory s) (Preprocessed.pis s) (comm-rand-of pre))
    sat-full = subst (λ c → satisfies-clauses (Circuit.clauses c) (witness-of s pre))
                     circuit-eq clause-ok
    -- Split off the comm clause.
    split = satisfies-clauses-split body-clauses
              (clause-comm-commitment cm-inputs out-wires ∷ []) sat-full
    sat-body-s : satisfies-clauses body-clauses
      (mk-witness (Preprocessed.memory s) (Preprocessed.pis s) (comm-rand-of pre))
    sat-body-s = proj₁ split
    holds-comm : holds (mk-witness (Preprocessed.memory s) (Preprocessed.pis s) (comm-rand-of pre))
                       (clause-comm-commitment cm-inputs out-wires)
    holds-comm = proj₁ (proj₂ split)
    sat-body : satisfies-clauses body-clauses
      (mk-witness (Preprocessed.memory s₀ ++ ms) (Preprocessed.pis s₀ ++ ps) (comm-rand-of pre))
    sat-body = subst₂ (λ m p → satisfies-clauses body-clauses
                                  (mk-witness m p (comm-rand-of pre)))
                      mem-eq-s pis-eq-s sat-body-s
    Rs : R-instrs pre s₀ instrs s
    Rs = bwd-body-trace {true} pre src s s₀ ms ps ps-safe wf1 init-eq tr hc-true sat-body
    co : comm-ok src pre s ≡ true
    co = bwd-comm-ok-true src pre s s₀ c r hc-true cc-just init-eq Rs holds-comm
  in s₀ , init-eq , Rs , tc , co

------------------------------------------------------------------------
-- Section E.  The eventual replacement for the postulate at the end of
-- `Properties.agda`.
--
-- Phase 4e:  after 4b / 4c / 4d are done, `circuit-faithful` is the
-- conjunction of the two directions.  Stated here for visibility; the
-- replacement in `Properties.agda` is the FINAL step.
------------------------------------------------------------------------

-- The bundled biconditional (spec §6.2, P5 — "`preprocess(S,P)=Σ` iff
-- `Σ ⊨ C_S(π_Σ)`").  The spec states P5 as an *iff* of propositions, i.e.
-- a logical equivalence, which `Function.Bundles._⇔_` captures exactly:
-- it bundles the two implications `to` / `from` with only their (trivial)
-- congruence laws — no round-trip identity is asserted.
--
-- We deliberately do NOT use the stronger `_↔_` (type isomorphism): a
-- genuine `↔` additionally demands the inverse equations `to (from x) ≡ x`
-- / `from (to r) ≡ r`, propositional equalities between *proofs* of the
-- `Set`-valued relations `R` / `satisfies`.  Those proofs are not unique,
-- so the inverse laws are not derivable without a proof-irrelevance
-- postulate — which the no-postulate discipline forbids and which the
-- spec's "iff" never required.
--
-- `to` is the forward direction; it ignores the extra `preprocess-shaped`
-- hypothesis (redundant given `R`, by `R⇒preprocess-shaped`).  `from` is
-- the backward direction (`circuit-faithful-bwd`).
circuit-faithful
  : ∀ (src : IrSource) (pre : ProofPreimage) (s : Preprocessed)
  → producer-safe src ≡ true
  → length (ProofPreimage.inputs pre) ≡ IrSource.num-inputs src   -- WF1 (§3.4)
  → preprocess-shaped src pre s                                   -- §5.4
  → R src pre s ⇔ satisfies (circuit src) (witness-of s pre)
circuit-faithful src pre s ps-safe wf1 pps =
  mk⇔ (circuit-faithful-fwd src pre s ps-safe)
      (circuit-faithful-bwd src pre s ps-safe wf1 pps)
