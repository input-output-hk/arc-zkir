module ZKIR.Syntax where

open import Data.Bool   using (Bool)
open import Data.List   using (List)
open import Data.Maybe  using (Maybe)
open import Data.Nat    using (ℕ)
open import Data.String using (String)

------------------------------------------------------------------------
-- Postulated external types
--
-- These types come from outside the IR proper.  Their internal
-- structure is not needed for the syntax; it will be given when we
-- define the semantics.
------------------------------------------------------------------------

postulate
  Fr        : Set
  -- ^ BLS12-381 scalar field element (transient_crypto::curve::Fr).
  --   This is also the base field of Jubjub and the "native field" of
  --   the proof system.

  Alignment : Set
  -- ^ Byte-alignment descriptor (base_crypto::fab::Alignment).
  --   Used by PersistentHash to describe the layout of its inputs.

------------------------------------------------------------------------
-- Identifiers  (ir.rs: Identifier)
--
-- In the concrete JSON/binary representation variables are strings
-- that begin with '%'.  Here we represent them as plain strings; the
-- leading-'%' invariant belongs to the well-formedness layer.
------------------------------------------------------------------------

Identifier : Set
Identifier = String

------------------------------------------------------------------------
-- Types  (ir_types.rs: IrType)
------------------------------------------------------------------------

data IrType : Set where
  native       : IrType
  -- ^ Element of the BLS12-381 scalar field.
  --   Serde name: "Scalar<BLS12-381>"

  jubjub-point : IrType
  -- ^ Point on the Jubjub elliptic curve.
  --   Serde name: "Point<Jubjub>"

------------------------------------------------------------------------
-- Typed identifier  (ir.rs: TypedIdentifier)
--
-- Used to declare the named inputs of a circuit.
------------------------------------------------------------------------

record TypedIdentifier : Set where
  constructor _⦂_
  field
    name   : Identifier
    val-t  : IrType

------------------------------------------------------------------------
-- Operands  (ir.rs: Operand)
--
-- An operand is either a reference to a previously bound variable or
-- an immediate field element.
------------------------------------------------------------------------

data Operand : Set where
  var : Identifier → Operand
  -- ^ Reference to a variable in circuit memory.

  imm : Fr → Operand
  -- ^ Immediate field element (written 0x… in the textual syntax).

------------------------------------------------------------------------
-- Instructions  (ir.rs: Instruction)
--
-- The 24 variants appear in the same order as in the Rust source.
-- Field names follow the Rust names, with underscores replaced by
-- hyphens and 'val_t' spelled as 'val-t'.
--
-- `bits` fields are u32 in Rust; we use ℕ here.
--
-- `outputs` / `inputs` fields that are Vec<Identifier> or Vec<Operand>
-- in Rust are List here.  Arity constraints (e.g. exactly 2 outputs
-- for DivModPowerOfTwo) belong to the typing layer.
------------------------------------------------------------------------

data Instruction : Set where

  -- Encode a typed value as raw Fr elements.
  --   Native      → 1 output
  --   JubjubPoint → 2 outputs (x and y coordinates)
  encode
    : (input   : Operand)
    → (outputs : List Identifier)
    → Instruction

  -- Decode raw Fr elements as a value of the given type.
  --   Native      ← 1 input
  --   JubjubPoint ← 2 inputs
  -- The circuit may become unsatisfiable if the inputs do not encode a
  -- valid value of the target type.
  decode
    : (inputs : List Operand)
    → (val-t  : IrType)
    → (output : Identifier)
    → Instruction

  -- Assert that cond = 1.  UB if cond ∉ {0, 1}.
  assert
    : (cond : Operand)
    → Instruction

  -- Conditionally select a value.  UB if bit ∉ {0, 1}.
  -- Output = a when bit = 1, b when bit = 0.
  cond-select
    : (bit    : Operand)
    → (a b    : Operand)
    → (output : Identifier)
    → Instruction

  -- Constrain val to fit in the given number of bits.
  constrain-bits
    : (val  : Operand)
    → (bits : ℕ)
    → Instruction

  -- Constrain a = b.
  constrain-eq
    : (a b : Operand)
    → Instruction

  -- Constrain val ∈ {0, 1}.
  constrain-to-boolean
    : (val : Operand)
    → Instruction

  -- Copy a value.  Does not extend the circuit; purely bookkeeping.
  copy
    : (val    : Operand)
    → (output : Identifier)
    → Instruction

  -- Declare public inputs under a boolean guard condition.
  -- Adds inputs to the public-input and activity transcript.
  -- No IR-level outputs.
  impact
    : (guard  : Operand)
    → (inputs : List Operand)
    → Instruction

  -- Multiply a Jubjub curve point by a Native scalar.
  ec-mul
    : (a      : Operand)
    → (scalar : Operand)
    → (output : Identifier)
    → Instruction

  -- Multiply the Jubjub group generator by a Native scalar.
  ec-mul-generator
    : (scalar : Operand)
    → (output : Identifier)
    → Instruction

  -- Hash a sequence of Native field elements to a Jubjub point.
  -- All inputs must be of type Native.
  hash-to-curve
    : (inputs : List Operand)
    → (output : Identifier)
    → Instruction

  -- Divide by 2^bits: outputs (val >> bits) and (val mod 2^bits).
  -- Exactly 2 outputs: [quotient, remainder].
  div-mod-power-of-two
    : (val     : Operand)
    → (bits    : ℕ)
    → (outputs : List Identifier)
    → Instruction

  -- Inverse of div-mod-power-of-two.
  -- Outputs divisor << bits | modulus, guaranteeing no field overflow
  -- and modulus < 2^bits.
  reconstitute-field
    : (divisor : Operand)
    → (modulus : Operand)
    → (bits    : ℕ)
    → (output  : Identifier)
    → Instruction

  -- Output val into the communications commitment.
  -- No IR-level output.
  output
    : (val : Operand)
    → Instruction

  -- Circuit-friendly (transient) hash: one output H(inputs).
  transient-hash
    : (inputs : List Operand)
    → (output : Identifier)
    → Instruction

  -- Long-term (persistent) hash with alignment metadata.
  -- Exactly 2 outputs (binary format).
  persistent-hash
    : (alignment : Alignment)
    → (inputs    : List Operand)
    → (outputs   : List Identifier)
    → Instruction

  -- Test equality.  Output is 1 iff a = b.
  test-eq
    : (a b    : Operand)
    → (output : Identifier)
    → Instruction

  -- Addition.
  -- Native:      field addition
  -- JubjubPoint: EC point addition
  add
    : (a b    : Operand)
    → (output : Identifier)
    → Instruction

  -- Prime-field multiplication (Native only).
  mul
    : (a b    : Operand)
    → (output : Identifier)
    → Instruction

  -- Prime-field negation (Native only).
  neg
    : (a      : Operand)
    → (output : Identifier)
    → Instruction

  -- Boolean NOT.  UB if a ∉ {0, 1}.
  not
    : (a      : Operand)
    → (output : Identifier)
    → Instruction

  -- Unsigned less-than in bits-bit precision.
  -- UB if a or b exceed 2^bits − 1.
  less-than
    : (a b    : Operand)
    → (bits   : ℕ)
    → (output : Identifier)
    → Instruction

  -- Retrieve the next value from the public input transcript.
  -- Outputs 0 if the guard condition fails (or is absent).
  public-input
    : (guard  : Maybe Operand)
    → (output : Identifier)
    → Instruction

  -- Retrieve the next value from the private witness transcript.
  -- Outputs 0 if the guard condition fails (or is absent).
  private-input
    : (guard  : Maybe Operand)
    → (output : Identifier)
    → Instruction

------------------------------------------------------------------------
-- Circuit source  (ir.rs: IrSource)
------------------------------------------------------------------------

record IrSource : Set where
  constructor mk-ir-source
  field
    inputs                        : List TypedIdentifier
    do-communications-commitment  : Bool
    instructions                  : List Instruction
