import PakFixedPolyomino.StandardBitTime
import Mathlib.Computability.Encoding

/-! # Metric reductions with fixed binary input and answer encodings

The postprocessor receives marked input bits followed by a separator and the
ordinary binary answer. Its runtime is measured in that actual binary length.
The pairing is fixed here for every reduction. An arbitrary `Encoding` field
could hide computation in its encoding function and is not used.

Polynomial bounds refer to the ordinary deterministic one-cell machines of
StandardBitTime. Membership and hardness use the ordinary nondeterministic
source class, with conventional initialization and all literal accepting
paths. No composition theorem or Pak reduction is asserted in this module.
-/

namespace PakFixedPolyomino.StandardBitMetric

open Computability StandardBitTime

/-- Each input bit is preceded by true; false separates the answer suffix. -/
def pairBits (x y : List Bool) : List Bool :=
  x.flatMap (fun b => [true, b]) ++ false :: y

def unpairBits : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: b :: rest => (unpairBits rest).map fun z => (b :: z.1, z.2)
  | [true] => none

@[simp] theorem pairBits_cons (b : Bool) (x y : List Bool) :
    pairBits (b :: x) y = true :: b :: pairBits x y := by
  simp [pairBits]

@[simp] theorem pairBits_nil (y : List Bool) : pairBits [] y = false :: y := rfl

@[simp] theorem unpair_pairBits (x y : List Bool) :
    unpairBits (pairBits x y) = some (x, y) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [unpairBits, ih]

theorem pairBits_injective :
    Function.Injective (fun z : List Bool × List Bool => pairBits z.1 z.2) := by
  intro a b hab
  have h := congrArg unpairBits hab
  simpa using h

@[simp] theorem pairBits_length (x y : List Bool) :
    (pairBits x y).length = 2 * x.length + 1 + y.length := by
  induction x with
  | nil => simp; omega
  | cons b x ih => simp [ih]; omega

def pairInputAnswer (x : List Bool) (answer : ℕ) : List Bool :=
  pairBits x (encodeNat answer)

theorem pairInputAnswer_length (x : List Bool) (answer : ℕ) :
    (pairInputAnswer x answer).length = 2 * x.length + 1 + (encodeNat answer).length :=
  pairBits_length x (encodeNat answer)

/-- A standard one-query metric reduction. Both maps have internally proved
ordinary tape-time witnesses. The answer is consumed/emitted in binary; the
postprocessor cannot choose its own input encoding or use a unit-cost ℕ cell. -/
structure Reduction (f g : List Bool → ℕ) where
  instanceMap : List Bool → List Bool
  postprocessor : List Bool → List Bool
  instance_polytime : PolyBitTime instanceMap
  postprocessor_polytime : PolyBitTime postprocessor
  correct : ∀ x, postprocessor (pairInputAnswer x (g (instanceMap x))) = encodeNat (f x)

def Reduces (f g : List Bool → ℕ) : Prop := Nonempty (Reduction f g)

def HardForSharpEXP (g : List Bool → ℕ) : Prop :=
  ∀ f, StandardNondeterministicMachine.SharpEXP f → Reduces f g

def CompleteForSharpEXP (g : List Bool → ℕ) : Prop :=
  StandardNondeterministicMachine.SharpEXP g ∧ HardForSharpEXP g

end PakFixedPolyomino.StandardBitMetric
