import PakFixedPolyomino.StandardBitVariableSubtractClosed
import PakFixedPolyomino.PakGuardedCapacityGeometryBitTime
import PakFixedPolyomino.StandardBitPolynomialBoundedPower
import PakFixedPolyomino.PakAllFrameWeightedOrdinarySourceReadout

/-! Physical compilation of the ORIGINAL guarded geometric source weight.
The actual scanner exponent S-L is computed by the closed subtraction loop.
Its bound by the original raw length supplies the actual power-loop bounds;
canonical decrement then emits 2^(S-L)-1. Invalid/short answers and malformed
pairs give exponent0 and clean empty output. All compiler premises are
supplied internally; the original literal answer-length guard is retained. -/
namespace PakFixedPolyomino.PakGuardedSourceReadoutWeightBitTime
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakGuardedCapacityGeometryBitTime (exponent subtractionInput)
open PakFixedWeightedOracleLengthGuard (macroSide)
open PakAllFrameWeightedOrdinarySourceReadout (sourceReadoutWeight)
variable {ns nt : Nat}

def exponentBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (exponent M p raw)

theorem exponent_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (exponentBits M p) := by
  have h := polyBitTime_comp
    (PakGuardedCapacityGeometryBitTime.subtraction_input_polyBitTime M p)
    StandardBitVariableSubtractClosed.subtract_polyBitTime
  have he : StandardBitVariableSubtractLoop.subtractBits ∘ subtractionInput M p=
      exponentBits M p := by
    funext raw
    simp only [Function.comp_apply,StandardBitVariableSubtractLoop.subtractBits,
      PakGuardedCapacityGeometryBitTime.subtraction_input_values,exponentBits]
  rwa [he] at h

def powerBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (2^exponent M p raw)

theorem power_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (powerBits M p) :=
  StandardBitPolynomialBoundedPower.power_polyBitTime 2 (exponent M p) Polynomial.X
    (exponent_polyBitTime M p)
    (by intro raw;simpa only [Polynomial.eval_X] using
      PakGuardedCapacityGeometryBitTime.exponent_le M p raw)

def weightBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (2^exponent M p raw-1)

theorem weight_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (weightBits M p) := by
  have h := polyBitTime_comp (power_polyBitTime M p)
    StandardBitCanonicalDecrement.predecessor_polyBitTime
  have he : (fun w => encodeNat (value w-1)) ∘ powerBits M p=weightBits M p := by
    funext raw
    simp only [Function.comp_apply,powerBits,value_encode_nat,weightBits]
  rwa [he] at h

theorem weight_pair (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    weightBits M p (pairBits x y)=
      if macroSide M p x<y.length then encodeNat (sourceReadoutWeight M p x) else [] := by
  rw [weightBits,PakGuardedCapacityGeometryBitTime.exponent_pair]
  split_ifs
  · rfl
  · rfl

theorem weight_none (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) (h : unpairBits raw=none) : weightBits M p raw=[] := by
  rw [weightBits,PakGuardedCapacityGeometryBitTime.exponent_none M p raw h]
  rfl

theorem weight_spec (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (exponentBits M p) ∧ PolyBitTime (powerBits M p) ∧
    PolyBitTime (weightBits M p) ∧
    (∀ raw,exponent M p raw≤raw.length) ∧
    (∀ x y,weightBits M p (pairBits x y)=
      if macroSide M p x<y.length then encodeNat (sourceReadoutWeight M p x) else []) ∧
    (∀ raw,unpairBits raw=none → weightBits M p raw=[]) :=
  ⟨exponent_polyBitTime M p,power_polyBitTime M p,weight_polyBitTime M p,
    PakGuardedCapacityGeometryBitTime.exponent_le M p,weight_pair M p,weight_none M p⟩

end
end PakFixedPolyomino.PakGuardedSourceReadoutWeightBitTime
