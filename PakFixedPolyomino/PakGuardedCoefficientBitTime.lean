import PakFixedPolyomino.PakWeightedDPIterationBitTime
import PakFixedPolyomino.StandardBitPolynomialBoundedPower

/-! The original coefficient denominator has a linear exponent. Its entire
ALLraw bit-time implementation is internal and independent of the unfinished
variable adder. The original literal-answer guard and actual full-boundary
qDegree are preserved; malformed/over-budget helper inputs return one. -/
namespace PakFixedPolyomino.PakGuardedCoefficientBitTime
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakWeightedDPIterationBitTime (side sideBits sideBits_eq sideBits_polyBitTime side_le)
variable {ns nt : Nat}

def minusFour (w : List Bool) : List Bool := encodeNat (value w-4)

theorem minusFour_polyBitTime : PolyBitTime minusFour := by
  let pred : List Bool → List Bool := fun w => encodeNat (value w-1)
  have hp : PolyBitTime pred := StandardBitCanonicalDecrement.predecessor_polyBitTime
  have h2 := polyBitTime_comp hp hp
  have h4 := polyBitTime_comp h2 h2
  have heq : (pred ∘ pred) ∘ (pred ∘ pred)=minusFour := by
    funext w
    simp only [pred,Function.comp_apply,value_encode_nat,Nat.sub_sub,minusFour]
  rwa [heq] at h4

def exponent (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : Nat :=
  4*side M p raw-4

def denominator (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (c^exponent M p raw)

theorem exponent_le (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    exponent M p raw≤4*raw.length :=
  (Nat.sub_le _ _).trans (Nat.mul_le_mul_left 4 (side_le M p raw))

theorem exponent_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (fun raw => encodeNat (exponent M p raw)) := by
  have hm := polyBitTime_comp (sideBits_polyBitTime M p) (StandardBitFixedMultiply.fixed_multiply_polyBitTime 4)
  have ht := polyBitTime_comp hm minusFour_polyBitTime
  have heq : minusFour ∘ ((fun w => encodeNat (4*value w)) ∘ sideBits M p)=
      (fun raw => encodeNat (exponent M p raw)) := by
    funext raw
    simp only [Function.comp_apply,minusFour,value_encode_nat,sideBits_eq,exponent]
  rwa [heq] at ht

theorem denominator_polyBitTime (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (denominator c M p) :=
  StandardBitPolynomialBoundedPower.power_polyBitTime c (exponent M p) (4*Polynomial.X)
    (exponent_polyBitTime M p) (fun raw => by
      simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using exponent_le M p raw)

theorem linear_degree {n : Nat} (hn : 2≤n) :
    PakAmpCoefficient.BoundaryMask.full.qDegree n n=4*n-4 := by
  rw [PakAmpCoefficient.BoundaryMask.full_qDegree hn hn]
  omega

theorem denominator_pair (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    denominator c M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then c^PakAmpCoefficient.BoundaryMask.full.qDegree
        (PakFixedWeightedOracleLengthGuard.macroSide M p x)
        (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 1) := by
  simp only [denominator,exponent,PakWeightedDPIterationBitTime.side,
    PakGuardComparatorBitTimeClosed.predicate_pair,PakGuardCounterBitTimeClosed.counter_value_pair,
    decide_eq_true_eq]
  split_ifs
  · rw [linear_degree (PakFixedWeightedOracleLengthGuard.macro_side_ge_two M p x)]
  · simp only [Nat.mul_zero,Nat.zero_sub,pow_zero]

theorem denominator_none (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) (h : unpairBits raw=none) : denominator c M p raw=[true] := by
  simp only [denominator,exponent,PakWeightedDPIterationBitTime.side,
    PakGuardComparatorBitTimeClosed.predicate_none M p raw h,Bool.false_eq_true,if_false,
    Nat.mul_zero,Nat.zero_sub,pow_zero]
  rfl

theorem denominator_spec (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (denominator c M p) ∧
    (∀ x y,denominator c M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then c^PakAmpCoefficient.BoundaryMask.full.qDegree
        (PakFixedWeightedOracleLengthGuard.macroSide M p x)
        (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 1)) ∧
    (∀ raw,unpairBits raw=none → denominator c M p raw=[true]) :=
  ⟨denominator_polyBitTime c M p,denominator_pair c M p,denominator_none c M p⟩
end
end PakFixedPolyomino.PakGuardedCoefficientBitTime
