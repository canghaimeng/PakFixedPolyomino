import PakFixedPolyomino.PakWeightedDPIterationBitTime
import PakFixedPolyomino.StandardBitVariableMultiplyLoop
import PakFixedPolyomino.StandardBitPolynomialBoundedPower

/-! The actual amplifier denominator under the ORIGINAL literal-answer guard.
Its quadratic exponent is physically computed by binary shift-and-add, then
an initialized fixed-base loop supplies every power tick and intermediate
width. The actual ordinary adder Poly proof remains the sole compiler premise.
Malformed/over-budget helper inputs return one; sourceAnswer remains separate. -/
namespace PakFixedPolyomino.PakGuardedAmplifierBitTime
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakWeightedDPIterationBitTime (side sideBits sideBits_eq sideBits_polyBitTime side_le)
variable {ns nt : Nat}

def exponent (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : Nat :=
  amplifierExponent (side M p raw)
def denominator (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (c^exponent M p raw)

theorem exponent_le (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    exponent M p raw≤2*raw.length*raw.length := by
  have hn := side_le M p raw
  have ht : side M p raw-1≤raw.length := (Nat.sub_le _ _).trans hn
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) ht
  unfold exponent amplifierExponent
  exact hm

theorem exponent_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime (fun raw => encodeNat (exponent M p raw)) := by
  have hs := sideBits_polyBitTime M p
  have hd := polyBitTime_comp hs StandardBitCanonicalDecrement.predecessor_polyBitTime
  have hp := StandardBitPairMaps.parallel_polyBitTime (sideBits M p)
    (fun raw => encodeNat (value (sideBits M p raw)-1)) hs hd
  have hm := polyBitTime_comp hp (StandardBitVariableMultiplyLoop.multiply_polyBitTime hadd)
  have ht := polyBitTime_comp hm (StandardBitFixedMultiply.fixed_multiply_polyBitTime 2)
  have heq : (fun w => encodeNat (2*value w)) ∘
      (StandardBitVariableMultiplyLoop.multiplyBits ∘ StandardBitPairMaps.parallel
        (sideBits M p) (fun raw => encodeNat (value (sideBits M p raw)-1)))=
      (fun raw => encodeNat (exponent M p raw)) := by
    funext raw
    simp only [Function.comp_apply,StandardBitPairMaps.parallel_pair,
      StandardBitVariableMultiplyLoop.multiply_pair,value_encode_nat,sideBits_eq,
      exponent,amplifierExponent]
    congr 1
    ring
  rwa [heq] at ht

theorem denominator_polyBitTime (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime (denominator c M p) := by
  exact StandardBitPolynomialBoundedPower.power_polyBitTime c (exponent M p) (2*Polynomial.X*Polynomial.X)
    (exponent_polyBitTime M p hadd) (fun raw => by
      simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using exponent_le M p raw)

theorem denominator_pair (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    denominator c M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then c^amplifierExponent (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 1) := by
  simp only [denominator,exponent,PakWeightedDPIterationBitTime.side,
    PakGuardComparatorBitTimeClosed.predicate_pair,PakGuardCounterBitTimeClosed.counter_value_pair,
    decide_eq_true_eq]
  split_ifs
  · rfl
  · simp only [amplifierExponent,Nat.mul_zero,Nat.zero_mul,pow_zero]

theorem denominator_none (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) (h : unpairBits raw=none) : denominator c M p raw=[true] := by
  simp only [denominator,exponent,PakWeightedDPIterationBitTime.side,
    PakGuardComparatorBitTimeClosed.predicate_none M p raw h,Bool.false_eq_true,if_false,
    amplifierExponent,Nat.mul_zero,Nat.zero_mul,pow_zero]
  rfl
theorem denominator_spec (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime (denominator c M p) ∧
    (∀ x y,denominator c M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then c^amplifierExponent (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 1)) ∧
    (∀ raw,unpairBits raw=none → denominator c M p raw=[true]) :=
  ⟨denominator_polyBitTime c M p hadd,denominator_pair c M p,denominator_none c M p⟩

end
end PakFixedPolyomino.PakGuardedAmplifierBitTime
