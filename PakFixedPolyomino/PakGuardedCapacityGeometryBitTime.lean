import PakFixedPolyomino.PakSourceCapacityThresholdBitTime
import PakFixedPolyomino.PakGuardedArithmeticBitTimeClosed

/-! Actual subtraction inputs for the ORIGINAL scanner-capacity exponent.
The generated parser occupies 74*input length+80 cells including its fixed
offsets. The first-source threshold remains its actual previously proved
value. Input construction is a physical bit compiler on EVERYraw; actual
variable subtraction/power/readout compilation remains separate. -/
namespace PakFixedPolyomino.PakGuardedCapacityGeometryBitTime
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open ULogTernaryGeneratedMarginScanner (input)
open PakFixedWeightedOracleLengthGuard (macroSide)
open PakAllFrameOrdinarySourceCapacityNecessary (firstSourceScannerCapacity)
open PakSourceCapacityThresholdBitTime (inputLengthBits thresholdBits add_outputs_polyBitTime)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open PakWeightedDPIterationBitTime (side sideBits sideBits_eq sideBits_polyBitTime side_le)
variable {ns nt : Nat}

def extent (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  74*(input M p x).length+80
def extentBits (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  encodeNat (extent M p x)

theorem extent_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (extentBits M p) := by
  have hm := polyBitTime_comp (PakSourceCapacityThresholdBitTime.input_length_polyBitTime M p)
    (StandardBitFixedMultiply.fixed_multiply_polyBitTime 74)
  have h := polyBitTime_comp hm (StandardBitFixedAdd.fixed_add_polyBitTime 80)
  have he : (fun w => encodeNat (value w+80)) ∘
      ((fun w => encodeNat (74*value w)) ∘ inputLengthBits M p)=extentBits M p := by
    funext x
    simp only [Function.comp_apply,inputLengthBits,value_encode_nat,extentBits,extent]
  rwa [he] at h

theorem capacity_arithmetic (n m : Nat) :
    n-2-(74*m+75+3)=n-(74*m+80) := by omega

theorem scanner_capacity_formula (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    PakSlotOneScannerMultiplicity.scannerCapacityCount (input M p x)=
      macroSide M p x-extent M p x := by
  simpa only [PakSlotOneScannerMultiplicity.scannerCapacityCount,
    PakSideScanner.sideScannerBits_length,ConcretePakSide.encodedWord_length,extent,macroSide] using
    capacity_arithmetic (ConcretePakSide.sideValue (input M p x)) (input M p x).length

def subtrahendBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (extent M p (firstBits raw)+firstSourceScannerCapacity M p (firstBits raw))

theorem subtrahend_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (subtrahendBits M p) := by
  have ha := add_outputs_polyBitTime (extentBits M p) (thresholdBits M p)
    (extent_polyBitTime M p) (PakSourceCapacityThresholdBitTime.threshold_polyBitTime M p)
  have h := polyBitTime_comp (f := firstBits)
    (g := fun x => encodeNat (value (extentBits M p x)+value (thresholdBits M p x)))
    first_polyBitTime ha
  have he : (fun x => encodeNat (value (extentBits M p x)+value (thresholdBits M p x))) ∘
      firstBits=subtrahendBits M p := by
    funext raw
    simp only [Function.comp_apply,extentBits,thresholdBits,value_encode_nat,subtrahendBits]
  rwa [he] at h

def subtractionInput (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  pairBits (sideBits M p raw) (subtrahendBits M p raw)

theorem subtraction_input_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (subtractionInput M p) := by
  have h := StandardBitPairMaps.parallel_polyBitTime (sideBits M p) (subtrahendBits M p)
    (sideBits_polyBitTime M p) (subtrahend_polyBitTime M p)
  have he : StandardBitPairMaps.parallel (sideBits M p) (subtrahendBits M p)=
      subtractionInput M p := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [he] at h

def exponent (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : Nat :=
  side M p raw-(extent M p (firstBits raw)+firstSourceScannerCapacity M p (firstBits raw))

theorem exponent_le (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    exponent M p raw≤raw.length := (Nat.sub_le _ _).trans (side_le M p raw)

theorem exponent_pair (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    exponent M p (pairBits x y)=
      if macroSide M p x<y.length then
        PakSlotOneScannerMultiplicity.scannerCapacityCount (input M p x)-
          firstSourceScannerCapacity M p x else 0 := by
  simp only [exponent,side,PakGuardComparatorBitTimeClosed.predicate_pair,
    PakGuardCounterBitTimeClosed.counter_value_pair,firstBits_pair,decide_eq_true_eq]
  split_ifs
  · rw [scanner_capacity_formula,Nat.sub_sub]
  · exact Nat.zero_sub _

theorem exponent_none (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) (h : unpairBits raw=none) : exponent M p raw=0 := by
  simp only [exponent,side,PakGuardComparatorBitTimeClosed.predicate_none M p raw h,
    Bool.false_eq_true,if_false,Nat.zero_sub]

theorem subtraction_input_values (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    value (StandardBitPairFirstCompaction.firstBits (subtractionInput M p raw))-
      value (StandardBitPairProjection.secondBits (subtractionInput M p raw))=
        exponent M p raw := by
  simp only [subtractionInput,firstBits_pair,StandardBitPairProjection.secondBits_pair,
    sideBits_eq,subtrahendBits,value_encode_nat,exponent]

theorem geometry_spec (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (extentBits M p) ∧ PolyBitTime (subtrahendBits M p) ∧
    PolyBitTime (subtractionInput M p) ∧
    (∀ raw,exponent M p raw≤raw.length) ∧
    (∀ x y,exponent M p (pairBits x y)=
      if macroSide M p x<y.length then
        PakSlotOneScannerMultiplicity.scannerCapacityCount (input M p x)-
          firstSourceScannerCapacity M p x else 0) ∧
    (∀ raw,unpairBits raw=none → exponent M p raw=0) :=
  ⟨extent_polyBitTime M p,subtrahend_polyBitTime M p,subtraction_input_polyBitTime M p,
    exponent_le M p,exponent_pair M p,exponent_none M p⟩

end
end PakFixedPolyomino.PakGuardedCapacityGeometryBitTime
