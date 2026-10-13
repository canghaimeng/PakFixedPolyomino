import PakFixedPolyomino.PakGuardedSourceReadoutWeightBitTime
import PakFixedPolyomino.PakGuardedReadoutStorageBounds

/-! Exact physical assembly of the ORIGINAL every-raw guarded postprocessor.
Only the ordinary variable-division compiler is explicit in this intermediate
module. The actual adder/subtractor, original baseline DP, amplifier and
coefficient powers, source geometric weight and literal guard are supplied
internally. The division premise must be discharged by the separately owned
ordinary div/mod machine before claiming closed metric-map compilation. -/
set_option maxRecDepth 4096
namespace PakFixedPolyomino.PakGuardedReadoutBitAssembly
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitPairFirstCompaction (firstBits firstBits_pair)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open PakFixedWeightedOracleLengthGuard (macroSide guardedPostprocessor guardedAnswer)
open PakFixedWeightedPhysicalSourceReadout (sourceAnswer)
open PakFixedWeightedRegisterInventory (params)
open PakWeightedCoupledCoefficient (weightedExtractionQ)
variable {ns nt : Nat}

def divideBits (raw : List Bool) : List Bool :=
  encodeNat (value (firstBits raw)/value (secondBits raw))

def divideOutputs (f g : List Bool → List Bool) (raw : List Bool) : List Bool :=
  encodeNat (value (f raw)/value (g raw))

theorem divide_outputs_polyBitTime (f g : List Bool → List Bool)
    (hf : PolyBitTime f) (hg : PolyBitTime g) (hd : PolyBitTime divideBits) :
    PolyBitTime (divideOutputs f g) := by
  have h := polyBitTime_comp (StandardBitPairMaps.parallel_polyBitTime f g hf hg) hd
  have he : divideBits ∘ StandardBitPairMaps.parallel f g=divideOutputs f g := by
    funext raw
    simp only [Function.comp_apply,divideBits,StandardBitPairMaps.parallel_pair,
      firstBits_pair,secondBits_pair,divideOutputs]
  rwa [he] at h

def subtractOutputs (f g : List Bool → List Bool) (raw : List Bool) : List Bool :=
  encodeNat (value (f raw)-value (g raw))

theorem subtract_outputs_polyBitTime (f g : List Bool → List Bool)
    (hf : PolyBitTime f) (hg : PolyBitTime g) : PolyBitTime (subtractOutputs f g) := by
  have h := polyBitTime_comp (StandardBitPairMaps.parallel_polyBitTime f g hf hg)
    StandardBitVariableSubtractClosed.subtract_polyBitTime
  have he : StandardBitVariableSubtractLoop.subtractBits ∘
      StandardBitPairMaps.parallel f g=subtractOutputs f g := by
    funext raw
    simp only [Function.comp_apply,StandardBitVariableSubtractLoop.subtractBits,
      StandardBitPairMaps.parallel_pair,firstBits_pair,secondBits_pair,subtractOutputs]
  rwa [he] at h

def amplifierQuotient (M : Machine ns nt 2) (p : Polynomial Nat) : List Bool → List Bool :=
  divideOutputs secondBits (PakGuardedAmplifierBitTime.denominator params.amp M p)

theorem amplifier_quotient_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (amplifierQuotient M p) :=
  divide_outputs_polyBitTime _ _ secondBits_polyBitTime
    (PakGuardedArithmeticBitTimeClosed.amplifier_polyBitTime params.amp M p) hd

def liveBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (value (amplifierQuotient M p raw)-1)

theorem live_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (liveBits M p) :=
  polyBitTime_comp (amplifier_quotient_polyBitTime M p hd)
    StandardBitCanonicalDecrement.predecessor_polyBitTime

def coefficientQuotient (M : Machine ns nt 2) (p : Polynomial Nat) : List Bool → List Bool :=
  divideOutputs (liveBits M p) (PakGuardedCoefficientBitTime.denominator weightedExtractionQ M p)

theorem coefficient_quotient_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (coefficientQuotient M p) :=
  divide_outputs_polyBitTime _ _ (live_polyBitTime M p hd)
    (PakGuardedArithmeticBitTimeClosed.coefficient_polyBitTime weightedExtractionQ M p) hd

def residualBits (M : Machine ns nt 2) (p : Polynomial Nat) : List Bool → List Bool :=
  subtractOutputs (coefficientQuotient M p) (PakWeightedDPIterationBitTime.dpBits M p)

theorem residual_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (residualBits M p) :=
  subtract_outputs_polyBitTime _ _ (coefficient_quotient_polyBitTime M p hd)
    (PakGuardedArithmeticBitTimeClosed.dp_polyBitTime M p)

def numeratorBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (value (residualBits M p raw)+
    value (PakGuardedSourceReadoutWeightBitTime.weightBits M p raw)-1)

theorem sum_predecessor_outputs_polyBitTime (f g : List Bool → List Bool)
    (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (fun raw => encodeNat (value (f raw)+value (g raw)-1)) := by
  have ha := PakSourceCapacityThresholdBitTime.add_outputs_polyBitTime f g hf hg
  have h := polyBitTime_comp
    (f := fun raw => encodeNat (value (f raw)+value (g raw)))
    (g := fun w => encodeNat (value w-1))
    ha StandardBitCanonicalDecrement.predecessor_polyBitTime
  have he : (fun w => encodeNat (value w-1)) ∘
      (fun raw => encodeNat (value (f raw)+value (g raw)))=
        (fun raw => encodeNat (value (f raw)+value (g raw)-1)) := by
    funext raw
    simp only [Function.comp_apply,value_encode_nat]
  rwa [he] at h

theorem numerator_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (numeratorBits M p) :=
  sum_predecessor_outputs_polyBitTime _ _ (residual_polyBitTime M p hd)
    (PakGuardedSourceReadoutWeightBitTime.weight_polyBitTime M p)

def coreBits (M : Machine ns nt 2) (p : Polynomial Nat) : List Bool → List Bool :=
  divideOutputs (numeratorBits M p) (PakGuardedSourceReadoutWeightBitTime.weightBits M p)

theorem core_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (coreBits M p) :=
  divide_outputs_polyBitTime _ _ (numerator_polyBitTime M p hd)
    (PakGuardedSourceReadoutWeightBitTime.weight_polyBitTime M p) hd

theorem core_pair (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool)
    (hg : macroSide M p x<y.length) :
    coreBits M p (pairBits x y)=encodeNat (sourceAnswer M p x (value y)) := by
  simp only [coreBits,divideOutputs,numeratorBits,residualBits,subtractOutputs,
    coefficientQuotient,liveBits,amplifierQuotient,secondBits_pair,
    PakGuardedAmplifierBitTime.denominator_pair,
    PakGuardedCoefficientBitTime.denominator_pair,
    PakWeightedDPIterationBitTime.dp_pair_baseline,
    PakGuardedSourceReadoutWeightBitTime.weight_pair,if_pos hg,value_encode_nat]
  rfl

def postprocessorBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  if PakGuardComparatorBitTimeClosed.predicate M p raw then coreBits M p raw else []

theorem postprocessor_eq (M : Machine ns nt 2) (p : Polynomial Nat) :
    postprocessorBits M p=guardedPostprocessor M p := by
  funext raw
  cases hp : unpairBits raw with
  | none =>
    simp only [postprocessorBits,PakGuardComparatorBitTimeClosed.predicate_none M p raw hp,
      Bool.false_eq_true,if_false,guardedPostprocessor,hp]
  | some xy =>
    obtain ⟨x,y⟩ := xy
    rw [StandardBitPairProjection.unpairBits_eq_some.mp hp]
    simp only [postprocessorBits,PakGuardComparatorBitTimeClosed.predicate_pair,
      decide_eq_true_eq,guardedPostprocessor,unpair_pairBits,guardedAnswer]
    split_ifs with hg
    · exact core_pair M p x y hg
    · rfl

theorem postprocessor_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) : PolyBitTime (guardedPostprocessor M p) := by
  have h := StandardBitConditionalBitTime.conditional_polyBitTime
    (PakGuardComparatorBitTimeClosed.predicate M p) (fun _ => []) (coreBits M p)
    (PakGuardComparatorBitTimeClosed.predicate_polyBitTime M p)
    StandardBitPairSanitize.empty_polyBitTime (core_polyBitTime M p hd)
  change PolyBitTime (postprocessorBits M p) at h
  rwa [postprocessor_eq] at h

theorem assembly_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (hd : PolyBitTime divideBits) :
    PolyBitTime (guardedPostprocessor M p) ∧
    postprocessorBits M p=guardedPostprocessor M p ∧
    (∀ raw,(guardedPostprocessor M p raw).length≤raw.length) :=
  ⟨postprocessor_polyBitTime M p hd,postprocessor_eq M p,
    PakGuardedReadoutStorageBounds.total_postprocessor_length M p⟩

end
end PakFixedPolyomino.PakGuardedReadoutBitAssembly
