import PakFixedPolyomino.StandardBitLiteralLengthPower
import PakFixedPolyomino.StandardBitLiteralSquarePower
import PakFixedPolyomino.StandardBitVariableAddClosed
import PakFixedPolyomino.PakAllFrameWeightedOrdinarySourceReadout

/-! Physical binary compilers for the ORIGINAL reserve, copier radius and
first source scanner threshold. Large numeric capacities are encoded in
binary, using the retained polynomial payload's real literal length. No
source-time, execution, bit-cost or arithmetic-operation premise is assumed.
The scanner endpoint and guarded geometric readout remain separate. -/
namespace PakFixedPolyomino.PakSourceCapacityThresholdBitTime
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open ULogTernaryGeneratedMarginScanner (input states)
open ULogTernaryGeneratedMarginSourceClock (reserve)
open PakAllFrameOrdinarySourceCapacityNecessary (firstSourceScannerCapacity)
variable {ns nt : Nat}

theorem source_polyBitTime (p : Polynomial Nat) :
    PolyBitTime (StandardBitCountedPolynomialPayload.source p) := by
  have h := polyBitTime_comp (f := StandardBitRetainedPayload.payload)
    (g := fun x => StandardBitPolynomialPayload.iterateSquare (p.natDegree+1)
      (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p) x))
    StandardBitRetainedPayload.payload_polyBitTime
    (StandardBitPolynomialPayload.seeded_iteration_polyBitTime
      (StandardBitPolynomialPayload.coefficientTotal p) (p.natDegree+1))
  rw [show StandardBitCountedPolynomialPayload.source p=
    (fun x => StandardBitPolynomialPayload.iterateSquare (p.natDegree+1)
      (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p)
        (StandardBitRetainedPayload.payload x))) by funext x;rfl]
  exact h

def reserveBits (nt : Nat) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  encodeNat (reserve nt p x)

theorem reserve_polyBitTime (nt : Nat) (p : Polynomial Nat) :
    PolyBitTime (reserveBits nt p) := by
  have h := polyBitTime_comp
    (f := StandardBitCountedPolynomialPayload.source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (g := StandardBitLiteralSquarePower.powerBits 2)
    (source_polyBitTime (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (StandardBitLiteralSquarePower.power_polyBitTime 2)
  have he : StandardBitLiteralSquarePower.powerBits 2 ∘
      StandardBitCountedPolynomialPayload.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)=reserveBits nt p := by
    funext x
    simp only [Function.comp_apply,StandardBitLiteralSquarePower.powerBits,
      StandardBitLiteralSquarePower.exponent,reserveBits,reserve,
      ULogTernaryGeneratedHeadedSourceExpansion.width,
      ULogTernaryGeneratedHeadedSourceExpansion.polynomial,
      ULogTernaryGeneratedWindowBudget.width,ULogTernaryGeneratedSourceExpansion.width,
      ULogTernaryGuardedPumpDelimiterInput.width,StandardBitCountedPolynomialPayload.width,
      StandardBitPolynomialPayload.width,StandardBitCountedPolynomialPayload.source,pow_two]
  rwa [he] at h

def radiusBits (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  encodeNat (PakOuterULogBridge.copiedCoreRadius (input M p x))

theorem radius_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (radiusBits M p) := by
  have h := polyBitTime_comp (f := input M p)
    (g := StandardBitLiteralLengthPower.powerBits 2 8 8)
    (ULogTernaryGeneratedMarginScanner.input_polyBitTime M p)
    (StandardBitLiteralLengthPower.power_polyBitTime 2 8 8)
  have he : StandardBitLiteralLengthPower.powerBits 2 8 8 ∘ input M p=radiusBits M p := by
    funext x
    simp only [Function.comp_apply,StandardBitLiteralLengthPower.powerBits,
      StandardBitLiteralLengthPower.exponent,radiusBits,PakOuterULogBridge.copiedCoreRadius,
      MStarParserCopySpec.timeExponent,Nat.mul_add,Nat.mul_one]
  rwa [he] at h

def inputLengthBits (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  encodeNat (input M p x).length

theorem input_length_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (inputLengthBits M p) := by
  have h := polyBitTime_comp (f := input M p) (g := StandardBitLiteralLength.lengthBits)
    (ULogTernaryGeneratedMarginScanner.input_polyBitTime M p)
    StandardBitLiteralLength.length_polyBitTime
  have he : StandardBitLiteralLength.lengthBits ∘ input M p=inputLengthBits M p := by
    funext x
    simp only [Function.comp_apply,StandardBitLiteralLength.lengthBits,inputLengthBits]
  rwa [he] at h

theorem add_outputs_polyBitTime (f g : List Bool → List Bool)
    (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (fun raw => encodeNat (value (f raw)+value (g raw))) := by
  have h := polyBitTime_comp (StandardBitPairMaps.parallel_polyBitTime f g hf hg)
    StandardBitVariableAddClosed.add_polyBitTime
  have he : StandardBitVariableAdd.addBits ∘ StandardBitPairMaps.parallel f g=
      (fun raw => encodeNat (value (f raw)+value (g raw))) := by
    funext raw
    rw [Function.comp_apply,StandardBitPairMaps.parallel_pair,StandardBitVariableAdd.add_pair]
  rwa [he] at h

theorem threshold_formula (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    firstSourceScannerCapacity M p x=
      PakOuterULogBridge.copiedCoreRadius (input M p x)+(input M p x).length+
        reserve nt p x+(states M p-1)+4 := by
  have positive := PakOuterULogBridge.copiedCoreRadius_ge_256 (input M p x)
  unfold firstSourceScannerCapacity PakCopierReserveLowerBound.consumedBeforeFinalBuffer
  rw [ULogTernaryGeneratedMarginScannerSaturatedPrefix.minimum_eq_radius_add_length]
  unfold ULogTernaryGeneratedMarginScannerWeightedRawReadout.firstSaturatedCapacity
  omega

def thresholdBits (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  encodeNat (firstSourceScannerCapacity M p x)

theorem threshold_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (thresholdBits M p) := by
  have hr := add_outputs_polyBitTime (radiusBits M p) (inputLengthBits M p)
    (radius_polyBitTime M p) (input_length_polyBitTime M p)
  have hs := add_outputs_polyBitTime
    (fun raw => encodeNat (value (radiusBits M p raw)+value (inputLengthBits M p raw)))
    (reserveBits nt p) hr (reserve_polyBitTime nt p)
  have h := polyBitTime_comp
    (f := fun raw => encodeNat
      (value (encodeNat (value (radiusBits M p raw)+value (inputLengthBits M p raw)))+
        value (reserveBits nt p raw)))
    (g := fun w => encodeNat (value w+((states M p-1)+4))) hs
    (StandardBitFixedAdd.fixed_add_polyBitTime ((states M p-1)+4))
  have he : (fun w => encodeNat (value w+((states M p-1)+4))) ∘
      (fun raw => encodeNat
        (value (encodeNat (value (radiusBits M p raw)+value (inputLengthBits M p raw)))+
          value (reserveBits nt p raw)))=thresholdBits M p := by
    funext raw
    simp only [Function.comp_apply,radiusBits,inputLengthBits,reserveBits,value_encode_nat,
      thresholdBits,threshold_formula,Nat.add_assoc]
  rwa [he] at h

theorem threshold_spec (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (reserveBits nt p) ∧ PolyBitTime (radiusBits M p) ∧
    PolyBitTime (inputLengthBits M p) ∧ PolyBitTime (thresholdBits M p) ∧
    ∀ x,thresholdBits M p x=encodeNat (firstSourceScannerCapacity M p x) :=
  ⟨reserve_polyBitTime nt p,radius_polyBitTime M p,input_length_polyBitTime M p,
    threshold_polyBitTime M p,fun _ => rfl⟩

end
end PakFixedPolyomino.PakSourceCapacityThresholdBitTime
