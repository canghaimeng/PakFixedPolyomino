import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerInputBounds
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSquareFrontFuel
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerWeightedRawReadout

/-! Concrete square padding and source time for the weighted qStart count.
The required prefix lies inside the actual low-capacity physical time region;
the earlier numerical horizon/padding/time premises are supplied internally.
ALLouter inversion and the weighted full-frame/baseline census are separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSaturatedPrefix
noncomputable section
open ULogTernaryGeneratedMarginScanner (input states)
open ULogTernaryGeneratedMarginScannerInputBounds
open ULogTernaryGeneratedMarginScannerSquareFrontFuel
open ULogTernaryGeneratedMarginScannerWeightedRawReadout
open PakGeneralCapacityOuterFrontEnvelope PakSlotOneScannerMultiplicity
open PakCopierReserveLowerBound PakWeightedCapacityCeilingReadout
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

theorem minimum_eq_radius_add_length (y : ConcretePakSide.Word) :
    minimumSuccessfulWorkCount y.length = PakOuterULogBridge.copiedCoreRadius y + y.length := by
  unfold minimumSuccessfulWorkCount
  rw [MStarCopierExecution.copier_width_eq_time_bound]
  rfl

def saturatedPrefixEnd (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  firstSaturatedCapacity M p x + (2 ^ p.eval x.length + 1) + 2

def remainingCapacityCount (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  scannerCapacityCount (input M p x) - consumedBeforeFinalBuffer (input M p x).length

theorem prefix_end_le_radius_length (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : saturatedPrefixEnd M p x ≤
      2 * PakOuterULogBridge.copiedCoreRadius (input M p x) + (input M p x).length + 7 := by
  have reserve := reserve_le_radius M p x
  have machine := states_le_input_length M p x
  have cutoff := source_cutoff_le_radius M p x
  have live := ULogTernaryGeneratedMarginScanner.states_ge M p
  unfold saturatedPrefixEnd firstSaturatedCapacity
  omega

theorem physical_prefix_end_le_five_radius (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : consumedBeforeFinalBuffer (input M p x).length + saturatedPrefixEnd M p x ≤
      5 * PakOuterULogBridge.copiedCoreRadius (input M p x) + 7 := by
  have prefixBound := prefix_end_le_radius_length M p x
  have size := input_length_le_radius (input M p x)
  unfold consumedBeforeFinalBuffer
  rw [minimum_eq_radius_add_length]
  omega

theorem sixteen_physical_prefix_end_le_side (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    16 * (consumedBeforeFinalBuffer (input M p x).length + saturatedPrefixEnd M p x) ≤
      ConcretePakSide.sideValue (input M p x) := by
  let R := PakOuterULogBridge.copiedCoreRadius (input M p x)
  have prefixBound := physical_prefix_end_le_five_radius M p x
  have large : 256 ≤ R := PakOuterULogBridge.copiedCoreRadius_ge_256 _
  have quadratic : 16 * (5 * R + 7) ≤ R ^ 2 := by nlinarith
  have growing : R ^ 2 ≤ R ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (Nat.mul_le_mul_left 16 prefixBound).trans
    (quadratic.trans (growing.trans (radius_nine_le_side _)))

theorem parser_extent_le_two_radius (y : ConcretePakSide.Word) :
    (ConcretePakSide.encodedWord y).length + 5 ≤ 2 * PakOuterULogBridge.copiedCoreRadius y := by
  have linear := parser_linear_le_pow y.length
  have exponent : 2 ^ (y.length + 9) ≤ 2 ^ (8 * (y.length + 1) + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have twice : 2 ^ (8 * (y.length + 1) + 1) = 2 * PakOuterULogBridge.copiedCoreRadius y := by
    unfold PakOuterULogBridge.copiedCoreRadius MStarParserCopySpec.timeExponent
    rw [pow_succ]
    ring
  rw [twice] at exponent
  rw [ConcretePakSide.encodedWord_length]
  omega

theorem radius_le_physical_prefix_end (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : PakOuterULogBridge.copiedCoreRadius (input M p x) ≤
      consumedBeforeFinalBuffer (input M p x).length + saturatedPrefixEnd M p x := by
  have sourcePositive : 1 ≤ (2 ^ p.eval x.length : Nat) := Nat.one_le_two_pow
  have live := ULogTernaryGeneratedMarginScanner.states_ge M p
  have large := PakOuterULogBridge.copiedCoreRadius_ge_256 (input M p x)
  unfold consumedBeforeFinalBuffer
  rw [minimum_eq_radius_add_length]
  unfold saturatedPrefixEnd firstSaturatedCapacity
  omega

theorem saturated_prefix_inside_capacity_count (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : saturatedPrefixEnd M p x ≤ remainingCapacityCount M p x := by
  have low := sixteen_physical_prefix_end_le_side M p x
  have parser := parser_extent_le_two_radius (input M p x)
  have radius := radius_le_physical_prefix_end M p x
  unfold remainingCapacityCount scannerCapacityCount
  rw [PakSideScanner.sideScannerBits_length]
  omega

theorem saturated_prefix_actual_minimum (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (enough : firstSaturatedCapacity M p x ≤ K) :
    minimumSuccessfulWorkCount (input M p x).length ≤
      consumedBeforeFinalBuffer (input M p x).length + K := by
  have size := minimum_eq_radius_add_length (input M p x)
  have positive := PakOuterULogBridge.copiedCoreRadius_ge_256 (input M p x)
  unfold firstSaturatedCapacity at enough
  unfold consumedBeforeFinalBuffer
  omega

theorem saturated_prefix_suffix_time (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (enough : firstSaturatedCapacity M p x ≤ K)
    (before : K < saturatedPrefixEnd M p x) :
    ULogTernaryGeneratedMarginScannerPhysicalFuel.totalPhysicalFuelBound M p x ≤
      residualSquareCutoff M p x (consumedBeforeFinalBuffer (input M p x).length + K) := by
  apply low_capacity_suffix_fuel_le_cutoff
  · exact saturated_prefix_actual_minimum M p x K enough
  · have prefixBound := sixteen_physical_prefix_end_le_side M p x
    omega

theorem concrete_square_weighted_qStart_readout (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    (weightedCapacitySum (remainingCapacityCount M p x)
        (rawCapacityCounts M p x (fun K => residualSquareCutoff M p x
          (consumedBeforeFinalBuffer (input M p x).length + K))) +
      fullCapacityWeight (remainingCapacityCount M p x) (firstSaturatedCapacity M p x) - 1) /
      fullCapacityWeight (remainingCapacityCount M p x) (firstSaturatedCapacity M p x) =
        acceptingCount M x (2 ^ p.eval x.length) := by
  apply weighted_raw_readout M p x ht (remainingCapacityCount M p x)
    (saturatedPrefixEnd M p x)
  · exact saturated_prefix_inside_capacity_count M p x
  · exact Nat.le_refl _
  · exact saturated_prefix_suffix_time M p x

end
end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSaturatedPrefix
