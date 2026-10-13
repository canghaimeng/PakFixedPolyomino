import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSaturatedPrefix
import PakFixedPolyomino.PakAllFrameOrdinarySourceCapacityNecessary
import PakFixedPolyomino.StandardMachineAcceptingCountBound

/-! The literal scanner-capacity interval used by the ALLframe ceiling.
The copier minimum, physical square slack, count bound and finite-capacity
containment follow from the actual generated input. These numerical facts
do not assert a bit-time algorithm or an ALLframe source-count identity. -/
namespace PakFixedPolyomino.PakAllFrameScannerSaturatedPrefixBounds
noncomputable section
open StandardNondeterministicMachine (Machine acceptingCount)
open ULogTernaryGeneratedMarginScanner (input)
open ULogTernaryGeneratedMarginScannerSaturatedPrefix
open ULogTernaryGeneratedMarginScannerWeightedRawReadout (firstSaturatedCapacity)
open PakAllFrameOrdinarySourceCapacityNecessary (firstSourceScannerCapacity)
open PakCopierReserveLowerBound PakSlotOneScannerMultiplicity
variable {ns nt : Nat}

def scannerSaturatedPrefixEnd (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : Nat :=
  consumedBeforeFinalBuffer (input M p x).length + saturatedPrefixEnd M p x

theorem threshold_lt_prefix_end (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    firstSourceScannerCapacity M p x < scannerSaturatedPrefixEnd M p x := by
  have source_nonneg : 0 ≤ (2 ^ p.eval x.length : Nat) := Nat.zero_le _
  unfold firstSourceScannerCapacity scannerSaturatedPrefixEnd saturatedPrefixEnd
  omega

theorem prefix_end_le_capacity_count (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    scannerSaturatedPrefixEnd M p x ≤ scannerCapacityCount (input M p x) := by
  have inside := saturated_prefix_inside_capacity_count M p x
  unfold remainingCapacityCount at inside
  have positive : 0 < saturatedPrefixEnd M p x := by
    have source_nonneg : 0 ≤ (2 ^ p.eval x.length : Nat) := Nat.zero_le _
    unfold saturatedPrefixEnd
    omega
  unfold scannerSaturatedPrefixEnd
  omega

theorem prefix_end_sixteen_le_side (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    16 * scannerSaturatedPrefixEnd M p x ≤ ConcretePakSide.sideValue (input M p x) :=
  sixteen_physical_prefix_end_le_side M p x

theorem threshold_source_count_gap (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    firstSourceScannerCapacity M p x + (2 ^ p.eval x.length + 1) + 2 ≤
      scannerSaturatedPrefixEnd M p x := by
  unfold firstSourceScannerCapacity scannerSaturatedPrefixEnd saturatedPrefixEnd
  omega

theorem prefix_capacity_minimum (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (enough : firstSourceScannerCapacity M p x ≤ K) :
    minimumSuccessfulWorkCount (input M p x).length ≤ K := by
  have saturated : firstSaturatedCapacity M p x ≤
      K - consumedBeforeFinalBuffer (input M p x).length := by
    unfold firstSourceScannerCapacity at enough
    omega
  have minimum := saturated_prefix_actual_minimum M p x
    (K - consumedBeforeFinalBuffer (input M p x).length) saturated
  unfold firstSourceScannerCapacity at enough
  omega

theorem prefix_capacity_final_saturated (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (enough : firstSourceScannerCapacity M p x ≤ K) :
    firstSaturatedCapacity M p x ≤ actualFinalCapacity (input M p x).length K := by
  unfold firstSourceScannerCapacity at enough
  unfold actualFinalCapacity
  omega

theorem prefix_capacity_physical_slack (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (before : K < scannerSaturatedPrefixEnd M p x) :
    16 * K ≤ ConcretePakSide.sideValue (input M p x) := by
  have bound := prefix_end_sixteen_le_side M p x
  omega

theorem source_count_le_readout_power (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    acceptingCount M x (2 ^ p.eval x.length) ≤ 2 ^ (2 ^ p.eval x.length + 1) :=
  StandardMachineAcceptingCountBound.accepting_count_le_two_pow M x _

def source_scanner_prefix_bounds_spec : Prop :=
  ∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool),
    firstSourceScannerCapacity M p x < scannerSaturatedPrefixEnd M p x ∧
    scannerSaturatedPrefixEnd M p x ≤ scannerCapacityCount (input M p x) ∧
    16 * scannerSaturatedPrefixEnd M p x ≤ ConcretePakSide.sideValue (input M p x) ∧
    firstSourceScannerCapacity M p x + (2 ^ p.eval x.length + 1) + 2 ≤
      scannerSaturatedPrefixEnd M p x ∧
    (∀ K : Nat, firstSourceScannerCapacity M p x ≤ K →
      minimumSuccessfulWorkCount (input M p x).length ≤ K ∧
      firstSaturatedCapacity M p x ≤ actualFinalCapacity (input M p x).length K) ∧
    (∀ K : Nat, K < scannerSaturatedPrefixEnd M p x →
      16 * K ≤ ConcretePakSide.sideValue (input M p x)) ∧
    acceptingCount M x (2 ^ p.eval x.length) ≤ 2 ^ (2 ^ p.eval x.length + 1)

theorem source_scanner_prefix_bounds_spec_holds : source_scanner_prefix_bounds_spec := by
  intro ns nt M p x
  exact ⟨threshold_lt_prefix_end M p x, prefix_end_le_capacity_count M p x,
    prefix_end_sixteen_le_side M p x, threshold_source_count_gap M p x,
    fun K h => ⟨prefix_capacity_minimum M p x K h, prefix_capacity_final_saturated M p x K h⟩,
    prefix_capacity_physical_slack M p x, source_count_le_readout_power M p x⟩

end
end PakFixedPolyomino.PakAllFrameScannerSaturatedPrefixBounds
