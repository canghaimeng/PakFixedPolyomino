import PakFixedPolyomino.PakAllFrameOrdinarySourceCounts
import PakFixedPolyomino.PakAllFrameScannerSaturatedPrefixBounds
import PakFixedPolyomino.PakFixedCoefficientAllCapacityNatCensus

/-! The original ALLframe geometric readout equals the original ordinary
accepting-path count. All capacity/time/spatial and word-inverse witnesses
are supplied internally. The only source premise is genuine RunsAtMost;
this arithmetic identity supplies no polynomial bit-time certificate. -/
namespace PakFixedPolyomino.PakAllFrameWeightedOrdinarySourceReadout
noncomputable section
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
open ULogTernaryGeneratedMarginScanner (input)
open PakAllFrameOrdinarySourceCapacityNecessary (firstSourceScannerCapacity)
open PakAllFrameOrdinarySourceCounts PakAllFrameScannerSaturatedPrefixBounds
open PakAllCapacityFrameNatWeightedCensus PakSlotOneScannerMultiplicity
open PakWeightedCapacityCeilingReadout PakWeightedFullFrameStandardFirstBranch
open PakWeightedCoupledInventory PakWeightedCoupledCoefficient
variable {ns nt : Nat}

def sourceReadoutWeight (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  fullCapacityWeight (scannerCapacityCount (input M p x)) (firstSourceScannerCapacity M p x)

theorem source_readout_weight_pos (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : 0 < sourceReadoutWeight M p x :=
  fullCapacityWeight_pos (threshold_lt_prefix_end M p x) (prefix_end_le_capacity_count M p x)

theorem nat_capacity_source_upper (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K : Nat) :
    capacityNatCount (input M p x) K ≤ acceptingCount M x (2 ^ p.eval x.length) := by
  by_cases inside : K < scannerCapacityCount (input M p x)
  · rw [capacity_nat_count_inside _ _ inside]
    exact fibre_count_le_accepting M p x ht ⟨K, inside⟩
  · rw [capacity_nat_count_outside _ _ (Nat.le_of_not_gt inside)]
    exact Nat.zero_le _

theorem nat_capacity_source_shortage (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (K : Nat) (shortage : K < firstSourceScannerCapacity M p x) :
    capacityNatCount (input M p x) K = 0 := by
  by_cases inside : K < scannerCapacityCount (input M p x)
  · rw [capacity_nat_count_inside _ _ inside]
    exact scanner_source_shortage_zero M p x ht ⟨K, inside⟩ shortage
  · exact capacity_nat_count_outside _ _ (Nat.le_of_not_gt inside)

theorem nat_capacity_source_saturated (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (K : Nat) (enough : firstSourceScannerCapacity M p x ≤ K)
    (before : K < scannerSaturatedPrefixEnd M p x) :
    capacityNatCount (input M p x) K = acceptingCount M x (2 ^ p.eval x.length) := by
  have inside : K < scannerCapacityCount (input M p x) :=
    before.trans_le (prefix_end_le_capacity_count M p x)
  rw [capacity_nat_count_inside _ _ inside]
  rw [low_capacity_fibre_exact M p x ht ⟨K, inside⟩
    (prefix_capacity_minimum M p x K enough) (prefix_capacity_physical_slack M p x K before)]
  rw [if_pos (prefix_capacity_final_saturated M p x K enough)]

theorem all_frame_weighted_source_readout (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    (weightedSlotOneCount (ConcretePakSide.sideValue (input M p x)) +
        sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x =
      acceptingCount M x (2 ^ p.eval x.length) := by
  rw [weighted_slot_one_nat_census]
  apply weighted_capacity_ceiling_readout
    (scannerCapacityCount (input M p x)) (firstSourceScannerCapacity M p x)
    (scannerSaturatedPrefixEnd M p x) (2 ^ p.eval x.length + 1)
    (acceptingCount M x (2 ^ p.eval x.length)) (capacityNatCount (input M p x))
  · exact threshold_lt_prefix_end M p x
  · exact prefix_end_le_capacity_count M p x
  · exact threshold_source_count_gap M p x
  · exact source_count_le_readout_power M p x
  · intro K _inside
    exact nat_capacity_source_upper M p x ht K
  · exact nat_capacity_source_shortage M p x ht
  · exact nat_capacity_source_saturated M p x ht

theorem fixed_wang_all_frame_source_readout (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    (openWangCount (weightedCoupledWangTile weightedExtractionQ)
          (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) /
        weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
          (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) -
      weightedBaselineCount (ConcretePakSide.sideValue (input M p x)) +
        sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x =
      acceptingCount M x (2 ^ p.eval x.length) := by
  rw [PakFixedCoefficientAllCapacityNatCensus.encoded_square_all_capacity_nat_census,
    Nat.add_sub_cancel_left, ← weighted_slot_one_nat_census]
  exact all_frame_weighted_source_readout M p x ht

def all_frame_weighted_source_readout_spec : Prop :=
  ∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool),
    0 < sourceReadoutWeight M p x ∧
    (RunsAtMost M x (2 ^ p.eval x.length) →
      (weightedSlotOneCount (ConcretePakSide.sideValue (input M p x)) +
        sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x =
          acceptingCount M x (2 ^ p.eval x.length) ∧
      (openWangCount (weightedCoupledWangTile weightedExtractionQ)
          (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) /
        weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
          (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) -
        weightedBaselineCount (ConcretePakSide.sideValue (input M p x)) +
          sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x =
        acceptingCount M x (2 ^ p.eval x.length))

theorem all_frame_weighted_source_readout_spec_holds : all_frame_weighted_source_readout_spec :=
  fun _ _ M p x => ⟨source_readout_weight_pos M p x, fun ht =>
    ⟨all_frame_weighted_source_readout M p x ht, fixed_wang_all_frame_source_readout M p x ht⟩⟩

end
end PakFixedPolyomino.PakAllFrameWeightedOrdinarySourceReadout
