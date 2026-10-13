import PakFixedPolyomino.PakAllFrameCapacityWeightedPartition
import PakFixedPolyomino.PakWeightedCapacityCeilingReadout

/-! The actual ALLcapacity frame census in the natural-number coordinates
used by the finite geometric ceiling. Counts outside the original finite
scanner capacity type are exactly zero; no frame or capacity is omitted. -/
namespace PakFixedPolyomino.PakAllCapacityFrameNatWeightedCensus
noncomputable section
open PakSlotOneScannerMultiplicity PakAllFrameCapacityWeightedPartition
open PakWeightedFullFrameStandardFirstBranch PakWeightedCapacityCeilingReadout

def capacityNatCount (x : ConcretePakSide.Word) (K : Nat) : Nat :=
  if h : K < scannerCapacityCount x then capacityFibreCount x ⟨K, h⟩ else 0

theorem capacity_nat_count_inside (x : ConcretePakSide.Word) (K : Nat)
    (h : K < scannerCapacityCount x) :
    capacityNatCount x K = capacityFibreCount x ⟨K, h⟩ := by
  simp only [capacityNatCount, dif_pos h]

theorem capacity_nat_count_outside (x : ConcretePakSide.Word) (K : Nat)
    (h : scannerCapacityCount x ≤ K) : capacityNatCount x K = 0 := by
  simp only [capacityNatCount, dif_neg (Nat.not_lt_of_ge h)]

theorem weighted_slot_one_nat_census (x : ConcretePakSide.Word) :
    weightedSlotOneCount (ConcretePakSide.sideValue x) =
      weightedCapacitySum (scannerCapacityCount x) (capacityNatCount x) := by
  rw [all_slot_one_weighted_capacity_partition]
  unfold weightedCapacitySum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro K hK
  have hi := Finset.mem_range.mp hK
  simp only [capacityNatCount, dif_pos hi]
  congr 2
  omega

theorem shifted_capacity_weight (S D L : Nat) :
    fullCapacityWeight S (D + L) = fullCapacityWeight (S - D) L := by
  unfold fullCapacityWeight
  rw [Nat.sub_add_eq]

def all_capacity_nat_census_spec : Prop :=
  (∀ (x : ConcretePakSide.Word) (K : Nat) (h : K < scannerCapacityCount x),
    capacityNatCount x K = capacityFibreCount x ⟨K, h⟩) ∧
  (∀ (x : ConcretePakSide.Word) (K : Nat),
    scannerCapacityCount x ≤ K → capacityNatCount x K = 0) ∧
  (∀ x : ConcretePakSide.Word,
    weightedSlotOneCount (ConcretePakSide.sideValue x) =
      weightedCapacitySum (scannerCapacityCount x) (capacityNatCount x)) ∧
  (∀ S D L : Nat,
    fullCapacityWeight S (D + L) = fullCapacityWeight (S - D) L)

theorem all_capacity_nat_census_spec_holds : all_capacity_nat_census_spec :=
  ⟨capacity_nat_count_inside, capacity_nat_count_outside,
    weighted_slot_one_nat_census, shifted_capacity_weight⟩

end
end PakFixedPolyomino.PakAllCapacityFrameNatWeightedCensus
