import PakFixedPolyomino.PakAllCapacityFrameNatWeightedCensus
import PakFixedPolyomino.PakFixedCoefficientAllCapacityFrameCensus

/-! ONE original fixed weighted Wang inventory, with ALL original frame
counts in the exact natural-capacity coordinates of the geometric readout. -/
namespace PakFixedPolyomino.PakFixedCoefficientAllCapacityNatCensus
open PakWeightedCoupledInventory PakWeightedCoupledCoefficient
open PakWeightedFullFrameStandardFirstBranch
open PakSlotOneScannerMultiplicity PakWeightedCapacityCeilingReadout
open PakAllCapacityFrameNatWeightedCensus

theorem encoded_square_all_capacity_nat_census (x : ConcretePakSide.Word) :
    openWangCount (weightedCoupledWangTile weightedExtractionQ)
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) /
      weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) =
      weightedBaselineCount (ConcretePakSide.sideValue x) +
        weightedCapacitySum (scannerCapacityCount x) (capacityNatCount x) := by
  rw [← weighted_slot_one_nat_census]
  have counted := PakFixedCoefficientAllCapacityFrameCensus.encoded_square_all_capacity_census x
  rw [← PakAllFrameCapacityWeightedPartition.all_slot_one_weighted_capacity_partition] at counted
  exact counted

def fixed_capacity_nat_census_spec : Prop :=
  ∀ x : ConcretePakSide.Word,
    openWangCount (weightedCoupledWangTile weightedExtractionQ)
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) /
      weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) =
      weightedBaselineCount (ConcretePakSide.sideValue x) +
        weightedCapacitySum (scannerCapacityCount x) (capacityNatCount x)

theorem fixed_capacity_nat_census_spec_holds : fixed_capacity_nat_census_spec :=
  encoded_square_all_capacity_nat_census

end PakFixedPolyomino.PakFixedCoefficientAllCapacityNatCensus
