import PakFixedPolyomino.PakAllFrameCapacityWeightedPartition
import PakFixedPolyomino.PakWeightedCoefficientFrameTransport

/-! ONE fixed weighted Wang inventory: full-coefficient extraction at every
encoded square equals the ALL slot-zero baseline plus EVERY actual capacity
fibre, with its physical geometric weight. Source-count identification,
connected polyomino geometry and BIT complexity remain separate. -/
namespace PakFixedPolyomino.PakFixedCoefficientAllCapacityFrameCensus
noncomputable section
open PakWeightedCoupledInventory PakWeightedCoupledCoefficient
open PakWeightedCoefficientFrameTransport PakWeightedFullFrameStandardFirstBranch
open PakAllFrameCapacityWeightedPartition PakSlotOneScannerMultiplicity

theorem encoded_square_all_capacity_census (x : ConcretePakSide.Word) :
    openWangCount (weightedCoupledWangTile weightedExtractionQ)
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) /
      weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) =
      weightedBaselineCount (ConcretePakSide.sideValue x) +
        ∑ c : ScannerCapacity x,
          2 ^ (scannerCapacityCount x - c.val - 1) * capacityFibreCount x c := by
  rw [weightedSquare_div_fullPower_eq_actualWeightedFullFrameSum
    (PakSideScanner.sideValue_ge_five x)]
  change weightedFullFrameSum (ConcretePakSide.sideValue x) = _
  rw [full_frame_weighted_first_branch, all_slot_one_weighted_capacity_partition]

end
end PakFixedPolyomino.PakFixedCoefficientAllCapacityFrameCensus
