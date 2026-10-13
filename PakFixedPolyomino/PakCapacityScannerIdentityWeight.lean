import PakFixedPolyomino.PakScannerTailIdentityWeights
import PakFixedPolyomino.PakSlotOneScannerMultiplicity

/-! The actual capacity-indexed scanner column has the geometric identity
weight used by the source readout. This theorem proves the product for every
physical capacity, including capacities below successful copying. It does
not assert completeness of the ALL full-frame census. -/
namespace PakFixedPolyomino.PakCapacityScannerIdentityWeight
noncomputable section
open PakScannerBaselineAutomaton PakSlotOneScannerMultiplicity
open PakScannerTailIdentityWeights

def pathIdentityWeight {n : Nat} (P : ScannerPath n) : Nat :=
  ∏ j : Fin n, tailIdentityCopies (P.column j)

theorem raw_capacity_path_weight (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    pathIdentityWeight (rawCapacityScannerPath x c) =
      2 ^ (scannerCapacityCount x - c.val - 1) := by
  have product : pathIdentityWeight (rawCapacityScannerPath x c) =
      terminalIdentityWeight (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x) (capacityTerminalIndex x c) := by
    unfold pathIdentityWeight terminalIdentityWeight
    change (∏ j : Fin ((PakSideScanner.sideScannerBits x).length + 2),
        rowIdentityCopies (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x) (capacityTerminalIndex x c) j.val) = _
    exact (Finset.prod_range _).symm
  rw [product, terminal_identity_weight _ _ _ (capacityTerminalIndex_lt x c)]
  congr 1
  unfold scannerCapacityCount capacityTerminalIndex
  omega

theorem path_weight_cast {n m : Nat} (h : n = m) (P : ScannerPath n) :
    pathIdentityWeight (Equiv.cast (congrArg ScannerPath h) P) =
      pathIdentityWeight P := by
  cases h
  rfl

theorem capacity_path_weight (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    pathIdentityWeight (capacityScannerPath x c) =
      2 ^ (scannerCapacityCount x - c.val - 1) := by
  unfold capacityScannerPath
  exact (path_weight_cast (PakSideScanner.sideScannerHeight x)
    (rawCapacityScannerPath x c)).trans (raw_capacity_path_weight x c)

end
end PakFixedPolyomino.PakCapacityScannerIdentityWeight
