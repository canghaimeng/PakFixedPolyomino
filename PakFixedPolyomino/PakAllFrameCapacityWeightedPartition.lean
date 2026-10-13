import PakFixedPolyomino.PakSlotOneFrameCapacityReadbackStandard

/-! Partition EVERY original slot-one frame by its internally extracted
physical capacity. Fibre counts are actual cardinalities, not a chosen image
or supplied counting certificate. Their source-count identification remains
a separate obligation. -/
namespace PakFixedPolyomino.PakAllFrameCapacityWeightedPartition
noncomputable section
open PakSlotOneFrameCapacityReadbackStandard PakSlotOneScannerMultiplicity
open PakWeightedFullFrameStandardFirstBranch

abbrev Frames (x : ConcretePakSide.Word) :=
  PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x)

def frameCapacity (x : ConcretePakSide.Word) (F : Frames x) : ScannerCapacity x :=
  Classical.choose (every_frame_has_capacity x F)

theorem frame_capacity_spec (x : ConcretePakSide.Word) (F : Frames x) :
    PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1 =
      capacityScannerPath x (frameCapacity x F) :=
  Classical.choose_spec (every_frame_has_capacity x F)

def CapacityFibre (x : ConcretePakSide.Word) (c : ScannerCapacity x) :=
  {F : Frames x // frameCapacity x F = c}

instance capacityFibreFintype (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    Fintype (CapacityFibre x c) :=
  @Fintype.ofFinite _ (Finite.of_injective
    (fun F : CapacityFibre x c => F.1) Subtype.val_injective)

def allFrameEquivCapacityFibres (x : ConcretePakSide.Word) :
    Frames x ≃ Σ c : ScannerCapacity x, CapacityFibre x c where
  toFun F := ⟨frameCapacity x F, ⟨F, rfl⟩⟩
  invFun s := s.2.1
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨c, F, hc⟩
    cases hc
    rfl

def capacityFibreCount (x : ConcretePakSide.Word) (c : ScannerCapacity x) : Nat :=
  Nat.card (CapacityFibre x c)

theorem capacity_fibre_weight (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    frameIdentityWeight F.1.1 = 2 ^ (scannerCapacityCount x - c.val - 1) := by
  apply entire_capacity_fibre_weight x c F.1
  simpa only [F.2] using frame_capacity_spec x F.1

theorem all_slot_one_weighted_capacity_partition (x : ConcretePakSide.Word) :
    weightedSlotOneCount (ConcretePakSide.sideValue x) =
      ∑ c : ScannerCapacity x,
        2 ^ (scannerCapacityCount x - c.val - 1) * capacityFibreCount x c := by
  let e := allFrameEquivCapacityFibres x
  have transport := e.symm.sum_comp (fun F : Frames x => frameIdentityWeight F.1)
  unfold weightedSlotOneCount
  rw [← transport, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ F : CapacityFibre x c, frameIdentityWeight F.1.1) =
        ∑ _F : CapacityFibre x c, 2 ^ (scannerCapacityCount x - c.val - 1) := by
      apply Finset.sum_congr rfl
      intro F _
      exact capacity_fibre_weight x c F
    _ = 2 ^ (scannerCapacityCount x - c.val - 1) * capacityFibreCount x c := by
      simp [capacityFibreCount, Nat.card_eq_fintype_card, Nat.mul_comm]

end
end PakFixedPolyomino.PakAllFrameCapacityWeightedPartition
