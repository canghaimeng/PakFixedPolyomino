import PakFixedPolyomino.PakWeightedCoupledInventory
import PakFixedPolyomino.PakSlotZeroFullFrameStandardBijection
import PakFixedPolyomino.PakSlotOneSideValueReflection

/-! Actual ALL full-frame weights split by their first occupied start slot.
The slot-zero part is an ALL headed-scanner-path weighted sum, including
early terminals. This is a finite census, not a BIT algorithm for its value. -/
namespace PakFixedPolyomino.PakWeightedFullFrameStandardFirstBranch
noncomputable section
open PakMStarCouplingCorrectness PakScannerBaselineAutomaton
open PakCoupledCoefficient PakWeightedCoupledInventory
open PakSlotZeroFullFrameStandardBijection

abbrev SlotOneFullFrame := PakSlotOneFullFrameReflection.SlotOneFullFrame

/-- A clean finite carrier obtained directly from the ALL full-frame subtype. -/
def cleanSlotZeroFintype (n : Nat) : Fintype (SlotZeroFullFrame n) :=
  @Fintype.ofFinite _ (Finite.of_injective Subtype.val Subtype.val_injective)

local instance cleanSlotZeroFrameInstance (n : Nat) : Fintype (SlotZeroFullFrame n) := cleanSlotZeroFintype n

private noncomputable def firstSlot {n : Nat} (F : FullFrame n n) : Fin 2 :=
  ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2

private noncomputable def toFirstBranch {n : Nat} (F : FullFrame n n) :
    Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) := by
  by_cases hzero : firstSlot F = 0
  · exact Sum.inl ⟨F, hzero⟩
  · exact Sum.inr ⟨F, by
      rcases PakFullFrameTableauReadback.FullFrame.firstArrow_slot_zero_or_one F with h | h
      · exact (hzero h).elim
      · exact h⟩

private def fromFirstBranch {n : Nat} :
    Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) → FullFrame n n :=
  Sum.elim Subtype.val Subtype.val

/-- The actual ALL full frames partition by their occupied start slot. -/
def fullFrameEquivFirstBranch (n : Nat) :
    FullFrame n n ≃ Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) where
  toFun := toFirstBranch
  invFun := fromFirstBranch
  left_inv F := by
    classical
    by_cases hzero : firstSlot F = 0
    · simp [toFirstBranch, fromFirstBranch, hzero]
    · simp [toFirstBranch, fromFirstBranch, hzero]
  right_inv s := by
    classical
    rcases s with F | F
    · have hzero : firstSlot F.1 = 0 := F.2
      simp [toFirstBranch, fromFirstBranch, hzero]
    · have hne : firstSlot F.1 ≠ 0 := by
        intro hzero
        have : (0 : Fin 2) = 1 := hzero.symm.trans F.2
        exact Fin.zero_ne_one this
      simp [toFirstBranch, fromFirstBranch, hne]

def frameIdentityWeight {n : Nat} (F : FullFrame n n) : Nat :=
  coupledIdentityWeight F.tiling

def scannerIdentityWeight {n : Nat} (P : ScannerPath n) : Nat :=
  ∏ j : Fin n, PakScannerTailIdentityWeights.tailIdentityCopies (P.column j)

theorem frame_weight_eq_scanner_weight {n : Nat} (F : FullFrame n n) :
    frameIdentityWeight F = scannerIdentityWeight (FullFrame.toScannerPath F) := by
  rw [frameIdentityWeight, identity_weight_right_column F.tiling F.width_pos]
  unfold scannerIdentityWeight
  apply Fintype.prod_congr
  intro j
  have east := (PakScannerBaselineAutomaton.FullFrame.scannerColumnReadback F).east j
  change (F.tiling.val ⟨n - 1, by have := F.width_pos; omega⟩ j).val.2 =
    (FullFrame.toScannerPath F).column j at east
  unfold coupledIdentityCopies
  rw [east]

def weightedFullFrameSum (n : Nat) : Nat :=
  ∑ F : FullFrame n n, frameIdentityWeight F

def weightedBaselineCount (n : Nat) : Nat :=
  ∑ F : SlotZeroFullFrame n, frameIdentityWeight F.val

def weightedSlotOneCount (n : Nat) : Nat :=
  ∑ F : SlotOneFullFrame n, frameIdentityWeight F.val

theorem full_frame_weighted_first_branch (n : Nat) :
    weightedFullFrameSum n = weightedBaselineCount n + weightedSlotOneCount n := by
  let e := fullFrameEquivFirstBranch n
  have transport := e.symm.sum_comp (frameIdentityWeight (n := n))
  unfold weightedFullFrameSum weightedBaselineCount weightedSlotOneCount
  rw [← transport, Fintype.sum_sum_type]
  rfl

theorem weighted_baseline_eq_all_headed_scanner_sum (n : Nat) :
    weightedBaselineCount n =
      ∑ P : HeadedScannerPath n, scannerIdentityWeight P.val := by
  let e := slotZeroFullFrameEquivHeadedScannerPath n
  calc
    weightedBaselineCount n =
        ∑ F : SlotZeroFullFrame n, scannerIdentityWeight (e F).val := by
      unfold weightedBaselineCount
      apply Fintype.sum_congr
      intro F
      exact frame_weight_eq_scanner_weight F.val
    _ = ∑ P : HeadedScannerPath n, scannerIdentityWeight P.val :=
      e.sum_comp (fun P => scannerIdentityWeight P.val)

end
end PakFixedPolyomino.PakWeightedFullFrameStandardFirstBranch
