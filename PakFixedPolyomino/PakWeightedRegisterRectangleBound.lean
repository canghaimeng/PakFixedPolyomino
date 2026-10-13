import PakFixedPolyomino.PakWeightedCoupledInventory

/-! Original weighted Wang perimeter bound before specialization to fixed Q. -/
namespace PakFixedPolyomino.PakWeightedRegisterRectangleBound
noncomputable section
open PakWeightedCoupledInventory
open PakCoupledCoefficient (Machine Coupled CoupledTiling)
def unweightedRectangleBase (Q : Nat) [NeZero Q] : Nat :=
  ConcreteWProd.perimeterBase Machine Q
    (ScanState := ConcretePakScanner.State)

theorem unweighted_rectangle_base_ge_two (Q : Nat) [NeZero Q] : 2 ≤ (unweightedRectangleBase Q) :=
  ConcreteWProd.perimeterBase_ge_two Machine Q

theorem unweighted_rectangle_count_bound (Q : Nat) [NeZero Q] (w h : Nat) (hw : 0 < w) (hh : 0 < h) :
    Fintype.card (CoupledTiling Q w h) ≤
      (unweightedRectangleBase Q) ^ (w + h) := by
  have included : Fintype.card (CoupledTiling Q w h) ≤
      openWangCount (ConcreteWProd.wangTile Machine Q
        (Coupled Q)) w h := by
    change Fintype.card (CoupledTiling Q w h) ≤
      openWangCount (withDummyWangTile (PakCoupledCoefficient.coupledWangTile
        Q)) w h
    unfold openWangCount
    rw [Fintype.card_congr (withDummyOpenEquiv
      (PakCoupledCoefficient.coupledWangTile Q) w h hw hh)]
    simp
  exact included.trans
    ((ConcreteWProd.rectangleBound Machine Q
      (Coupled Q)).bound w h)

def liveRectangleBase (Q : Nat) [NeZero Q] : Nat := 2 * (unweightedRectangleBase Q)

theorem live_rectangle_base_pos (Q : Nat) [NeZero Q] : 0 < (liveRectangleBase Q) := by
  exact Nat.mul_pos (by decide : 0 < 2)
    (lt_of_lt_of_le (by decide : 0 < 2) (unweighted_rectangle_base_ge_two Q))

def liveRectangleBound (Q : Nat) [NeZero Q] : WangRectangleBound (liveRectangleBase Q) (weightedCoupledWangTile Q) where
  bound w h := by
    by_cases hw : 0 < w
    swap
    · have hz : w = 0 := by omega
      subst w
      apply le_trans (b := 1)
      · unfold openWangCount
        rw [Fintype.card_le_one_iff]
        intro f g
        apply Subtype.ext
        funext i
        exact Fin.elim0 i
      · exact Nat.one_le_pow _ _ (live_rectangle_base_pos Q)
    by_cases hh : 0 < h
    swap
    · have hz : h = 0 := by omega
      subst h
      apply le_trans (b := 1)
      · unfold openWangCount
        rw [Fintype.card_le_one_iff]
        intro f g
        apply Subtype.ext
        funext i j
        exact Fin.elim0 j
      · exact Nat.one_le_pow _ _ (live_rectangle_base_pos Q)
    have weighted := weighted_count_le_unrefined Q w h
    have unweighted := unweighted_rectangle_count_bound Q w h hw hh
    have power : 2 ^ h ≤ 2 ^ (w + h) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    calc
      openWangCount (weightedCoupledWangTile Q) w h ≤
          2 ^ h * Fintype.card (CoupledTiling Q w h) := weighted
      _ ≤ 2 ^ h * (unweightedRectangleBase Q) ^ (w + h) :=
        Nat.mul_le_mul_left _ unweighted
      _ ≤ 2 ^ (w + h) * (unweightedRectangleBase Q) ^ (w + h) :=
        Nat.mul_le_mul_right _ power
      _ = (liveRectangleBase Q) ^ (w + h) := by
        unfold liveRectangleBase
        rw [Nat.mul_pow]

def rectangleBase (Q : Nat) [NeZero Q] : Nat := (liveRectangleBase Q) + 1

theorem rectangle_base_ge_two (Q : Nat) [NeZero Q] : 2 ≤ (rectangleBase Q) := by
  exact Nat.succ_le_succ (live_rectangle_base_pos Q)

def rectangleBound (Q : Nat) [NeZero Q] :
    WangRectangleBound (rectangleBase Q) (withDummyWangTile (weightedCoupledWangTile Q)) :=
  (liveRectangleBound Q).withDummy (weightedCoupledWangTile Q)

end
end PakFixedPolyomino.PakWeightedRegisterRectangleBound
