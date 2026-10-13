import PakFixedPolyomino.PakCoupledCoefficient
import PakFixedPolyomino.PakScannerTailIdentityWeights

/-! Fixed local tail-mode-hash identity refinement of the actual MStar
coupled Wang inventory. Combinatorial only: not BIT-time. -/

namespace PakFixedPolyomino.PakWeightedCoupledInventory

open PakCoupledCoefficient (CoupledTrack CoupledTiling Coupled Machine
  coefficientPerimeterBase amplifierProjection Coupled)
open PakScannerTailIdentityWeights WangIdentityRefinement
open PakScannerTerminal
open Finset

noncomputable section

def coupledIdentityCopies (Q : ℕ) [NeZero Q] (u : CoupledTrack Q) : ℕ :=
  tailIdentityCopies u.val.2

abbrev WeightedCoupledTrack (Q : ℕ) [NeZero Q] :=
  RefinedIndex (CoupledTrack Q) (coupledIdentityCopies Q)

def weightedCoupledWangTile (Q : ℕ) [NeZero Q] :=
  refinedTile (PakCoupledCoefficient.coupledWangTile Q) (coupledIdentityCopies Q)

abbrev WeightedCoupledTiling (Q : ℕ) [NeZero Q] (w h : ℕ) :=
  OpenWangTiling (weightedCoupledWangTile Q) w h

def coupledIdentityWeight {Q w h : ℕ} [NeZero Q]
    (F : CoupledTiling Q w h) : ℕ :=
  ∏ i : Fin w, ∏ j : Fin h, coupledIdentityCopies Q (F.val i j)

lemma copies_bounds (Q : ℕ) [NeZero Q] (u : CoupledTrack Q) :
    1 ≤ coupledIdentityCopies Q u ∧ coupledIdentityCopies Q u ≤ 2 := by
  dsimp [coupledIdentityCopies, tailIdentityCopies]
  cases u.val.2 with
  | none => constructor <;> decide
  | some st =>
    rcases st with ⟨s, t⟩
    by_cases hmode : s.mode = .tail ∧ s.centre = .hash <;> simp [hmode]

lemma refined_colours (Q : ℕ) [NeZero Q] (u : WeightedCoupledTrack Q) :
    weightedCoupledWangTile Q u =
      PakCoupledCoefficient.coupledWangTile Q u.1 :=
  rfl

def weighted_open_equiv (Q w h : ℕ) [NeZero Q] :
    WeightedCoupledTiling Q w h ≃
      Σ F : CoupledTiling Q w h,
        (i : Fin w) → (j : Fin h) → Fin (coupledIdentityCopies Q (F.val i j)) :=
  openRefinementEquiv (PakCoupledCoefficient.coupledWangTile Q)
    (coupledIdentityCopies Q) w h

theorem weighted_count_eq_sum (Q w h : ℕ) [NeZero Q] :
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ F : CoupledTiling Q w h, coupledIdentityWeight F :=
  open_count_refined_eq_sum (PakCoupledCoefficient.coupledWangTile Q)
    (coupledIdentityCopies Q) w h

lemma interior_identity_one {Q w h : ℕ} [NeZero Q]
    (F : CoupledTiling Q w h) (i : Fin w) (j : Fin h)
    (hi : i.val + 1 ≠ w) :
    coupledIdentityCopies Q (F.val i j) = 1 := by
  have hcell :
      PakCouplingGenerated.amp Machine Q (F.val i j).val =
        (amplifierProjection F).val i j :=
    rfl
  have hne :
      (PakCouplingGenerated.amp Machine Q (F.val i j).val).val.eastActive =
        false := by
    rw [hcell]
    cases he : ((amplifierProjection F).val i j).val.eastActive
    · rfl
    · have := PakAmpCoefficient.eastActive_forces_right_boundary
        (amplifierProjection F) i j he
      exact (hi this).elim
  have hC : Coupled Q (F.val i j).val := (F.val i j).property
  have hidle : (F.val i j).val.2 = none :=
    PakCouplingGenerated.coupled_nonEast_idle
      MStarULogAssembly.boundaryData Machine Q hC hne
  unfold coupledIdentityCopies tailIdentityCopies
  rw [hidle]

lemma identity_weight_right_column {Q w h : ℕ} [NeZero Q]
    (F : CoupledTiling Q w h) (hw : 0 < w) :
    coupledIdentityWeight F =
      ∏ j : Fin h,
        coupledIdentityCopies Q (F.val ⟨w - 1, by omega⟩ j) := by
  unfold coupledIdentityWeight
  let iLast : Fin w := ⟨w - 1, by omega⟩
  apply Fintype.prod_eq_single iLast
  intro i hi
  have hne : i.val + 1 ≠ w := by
    intro h
    apply hi
    apply Fin.ext
    have : i.val = w - 1 := by omega
    simpa [iLast] using this
  refine prod_eq_one ?_
  intro j _
  exact interior_identity_one F i j hne

lemma identity_weight_empty_width {Q h : ℕ} [NeZero Q]
    (F : CoupledTiling Q 0 h) :
    coupledIdentityWeight F = 1 := by
  unfold coupledIdentityWeight
  exact Fintype.prod_empty _

theorem identity_weight_le_pow {Q w h : ℕ} [NeZero Q]
    (F : CoupledTiling Q w h) :
    coupledIdentityWeight F ≤ 2 ^ h := by
  by_cases hw : 0 < w
  · rw [identity_weight_right_column F hw]
    have hpt : ∀ j : Fin h, coupledIdentityCopies Q
        (F.val ⟨w - 1, by omega⟩ j) ≤ 2 :=
      fun j => (copies_bounds Q _).2
    have hprod :
        (∏ j : Fin h, coupledIdentityCopies Q
            (F.val ⟨w - 1, by omega⟩ j)) ≤
          ∏ _j : Fin h, 2 :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hpt j)
    have hconst : (∏ _j : Fin h, (2 : ℕ)) = 2 ^ h := by
      simp [prod_const, Fintype.card_fin]
    exact hprod.trans (le_of_eq hconst)
  · have : w = 0 := by omega
    subst this
    simpa [identity_weight_empty_width F] using Nat.one_le_two_pow (n := h)

theorem weighted_count_le_unrefined (Q w h : ℕ) [NeZero Q] :
    openWangCount (weightedCoupledWangTile Q) w h ≤
      2 ^ h * Fintype.card (CoupledTiling Q w h) := by
  rw [weighted_count_eq_sum, Nat.mul_comm]
  have hle :
      ∑ F : CoupledTiling Q w h, coupledIdentityWeight F ≤
        ∑ _F : CoupledTiling Q w h, 2 ^ h :=
    sum_le_sum fun F _ => identity_weight_le_pow F
  simpa [sum_const, card_univ, nsmul_eq_mul] using hle

lemma unrefined_card_le_perimeter {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    Fintype.card (CoupledTiling 1 w h) ≤
      coefficientPerimeterBase ^ (w + h) := by
  have hequiv := Fintype.card_congr
    (withDummyOpenEquiv (PakCoupledCoefficient.coupledWangTile 1) w h hw hh)
  have hcomp : Fintype.card (CoupledTiling 1 w h) ≤
      Fintype.card
        (OpenWangTiling (withDummyWangTile
          (PakCoupledCoefficient.coupledWangTile 1)) w h) := by
    rw [hequiv]
    simp
  have hbound :=
    (ConcreteWProd.rectangleBound Machine 1 (Coupled 1)).bound w h
  unfold openWangCount at hbound
  change Fintype.card
      (OpenWangTiling (withDummyWangTile
        (PakCoupledCoefficient.coupledWangTile 1)) w h) ≤
        coefficientPerimeterBase ^ (w + h) at hbound
  exact hcomp.trans hbound

theorem weighted_count_le_q1_perimeter {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    openWangCount (weightedCoupledWangTile 1) w h ≤
      2 ^ h * coefficientPerimeterBase ^ (w + h) :=
  (weighted_count_le_unrefined 1 w h).trans
    (Nat.mul_le_mul_left _ (unrefined_card_le_perimeter hw hh))

theorem weighted_count_le_revised_base {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    openWangCount (weightedCoupledWangTile 1) w h ≤
      (2 * coefficientPerimeterBase) ^ (w + h) := by
  have hmain := weighted_count_le_q1_perimeter hw hh
  have hpow : 2 ^ h ≤ 2 ^ (w + h) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left h w)
  have hmul :
      2 ^ h * coefficientPerimeterBase ^ (w + h) ≤
        2 ^ (w + h) * coefficientPerimeterBase ^ (w + h) :=
    Nat.mul_le_mul_right _ hpow
  have hre : 2 ^ (w + h) * coefficientPerimeterBase ^ (w + h) =
      (2 * coefficientPerimeterBase) ^ (w + h) := by
    rw [Nat.mul_pow]
  exact hmain.trans (hmul.trans (le_of_eq hre))

theorem terminal_column_weight {Q w : ℕ} [NeZero Q]
    (bits : List Bool) (positive : 0 < bits.length) (terminal : ℕ)
    (bound : terminal < bits.length) (hw : 0 < w)
    (F : CoupledTiling Q w (bits.length + 2))
    (hcol : ∀ j : Fin (bits.length + 2),
      (F.val ⟨w - 1, by omega⟩ j).val.2 =
        some (terminalScannerState bits positive terminal j.val,
          terminalScannerState bits positive terminal (j.val + 1))) :
    coupledIdentityWeight F = 2 ^ (bits.length - terminal - 1) := by
  rw [identity_weight_right_column F hw]
  have hrow :
      ∀ j : Fin (bits.length + 2),
        coupledIdentityCopies Q (F.val ⟨w - 1, by omega⟩ j) =
          rowIdentityCopies bits positive terminal j.val := by
    intro j
    unfold coupledIdentityCopies rowIdentityCopies
    rw [hcol j]
  simp_rw [hrow]
  have hrange :
      (∏ j : Fin (bits.length + 2),
          rowIdentityCopies bits positive terminal j.val) =
        ∏ row ∈ range (bits.length + 2),
          rowIdentityCopies bits positive terminal row :=
    (prod_range (rowIdentityCopies bits positive terminal)).symm
  rw [hrange]
  exact terminal_identity_weight bits positive terminal bound

/-- Joint: exact weighted count, uniform `2^h` bound, Q=1 perimeter. -/
def weighted_coupled_inventory_spec : Prop :=
  (∀ Q w h : ℕ, [NeZero Q] →
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ F : CoupledTiling Q w h, coupledIdentityWeight F) ∧
  (∀ Q w h : ℕ, [NeZero Q] → ∀ F : CoupledTiling Q w h,
    coupledIdentityWeight F ≤ 2 ^ h) ∧
  (∀ Q w h : ℕ, [NeZero Q] →
    openWangCount (weightedCoupledWangTile Q) w h ≤
      2 ^ h * Fintype.card (CoupledTiling Q w h)) ∧
  (∀ w h : ℕ, 0 < w → 0 < h →
    openWangCount (weightedCoupledWangTile 1) w h ≤
      2 ^ h * coefficientPerimeterBase ^ (w + h)) ∧
  (∀ w h : ℕ, 0 < w → 0 < h →
    openWangCount (weightedCoupledWangTile 1) w h ≤
      (2 * coefficientPerimeterBase) ^ (w + h))

theorem weighted_coupled_inventory_spec_holds :
    weighted_coupled_inventory_spec :=
  ⟨weighted_count_eq_sum, fun _ _ _ => identity_weight_le_pow,
    weighted_count_le_unrefined, fun _ _ => weighted_count_le_q1_perimeter,
    fun _ _ => weighted_count_le_revised_base⟩

end
end PakFixedPolyomino.PakWeightedCoupledInventory
