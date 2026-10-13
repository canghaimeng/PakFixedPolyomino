import PakFixedPolyomino.Wang

/-! Distinct finite Wang identities with identical colours. Projection is
an exact equivalence with the original tiling plus an independent finite
identity choice at every cell. Counts concern all open tilings. -/
namespace PakFixedPolyomino.WangIdentityRefinement
noncomputable section

abbrev RefinedIndex (W : Type*) (copies : W → Nat) := Σ a : W, Fin (copies a)

def refinedTile {W H V : Type*} (tile : W → WangTile H V) (copies : W → Nat) :
    RefinedIndex W copies → WangTile H V := fun a => tile a.1

abbrev IdentityChoices {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (copies : W → Nat) (w h : Nat)
    (F : OpenWangTiling tile w h) :=
  (i : Fin w) → (j : Fin h) → Fin (copies (F.1 i j))

def openRefinementEquiv {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (copies : W → Nat) (w h : Nat) :
    OpenWangTiling (refinedTile tile copies) w h ≃
      Σ F : OpenWangTiling tile w h, IdentityChoices tile copies w h F where
  toFun R :=
    ⟨⟨fun i j => (R.1 i j).1, R.2⟩, fun i j => (R.1 i j).2⟩
  invFun P :=
    ⟨fun i j => ⟨P.1.1 i j, P.2 i j⟩, P.1.2⟩
  left_inv R := by
    apply Subtype.ext
    funext i j
    rfl
  right_inv P := by
    cases P
    rfl

theorem identity_choices_card {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (copies : W → Nat) (w h : Nat)
    (F : OpenWangTiling tile w h) :
    Fintype.card (IdentityChoices tile copies w h F) =
      ∏ i : Fin w, ∏ j : Fin h, copies (F.1 i j) := by
  simp only [IdentityChoices, Fintype.card_pi, Fintype.card_fin]

theorem open_count_refined_eq_sum {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (copies : W → Nat) (w h : Nat) :
    openWangCount (refinedTile tile copies) w h =
      ∑ F : OpenWangTiling tile w h, ∏ i : Fin w, ∏ j : Fin h, copies (F.1 i j) := by
  unfold openWangCount
  rw [Fintype.card_congr (openRefinementEquiv tile copies w h), Fintype.card_sigma]
  simp only [identity_choices_card]

end
end PakFixedPolyomino.WangIdentityRefinement
