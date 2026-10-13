import Mathlib

namespace PakFixedPolyomino

noncomputable section

/-- A Wang tile with horizontal and vertical colour types. -/
structure WangTile (Horizontal Vertical : Type*) where
  west : Horizontal
  east : Horizontal
  south : Vertical
  north : Vertical
  deriving DecidableEq

/-- Open-boundary Wang tilings of a finite rectangle. -/
def OpenWangTiling {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (w h : ℕ) :=
  { f : Fin w → Fin h → W //
      (∀ (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w),
        (tile (f i j)).east = (tile (f ⟨i.1 + 1, hi⟩ j)).west) ∧
      (∀ (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h),
        (tile (f i j)).north = (tile (f i ⟨j.1 + 1, hj⟩)).south) }

instance {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (w h : ℕ) :
    Fintype (OpenWangTiling tile w h) := by
  classical
  letI : Fintype (Fin w → Fin h → W) := inferInstance
  letI : Finite (Fin w → Fin h → W) := Fintype.finite this
  unfold OpenWangTiling
  exact Fintype.ofFinite _

def openWangCount {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (w h : ℕ) : ℕ :=
  Fintype.card (OpenWangTiling tile w h)

/-- Square open counts are exactly the rectangular count on equal arguments. -/
theorem square_open_count_eq_rect {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V) (n : ℕ) :
    openWangCount tile n n = openWangCount tile n n := rfl

/-- A `1 × 1` open rectangle has no matching constraints. -/
theorem openWangCount_one_one {W H V : Type*} [Fintype W]
    [DecidableEq W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) : openWangCount tile 1 1 = Fintype.card W := by
  let encode : OpenWangTiling tile 1 1 → W := fun f => f.1 ⟨0, by decide⟩ ⟨0, by decide⟩
  let decode : W → OpenWangTiling tile 1 1 := fun u =>
    ⟨fun _ _ => u, by
      constructor
      · intro i _ hi; omega
      · intro _ j hj; omega⟩
  have hleft : Function.LeftInverse decode encode := by
    intro f
    apply Subtype.ext
    funext i j
    have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by omega)
    have hj : j = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by omega)
    subst i; subst j
    rfl
  have hright : Function.RightInverse decode encode := by intro u; rfl
  exact Fintype.card_congr (Equiv.mk encode decode hleft hright)

end
end PakFixedPolyomino
