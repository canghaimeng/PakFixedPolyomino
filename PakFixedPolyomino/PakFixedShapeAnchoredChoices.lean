import PakFixedPolyomino.TilingAnchoredChoices
import PakFixedPolyomino.PakFixedWeightedShapeFamily

/-! All translation choices for the SAME fixed shape set. These are finite
geometric choices; the standard nondeterministic membership machine is separate. -/
namespace PakFixedPolyomino.PakFixedShapeAnchoredChoices
noncomputable section
open TilingAnchoredChoices PakFixedWeightedShapeFamily
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def candidates (c : Cell) : Finset (Placement Shape) :=
  (Finset.univ : Finset (Anchor shapeSupport)).image (placeAt c)

def choiceCount : Nat := ∑ P : Shape,(shapeSupport P).card

theorem candidates_card (c : Cell) : (candidates c).card = choiceCount := by
  rw [candidates,Finset.card_image_of_injective _ (placeAt_injective shapeSupport c)]
  simp [choiceCount,Anchor,Fintype.card_sigma]

theorem mem_candidates (c : Cell) (p : Placement Shape) :
    p ∈ candidates c ↔ c ∈ Placement.cells shapeSupport p := by
  constructor
  · intro hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact placeAt_contains shapeSupport c a
  · intro hp
    exact Finset.mem_image.mpr ⟨anchorOf shapeSupport c p hp,Finset.mem_univ _,
      placeAt_anchorOf shapeSupport c p hp⟩

theorem tiling_next_unique (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Finset (Placement Shape)) (c : Cell)
    (hc : c ∈ uncovered shapeSupport (square n) done) :
    ∃! p : Placement Shape,p ∈ candidates c ∧ p ∈ T.placements ∧ p ∉ done := by
  obtain ⟨a,ha,_⟩ := uncovered_choice_unique shapeSupport T done c hc
  refine ⟨placeAt c a,⟨(mem_candidates c _).mpr (placeAt_contains shapeSupport c a),ha⟩,?_⟩
  intro p hp
  exact T.cover_unique hp.2.1 ha.1 ((mem_candidates c p).mp hp.1)
    (placeAt_contains shapeSupport c a)

theorem next_uncovered_decreases (n : Nat) (done : Finset (Placement Shape))
    (c : Cell) (hc : c ∈ uncovered shapeSupport (square n) done)
    (p : Placement Shape) (hp : p ∈ candidates c) :
    (uncovered shapeSupport (square n) (insert p done)).card <
      (uncovered shapeSupport (square n) done).card := by
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact uncovered_strictly_decreases shapeSupport c hc a

theorem uncovered_card_bound (n : Nat) (done : Finset (Placement Shape)) :
    (uncovered shapeSupport (square n) done).card ≤ n^2 := by
  rw [← card_square]
  exact Finset.card_le_card Finset.sdiff_subset

theorem fixed_shape_anchored_choice_spec :
    (∀ c,(candidates c).card = choiceCount) ∧
    (∀ c p,p ∈ candidates c ↔ c ∈ Placement.cells shapeSupport p) ∧
    (∀ n (T : Tiling shapeSupport (square n)) done c,
      c ∈ uncovered shapeSupport (square n) done →
      ∃! p : Placement Shape,p ∈ candidates c ∧ p ∈ T.placements ∧ p ∉ done) ∧
    (∀ n done c,c ∈ uncovered shapeSupport (square n) done → ∀ p,p ∈ candidates c →
      (uncovered shapeSupport (square n) (insert p done)).card <
        (uncovered shapeSupport (square n) done).card) ∧
    (∀ n done,(uncovered shapeSupport (square n) done).card ≤ n^2) :=
  ⟨candidates_card,mem_candidates,tiling_next_unique,next_uncovered_decreases,uncovered_card_bound⟩

end
end PakFixedPolyomino.PakFixedShapeAnchoredChoices
