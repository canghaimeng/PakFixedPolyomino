import PakFixedPolyomino.PakFixedShapeFlaggedFrameBounds

/-! Every successful reference prefix recovers an original placement set.
This supplies its exact next state and frame bounds internally. The physical
ND raw-run decomposition remains a separate compiler obligation. -/
namespace PakFixedPolyomino.PakFixedShapeFlaggedReachability
noncomputable section
open PakFixedShapeChoiceWords (Done)
open PakFixedShapeFiniteLabelRound (L labelAt)
open PakFixedShapeFlaggedPreparation (state prepare)
open PakFixedWeightedStandardBinaryCount (value)

theorem original_output (side : List Bool) (done : Done) (is : List (Fin L))
    (out : List Bool) (h : PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out) :
    ∃ next : Done, PakFixedShapeChoiceWords.run (value side) (is.map labelAt) done=some next ∧
      out=state side next := by
  rw [PakFixedShapeFlaggedChoiceWords.run_original] at h
  cases hr : PakFixedShapeChoiceWords.run (value side) (is.map labelAt) done with
  | none => simp [hr] at h
  | some next =>
    refine ⟨next,rfl,?_⟩
    exact (Option.some.inj (by simpa only [hr,Option.map_some] using h)).symm

theorem reachable_bounds (side : List Bool) (done : Done) (is : List (Fin L))
    (out : List Bool) (h : PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out) :
    out.length≤PakFixedShapeFlaggedFrameBounds.frameBound side.length ∧
    (prepare out).length≤PakFixedShapeFlaggedFrameBounds.frameBound side.length ∧
    is.length≤(value side)^2 := by
  obtain ⟨next,_,he⟩ := original_output side done is out h
  refine ⟨he ▸ PakFixedShapeFlaggedFrameBounds.state_frame_bound side next,
    he ▸ PakFixedShapeFlaggedFrameBounds.prepared_frame_bound side next,
    PakFixedShapeFlaggedChoiceWords.successful_prefix_length_le side done is out h⟩

theorem exhausted_iff_original (side : List Bool) (done : Done) (is : List (Fin L))
    (out : List Bool) (h : PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out) :
    (prepare out).headD false=false ↔
      (PakFixedShapeChoiceWords.run (value side) (is.map labelAt) done).map
        (PakFixedShapeFirstUncovered.firstUncovered (value side))=some none := by
  obtain ⟨next,hr,he⟩ := original_output side done is out h
  rw [he,hr,Option.map_some,Option.some.injEq]
  exact PakFixedShapeFlaggedPreparation.stops_iff side next

end
end PakFixedPolyomino.PakFixedShapeFlaggedReachability
