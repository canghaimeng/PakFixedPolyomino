import PakFixedPolyomino.PakFixedShapeFeedbackComponents

/-! The physical flag-strip bound at both feedback positions, supplied from
the original frame and valid placement semantics, for every component run. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackStripBounds
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases PakFixedShapeFeedbackComponents
open PakFixedShapeFlaggedPreparation (state prepare)
open PakFixedShapeFiniteLabelRound (L checkedRound labelAt)
open PakFixedShapeChoiceWords (Done)
open PakFixedShapeFlaggedFrameBounds (frameBound)

theorem flagged_state_length (side : List Bool) (done : Done) :
    (true::state side done).length≤frameBound side.length := by
  rw [List.length_cons,PakFixedShapeFlaggedFrameBounds.state_length]
  have hb := PakFixedShapeFlaggedFrameBounds.square_cells_bound side
  dsimp [frameBound]
  omega

theorem continue_length (raw : List Bool) (h : raw.headD false=true) : raw.length=raw.tail.length+1 := by
  cases raw with
  | nil => simp at h
  | cons b bs => simp

theorem valid_round_length (side : List Bool) (done : Done) (i : Fin L)
    (hp : (prepare (state side done)).headD false=true)
    (hm : (checkedRound (labelAt i) (prepare (state side done)).tail).headD false=true) :
    (checkedRound (labelAt i) (prepare (state side done)).tail).length≤frameBound side.length := by
  obtain ⟨next,he,_⟩ := successful_backedge_state side done i hp hm
  rw [continue_length _ hm,he]
  exact flagged_state_length side next

theorem before_choice_prefix (side : List Bool) (done : Done) :
    RunsAtMost stripMachine (prepare (state side done)) (4*frameBound side.length+4) :=
  strip_prefix_uniform side _ (PakFixedShapeFlaggedFrameBounds.prepared_frame_bound side done)

theorem before_prepare_prefix (side : List Bool) (done : Done) (i : Fin L)
    (hp : (prepare (state side done)).headD false=true)
    (hm : (checkedRound (labelAt i) (prepare (state side done)).tail).headD false=true) :
    RunsAtMost stripMachine (checkedRound (labelAt i) (prepare (state side done)).tail)
      (4*frameBound side.length+4) := strip_prefix_uniform side _ (valid_round_length side done i hp hm)

theorem every_valid_round_strip_prefix (side : List Bool) (done : Done)
    (hp : (prepare (state side done)).headD false=true) (u : List (Fin (L+1)))
    (out : Configuration (StandardBitFiniteChoicePrefix.ns L+PakFixedShapeNondeterministicRound.implementation.states+2)
      (roundAlphabet+extraAlphabet+3))
    (hr : run roundMachine u (initial roundMachine (prepare (state side done)).tail)=some out)
    (ha : out.state=roundMachine.accept) (hflag : out.tape out.head=roundMachine.one) :
    ∀ slots final,run stripMachine slots (restart stripMachine out)=some final →
      slots.length≤4*frameBound side.length+4 := by
  obtain ⟨i,_,hh,ht⟩ := round_accepted_clean _ u out hr ha
  have hflag' := (congrFun ht 0).symm.trans ((congrArg out.tape hh).symm.trans hflag)
  have hm := (clean_head_one_iff roundMachine _).mp hflag'
  obtain ⟨mb,mz,mo,hb,hz,ho⟩ := codes
  have hs := restart_clean stripMachine roundMachine (hb.trans mb.symm) (hz.trans mz.symm) (ho.trans mo.symm) _ out hh ht
  intro slots final hrun
  have hrun' := (congrArg (run stripMachine slots) hs).symm.trans hrun
  exact before_prepare_prefix side done i hp hm slots final hrun'

end
end PakFixedPolyomino.PakFixedShapeFeedbackStripBounds
