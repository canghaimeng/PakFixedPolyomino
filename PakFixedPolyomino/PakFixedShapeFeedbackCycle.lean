import PakFixedPolyomino.PakFixedShapeFeedbackEncoding

/-! Exact durations and endpoint data for every actual complete clean
feedback cycle. These facts require real component runs, not time premises. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackCycle
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases PakFixedShapeFeedbackComponents PakFixedShapeFeedbackEncoding
open PakFixedShapeFiniteLabelRound (L)
open PakFixedShapeFlaggedPreparation (prepare)

abbrev PConfig := Configuration preparation.states (roundAlphabet+extraAlphabet+3)
abbrev HConfig := Configuration 10 (roundAlphabet+extraAlphabet+3)
abbrev MConfig := Configuration
  (StandardBitFiniteChoicePrefix.ns L+PakFixedShapeNondeterministicRound.implementation.states+2)
  (roundAlphabet+extraAlphabet+3)

theorem prepare_end_unique (raw : List Bool) (a : Nat) (p : PConfig)
    (hr : run prepareMachine (ticks a) (initial prepareMachine raw)=some p)
    (ha : p.state=prepareMachine.accept) : a=prepareTime raw ∧ p=pfinal raw := by
  obtain ⟨hw,he⟩ := prepare_accepted_unique raw (ticks a) p hr ha
  refine ⟨?_,he⟩
  have hl := congrArg List.length hw
  simpa only [ticks,List.length_replicate] using hl

theorem strip_end_unique (raw : List Bool) (a : Nat) (h : HConfig)
    (hr : run stripMachine (ticks a) (initial stripMachine raw)=some h)
    (ha : h.state=stripMachine.accept) : a=stripTime raw ∧ h=hfinal raw := by
  obtain ⟨hw,he⟩ := strip_accepted_unique raw (ticks a) h hr ha
  refine ⟨?_,he⟩
  have hl := congrArg List.length hw
  simpa only [ticks,List.length_replicate] using hl

theorem cycle_unique (raw : List Bool) (a b d : Nat) (u : List Slot)
    (p : PConfig) (h1 : HConfig) (m : MConfig) (h2 : HConfig)
    (hrp : run prepareMachine (ticks a) (initial prepareMachine raw)=some p)
    (hap : p.state=prepareMachine.accept) (hfp : p.tape p.head=prepareMachine.one)
    (hrh1 : run stripMachine (ticks b) (StandardMachineNondeterministicFeedback.restartH stripMachine p)=some h1)
    (hah1 : h1.state=stripMachine.accept)
    (hrm : run roundMachine u (StandardMachineNondeterministicFeedback.restartM roundMachine h1)=some m)
    (ham : m.state=roundMachine.accept) (hfm : m.tape m.head=roundMachine.one)
    (hrh2 : run stripMachine (ticks d) (StandardMachineNondeterministicFeedback.restartH stripMachine m)=some h2)
    (hah2 : h2.state=stripMachine.accept) :
    ∃ i : Fin L,
      a=prepareTime raw ∧ p=pfinal raw ∧
      b=stripTime (prepare raw) ∧ h1=hfinal (prepare raw) ∧
      u=PakFixedShapeNondeterministicRound.path (prepare raw).tail i ∧ m=mfinal raw i ∧
      d=stripTime (checked raw i) ∧ h2=hfinal (checked raw i) ∧
      (prepare raw).headD false=true ∧ (checked raw i).headD false=true := by
  obtain ⟨rfl,rfl⟩ := prepare_end_unique raw a p hrp hap
  rw [restart_h_p] at hrh1
  obtain ⟨rfl,rfl⟩ := strip_end_unique (prepare raw) b h1 hrh1 hah1
  rw [restart_m_h] at hrm
  obtain ⟨i,hi,_,_⟩ := round_accepted_clean (prepare raw).tail u m hrm ham
  rw [hi,round_path_run] at hrm
  have he : m=mfinal raw i := (Option.some.inj hrm).symm
  subst m
  rw [restart_h_m] at hrh2
  obtain ⟨rfl,rfl⟩ := strip_end_unique (checked raw i) d h2 hrh2 hah2
  exact ⟨i,rfl,rfl,rfl,rfl,hi,rfl,rfl,rfl,
    (clean_head_one_iff prepareMachine (prepare raw)).mp hfp,
    (clean_head_one_iff roundMachine (checked raw i)).mp hfm⟩

end
end PakFixedPolyomino.PakFixedShapeFeedbackCycle
