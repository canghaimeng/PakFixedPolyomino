import PakFixedPolyomino.PakFixedShapeFeedbackCycle

/-! Exhaustive inverse of every actual raw accepting feedback word. No
canonical-image restriction is added to the standard Accepted predicate. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackDecoding
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases PakFixedShapeFeedbackComponents
open PakFixedShapeFeedbackEncoding PakFixedShapeFeedbackCycle
open PakFixedShapeFiniteLabelRound (L)
open PakFixedShapeFlaggedPreparation (prepare)

theorem trace_encoding (cP : PConfig) (slots : List Slot)
    (ht : StandardMachineNondeterministicFeedback.AcceptTrace prepareMachine roundMachine stripMachine positive cP slots) :
    ∀ raw,cP=initial prepareMachine raw → ∃ is,terminates raw is ∧ slots=encode raw is := by
  induction ht with
  | stop cP p a hr ha hn =>
    intro raw he
    subst cP
    obtain ⟨rfl,rfl⟩ := prepare_end_unique raw a p hr ha
    have hflag : (prepare raw).headD false=false := by
      exact Bool.eq_false_iff.mpr (fun hp => hn ((clean_head_one_iff prepareMachine (prepare raw)).mpr hp))
    exact ⟨[],(terminates_nil raw).mpr hflag,rfl⟩
  | next cP p h1 m h2 u rest a b d hrp hap hfp hrh1 hah1 hrm ham hfm hrh2 hah2 ht ih =>
    intro raw he
    subst cP
    obtain ⟨i,rfl,rfl,rfl,rfl,hu,rfl,rfl,rfl,hp,hm⟩ :=
      cycle_unique raw a b d u p h1 m h2 hrp hap hfp hrh1 hah1 hrm ham hfm hrh2 hah2
    obtain ⟨is,hs,he⟩ := ih (next raw i) (restart_p_h (checked raw i))
    refine ⟨i::is,(terminates_cons raw i is).mpr ⟨hp,hm,hs⟩,?_⟩
    simp only [encode,cycleWord,pword,hword,zero,hu,he,List.append_assoc]

theorem accepted_iff_encoding (raw : List Bool) (slots : List Slot) :
    Accepted machine raw slots ↔ ∃ is,terminates raw is ∧ slots=encode raw is := by
  constructor
  · intro ha
    have ht := (StandardMachineNondeterministicFeedback.accepted_iff_init prepareMachine roundMachine stripMachine
      positive same_codes raw slots).mp ha
    exact trace_encoding _ _ ht raw rfl
  · rintro ⟨is,ht,rfl⟩
    exact encoded_accepted raw is ht

end
end PakFixedPolyomino.PakFixedShapeFeedbackDecoding
