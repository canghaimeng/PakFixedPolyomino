import PakFixedPolyomino.PakFixedShapeFeedbackStripBounds
import PakFixedPolyomino.StandardMachineNondeterministicFeedback
import PakFixedPolyomino.StandardMachineAcceptingPrefixUniqueness

/-! A proof-level physical encoding of reference placement words. The finite
machine rules do not depend on this encoding or on selected durations. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackEncoding
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases
open PakFixedShapeFeedbackComponents
open PakFixedShapeFiniteLabelRound (L checkedRound labelAt)
open PakFixedShapeFlaggedPreparation (prepare state)

abbrev Slot := Fin (L+1)
theorem positive : 0<L+1 := Nat.zero_lt_succ L
def zero : Slot := StandardMachineNondeterministicFeedback.zeroSlot positive

theorem same_codes : StandardMachineNondeterministicFeedback.SameCodes
    prepareMachine roundMachine stripMachine := by
  obtain ⟨mb,mz,mo,hb,hz,ho⟩ := codes
  exact ⟨mb.symm,mz.symm,mo.symm,hb.symm,hz.symm,ho.symm⟩

def machine := StandardMachineNondeterministicFeedback.machine
  prepareMachine roundMachine stripMachine positive same_codes

def checked (raw : List Bool) (i : Fin L) := checkedRound (labelAt i) (prepare raw).tail
def next (raw : List Bool) (i : Fin L) := (checked raw i).tail
def pword (raw : List Bool) : List Slot := List.replicate (prepareTime raw) zero
def hword (raw : List Bool) : List Slot := List.replicate (stripTime raw) zero
def cycleWord (raw : List Bool) (i : Fin L) : List Slot :=
  pword raw++[zero]++hword (prepare raw)++[zero]++
    PakFixedShapeNondeterministicRound.path (prepare raw).tail i++[zero]++
    hword (checked raw i)++[zero]
def encode : List Bool → List (Fin L) → List Slot
  | raw,[] => pword raw++[zero]
  | raw,i::is => cycleWord raw i++encode (next raw i) is

def terminates (raw : List Bool) (is : List (Fin L)) : Prop :=
  (PakFixedShapeFlaggedChoiceWords.run is raw).map
    (fun out => (prepare out).headD false)=some false

theorem terminates_nil (raw : List Bool) : terminates raw [] ↔ (prepare raw).headD false=false := by
  simp [terminates,PakFixedShapeFlaggedChoiceWords.run]

theorem terminates_cons (raw : List Bool) (i : Fin L) (is : List (Fin L)) :
    terminates raw (i::is) ↔
      (prepare raw).headD false=true ∧ (checked raw i).headD false=true ∧ terminates (next raw i) is := by
  have step_formula : PakFixedShapeFlaggedChoiceWords.step i raw=
      if (prepare raw).headD false then
        if (checked raw i).headD false then some (next raw i) else none
      else none := by
    simp only [PakFixedShapeFlaggedChoiceWords.step,PakFixedShapeFiniteLabelRound.round_code,checked,next]
    rfl
  change ((PakFixedShapeFlaggedChoiceWords.step i raw).bind (PakFixedShapeFlaggedChoiceWords.run is)).map
    (fun out => (prepare out).headD false)=some false ↔
      (prepare raw).headD false=true ∧ (checked raw i).headD false=true ∧
        (PakFixedShapeFlaggedChoiceWords.run is (next raw i)).map (fun out => (prepare out).headD false)=some false
  rw [step_formula]
  cases hp : (prepare raw).headD false <;> cases hm : (checked raw i).headD false <;>
    simp only [hp,hm,Bool.false_eq_true,if_false,if_true,Option.bind_none,Option.bind_some,
      Option.map_none,and_false,and_true,false_and,true_and] <;> simp

def pfinal (raw : List Bool) :=
  (⟨prepareMachine.accept,0,inputTape prepareMachine (prepare raw)⟩ :
    Configuration preparation.states (roundAlphabet+extraAlphabet+3))
def hfinal (raw : List Bool) :=
  (⟨stripMachine.accept,0,inputTape stripMachine raw.tail⟩ :
    Configuration 10 (roundAlphabet+extraAlphabet+3))
def mfinal (raw : List Bool) (i : Fin L) :=
  (⟨roundMachine.accept,0,inputTape roundMachine (checked raw i)⟩ :
    Configuration (StandardBitFiniteChoicePrefix.ns L+PakFixedShapeNondeterministicRound.implementation.states+2)
      (roundAlphabet+extraAlphabet+3))

theorem restart_h_p (raw : List Bool) :
    StandardMachineNondeterministicFeedback.restartH stripMachine (pfinal raw)=
      initial stripMachine (prepare raw) := by
  obtain ⟨_,_,_,hb,hz,ho⟩ := codes
  exact restart_clean stripMachine prepareMachine hb hz ho _ _ rfl rfl

theorem restart_m_h (raw : List Bool) :
    StandardMachineNondeterministicFeedback.restartM roundMachine (hfinal raw)=initial roundMachine raw.tail := by
  obtain ⟨mb,mz,mo,hb,hz,ho⟩ := codes
  exact restart_clean roundMachine stripMachine (mb.trans hb.symm) (mz.trans hz.symm) (mo.trans ho.symm) _ _ rfl rfl

theorem restart_h_m (raw : List Bool) (i : Fin L) :
    StandardMachineNondeterministicFeedback.restartH stripMachine (mfinal raw i)=initial stripMachine (checked raw i) := by
  obtain ⟨mb,mz,mo,hb,hz,ho⟩ := codes
  exact restart_clean stripMachine roundMachine (hb.trans mb.symm) (hz.trans mz.symm) (ho.trans mo.symm) _ _ rfl rfl

theorem restart_p_h (raw : List Bool) :
    StandardMachineNondeterministicFeedback.restartP prepareMachine (hfinal raw)=initial prepareMachine raw.tail := by
  obtain ⟨_,_,_,hb,hz,ho⟩ := codes
  exact restart_clean prepareMachine stripMachine hb.symm hz.symm ho.symm _ _ rfl rfl

theorem encoded_trace (raw : List Bool) (is : List (Fin L)) (ht : terminates raw is) :
    StandardMachineNondeterministicFeedback.AcceptTrace prepareMachine roundMachine stripMachine positive
      (initial prepareMachine raw) (encode raw is) := by
  induction is generalizing raw with
  | nil =>
    have hp := (terminates_nil raw).mp ht
    have hn : (pfinal raw).tape (pfinal raw).head≠prepareMachine.one := by
      intro he
      have h := (clean_head_one_iff prepareMachine (prepare raw)).mp he
      rw [hp] at h
      contradiction
    exact StandardMachineNondeterministicFeedback.AcceptTrace.stop _ (pfinal raw) (prepareTime raw)
      (prepare_time_spec raw).2 rfl hn
  | cons i is ih =>
    obtain ⟨hp,hm,hs⟩ := (terminates_cons raw i is).mp ht
    have hpflag : (pfinal raw).tape (pfinal raw).head=prepareMachine.one :=
      (clean_head_one_iff prepareMachine (prepare raw)).mpr hp
    have hmflag : (mfinal raw i).tape (mfinal raw i).head=roundMachine.one :=
      (clean_head_one_iff roundMachine (checked raw i)).mpr hm
    have hh1 : run stripMachine (ticks (stripTime (prepare raw)))
        (StandardMachineNondeterministicFeedback.restartH stripMachine (pfinal raw))=some (hfinal (prepare raw)) := by
      rw [restart_h_p]
      exact (strip_time_spec (prepare raw)).2
    have hmr : run roundMachine (PakFixedShapeNondeterministicRound.path (prepare raw).tail i)
        (StandardMachineNondeterministicFeedback.restartM roundMachine (hfinal (prepare raw)))=some (mfinal raw i) := by
      rw [restart_m_h]
      exact round_path_run _ i
    have hh2 : run stripMachine (ticks (stripTime (checked raw i)))
        (StandardMachineNondeterministicFeedback.restartH stripMachine (mfinal raw i))=some (hfinal (checked raw i)) := by
      rw [restart_h_m]
      exact (strip_time_spec (checked raw i)).2
    have hrest : StandardMachineNondeterministicFeedback.AcceptTrace prepareMachine roundMachine stripMachine positive
        (StandardMachineNondeterministicFeedback.restartP prepareMachine (hfinal (checked raw i))) (encode (next raw i) is) := by
      rw [restart_p_h]
      exact ih _ hs
    simpa only [encode,cycleWord,pword,hword,zero,List.append_assoc] using
      StandardMachineNondeterministicFeedback.AcceptTrace.next (initial prepareMachine raw) (pfinal raw)
        (hfinal (prepare raw)) (mfinal raw i) (hfinal (checked raw i))
        (PakFixedShapeNondeterministicRound.path (prepare raw).tail i) (encode (next raw i) is)
        (prepareTime raw) (stripTime (prepare raw)) (stripTime (checked raw i))
        (prepare_time_spec raw).2 rfl hpflag hh1 rfl hmr rfl hmflag hh2 rfl hrest

theorem encoded_accepted (raw : List Bool) (is : List (Fin L)) (ht : terminates raw is) :
    Accepted machine raw (encode raw is) := by
  exact (StandardMachineNondeterministicFeedback.accepted_iff_init prepareMachine roundMachine stripMachine
    positive same_codes raw _).mpr (encoded_trace raw is ht)

end
end PakFixedPolyomino.PakFixedShapeFeedbackEncoding
