import PakFixedPolyomino.PakFixedShapeConfigurationRank
import PakFixedPolyomino.PakFixedShapeFlaggedReachability
import PakFixedPolyomino.PakFixedShapeNondeterministicTimeEnvelope
import PakFixedPolyomino.StandardMachineDeterministicDuration

/-! Internally supplied physical component bounds and exact clean outputs
for the original family. These facts concern every successful component run,
and therefore apply to the feedback compiler's arbitrary raw-run inverse. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackComponents
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases
open PakFixedShapeFlaggedPreparation (state prepare)
open PakFixedShapeFiniteLabelRound (L checkedRound labelAt)
open PakFixedShapeChoiceWords (Done)
open PakFixedShapeFlaggedFrameBounds (frameBound)

def restart {ns nt nb ms : Nat} (M : Machine ns nt nb) (c : Configuration ms nt) : Configuration ns nt :=
  ⟨M.start,c.head,c.tape⟩

theorem restart_clean {ns nt nb ms mb : Nat} (M : Machine ns nt nb) (N : Machine ms nt mb)
    (hb : M.blank=N.blank) (hz : M.zero=N.zero) (ho : M.one=N.one)
    (raw : List Bool) (c : Configuration ms nt) (hh : c.head=0) (ht : c.tape=inputTape N raw) :
    restart M c=initial M raw := by
  have he := StandardMachineCleanWordReadback.inputTape_codes M N hb hz ho raw
  cases c
  simp_all [restart,initial]

def prepareTime (raw : List Bool) : Nat := StandardMachineDeterministicDuration.duration
  prepareMachine prepare (fun n => preparation.polynomial.eval n) prepare_computes raw
def stripTime (raw : List Bool) : Nat := StandardMachineDeterministicDuration.duration
  stripMachine (fun raw => raw.tail) (fun n => 4*n+4) strip_computes raw

theorem prepare_time_spec (raw : List Bool) :
    prepareTime raw≤preparation.polynomial.eval raw.length ∧
      run prepareMachine (ticks (prepareTime raw)) (initial prepareMachine raw)=
        some ⟨prepareMachine.accept,0,inputTape prepareMachine (prepare raw)⟩ :=
  StandardMachineDeterministicDuration.duration_spec _ _ _ prepare_computes raw

theorem strip_time_spec (raw : List Bool) : stripTime raw≤4*raw.length+4 ∧
    run stripMachine (ticks (stripTime raw)) (initial stripMachine raw)=
      some ⟨stripMachine.accept,0,inputTape stripMachine raw.tail⟩ :=
  StandardMachineDeterministicDuration.duration_spec _ _ _ strip_computes raw

theorem prepare_prefix_uniform (side : List Bool) (done : Done) :
    RunsAtMost prepareMachine (state side done) (preparation.polynomial.eval (frameBound side.length)) := by
  intro slots out hr
  exact ((prepare_computes.actual_bounds _ _ _ (state side done)).1 slots out hr).trans
    (StandardBitTimeComposition.eval_mono preparation.polynomial
      (PakFixedShapeFlaggedFrameBounds.state_frame_bound side done))

theorem round_prefix_uniform (side : List Bool) (done : Done) :
    RunsAtMost roundMachine (prepare (state side done)).tail
      (PakFixedShapeNondeterministicRound.polynomial.eval (frameBound side.length)) := by
  have hl : (prepare (state side done)).tail.length≤frameBound side.length := by
    have hb := PakFixedShapeFlaggedFrameBounds.prepared_frame_bound side done
    rw [List.length_tail]
    omega
  intro slots out hr
  exact (round_prefix_bound _ slots out hr).trans
    (StandardBitTimeComposition.eval_mono PakFixedShapeNondeterministicRound.polynomial hl)

theorem strip_prefix_uniform (side : List Bool) (raw : List Bool) (hl : raw.length≤frameBound side.length) :
    RunsAtMost stripMachine raw (4*frameBound side.length+4) := by
  intro slots out hr
  have h := (strip_computes.actual_bounds _ _ _ raw).1 slots out hr
  omega

theorem prepare_accepted_unique (raw : List Bool) (slots : List (Fin 1))
    (out : Configuration preparation.states (roundAlphabet+extraAlphabet+3))
    (hr : run prepareMachine slots (initial prepareMachine raw)=some out) (ha : out.state=prepareMachine.accept) :
    slots=ticks (prepareTime raw) ∧ out=⟨prepareMachine.accept,0,inputTape prepareMachine (prepare raw)⟩ :=
  StandardMachineDeterministicDuration.accepted_run_unique _ _ _ prepare_computes raw slots out hr ha

theorem strip_accepted_unique (raw : List Bool) (slots : List (Fin 1))
    (out : Configuration 10 (roundAlphabet+extraAlphabet+3))
    (hr : run stripMachine slots (initial stripMachine raw)=some out) (ha : out.state=stripMachine.accept) :
    slots=ticks (stripTime raw) ∧ out=⟨stripMachine.accept,0,inputTape stripMachine raw.tail⟩ :=
  StandardMachineDeterministicDuration.accepted_run_unique _ _ _ strip_computes raw slots out hr ha

theorem successful_step_state (side : List Bool) (done : Done) (i : Fin L) (raw : List Bool)
    (hr : PakFixedShapeFlaggedChoiceWords.step i (state side done)=some raw) :
    ∃ next : Done,raw=state side next := by
  obtain ⟨next,_,he⟩ := PakFixedShapeFlaggedReachability.original_output side done [i] raw
    (by simp only [PakFixedShapeFlaggedChoiceWords.run,hr,Option.bind_some])
  exact ⟨next,he⟩

theorem successful_step_flags (side : List Bool) (done : Done) (i : Fin L)
    (hp : (prepare (state side done)).headD false=true)
    (hm : (checkedRound (labelAt i) (prepare (state side done)).tail).headD false=true) :
    PakFixedShapeFlaggedChoiceWords.step i (state side done)=
      some (checkedRound (labelAt i) (prepare (state side done)).tail).tail := by
  simp only [PakFixedShapeFlaggedChoiceWords.step,hp,if_true,
    PakFixedShapeFiniteLabelRound.round_code,hm]

theorem successful_backedge_state (side : List Bool) (done : Done) (i : Fin L)
    (hp : (prepare (state side done)).headD false=true)
    (hm : (checkedRound (labelAt i) (prepare (state side done)).tail).headD false=true) :
    ∃ next : Done,
      (checkedRound (labelAt i) (prepare (state side done)).tail).tail=state side next ∧
      PakFixedShapeOccupancyRank.rank (state side next)<PakFixedShapeOccupancyRank.rank (state side done) := by
  have hs := successful_step_flags side done i hp hm
  obtain ⟨next,he⟩ := successful_step_state side done i _ hs
  refine ⟨next,he,?_⟩
  exact he ▸ PakFixedShapeOccupancyRank.step_decreases side done i _ hs

theorem clean_head_one_iff {ns nt nb : Nat} (M : Machine ns nt nb) (raw : List Bool) :
    inputTape M raw 0=M.one ↔ raw.headD false=true := by
  cases raw with
  | nil =>
    simp only [List.headD_nil,Bool.false_eq_true,iff_false]
    exact M.blank_ne_one
  | cons b bs => cases b <;> simp [inputTape,M.zero_ne_one]

theorem physical_backedge (side : List Bool) (done : Done)
    (a b d : List (Fin 1)) (u : List (Fin (L+1)))
    (pout : Configuration preparation.states (roundAlphabet+extraAlphabet+3))
    (h1 h2 : Configuration 10 (roundAlphabet+extraAlphabet+3))
    (mout : Configuration (StandardBitFiniteChoicePrefix.ns L+PakFixedShapeNondeterministicRound.implementation.states+2)
      (roundAlphabet+extraAlphabet+3))
    (hrp : run prepareMachine a (initial prepareMachine (state side done))=some pout)
    (hap : pout.state=prepareMachine.accept) (hfp : pout.tape pout.head=prepareMachine.one)
    (hrh1 : run stripMachine b (restart stripMachine pout)=some h1) (hah1 : h1.state=stripMachine.accept)
    (hrm : run roundMachine u (restart roundMachine h1)=some mout)
    (ham : mout.state=roundMachine.accept) (hfm : mout.tape mout.head=roundMachine.one)
    (hrh2 : run stripMachine d (restart stripMachine mout)=some h2) (hah2 : h2.state=stripMachine.accept) :
    ∃ (i : Fin L) (next : Done),
      u=PakFixedShapeNondeterministicRound.path (prepare (state side done)).tail i ∧
      PakFixedShapeFlaggedChoiceWords.step i (state side done)=some (state side next) ∧
      restart prepareMachine h2=initial prepareMachine (state side next) ∧
      PakFixedShapeConfigurationRank.rank (initial prepareMachine (state side next))<
        PakFixedShapeConfigurationRank.rank (initial prepareMachine (state side done)) := by
  obtain ⟨mb,mz,mo,hb,hz,ho⟩ := codes
  obtain ⟨_,hep⟩ := prepare_accepted_unique _ a pout hrp hap
  subst pout
  have hp := (clean_head_one_iff prepareMachine (prepare (state side done))).mp hfp
  have hstart1 := restart_clean stripMachine prepareMachine hb hz ho
    (prepare (state side done)) ⟨prepareMachine.accept,0,inputTape prepareMachine (prepare (state side done))⟩ rfl rfl
  have hrh1' := (congrArg (run stripMachine b) hstart1).symm.trans hrh1
  obtain ⟨_,heh1⟩ := strip_accepted_unique _ b h1 hrh1' hah1
  subst h1
  have hstartm := restart_clean roundMachine stripMachine (mb.trans hb.symm) (mz.trans hz.symm) (mo.trans ho.symm)
    (prepare (state side done)).tail
    ⟨stripMachine.accept,0,inputTape stripMachine (prepare (state side done)).tail⟩ rfl rfl
  have hrm' := (congrArg (run roundMachine u) hstartm).symm.trans hrm
  obtain ⟨i,hi,hh,ht⟩ := round_accepted_clean _ u mout hrm' ham
  have hem : mout=⟨roundMachine.accept,0,inputTape roundMachine (checkedRound (labelAt i) (prepare (state side done)).tail)⟩ := by
    cases mout
    simp_all <;> rfl
  subst mout
  have hm := (clean_head_one_iff roundMachine (checkedRound (labelAt i) (prepare (state side done)).tail)).mp hfm
  have hstart2 := restart_clean stripMachine roundMachine (hb.trans mb.symm) (hz.trans mz.symm) (ho.trans mo.symm)
    (checkedRound (labelAt i) (prepare (state side done)).tail)
    ⟨roundMachine.accept,0,inputTape roundMachine (checkedRound (labelAt i) (prepare (state side done)).tail)⟩ rfl rfl
  have hrh2' := (congrArg (run stripMachine d) hstart2).symm.trans hrh2
  obtain ⟨_,heh2⟩ := strip_accepted_unique _ d h2 hrh2' hah2
  subst h2
  obtain ⟨next,he,hd⟩ := successful_backedge_state side done i hp hm
  refine ⟨i,next,hi,?_,?_,?_⟩
  · exact (successful_step_flags side done i hp hm).trans (congrArg some he)
  · exact (restart_clean prepareMachine stripMachine hb.symm hz.symm ho.symm _ _ rfl rfl).trans
      (congrArg (initial prepareMachine) he)
  · exact (PakFixedShapeConfigurationRank.rank_initial _).trans_lt
      (hd.trans_eq (PakFixedShapeConfigurationRank.rank_initial _).symm)

end
end PakFixedPolyomino.PakFixedShapeFeedbackComponents
