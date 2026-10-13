import PakFixedPolyomino.PakFixedShapeFeedbackCycle

/-! All local premises for the reachable feedback runtime compiler, proved
internally on original square states and actual component histories. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackCausalBounds
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicPhases PakFixedShapeFeedbackComponents PakFixedShapeFeedbackEncoding
open PakFixedShapeFeedbackCycle
open PakFixedShapeFlaggedPreparation (state prepare)
open PakFixedShapeConfigurationRank (Entry rank)
open PakFixedShapeFlaggedFrameBounds (frameBound)

def A (side : List Bool) := preparation.polynomial.eval (frameBound side.length)
def B (side : List Bool) := PakFixedShapeNondeterministicRound.polynomial.eval (frameBound side.length)
def C (side : List Bool) := 4*frameBound side.length+4

theorem preparation_bound (side : List Bool) (cP : PConfig) (hi : Entry side cP)
    (a : Nat) (p : PConfig) (hr : run prepareMachine (ticks a) cP=some p) : a≤A side := by
  obtain ⟨done,rfl⟩ := hi
  simpa only [A,C,ticks,List.length_replicate] using prepare_prefix_uniform side done (ticks a) p hr

theorem first_strip_bound (side : List Bool) (cP : PConfig) (a : Nat) (p : PConfig)
    (hi : Entry side cP) (hrp : run prepareMachine (ticks a) cP=some p)
    (hap : p.state=prepareMachine.accept) (hfp : p.tape p.head=prepareMachine.one)
    (b : Nat) (h1 : HConfig)
    (hrh1 : run stripMachine (ticks b) (StandardMachineNondeterministicFeedback.restartH stripMachine p)=some h1) : b≤C side := by
  obtain ⟨done,rfl⟩ := hi
  obtain ⟨_,rfl⟩ := prepare_end_unique (state side done) a p hrp hap
  rw [restart_h_p] at hrh1
  simpa only [A,C,ticks,List.length_replicate] using
    PakFixedShapeFeedbackStripBounds.before_choice_prefix side done (ticks b) h1 hrh1

theorem round_bound (side : List Bool) (cP : PConfig) (a : Nat) (p : PConfig)
    (b : Nat) (h1 : HConfig) (hi : Entry side cP)
    (hrp : run prepareMachine (ticks a) cP=some p) (hap : p.state=prepareMachine.accept)
    (hfp : p.tape p.head=prepareMachine.one)
    (hrh1 : run stripMachine (ticks b) (StandardMachineNondeterministicFeedback.restartH stripMachine p)=some h1)
    (hah1 : h1.state=stripMachine.accept) (u : List Slot) (m : MConfig)
    (hrm : run roundMachine u (StandardMachineNondeterministicFeedback.restartM roundMachine h1)=some m) : u.length≤B side := by
  obtain ⟨done,rfl⟩ := hi
  obtain ⟨_,rfl⟩ := prepare_end_unique (state side done) a p hrp hap
  rw [restart_h_p] at hrh1
  obtain ⟨_,rfl⟩ := strip_end_unique (prepare (state side done)) b h1 hrh1 hah1
  rw [restart_m_h] at hrm
  exact round_prefix_uniform side done u m hrm

theorem second_strip_bound (side : List Bool) (cP : PConfig) (a : Nat) (p : PConfig)
    (b : Nat) (h1 : HConfig) (u : List Slot) (m : MConfig) (hi : Entry side cP)
    (hrp : run prepareMachine (ticks a) cP=some p) (hap : p.state=prepareMachine.accept)
    (hfp : p.tape p.head=prepareMachine.one)
    (hrh1 : run stripMachine (ticks b) (StandardMachineNondeterministicFeedback.restartH stripMachine p)=some h1)
    (hah1 : h1.state=stripMachine.accept)
    (hrm : run roundMachine u (StandardMachineNondeterministicFeedback.restartM roundMachine h1)=some m)
    (ham : m.state=roundMachine.accept) (hfm : m.tape m.head=roundMachine.one)
    (d : Nat) (h2 : HConfig)
    (hrh2 : run stripMachine (ticks d) (StandardMachineNondeterministicFeedback.restartH stripMachine m)=some h2) : d≤C side := by
  obtain ⟨done,rfl⟩ := hi
  obtain ⟨_,rfl⟩ := prepare_end_unique (state side done) a p hrp hap
  rw [restart_h_p] at hrh1
  obtain ⟨_,rfl⟩ := strip_end_unique (prepare (state side done)) b h1 hrh1 hah1
  rw [restart_m_h] at hrm
  have hp := (clean_head_one_iff prepareMachine (prepare (state side done))).mp hfp
  simpa only [A,C,ticks,List.length_replicate] using
    PakFixedShapeFeedbackStripBounds.every_valid_round_strip_prefix side done hp u m hrm ham hfm (ticks d) h2 hrh2

theorem return_entry_decreases (side : List Bool) (cP : PConfig) (a : Nat) (p : PConfig)
    (b : Nat) (h1 : HConfig) (u : List Slot) (m : MConfig) (d : Nat) (h2 : HConfig) (hi : Entry side cP)
    (hrp : run prepareMachine (ticks a) cP=some p) (hap : p.state=prepareMachine.accept)
    (hfp : p.tape p.head=prepareMachine.one)
    (hrh1 : run stripMachine (ticks b) (StandardMachineNondeterministicFeedback.restartH stripMachine p)=some h1)
    (hah1 : h1.state=stripMachine.accept)
    (hrm : run roundMachine u (StandardMachineNondeterministicFeedback.restartM roundMachine h1)=some m)
    (ham : m.state=roundMachine.accept) (hfm : m.tape m.head=roundMachine.one)
    (hrh2 : run stripMachine (ticks d) (StandardMachineNondeterministicFeedback.restartH stripMachine m)=some h2)
    (hah2 : h2.state=stripMachine.accept) :
    Entry side (StandardMachineNondeterministicFeedback.restartP prepareMachine h2) ∧
      rank (StandardMachineNondeterministicFeedback.restartP prepareMachine h2)<rank cP := by
  obtain ⟨done,rfl⟩ := hi
  obtain ⟨_,next,_,_,he,hd⟩ := physical_backedge side done (ticks a) (ticks b) (ticks d) u p h1 h2 m
    hrp hap hfp hrh1 hah1 hrm ham hfm hrh2 hah2
  refine ⟨⟨next,he⟩,?_⟩
  exact (congrArg rank he).trans_lt hd

theorem initial_entry (side : List Bool) : Entry side (initial prepareMachine (state side ∅)) := ⟨∅,rfl⟩

end
end PakFixedPolyomino.PakFixedShapeFeedbackCausalBounds
