import PakFixedPolyomino.MStarULogAssembly

/-! Kernel replacements for the literal outer accept/reject maps and the
interpreter's accepting edge movement. Frozen original tables are unchanged. -/
namespace PakFixedPolyomino.PakOuterULogKernelAcceptFacts
open OneTapeTableau FiniteOneTapeProgram

theorem simulated_accept_maps_to_outer_accept :
    MStarOuterProgram.mapUState MStarULogAssembly.data ULogControl.qAccept =
      MStarOuterProgram.State.accept := by
  rfl

theorem simulated_reject_maps_to_outer_reject :
    MStarOuterProgram.mapUState MStarULogAssembly.data ULogControl.qReject =
      MStarOuterProgram.State.reject := by
  rfl

def acceptingMoveTest (act : Action ULogControl.State ULogProgram.Tape) : Bool :=
  decide (act.target ≠ ULogControl.qAccept ∨ act.move = .stay)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem rule_accepting_move_test :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      (ULogProgram.program.rule q x slot).all acceptingMoveTest = true := by
  decide

theorem ulog_rule_target_accept_move_stay
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (act : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q x slot = some act)
    (htarget : act.target = ULogControl.qAccept) : act.move = .stay := by
  have ht := rule_accepting_move_test q x slot
  simpa [hrule, acceptingMoveTest, htarget] using ht

def kernel_accept_facts_spec : Prop :=
  MStarOuterProgram.mapUState MStarULogAssembly.data ULogControl.qAccept =
      MStarOuterProgram.State.accept ∧
  MStarOuterProgram.mapUState MStarULogAssembly.data ULogControl.qReject =
      MStarOuterProgram.State.reject ∧
  (∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (act : Action ULogControl.State ULogProgram.Tape),
    ULogProgram.program.rule q x slot = some act →
      act.target = ULogControl.qAccept → act.move = .stay)

theorem kernel_accept_facts_spec_holds : kernel_accept_facts_spec :=
  ⟨simulated_accept_maps_to_outer_accept, simulated_reject_maps_to_outer_reject,
    ulog_rule_target_accept_move_stay⟩

end PakFixedPolyomino.PakOuterULogKernelAcceptFacts
