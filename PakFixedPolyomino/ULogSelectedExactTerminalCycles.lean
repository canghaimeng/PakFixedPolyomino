import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroInverse

/-! Literal terminal cycles use the selected lookup and basic local frame
invariants. Readiness of the alternative slot is unnecessary. Target-one
uses the separately audited standard-axiom first-hit rejection proof. -/
namespace PakFixedPolyomino.ULogSelectedExactTerminalCycles
open ULogBootstrapExecution ULogProgram
open ULogFiniteTapeNondeterministicMicroInverse ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)

theorem selected_accepting_cycle_nonempty {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (focus : frame.config.focus < 3) (reads : ∀ r ∈ frame.config.program, r.read < 3)
    (writes : ∀ r ∈ frame.config.program, r.action.write < 3)
    (runtime : PassivePath frame.runtime) (stateCapacity : frame.config.state ≤ frame.capacity)
    (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action) (accept : action.target = 0) :
    Nonempty (ExactAcceptingWitness frame slot) := by
  obtain ⟨⟨tape, cycle⟩⟩ := branchedCycle_semanticTargetZero_exact_nonempty
    frame.config slot action lookup accept input frame.clockZeros frame.capacity
    frame.runtime frame.outer suffix runtime focus reads writes stateCapacity
  exact ⟨{ tape := tape, exact_cycle := by simpa only [SemanticCycleFrame.encode] using cycle }⟩

theorem selected_rejecting_cycle_nonempty {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (focus : frame.config.focus < 3) (reads : ∀ r ∈ frame.config.program, r.read < 3)
    (writes : ∀ r ∈ frame.config.program, r.action.write < 3)
    (runtime : PassivePath frame.runtime) (stateCapacity : frame.config.state ≤ frame.capacity)
    (oneCapacity : 1 ≤ frame.capacity) (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action) (reject : action.target = 1) :
    Nonempty (ExactConcreteCycle slot frame.encode .rejected) := by
  simpa only [SemanticCycleFrame.encode] using
    ULogActiveExactTargetOne.branchedCycle_semanticTargetOne_exact_nonempty
      frame.config slot action lookup reject input frame.clockZeros frame.capacity
      frame.runtime frame.outer suffix runtime focus reads writes stateCapacity oneCapacity

theorem selected_target_one_no_accepting_tail {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (focus : frame.config.focus < 3) (reads : ∀ r ∈ frame.config.program, r.read < 3)
    (writes : ∀ r ∈ frame.config.program, r.action.write < 3)
    (runtime : PassivePath frame.runtime) (stateCapacity : frame.config.state ≤ frame.capacity)
    (oneCapacity : 1 ≤ frame.capacity) (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action) (reject : action.target = 1)
    (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) : False := by
  obtain ⟨cycle⟩ := selected_rejecting_cycle_nonempty frame slot focus reads writes runtime
    stateCapacity oneCapacity action lookup reject
  have choice := cycle.choicePrefix.finish_unique (frame_first_choice frame focus)
  have selected : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape) := by simpa only [choice] using raw
  obtain ⟨tail, _, after⟩ := split_after_cycle_selection cycle selected
  have last := microPath_halted_start after (by rfl)
  cases last.2

end PakFixedPolyomino.ULogSelectedExactTerminalCycles
