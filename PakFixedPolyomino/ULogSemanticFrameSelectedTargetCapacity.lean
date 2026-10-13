import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroInverse
import PakFixedPolyomino.ULogConcreteChoiceLookupUnderflow

/-! Capacity necessity for the actual selected physical branch of a semantic
frame. Both-slot readiness is not assumed. This local result is used when
auditing physical paths below the sufficient-capacity threshold. -/
namespace PakFixedPolyomino.ULogSemanticFrameSelectedTargetCapacity
open ULogBootstrapExecution ULogConcreteChoiceBarrier ULogConcreteSlotMicroExpansion
open ULogFiniteTapeNondeterministicMicroInverse ULogAlphabet ULogProgram
open ULogConcreteChoiceLookupUnderflow
open ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)

theorem selected_lookup_exists {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (focus : frame.config.focus < 3)
    (nonempty : frame.config.program ≠ [])
    (reads : ∀ r ∈ frame.config.program, r.read < 3) (runtime : PassivePath frame.runtime)
    (slot : Bool) (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) :
    ∃ action, ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action := by
  cases lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot with
  | some action => exact ⟨action, rfl⟩
  | none =>
    obtain ⟨rejectCycle⟩ := ULogActiveExactNoRule.branchedCycle_semanticNoRule_exact_nonempty
      frame.config slot input frame.clockZeros frame.capacity frame.runtime frame.outer suffix
      runtime focus nonempty reads lookup
    have cycle : ExactConcreteCycle slot frame.encode .rejected := by
      simpa only [SemanticCycleFrame.encode] using rejectCycle
    have choice := cycle.choicePrefix.finish_unique (frame_first_choice frame focus)
    have selected : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex slot :: rest)
        (.accepted tape) := by simpa only [choice] using raw
    obtain ⟨tail, _, after⟩ := split_after_cycle_selection cycle selected
    have last := ULogConcreteMicroPathSplitting.microPath_halted_start after (by rfl)
    cases last.2

theorem selected_nonhalting_target_le_capacity {input : List Bool}
    (frame : SemanticCycleFrame input ([] : List Tape)) (focus : frame.config.focus < 3)
    (reads : ∀ r ∈ frame.config.program, r.read < 3) (runtime : PassivePath frame.runtime)
    (stateCapacity : frame.config.state ≤ frame.capacity)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (write : action.write < 3) (nonhalting : 2 ≤ action.target)
    (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) : action.target ≤ frame.capacity := by
  by_contra shortage
  have impossible := no_accepting_choice_capacity slot frame.config.state frame.config.focus
    focus frame.config.program reads action write lookup input (frame.config.leftRev.map payloadNat)
    (clockCellsAfter (frame.config.right.map payloadNat) frame.clockZeros frame.runtime)
    frame.outer (payloadNatList_safe frame.config.leftRev)
    (cursorDynamicProgramToHead_passive input frame.config.leftRev)
    (clockCellsAfter_passive frame.config.right frame.clockZeros frame.runtime runtime)
    frame.capacity stateCapacity (by omega) nonhalting rest tape
  apply impossible
  simpa only [frameChoice, choiceStart, stateWorkspace, List.append_nil, List.append_assoc] using raw

end PakFixedPolyomino.ULogSemanticFrameSelectedTargetCapacity
