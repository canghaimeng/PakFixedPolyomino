import PakFixedPolyomino.ULogSemanticFrameSelectedTargetCapacity
import PakFixedPolyomino.ULogConcreteClockChoiceUnderflow

/-! An actual selected right-boundary branch needs strictly more capacity
than its target state. This complements target capacity without assuming
readiness for the alternative slot. -/
namespace PakFixedPolyomino.ULogSemanticFrameSelectedRightCapacity
open ULogBootstrapExecution ULogProgram ULogAlphabet
open ULogFiniteTapeNondeterministicMicroInverse ULogSemanticFrameSelectedTargetCapacity
open ULogConcreteChoiceLookupUnderflow ULogConcreteClockChoiceUnderflow
open MStarParserExecution (Zipper)

theorem selected_right_boundary_target_lt_capacity {input : List Bool}
    (frame : SemanticCycleFrame input ([] : List Tape)) (focus : frame.config.focus < 3)
    (reads : ∀ r ∈ frame.config.program, r.read < 3) (runtime : PassivePath frame.runtime)
    (stateCapacity : frame.config.state ≤ frame.capacity)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (write : action.write < 3) (nonhalting : 2 ≤ action.target)
    (move : action.move = .right) (right : frame.config.right = [])
    (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) : action.target < frame.capacity := by
  have target := selected_nonhalting_target_le_capacity frame focus reads runtime stateCapacity
    slot action lookup write nonhalting rest tape raw
  by_contra shortage
  have same : action.target = frame.capacity := by omega
  have growth : action.target = frame.config.state + (frame.capacity - frame.config.state) := by
    omega
  cases zeros : frame.clockZeros with
  | zero =>
    apply no_accepting_choice_right slot frame.config.state frame.config.focus focus
      frame.config.program reads action write lookup input (frame.config.leftRev.map payloadNat)
      frame.outer frame.runtime (ulogCore clockZero) (frame.capacity - frame.config.state)
      (payloadNatList_safe frame.config.leftRev)
      (cursorDynamicProgramToHead_passive input frame.config.leftRev) runtime growth nonhalting
      move (Or.inl rfl) rest tape
    simpa only [frameChoice, choiceStart, stateWorkspace, right, List.map_nil, zeros,
      clockAfter_empty_zero, List.append_nil, List.append_assoc] using raw
  | succ n =>
    apply no_accepting_choice_right slot frame.config.state frame.config.focus focus
      frame.config.program reads action write lookup input (frame.config.leftRev.map payloadNat)
      frame.outer (List.replicate n (ulogCore clockOne) ++ ulogCore clockZero :: frame.runtime)
      (ulogCore clockOne) (frame.capacity - frame.config.state)
      (payloadNatList_safe frame.config.leftRev)
      (cursorDynamicProgramToHead_passive input frame.config.leftRev)
      (clockOnesZero_passive n runtime) growth nonhalting move (Or.inr rfl) rest tape
    simpa only [frameChoice, choiceStart, stateWorkspace, right, List.map_nil, zeros,
      clockAfter_empty_succ, List.append_nil, List.append_assoc] using raw

theorem selected_nonhalting_capacity_ready {input : List Bool}
    (frame : SemanticCycleFrame input ([] : List Tape)) (focus : frame.config.focus < 3)
    (reads : ∀ r ∈ frame.config.program, r.read < 3) (runtime : PassivePath frame.runtime)
    (stateCapacity : frame.config.state ≤ frame.capacity)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (write : action.write < 3) (nonhalting : 2 ≤ action.target)
    (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) : SemanticCapacityReady frame.config action frame.capacity := by
  have target := selected_nonhalting_target_le_capacity frame focus reads runtime stateCapacity
    slot action lookup write nonhalting rest tape raw
  cases move : action.move with
  | stay => simpa only [SemanticCapacityReady, move] using target
  | left => simpa only [SemanticCapacityReady, move] using target
  | right =>
    cases right : frame.config.right with
    | nil =>
        simpa only [SemanticCapacityReady, move, right] using
          selected_right_boundary_target_lt_capacity frame focus reads runtime stateCapacity
            slot action lookup write nonhalting move right rest tape raw
    | cons b bs => simpa only [SemanticCapacityReady, move, right] using target

end PakFixedPolyomino.ULogSemanticFrameSelectedRightCapacity
