/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeCycleBound
import PakFixedPolyomino.ULogLocalTimeStayGrowth
import PakFixedPolyomino.ULogLocalTimeStayDecrease
import PakFixedPolyomino.ULogLocalTimeRightDecrease
import PakFixedPolyomino.ULogLocalTimeRightGrowth
import PakFixedPolyomino.ULogLocalTimeRightBoundary
import PakFixedPolyomino.ULogLocalTimeLeftDecrease
import PakFixedPolyomino.ULogLocalTimeLeftGrowth
import PakFixedPolyomino.ULogLocalTimeLeftBoundary

/-! Ten-case physical dispatcher and complete nonhalting cycle cubic bound.
Frozen callbacks instantiate CanonicalTailBuilder internally. No movement
restriction remains on the complete-cycle theorem. Global ready and the
original counting theorem remain open. -/

namespace PakFixedPolyomino.ULogLocalTimeAllCycles

open ULogProgram ULogBootstrapExecution
open PakULogCycleResourceBound ULogLocalTimeCycleBound
open ULogLocalTimeStayGrowth
open ULogLocalTimeStayDecrease
open ULogLocalTimeRightDecrease
open ULogLocalTimeRightGrowth
open ULogLocalTimeRightBoundary
open ULogLocalTimeLeftDecrease
open ULogLocalTimeLeftGrowth
open ULogLocalTimeLeftBoundary

theorem cursor_radius_resources_invariant
    {input : List Bool} {suffix : List Tape} (frame : SemanticCycleFrame input suffix)
    (capacity : Nat) (outer : List Tape) :
    semanticFrameCursorRadius input
      ({ frame with capacity := capacity, outer := outer } : SemanticCycleFrame input suffix) =
      semanticFrameCursorRadius input frame := by rfl

theorem canonicalTailBuilder_all
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix) (slot : Bool)
    (ready : ULogBootstrapExecution.FrameReady frame)
    (hruntime : ULogBootstrapExecution.PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (reframe : ULogBootstrapExecution.ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map
        ULogBootstrapExecution.payloadNat)
      (ULogBootstrapExecution.clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map
          ULogBootstrapExecution.payloadNat)
        frame.clockZeros frame.runtime)) :
    ULogLocalTimeStayGrowth.CanonicalTailBuilder frame slot action reframe
      (PakULogCycleResourceBound.semanticFrameCursorRadius input frame) := by
  cases hm : action.move with
  | stay =>
    by_cases hle : frame.config.state ≤ action.target
    · have ht : action.target = frame.config.state +
          (action.target - frame.config.state) := by omega
      exact canonicalTailBuilder_stayAtLeast frame slot ready hruntime
        action hlookup hhalt (action.target - frame.config.state) ht hm reframe
    · have hs : frame.config.state = action.target +
          (frame.config.state - action.target) := by omega
      exact canonicalTailBuilder_stayAtMost frame slot ready hruntime
        action hlookup hhalt (frame.config.state - action.target) hs hm reframe
  | right =>
    cases hr : frame.config.right with
    | cons next rightTail =>
      by_cases hle : action.target ≤ frame.config.state
      · have hs : frame.config.state = action.target +
            (frame.config.state - action.target) := by omega
        exact canonicalTailBuilder_rightInternalAtMost frame slot ready
          hruntime action hlookup hhalt next rightTail hr
          (frame.config.state - action.target) hs hm reframe
      · have ht : action.target = frame.config.state +
            (action.target - frame.config.state) := by omega
        exact canonicalTailBuilder_rightInternalAtLeast frame slot ready
          hruntime action hlookup hhalt next rightTail hr
          (action.target - frame.config.state) ht hm reframe
    | nil =>
      by_cases hlt : action.target < frame.config.state
      · have hs : frame.config.state = action.target +
            ((frame.config.state - action.target - 1) + 1) := by omega
        exact canonicalTailBuilder_rightBoundaryAtMost frame slot ready
          hruntime action hlookup hhalt hr
          (frame.config.state - action.target - 1) hs hm reframe
      · have ht : action.target = frame.config.state +
            (action.target - frame.config.state) := by omega
        exact canonicalTailBuilder_rightBoundaryAtLeast frame slot ready
          hruntime action hlookup hhalt hr
          (action.target - frame.config.state) ht hm reframe
  | left =>
    cases hl : frame.config.leftRev with
    | cons previous leftTail =>
      by_cases hle : action.target ≤ frame.config.state
      · have hs : frame.config.state = action.target +
            (frame.config.state - action.target) := by omega
        exact canonicalTailBuilder_leftInternalAtMost frame slot ready
          hruntime action hlookup hhalt previous leftTail hl
          (frame.config.state - action.target) hs hm reframe
      · have ht : action.target = frame.config.state +
            (action.target - frame.config.state) := by omega
        exact canonicalTailBuilder_leftInternalAtLeast frame slot ready
          hruntime action hlookup hhalt previous leftTail hl
          (action.target - frame.config.state) ht hm reframe
    | nil =>
      by_cases hlt : action.target < frame.config.state
      · have hs : frame.config.state = action.target +
            ((frame.config.state - action.target - 1) + 1) := by omega
        exact canonicalTailBuilder_leftBoundaryAtMost frame slot ready
          hruntime action hlookup hhalt hl
          (frame.config.state - action.target - 1) hs hm reframe
      · have ht : action.target = frame.config.state +
            (action.target - frame.config.state) := by omega
        exact canonicalTailBuilder_leftBoundaryAtLeast frame slot ready
          hruntime action hlookup hhalt hl
          (action.target - frame.config.state) ht hm reframe

theorem nonhalting_complete_cycle_bound
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix) (slot : Bool)
    (ready : ULogBootstrapExecution.FrameReady frame)
    (hruntime : ULogBootstrapExecution.PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (reframe : ULogBootstrapExecution.ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map
        ULogBootstrapExecution.payloadNat)
      (ULogBootstrapExecution.clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map
          ULogBootstrapExecution.payloadNat)
        frame.clockZeros frame.runtime))
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * (semanticFrameCursorRadius input frame) ^ 3 +
        23 * (semanticFrameCursorRadius input frame) ^ 2 +
          38 * semanticFrameCursorRadius input frame + 28 :=
  exactCycle_le_of_canonicalTailBuilder frame slot ready hruntime
    action hlookup reframe cycle
    (canonicalTailBuilder_all frame slot ready hruntime action hlookup
      hhalt reframe)

theorem nonhalting_complete_cycle_bound_of_radius_le
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix) (slot : Bool)
    (ready : ULogBootstrapExecution.FrameReady frame)
    (hruntime : ULogBootstrapExecution.PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (reframe : ULogBootstrapExecution.ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map
        ULogBootstrapExecution.payloadNat)
      (ULogBootstrapExecution.clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map
          ULogBootstrapExecution.payloadNat)
        frame.clockZeros frame.runtime))
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode)
    (R : Nat)
    (hR : semanticFrameCursorRadius input frame ≤ R) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by
  refine le_trans (nonhalting_complete_cycle_bound frame slot ready hruntime
    action hlookup hhalt reframe cycle) ?_
  set r := semanticFrameCursorRadius input frame
  have hsq : r ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hcu : r ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have h6 : 6 * r ^ 3 ≤ 6 * R ^ 3 := Nat.mul_le_mul_left 6 hcu
  have h23 : 23 * r ^ 2 ≤ 23 * R ^ 2 := Nat.mul_le_mul_left 23 hsq
  have h38 : 38 * r ≤ 38 * R := Nat.mul_le_mul_left 38 hR
  omega

end PakFixedPolyomino.ULogLocalTimeAllCycles
