import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Exact first-hit nonhalting cycles from selected-slot local readiness.

`FrameReady` asks capacity/outer readiness of BOTH occupied slots. A raw
accepting physical path supplies only the selected branch, so the
unselected alternative may underflow. This module uses
`SelectedFrameReady` at one fixed slot and reuses the audited
`exactCycle_semanticLookupSome_*` constructors. Same physical
program/table/clock/capacity/outer/suffix. -/

namespace PakFixedPolyomino.ULogSelectedExactPositiveCycles
open ULogBootstrapExecution ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

/-- Local readiness of one selected slot. Capacity and outer hypotheses
quantify only over the actual lookup at this same `slot`. -/
structure SelectedFrameReady {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool) : Prop where
  runtime_passive : PassivePath frame.runtime
  focus_lt_three : frame.config.focus < 3
  program_nonempty : frame.config.program ≠ []
  reads_lt_three : ∀ r ∈ frame.config.program, r.read < 3
  writes_lt_three : ∀ r ∈ frame.config.program, r.action.write < 3
  state_le_capacity : frame.config.state ≤ frame.capacity
  capacity_ready : ∀ action,
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action →
      SemanticCapacityReady frame.config action frame.capacity
  outer_ready : ∀ action,
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action →
      SemanticOuterReady frame.config action frame.outer

theorem SelectedFrameReady.ofFrameReady
    {input : List Bool} {suffix : List Tape}
    {frame : SemanticCycleFrame input suffix} (slot : Bool)
    (ready : FrameReady frame) : SelectedFrameReady frame slot where
  runtime_passive := ready.runtime_passive
  focus_lt_three := ready.focus_lt_three
  program_nonempty := ready.program_nonempty
  reads_lt_three := ready.reads_lt_three
  writes_lt_three := ready.writes_lt_three
  state_le_capacity := ready.state_le_capacity
  capacity_ready := fun action hlookup => ready.capacity_ready slot action hlookup
  outer_ready := fun action hlookup => ready.outer_ready slot action hlookup

theorem selected_target_ge_two
    {c : ULogSemantics.Config} {action : ULogBytecode.ActionCode}
    {next : ULogSemantics.Config}
    (haction : ULogSemantics.applyAction c action = next)
    (hhalt : ULogSemantics.halted next = false) :
    2 ≤ action.target := by
  have hnot : ¬ ULogSemantics.halted
      (ULogSemantics.applyAction c action) = true := by
    intro hterminal
    rw [haction, hhalt] at hterminal
    contradiction
  have hnlt : ¬ action.target < 2 := fun ht =>
    hnot ((halted_applyAction_iff_target_lt_two c action).mpr ht)
  omega

/-- Compact 10-case first-hit dispatcher. Stay / internal / boundary
branches split by move, emptiness of the travelled tape, and
shrink versus growth of the target. -/
noncomputable def selected_exact_positive_cycle
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config)
    (ready : SelectedFrameReady frame slot)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = next)
    (hhalt : ULogSemantics.halted next = false)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower := selected_target_ge_two haction hhalt
  have hruntime := ready.runtime_passive
  cases hmove : action.move with
  | stay =>
      by_cases htarget : action.target < frame.config.state
      · let extra := frame.config.state - action.target - 1
        have hstate :
            frame.config.state = action.target + (extra + 1) := by
          dsimp [extra]; omega
        let hcycle := Classical.choice
          (exactCycle_semanticLookupSome_stayAtMost
            frame.config slot action hlookup input frame.clockZeros
            frame.capacity frame.runtime frame.outer suffix hruntime
            ready.focus_lt_three ready.reads_lt_three ready.writes_lt_three
            (extra + 1) hstate ready.state_le_capacity htargetLower hmove)
        have hreframe := reframe.eq_before
        simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
          semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
          using hcycle
      · let growth := action.target - frame.config.state
        have htargetEq :
            action.target = frame.config.state + growth := by
          dsimp [growth]; omega
        have hcapacity : action.target ≤ frame.capacity := by
          simpa [SemanticCapacityReady, hmove] using
            ready.capacity_ready action hlookup
        let hcycle := Classical.choice
          (exactCycle_semanticLookupSome_stayAtLeast
            frame.config slot action hlookup input frame.clockZeros
            frame.capacity frame.runtime frame.outer suffix hruntime
            ready.focus_lt_three ready.reads_lt_three ready.writes_lt_three
            growth htargetEq hcapacity htargetLower hmove)
        have hreframe := reframe.eq_before
        simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
          semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
          using hcycle
  | right =>
      cases hright : frame.config.right with
      | nil =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]; omega
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_rightBoundaryAtMost
                frame.config slot action hlookup hright input
                frame.clockZeros frame.capacity frame.runtime frame.outer
                suffix hruntime ready.focus_lt_three ready.reads_lt_three
                ready.writes_lt_three extra hstate ready.state_le_capacity
                htargetLower hmove)
            have hreframeNil :
                clockCellsBefore [] reframe.zeros reframe.runtime =
                  clockCellsAfter [] frame.clockZeros frame.runtime := by
              simpa [ULogSemantics.applyAction, hmove, hright] using
                reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter,
              ULogSemantics.applyAction, hmove, hright, hreframeNil]
              using hcycle
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]; omega
            have hcapacity : action.target < frame.capacity := by
              simpa [SemanticCapacityReady, hmove, hright] using
                ready.capacity_ready action hlookup
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_rightBoundaryAtLeast
                frame.config slot action hlookup hright input
                frame.clockZeros frame.capacity frame.runtime frame.outer
                suffix hruntime ready.focus_lt_three ready.reads_lt_three
                ready.writes_lt_three growth htargetEq hcapacity
                htargetLower hmove)
            have hreframeNil :
                clockCellsBefore [] reframe.zeros reframe.runtime =
                  clockCellsAfter [] frame.clockZeros frame.runtime := by
              simpa [ULogSemantics.applyAction, hmove, hright] using
                reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter,
              ULogSemantics.applyAction, hmove, hright, hreframeNil]
              using hcycle
      | cons nextCell rightTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]; omega
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_rightInternalAtMost
                frame.config slot action hlookup nextCell rightTail hright
                input frame.clockZeros frame.capacity frame.runtime
                frame.outer suffix hruntime ready.focus_lt_three
                ready.reads_lt_three ready.writes_lt_three (extra + 1)
                hstate ready.state_le_capacity htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hright,
              hreframe] using hcycle
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]; omega
            have hcapacity : action.target ≤ frame.capacity := by
              simpa [SemanticCapacityReady, hmove, hright] using
                ready.capacity_ready action hlookup
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_rightInternalAtLeast
                frame.config slot action hlookup nextCell rightTail hright
                input frame.clockZeros frame.capacity frame.runtime
                frame.outer suffix hruntime ready.focus_lt_three
                ready.reads_lt_three ready.writes_lt_three growth htargetEq
                hcapacity htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hright,
              hreframe] using hcycle
  | left =>
      cases hleft : frame.config.leftRev with
      | nil =>
          have hex : ∃ tail,
              frame.outer = MStarConcreteAlphabet.work :: tail := by
            simpa [SemanticOuterReady, hmove, hleft] using
              ready.outer_ready action hlookup
          let outerTail := Classical.choose hex
          have houter : frame.outer =
              MStarConcreteAlphabet.work :: outerTail :=
            Classical.choose_spec hex
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]; omega
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_leftBoundaryAtMost
                frame.config slot action hlookup hleft input
                frame.clockZeros frame.capacity frame.runtime outerTail
                suffix hruntime ready.focus_lt_three ready.reads_lt_three
                ready.writes_lt_three extra hstate ready.state_le_capacity
                htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
              houter, hreframe] using hcycle
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]; omega
            have hcapacity : action.target ≤ frame.capacity := by
              simpa [SemanticCapacityReady, hmove] using
                ready.capacity_ready action hlookup
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_leftBoundaryAtLeast
                frame.config slot action hlookup hleft input
                frame.clockZeros frame.capacity frame.runtime outerTail
                suffix hruntime ready.focus_lt_three ready.reads_lt_three
                ready.writes_lt_three growth htargetEq hcapacity
                htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
              houter, hreframe] using hcycle
      | cons nextCell leftTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]; omega
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_leftInternalAtMost
                frame.config slot action hlookup nextCell leftTail hleft
                input frame.clockZeros frame.capacity frame.runtime
                frame.outer suffix hruntime ready.focus_lt_three
                ready.reads_lt_three ready.writes_lt_three (extra + 1)
                hstate ready.state_le_capacity htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
              hreframe] using hcycle
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]; omega
            have hcapacity : action.target ≤ frame.capacity := by
              simpa [SemanticCapacityReady, hmove, hleft] using
                ready.capacity_ready action hlookup
            let hcycle := Classical.choice
              (exactCycle_semanticLookupSome_leftInternalAtLeast
                frame.config slot action hlookup nextCell leftTail hleft
                input frame.clockZeros frame.capacity frame.runtime
                frame.outer suffix hruntime ready.focus_lt_three
                ready.reads_lt_three ready.writes_lt_three growth htargetEq
                hcapacity htargetLower hmove)
            have hreframe := reframe.eq_before
            simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
              semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
              hreframe] using hcycle

/-- Internally construct the selected-slot exact continuation: lookup the
actual action, reframe the positive binary clock, and realize the
first-hit cycle. No continuation certificate is supplied. -/
noncomputable def selected_positive_continuation
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (budget : Nat)
    (ready : SelectedFrameReady frame slot)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (hhalt : ULogSemantics.halted next = false) :
    ExactPositiveResourceContinuation frame slot next (budget - 1) := by
  let actionWitness := Classical.indefiniteDescription _
    (ULogSemantics.stepSlot_some_rule hstep).2
  let action := actionWitness.1
  have hlookup : ULogBytecode.lookupRule frame.config.program
      frame.config.state frame.config.focus slot = some action :=
    actionWitness.2.1
  have haction : ULogSemantics.applyAction frame.config action = next :=
    actionWitness.2.2
  have hafter :=
    decodeBinaryClock_after_eq_pred frame.clockZeros frame.runtime budget
      hclock
  let reframeWitness := Classical.indefiniteDescription _
    (exists_clockReframe_of_positive_binaryClock
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime ready.runtime_passive
      (budget - 1) hafter (by omega))
  let reframe := reframeWitness.1
  exact
    { action := action
      reframe := reframe
      lookup := hlookup
      action_eq := haction
      clock_decoded := reframeWitness.2
      exact_cycle := selected_exact_positive_cycle frame slot next ready
        action hlookup haction hhalt reframe }

/-- Public checked target: a selected-slot nonhalting step with a genuine
positive decoded clock yields a nonempty exact resource continuation. -/
theorem selected_positive_continuation_spec
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (budget : Nat)
    (ready : SelectedFrameReady frame slot)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (hhalt : ULogSemantics.halted next = false) :
    Nonempty (ExactPositiveResourceContinuation frame slot next
      (budget - 1)) :=
  ⟨selected_positive_continuation frame slot next budget ready hclock
    hbudget hstep hhalt⟩

end PakFixedPolyomino.ULogSelectedExactPositiveCycles
