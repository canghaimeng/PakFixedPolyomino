/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeStayGrowth

/-! Actual complete positive cycle time from a proved continuation.
The old excluded continuation file is preserved. This module reuses its
bounded-parts strategy with the repaired physical stay continuation. -/

namespace PakFixedPolyomino.ULogLocalTimeCycleBound

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution ULogBootstrapExecution
open PakULogCycleResourceBound PakULogNonterminalTailFuel PakULogTraceResourceBound
open ULogLocalTimeStayGrowth

theorem exactCycle_le_of_canonicalTailBuilder
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime))
    (cycle : ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode)
    (tailBuilder : CanonicalTailBuilder frame slot action reframe
      (semanticFrameCursorRadius input frame)) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * (semanticFrameCursorRadius input frame) ^ 3 +
        23 * (semanticFrameCursorRadius input frame) ^ 2 +
          38 * semanticFrameCursorRadius input frame + 28 := by
  let R := semanticFrameCursorRadius input frame
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, hactionRule⟩ :=
    automatic_lookup_some slot frame.config.state frame.config.focus
      ready.focus_lt_three
      (cursorDynamicProgramToHead input
        (frame.config.leftRev.map payloadNat))
      (clockCellsAfter (frame.config.right.map payloadNat)
        frame.clockZeros frame.runtime)
      hp hclock frame.config.program ready.reads_lt_three action hlookup
  let programToHead := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let cursorRuntime := clockCellsAfter
    (frame.config.right.map payloadNat) frame.clockZeros frame.runtime
  let spare : List Tape :=
    List.replicate (frame.capacity - frame.config.state)
      MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let actionStart := actionWriteStart r.action.write left
    (List.replicate r.action.target (ulogCore codeZero) ++
      ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead)
    (readHeadNat r.read)
    (cursorRuntime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: spare)
  obtain ⟨tailRun⟩ := tailBuilder skip r rs heq certs rscan hmatch
    hactionRule
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨cursorRun0⟩ :=
    mismatchCertificateList_matchedActionWrite_bounded_sharp slot
      frame.config.state frame.config.focus programToHead cursorRuntime
      frame.outer (ulogCore stateSep :: spare) skip r rs
      (by simpa [programToHead, cursorRuntime] using certs) hmatch
      rscan.read_valid hwrite hboundary
      (by simpa [programToHead, cursorRuntime, hmatch.2.1] using
        rscan.source_corridor)
      (by simpa [programToHead] using
        (matchedReadPath_safe r.slot r rs programToHead hp))
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) programToHead cursorRuntime
  have hCR : C = R := by
    dsimp [C, R, programToHead, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  let cursorStart := ruleCursorResult slot frame.config.state frame.config.focus
    (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
    programToHead cursorRuntime frame.outer (ulogCore stateSep :: spare)
  have cursorRun : BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18) +
        (6 * R ^ 2 + 11 * R + 13)) cursorStart actionStart :=
    { steps := by
        exact cursorRun0.steps
      le_bound := by
        calc
          cursorRun0.steps ≤ skip.length * (6 * C ^ 2 + 17 * C + 18) +
              (6 * C ^ 2 + 11 * C + 13) := cursorRun0.le_bound
          _ = skip.length * (6 * R ^ 2 + 17 * R + 18) +
              (6 * R ^ 2 + 11 * R + 13) :=
            congrArg (fun n : ℕ => skip.length * (6 * n ^ 2 + 17 * n + 18) +
              (6 * n ^ 2 + 11 * n + 13)) hCR
      run := by
        exact cursorRun0.run }
  have frameSize := semanticFrame_has_sizeEnvelope frame
  let choiceLeft := dynamicRuleReturnPath
    (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input ++
      ulogCore pcMark :: frame.outer
  let choiceRight := cursorRuntime ++
    List.replicate frame.config.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: spare
  obtain ⟨dynamic0⟩ := dynamicRuleSourceStarted_bounded_radius slot
    (frame.config.leftRev.map payloadNat) (payloadNatList_safe _)
    (skip ++ r :: rs) (by simp) input frame.outer
    (readHeadNat frame.config.focus)
    (cursorRuntime ++ List.replicate frame.config.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: spare)
    (by simpa [heq] using frameSize.dynamic_path_le)
    (by simpa [heq] using frameSize.rules_le)
  have hchoice0 := clockDecrementCells_firstChoice
    (readHeadNat frame.config.focus)
    (choiceHead_readHeadNat_of_lt_three frame.config.focus
      ready.focus_lt_three)
    frame.clockZeros (frame.config.right.map payloadNat)
    (payloadNatList_safe frame.config.right) choiceLeft
    (frame.runtime ++ List.replicate frame.config.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: spare)
  have hchoice : FirstValidZeroHit IsConcreteChoice frame.encode
      (.running .chooseSlot
        ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩) := by
    simpa [SemanticCycleFrame.encode, semanticCycleEncoding,
      clockCellsBefore, clockCellsAfter, stateWorkspace, choiceLeft,
      choiceRight, cursorRuntime, spare, heq, List.append_assoc] using hchoice0
  have hchoiceEq : cycle.choice =
      .running .chooseSlot
        ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩ :=
    cycle.choicePrefix.finish_unique hchoice
  have hselected : oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
            (skip ++ r :: rs) input)
          frame.outer (ulogCore pcMark)
          (readHeadNat frame.config.focus :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil
      (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath
        (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat frame.config.focus)
                (choiceHead_readHeadNat_of_lt_three frame.config.focus
                  ready.focus_lt_three)
                (xs ++ ulogCore pcMark :: frame.outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat frame.config.focus)
                (choiceHead_readHeadNat_of_lt_three frame.config.focus
                  ready.focus_lt_three)
                (xs ++ ulogCore pcMark :: frame.outer) x choiceRight
  have hbranch : cycle.branch =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
            (skip ++ r :: rs) input)
          frame.outer (ulogCore pcMark)
          (readHeadNat frame.config.focus :: choiceRight)) := by
    have hs := validStepAt_some_eq_oneStepAt cycle.selected
    rw [hchoiceEq, hselected] at hs
    exact hs.symm
  have heqStart := dynamicRuleSourceStarted_eq_cursorResult slot
    frame.config.state frame.config.focus
    (frame.config.leftRev.map payloadNat) input skip r rs cursorRuntime
    frame.outer (ulogCore stateSep :: spare)
  have dynamic : BoundedStopFreeRun (2 * R + 2) cycle.branch cursorStart :=
    { steps := dynamic0.steps
      le_bound := by simpa [R] using dynamic0.le_bound
      run := by
        rw [hbranch]
        rw [show cursorStart = dynamicRuleSourceStarted slot
          (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input
          frame.outer (readHeadNat frame.config.focus)
          (cursorRuntime ++ List.replicate frame.config.state
            (ulogCore stateZero) ++ ulogCore stateOne :: ulogCore stateSep ::
              spare) by exact heqStart.symm]
        simpa [choiceRight, cursorRuntime, List.append_assoc] using dynamic0.run }
  have hskip : 32 * skip.length ≤ R := by
    dsimp [R, semanticFrameCursorRadius]
    rw [heq]
    simp [encodeRules_append]
    omega
  have hchoiceBound := exactConcreteCycle_frame_choicePrefix_le_radius
    frame cycle ready.focus_lt_three frameSize.right_le frameSize.clock_le
  apply exactCycle_nonterminal_le_of_bounded_parts cycle
    (by dsimp [R, semanticFrameCursorRadius]; omega) hskip
    (by simpa [R] using hchoiceBound) dynamic rfl cursorRun
    (by exact tailRun)
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary,
      SemanticCycleFrame.encode, semanticCycleEncoding])

/-- Every actual complete state-growth stay cycle has the displayed literal
transition bound. Actual nonhalting, capacity and passive-runtime hypotheses
remain explicit; no other movement case or global frame count is asserted. -/
theorem stay_growth_cycle_le
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .stay)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime))
    (cycle : ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * (semanticFrameCursorRadius input frame) ^ 3 +
        23 * (semanticFrameCursorRadius input frame) ^ 2 +
          38 * semanticFrameCursorRadius input frame + 28 := by
  exact exactCycle_le_of_canonicalTailBuilder frame slot ready hruntime
    action hlookup reframe cycle
    (canonicalTailBuilder_stayAtLeast frame slot ready hruntime action
      hlookup hhalt growth htarget hmove reframe)

end PakFixedPolyomino.ULogLocalTimeCycleBound
