/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeStayGrowth

/-! One repaired right-boundary state-decrease continuation. Actual
nonhalting supplies the target lower bound; the encoded corridor supplies
its radius. This boundary step consumes one actual workspace cell; state capacity
is reduced accordingly. Other movement branches remain open. -/

namespace PakFixedPolyomino.ULogLocalTimeRightBoundary

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution ULogBootstrapExecution
open PakULogCycleResourceBound PakULogNonterminalTailFuel PakULogTraceResourceBound
open PakULogContinuationResourceGeometry
open ULogLocalTimeStayGrowth

theorem canonicalTailBuilder_rightBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (hright : frame.config.right = [])
    (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    CanonicalTailBuilder frame slot action reframe
      (semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let programToHead := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let boundary := clockBoundaryAfter frame.clockZeros
  let runtimeTail := clockTailAfter frame.clockZeros frame.runtime
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let spare : List Tape := List.replicate
    (frame.capacity - frame.config.state) MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) programToHead cursorRuntime
  have hclockDecomp : cursorRuntime = boundary :: runtimeTail := by
    dsimp [cursorRuntime, boundary, runtimeTail]
    rw [hright]
    exact clockCellsAfter_nil_decompose frame.clockZeros frame.runtime
  have hCR : C = semanticFrameCursorRadius input frame := by
    dsimp [C, programToHead, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have htailSafe := clockTailAfter_passive frame.clockZeros frame.runtime hruntime
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htarget : r.source = r.action.target + (extra + 1) := by
    rw [hactionRule]
    exact hmatch.1.trans hstate
  have hmoveRule : r.action.move = .right := by rw [hactionRule]; exact hmove
  have htargetLower : 2 ≤ r.action.target := by
    rw [hactionRule]
    exact nonhalting_action_target frame.config action hhalt
  have radius := matchedTargetZeroWithin_canonicalBudget
    frame.config.state frame.config.focus [] skip r rs programToHead cursorRuntime
  have hdecomp := matchedCursor_cleanup_decomposition slot frame.config.state
    frame.config.focus programToHead cursorRuntime skip r rs
    (mismatchCertificateList_initial_trace slot frame.config.state
      frame.config.focus programToHead cursorRuntime certs (by simp)) frame.outer
  obtain ⟨tail0⟩ := matchedAtMost_rightBoundary_tail_bounded_radius
    (R := C) r.action.write r.action.target extra hwrite htargetLower
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs)) (cursorCleanupTerminal skip)
    boundary frame.outer runtimeTail spare left (readHeadNat r.read)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (by simpa [hmoveRule] using matchedWritePath_safe r rs programToHead hp)
    (by simpa [hmoveRule, hclockDecomp] using
      matchedTargetPath_safe r hwrite rs programToHead cursorRuntime hp hclock)
    (by simpa [left, final, hmoveRule, List.append_assoc] using hdecomp)
    (passivePath_move (cursorMatchedMovePath_passive rs programToHead hp))
    (clockBoundaryAfter_valid frame.clockZeros)
    (matchedRightBoundary_shift_safe runtimeTail htailSafe r.action.target)
    (matchedRightBoundary_return_safe boundary
      (clockBoundaryAfter_valid frame.clockZeros) runtimeTail htailSafe
      r.action.target)
    (by
      have hc := matchedCleanupClock_rightInternal_safe skip r rs
        programToHead hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank] using hc)
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip)
    (matchedCleanupProgram_appendUnhead_safe skip r rs programToHead hp)
    (by
      have hb := radius.read_corridor_le
      show (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++
          cursorMatchedMovePath rs programToHead).length ≤ C
      simp [encodedActionPath, hmoveRule, moveBits] at hb ⊢
      omega)
    (by
      show (moveBits .right ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: boundary :: runtimeTail).length ≤ C
      simpa [C, hmoveRule, hclockDecomp] using radius.target_corridor_le)
    (by rw [← htarget]; exact radius.source_le)
    (by
      have hcp := cursorCleanupProgramPrefix_length_le skip r
      dsimp [C, canonicalMismatchBudget]
      simp [encodeRules_append, ULogBytecode.encodeRules] at hcp ⊢
      omega)
    (by
      dsimp [C, canonicalMismatchBudget, programToHead]
      simp [cursorMatchedMovePath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
    (by
      dsimp [C, canonicalMismatchBudget]
      simp [cursorCleanupPcPath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
    (by
      have ht : r.action.target ≤ frame.config.state := by
        rw [← hmatch.1]
        omega
      have hlen : cursorRuntime.length = runtimeTail.length + 1 := by
        simp only [hclockDecomp, List.length_cons]
      dsimp [C, canonicalMismatchBudget]
      simp only [List.nil_append, encodeRules_append,
        ULogBytecode.encodeRules, List.length_append, List.length_cons,
        List.length_replicate, List.length_singleton, List.length_nil]
      omega)
  have hprogramRestored : programToHead.map restoreProgramCell =
      programToHead := cursorDynamicProgramToHead_restored input
        (frame.config.leftRev.map payloadNat) (payloadNatList_safe _)
  have hclean := cleanedCursorCycleLeft_eq skip r rs programToHead
    frame.outer hprogramRestored
  have hcleanDyn := hclean.trans (canonicalCursorCycleLeft_dynamic
    (skip ++ r :: rs) input (frame.config.leftRev.map payloadNat) frame.outer)
  have hleftOut :
      restoreProgramCell (unheadTape (writeHeadNat r.action.write)) ::
          (cursorMatchedMovePath rs programToHead).reverse.map restoreProgramCell ++
            (cursorCleanupProgramPrefix skip r).reverse.map restoreProgramCell ++
              ulogCore codeOne ::
                (cursorCleanupPcPath skip (r :: rs)).reverse.map restorePcCell ++
                  ulogCore pcMark :: frame.outer =
        dynamicRuleReturnPath
            ((r.action.write :: frame.config.leftRev).map payloadNat)
            (skip ++ r :: rs) input ++ ulogCore pcMark :: frame.outer := by
    rw [unhead_writeHeadNat,
      restoreProgramCell_payloadCell _ (payloadNat_safe _)]
    simpa [cleanedCycleLeft, programToHead, dynamicRuleReturnPath,
      List.reverse_append, List.map_append, List.append_assoc,
      List.cons_append] using congrArg
        (fun xs => payloadNat r.action.write :: xs) hcleanDyn
  have hsum : extra + (frame.capacity - frame.config.state) =
      (frame.capacity - 1) - r.action.target := by
    have hcap := ready.state_le_capacity
    have hs : frame.config.state = r.action.target + (extra + 1) := by
      rw [hactionRule]; exact hstate
    omega
  have hwork : List.replicate extra MStarConcreteAlphabet.work ++ spare =
      List.replicate ((frame.capacity - 1) - r.action.target)
        MStarConcreteAlphabet.work ++ suffix := by
    dsimp [spare]
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hout := congrArg
    (fun ws => cursorRuntime ++
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hreframeRight :
      clockCellsBefore [] reframe.zeros reframe.runtime = cursorRuntime := by
    simpa [hmove, hright, ULogSemantics.applyAction, cursorRuntime] using
      reframe.eq_before
  refine ⟨
    { steps := tail0.steps
      le_bound := ?_
      run := ?_ }⟩
  · calc
      tail0.steps ≤ 16 * (C + 1) ^ 2 := tail0.le_bound
      _ = 16 * (semanticFrameCursorRadius input frame + 1) ^ 2 :=
        congrArg (fun n => 16 * (n + 1) ^ 2) hCR
      _ ≤ 24 * (semanticFrameCursorRadius input frame + 1) ^ 2 := by
        nlinarith
  · convert tail0.run using 1
    · simp only [left, final, programToHead, ← hclockDecomp, spare,
        htarget, hmoveRule, List.append_assoc, List.cons_append]
      rfl
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hmove, hright,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction,
        ULogSemantics.blankCode, readHeadNat, hreframeRight, heq,
        List.append_assoc, List.cons_append]
      dsimp [stateWorkspace]
      simpa only [hclockDecomp, List.append_assoc, List.cons_append] using hout.symm

theorem canonicalTailBuilder_rightBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (hright : frame.config.right = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    CanonicalTailBuilder frame slot action reframe
      (semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let programToHead := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let boundary := clockBoundaryAfter frame.clockZeros
  let runtimeTail := clockTailAfter frame.clockZeros frame.runtime
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let sourceSpare : List Tape := List.replicate
    (frame.capacity - frame.config.state) MStarConcreteAlphabet.work ++ suffix
  let targetSpare : List Tape := List.replicate
    ((frame.capacity - 1) - r.action.target) MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) programToHead cursorRuntime
  have hclockDecomp : cursorRuntime = boundary :: runtimeTail := by
    dsimp [cursorRuntime, boundary, runtimeTail]
    rw [hright]
    exact clockCellsAfter_nil_decompose frame.clockZeros frame.runtime
  have hCR : C = semanticFrameCursorRadius input frame := by
    dsimp [C, programToHead, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have htailSafe := clockTailAfter_passive frame.clockZeros frame.runtime hruntime
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htargetRule : r.action.target = r.source + growth := by
    rw [hmatch.1, hactionRule]
    exact htarget
  have hmoveRule : r.action.move = .right := by rw [hactionRule]; exact hmove
  have htargetLower : 2 ≤ r.action.target := by
    rw [hactionRule]
    exact nonhalting_action_target frame.config action hhalt
  have hcapacity : r.action.target < frame.capacity := by
    simpa [SemanticCapacityReady, hactionRule, hmove, hright] using ready.capacity_ready slot action hlookup
  have radius := matchedTargetZeroWithin_canonicalBudget
    frame.config.state frame.config.focus [] skip r rs programToHead cursorRuntime
  have hdecomp := matchedCursor_cleanup_decomposition slot frame.config.state
    frame.config.focus programToHead cursorRuntime skip r rs
    (mismatchCertificateList_initial_trace slot frame.config.state
      frame.config.focus programToHead cursorRuntime certs (by simp)) frame.outer
  obtain ⟨tail0⟩ := matchedAtLeast_rightBoundary_tail_bounded_radius
    (R := C) r.action.write r.source growth hwrite
      (by simpa only [htargetRule] using htargetLower)
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs)) (cursorCleanupTerminal skip)
    boundary frame.outer runtimeTail targetSpare left (readHeadNat r.read)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (by simpa [htargetRule, hmoveRule] using
      matchedWritePath_safe r rs programToHead hp)
    (by simpa [hmoveRule, hclockDecomp] using
      matchedTargetPath_safe r hwrite rs programToHead cursorRuntime hp hclock)
    (by simpa [left, final, htargetRule, hmoveRule,
      List.append_assoc] using hdecomp)
    (passivePath_move (cursorMatchedMovePath_passive rs programToHead hp))
    (clockBoundaryAfter_valid frame.clockZeros)
    (matchedRightBoundary_shift_safe runtimeTail htailSafe (r.source + growth))
    (matchedRightBoundary_return_safe boundary
      (clockBoundaryAfter_valid frame.clockZeros) runtimeTail htailSafe
      (r.source + growth))
    (by
      have hc := matchedCleanupClock_rightInternal_safe skip r rs
        programToHead hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank] using hc)
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip)
    (matchedCleanupProgram_appendUnhead_safe skip r rs programToHead hp)
    (by
      have hb := radius.read_corridor_le
      show (List.replicate (r.source + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++
          cursorMatchedMovePath rs programToHead).length ≤ C
      simp [encodedActionPath, htargetRule, hmoveRule, moveBits] at hb ⊢
      omega)
    (by
      show (moveBits .right ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: boundary :: runtimeTail).length ≤ C
      simpa [C, hmoveRule, hclockDecomp] using radius.target_corridor_le)
    (by rw [← htargetRule]; exact matched_radius_target_le radius)
    (by
      have hcp := cursorCleanupProgramPrefix_length_le skip r
      dsimp [C, canonicalMismatchBudget]
      simp [encodeRules_append, ULogBytecode.encodeRules] at hcp ⊢
      omega)
    (by
      dsimp [C, canonicalMismatchBudget, programToHead]
      simp [cursorMatchedMovePath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
    (by
      dsimp [C, canonicalMismatchBudget]
      simp [cursorCleanupPcPath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
    (by
      have ht : r.action.target ≤ (ULogBytecode.encodeRule r).length := by
        simp [ULogBytecode.encodeRule, ULogBytecode.encodeAction]
        omega
      have hlen : cursorRuntime.length = runtimeTail.length + 1 := by
        simp only [hclockDecomp, List.length_cons]
      dsimp [C, canonicalMismatchBudget]
      simp only [List.nil_append, encodeRules_append,
        ULogBytecode.encodeRules, List.length_append, List.length_cons,
        List.length_replicate, List.length_singleton, List.length_nil]
      omega)
  have hsum : frame.capacity - frame.config.state = growth + 1 +
      ((frame.capacity - 1) - r.action.target) := by
    have ht : r.action.target = frame.config.state + growth := by
      rw [hactionRule]; exact htarget
    omega
  have hsourceSpare : sourceSpare =
      List.replicate growth MStarConcreteAlphabet.work ++
        MStarConcreteAlphabet.work :: targetSpare := by
    dsimp [sourceSpare, targetSpare]
    rw [hsum, List.replicate_add, List.replicate_add]
    simp only [List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append, List.replicate_zero]
  dsimp only [sourceSpare, targetSpare] at hsourceSpare
  have hprogramRestored : programToHead.map restoreProgramCell =
      programToHead := cursorDynamicProgramToHead_restored input
        (frame.config.leftRev.map payloadNat) (payloadNatList_safe _)
  have hclean := cleanedCursorCycleLeft_eq skip r rs programToHead
    frame.outer hprogramRestored
  have hcleanDyn := hclean.trans (canonicalCursorCycleLeft_dynamic
    (skip ++ r :: rs) input (frame.config.leftRev.map payloadNat) frame.outer)
  have hleftOut :
      restoreProgramCell (unheadTape (writeHeadNat r.action.write)) ::
          (cursorMatchedMovePath rs programToHead).reverse.map restoreProgramCell ++
            (cursorCleanupProgramPrefix skip r).reverse.map restoreProgramCell ++
              ulogCore codeOne ::
                (cursorCleanupPcPath skip (r :: rs)).reverse.map restorePcCell ++
                  ulogCore pcMark :: frame.outer =
        dynamicRuleReturnPath
            ((r.action.write :: frame.config.leftRev).map payloadNat)
            (skip ++ r :: rs) input ++ ulogCore pcMark :: frame.outer := by
    rw [unhead_writeHeadNat,
      restoreProgramCell_payloadCell _ (payloadNat_safe _)]
    simpa [cleanedCycleLeft, programToHead, dynamicRuleReturnPath,
      List.reverse_append, List.map_append, List.append_assoc,
      List.cons_append] using congrArg
        (fun xs => payloadNat r.action.write :: xs) hcleanDyn
  have hworkspace :
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: targetSpare =
      stateWorkspace (frame.capacity - 1) r.action.target suffix := by
    simp only [targetSpare, stateWorkspace, List.append_assoc, List.cons_append]
  have hreframeRight :
      clockCellsBefore [] reframe.zeros reframe.runtime = cursorRuntime := by
    simpa [hmove, hright, ULogSemantics.applyAction, cursorRuntime] using
      reframe.eq_before
  refine ⟨
    { steps := tail0.steps
      le_bound := ?_
      run := ?_ }⟩
  · calc
      tail0.steps ≤ 20 * (C + 1) ^ 2 := tail0.le_bound
      _ = 20 * (semanticFrameCursorRadius input frame + 1) ^ 2 :=
        congrArg (fun n => 20 * (n + 1) ^ 2) hCR
      _ ≤ 24 * (semanticFrameCursorRadius input frame + 1) ^ 2 := by
        nlinarith
  · convert tail0.run using 1
    · simp only [left, final, programToHead, ← hclockDecomp,
        hsourceSpare, targetSpare, htargetRule, hmoveRule, List.append_assoc, List.cons_append]
      rfl
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hmove, hright,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction,
        ULogSemantics.blankCode, readHeadNat, hreframeRight, hworkspace,
        heq, List.append_assoc, List.cons_append]
      simpa only [hclockDecomp, htargetRule, List.append_assoc, List.cons_append] using
        congrArg (fun xs => cursorRuntime ++ xs) hworkspace.symm

end PakFixedPolyomino.ULogLocalTimeRightBoundary
