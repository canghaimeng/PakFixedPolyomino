/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeStayGrowth

/-! Repaired left-boundary continuations for both state directions. Actual
nonhalting supplies the target lower bound; the encoded corridor supplies
its radius. The full cleanup restores the boundary cell and consumes one
outer work cell. Global resources and the original counting theorem remain open. -/

namespace PakFixedPolyomino.ULogLocalTimeLeftBoundary

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution ULogBootstrapExecution
open PakULogCycleResourceBound PakULogNonterminalTailFuel PakULogTraceResourceBound
open PakULogContinuationResourceGeometry
open ULogLocalTimeStayGrowth

theorem canonicalTailBuilder_leftBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (hleft : frame.config.leftRev = []) (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    CanonicalTailBuilder frame slot action reframe
      (semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let fullProgram := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let tailProgram := leftBoundaryScanPrefix input
  let boundary := leftBoundaryMarker input
  let scanPrefix := cursorMatchedMovePath rs tailProgram
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let spare : List Tape := List.replicate
    (frame.capacity - frame.config.state) MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  have houterReady := ready.outer_ready slot action hlookup
  obtain ⟨outerTail, houter⟩ : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) fullProgram cursorRuntime
  have hsplit : fullProgram = tailProgram ++ [boundary] := by
    simpa [fullProgram, tailProgram, boundary, hleft] using
      cursorDynamicProgramToHead_emptyLeft_split input
  have hscanSplit : cursorMatchedMovePath rs fullProgram =
      scanPrefix ++ [boundary] := by
    simp [scanPrefix, cursorMatchedMovePath, hsplit, List.append_assoc]
  have hCR : C = semanticFrameCursorRadius input frame := by
    dsimp [C, fullProgram, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hpTail := leftBoundaryScanPrefix_passive input
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htarget : r.source = r.action.target + (extra + 1) := by
    rw [hactionRule]
    exact hmatch.1.trans hstate
  have hmoveRule : r.action.move = .left := by rw [hactionRule]; exact hmove
  have htargetLower : 2 ≤ r.action.target := by
    rw [hactionRule]
    exact nonhalting_action_target frame.config action hhalt
  have radius := matchedTargetZeroWithin_canonicalBudget
    frame.config.state frame.config.focus [] skip r rs fullProgram cursorRuntime
  have hdecomp := matchedCursor_cleanup_decomposition slot frame.config.state
    frame.config.focus fullProgram cursorRuntime skip r rs
    (mismatchCertificateList_initial_trace slot frame.config.state
      frame.config.focus fullProgram cursorRuntime certs (by simp)) frame.outer
  obtain ⟨tail0⟩ := matchedAtMost_leftBoundary_tail_bounded_radius
    (R := C) r.action.write r.action.target extra hwrite htargetLower
    (cursorCleanupProgramPrefix skip r) scanPrefix
    (cursorCleanupPcPath skip (r :: rs)) (cursorCleanupTerminal skip)
    boundary outerTail cursorRuntime spare left (readHeadNat r.read)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (by simpa [hmoveRule, hscanSplit] using
      matchedWritePath_safe r rs fullProgram hp)
    (by simpa [hmoveRule, hscanSplit, List.append_assoc] using
      matchedTargetPath_safe r hwrite rs fullProgram cursorRuntime hp hclock)
    (by simpa [left, final, hmoveRule, hscanSplit, houter,
      List.append_assoc] using hdecomp)
    (by simpa [hscanSplit] using
      passivePath_move (cursorMatchedMovePath_passive rs fullProgram hp))
    (leftBoundaryMarker_valid input)
    (matchedLeftBoundary_shift_safe_general skip r rs tailProgram hpTail)
    (matchedLeftBoundary_return_safe_general skip r rs tailProgram hpTail
      boundary (leftBoundaryMarker_passive input))
    (by
      have hc := matchedCleanupClock_leftInternal_safe skip r rs fullProgram
        hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank, hscanSplit, List.append_assoc] using hc)
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip)
    (by simpa [hscanSplit, boundary] using
      cursorCleanupProgramPath_restoreHeadSafe skip r rs fullProgram hp)
    (by
      have hb := radius.read_corridor_le
      show (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [boundary]).length
          ≤ C
      simp [encodedActionPath, hmoveRule, hscanSplit, moveBits,
        List.append_assoc] at hb ⊢
      omega)
    (by
      show (moveBits .left ++ scanPrefix ++ [boundary] ++
        writeHeadNat r.action.write :: cursorRuntime).length ≤ C
      simpa [hmoveRule, hscanSplit, List.append_assoc] using
        radius.target_corridor_le)
    (by rw [← htarget]; exact radius.source_le)
    (by
      have hcp := cursorCleanupProgramPrefix_length_le skip r
      dsimp [C, canonicalMismatchBudget]
      simp [encodeRules_append, ULogBytecode.encodeRules] at hcp ⊢
      omega)
    (by
      have hlen : scanPrefix.length ≤
          (cursorMatchedMovePath rs fullProgram).length := by simp [hscanSplit]
      have hfullScan : (cursorMatchedMovePath rs fullProgram).length ≤ C := by
        dsimp [C, canonicalMismatchBudget]
        simp [cursorMatchedMovePath, encodeRules_append, ULogBytecode.encodeRules]
        omega
      exact Nat.le_trans hlen hfullScan)
    (by
      dsimp [C, canonicalMismatchBudget]
      simp [cursorCleanupPcPath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
  have hprogramRestored : fullProgram.map restoreProgramCell = fullProgram :=
    cursorDynamicProgramToHead_restored input
      (frame.config.leftRev.map payloadNat) (payloadNatList_safe _)
  have hclean := cleanedCursorCycleLeft_eq skip r rs fullProgram outerTail
    hprogramRestored
  have hcleanDyn := hclean.trans (canonicalCursorCycleLeft_dynamic
    (skip ++ r :: rs) input (frame.config.leftRev.map payloadNat) outerTail)
  have hleftOut :
      restoreProgramCell boundary :: scanPrefix.reverse.map restoreProgramCell ++
          (cursorCleanupProgramPrefix skip r).reverse.map restoreProgramCell ++
        ulogCore codeOne ::
          (cursorCleanupPcPath skip (r :: rs)).reverse.map restorePcCell ++
            ulogCore pcMark :: outerTail =
      dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
          (skip ++ r :: rs) input ++ ulogCore pcMark :: outerTail := by
    simpa [cleanedCycleLeft, hscanSplit, List.reverse_append, List.map_append,
      List.append_assoc] using hcleanDyn
  have hsum : extra + 1 + (frame.capacity - frame.config.state) =
      frame.capacity - r.action.target := by
    have hcap := ready.state_le_capacity
    have hs : frame.config.state = r.action.target + (extra + 1) := by
      rw [hactionRule]; exact hstate
    omega
  have hwork : List.replicate (extra + 1) MStarConcreteAlphabet.work ++
      spare = List.replicate (frame.capacity - r.action.target)
        MStarConcreteAlphabet.work ++ suffix := by
    dsimp [spare]
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hout := congrArg
    (fun ws => unheadTape (writeHeadNat r.action.write) :: cursorRuntime ++
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hclockCons :
      clockCellsAfter
        (payloadNat r.action.write :: frame.config.right.map payloadNat)
        frame.clockZeros frame.runtime =
      payloadNat r.action.write :: cursorRuntime := by
    dsimp [cursorRuntime]
    simp [clockCellsAfter, List.cons_append]
  have hnewRight :
      (ULogSemantics.applyAction frame.config action).right =
        action.write :: frame.config.right := by
    simp [ULogSemantics.applyAction, hmove, hleft]
  have hreframeLeft :
      clockCellsBefore
        (payloadNat r.action.write :: frame.config.right.map payloadNat)
        reframe.zeros reframe.runtime =
      payloadNat r.action.write :: cursorRuntime := by
    have hnew :
        (ULogSemantics.applyAction frame.config action).right.map payloadNat =
          payloadNat r.action.write :: frame.config.right.map payloadNat := by
      rw [hnewRight, ← hactionRule]
      simp only [List.map_cons]
    rw [← hnew, reframe.eq_before, hnew, hclockCons]
  refine ⟨⟨tail0.steps, ?_, ?_⟩⟩
  · calc
      tail0.steps ≤ 20 * (C + 1) ^ 2 := tail0.le_bound
      _ = 20 * (semanticFrameCursorRadius input frame + 1) ^ 2 :=
        congrArg (fun n => 20 * (n + 1) ^ 2) hCR
      _ ≤ 24 * (semanticFrameCursorRadius input frame + 1) ^ 2 := by
        nlinarith
  · convert tail0.run using 1
    · simp only [left, final, fullProgram, htarget, hmoveRule, hscanSplit,
        houter, List.append_assoc, List.cons_append]
      rfl
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction,
        ULogSemantics.blankCode, readHeadNat, heq, List.append_assoc]
      rw [hreframeLeft]
      simp only [payloadNat, List.cons_append]
      dsimp [stateWorkspace]
      simpa only [unhead_writeHeadNat, payloadNat, readHeadNat, List.append_assoc,
        List.cons_append] using hout.symm

theorem canonicalTailBuilder_leftBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (hleft : frame.config.leftRev = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    CanonicalTailBuilder frame slot action reframe
      (semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let fullProgram := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let tailProgram := leftBoundaryScanPrefix input
  let boundary := leftBoundaryMarker input
  let scanPrefix := cursorMatchedMovePath rs tailProgram
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let sourceSpare : List Tape := List.replicate
    (frame.capacity - frame.config.state) MStarConcreteAlphabet.work ++ suffix
  let targetSpare : List Tape := List.replicate
    (frame.capacity - r.action.target) MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  have houterReady := ready.outer_ready slot action hlookup
  obtain ⟨outerTail, houter⟩ : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) fullProgram cursorRuntime
  have hsplit : fullProgram = tailProgram ++ [boundary] := by
    simpa [fullProgram, tailProgram, boundary, hleft] using
      cursorDynamicProgramToHead_emptyLeft_split input
  have hscanSplit : cursorMatchedMovePath rs fullProgram =
      scanPrefix ++ [boundary] := by
    simp [scanPrefix, cursorMatchedMovePath, hsplit, List.append_assoc]
  have hCR : C = semanticFrameCursorRadius input frame := by
    dsimp [C, fullProgram, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hpTail := leftBoundaryScanPrefix_passive input
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htargetRule : r.action.target = r.source + growth := by
    rw [hmatch.1, hactionRule]
    exact htarget
  have hmoveRule : r.action.move = .left := by rw [hactionRule]; exact hmove
  have htargetLower : 2 ≤ r.action.target := by
    rw [hactionRule]
    exact nonhalting_action_target frame.config action hhalt
  have hcapacity : r.action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hactionRule, hmove] using ready.capacity_ready slot action hlookup
  have radius := matchedTargetZeroWithin_canonicalBudget
    frame.config.state frame.config.focus [] skip r rs fullProgram cursorRuntime
  have hdecomp := matchedCursor_cleanup_decomposition slot frame.config.state
    frame.config.focus fullProgram cursorRuntime skip r rs
    (mismatchCertificateList_initial_trace slot frame.config.state
      frame.config.focus fullProgram cursorRuntime certs (by simp)) frame.outer
  obtain ⟨tail0⟩ := matchedAtLeast_leftBoundary_tail_bounded_radius
    (R := C) r.action.write r.source growth hwrite
      (by simpa only [htargetRule] using htargetLower)
    (cursorCleanupProgramPrefix skip r) scanPrefix
    (cursorCleanupPcPath skip (r :: rs)) (cursorCleanupTerminal skip)
    boundary outerTail cursorRuntime targetSpare left (readHeadNat r.read)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (by simpa [htargetRule, hmoveRule, hscanSplit] using
      matchedWritePath_safe r rs fullProgram hp)
    (by simpa [hmoveRule, hscanSplit, List.append_assoc] using
      matchedTargetPath_safe r hwrite rs fullProgram cursorRuntime hp hclock)
    (by simpa [left, final, htargetRule, hmoveRule, hscanSplit, houter,
      List.append_assoc] using hdecomp)
    (by simpa [hscanSplit] using
      passivePath_move (cursorMatchedMovePath_passive rs fullProgram hp))
    (leftBoundaryMarker_valid input)
    (matchedLeftBoundary_shift_safe_general skip r rs tailProgram hpTail)
    (matchedLeftBoundary_return_safe_general skip r rs tailProgram hpTail
      boundary (leftBoundaryMarker_passive input))
    (by
      have hc := matchedCleanupClock_leftInternal_safe skip r rs fullProgram
        hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank, hscanSplit, List.append_assoc] using hc)
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip)
    (by simpa [hscanSplit, boundary] using
      cursorCleanupProgramPath_restoreHeadSafe skip r rs fullProgram hp)
    (by
      have hb := radius.read_corridor_le
      show (List.replicate (r.source + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [boundary]).length
          ≤ C
      simp [encodedActionPath, htargetRule, hmoveRule, hscanSplit, moveBits,
        List.append_assoc] at hb ⊢
      omega)
    (by
      show (moveBits .left ++ scanPrefix ++ [boundary] ++
        writeHeadNat r.action.write :: cursorRuntime).length ≤ C
      simpa [hmoveRule, hscanSplit, List.append_assoc] using
        radius.target_corridor_le)
    (by
      have hb := radius.read_corridor_le
      show r.source + growth ≤ C
      simp [encodedActionPath, htargetRule, hmoveRule, hscanSplit, moveBits,
        List.append_assoc] at hb
      omega)
    (by
      have hcp := cursorCleanupProgramPrefix_length_le skip r
      dsimp [C, canonicalMismatchBudget]
      simp [encodeRules_append, ULogBytecode.encodeRules] at hcp ⊢
      omega)
    (by
      have hlen : scanPrefix.length ≤
          (cursorMatchedMovePath rs fullProgram).length := by simp [hscanSplit]
      have hfullScan : (cursorMatchedMovePath rs fullProgram).length ≤ C := by
        dsimp [C, canonicalMismatchBudget]
        simp [cursorMatchedMovePath, encodeRules_append, ULogBytecode.encodeRules]
        omega
      exact Nat.le_trans hlen hfullScan)
    (by
      dsimp [C, canonicalMismatchBudget]
      simp [cursorCleanupPcPath, encodeRules_append,
        ULogBytecode.encodeRules]
      omega)
  have hsum : frame.capacity - frame.config.state =
      growth + (frame.capacity - r.action.target) := by
    have htargetFrame : r.action.target = frame.config.state + growth := by
      rw [hactionRule]
      exact htarget
    rw [htargetFrame]
    omega
  have hsourceSpare : sourceSpare =
      List.replicate growth MStarConcreteAlphabet.work ++ targetSpare := by
    dsimp [sourceSpare, targetSpare]
    rw [hsum, List.replicate_add]
    simp only [List.append_assoc]
  dsimp only [sourceSpare, targetSpare] at hsourceSpare
  have hprogramRestored : fullProgram.map restoreProgramCell = fullProgram :=
    cursorDynamicProgramToHead_restored input
      (frame.config.leftRev.map payloadNat) (payloadNatList_safe _)
  have hclean := cleanedCursorCycleLeft_eq skip r rs fullProgram outerTail
    hprogramRestored
  have hcleanDyn := hclean.trans (canonicalCursorCycleLeft_dynamic
    (skip ++ r :: rs) input (frame.config.leftRev.map payloadNat) outerTail)
  have hleftOut :
      restoreProgramCell boundary :: scanPrefix.reverse.map restoreProgramCell ++
          (cursorCleanupProgramPrefix skip r).reverse.map restoreProgramCell ++
        ulogCore codeOne ::
          (cursorCleanupPcPath skip (r :: rs)).reverse.map restorePcCell ++
            ulogCore pcMark :: outerTail =
      dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
          (skip ++ r :: rs) input ++ ulogCore pcMark :: outerTail := by
    simpa [cleanedCycleLeft, hscanSplit, List.reverse_append,
      List.map_append, List.append_assoc] using hcleanDyn
  have hworkspace :
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: targetSpare =
      stateWorkspace frame.capacity r.action.target suffix := by
    dsimp [targetSpare, stateWorkspace]
    simp [List.append_assoc]
  have hclockCons :
      clockCellsAfter
        (payloadNat r.action.write :: frame.config.right.map payloadNat)
        frame.clockZeros frame.runtime =
      payloadNat r.action.write :: cursorRuntime := by
    dsimp [cursorRuntime]
    simp [clockCellsAfter, List.cons_append]
  have hnewRight :
      (ULogSemantics.applyAction frame.config action).right =
        action.write :: frame.config.right := by
    simp [ULogSemantics.applyAction, hmove, hleft]
  have hreframeLeft :
      clockCellsBefore
        (payloadNat r.action.write :: frame.config.right.map payloadNat)
        reframe.zeros reframe.runtime =
      payloadNat r.action.write :: cursorRuntime := by
    have hnew :
        (ULogSemantics.applyAction frame.config action).right.map payloadNat =
          payloadNat r.action.write :: frame.config.right.map payloadNat := by
      rw [hnewRight, ← hactionRule]
      simp only [List.map_cons]
    rw [← hnew, reframe.eq_before, hnew, hclockCons]
  refine ⟨⟨tail0.steps, ?_, ?_⟩⟩
  · calc
      tail0.steps ≤ 24 * (C + 1) ^ 2 := tail0.le_bound
      _ = 24 * (semanticFrameCursorRadius input frame + 1) ^ 2 :=
        congrArg (fun n => 24 * (n + 1) ^ 2) hCR
  · convert tail0.run using 1
    · simp only [left, final, fullProgram, cursorRuntime, hsourceSpare, targetSpare,
        htargetRule, hmoveRule, hscanSplit, houter, List.append_assoc,
        List.cons_append]
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction,
        ULogSemantics.blankCode, readHeadNat, heq, List.append_assoc]
      rw [hreframeLeft]
      simp only [payloadNat, List.cons_append]
      simpa only [htargetRule, readHeadNat, payloadNat, List.append_assoc,
        List.cons_append] using congrArg
        (fun xs => unheadTape (readHeadNat r.action.write) :: (cursorRuntime ++ xs))
        hworkspace.symm

end PakFixedPolyomino.ULogLocalTimeLeftBoundary
