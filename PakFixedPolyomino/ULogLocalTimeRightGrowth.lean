/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeRightDecrease

/-! One repaired right-internal state-growth continuation. Actual
nonhalting supplies the target lower bound; the encoded corridor supplies
its radius; capacity reserve supplies the growth cells. Other movement
branches and shared cycle assembly are not claimed. -/

namespace PakFixedPolyomino.ULogLocalTimeRightGrowth

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution ULogBootstrapExecution
open PakULogCycleResourceBound PakULogNonterminalTailFuel PakULogTraceResourceBound
open PakULogContinuationResourceGeometry
open ULogLocalTimeStayGrowth

theorem canonicalTailBuilder_rightInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (next : Nat) (rightTail : List Nat)
    (hright : frame.config.right = next :: rightTail)
    (growth : Nat) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    CanonicalTailBuilder frame slot action reframe
      (PakULogCycleResourceBound.semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let programToHead := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let runtimeTail := clockCellsAfter (rightTail.map payloadNat)
    frame.clockZeros frame.runtime
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let sourceSpare : List Tape :=
    List.replicate (frame.capacity - frame.config.state)
      MStarConcreteAlphabet.work ++ suffix
  let targetSpare : List Tape :=
    List.replicate (frame.capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) programToHead cursorRuntime
  have hCR : C = PakULogCycleResourceBound.semanticFrameCursorRadius input frame := by
    dsimp [C, programToHead, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hcursorRuntime : cursorRuntime = payloadNat next :: runtimeTail := by
    dsimp [cursorRuntime, runtimeTail]
    simp [hright, clockCellsAfter]
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htargetRule : r.action.target = r.source + growth := by
    rw [hmatch.1, hactionRule]
    exact htarget
  have hmoveRule : r.action.move = .right := by
    rw [hactionRule]
    exact hmove
  have htargetLower : 2 ≤ r.action.target := by
    rw [hactionRule]
    exact nonhalting_action_target frame.config action hhalt
  have hcapacity : r.action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hactionRule, hmove, hright] using ready.capacity_ready slot action hlookup
  have radius := matchedTargetZeroWithin_canonicalBudget
    frame.config.state frame.config.focus [] skip r rs programToHead cursorRuntime
  have hdecomp := matchedCursor_cleanup_decomposition slot frame.config.state
    frame.config.focus programToHead cursorRuntime skip r rs
    (mismatchCertificateList_initial_trace slot frame.config.state
      frame.config.focus programToHead cursorRuntime certs (by simp)) frame.outer
  obtain ⟨tail0⟩ := matchedAtLeast_rightInternal_tail_bounded_radius
    (R := C) r.action.write r.source growth hwrite
    (by simpa only [htargetRule] using htargetLower)
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) frame.outer runtimeTail targetSpare left
    (readHeadNat r.read) (payloadNat next)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (payloadNat_safe next)
    (by simpa [htargetRule, hmoveRule] using
      matchedWritePath_safe r rs programToHead hp)
    (by
      have hsafe := matchedTargetPath_safe r hwrite rs programToHead cursorRuntime
        hp hclock
      simpa [hmoveRule, hcursorRuntime] using hsafe)
    (by simpa [left, final, htargetRule, hmoveRule,
      List.append_assoc] using hdecomp)
    (passivePath_move (cursorMatchedMovePath_passive rs programToHead hp))
    (matchedCleanupClock_rightInternal_safe skip r rs programToHead hp next)
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
      simpa [hmoveRule, ← hcursorRuntime] using radius.target_corridor_le)
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
  have hsum : frame.capacity - frame.config.state =
      growth + (frame.capacity - r.action.target) := by
    have ht : r.action.target = frame.config.state + growth := by
      rw [hactionRule]
      exact htarget
    omega
  have hsourceSpare : sourceSpare =
      List.replicate growth MStarConcreteAlphabet.work ++ targetSpare := by
    dsimp [sourceSpare, targetSpare]
    rw [hsum, List.replicate_add]
    simp only [List.append_assoc]
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
      stateWorkspace frame.capacity r.action.target suffix := by
    dsimp [targetSpare, stateWorkspace]
    simp only [List.append_assoc, List.cons_append]
  have hreframeRight :
      clockCellsBefore (rightTail.map payloadNat) reframe.zeros
        reframe.runtime = runtimeTail := by
    simpa [hmove, hright, ULogSemantics.applyAction, runtimeTail] using
      reframe.eq_before
  refine ⟨
    { steps := tail0.steps
      le_bound := ?_
      run := ?_ }⟩
  · calc
      tail0.steps ≤ 20 * (C + 1) ^ 2 := tail0.le_bound
      _ = 20 * (PakULogCycleResourceBound.semanticFrameCursorRadius input frame + 1) ^ 2 :=
        congrArg (fun n => 20 * (n + 1) ^ 2) hCR
      _ ≤ 24 * (PakULogCycleResourceBound.semanticFrameCursorRadius input frame + 1) ^ 2 := by
        nlinarith
  · convert tail0.run using 1
    · simp only [left, final, programToHead, cursorRuntime, hsourceSpare,
        htargetRule, hmoveRule, hcursorRuntime, targetSpare,
        List.append_assoc, List.cons_append]
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hright,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction,
        headTapeOfCell_payloadNat, hreframeRight, heq,
        List.append_assoc, List.cons_append]
      simpa only [htargetRule, targetSpare, List.append_assoc,
        List.cons_append] using hworkspace.symm

end PakFixedPolyomino.ULogLocalTimeRightGrowth
