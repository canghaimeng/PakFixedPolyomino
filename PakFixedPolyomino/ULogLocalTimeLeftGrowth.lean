/- Local physical time from actual FrameReady and selected lookup only.
No global per-tick target or outer reserve. Original source is preserved. -/

import PakFixedPolyomino.ULogLocalTimeLeftDecrease

/-! One repaired left-internal state-growth continuation. Actual
nonhalting supplies the target lower bound; the encoded corridor supplies
its radius; capacity reserve supplies the growth cells. Other movement
branches and shared cycle assembly are not claimed. -/

namespace PakFixedPolyomino.ULogLocalTimeLeftGrowth

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution ULogBootstrapExecution
open PakULogCycleResourceBound PakULogNonterminalTailFuel PakULogTraceResourceBound
open PakULogContinuationResourceGeometry
open ULogLocalTimeStayGrowth

theorem canonicalTailBuilder_leftInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction frame.config action) = false)
    (previous : Nat) (leftTail : List Nat)
    (hleft : frame.config.leftRev = previous :: leftTail)
    (growth : Nat) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ULogLocalTimeStayGrowth.CanonicalTailBuilder frame slot action reframe
      (PakULogCycleResourceBound.semanticFrameCursorRadius input frame) := by
  intro skip r rs heq certs rscan hmatch hactionRule
  dsimp only
  let fullProgram := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let tailProgram := cursorDynamicProgramToHead input
    (leftTail.map payloadNat)
  let scanPrefix := cursorMatchedMovePath rs tailProgram
  let cursorRuntime := clockCellsAfter (frame.config.right.map payloadNat)
    frame.clockZeros frame.runtime
  let sourceSpare : List Tape := List.replicate
    (frame.capacity - frame.config.state) MStarConcreteAlphabet.work ++ suffix
  let targetSpare : List Tape := List.replicate
    (frame.capacity - r.action.target) MStarConcreteAlphabet.work ++ suffix
  let final := canonicalRuleCursor skip (r :: rs)
  let left := matchedReadLeftAt r.slot r.source r.read final.boundary
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: frame.outer)
  let C := canonicalMismatchBudget frame.config.state frame.config.focus []
    skip (r :: rs) fullProgram cursorRuntime
  have hfull : fullProgram = tailProgram ++ [payloadNat previous] := by
    simp [fullProgram, tailProgram, hleft, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have hscanSplit : cursorMatchedMovePath rs fullProgram =
      scanPrefix ++ [payloadNat previous] := by
    simp [scanPrefix, cursorMatchedMovePath, hfull, List.append_assoc]
  have hCR : C = PakULogCycleResourceBound.semanticFrameCursorRadius input frame := by
    dsimp [C, fullProgram, cursorRuntime]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hpTail := cursorDynamicProgramToHead_passive input leftTail
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime hruntime
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have htargetRule : r.action.target = r.source + growth := by
    rw [hmatch.1, hactionRule]
    exact htarget
  have hmoveRule : r.action.move = .left := by
    rw [hactionRule]
    exact hmove
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
  obtain ⟨tail0⟩ := matchedAtLeast_leftInternal_tail_bounded_radius
    (R := C) r.action.write r.source growth hwrite
    (by simpa only [htargetRule] using htargetLower)
    (cursorCleanupProgramPrefix skip r) scanPrefix
    (cursorCleanupPcPath skip (r :: rs)) (cursorCleanupTerminal skip)
    frame.outer cursorRuntime targetSpare left (readHeadNat r.read)
    (payloadNat previous)
    (choiceHead_readHeadNat_of_lt_three r.read rscan.read_valid)
    (payloadNat_safe previous)
    (by simpa [htargetRule, hmoveRule, hscanSplit] using
      matchedWritePath_safe r rs fullProgram hp)
    (by simpa [hmoveRule, hscanSplit, List.append_assoc] using
      matchedTargetPath_safe r hwrite rs fullProgram cursorRuntime hp hclock)
    (by simpa [left, final, htargetRule, hmoveRule, hscanSplit,
      List.append_assoc] using hdecomp)
    (passivePath_move
      (passivePath_append
        (cursorMatchedMovePath_passive rs tailProgram hpTail)
        (passivePath_map_payloadNat [previous])))
    (matchedCleanupClock_leftInternal_safe skip r rs tailProgram hpTail previous)
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs tailProgram hpTail)
    (by
      have hb := radius.read_corridor_le
      show (List.replicate (r.source + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++
          [payloadNat previous]).length ≤ C
      simp [encodedActionPath, htargetRule, hmoveRule, hscanSplit, moveBits,
        List.append_assoc] at hb ⊢
      omega)
    (by
      simpa [hmoveRule, hscanSplit, List.append_assoc] using
        radius.target_corridor_le)
    (by rw [← htargetRule]; exact matched_radius_target_le radius)
    (by
      have hcp := cursorCleanupProgramPrefix_length_le skip r
      dsimp [C, canonicalMismatchBudget]
      simp [encodeRules_append, ULogBytecode.encodeRules] at hcp ⊢
      omega)
    (by
      have hlen : scanPrefix.length ≤
          (cursorMatchedMovePath rs fullProgram).length := by
        simp [hscanSplit]
      have hfullScan : (cursorMatchedMovePath rs fullProgram).length ≤ C := by
        dsimp [C, canonicalMismatchBudget]
        simp [cursorMatchedMovePath, encodeRules_append,
          ULogBytecode.encodeRules]
        omega
      exact Nat.le_trans hlen hfullScan)
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
  have hprogramRestored : tailProgram.map restoreProgramCell = tailProgram :=
    cursorDynamicProgramToHead_restored input (leftTail.map payloadNat)
      (payloadNatList_safe _)
  have hclean := cleanedCursorCycleLeft_eq skip r rs tailProgram frame.outer
    hprogramRestored
  have hcleanDyn := hclean.trans (canonicalCursorCycleLeft_dynamic
    (skip ++ r :: rs) input (leftTail.map payloadNat) frame.outer)
  have hleftOut :
      scanPrefix.reverse.map restoreProgramCell ++
          (cursorCleanupProgramPrefix skip r).reverse.map restoreProgramCell ++
        ulogCore codeOne ::
          (cursorCleanupPcPath skip (r :: rs)).reverse.map restorePcCell ++
            ulogCore pcMark :: frame.outer =
      dynamicRuleReturnPath (leftTail.map payloadNat) (skip ++ r :: rs) input ++
        ulogCore pcMark :: frame.outer := by
    simpa [cleanedCycleLeft, scanPrefix, tailProgram, List.reverse_append,
      List.map_append, List.append_assoc] using hcleanDyn
  have hworkspace :
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: targetSpare =
      stateWorkspace frame.capacity r.action.target suffix := by
    dsimp [targetSpare, stateWorkspace]
    simp only [List.append_assoc, List.cons_append]
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
    · simp only [left, final, fullProgram, cursorRuntime, hsourceSpare,
        htargetRule, hmoveRule, hscanSplit, targetSpare,
        List.append_assoc, List.cons_append]
    · simp only [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
        semanticCycleEncoding]
      rw [hleftOut]
      simp [semanticCapacityAfter, semanticOuterAfter, hleft,
        ← hactionRule, hmoveRule, ULogSemantics.applyAction, hnewRight,
        headTapeOfCell_payloadNat, heq, List.append_assoc]
      rw [hreframeLeft]
      simp only [payloadNat, List.cons_append]
      simpa only [htargetRule, targetSpare, List.append_assoc, List.cons_append] using
        congrArg (fun xs =>
          unheadTape (readHeadNat r.action.write) :: (cursorRuntime ++ xs))
          hworkspace.symm

end PakFixedPolyomino.ULogLocalTimeLeftGrowth
