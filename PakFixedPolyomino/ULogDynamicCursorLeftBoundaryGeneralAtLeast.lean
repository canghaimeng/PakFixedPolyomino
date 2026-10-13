import PakFixedPolyomino.ULogDynamicCursorLeftBoundaryGeneral

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMismatchPrefix_matchedAtLeast_leftBoundary_general
    (slot : Bool) (current actual : ℕ) (input : List Bool)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input []) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead input [])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead input []) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs
          (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [leftBoundaryMarker input]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
                [leftBoundaryMarker input])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
          [leftBoundaryMarker input])) :
    Reaches
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) input
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have haction := reaches_mismatchPrefix_matchedAtLeast slot current actual
    (cursorDynamicProgramToHead input []) runtime
    (MStarConcreteAlphabet.work :: outer) suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hcursorBoundary hcorridor hreadPath hwritePath
    htargetPath
  have hp := cursorDynamicProgramToHead_emptyLeft_split input
  have hcleanup := reaches_cursorMatched_leftBoundary_cleanup_normalized
    slot current actual (leftBoundaryScanPrefix input) runtime outer
    (leftBoundaryMarker input) skip r rs final (by simpa [hp] using trace)
    hwrite hmove
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    (leftBoundaryMarker_valid input) (by simpa [hp] using hscan)
    hshift hreturn hclock hprogram (by
      simpa [hp] using cursorDynamicProgramToHead_restored input []
        (by simp [PayloadPathSafe]))
  have hall := reaches_trans haction (by simpa [hp] using hcleanup)
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    [] input skip r rs runtime (MStarConcreteAlphabet.work :: outer)
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hall
  rw [← hp, canonicalCursorCycleLeft_dynamic] at hall
  simpa [List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
