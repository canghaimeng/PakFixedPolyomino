import PakFixedPolyomino.ULogDynamicCursorRightBoundary

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMismatchPrefix_matchedAtMost_leftBoundary
    (slot : Bool) (current actual : ℕ)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead [] []) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead [] [])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead [] []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead [] [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead [] []) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead [] [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [ulogCore payloadStartOne]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs [] ++
                [ulogCore payloadStartOne])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs [] ++ [ulogCore payloadStartOne])) :
    Reaches
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) []
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) [] ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  have haction := reaches_mismatchPrefix_matchedAtMost slot current actual
    (cursorDynamicProgramToHead [] []) runtime
    (MStarConcreteAlphabet.work :: outer) suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch extra
    htarget hread hwrite htargetLower hcursorBoundary hcorridor hreadPath hwritePath
    htargetPath
  have hp : cursorDynamicProgramToHead [] [] =
      ([] : List Tape) ++ [ulogCore payloadStartOne] := by
    simp [cursorDynamicProgramToHead, payloadProgramPrefix]
  have hcleanup := reaches_cursorMatched_leftBoundary_cleanup_normalized
    slot current actual [] runtime outer (ulogCore payloadStartOne)
    skip r rs final (by simpa [hp] using trace) hwrite hmove
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    (Or.inr rfl) (by simpa [hp] using hscan) hshift hreturn hclock hprogram
    (by native_decide)
  have hall := reaches_trans haction (by simpa [hp] using hcleanup)
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    [] [] skip r rs runtime (MStarConcreteAlphabet.work :: outer)
      (ulogCore stateSep :: suffix)] at hall
  have hcanonical :
      canonicalCursorCycleLeft (skip ++ r :: rs)
          [ulogCore payloadStartOne] outer =
        dynamicRuleReturnPath [] (skip ++ r :: rs) [] ++
          ulogCore pcMark :: outer := by
    simpa [cursorDynamicProgramToHead, payloadProgramPrefix] using
      canonicalCursorCycleLeft_dynamic (skip ++ r :: rs) [] [] outer
  rw [hcanonical] at hall
  simpa [List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
