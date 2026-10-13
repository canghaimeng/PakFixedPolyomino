import PakFixedPolyomino.ULogDynamicCursorRightInternalAtLeast

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMismatchPrefix_matchedAtLeast_leftInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input (cell :: leftTape)) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input (cell :: leftTape))
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape)))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape))))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input (cell :: leftTape)) ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input (cell :: leftTape))))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    Reaches
      (dynamicRuleSourceStarted slot (cell :: leftTape)
        (skip ++ r :: rs) input outer (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have haction := reaches_mismatchPrefix_matchedAtLeast slot current actual
    (cursorDynamicProgramToHead input (cell :: leftTape)) runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath hwritePath htargetPath
  have hpath : cursorDynamicProgramToHead input (cell :: leftTape) =
      cursorDynamicProgramToHead input leftTape ++ [cell] := by
    simp [cursorDynamicProgramToHead, List.reverse_cons, List.append_assoc]
  have hcell : PayloadCell cell := hleft cell (by simp)
  have hleftTail : PayloadPathSafe leftTape := by
    intro x hx
    exact hleft x (by simp [hx])
  have hcleanup := reaches_cursorMatched_leftInternal_cleanup_normalized
    slot current actual (cursorDynamicProgramToHead input leftTape) runtime
    outer cell skip r rs final (by simpa [hpath] using trace) hwrite hmove
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hcell (by simpa [hpath] using hscan) hclock hprogram
    (cursorDynamicProgramToHead_restored input leftTape hleftTail)
  have hall := reaches_trans haction (by simpa [hpath] using hcleanup)
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    (cell :: leftTape) input skip r rs runtime outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hall
  rw [canonicalCursorCycleLeft_dynamic] at hall
  simpa [List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
