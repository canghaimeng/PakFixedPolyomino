import PakFixedPolyomino.ULogDynamicCursorStayAtMost

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_dynamicMismatchPrefix_matchedAtMost_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape clockTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hclockTape : PayloadPathSafe clockTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter clockTape clockZeros runtime)
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockCellsAfter clockTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write ::
          clockCellsAfter clockTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    BranchedReaches slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          clockCellsAfter clockTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  have hactual : actual < 3 := by
    rw [← hmatch.2.1]
    exact hread
  have hhead : choiceHead (readHeadNat actual) = true := by
    interval_cases actual <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat actual) hhead
    clockZeros clockTape hclockTape
    (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  obtain ⟨branchStart, hbranch, hrun⟩ :=
    chooseSlot_dynamicMismatchPrefix_matchedAtMost_stay
      slot current actual input leftTape hleft
      (clockCellsAfter clockTape clockZeros runtime) outer suffix
      skip r rs final trace hmatch extra htarget hread hwrite htargetLower hmove hboundary
      hcorridor hreadPath hwritePath htargetPath hscan hrestoreClock hprogram
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
          ulogCore pcMark :: outer,
        readHeadNat actual,
        clockCellsAfter clockTape clockZeros runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩,
    branchStart, ?_, hbranch, hrun⟩
  simpa [clockCellsBefore, clockCellsAfter, List.append_assoc] using hdec

end PakFixedPolyomino.ULogBootstrapExecution
