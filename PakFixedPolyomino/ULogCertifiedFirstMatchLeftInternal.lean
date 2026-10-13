import PakFixedPolyomino.ULogCertifiedFirstMatchRightInternal

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_certifiedFirstMatchAtMost_leftInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input (cell :: leftTape))
      (clockCellsAfter rightTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input (cell :: leftTape))
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
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
        writeHeadNat r.action.write ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input (cell :: leftTape))))
    (hrestoreClock : RestoreClockSafe
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
    BranchedReaches slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  have trace := mismatchCertificateList_initial_trace slot current actual
    (cursorDynamicProgramToHead input (cell :: leftTape))
    (clockCellsAfter rightTape clockZeros runtime) certs (by simp)
  have hboundary :
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundary ∨
        (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryZero ∨
          (canonicalRuleCursor skip (r :: rs)).boundary =
            sourceBoundaryOne :=
    boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hactual : actual < 3 := by
    rw [← hmatch.2.1]
    exact hread
  have hhead : choiceHead (readHeadNat actual) = true := by
    interval_cases actual <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat actual) hhead
    clockZeros rightTape hright
    (dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot (cell :: leftTape) hleft
      (skip ++ r :: rs) (by simp) input outer (readHeadNat actual) hhead
      (clockCellsAfter rightTape clockZeros runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hrule := reaches_dynamicMismatchPrefix_matchedAtMost_leftInternal
    slot current actual input cell leftTape hleft
    (clockCellsAfter rightTape clockZeros runtime) outer suffix skip r rs
    (canonicalRuleCursor skip (r :: rs)) trace hmatch extra htarget hread
    hwrite htargetLower hmove hboundary hcorridor hreadPath hwritePath htargetPath hscan
    hrestoreClock hprogram
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
          ulogCore pcMark :: outer,
        readHeadNat actual,
        clockCellsAfter rightTape clockZeros runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩,
    branchStart, ?_, hbranch, reaches_trans hlookup ?_⟩
  · simpa [clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hdec
  · simpa [clockCellsAfter, List.append_assoc] using hrule

end PakFixedPolyomino.ULogBootstrapExecution
