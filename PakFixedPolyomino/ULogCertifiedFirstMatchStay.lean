import PakFixedPolyomino.ULogCertifiedMismatchTrace

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_certifiedFirstMatchAtMost_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape clockTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hclockTape : PayloadPathSafe clockTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter clockTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
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
  have trace := mismatchCertificateList_initial_trace slot current actual
    (cursorDynamicProgramToHead input leftTape)
    (clockCellsAfter clockTape clockZeros runtime) certs (by simp)
  have hboundary :
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundary ∨
        (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryZero ∨
          (canonicalRuleCursor skip (r :: rs)).boundary =
            sourceBoundaryOne := by
    exact boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  exact branchedCycle_dynamicMismatchPrefix_matchedAtMost_stay
    slot current actual input leftTape clockTape hleft hclockTape clockZeros
    runtime outer suffix skip r rs (canonicalRuleCursor skip (r :: rs))
    trace hmatch extra htarget hread hwrite htargetLower hmove hboundary hcorridor
    hreadPath hwritePath htargetPath hscan hrestoreClock hprogram

end PakFixedPolyomino.ULogBootstrapExecution
