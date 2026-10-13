import PakFixedPolyomino.ULogAutomaticSemanticRightBoundaryAtMost

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_certifiedFirstMatchAtLeast_rightBoundary
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)))
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
        writeHeadNat r.action.write :: clockBoundaryAfter clockZeros ::
          clockTailAfter clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hshift : ShiftRuntimeSafe
      (clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne]).reverse ++ [clockBoundaryAfter clockZeros]))
    (hrestoreClock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape) ++
                  [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
            [unheadTape (writeHeadNat r.action.write)])) :
    BranchedReaches slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore [] clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++
                  MStarConcreteAlphabet.work :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have trace := mismatchCertificateList_initial_trace slot current actual
    (cursorDynamicProgramToHead input leftTape)
    (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hactual : actual < 3 := by rw [← hmatch.2.1]; exact hread
  have hhead : choiceHead (readHeadNat actual) = true := by
    interval_cases actual <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat actual) hhead
    clockZeros [] (by simp [PayloadPathSafe])
    (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++
          MStarConcreteAlphabet.work :: suffix)
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot leftTape hleft
      (skip ++ r :: rs) (by simp) input outer (readHeadNat actual) hhead
      (clockCellsAfter [] clockZeros runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work :: suffix)
  have hrule := reaches_dynamicMismatchPrefix_matchedAtLeast_rightBoundary
    slot current actual input leftTape hleft (clockBoundaryAfter clockZeros)
    (clockBoundaryAfter_valid clockZeros) (clockTailAfter clockZeros runtime)
    outer suffix skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch
    growth htarget hread hwrite htargetLower hmove hboundary hcorridor hreadPath hwritePath
    htargetPath hscan hshift hreturn hrestoreClock hprogram
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
          ulogCore pcMark :: outer,
        readHeadNat actual,
        clockCellsAfter [] clockZeros runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++
                MStarConcreteAlphabet.work :: suffix⟩,
    branchStart, ?_, hbranch, reaches_trans hlookup ?_⟩
  · simpa [clockCellsBefore, clockCellsAfter, List.append_assoc] using hdec
  · simpa [hdecomp, List.append_assoc] using hrule

end PakFixedPolyomino.ULogBootstrapExecution
