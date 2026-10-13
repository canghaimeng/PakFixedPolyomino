import PakFixedPolyomino.ULogCertifiedProgramLookup

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMismatchPrefix_matchedAtLeast_rightInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (cell : Tape) (hcell : PayloadCell cell)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input leftTape) (cell :: runtime)
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read) (cell :: runtime)))
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
        writeHeadNat r.action.write :: cell :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
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
    Reaches
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual)
        (cell :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have haction := reaches_mismatchPrefix_matchedAtLeast slot current actual
    (cursorDynamicProgramToHead input leftTape) (cell :: runtime) outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath hwritePath htargetPath
  have hcleanup := reaches_cursorMatched_rightInternal_cleanup_normalized
    slot current actual (cursorDynamicProgramToHead input leftTape)
    (cell :: runtime) outer skip r rs final trace hwrite hmove cell
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    (by exact hcell) hscan hclock hprogram (by
      have hhead : choiceHead (writeHeadNat r.action.write) = true := by
        interval_cases r.action.write <;> native_decide
      have hnewLeft : PayloadPathSafe
          (unheadTape (writeHeadNat r.action.write) :: leftTape) := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact unheadTape_payloadCell _ hhead
        · exact hleft x hx
      have hrestored := cursorDynamicProgramToHead_restored input
        (unheadTape (writeHeadNat r.action.write) :: leftTape) hnewLeft
      simpa [cursorDynamicProgramToHead, List.reverse_cons,
        List.append_assoc] using hrestored)
  have hall := reaches_trans haction hcleanup
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs (cell :: runtime) outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hall
  have hpath :
      cursorDynamicProgramToHead input leftTape ++
          [unheadTape (writeHeadNat r.action.write)] =
        cursorDynamicProgramToHead input
          (unheadTape (writeHeadNat r.action.write) :: leftTape) := by
    simp [cursorDynamicProgramToHead, List.reverse_cons, List.append_assoc]
  rw [hpath, canonicalCursorCycleLeft_dynamic] at hall
  simpa [List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
