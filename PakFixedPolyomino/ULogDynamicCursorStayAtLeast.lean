import PakFixedPolyomino.ULogCertifiedFirstMatchStay

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMismatchPrefix_matchedAtLeast_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read) runtime))
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
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hclock : RestoreClockSafe
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
    Reaches
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have h := reaches_mismatchPrefix_matchedAtLeast_stay_normalized
    slot current actual (cursorDynamicProgramToHead input leftTape)
    runtime outer suffix skip r rs final trace hmatch growth htarget hread
    hwrite htargetLower hmove hboundary hcorridor hreadPath hwritePath htargetPath hscan
    hclock hprogram (cursorDynamicProgramToHead_restored input leftTape hleft)
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs runtime outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at h
  rw [canonicalCursorCycleLeft_dynamic] at h
  simpa [List.append_assoc] using h

theorem chooseSlot_dynamicMismatchPrefix_matchedAtLeast_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read) runtime))
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
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hclock : RestoreClockSafe
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
    ∃ branchStart,
      oneStepAt (ULogBytecode.slotIndex slot)
          (.running .chooseSlot
            ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
                ulogCore pcMark :: outer,
              readHeadNat actual,
              runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate growth MStarConcreteAlphabet.work ++
                    suffix⟩) = branchStart ∧
      Reaches branchStart
        (.running .cycleStart
          ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
              ulogCore pcMark :: outer,
            writeHeadNat r.action.write,
            runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  have hactual : actual < 3 := by
    rw [← hmatch.2.1]
    exact hread
  have hhead : choiceHead (readHeadNat actual) = true := by
    interval_cases actual <;> native_decide
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot leftTape hleft
      (skip ++ r :: rs) (by simp) input outer (readHeadNat actual) hhead
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hrule := reaches_dynamicMismatchPrefix_matchedAtLeast_stay
    slot current actual input leftTape hleft runtime outer suffix skip r rs
    final trace hmatch growth htarget hread hwrite htargetLower hmove hboundary hcorridor
    hreadPath hwritePath htargetPath hscan hclock hprogram
  exact ⟨branchStart, hbranch, reaches_trans hlookup hrule⟩

end PakFixedPolyomino.ULogBootstrapExecution
