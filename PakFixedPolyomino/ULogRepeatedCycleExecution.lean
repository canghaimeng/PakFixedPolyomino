import PakFixedPolyomino.ULogRuleCycleExecution

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem chooseSlot_reaches_matchedRuleCodeAtMost_stay_cycle
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (matchedRuleMovePath rs input))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary :: (ruleProgramPath r rs input)).reverse))
    (hprogram : RestoreHeadSafe (ruleProgramPath r rs input))
    (left tail : List Tape) :
    ∃ branchStart,
      oneStepAt (ULogBytecode.slotIndex r.slot)
          (.running .chooseSlot
            ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
              readHeadNat r.read,
              runtime ++ List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail⟩) =
        branchStart ∧
      Reaches branchStart
        (.running .cycleStart
          ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
            writeHeadNat r.action.write,
            runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have hmatched := reaches_matchedRuleCodeAtMost_stay_cycle r rs input extra
    hsource hread hwrite htargetLower hmove runtime hsourcePath hreadPath hwritePath
    htargetPath hscan hclock hprogram left tail
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  cases hslot : r.slot with
  | false =>
      obtain ⟨branchStart, hbranch, hrule⟩ :=
        chooseSlot_zero_reaches_ruleSource (r :: rs) (by simp) input left
          (readHeadNat r.read) hhead
          (runtime ++ List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
      refine ⟨branchStart, ?_, reaches_trans hrule ?_⟩
      · simpa [ULogBytecode.slotIndex, hslot] using hbranch
      · simpa [hslot] using hmatched
  | true =>
      obtain ⟨branchStart, hbranch, hrule⟩ :=
        chooseSlot_one_reaches_ruleSource (r :: rs) (by simp) input left
          (readHeadNat r.read) hhead
          (runtime ++ List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
      refine ⟨branchStart, ?_, reaches_trans hrule ?_⟩
      · simpa [ULogBytecode.slotIndex, hslot] using hbranch
      · simpa [hslot] using hmatched

theorem chooseSlot_reaches_matchedRuleCodeAtLeast_stay_cycle
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (growth : ℕ)
    (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (matchedRuleMovePath rs input))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary :: (ruleProgramPath r rs input)).reverse))
    (hprogram : RestoreHeadSafe (ruleProgramPath r rs input))
    (left tail : List Tape) :
    ∃ branchStart,
      oneStepAt (ULogBytecode.slotIndex r.slot)
          (.running .chooseSlot
            ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
              readHeadNat r.read,
              runtime ++ List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate growth MStarConcreteAlphabet.work ++ tail⟩) =
        branchStart ∧
      Reaches branchStart
        (.running .cycleStart
          ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
            writeHeadNat r.action.write,
            runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
  have hmatched := reaches_matchedRuleCodeAtLeast_stay_cycle r rs input growth
    htarget hread hwrite htargetLower hmove runtime hsourcePath hreadPath hwritePath
    htargetPath hscan hclock hprogram left tail
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  cases hslot : r.slot with
  | false =>
      obtain ⟨branchStart, hbranch, hrule⟩ :=
        chooseSlot_zero_reaches_ruleSource (r :: rs) (by simp) input left
          (readHeadNat r.read) hhead
          (runtime ++ List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail)
      refine ⟨branchStart, ?_, reaches_trans hrule ?_⟩
      · simpa [ULogBytecode.slotIndex, hslot] using hbranch
      · simpa [hslot] using hmatched
  | true =>
      obtain ⟨branchStart, hbranch, hrule⟩ :=
        chooseSlot_one_reaches_ruleSource (r :: rs) (by simp) input left
          (readHeadNat r.read) hhead
          (runtime ++ List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail)
      refine ⟨branchStart, ?_, reaches_trans hrule ?_⟩
      · simpa [ULogBytecode.slotIndex, hslot] using hbranch
      · simpa [hslot] using hmatched
end PakFixedPolyomino.ULogBootstrapExecution
