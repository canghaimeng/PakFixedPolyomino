import PakFixedPolyomino.ULogRepeatedCycleExecution

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def BranchedReaches (slot : Bool) (start finish : Result) : Prop :=
  ∃ choice branch,
    Reaches start choice ∧
      oneStepAt (ULogBytecode.slotIndex slot) choice = branch ∧
        Reaches branch finish

def clockRuntimeBefore (k : ℕ) (tape : List Bool)
    (runtime : List Tape) : List Tape :=
  tape.map payloadTape ++ List.replicate k (ulogCore clockZero) ++
    ulogCore clockOne :: runtime

def clockRuntimeAfter (k : ℕ) (tape : List Bool)
    (runtime : List Tape) : List Tape :=
  tape.map payloadTape ++ List.replicate k (ulogCore clockOne) ++
    ulogCore clockZero :: runtime

theorem branchedCycle_matchedRuleCodeAtMost_stay
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input clockTape : List Bool) (clockZeros extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: clockRuntimeAfter clockZeros clockTape runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write ::
          clockRuntimeAfter clockZeros clockTape runtime))
    (hscan : MoveScanSafe (matchedRuleMovePath rs input))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary :: (ruleProgramPath r rs input)).reverse))
    (hprogram : RestoreHeadSafe (ruleProgramPath r rs input))
    (left tail : List Tape) :
    BranchedReaches r.slot
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          readHeadNat r.read,
          clockRuntimeBefore clockZeros clockTape runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          writeHeadNat r.action.write,
          clockRuntimeAfter clockZeros clockTape runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have hdec := reaches_clockDecrementPower (readHeadNat r.read) hhead
    clockZeros clockTape
    (ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left)
    (runtime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨branchStart, hbranch, hrun⟩ :=
    chooseSlot_reaches_matchedRuleCodeAtMost_stay_cycle r rs input extra
      hsource hread hwrite htargetLower hmove
      (clockRuntimeAfter clockZeros clockTape runtime)
      hsourcePath hreadPath hwritePath htargetPath hscan hrestoreClock
      hprogram left tail
  refine ⟨.running .chooseSlot
      ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
        readHeadNat r.read,
        clockRuntimeAfter clockZeros clockTape runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩,
    branchStart, ?_, hbranch, hrun⟩
  simpa [clockRuntimeBefore, clockRuntimeAfter, List.append_assoc] using hdec

theorem branchedCycle_matchedRuleCodeAtLeast_stay
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input clockTape : List Bool) (clockZeros growth : ℕ)
    (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: clockRuntimeAfter clockZeros clockTape runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write ::
          clockRuntimeAfter clockZeros clockTape runtime))
    (hscan : MoveScanSafe (matchedRuleMovePath rs input))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary :: (ruleProgramPath r rs input)).reverse))
    (hprogram : RestoreHeadSafe (ruleProgramPath r rs input))
    (left tail : List Tape) :
    BranchedReaches r.slot
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          readHeadNat r.read,
          clockRuntimeBefore clockZeros clockTape runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ tail⟩)
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          writeHeadNat r.action.write,
          clockRuntimeAfter clockZeros clockTape runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have hdec := reaches_clockDecrementPower (readHeadNat r.read) hhead
    clockZeros clockTape
    (ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left)
    (runtime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ tail)
  obtain ⟨branchStart, hbranch, hrun⟩ :=
    chooseSlot_reaches_matchedRuleCodeAtLeast_stay_cycle r rs input growth
      htarget hread hwrite htargetLower hmove
      (clockRuntimeAfter clockZeros clockTape runtime)
      hsourcePath hreadPath hwritePath htargetPath hscan hrestoreClock
      hprogram left tail
  refine ⟨.running .chooseSlot
      ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
        readHeadNat r.read,
        clockRuntimeAfter clockZeros clockTape runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail⟩,
    branchStart, ?_, hbranch, hrun⟩
  simpa [clockRuntimeBefore, clockRuntimeAfter, List.append_assoc] using hdec

end PakFixedPolyomino.ULogBootstrapExecution
