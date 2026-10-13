import PakFixedPolyomino.ULogDynamicMoveCases

/-! Labelled one-cycle refinement for internal tape movements. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def clockCellsBefore (rightTape : List Tape) (k : ℕ)
    (runtime : List Tape) : List Tape :=
  rightTape ++ List.replicate k (ulogCore clockZero) ++
    ulogCore clockOne :: runtime

def clockCellsAfter (rightTape : List Tape) (k : ℕ)
    (runtime : List Tape) : List Tape :=
  rightTape ++ List.replicate k (ulogCore clockOne) ++
    ulogCore clockZero :: runtime

theorem branchedCycle_dynamicRightInternal_atMost
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (cell : Tape) (rightTape : List Tape)
    (hright : PayloadPathSafe (cell :: rightTape))
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (clockZeros extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read)
        (cell :: clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (dynamicMatchedRuleMovePath rs input leftTape)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs input leftTape))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        dynamicMatchedRuleMovePath rs input leftTape ++
          writeHeadNat r.action.write :: cell ::
            clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe (dynamicMatchedRuleMovePath rs input leftTape))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary ::
            (dynamicRuleProgramPath r rs input leftTape ++
              [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (dynamicRuleProgramPath r rs input leftTape ++
        [unheadTape (writeHeadNat r.action.write)]))
    (outer tail : List Tape) :
    BranchedReaches r.slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat r.read,
          clockCellsBefore (cell :: rightTape) clockZeros runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
            (unheadTape (writeHeadNat r.action.write) :: leftTape)
            (r :: rs) input ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter rightTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat r.read) hhead
    clockZeros (cell :: rightTape) hright
    (dynamicRuleReturnPath leftTape (r :: rs) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource r.slot leftTape hleft (r :: rs)
      (by simp) input outer (readHeadNat r.read) hhead
      (clockCellsAfter (cell :: rightTape) clockZeros runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
  have hrule := reaches_dynamicMatchedRuleCodeAtMost_rightInternal_cycle
    leftTape hleft r rs input extra hsource hread hwrite htargetLower hmove cell
    (hright cell (by simp)) (clockCellsAfter rightTape clockZeros runtime)
    (by simpa [clockCellsAfter, List.append_assoc] using hcorridor)
    hreadPath hwritePath
    (by simpa [clockCellsAfter, List.append_assoc] using htargetPath)
    hscan hclock hprogram outer tail
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath leftTape (r :: rs) input ++
          ulogCore pcMark :: outer,
        readHeadNat r.read,
        clockCellsAfter (cell :: rightTape) clockZeros runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩,
    branchStart, ?_, hbranch, reaches_trans hlookup ?_⟩
  · simpa [clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hdec
  · simpa [clockCellsAfter, List.append_assoc] using hrule

theorem branchedCycle_dynamicLeftInternal_atMost
    (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (clockZeros extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input (cell :: leftTape)
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (dynamicMatchedRuleMovePath rs input (cell :: leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs input (cell :: leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        dynamicMatchedRuleMovePath rs input (cell :: leftTape) ++
          writeHeadNat r.action.write ::
            clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (dynamicMatchedRuleMovePath rs input (cell :: leftTape)))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary ::
            (dynamicRuleProgramPath r rs input leftTape)).reverse))
    (hprogram : RestoreHeadSafe
      (dynamicRuleProgramPath r rs input leftTape))
    (outer tail : List Tape) :
    BranchedReaches r.slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat r.read,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat r.read) hhead
    clockZeros rightTape hright
    (dynamicRuleReturnPath (cell :: leftTape) (r :: rs) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource r.slot (cell :: leftTape) hleft
      (r :: rs) (by simp) input outer (readHeadNat r.read) hhead
      (clockCellsAfter rightTape clockZeros runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
  have hrule := reaches_dynamicMatchedRuleCodeAtMost_leftInternal_cycle
    cell leftTape hleft r rs input extra hsource hread hwrite htargetLower hmove
    (clockCellsAfter rightTape clockZeros runtime) hcorridor hreadPath
    hwritePath htargetPath hscan hclock hprogram outer tail
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath (cell :: leftTape) (r :: rs) input ++
          ulogCore pcMark :: outer,
        readHeadNat r.read,
        clockCellsAfter rightTape clockZeros runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩,
    branchStart, ?_, hbranch, reaches_trans hlookup ?_⟩
  · simpa [clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hdec
  · simpa [clockCellsAfter, List.append_assoc] using hrule

end PakFixedPolyomino.ULogBootstrapExecution
