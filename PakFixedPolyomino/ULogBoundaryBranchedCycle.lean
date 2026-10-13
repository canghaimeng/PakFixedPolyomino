import PakFixedPolyomino.ULogEmptyLeftBoundaryCycle

/-! Labelled full-cycle refinement at the preserved left boundary. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_dynamicLeftBoundary_atMost
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (clockZeros extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs [] [] (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (dynamicMatchedRuleMovePath rs [] [])))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs [] []))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ dynamicMatchedRuleMovePath rs [] [] ++
        writeHeadNat r.action.write ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe (dynamicMatchedRuleMovePath rs [] []))
    (hshift : ShiftRuntimeSafe
      (((ULogBytecode.encodeRules rs).map codeTape).reverse ++
        ((ULogBytecode.encodeRule r).map codeTape).reverse ++
          ulogCore sourceBoundary ::
            (List.replicate (r :: rs).length (ulogCore pcDone)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((((ULogBytecode.encodeRules rs).map codeTape).reverse ++
        ((ULogBytecode.encodeRule r).map codeTape).reverse ++
          ulogCore sourceBoundary ::
            (List.replicate (r :: rs).length (ulogCore pcDone)).reverse).reverse ++
              [ulogCore payloadStartOne]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary :: (ruleProgramPath r rs [])).reverse))
    (hprogram : RestoreHeadSafe (ruleProgramPath r rs []))
    (outer tail : List Tape) :
    BranchedReaches r.slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (r :: rs) [] ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
          readHeadNat r.read,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (r :: rs) [] ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
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
    (dynamicRuleReturnPath [] (r :: rs) [] ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    (runtime ++ List.replicate r.source (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource r.slot []
      (by simp [PayloadPathSafe]) (r :: rs) (by simp) []
      (MStarConcreteAlphabet.work :: outer) (readHeadNat r.read) hhead
      (clockCellsAfter rightTape clockZeros runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
  have hrule := reaches_dynamicMatchedRuleCodeAtMost_leftBoundary_cycle
    r rs extra hsource hread hwrite htargetLower hmove
    (clockCellsAfter rightTape clockZeros runtime) hcorridor hreadPath
    hwritePath htargetPath hscan hshift hreturn hclock hprogram outer tail
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath [] (r :: rs) [] ++
          ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
        readHeadNat r.read,
        clockCellsAfter rightTape clockZeros runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩,
    branchStart, ?_, hbranch, reaches_trans hlookup ?_⟩
  · simpa [clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hdec
  · simpa [clockCellsAfter, List.append_assoc] using hrule

end PakFixedPolyomino.ULogBootstrapExecution
