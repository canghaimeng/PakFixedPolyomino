import PakFixedPolyomino.ULogDynamicBranchedCycles

/-! Runtime-shifting boundary movement for repeated universal cycles. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def rightBoundaryShiftPath (runtime : List Tape) (target : ℕ) : List Tape :=
  runtime ++ List.replicate target (ulogCore stateZero) ++
    [ulogCore stateOne, ulogCore stateSep]

theorem reaches_dynamicMatchedRuleCodeAtMost_rightBoundary_cycle
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + (extra + 1))
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right) (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read) (boundary :: runtime)))
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
          writeHeadNat r.action.write :: boundary :: runtime))
    (hscan : MoveScanSafe (dynamicMatchedRuleMovePath rs input leftTape))
    (hshift : ShiftRuntimeSafe
      (rightBoundaryShiftPath runtime r.action.target))
    (hreturn : ReturnMovedSafe
      ((runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary ::
            (dynamicRuleProgramPath r rs input leftTape ++
              [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (dynamicRuleProgramPath r rs input leftTape ++
        [unheadTape (writeHeadNat r.action.write)]))
    (outer tail : List Tape) :
    Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input outer
        (readHeadNat r.read)
        (boundary :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
            (unheadTape (writeHeadNat r.action.write) :: leftTape)
            (r :: rs) input ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_dynamicMatchedRuleCodeAtMostState leftTape r rs
    input (extra + 1) hsource hread hwrite htargetLower (boundary :: runtime)
    hcorridor hreadPath hwritePath htargetPath outer tail
  have hpc : RestorePcSafe
      (List.replicate (r :: rs).length (ulogCore pcDone)) := by
    intro x hx
    have hm : (r :: rs).length ≠ 0 ∧ x = ulogCore pcDone := by
      simpa only [List.mem_replicate] using hx
    exact Or.inl hm.2
  have holdHead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveRightBoundary_cleanup
    ((ULogBytecode.encodeRule r).map codeTape)
    (dynamicMatchedRuleMovePath rs input leftTape)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) outer (writeHeadNat r.action.write) boundary
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      [ulogCore stateOne])
    (ulogCore stateSep)
    (List.replicate extra MStarConcreteAlphabet.work ++ tail)
    hscan hboundary
    (by simpa [rightBoundaryShiftPath, List.append_assoc] using hshift)
    (by simpa [List.append_assoc] using hreturn)
    holdHead
    (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hclock)
    hpc (Or.inr rfl)
    (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hprogram)
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (dynamicRuleProgramPath r rs input leftTape ++
              [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleftEq := matchedRuleLeft_eq r rs outer
    rw [hmove] at hleftEq
    rw [hmove]
    rw [hleftEq]
    simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.replicate_succ,
      List.append_assoc] using hcleanup
  have hall := reaches_trans haction hcleanup'
  have hnewLeft : PayloadPathSafe
      (unheadTape (writeHeadNat r.action.write) :: leftTape) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact unheadTape_payloadCell _ holdHead
    · exact hleft x hx
  have hpathEq :
      dynamicRuleProgramPath r rs input
          (unheadTape (writeHeadNat r.action.write) :: leftTape) =
        dynamicRuleProgramPath r rs input leftTape ++
          [unheadTape (writeHeadNat r.action.write)] := by
    simp [dynamicRuleProgramPath, List.append_assoc]
  rw [← hpathEq] at hall
  rw [cleanedCycleLeft_dynamicRuleProgramPath _ hnewLeft] at hall
  exact hall

end PakFixedPolyomino.ULogBootstrapExecution
