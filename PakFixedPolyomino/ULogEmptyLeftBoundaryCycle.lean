import PakFixedPolyomino.ULogDynamicBoundaryCycles

/-! The left-boundary cycle for the preserved empty-input marker. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem dynamicMatchedRuleMovePath_empty (rs : List ULogBytecode.RuleCode) :
    dynamicMatchedRuleMovePath rs [] [] =
      (ULogBytecode.encodeRules rs).map codeTape ++
        [ulogCore payloadStartOne] := by
  simp [dynamicMatchedRuleMovePath, matchedRuleMovePath,
    payloadProgramPrefix]

theorem reaches_dynamicMatchedRuleCodeAtMost_leftBoundary_cycle
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (extra : ℕ) (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs [] [] (readHeadNat r.read) runtime))
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
        writeHeadNat r.action.write :: runtime))
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
    Reaches
      (dynamicRuleSourceStarted r.slot [] (r :: rs) []
        (MStarConcreteAlphabet.work :: outer) (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (r :: rs) [] ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_dynamicMatchedRuleCodeAtMostState [] r rs [] extra
    hsource hread hwrite htargetLower runtime hcorridor hreadPath hwritePath htargetPath
    (MStarConcreteAlphabet.work :: outer) tail
  have hpc : RestorePcSafe
      (List.replicate (r :: rs).length (ulogCore pcDone)) := by
    intro x hx
    have hm : (r :: rs).length ≠ 0 ∧ x = ulogCore pcDone := by
      simpa only [List.mem_replicate] using hx
    exact Or.inl hm.2
  have holdHead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveLeftBoundary_cleanup
    ((ULogBytecode.encodeRule r).map codeTape)
    ((ULogBytecode.encodeRules rs).map codeTape)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) (ulogCore payloadStartOne) outer
    (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail)
    (by simpa [dynamicMatchedRuleMovePath_empty] using hscan)
    (Or.inr rfl) hshift hreturn holdHead
    (by simpa [ruleProgramPath, matchedRuleMovePath,
      payloadProgramPrefix, List.append_assoc] using hclock)
    hpc (Or.inr rfl)
    (by simpa [ruleProgramPath, matchedRuleMovePath,
      payloadProgramPrefix, List.append_assoc] using hprogram)
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs [] [])
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (ruleProgramPath r rs []) outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleftEq := matchedRuleLeft_eq r rs
      (MStarConcreteAlphabet.work :: outer)
    rw [hmove] at hleftEq
    rw [hmove, dynamicMatchedRuleMovePath_empty, hleftEq]
    simpa [ruleProgramPath, matchedRuleMovePath, payloadProgramPrefix,
      List.append_assoc] using hcleanup
  have hall := reaches_trans haction hcleanup'
  rw [cleanedCycleLeft_ruleProgramPath] at hall
  simpa [dynamicRuleReturnPath] using hall

end PakFixedPolyomino.ULogBootstrapExecution
