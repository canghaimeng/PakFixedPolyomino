import PakFixedPolyomino.ULogDynamicRuleAction

/-! Repeated-cycle cleanup for evolving simulated left/right tapes. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def dynamicRuleProgramPath (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (leftTape : List Tape) : List Tape :=
  ruleProgramPath r rs input ++ leftTape.reverse

theorem restoreProgramCell_payloadCell (x : Tape) (hx : PayloadCell x) :
    restoreProgramCell x = x := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem restoreProgramCell_payloadPath (path : List Tape)
    (hsafe : PayloadPathSafe path) :
    path.map restoreProgramCell = path := by
  induction path with
  | nil => rfl
  | cons x xs ih =>
      simp [restoreProgramCell_payloadCell x (hsafe x (by simp)),
        ih (fun y hy => hsafe y (by simp [hy]))]

theorem cleanedCycleLeft_dynamicRuleProgramPath
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (outer : List Tape) :
    cleanedCycleLeft
        (List.replicate (r :: rs).length (ulogCore pcDone))
        (dynamicRuleProgramPath r rs input leftTape) outer =
      dynamicRuleReturnPath leftTape (r :: rs) input ++
        ulogCore pcMark :: outer := by
  simp [cleanedCycleLeft, dynamicRuleProgramPath, dynamicRuleReturnPath,
    ruleProgramPath, matchedRuleMovePath, ruleReturnPath,
    ULogBytecode.encodeRules, List.map_append, List.map_reverse,
    List.reverse_append, restoreProgramCell_comp_codeTape,
    restoreProgramCell_payloadProgramPrefix,
    restoreProgramCell_payloadPath leftTape hleft,
    codeTape, List.append_assoc]

theorem reaches_dynamicMatchedRuleCodeAtMost_stay_cycle
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read) runtime))
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
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (dynamicMatchedRuleMovePath rs input leftTape))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore sourceBoundary ::
            (dynamicRuleProgramPath r rs input leftTape)).reverse))
    (hprogram : RestoreHeadSafe
      (dynamicRuleProgramPath r rs input leftTape))
    (outer tail : List Tape) :
    Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input outer
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_dynamicMatchedRuleCodeAtMostState leftTape r rs
    input extra hsource hread hwrite htargetLower runtime hcorridor hreadPath
    hwritePath htargetPath outer tail
  have hpc : RestorePcSafe
      (List.replicate (r :: rs).length (ulogCore pcDone)) := by
    intro x hx
    have hm : (r :: rs).length ≠ 0 ∧ x = ulogCore pcDone := by
      simpa only [List.mem_replicate] using hx
    exact Or.inl hm.2
  have hnewHead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveStay_cleanup
    ((ULogBytecode.encodeRule r).map codeTape)
    (dynamicMatchedRuleMovePath rs input leftTape)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) outer (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail)
    hscan (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath] using hclock) hpc (Or.inr rfl)
    (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath] using hprogram) hnewHead
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (dynamicRuleProgramPath r rs input leftTape) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleft := matchedRuleLeft_eq r rs outer
    rw [hmove] at hleft
    rw [hmove]
    rw [hleft]
    simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath] using hcleanup
  have hall := reaches_trans haction hcleanup'
  rw [cleanedCycleLeft_dynamicRuleProgramPath leftTape hleft] at hall
  exact hall

theorem unheadTape_payloadCell (head : Tape)
    (hhead : choiceHead head = true) : PayloadCell (unheadTape head) := by
  unfold choiceHead at hhead
  simp only [decide_eq_true_eq] at hhead
  rcases hhead with rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (by decide))

theorem reaches_dynamicMatchedRuleCodeAtMost_rightInternal_cycle
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right) (cell : Tape)
    (hcell : PayloadCell cell) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read) (cell :: runtime)))
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
          writeHeadNat r.action.write :: cell :: runtime))
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
    Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input outer
        (readHeadNat r.read)
        (cell :: runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
            (unheadTape (writeHeadNat r.action.write) :: leftTape)
            (r :: rs) input ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_dynamicMatchedRuleCodeAtMostState leftTape r rs
    input extra hsource hread hwrite htargetLower (cell :: runtime)
    hcorridor hreadPath
    hwritePath htargetPath outer tail
  have hpc : RestorePcSafe
      (List.replicate (r :: rs).length (ulogCore pcDone)) := by
    intro x hx
    have hm : (r :: rs).length ≠ 0 ∧ x = ulogCore pcDone := by
      simpa only [List.mem_replicate] using hx
    exact Or.inl hm.2
  have holdHead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveRightInternal_cleanup
    ((ULogBytecode.encodeRule r).map codeTape)
    (dynamicMatchedRuleMovePath rs input leftTape)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) outer (writeHeadNat r.action.write) cell
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail)
    hscan holdHead hcell
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
          (cell :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (dynamicRuleProgramPath r rs input leftTape ++
              [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleftEq := matchedRuleLeft_eq r rs outer
    rw [hmove] at hleftEq
    rw [hmove]
    rw [hleftEq]
    simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hcleanup
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
