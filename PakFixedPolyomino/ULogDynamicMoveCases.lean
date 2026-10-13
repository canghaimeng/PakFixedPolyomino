import PakFixedPolyomino.ULogDynamicRuleCycle

/-! Internal left movement and labelled lookup for evolving tape cycles. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem dynamicMatchedRuleMovePath_cons (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (cell : Tape) (leftTape : List Tape) :
    dynamicMatchedRuleMovePath rs input (cell :: leftTape) =
      dynamicMatchedRuleMovePath rs input leftTape ++ [cell] := by
  simp [dynamicMatchedRuleMovePath, List.append_assoc]

theorem reaches_dynamicMatchedRuleCodeAtMost_leftInternal_cycle
    (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left) (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input (cell :: leftTape)
        (readHeadNat r.read) runtime))
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
          writeHeadNat r.action.write :: runtime))
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
    Reaches
      (dynamicRuleSourceStarted r.slot (cell :: leftTape) (r :: rs) input
        outer (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_dynamicMatchedRuleCodeAtMostState
    (cell :: leftTape) r rs input extra hsource hread hwrite htargetLower runtime
    hcorridor hreadPath hwritePath htargetPath outer tail
  have hpc : RestorePcSafe
      (List.replicate (r :: rs).length (ulogCore pcDone)) := by
    intro x hx
    have hm : (r :: rs).length ≠ 0 ∧ x = ulogCore pcDone := by
      simpa only [List.mem_replicate] using hx
    exact Or.inl hm.2
  have holdHead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcell : PayloadCell cell := hleft cell (by simp)
  have hleftTail : PayloadPathSafe leftTape := by
    intro x hx
    exact hleft x (by simp [hx])
  have hscan' : MoveScanSafe
      (dynamicMatchedRuleMovePath rs input leftTape ++ [cell]) := by
    simpa [dynamicMatchedRuleMovePath_cons] using hscan
  have hcleanup := reaches_moveLeftInternal_cleanup
    ((ULogBytecode.encodeRule r).map codeTape)
    (dynamicMatchedRuleMovePath rs input leftTape)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) outer cell (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail)
    hscan' hcell holdHead
    (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hclock)
    hpc (Or.inr rfl)
    (by simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hprogram)
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (dynamicMatchedRuleMovePath rs input (cell :: leftTape))
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
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleftEq := matchedRuleLeft_eq r rs outer
    rw [hmove] at hleftEq
    rw [hmove]
    rw [dynamicMatchedRuleMovePath_cons]
    rw [hleftEq]
    simpa [dynamicRuleProgramPath, dynamicMatchedRuleMovePath,
      ruleProgramPath, List.append_assoc] using hcleanup
  have hall := reaches_trans haction hcleanup'
  rw [cleanedCycleLeft_dynamicRuleProgramPath leftTape hleftTail] at hall
  exact hall

theorem chooseSlot_reaches_dynamicRuleSource (slot : Bool)
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (hhead : choiceHead head = true) (right : List Tape) :
    ∃ branchStart,
      oneStepAt (ULogBytecode.slotIndex slot)
          (.running .chooseSlot
            ⟨dynamicRuleReturnPath leftTape rules input ++
                ulogCore pcMark :: outer,
              head, right⟩) = branchStart ∧
        Reaches branchStart
          (dynamicRuleSourceStarted slot leftTape rules input outer head right) := by
  let path := dynamicRuleReturnPath leftTape rules input
  have hp : path ≠ [] := dynamicRuleReturnPath_ne_nil leftTape rules input
  have hreach := reaches_dynamicRuleSourceStarted slot leftTape hleft rules
    hrules input outer head right
  cases hslot : slot with
  | false =>
      refine ⟨.running (.ruleSeekChoice false)
          (beforeLeftPath path outer (ulogCore pcMark) (head :: right)),
        ?_, ?_⟩
      · cases he : path with
        | nil => exact (hp he).elim
        | cons x xs =>
            have hpathEq : dynamicRuleReturnPath leftTape rules input =
                x :: xs := by simpa [path] using he
            rw [hpathEq]
            simpa [ULogBytecode.slotIndex, hslot, path,
              beforeLeftPath, he,
              List.append_assoc] using
              (oneStepAt_chooseSlot_zero head hhead
                (xs ++ ulogCore pcMark :: outer) x right)
      · simpa [hslot, path] using hreach
  | true =>
      refine ⟨.running (.ruleSeekChoice true)
          (beforeLeftPath path outer (ulogCore pcMark) (head :: right)),
        ?_, ?_⟩
      · cases he : path with
        | nil => exact (hp he).elim
        | cons x xs =>
            have hpathEq : dynamicRuleReturnPath leftTape rules input =
                x :: xs := by simpa [path] using he
            rw [hpathEq]
            simpa [ULogBytecode.slotIndex, hslot, path,
              beforeLeftPath, he,
              List.append_assoc] using
              (oneStepAt_chooseSlot_one head hhead
                (xs ++ ulogCore pcMark :: outer) x right)
      · simpa [hslot, path] using hreach

end PakFixedPolyomino.ULogBootstrapExecution
