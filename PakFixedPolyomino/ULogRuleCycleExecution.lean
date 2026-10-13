import PakFixedPolyomino.ULogCycleRefinement

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def ruleProgramPath (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool) : List Tape :=
  (ULogBytecode.encodeRule r).map codeTape ++ matchedRuleMovePath rs input

@[simp] theorem restoreProgramCell_codeTape (b : Bool) :
    restoreProgramCell (codeTape b) = codeTape b := by
  cases b <;> decide

@[simp] theorem restoreProgramCell_payloadEnd :
    restoreProgramCell (ulogCore payloadEnd) = ulogCore payloadEnd := by
  decide

@[simp] theorem restoreProgramCell_payloadDone :
    restoreProgramCell (ulogCore payloadDone) = ulogCore payloadDone := by
  decide

@[simp] theorem restoreProgramCell_payloadStartDone :
    restoreProgramCell (ulogCore payloadStartDone) =
      ulogCore payloadStartDone := by
  decide

@[simp] theorem restoreProgramCell_payloadStartOne :
    restoreProgramCell (ulogCore payloadStartOne) =
      ulogCore payloadStartOne := by
  decide

@[simp] theorem restoreProgramCell_comp_codeTape :
    restoreProgramCell ∘ codeTape = codeTape := by
  funext b
  exact restoreProgramCell_codeTape b

theorem restoreProgramCell_payloadProgramPrefix (input : List Bool) :
    (payloadProgramPrefix input).map restoreProgramCell =
      payloadProgramPrefix input := by
  cases input with
  | nil => simp [payloadProgramPrefix]
  | cons b bs => simp [payloadProgramPrefix]

theorem restoreProgramCell_ruleProgramPath
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) :
    (ruleProgramPath r rs input).map restoreProgramCell =
      ruleProgramPath r rs input := by
  simp [ruleProgramPath, matchedRuleMovePath, List.map_append,
    List.map_reverse, restoreProgramCell_comp_codeTape,
    restoreProgramCell_payloadProgramPrefix]

@[simp] theorem restorePcCell_done :
    restorePcCell (ulogCore pcDone) = ulogCore pcDone := by
  decide

theorem cleanedCycleLeft_ruleProgramPath
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (outer : List Tape) :
    cleanedCycleLeft
        (List.replicate (r :: rs).length (ulogCore pcDone))
        (ruleProgramPath r rs input) outer =
      ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: outer := by
  simp [cleanedCycleLeft, ruleProgramPath, matchedRuleMovePath,
    ruleReturnPath, ULogBytecode.encodeRules, List.map_append,
    List.map_reverse, List.reverse_append,
    restoreProgramCell_comp_codeTape,
    restoreProgramCell_payloadProgramPrefix, codeTape, List.append_assoc]

theorem reaches_matchedRuleCodeAtMost_stay_cycle
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
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
  have haction := reaches_matchedRuleCodeAtMostState r rs input extra
    hsource hread hwrite htargetLower runtime hsourcePath hreadPath hwritePath
    htargetPath left tail
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
    (matchedRuleMovePath rs input)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) left (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail)
    hscan (by simpa [ruleProgramPath] using hclock) hpc (Or.inr rfl)
    (by simpa [ruleProgramPath] using hprogram) hnewHead
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (matchedRuleMovePath rs input)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (ruleProgramPath r rs input) left,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail⟩) := by
    have hleft := matchedRuleLeft_eq r rs left
    rw [hmove] at hleft
    rw [hmove]
    rw [hleft]
    simpa [ruleProgramPath] using hcleanup
  have hall := reaches_trans haction hcleanup'
  rw [cleanedCycleLeft_ruleProgramPath] at hall
  exact hall

theorem reaches_matchedRuleCodeAtLeast_stay_cycle
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
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running .cycleStart
        ⟨ruleReturnPath (r :: rs) input ++ ulogCore pcMark :: left,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
  have haction := reaches_matchedRuleCodeAtLeastState r rs input growth
    htarget hread hwrite htargetLower runtime hsourcePath hreadPath hwritePath
    htargetPath left tail
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
    (matchedRuleMovePath rs input)
    (List.replicate (r :: rs).length (ulogCore pcDone))
    (ulogCore sourceBoundary) left (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
    hscan (by simpa [ruleProgramPath] using hclock) hpc (Or.inr rfl)
    (by simpa [ruleProgramPath] using hprogram) hnewHead
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (matchedRuleMovePath rs input)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running .cycleStart
        ⟨cleanedCycleLeft
            (List.replicate (r :: rs).length (ulogCore pcDone))
            (ruleProgramPath r rs input) left,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    have hleft := matchedRuleLeft_eq r rs left
    rw [hmove] at hleft
    rw [hmove]
    rw [hleft]
    simpa [ruleProgramPath] using hcleanup
  have hall := reaches_trans haction hcleanup'
  rw [cleanedCycleLeft_ruleProgramPath] at hall
  exact hall

end PakFixedPolyomino.ULogBootstrapExecution
