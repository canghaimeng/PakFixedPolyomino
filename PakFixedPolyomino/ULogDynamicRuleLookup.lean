import PakFixedPolyomino.ULogDynamicRuntimeExecution

/-! Rule lookup across the evolving left side of the simulated tape. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def dynamicRuleReturnPath (leftTape : List Tape)
    (rules : List ULogBytecode.RuleCode) (input : List Bool) : List Tape :=
  leftTape ++ ruleReturnPath rules input

theorem dynamicRuleReturnPath_ne_nil (leftTape : List Tape)
    (rules : List ULogBytecode.RuleCode) (input : List Bool) :
    dynamicRuleReturnPath leftTape rules input ≠ [] := by
  simp [dynamicRuleReturnPath, ruleReturnPath]

theorem dynamicRuleReturnPath_pass (slot : Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (input : List Bool)
    (x : Tape) (hx : x ∈ dynamicRuleReturnPath leftTape rules input)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleSeekChoice slot) ⟨y :: left, x, right⟩) =
      .running (.ruleSeekChoice slot) ⟨left, y, x :: right⟩ := by
  rcases List.mem_append.mp hx with hdynamic | hfixed
  · apply ruleSeekChoice_pass slot x
    rcases hleft x hdynamic with rfl | rfl | rfl <;> simp
  · exact ruleReturnPath_pass slot rules input x hfixed left y right

theorem dynamicRuleReturnPath_reverse (leftTape : List Tape)
    (rules : List ULogBytecode.RuleCode) (input : List Bool) :
    (dynamicRuleReturnPath leftTape rules input).reverse =
      List.replicate rules.length (ulogCore pcDone) ++
        codeTape true :: (ULogBytecode.encodeRules rules).map codeTape ++
          (payloadProgramPrefix input).reverse ++ leftTape.reverse := by
  simp [dynamicRuleReturnPath, List.reverse_append, ruleReturnPath_reverse,
    List.append_assoc]

def dynamicRuleSourceStarted (slot : Bool) (leftTape : List Tape)
    (rules : List ULogBytecode.RuleCode) (input : List Bool)
    (left : List Tape) (head : Tape) (right : List Tape) : Result :=
  match ULogBytecode.encodeRules rules with
  | [] => .rejected
  | b :: bs =>
      .running (.fieldCompare .source slot)
        ⟨ulogCore sourceBoundary ::
            List.replicate rules.length (ulogCore pcDone) ++
              ulogCore pcMark :: left,
          codeTape b,
          bs.map codeTape ++ (payloadProgramPrefix input).reverse ++
            leftTape.reverse ++ head :: right⟩

theorem reaches_dynamicRuleSourceStarted (slot : Bool)
    (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (left : List Tape) (head : Tape)
    (right : List Tape) :
    Reaches
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath leftTape rules input) left
          (ulogCore pcMark) (head :: right)))
      (dynamicRuleSourceStarted slot leftTape rules input left head right) := by
  let path := dynamicRuleReturnPath leftTape rules input
  have h₀ : Reaches
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath path left (ulogCore pcMark) (head :: right)))
      (.running (.ruleSeekChoice slot)
        (afterLeftPath path left (ulogCore pcMark) (head :: right))) :=
    ⟨path.length, run_left_path_of (.ruleSeekChoice slot) path
      (by
        intro x hx l y r
        exact dynamicRuleReturnPath_pass slot leftTape hleft rules input x
          (by simpa [path] using hx) l y r)
      left (ulogCore pcMark) (head :: right)⟩
  have h₁ : Reaches
      (.running (.ruleSeekChoice slot)
        (afterLeftPath path left (ulogCore pcMark) (head :: right)))
      (.running (.ruleCountSeek slot)
        (beforeRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right))) := by
    apply reaches_step
    cases rules with
    | nil => exact (hrules rfl).elim
    | cons r rs =>
        simp [path, afterLeftPath, beforeRightPath,
          dynamicRuleReturnPath_reverse, ruleSeekChoice_mark,
          codeTape, List.replicate_succ, List.append_assoc]
  have h₂ : Reaches
      (.running (.ruleCountSeek slot)
        (beforeRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right)))
      (.running (.ruleCountSeek slot)
        (afterRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right))) := by
    refine ⟨(List.replicate rules.length (ulogCore pcDone)).length, ?_⟩
    exact run_right_path_of (.ruleCountSeek slot)
      (List.replicate rules.length (ulogCore pcDone)) (by
        intro x hx l y r
        have hm : rules.length ≠ 0 ∧ x = ulogCore pcDone := by
          simpa only [List.mem_replicate] using hx
        rw [hm.2]
        exact ruleCountSeek_done slot l y r)
      (ulogCore pcMark :: left) (ulogCore codeOne)
      ((ULogBytecode.encodeRules rules).map codeTape ++
        (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
          head :: right)
  have henc : ULogBytecode.encodeRules rules ≠ [] :=
    encodeRules_ne_nil hrules
  have h₃ : Reaches
      (.running (.ruleCountSeek slot)
        (afterRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right)))
      (dynamicRuleSourceStarted slot leftTape rules input left head right) := by
    cases he : ULogBytecode.encodeRules rules with
    | nil => exact (henc he).elim
    | cons b bs =>
        apply reaches_step
        simpa [dynamicRuleSourceStarted, afterRightPath, he,
          List.replicate_succ', List.append_assoc] using
          (ruleCountSeek_end slot
            (List.replicate rules.length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
            (codeTape b)
            (bs.map codeTape ++ (payloadProgramPrefix input).reverse ++
              leftTape.reverse ++ head :: right))
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

end PakFixedPolyomino.ULogBootstrapExecution
