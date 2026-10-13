import PakFixedPolyomino.ULogDynamicRuleLookup

/-! Successful source/read decoding with an evolving simulated left tape. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def dynamicMatchedRuleMovePath (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (leftTape : List Tape) : List Tape :=
  matchedRuleMovePath rs input ++ leftTape.reverse

def dynamicFirstRuleCorridor (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (leftTape : List Tape) (head : Tape)
    (runtimePrefix : List Tape) : List Tape :=
  ((ULogBytecode.encodeNatField r.read ++ [r.slot] ++
      ULogBytecode.encodeAction r.action ++ ULogBytecode.encodeRules rs).map
        codeTape) ++
    (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
      head :: runtimePrefix

theorem dynamicRuleSourceStarted_cons_eq (slot : Bool)
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (left : List Tape) (head : Tape) (runtimePrefix suffix : List Tape) :
    dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtimePrefix ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      sourceCompareStart slot r.source 0
        (dynamicFirstRuleCorridor r rs input leftTape head runtimePrefix)
        (ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
        suffix := by
  rcases r with ⟨source, read, ruleSlot, action⟩
  cases source <;>
    simp [dynamicRuleSourceStarted, sourceCompareStart,
      dynamicFirstRuleCorridor, ULogBytecode.encodeRules,
      ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
      List.replicate_succ, List.map_append, List.append_assoc,
      sourceCompareScanPath, codeTape]

theorem reaches_dynamicRuleSourceMatch_read (slot : Bool)
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (left : List Tape) (head : Tape) (runtimePrefix suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtimePrefix)) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtimePrefix ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (sourceReadStarted slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot ::
            encodedActionPath r.action.write r.action.target r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
          head :: runtimePrefix)
        suffix) := by
  rw [dynamicRuleSourceStarted_cons_eq]
  have h₀ := reaches_sourceMatchRestored slot r.source
    (dynamicFirstRuleCorridor r rs input leftTape head runtimePrefix)
    hcorridor
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left) suffix
  have hcorridorEq :
      dynamicFirstRuleCorridor r rs input leftTape head runtimePrefix =
        codeTape (unaryFieldFirst r.read) ::
          ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
            codeTape r.slot ::
              encodedActionPath r.action.write r.action.target r.action.move
                (dynamicMatchedRuleMovePath rs input leftTape) ++
              head :: runtimePrefix) := by
    rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
    cases read <;>
      simp [dynamicFirstRuleCorridor, dynamicMatchedRuleMovePath,
        matchedRuleMovePath, encodedActionPath,
        ULogBytecode.encodeNatField, ULogBytecode.encodeAction,
        encodeMove_eq, moveBits, unaryFieldFirst, List.replicate_succ,
        List.map_append, codeTape, List.append_assoc]
  have h₁ : Reaches
      (sourceFieldRestored slot r.source
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        (dynamicFirstRuleCorridor r rs input leftTape head runtimePrefix)
        suffix)
      (sourceReadStarted slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot ::
            encodedActionPath r.action.write r.action.target r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
            head :: runtimePrefix)
        suffix) := by
    rw [hcorridorEq]
    exact reaches_sourceFieldRestored_read slot r.source
      (unaryFieldFirst r.read)
      (List.replicate (r :: rs).length (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
        codeTape r.slot ::
          encodedActionPath r.action.write r.action.target r.action.move
            (dynamicMatchedRuleMovePath rs input leftTape) ++
          head :: runtimePrefix)
      suffix
  exact reaches_trans h₀ h₁

end PakFixedPolyomino.ULogBootstrapExecution
