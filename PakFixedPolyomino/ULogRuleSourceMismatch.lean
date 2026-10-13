import PakFixedPolyomino.ULogMismatchRestorationMaps

/-! Complete RuleCode source-field mismatch traces for both inequalities. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem dynamicRuleSourceStarted_cons_against_eq (slot : Bool)
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (current : ℕ) (left : List Tape) (head : Tape)
    (runtime suffix : List Tape) :
    dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      sourceCompareStartAgainst slot r.source current 0
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
        suffix := by
  rcases r with ⟨source, read, ruleSlot, action⟩
  cases source <;> cases current <;>
    simp [dynamicRuleSourceStarted, sourceCompareStartAgainst,
      dynamicFirstRuleCorridor, ULogBytecode.encodeRules,
      ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
      sourceCompareScanPath, List.replicate_succ,
      List.map_append, List.append_assoc, codeTape]

theorem reaches_dynamicRuleSourceShort_restore (slot : Bool)
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (extra : ℕ) (left : List Tape) (head : Tape)
    (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime)) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (dynamicFirstRuleCorridor r rs input leftTape head runtime))
          (List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
          (ulogCore sourceBoundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  rw [dynamicRuleSourceStarted_cons_against_eq]
  have hcommon := reaches_sourceCompareCommon slot r.source
    (r.source + extra + 1) 0
    (dynamicFirstRuleCorridor r rs input leftTape head runtime) hcorridor
    (ulogCore sourceBoundary ::
      List.replicate (r :: rs).length (ulogCore pcDone) ++
        ulogCore pcMark :: left)
    suffix
  have hcommon' : Reaches
      (sourceCompareStartAgainst slot r.source (r.source + extra + 1) 0
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
        suffix)
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore sourceBoundary ::
            List.replicate (r :: rs).length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
        suffix) := by
    simpa [Nat.min_eq_left, Nat.add_assoc] using hcommon
  have hmismatch := reaches_sourceShortMismatch_restore slot r.source extra
    (dynamicFirstRuleCorridor r rs input leftTape head runtime) hcorridor
    (ulogCore sourceBoundary)
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left)
    suffix
  have hmismatch' : Reaches
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore sourceBoundary ::
            List.replicate (r :: rs).length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (dynamicFirstRuleCorridor r rs input leftTape head runtime))
          (List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
          (ulogCore sourceBoundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
    simpa [List.append_assoc] using hmismatch
  exact reaches_trans hcommon' hmismatch'

theorem reaches_dynamicRuleSourceLong_restore (slot : Bool)
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (current extra : ℕ) (hsource : r.source = current + extra + 1)
    (left : List Tape) (head : Tape) (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime)) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (dynamicFirstRuleCorridor r rs input leftTape head runtime))
          (List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
          (ulogCore sourceBoundary)
          (ulogCore stateOne :: suffix))) := by
  rw [dynamicRuleSourceStarted_cons_against_eq]
  have hcommon := reaches_sourceCompareCommon slot r.source current 0
    (dynamicFirstRuleCorridor r rs input leftTape head runtime) hcorridor
    (ulogCore sourceBoundary ::
      List.replicate (r :: rs).length (ulogCore pcDone) ++
        ulogCore pcMark :: left)
    suffix
  have hcommon' : Reaches
      (sourceCompareStartAgainst slot r.source current 0
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
        suffix)
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore sourceBoundary ::
            List.replicate (r :: rs).length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
        suffix) := by
    simpa [hsource, Nat.min_eq_right, Nat.add_assoc] using hcommon
  have hmismatch := reaches_sourceLongMismatch_restore slot current extra
    (dynamicFirstRuleCorridor r rs input leftTape head runtime) hcorridor
    (ulogCore sourceBoundary)
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left)
    suffix
  have hmismatch' : Reaches
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore sourceBoundary ::
            List.replicate (r :: rs).length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (dynamicFirstRuleCorridor r rs input leftTape head runtime))
          (List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
          (ulogCore sourceBoundary) (ulogCore stateOne :: suffix))) := by
    simpa [Nat.succ_eq_add_one, List.append_assoc] using hmismatch
  exact reaches_trans hcommon' hmismatch'

end PakFixedPolyomino.ULogBootstrapExecution
