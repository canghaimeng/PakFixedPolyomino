import PakFixedPolyomino.ULogFirstRuleAdvance

/-! Source comparison and mismatch restoration at an arbitrary rule-list cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def atBitsTail (q : State) (bits : List Bool) (left tail : List Tape) : Result :=
  match tail with
  | [] => .rejected
  | after :: right => atBits q bits left after right

def ruleContinuationCorridor (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programPath : List Tape) : List Tape :=
  ((ULogBytecode.encodeNatField r.read ++ [r.slot] ++
      ULogBytecode.encodeAction r.action ++ ULogBytecode.encodeRules rs).map
        codeTape) ++ programPath

theorem atBitsTail_encodeRules_cons_source (slot : Bool)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (current : ℕ) (programPath left suffix : List Tape) :
    atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) left
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      sourceCompareStartAgainst slot r.source current 0
        (ruleContinuationCorridor r rs programPath) left suffix := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  cases source <;> cases current <;> cases programPath <;>
    simp [atBitsTail, atBits, sourceCompareStartAgainst,
      ruleContinuationCorridor, ULogBytecode.encodeRules,
      ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      ULogBytecode.encodeNatField, sourceCompareScanPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]

theorem reaches_atBitsSourceShort_restore (slot : Bool)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programPath : List Tape) (extra : ℕ) (boundary : ULogLetter)
    (pcBase suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath)) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  rw [atBitsTail_encodeRules_cons_source]
  have hcommon := reaches_sourceCompareCommon slot r.source
    (r.source + extra + 1) 0
    (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary :: pcBase) suffix
  have hcommon' : Reaches
      (sourceCompareStartAgainst slot r.source (r.source + extra + 1) 0
        (ruleContinuationCorridor r rs programPath)
        (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (ruleContinuationCorridor r rs programPath)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa [Nat.min_eq_left, Nat.add_assoc] using hcommon
  have hmismatch := reaches_sourceShortMismatch_restore slot r.source extra
    (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary) pcBase suffix
  have hmismatch' : Reaches
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (ruleContinuationCorridor r rs programPath)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
    simpa [List.append_assoc] using hmismatch
  exact reaches_trans hcommon' hmismatch'

theorem reaches_atBitsSourceLong_restore (slot : Bool)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programPath : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (boundary : ULogLetter) (pcBase suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath)) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
  rw [atBitsTail_encodeRules_cons_source]
  have hcommon := reaches_sourceCompareCommon slot r.source current 0
    (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary :: pcBase) suffix
  have hcommon' : Reaches
      (sourceCompareStartAgainst slot r.source current 0
        (ruleContinuationCorridor r rs programPath)
        (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (ruleContinuationCorridor r rs programPath)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa [hsource, Nat.min_eq_right, Nat.add_assoc] using hcommon
  have hmismatch := reaches_sourceLongMismatch_restore slot current extra
    (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary) pcBase suffix
  have hmismatch' : Reaches
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (ruleContinuationCorridor r rs programPath)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
    simpa [Nat.succ_eq_add_one, List.append_assoc] using hmismatch
  exact reaches_trans hcommon' hmismatch'

end PakFixedPolyomino.ULogBootstrapExecution
