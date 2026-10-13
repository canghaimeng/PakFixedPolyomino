import PakFixedPolyomino.ULogRuleListSourceComparison

/-! Exact arbitrary-cursor RuleCode reconstruction after source mismatch. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem ruleSourceShort_restored
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programPath suffix : List Tape) (extra : ℕ)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    (sourceShortRestorePath r.source
        (ruleContinuationCorridor r rs programPath)).reverse.map
          restoreMismatchCell ++
        ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ programPath ++
        List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix := by
  rw [sourceShortRestorePath_map r.source extra
    (ruleContinuationCorridor r rs programPath) hcorridor
    hreadBoundary suffix]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [ruleContinuationCorridor, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, codeTape,
    List.map_append, List.append_assoc]

theorem ruleSourceLong_restored
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programPath suffix : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    (sourceLongRestorePath extra current
        (ruleContinuationCorridor r rs programPath)).reverse.map
          restoreMismatchCell ++ ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ programPath ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix := by
  rw [sourceLongRestorePath_map extra current
    (ruleContinuationCorridor r rs programPath) hcorridor
    hreadBoundary suffix]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  change source = current + extra + 1 at hsource
  subst source
  simp [ruleContinuationCorridor, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, codeTape,
    List.map_append, List.append_assoc, Nat.add_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
