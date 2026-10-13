import PakFixedPolyomino.ULogRuleCursorHistory

/-! Canonical cursor history and its exact successful-cleanup decomposition. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def initialRuleCursor (rules : List ULogBytecode.RuleCode) : RuleCursorData :=
  ⟨0, List.replicate (rules.length - 1) (ulogCore pcDone), sourceBoundary⟩

theorem mismatchPrefixTrace_canonical_shape
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {final : RuleCursorData} {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ rest)) skip rest final)
    (hrest : rest ≠ []) :
    final.done = skip.length ∧
      final.boundary = boundaryAfter sourceBoundary skip ∧
        final.path = List.replicate (rest.length - 1) (ulogCore pcDone) ++
          mismatchHistory sourceBoundary skip := by
  have h := mismatchPrefixTrace_shape slot current actual programToHead runtime
    trace hrest ([] : List Tape) (by simp [initialRuleCursor])
  simpa [initialRuleCursor] using h

theorem matchedRuleLeftAt_eq (r : ULogBytecode.RuleCode)
    (boundary : ULogLetter) (base : List Tape) :
    matchedMoveLeft r.action.write r.action.target r.action.move
        (matchedReadLeftAt r.slot r.source r.read boundary base) =
      ((ULogBytecode.encodeRule r).map codeTape).reverse ++
        ulogCore boundary :: base := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [matchedMoveLeft, matchedReadLeftAt, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, encodeMove_eq,
    codeTape, List.map_append, List.reverse_append, List.append_assoc]

def cursorCleanupTerminal (skip : List ULogBytecode.RuleCode) : Tape :=
  match skip with
  | [] => ulogCore sourceBoundary
  | _ :: _ => ulogCore codeOne

def cursorCleanupProgramPrefix (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) : List Tape :=
  match skip with
  | [] => (ULogBytecode.encodeRule r).map codeTape
  | _ :: _ =>
      (((ULogBytecode.encodeRule r).map codeTape).reverse ++
        ulogCore (boundaryAfter sourceBoundary skip) ::
          (mismatchHistory sourceBoundary skip).tail.reverse).reverse

def cursorCleanupPcPath (skip rest : List ULogBytecode.RuleCode) :
    List Tape :=
  List.replicate skip.length (ulogCore codeZero) ++
    List.replicate rest.length (ulogCore pcDone)

theorem matchedCursor_cleanup_decomposition
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {final : RuleCursorData} (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (outer : List Tape) :
    matchedMoveLeft r.action.write r.action.target r.action.move
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++
              ulogCore pcMark :: outer)) =
      (cursorCleanupProgramPrefix skip r).reverse ++
        cursorCleanupTerminal skip ::
          (cursorCleanupPcPath skip (r :: rs)).reverse ++
            ulogCore pcMark :: outer := by
  rcases mismatchPrefixTrace_canonical_shape slot current actual
    programToHead runtime trace (by simp) with
    ⟨hdone, hboundary, hpath⟩
  rw [matchedRuleLeftAt_eq, hdone, hboundary, hpath]
  cases skip with
  | nil =>
      simp [cursorCleanupProgramPrefix, cursorCleanupTerminal,
        cursorCleanupPcPath, mismatchHistory, boundaryAfter,
        List.reverse_append, List.replicate_succ,
        List.append_assoc]
  | cons s ss =>
      have hsourceNe : sourceBoundary ≠ sourceBoundaryZero := by decide
      simp [cursorCleanupProgramPrefix, cursorCleanupTerminal,
        cursorCleanupPcPath, mismatchHistory, skippedRuleSegment,
        restoredBoundaryCell, hsourceNe, List.reverse_append,
        List.replicate_succ, List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
