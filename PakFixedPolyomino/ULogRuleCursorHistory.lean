import PakFixedPolyomino.ULogRuleListMatchedAction

/-! Closed-form boundary/path shape of an arbitrary mismatch-prefix trace. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def restoredBoundaryCell (boundary : ULogLetter) : Tape :=
  if boundary = sourceBoundaryZero then ulogCore codeZero
  else ulogCore codeOne

def skippedRuleSegment (boundary : ULogLetter)
    (r : ULogBytecode.RuleCode) : List Tape :=
  restoredBoundaryCell boundary :: (mismatchRulePrefix r).tail.reverse

def boundaryAfter : ULogLetter → List ULogBytecode.RuleCode → ULogLetter
  | boundary, [] => boundary
  | _, r :: rs => boundaryAfter
      (nextSourceBoundary (moveSecond r.action.move)) rs

def mismatchHistory : ULogLetter → List ULogBytecode.RuleCode → List Tape
  | _, [] => []
  | boundary, r :: rs =>
      skippedRuleSegment boundary r ++
        mismatchHistory (nextSourceBoundary (moveSecond r.action.move)) rs

theorem advanceMismatchPath_eq (r : ULogBytecode.RuleCode)
    (boundary : ULogLetter) (path : List Tape) :
    advanceMismatchPath r boundary path =
      path ++ skippedRuleSegment boundary r := by
  rfl

theorem mismatchPrefixTrace_shape
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final)
    (hrest : rest ≠ []) (history : List Tape)
    (hpath : start.path =
      List.replicate ((skip ++ rest).length - 1) (ulogCore pcDone) ++
        history) :
    final.done = start.done + skip.length ∧
      final.boundary = boundaryAfter start.boundary skip ∧
        final.path =
          List.replicate (rest.length - 1) (ulogCore pcDone) ++
            history ++ mismatchHistory start.boundary skip := by
  induction trace generalizing history with
  | nil c rest =>
      simp [boundaryAfter, mismatchHistory] at hpath ⊢
      exact hpath
  | cons c r skip rest final ready next ih =>
      have hremaining : skip ++ rest ≠ [] := ready.remaining_ne
      have hrep : List.replicate (((r :: skip) ++ rest).length - 1)
            (ulogCore pcDone) =
          ulogCore pcDone ::
            List.replicate ((skip ++ rest).length - 1)
              (ulogCore pcDone) := by
        cases he : skip ++ rest with
        | nil => exact (hremaining he).elim
        | cons a xs =>
            simp [List.cons_append, he, List.replicate_succ]
      have htail : ready.tail =
          List.replicate ((skip ++ rest).length - 1) (ulogCore pcDone) ++
            history := by
        rw [ready.path_eq, hrep] at hpath
        exact List.cons.inj hpath |>.2
      have hnextPath :
          (advanceRuleCursor c r ready.tail).path =
            List.replicate ((skip ++ rest).length - 1)
                (ulogCore pcDone) ++
              (history ++ skippedRuleSegment c.boundary r) := by
        simp [advanceRuleCursor, advanceMismatchPath_eq, htail,
          List.append_assoc]
      have hi := ih hrest (history ++ skippedRuleSegment c.boundary r)
        hnextPath
      rcases hi with ⟨hdone, hboundary, hfinalPath⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [advanceRuleCursor] at hdone ⊢
        omega
      · simpa [advanceRuleCursor, boundaryAfter] using hboundary
      · simpa [advanceRuleCursor, boundaryAfter, mismatchHistory,
          List.append_assoc] using hfinalPath

end PakFixedPolyomino.ULogBootstrapExecution
