import PakFixedPolyomino.ULogRuleCursorInvariant

/-! Cursor-preserving source mismatch steps for arbitrary rule-list induction. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorSourceShort_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone ::
              advanceMismatchPath r boundary path).reverse ++
                ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  have htail : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hadvance := reaches_ruleCursorSourceShort_advance slot done
        (ulogCore pcDone :: path) hpath boundary hboundary r rs hrs
        programPath extra outer suffix hcorridor hreadBoundary after right he
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hadvance
      simpa [atBitsTail, he, List.append_assoc] using hadvance

theorem reaches_ruleCursorSourceLong_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone ::
              advanceMismatchPath r boundary path).reverse ++
                ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have htail : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hadvance := reaches_ruleCursorSourceLong_advance slot done
        (ulogCore pcDone :: path) hpath boundary hboundary r rs hrs
        programPath current extra hsource outer suffix hcorridor
        hreadBoundary after right he
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hadvance
      simpa [atBitsTail, he, List.append_assoc] using hadvance

end PakFixedPolyomino.ULogBootstrapExecution
