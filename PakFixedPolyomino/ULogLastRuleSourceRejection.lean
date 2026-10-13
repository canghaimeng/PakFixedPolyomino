import PakFixedPolyomino.ULogLastRuleSlotRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorSourceShort_last_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r [] programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++
        List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  have hrestore := reaches_atBitsSourceShort_restore slot r [] programPath
    extra boundary pcBase suffix hcorridor
  have hrestored := ruleSourceShort_restored r [] programPath suffix extra
    hcorridor hreadBoundary
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (sourceShortRestorePath r.source
        (ruleContinuationCorridor r [] programPath)).reverse.map
          restoreMismatchCell ++
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programPath ++
            List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) := by
        simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have hreject := reaches_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary
    (sourceShortRestorePath r.source
      (ruleContinuationCorridor r [] programPath))
    (sourceShortRestorePath_safe r.source
      (ruleContinuationCorridor r [] programPath) hcorridor)
    (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
    r outer after right hrestored' hzero hone
  have hrestore' : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary :: pcBase)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceShortRestorePath r.source
          (ruleContinuationCorridor r [] programPath))
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse
        outer boundary
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
    have hreturn : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: path).reverse ≠ [] := by simp
    cases he : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: path).reverse with
    | nil => exact (hreturn he).elim
    | cons x xs =>
        simpa [pcBase, restoreAdvanceStarted, he, beforeLeftPath,
          List.append_assoc] using hrestore
  exact reaches_trans hrestore' hreject

theorem reaches_ruleCursorSourceLong_last_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programPath : List Tape)
    (current extra : ℕ) (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r [] programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      .rejected := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  have hrestore := reaches_atBitsSourceLong_restore slot r [] programPath
    current extra hsource boundary pcBase suffix hcorridor
  have hrestored := ruleSourceLong_restored r [] programPath suffix
    current extra hsource hcorridor hreadBoundary
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (sourceLongRestorePath extra current
        (ruleContinuationCorridor r [] programPath)).reverse.map
          restoreMismatchCell ++ (ulogCore stateOne :: suffix) =
      (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programPath ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
        simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have hreject := reaches_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary
    (sourceLongRestorePath extra current
      (ruleContinuationCorridor r [] programPath))
    (sourceLongRestorePath_safe extra current
      (ruleContinuationCorridor r [] programPath) hcorridor)
    (ulogCore stateOne :: suffix) r outer after right hrestored' hzero hone
  have hrestore' : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary :: pcBase)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceLongRestorePath extra current
          (ruleContinuationCorridor r [] programPath))
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse
        outer boundary (ulogCore stateOne :: suffix)) := by
    have hreturn : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: path).reverse ≠ [] := by simp
    cases he : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: path).reverse with
    | nil => exact (hreturn he).elim
    | cons x xs =>
        simpa [pcBase, restoreAdvanceStarted, he, beforeLeftPath,
          List.append_assoc] using hrestore
  exact reaches_trans hrestore' hreject

end PakFixedPolyomino.ULogBootstrapExecution
