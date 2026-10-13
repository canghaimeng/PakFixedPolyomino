import PakFixedPolyomino.ULogRuleListRestoration

/-! Both source mismatch directions advance an arbitrary rule-list cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem sourceShortRestorePath_safe (done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor) :
    MismatchRestorePathSafe (sourceShortRestorePath done corridor) := by
  intro x hx
  unfold sourceShortRestorePath at hx
  rcases List.mem_append.mp hx with hp | hs
  · have hp' : x ∈ sourceShortFinishPath done corridor := by
      simpa using hp
    unfold sourceShortFinishPath at hp'
    rcases List.mem_append.mp hp' with hc | hm
    · have h := hcorridor x hc
      exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2, h.2.2.2.2.1⟩
    · have heq : x = ulogCore stateMark :=
        (by simpa only [List.mem_replicate] using hm :
          done ≠ 0 ∧ x = ulogCore stateMark).2
      rw [heq]
      decide
  · simp only [List.mem_cons, List.mem_replicate] at hs
    rcases hs with rfl | hs
    · decide
    · rw [hs.2]
      decide

theorem reaches_ruleCursorSourceShort_advance
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++
        List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++
              ulogCore pcMark :: outer)
        after right) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  have hrestore := reaches_atBitsSourceShort_restore slot r rs programPath
    extra boundary pcBase suffix hcorridor
  have hrestored := ruleSourceShort_restored r rs programPath suffix extra
    hcorridor hreadBoundary
  have hrestored' :
      (sourceShortRestorePath r.source
        (ruleContinuationCorridor r rs programPath)).reverse.map
          restoreMismatchCell ++
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
        codeTape ++ after :: right := by
    have hafter' := congrArg
      (fun xs =>
        (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ xs) hafter
    calc
      _ = (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++
          (programPath ++
            List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) := by
        simpa [List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have hadvance := reaches_restoreMismatchAdvanceRule slot done path hpath
    boundary hboundary
    (sourceShortRestorePath r.source
      (ruleContinuationCorridor r rs programPath))
    (sourceShortRestorePath_safe r.source
      (ruleContinuationCorridor r rs programPath) hcorridor)
    (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
    r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
    outer after right hrestored'
  have hrestore' : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceShortRestorePath r.source
          (ruleContinuationCorridor r rs programPath))
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
  exact reaches_trans hrestore' hadvance

theorem reaches_ruleCursorSourceLong_advance
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix = after :: right) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++
              ulogCore pcMark :: outer)
        after right) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  have hrestore := reaches_atBitsSourceLong_restore slot r rs programPath
    current extra hsource boundary pcBase suffix hcorridor
  have hrestored := ruleSourceLong_restored r rs programPath suffix
    current extra hsource hcorridor hreadBoundary
  have hrestored' :
      (sourceLongRestorePath extra current
        (ruleContinuationCorridor r rs programPath)).reverse.map
          restoreMismatchCell ++ (ulogCore stateOne :: suffix) =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
        codeTape ++ after :: right := by
    have hafter' := congrArg
      (fun xs =>
        (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ xs) hafter
    calc
      _ = (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++
          (programPath ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
        simpa [List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have hadvance := reaches_restoreMismatchAdvanceRule slot done path hpath
    boundary hboundary
    (sourceLongRestorePath extra current
      (ruleContinuationCorridor r rs programPath))
    (sourceLongRestorePath_safe extra current
      (ruleContinuationCorridor r rs programPath) hcorridor)
    (ulogCore stateOne :: suffix)
    r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
    outer after right hrestored'
  have hrestore' : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceLongRestorePath extra current
          (ruleContinuationCorridor r rs programPath))
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
  exact reaches_trans hrestore' hadvance

end PakFixedPolyomino.ULogBootstrapExecution
