import PakFixedPolyomino.ULogDynamicCursorClockStayAtMost

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem boundaryAfter_append_singleton (boundary : ULogLetter)
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    boundaryAfter boundary (passed ++ [r]) =
      nextSourceBoundary (moveSecond r.action.move) := by
  induction passed generalizing boundary with
  | nil => simp [boundaryAfter]
  | cons s ss ih =>
      simp only [List.cons_append, boundaryAfter]
      exact ih _

theorem mismatchHistory_append_singleton (boundary : ULogLetter)
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    mismatchHistory boundary (passed ++ [r]) =
      mismatchHistory boundary passed ++
        skippedRuleSegment (boundaryAfter boundary passed) r := by
  induction passed generalizing boundary with
  | nil => simp [mismatchHistory, boundaryAfter]
  | cons s ss ih =>
      simp only [List.cons_append, mismatchHistory, boundaryAfter]
      rw [ih]
      simp [List.append_assoc]

theorem mismatchHistory_safe (boundary : ULogLetter)
    (skip : List ULogBytecode.RuleCode) :
    MismatchAdvancePathSafe (mismatchHistory boundary skip) := by
  induction skip generalizing boundary with
  | nil =>
      simp only [mismatchHistory]
      constructor <;> simp [MismatchBoundaryFree]
  | cons r rs ih =>
      have htail := mismatchRulePrefix_tail_safe r
      have hrest := ih (nextSourceBoundary (moveSecond r.action.move))
      constructor
      · intro x hx
        simp only [mismatchHistory, skippedRuleSegment, List.mem_append,
          List.mem_cons, List.mem_reverse] at hx
        rcases hx with (hb | hx) | hx
        · rw [hb]
          simp [restoredBoundaryCell]
          split <;> decide
        · exact htail.1 x hx
        · exact hrest.1 x hx
      · intro x hx
        simp only [mismatchHistory, skippedRuleSegment, List.mem_append,
          List.mem_cons, List.mem_reverse] at hx
        rcases hx with (hb | hx) | hx
        · rw [hb]
          simp [restoredBoundaryCell]
          split <;> decide
        · exact htail.2 x hx
        · exact hrest.2 x hx

def canonicalRuleCursor (passed remaining : List ULogBytecode.RuleCode) :
    RuleCursorData :=
  ⟨passed.length,
    List.replicate (remaining.length - 1) (ulogCore pcDone) ++
      mismatchHistory sourceBoundary passed,
    boundaryAfter sourceBoundary passed⟩

theorem canonicalRuleCursor_initial
    (rules : List ULogBytecode.RuleCode) :
    canonicalRuleCursor [] rules = initialRuleCursor rules := by
  simp [canonicalRuleCursor, initialRuleCursor, mismatchHistory, boundaryAfter]

theorem boundaryAfter_valid (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (skip : List ULogBytecode.RuleCode) :
    boundaryAfter boundary skip = sourceBoundary ∨
      boundaryAfter boundary skip = sourceBoundaryZero ∨
        boundaryAfter boundary skip = sourceBoundaryOne := by
  induction skip generalizing boundary with
  | nil => simpa [boundaryAfter] using hboundary
  | cons r rs ih =>
      exact ih _ (nextSourceBoundary_valid (moveSecond r.action.move))

theorem canonicalRuleCursor_path_cons
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (remaining : List ULogBytecode.RuleCode) (hremaining : remaining ≠ []) :
    (canonicalRuleCursor passed (r :: remaining)).path =
      ulogCore pcDone :: (canonicalRuleCursor passed remaining).path := by
  cases remaining with
  | nil => exact (hremaining rfl).elim
  | cons s ss =>
      simp [canonicalRuleCursor, List.replicate_succ]

theorem canonicalRuleCursor_path_safe
    (passed remaining : List ULogBytecode.RuleCode) :
    MismatchAdvancePathSafe (canonicalRuleCursor passed remaining).path := by
  have hhistory := mismatchHistory_safe sourceBoundary passed
  constructor
  · intro x hx
    simp only [canonicalRuleCursor, List.mem_append,
      List.mem_replicate] at hx
    rcases hx with hp | hh
    · rw [hp.2]
      decide
    · exact hhistory.1 x hh
  · intro x hx
    simp only [canonicalRuleCursor, List.mem_append,
      List.mem_replicate] at hx
    rcases hx with hp | hh
    · rw [hp.2]
      decide
    · exact hhistory.2 x hh

theorem advance_canonicalRuleCursor
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (remaining : List ULogBytecode.RuleCode) :
    advanceRuleCursor (canonicalRuleCursor passed (r :: remaining)) r
        (canonicalRuleCursor passed remaining).path =
      canonicalRuleCursor (passed ++ [r]) remaining := by
  unfold advanceRuleCursor canonicalRuleCursor
  simp only [advanceMismatchPath_eq]
  rw [mismatchHistory_append_singleton,
    boundaryAfter_append_singleton]
  simp [List.append_assoc]

structure RuleMismatchCertificate (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) : Prop where
  mismatch : ¬ RuleMatchesCursor slot current actual r
  actual_valid : actual < 3
  read_valid : r.read < 3
  source_corridor : SourceCompareCorridorSafe
    (cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime)
  read_boundary_free : ∀ x ∈
    cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime,
      x ≠ ulogCore readBoundary
  read_scan : ReadCorridorSafe (cursorReadScanPath r rs programToHead)
  read_restore : MismatchRestorePathSafe
    (readMismatchRestorePath r.source r.read
      (cursorReadScanPath r rs programToHead))
  slot_scan : ReadCorridorSafe
    (codeTape (!slot) :: encodedActionPath r.action.write
      r.action.target r.action.move (cursorMatchedMovePath rs programToHead))
  slot_restore : MismatchRestorePathSafe
    (slotMismatchRestorePath r.source r.read)
  program_restore : RestoreMismatchIdentity programToHead

inductive MismatchCertificateList (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) :
    List ULogBytecode.RuleCode → List ULogBytecode.RuleCode → Prop
  | nil (rest : List ULogBytecode.RuleCode) :
      MismatchCertificateList slot current actual programToHead runtime [] rest
  | cons (r : ULogBytecode.RuleCode)
      (skip rest : List ULogBytecode.RuleCode)
      (head : RuleMismatchCertificate slot current actual programToHead runtime
        r (skip ++ rest))
      (tail : MismatchCertificateList slot current actual programToHead runtime
        skip rest) :
      MismatchCertificateList slot current actual programToHead runtime
        (r :: skip) rest

theorem mismatchCertificateList_trace
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {skip rest : List ULogBytecode.RuleCode}
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip rest)
    (hrest : rest ≠ []) (passed : List ULogBytecode.RuleCode) :
    MismatchPrefixTrace slot current actual programToHead runtime
      (canonicalRuleCursor passed (skip ++ rest)) skip rest
      (canonicalRuleCursor (passed ++ skip) rest) := by
  induction certs generalizing passed with
  | nil rest =>
      simpa using (MismatchPrefixTrace.nil
        (slot := slot) (current := current) (actual := actual)
        (programToHead := programToHead) (runtime := runtime)
        (canonicalRuleCursor passed rest) rest)
  | cons r skip rest head tail ih =>
      have hremaining : skip ++ rest ≠ [] := by
        intro h
        have : rest = [] := by simpa using congrArg (List.drop skip.length) h
        exact hrest this
      let c := canonicalRuleCursor passed (r :: (skip ++ rest))
      let tailPath := (canonicalRuleCursor passed (skip ++ rest)).path
      have hpath : c.path = ulogCore pcDone :: tailPath := by
        exact canonicalRuleCursor_path_cons passed r (skip ++ rest)
          hremaining
      let hready : CursorMismatchReady slot current actual c r
          (skip ++ rest) programToHead runtime :=
        { tail := tailPath
          path_eq := hpath
          path_safe := by
            rw [← hpath]
            exact canonicalRuleCursor_path_safe passed
              (r :: (skip ++ rest))
          boundary_valid := by
            exact boundaryAfter_valid sourceBoundary (Or.inl rfl) passed
          remaining_ne := hremaining
          mismatch := head.mismatch
          actual_valid := head.actual_valid
          read_valid := head.read_valid
          source_corridor := head.source_corridor
          read_boundary_free := head.read_boundary_free
          read_scan := head.read_scan
          read_restore := head.read_restore
          slot_scan := head.slot_scan
          slot_restore := head.slot_restore
          program_restore := head.program_restore }
      have hnext := ih hrest (passed ++ [r])
      have hstep : advanceRuleCursor c r tailPath =
          canonicalRuleCursor (passed ++ [r]) (skip ++ rest) := by
        exact advance_canonicalRuleCursor passed r (skip ++ rest)
      have hnext' : MismatchPrefixTrace slot current actual programToHead
          runtime (advanceRuleCursor c r tailPath) skip rest
          (canonicalRuleCursor (passed ++ (r :: skip)) rest) := by
        rw [hstep]
        simpa [List.append_assoc] using hnext
      have hreadyTail : hready.tail = tailPath := by rfl
      refine MismatchPrefixTrace.cons c r skip rest
        (canonicalRuleCursor (passed ++ (r :: skip)) rest) hready ?_
      simpa [hreadyTail] using hnext'

theorem mismatchCertificateList_initial_trace
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {skip rest : List ULogBytecode.RuleCode}
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip rest)
    (hrest : rest ≠ []) :
    MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ rest)) skip rest
      (canonicalRuleCursor skip rest) := by
  simpa [canonicalRuleCursor_initial] using
    mismatchCertificateList_trace slot current actual programToHead
      runtime certs hrest []

end PakFixedPolyomino.ULogBootstrapExecution
