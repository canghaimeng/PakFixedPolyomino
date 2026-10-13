import PakFixedPolyomino.ULogRuleCursorMismatch

/-! Certified arbitrary-prefix fold of the unified mismatch cursor step. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

structure RuleCursorData where
  done : ℕ
  path : List Tape
  boundary : ULogLetter

def ruleCursorBase (c : RuleCursorData) (outer : List Tape) : List Tape :=
  ulogCore c.boundary ::
    (List.replicate c.done (ulogCore codeZero) ++
      ulogCore pcDone :: c.path).reverse ++ ulogCore pcMark :: outer

def ruleCursorResult (slot : Bool) (current actual : ℕ)
    (c : RuleCursorData) (rules : List ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape) : Result :=
  atBitsTail (.fieldCompare .source slot) (ULogBytecode.encodeRules rules)
    (ruleCursorBase c outer)
    (programToHead ++ readHeadNat actual :: runtime ++
      List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: suffix)

def advanceRuleCursor (c : RuleCursorData) (r : ULogBytecode.RuleCode)
    (tail : List Tape) : RuleCursorData :=
  ⟨c.done + 1, advanceMismatchPath r c.boundary tail,
    nextSourceBoundary (moveSecond r.action.move)⟩

structure CursorMismatchReady (slot : Bool) (current actual : ℕ)
    (c : RuleCursorData) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape) where
  tail : List Tape
  path_eq : c.path = ulogCore pcDone :: tail
  path_safe : MismatchAdvancePathSafe (ulogCore pcDone :: tail)
  boundary_valid : c.boundary = sourceBoundary ∨
    c.boundary = sourceBoundaryZero ∨ c.boundary = sourceBoundaryOne
  remaining_ne : rs ≠ []
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

theorem reaches_cursorMismatchReady
    (slot : Bool) (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape)
    (h : CursorMismatchReady slot current actual c r rs
      programToHead runtime) :
    Reaches
      (ruleCursorResult slot current actual c (r :: rs)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual (advanceRuleCursor c r h.tail) rs
        programToHead runtime outer suffix) := by
  have hstep := reaches_ruleCursorMismatch_step slot current actual
    h.actual_valid c.done h.tail h.path_safe c.boundary h.boundary_valid
    r rs h.remaining_ne h.mismatch h.read_valid programToHead runtime outer
    suffix h.source_corridor h.read_boundary_free h.read_scan h.read_restore
    h.slot_scan h.slot_restore h.program_restore
  simpa [ruleCursorResult, ruleCursorBase, advanceRuleCursor, h.path_eq,
    List.append_assoc] using hstep

inductive MismatchPrefixTrace (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) :
    RuleCursorData → List ULogBytecode.RuleCode →
      List ULogBytecode.RuleCode → RuleCursorData → Prop
  | nil (c : RuleCursorData) (rest : List ULogBytecode.RuleCode) :
      MismatchPrefixTrace slot current actual programToHead runtime
        c [] rest c
  | cons (c : RuleCursorData) (r : ULogBytecode.RuleCode)
      (skip rest : List ULogBytecode.RuleCode) (final : RuleCursorData)
      (ready : CursorMismatchReady slot current actual c r (skip ++ rest)
        programToHead runtime)
      (next : MismatchPrefixTrace slot current actual programToHead runtime
        (advanceRuleCursor c r ready.tail) skip rest final) :
      MismatchPrefixTrace slot current actual programToHead runtime
        c (r :: skip) rest final

theorem reaches_mismatchPrefix
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final) :
    Reaches
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix) := by
  induction trace with
  | nil c rest => exact reaches_refl _
  | cons c r skip rest final ready next ih =>
      have hstep := reaches_cursorMismatchReady slot current actual c r
        (skip ++ rest) programToHead runtime outer suffix ready
      exact reaches_trans hstep ih

end PakFixedPolyomino.ULogBootstrapExecution
