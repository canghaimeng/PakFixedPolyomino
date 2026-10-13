import PakFixedPolyomino.ULogLastRuleSourceRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorMismatch_last_reject
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode)
    (hmismatch : ¬ RuleMatchesCursor slot current actual r)
    (hreadCode : r.read < 3)
    (programToHead runtime outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat actual) runtime))
    (hreadBoundary : ∀ x ∈
      cursorRuleCorridor r [] programToHead (readHeadNat actual) runtime,
        x ≠ ulogCore readBoundary)
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r [] programToHead))
    (hreadRestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)))
    (hslotScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath [] programToHead)))
    (hslotRestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  by_cases hsource : r.source = current
  · by_cases hread : r.read = actual
    · have hslotNe : r.slot ≠ slot := by
        intro hslot
        exact hmismatch ⟨hsource, hread, hslot⟩
      have hslot : r.slot = !slot := by
        cases hrslot : r.slot <;> cases hsslot : slot <;> simp_all
      have h := reaches_ruleCursorSlotMismatch_last_reject slot done path
        hpath boundary hboundary r hslot programToHead hreadCode runtime
        outer suffix (by simpa [hread] using hcorridor)
        (by simpa [hslot] using hslotScan)
        (by simpa [hsource, hread] using hslotRestoreSafe)
        after right (by simpa [hsource, hread] using hafter) hzero hone
      simpa [hsource, hread, List.append_assoc] using h
    · have h := reaches_ruleCursorReadMismatch_last_reject slot done path
        hpath boundary hboundary r programToHead actual hreadCode hactual
        hread runtime outer suffix hcorridor hreadScan hreadRestoreSafe
        hrestoreIdentity after right (by simpa [hsource] using hafter)
        hzero hone
      simpa [hsource, List.append_assoc] using h
  · by_cases hlt : r.source < current
    · have hextra : ∃ extra, current = r.source + extra + 1 :=
        ⟨current - r.source - 1, by omega⟩
      obtain ⟨extra, hcurrent⟩ := hextra
      have h := reaches_ruleCursorSourceShort_last_reject slot done path
        hpath boundary hboundary r
        (programToHead ++ readHeadNat actual :: runtime) extra outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
        after right (by simpa [hcurrent, List.append_assoc] using hafter)
        hzero hone
      simpa [hcurrent, List.append_assoc] using h
    · have hcurLt : current < r.source := by omega
      have hextra : ∃ extra, r.source = current + extra + 1 :=
        ⟨r.source - current - 1, by omega⟩
      obtain ⟨extra, hrsource⟩ := hextra
      have h := reaches_ruleCursorSourceLong_last_reject slot done path
        hpath boundary hboundary r
        (programToHead ++ readHeadNat actual :: runtime) current extra
        hrsource outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
        after right (by simpa [List.append_assoc] using hafter) hzero hone
      simpa [List.append_assoc] using h

theorem reaches_ruleCursorResult_lastMismatch_reject
    (slot : Bool) (current actual : ℕ)
    (c : RuleCursorData) (r : ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape)
    (hactual : actual < 3)
    (hpath : MismatchAdvancePathSafe c.path)
    (hboundary : c.boundary = sourceBoundary ∨
      c.boundary = sourceBoundaryZero ∨ c.boundary = sourceBoundaryOne)
    (hmismatch : ¬ RuleMatchesCursor slot current actual r)
    (hreadCode : r.read < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat actual) runtime))
    (hreadBoundary : ∀ x ∈
      cursorRuleCorridor r [] programToHead (readHeadNat actual) runtime,
        x ≠ ulogCore readBoundary)
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r [] programToHead))
    (hreadRestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)))
    (hslotScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath [] programToHead)))
    (hslotRestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (ruleCursorResult slot current actual c [r]
        programToHead runtime outer suffix)
      .rejected := by
  exact reaches_ruleCursorMismatch_last_reject slot current actual
    hactual c.done c.path hpath c.boundary hboundary r hmismatch hreadCode
    programToHead runtime outer suffix hcorridor hreadBoundary hreadScan
    hreadRestoreSafe hslotScan hslotRestoreSafe hrestoreIdentity after right
    hafter hzero hone

end PakFixedPolyomino.ULogBootstrapExecution
