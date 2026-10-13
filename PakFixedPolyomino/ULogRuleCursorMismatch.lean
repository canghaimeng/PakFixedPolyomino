import PakFixedPolyomino.ULogRuleCursorSlotAdvance

/-! Unified arbitrary-cursor step for every nonmatching RuleCode. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def RuleMatchesCursor (slot : Bool) (current actual : ℕ)
    (r : ULogBytecode.RuleCode) : Prop :=
  r.source = current ∧ r.read = actual ∧ r.slot = slot

theorem reaches_ruleCursorMismatch_step
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (hmismatch : ¬ RuleMatchesCursor slot current actual r)
    (hreadCode : r.read < 3)
    (programToHead runtime outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat actual) runtime))
    (hreadBoundary : ∀ x ∈
      cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime,
        x ≠ ulogCore readBoundary)
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r rs programToHead))
    (hreadRestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)))
    (hslotScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hslotRestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  by_cases hsource : r.source = current
  · by_cases hread : r.read = actual
    · have hslotNe : r.slot ≠ slot := by
        intro hslot
        exact hmismatch ⟨hsource, hread, hslot⟩
      have hslot : r.slot = !slot := by
        cases hrslot : r.slot <;> cases hsslot : slot <;> simp_all
      have h := reaches_ruleCursorSlotMismatch_step slot done path hpath
        boundary hboundary r hslot rs hrs programToHead hreadCode runtime
        outer suffix
        (by simpa [hread] using hcorridor)
        (by simpa [hslot] using hslotScan)
        (by simpa [hsource, hread] using hslotRestoreSafe)
      simpa [hsource, hread, List.append_assoc] using h
    · have h := reaches_ruleCursorReadMismatch_step slot done path hpath
        boundary hboundary r rs hrs programToHead actual hreadCode hactual
        hread runtime outer suffix hcorridor hreadScan hreadRestoreSafe
        hrestoreIdentity
      simpa [hsource, List.append_assoc] using h
  · by_cases hlt : r.source < current
    · have hextra : ∃ extra, current = r.source + extra + 1 := by
        exact ⟨current - r.source - 1, by omega⟩
      obtain ⟨extra, hcurrent⟩ := hextra
      have h := reaches_ruleCursorSourceShort_step slot done path hpath
        boundary hboundary r rs hrs
        (programToHead ++ readHeadNat actual :: runtime) extra outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
      simpa [hcurrent, List.append_assoc] using h
    · have hcurLt : current < r.source := by omega
      have hextra : ∃ extra, r.source = current + extra + 1 := by
        exact ⟨r.source - current - 1, by omega⟩
      obtain ⟨extra, hrsource⟩ := hextra
      have h := reaches_ruleCursorSourceLong_step slot done path hpath
        boundary hboundary r rs hrs
        (programToHead ++ readHeadNat actual :: runtime) current extra
        hrsource outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
      simpa [List.append_assoc] using h

end PakFixedPolyomino.ULogBootstrapExecution
