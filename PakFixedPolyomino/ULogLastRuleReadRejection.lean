import PakFixedPolyomino.ULogLastRuleRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorReadMismatch_last_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programToHead : List Tape)
    (actual : ℕ) (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe
      (cursorReadScanPath r [] programToHead))
    (hrestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  let pcBase := returnPath ++ ulogCore pcMark :: outer
  have hsource := reaches_ruleCursorSourceMatch_read slot boundary hboundary
    r [] programToHead pcBase (readHeadNat actual) runtime suffix
    hsourceCorridor
  have hreadMismatch := reaches_sourceReadAtMismatch_boundary slot r.source
    r.read actual hread hactual hreadNe boundary pcBase
    (cursorReadScanPath r [] programToHead) runtime suffix hreadScan
  have hrestore : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r]) (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r [] programToHead))
          pcBase (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) :=
    reaches_trans hsource hreadMismatch
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      have hrestore' : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules [r])
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (readMismatchRestorePath r.source r.read
              (cursorReadScanPath r [] programToHead))
            returnPath outer boundary
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)) := by
        rw [hafter] at hrestore
        simpa [restoreAdvanceStarted, pcBase, he, beforeLeftPath,
          List.append_assoc] using hrestore
      have hrestored := cursorReadMismatch_restored r [] programToHead
        runtime suffix actual hrestoreIdentity
      have hafter' := congrArg
        (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
      have hrestored' :
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r [] programToHead)).reverse.map
                restoreMismatchCell ++
              readHeadNat actual :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix =
            (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
        calc
          _ = (ULogBytecode.encodeRule r).map codeTape ++
                (programToHead ++ readHeadNat actual :: runtime ++
                  List.replicate r.source (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix) := by
              simpa [ULogBytecode.encodeRules, List.append_assoc] using
                hrestored
          _ = _ := by simpa [List.append_assoc] using hafter'
      have hreject := reaches_restoreMismatchLastRule_reject slot done path
        hpath boundary hboundary
        (readMismatchRestorePath r.source r.read
          (cursorReadScanPath r [] programToHead)) hrestoreSafe
        (readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
        r outer after right (by simpa [List.append_assoc] using hrestored')
        hzero hone
      have hrestore'' : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules [r])
            (ulogCore boundary ::
              (List.replicate done (ulogCore codeZero) ++
                ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
            (programToHead ++ readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))
          (restoreAdvanceStarted slot
            (readMismatchRestorePath r.source r.read
              (cursorReadScanPath r [] programToHead))
            returnPath outer boundary
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)) := by
        rw [hafter]
        simpa [pcBase, returnPath] using hrestore'
      exact reaches_trans hrestore'' hreject

end PakFixedPolyomino.ULogBootstrapExecution
