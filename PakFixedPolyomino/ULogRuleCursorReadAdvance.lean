import PakFixedPolyomino.ULogReadSlotMismatchReconstruction

/-! Complete arbitrary-cursor advance for all unequal read/head pairs. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorReadMismatch_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programToHead : List Tape) (actual : ℕ)
    (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe
      (cursorReadScanPath r rs programToHead))
    (hrestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone ::
              advanceMismatchPath r boundary path).reverse ++
                ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  have hsource := reaches_ruleCursorSourceMatch_read slot boundary hboundary
    r rs programToHead pcBase (readHeadNat actual) runtime suffix
    hsourceCorridor
  have hreadMismatch := reaches_sourceReadAtMismatch_boundary slot r.source
    r.read actual hread hactual hreadNe boundary pcBase
    (cursorReadScanPath r rs programToHead) runtime suffix hreadScan
  have hrestore : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r rs programToHead))
          pcBase (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
    exact reaches_trans hsource hreadMismatch
  have htail : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorReadMismatch_restored r rs programToHead
        runtime suffix actual hrestoreIdentity
      have hrestored' :
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r rs programToHead)).reverse.map
              restoreMismatchCell ++
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix) =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs =>
            (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++
                ULogBytecode.encodeRules rs).map codeTape ++
              (programToHead ++ readHeadNat actual :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      have hadvance := reaches_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (readMismatchRestorePath r.source r.read
          (cursorReadScanPath r rs programToHead)) hrestoreSafe
        (readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right hrestored'
      have hreturn : (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
      have hrestoreHe : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (.running (.restoreRule slot)
            (beforeLeftPath
              (readMismatchRestorePath r.source r.read
                (cursorReadScanPath r rs programToHead))
              pcBase (ulogCore boundary)
              (readHeadNat actual :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))) := by
        rw [he] at hrestore
        exact hrestore
      have hrestore' : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (readMismatchRestorePath r.source r.read
              (cursorReadScanPath r rs programToHead))
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)) := by
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hrestoreHe
      have hall := reaches_trans hrestore' hadvance
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hall
      simpa [atBitsTail, he, pcBase, List.reverse_append,
        List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
