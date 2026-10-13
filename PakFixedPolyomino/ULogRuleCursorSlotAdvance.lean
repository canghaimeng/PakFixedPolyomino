import PakFixedPolyomino.ULogRuleCursorReadAdvance

/-! Complete arbitrary-cursor advance for opposite-slot rules. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorSlotMismatch_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (rs : List ULogBytecode.RuleCode) (hrs : rs ≠ [])
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hrestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read)) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone ::
              advanceMismatchPath r boundary path).reverse ++
                ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  have hsource := reaches_ruleCursorSourceMatch_read slot boundary hboundary
    r rs programToHead pcBase (readHeadNat r.read) runtime suffix
    hsourceCorridor
  have hslotMismatch := reaches_sourceReadAtSlotMismatch_boundary slot
    r.source r.read hread boundary pcBase
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead))
    runtime suffix hreadScan
  have hrestore : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath r.source r.read)
          pcBase (ulogCore boundary)
          (codeTape (!slot) ::
            encodedActionPath r.action.write r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))) := by
    have hslotMismatch' : Reaches
        (sourceReadStartedAt slot r.source boundary
          (unaryFieldFirst r.read) pcBase
          ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
            codeTape r.slot :: encodedActionPath r.action.write
              r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime)
          suffix)
        (.running (.restoreRule slot)
          (beforeLeftPath (slotMismatchRestorePath r.source r.read)
            pcBase (ulogCore boundary)
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))) := by
      simpa [hslot] using hslotMismatch
    exact reaches_trans hsource hslotMismatch'
  have htail : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorSlotMismatch_restored slot r hslot rs
        programToHead runtime suffix
      have hrestored' :
          (slotMismatchRestorePath r.source r.read).reverse.map
                restoreMismatchCell ++
              (codeTape (!slot) ::
                encodedActionPath r.action.write r.action.target r.action.move
                  (cursorMatchedMovePath rs programToHead) ++
                readHeadNat r.read :: runtime ++
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
              (programToHead ++ readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      have hadvance := reaches_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (slotMismatchRestorePath r.source r.read) hrestoreSafe
        (codeTape (!slot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath rs programToHead) ++
          readHeadNat r.read :: runtime ++
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
            (beforeLeftPath (slotMismatchRestorePath r.source r.read)
              pcBase (ulogCore boundary)
              (codeTape (!slot) ::
                encodedActionPath r.action.write r.action.target r.action.move
                  (cursorMatchedMovePath rs programToHead) ++
                readHeadNat r.read :: runtime ++
                  List.replicate r.source (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix))) := by
        rw [he] at hrestore
        exact hrestore
      have hrestore' : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (slotMismatchRestorePath r.source r.read)
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
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
