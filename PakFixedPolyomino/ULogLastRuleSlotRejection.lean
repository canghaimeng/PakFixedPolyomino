import PakFixedPolyomino.ULogLastRuleReadRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorSlotMismatch_last_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath [] programToHead)))
    (hrestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat r.read :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  let pcBase := returnPath ++ ulogCore pcMark :: outer
  have hsource := reaches_ruleCursorSourceMatch_read slot boundary hboundary
    r [] programToHead pcBase (readHeadNat r.read) runtime suffix
    hsourceCorridor
  have hslotMismatch := reaches_sourceReadAtSlotMismatch_boundary slot
    r.source r.read hread boundary pcBase
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath [] programToHead))
    runtime suffix hreadScan
  have hrestore : Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r]) (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath r.source r.read)
          pcBase (ulogCore boundary)
          (codeTape (!slot) ::
            encodedActionPath r.action.write r.action.target r.action.move
              (cursorMatchedMovePath [] programToHead) ++
            readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))) := by
    have hmismatch : Reaches
        (sourceReadStartedAt slot r.source boundary
          (unaryFieldFirst r.read) pcBase
          ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
            codeTape r.slot :: encodedActionPath r.action.write
              r.action.target r.action.move
                (cursorMatchedMovePath [] programToHead) ++
              readHeadNat r.read :: runtime)
          suffix)
        (.running (.restoreRule slot)
          (beforeLeftPath (slotMismatchRestorePath r.source r.read)
            pcBase (ulogCore boundary)
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath [] programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))) := by
      simpa [hslot] using hslotMismatch
    exact reaches_trans hsource hmismatch
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      have hrestore' : Reaches
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules [r])
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (slotMismatchRestorePath r.source r.read) returnPath outer
            boundary
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath [] programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)) := by
        rw [hafter] at hrestore
        simpa [restoreAdvanceStarted, pcBase, he, beforeLeftPath,
          List.append_assoc] using hrestore
      have hrestored := cursorSlotMismatch_restored slot r hslot []
        programToHead runtime suffix
      have hafter' := congrArg
        (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
      have hrestored' :
          (slotMismatchRestorePath r.source r.read).reverse.map
                restoreMismatchCell ++
              (codeTape (!slot) ::
                encodedActionPath r.action.write r.action.target r.action.move
                  (cursorMatchedMovePath [] programToHead) ++
                readHeadNat r.read :: runtime ++
                  List.replicate r.source (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix) =
            (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
        calc
          _ = (ULogBytecode.encodeRule r).map codeTape ++
                (programToHead ++ readHeadNat r.read :: runtime ++
                  List.replicate r.source (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix) := by
              simpa [ULogBytecode.encodeRules, List.append_assoc] using
                hrestored
          _ = _ := by simpa [List.append_assoc] using hafter'
      have hreject := reaches_restoreMismatchLastRule_reject slot done path
        hpath boundary hboundary (slotMismatchRestorePath r.source r.read)
        hrestoreSafe
        (codeTape (!slot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath [] programToHead) ++
          readHeadNat r.read :: runtime ++
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
            (programToHead ++ readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))
          (restoreAdvanceStarted slot
            (slotMismatchRestorePath r.source r.read) returnPath outer
            boundary
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath [] programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)) := by
        rw [hafter]
        simpa [pcBase, returnPath] using hrestore'
      exact reaches_trans hrestore'' hreject

end PakFixedPolyomino.ULogBootstrapExecution
