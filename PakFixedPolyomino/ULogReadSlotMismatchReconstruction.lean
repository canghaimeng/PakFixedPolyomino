import PakFixedPolyomino.ULogReadSlotMismatchBoundary

/-! Exact complete-rule reconstruction for read and slot mismatches. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def cursorReadScanPath (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape) :
    List Tape :=
  codeTape r.slot :: encodedActionPath r.action.write r.action.target
    r.action.move (cursorMatchedMovePath rs programToHead)

theorem cursorReadScanPath_restoreIdentity (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hprogram : RestoreMismatchIdentity programToHead) :
    RestoreMismatchIdentity (cursorReadScanPath r rs programToHead) := by
  change (cursorReadScanPath r rs programToHead).map restoreMismatchCell = _
  change programToHead.map restoreMismatchCell = programToHead at hprogram
  have hcode (b : Bool) : restoreMismatchCell (codeTape b) = codeTape b := by
    cases b <;> decide
  have hcomp : restoreMismatchCell ∘ codeTape = codeTape := by
    funext b
    exact hcode b
  have hmove : (moveBits r.action.move).map restoreMismatchCell =
      moveBits r.action.move := by
    cases r.action.move <;> decide
  simp [cursorReadScanPath, encodedActionPath, cursorMatchedMovePath,
    List.map_append, hprogram, hcode, hcomp, hmove]

theorem cursorReadMismatch_restored
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime suffix : List Tape) (actual : ℕ)
    (hprogram : RestoreMismatchIdentity programToHead) :
    (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)).reverse.map
          restoreMismatchCell ++
        readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ programToHead ++ readHeadNat actual :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix := by
  rw [readMismatchRestorePath_map r.source r.read
    (cursorReadScanPath r rs programToHead)
    (cursorReadScanPath_restoreIdentity r rs programToHead hprogram)]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [cursorReadScanPath, cursorMatchedMovePath, encodedActionPath,
    ULogBytecode.encodeRule, ULogBytecode.encodeAction,
    ULogBytecode.encodeNatField, moveBits, codeTape, List.map_append,
    List.append_assoc]

theorem cursorSlotMismatch_restored
    (lookupSlot : Bool) (r : ULogBytecode.RuleCode)
    (hslot : r.slot = !lookupSlot) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime suffix : List Tape) :
    (slotMismatchRestorePath r.source r.read).reverse.map
          restoreMismatchCell ++
        codeTape (!lookupSlot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath rs programToHead) ++
          readHeadNat r.read :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ programToHead ++ readHeadNat r.read :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix := by
  rw [slotMismatchRestorePath_map]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  change slot = !lookupSlot at hslot
  subst slot
  simp [cursorMatchedMovePath, encodedActionPath,
    ULogBytecode.encodeRule, ULogBytecode.encodeAction,
    ULogBytecode.encodeNatField, moveBits, codeTape, List.map_append,
    List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
