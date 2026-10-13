import PakFixedPolyomino.ULogCursorSlotMismatch

/-! Exact restore paths for read and slot mismatch exits. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def readMismatchRestorePath (source read : ℕ)
    (scanPath : List Tape) : List Tape :=
  scanPath.reverse ++ ulogCore readBoundary ::
    List.replicate read (ulogCore codeZero) ++ ulogCore codeOne ::
      List.replicate source (ulogCore codeZero)

def slotMismatchRestorePath (source read : ℕ) : List Tape :=
  ulogCore codeOne :: List.replicate read (ulogCore codeZero) ++
    ulogCore codeOne :: List.replicate source (ulogCore codeZero)

def RestoreMismatchIdentity (path : List Tape) : Prop :=
  path.map restoreMismatchCell = path

theorem readMismatchRestorePath_map (source read : ℕ)
    (scanPath : List Tape) (hscan : RestoreMismatchIdentity scanPath) :
    (readMismatchRestorePath source read scanPath).reverse.map
        restoreMismatchCell =
      (ULogBytecode.encodeNatField source ++
        ULogBytecode.encodeNatField read).map codeTape ++ scanPath := by
  change scanPath.map restoreMismatchCell = scanPath at hscan
  have hzeroState : ulogCore codeZero ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroSource : ulogCore codeZero ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroRead : ulogCore codeZero ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeState : ulogCore codeOne ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeSource : ulogCore codeOne ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeRead : ulogCore codeOne ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hreadState : ulogCore readBoundary ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hreadSource : ulogCore readBoundary ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  simp [readMismatchRestorePath, ULogBytecode.encodeNatField,
    List.reverse_append, List.map_append, restoreMismatchCell,
    hzeroState, hzeroSource, hzeroRead, honeState, honeSource, honeRead,
    hreadState, hreadSource, hscan, codeTape, List.append_assoc]

theorem slotMismatchRestorePath_map (source read : ℕ) :
    (slotMismatchRestorePath source read).reverse.map restoreMismatchCell =
      (ULogBytecode.encodeNatField source ++
        ULogBytecode.encodeNatField read).map codeTape := by
  have hzeroState : ulogCore codeZero ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroSource : ulogCore codeZero ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroRead : ulogCore codeZero ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeState : ulogCore codeOne ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeSource : ulogCore codeOne ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeRead : ulogCore codeOne ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  simp [slotMismatchRestorePath, ULogBytecode.encodeNatField,
    List.reverse_append, List.map_append, restoreMismatchCell,
    hzeroState, hzeroSource, hzeroRead, honeState, honeSource, honeRead,
    codeTape, List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
