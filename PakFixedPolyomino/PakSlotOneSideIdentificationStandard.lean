import PakFixedPolyomino.PakScannerKernelReadLetterFacts
import PakFixedPolyomino.PakScannerRawShapeStandard

/-! The original bit/work readback for EVERY unchanged slot-one FullFrame.
Uses the same scannerTapeLetter and trimmed zipper, with structural kernel
facts. This is not whole-side identification without the copier terminator. -/
namespace PakFixedPolyomino.PakSlotOneSideIdentificationStandard
open ConcretePakScanner MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open PakScannerKernelReadLetterFacts

/-- Any encoded prefix recovered from a slot-one frame fits inside the actual
time-one scanner window.  This is the index bound used by all later bit reads. -/
theorem inputCells_length_le_sub_one_of_prefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List (Tape CoreTape))
    (h : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++
        tail) :
    (inputCells zero one work (ConcretePakSide.encodedWord x)).length ≤ n - 1 := by
  have htotal :
      ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).length = n - 1 := by
    rw [PakScannerRawShapeStandard.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
    rw [PakScannerRawShape.scannerBufferPrefix_eq_ofFn]
    simp
  have hlen := congrArg List.length h
  simp only [List.length_append] at hlen
  omega

theorem slotOneTrimmedZipper_getD_eq_scannerTapeLetter {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (k : ℕ) (hk : k < n - 1) :
    ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD k
        (Tape.core zero) =
      PakScannerRawShape.scannerTapeLetter
        ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
          ⟨k + 1, by omega⟩).centre := by
  rw [PakScannerRawShapeStandard.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
  rw [PakScannerRawShape.scannerBufferPrefix_eq_ofFn, List.map_ofFn]
  rw [List.getD_eq_get _ _ ⟨k, by simpa using hk⟩]
  simp [Function.comp_def]

theorem slotOne_testBit_eq_encodedWord {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List (Tape CoreTape))
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail)
    (k : ℕ) (hk : k < (ConcretePakSide.encodedWord x).length) :
    n.testBit k = (ConcretePakSide.encodedWord x).reverse.getD k false := by
  have hlen := inputCells_length_le_sub_one_of_prefix F x tail hprefix
  have hinputLen : (inputCells zero one work
      (ConcretePakSide.encodedWord x)).length =
      (ConcretePakSide.encodedWord x).length + 1 := by
    simp [inputCells]
  have hkWindow : k < n - 1 := by
    rw [hinputLen] at hlen
    omega
  have hget := congrArg (fun cells => cells.getD k (Tape.core zero)) hprefix
  have hkInput : k < (inputCells zero one work
      (ConcretePakSide.encodedWord x)).length := by
    rw [hinputLen]
    omega
  rw [List.getD_append _ _ _ k hkInput] at hget
  have hinput : (inputCells zero one work
      (ConcretePakSide.encodedWord x)).getD k (Tape.core zero) =
      bitCell zero one
        ((ConcretePakSide.encodedWord x).reverse.getD k false) := by
    unfold inputCells
    rw [List.getD_append _ _ _ k (by simpa using hk)]
    exact List.getD_map _ false (bitCell zero one)
  have hletter : PakScannerRawShape.scannerTapeLetter
      ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨k + 1, by omega⟩).centre =
      bitCell zero one
        ((ConcretePakSide.encodedWord x).reverse.getD k false) := by
    rw [← hinput, ← hget]
    exact (slotOneTrimmedZipper_getD_eq_scannerTapeLetter F k hkWindow).symm
  have hlegal :=
    (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).legal
      (⟨k, by omega⟩ : Fin n)
  exact legalScan_scannerTapeLetter_bit
    ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
      ⟨k, by omega⟩)
    ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
      ⟨k + 1, by omega⟩)
    (n.testBit k) ((ConcretePakSide.encodedWord x).reverse.getD k false)
    (by simpa using hlegal) hletter

theorem slotOne_testBit_eq_sideValue_of_lt_encodedWord {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List (Tape CoreTape))
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail)
    (k : ℕ) (hk : k < (ConcretePakSide.encodedWord x).length) :
    n.testBit k = (ConcretePakSide.sideValue x).testBit k := by
  rw [slotOne_testBit_eq_encodedWord F x tail hprefix k hk]
  have hkSide : k < (PakSideScanner.sideScannerBits x).length := by
    have hle := PakSideScanner.parserCells_le_sideScannerBits_length x
    have hparser : (PakEncodedStart.parserCells x).length =
        (inputCells zero one work (ConcretePakSide.encodedWord x)).length := rfl
    rw [hparser] at hle
    have hinputLen : (inputCells zero one work
        (ConcretePakSide.encodedWord x)).length =
        (ConcretePakSide.encodedWord x).length + 1 := by
      simp [inputCells]
    rw [hinputLen] at hle
    omega
  rw [← PakSideScanner.sideScannerBits_getD_encodedWord x k hkSide]
  exact PakSideScanner.sideScannerBits_getD x k (by
    simpa [PakSideScanner.sideScannerBits_length] using hkSide)

theorem slotOne_workDelimiter_enters_midHigh {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List (Tape CoreTape))
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail) :
    n.testBit (ConcretePakSide.encodedWord x).length = false ∧
      let s := (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨(ConcretePakSide.encodedWord x).length + 1, by
          have hlen := inputCells_length_le_sub_one_of_prefix F x tail hprefix
          have hi : (inputCells zero one work
              (ConcretePakSide.encodedWord x)).length =
              (ConcretePakSide.encodedWord x).length + 1 := by simp [inputCells]
          rw [hi] at hlen
          omega⟩
      s.phase = .mid ∧ s.mode = .high := by
  let k := (ConcretePakSide.encodedWord x).length
  have hlen := inputCells_length_le_sub_one_of_prefix F x tail hprefix
  have hinputLen : (inputCells zero one work
      (ConcretePakSide.encodedWord x)).length = k + 1 := by
    simp [inputCells, k]
  have hkWindow : k < n - 1 := by
    rw [hinputLen] at hlen
    omega
  have hget := congrArg (fun cells => cells.getD k (Tape.core zero)) hprefix
  rw [List.getD_append _ _ _ k (by rw [hinputLen]; omega)] at hget
  have hinput : (inputCells zero one work
      (ConcretePakSide.encodedWord x)).getD k (Tape.core zero) =
      Tape.core work := by
    unfold inputCells
    rw [List.getD_append_right]
    · simp [k]
    · simp [k]
  have hletter : PakScannerRawShape.scannerTapeLetter
      ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨k + 1, by omega⟩).centre = Tape.core work := by
    rw [← hinput, ← hget]
    exact (slotOneTrimmedZipper_getD_eq_scannerTapeLetter F k hkWindow).symm
  have hlegal :=
    (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).legal
      (⟨k, by omega⟩ : Fin n)
  simpa [k] using legalScan_scannerTapeLetter_work
    ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
      ⟨k, by omega⟩)
    ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
      ⟨k + 1, by omega⟩)
    (n.testBit k) (by simpa using hlegal) hletter

end PakFixedPolyomino.PakSlotOneSideIdentificationStandard
