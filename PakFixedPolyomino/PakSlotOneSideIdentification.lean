import PakFixedPolyomino.MStarParserOrderedLength

/-! # Slot-one side-length identification

This module identifies the square side encoded by an actual slot-one scanner
prefix.  It deliberately does not identify the scanner's optional terminal
position; that requires the separate reverse copier argument. -/

namespace PakFixedPolyomino.PakSlotOneSideIdentification

open ConcretePakScanner
open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution

def PostWorkScannerState (s : ConcretePakScanner.State) : Prop :=
  (s.phase = .mid ∧ (s.mode = .high ∨ s.mode = .tail)) ∨
    s.phase = .top

instance (s : ConcretePakScanner.State) : Decidable (PostWorkScannerState s) := by
  unfold PostWorkScannerState
  infer_instance

/-- On every legal scanner edge, a target centre spelling an ordinary bit
determines the ripple label of that edge. -/
theorem legalScan_scannerTapeLetter_bit :
    ∀ (s t : ConcretePakScanner.State) (b expected : Bool),
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre =
        bitCell zero one expected →
      b = expected := by
  native_decide

/-- The physical work delimiter is precisely a false-labelled transition
into the high mid-mode. -/
theorem legalScan_scannerTapeLetter_work :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre = Tape.core work →
      b = false ∧ t.phase = .mid ∧ t.mode = .high := by
  native_decide

def hiddenTrueTailSource : ConcretePakScanner.State :=
  { phase := .mid, left := .work, centre := .work,
    lookahead := .lh0, mode := .high }

def hiddenTrueTailTarget : ConcretePakScanner.State :=
  { phase := .mid, left := .work, centre := .hash,
    lookahead := .lh0, mode := .tail }

/-- Truthful obstruction to identifying the side from the parser prefix
alone: after a work cell, the `.mid` clause can consume a hidden true bit and
jump directly to tail mode while emitting hash, without an intervening
`rightEnd`.  A reverse copier invariant is therefore required before the
side-length theorem can be stated. -/
theorem hiddenTrueTailCounterexample :
    PostWorkScannerState hiddenTrueTailSource ∧
      ConcretePakScanner.LegalScan hiddenTrueTailSource hiddenTrueTailTarget true ∧
      hiddenTrueTailTarget.centre = .hash ∧
      hiddenTrueTailTarget.mode = .tail := by
  native_decide

/-- Once a reverse copier argument certifies that the target remains a work
cell, the hidden-true tail jump is excluded and the next ripple bit is zero. -/
theorem legalScan_postWork_to_work :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      PostWorkScannerState s →
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre = Tape.core work →
      b = false ∧ PostWorkScannerState t := by
  native_decide

theorem legalScan_midHigh_to_core
    (s t : ConcretePakScanner.State) (b : Bool)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .high)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hcore : PakScannerRawShape.bufferStage t.centre =
      PakScannerRawShape.ScannerWordStage.core) :
    b = false ∧ t.phase = .mid ∧ t.mode = .high ∧
      PakScannerRawShape.scannerTapeLetter t.centre = Tape.core work := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ConcretePakScanner.Shift,
      ConcretePakScanner.newMid, ConcretePakScanner.modeOut,
      PakScannerRawShape.bufferStage] at hclause hcore ⊢ <;>
    simp_all [PakScannerRawShape.scannerTapeLetter,
      PakCouplingGenerated.bufferCell, OneTapeTableau.cellLetter,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      MStarULogAssembly.data, MStarCopierMicrocode.attach] <;>
    all_goals cases b <;> cases hm : t.mode <;>
      simp_all [ConcretePakScanner.modeOut, ConcretePakScanner.newMid]

theorem legalScan_to_rightEnd
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hend : t.centre = .rightEnd) :
    b = false ∧ s.phase = .mid ∧ t.phase = .mid ∧ t.mode = .tail := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ConcretePakScanner.Shift,
      ConcretePakScanner.newMid, ConcretePakScanner.modeOut] at hclause hend ⊢ <;>
    simp_all <;>
    all_goals cases b <;> cases hm : t.mode <;>
      simp_all [ConcretePakScanner.headBuffer, ConcretePakScanner.newMid]

theorem legalScan_from_midTail
    (s t : ConcretePakScanner.State) (b : Bool)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (hlegal : ConcretePakScanner.LegalScan s t b) :
    b = false ∧
      ((t.phase = .mid ∧ t.mode = .tail ∧ t.centre = .hash) ∨
        t.phase = .top) := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ConcretePakScanner.Shift,
      ConcretePakScanner.newMid, ConcretePakScanner.modeOut] at hclause ⊢ <;>
    simp_all <;>
    all_goals cases b <;> cases hm : t.mode <;>
      simp_all [ConcretePakScanner.modeOut, ConcretePakScanner.newMid]

theorem scannerTapeLetter_core_forces_stage_core
    (b : ConcretePakScanner.Buffer) (a : MStarULogAssembly.CoreTape)
    (h : PakScannerRawShape.scannerTapeLetter b = Tape.core a) :
    PakScannerRawShape.bufferStage b =
      PakScannerRawShape.ScannerWordStage.core := by
  cases b <;>
    simp [PakScannerRawShape.scannerTapeLetter,
      PakScannerRawShape.bufferStage, PakCouplingGenerated.bufferCell,
      OneTapeTableau.cellLetter, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach] at h ⊢

theorem scannerTapeLetter_rightEnd_iff (b : ConcretePakScanner.Buffer) :
    PakScannerRawShape.scannerTapeLetter b = MStarCopierMicrocode.rightEnd ↔
      b = .rightEnd := by
  cases b <;>
    simp [PakScannerRawShape.scannerTapeLetter,
      PakCouplingGenerated.bufferCell, OneTapeTableau.cellLetter,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      MStarULogAssembly.data, MStarCopierMicrocode.attach,
      MStarCopierMicrocode.rightEnd]

theorem scannerTapeLetter_hash_iff (b : ConcretePakScanner.Buffer) :
    PakScannerRawShape.scannerTapeLetter b = Tape.hash ↔ b = .hash := by
  cases b <;>
    simp [PakScannerRawShape.scannerTapeLetter,
      PakCouplingGenerated.bufferCell, OneTapeTableau.cellLetter,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      MStarULogAssembly.data, MStarCopierMicrocode.attach]

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
    rw [PakScannerRawShape.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
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
  rw [PakScannerRawShape.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
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

end PakFixedPolyomino.PakSlotOneSideIdentification
