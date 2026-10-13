import PakFixedPolyomino.PakSlotOneSideIdentification

/-! Structural source/read facts for the original scanner. These preserve the
original hidden-true-tail counterexample; no canonical terminal premise. -/
namespace PakFixedPolyomino.PakScannerKernelReadLetterFacts
open ConcretePakScanner MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open PakSlotOneSideIdentification

theorem legalScan_scannerTapeLetter_bit :
    ∀ (s t : ConcretePakScanner.State) (b expected : Bool),
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre =
        bitCell zero one expected →
      b = expected := by
  intro s t b expected hlegal hletter
  rcases hlegal with ⟨c, hc⟩
  cases c <;> cases b <;> cases expected <;> cases hm : t.mode <;>
    simp [LegalClause, Shift, headBuffer, newMid, modeOut, hm] at hc <;>
    simp_all [PakScannerRawShape.scannerTapeLetter, PakCouplingGenerated.bufferCell,
      OneTapeTableau.cellLetter, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach, bitCell, zero, one, work]

/-- The physical work delimiter is precisely a false-labelled transition
into the high mid-mode. -/
theorem legalScan_scannerTapeLetter_work :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre = Tape.core work →
      b = false ∧ t.phase = .mid ∧ t.mode = .high := by
  intro s t b hlegal hletter
  rcases hlegal with ⟨c, hc⟩
  cases c <;> cases b <;> cases hm : t.mode <;>
    simp [LegalClause, Shift, headBuffer, newMid, modeOut, hm] at hc <;>
    simp_all [PakScannerRawShape.scannerTapeLetter, PakCouplingGenerated.bufferCell,
      OneTapeTableau.cellLetter, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach, bitCell, zero, one, work]

theorem hiddenTrueTailCounterexample :
    PostWorkScannerState hiddenTrueTailSource ∧
      ConcretePakScanner.LegalScan hiddenTrueTailSource hiddenTrueTailTarget true ∧
      hiddenTrueTailTarget.centre = .hash ∧
      hiddenTrueTailTarget.mode = .tail := by
  decide

/-- Once a reverse copier argument certifies that the target remains a work
cell, the hidden-true tail jump is excluded and the next ripple bit is zero. -/
theorem legalScan_postWork_to_work :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      PostWorkScannerState s →
      ConcretePakScanner.LegalScan s t b →
      PakScannerRawShape.scannerTapeLetter t.centre = Tape.core work →
      b = false ∧ PostWorkScannerState t := by
  intro s t b _hs hlegal hletter
  obtain ⟨hb, hp, hm⟩ := legalScan_scannerTapeLetter_work s t b hlegal hletter
  exact ⟨hb, Or.inl ⟨hp, Or.inl hm⟩⟩

end PakFixedPolyomino.PakScannerKernelReadLetterFacts
