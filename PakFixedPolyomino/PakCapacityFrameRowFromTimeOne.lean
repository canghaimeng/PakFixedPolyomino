import PakFixedPolyomino.PakCapacityCopierMinimumBoundaryReadback

/-! Recover the entire physical trimmed row from an exact time-one configuration.
Both boundary hashes are retained. The configuration equality is explicit in
this local bridge; the ALL capacity-fibre configuration readback is separate. -/
namespace PakFixedPolyomino.PakCapacityFrameRowFromTimeOne
open MStarConcreteAlphabet MStarOuterProgram
open PakGeneralCapacityInitialWindow PakSlotOneScannerMultiplicity

abbrev Frames (x : ConcretePakSide.Word) :=
  PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x)

noncomputable def timeOneConfig {x : ConcretePakSide.Word} (F : Frames x) :=
  (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩

theorem anchored_cells_window (cells : List MStarULogAssembly.Tape) :
    (List.ofFn fun i : Fin (cells.length + 2) =>
      if (1 : Int) ≤ i.val then cells.getD (Int.toNat ((i.val : Int) - 1)) Tape.hash
      else Tape.hash) = Tape.hash :: cells ++ [Tape.hash] := by
  rw [List.cons_append]
  apply List.ext_getElem (by simp)
  intro i hi hj
  cases i with
  | zero => simp
  | succ k =>
      have hkbound : k < cells.length + 1 := by simp only [List.length_ofFn] at hi; omega
      simp only [List.getElem_ofFn, List.getElem_cons_succ]
      have hpos : (1 : Int) ≤ (k + 1 : Nat) := by omega
      rw [if_pos hpos]
      have hindex : Int.toNat (((k + 1 : Nat) : Int) - 1) = k := by omega
      rw [hindex]
      by_cases hk : k < cells.length
      · rw [List.getElem_append_left hk]
        exact List.getD_eq_getElem _ _ hk
      · have he : k = cells.length := by omega
        subst k
        rw [List.getElem_append_right (by omega)]
        simp [List.getD_eq_default]

theorem capacity_window_cells (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    PakOuterParserReflection.windowCells (ConcretePakSide.sideValue x)
      (capacityEncodedParserConfig x cap) =
      Tape.hash :: capacityInitialCells x cap ++ [Tape.hash] := by
  have hn := PakSideScanner.sideValue_ge_five x
  have hlen : (capacityInitialCells x cap).length + 2 = ConcretePakSide.sideValue x := by
    rw [capacityInitialCells_length, PakSideScanner.sideScannerBits_length]
    omega
  simpa [PakOuterParserReflection.windowCells, capacityEncodedParserConfig,
    capacityInitialTape, hlen] using anchored_cells_window (capacityInitialCells x cap)

theorem trimmed_row_of_timeOne (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : Frames x) (hc : timeOneConfig F = capacityEncodedParserConfig x cap) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        capacityInitialCells x cap ++ [Tape.hash] := by
  have hn := PakSideScanner.sideValue_ge_five x
  have hc' := hc
  unfold timeOneConfig at hc'
  simp only [PakSlotOneParserDecode.slotOneTrimmedZipper,
    PakSlotOneParserDecode.slotOneTimeOneZipper, PakOuterParserReflection.windowZipper]
  rw [PakSlotOneParserDecodeStandard.slotOne_timeOne_headIndex_eq_one F, hc']
  change (capacityEncodedParserConfig x cap).tape (1 : Int) ::
    (PakOuterParserReflection.windowCells (ConcretePakSide.sideValue x)
      (capacityEncodedParserConfig x cap)).drop 2 = _
  have hi : 1 < (PakOuterParserReflection.windowCells (ConcretePakSide.sideValue x)
      (capacityEncodedParserConfig x cap)).length := by
    simp only [PakOuterParserReflection.windowCells, List.length_ofFn]
    omega
  have he := List.drop_eq_getElem_cons hi
  have hg : (PakOuterParserReflection.windowCells (ConcretePakSide.sideValue x)
      (capacityEncodedParserConfig x cap))[1] =
      (capacityEncodedParserConfig x cap).tape (1 : Int) := by
    simp [PakOuterParserReflection.windowCells]
  rw [hg] at he
  rw [← he, capacity_window_cells]
  simp

theorem minimum_of_timeOne (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : Frames x) (hc : timeOneConfig F = capacityEncodedParserConfig x cap) :
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val := by
  apply PakCapacityCopierMinimumBoundaryReadback.frame_capacity_tail_with_boundary_forces_minimum
    x cap F
  rw [← List.append_assoc, ← PakGeneralCapacityParserCopierFront.capacityInitialCells_eq_parserInput_append_tail]
  exact trimmed_row_of_timeOne x cap F hc

end PakFixedPolyomino.PakCapacityFrameRowFromTimeOne
