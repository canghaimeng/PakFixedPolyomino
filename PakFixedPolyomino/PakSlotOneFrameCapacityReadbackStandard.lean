import PakFixedPolyomino.PakSlotOneSideValueReflectionStandard
import PakFixedPolyomino.PakCapacityScannerStandardClassification
import PakFixedPolyomino.PakCapacityScannerIdentityWeight
import PakFixedPolyomino.PakWeightedFullFrameStandardFirstBranch

/-! Every original slot-one frame at an encoded square has one actual scanner
capacity. No minimum successful reserve or canonical terminal is assumed.
The entire capacity fibre has the literal geometric column weight. -/
namespace PakFixedPolyomino.PakSlotOneFrameCapacityReadbackStandard
open PakScannerBaselineAutomaton PakSlotOneScannerMultiplicity
open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open PakSlotOneSideValueReflection

theorem scannerPath_cast_states {n m : Nat} (h : n = m)
    (P : ScannerPath n) (k : Nat) (hk : k ≤ m) :
    (Equiv.cast (congrArg ScannerPath h) P).states ⟨k, by omega⟩ =
      P.states ⟨k, by omega⟩ := by
  subst m
  rfl

theorem scannerPath_cast_back {n m : Nat} (h : n = m) (P : ScannerPath m) :
    Equiv.cast (congrArg ScannerPath h)
      (Equiv.cast (congrArg ScannerPath h.symm) P) = P := by
  subst m
  rfl

theorem scannerPath_eq_capacityPath_of_terminal
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (P : ScannerPath (ConcretePakSide.sideValue x))
    (hmode : (P.states ⟨capacityTerminalIndex x c, by
      have := capacityTerminalIndex_lt x c
      have := PakSideScanner.sideScannerHeight x
      omega⟩).mode = .high)
    (hright : (P.states ⟨capacityTerminalIndex x c + 1, by
      have := capacityTerminalIndex_lt x c
      have := PakSideScanner.sideScannerHeight x
      omega⟩).centre = .rightEnd) : P = capacityScannerPath x c := by
  let h := PakSideScanner.sideScannerHeight x
  let raw := Equiv.cast (congrArg ScannerPath h.symm) P
  have he : raw = rawCapacityScannerPath x c := by
    apply PakCapacityScannerStandardClassification.scannerPath_eq_rawCapacityScannerPath_of_terminal
    · dsimp only [raw]
      rw [scannerPath_cast_states h.symm P _ (by
        have := capacityTerminalIndex_lt x c
        omega)]
      exact hmode
    · dsimp only [raw]
      rw [scannerPath_cast_states h.symm P _ (by
        have := capacityTerminalIndex_lt x c
        omega)]
      exact hright
  calc
    P = Equiv.cast (congrArg ScannerPath h) raw := (scannerPath_cast_back h P).symm
    _ = Equiv.cast (congrArg ScannerPath h) (rawCapacityScannerPath x c) :=
      congrArg (Equiv.cast (congrArg ScannerPath h)) he
    _ = capacityScannerPath x c := rfl

theorem terminalIndex_lt_sideScannerBits
    (x : ConcretePakSide.Word)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x))
    (remaining : List CoreTape) (hashes : Nat)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++
        [Tape.core work, Tape.core work] ++ remaining.map Tape.core ++
        [MStarCopierMicrocode.rightEnd] ++ List.replicate hashes Tape.hash) :
    terminalIndex x remaining < (PakSideScanner.sideScannerBits x).length := by
  have ht := PakSlotOneSideValueReflectionStandard.terminalIndex_lt
    F x remaining hashes hshape
  have hh := PakSideScanner.sideScannerHeight x
  have hle : terminalIndex x remaining ≤ (PakSideScanner.sideScannerBits x).length := by
    omega
  by_contra hnot
  have heq : terminalIndex x remaining = (PakSideScanner.sideScannerBits x).length := by
    omega
  let P := FullFrame.toScannerPath F.1
  have hmid := (PakSlotOneSideValueReflectionStandard.terminal_edge_false_and_tail
    F x remaining hashes hshape).2.1
  have hlegal := P.legal ⟨terminalIndex x remaining + 1, by omega⟩
  have hlast : terminalIndex x remaining + 2 = ConcretePakSide.sideValue x := by omega
  have hcap : (P.states ⟨terminalIndex x remaining + 2, by omega⟩).phase = .cap := by
    rw [show (⟨terminalIndex x remaining + 2, by omega⟩ :
      Fin (ConcretePakSide.sideValue x + 1)) = ⟨ConcretePakSide.sideValue x, by omega⟩
      from Fin.ext hlast, P.top]
    rfl
  have htop := (PakScannerKernelTerminalFacts.legal_to_cap_is_top hlegal hcap).2.1
  have : ConcretePakScanner.Phase.mid = .top := hmid.symm.trans htop
  cases this

theorem every_frame_has_capacity (x : ConcretePakSide.Word)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x)) :
    ∃ c : ScannerCapacity x, FullFrame.toScannerPath F.1 = capacityScannerPath x c := by
  obtain ⟨y, remaining, hashes, hshape⟩ :=
    PakSlotOneSideValueReflectionStandard.slotOne_cells_terminal_shape F
  have hy : ConcretePakSide.sideValue x = ConcretePakSide.sideValue y :=
    Nat.eq_of_testBit_eq fun k =>
      PakSlotOneSideValueReflectionStandard.testBit_eq_sideValue
        F y remaining hashes k hshape
  have hxy := ConcretePakSide.sideValue_injective hy
  subst y
  have ht := terminalIndex_lt_sideScannerBits x F remaining hashes hshape
  let c : ScannerCapacity x := ⟨remaining.length, by
    unfold scannerCapacityCount
    unfold terminalIndex at ht
    omega⟩
  refine ⟨c, scannerPath_eq_capacityPath_of_terminal x c _ ?_ ?_⟩
  · have hh := PakSlotOneSideValueReflectionStandard.core_interval_false_midHigh
      F x remaining hashes hshape (2 + remaining.length) (by
        unfold terminalIndex
        omega)
    have hi : (ConcretePakSide.encodedWord x).length +
        (2 + remaining.length) + 1 = capacityTerminalIndex x c := by
      dsimp [c, capacityTerminalIndex]
      omega
    simpa only [hi] using hh.2.2
  · have hk := PakSlotOneSideValueReflectionStandard.terminalIndex_lt
      F x remaining hashes hshape
    have hr := PakSlotOneSideValueReflectionStandard.getD_terminalIndex
      F x remaining hashes hshape
    rw [PakSlotOneSideIdentificationStandard.slotOneTrimmedZipper_getD_eq_scannerTapeLetter
      F (terminalIndex x remaining) hk] at hr
    have hc := (PakSlotOneSideIdentification.scannerTapeLetter_rightEnd_iff _).mp hr
    simpa only [c, capacityTerminalIndex, terminalIndex] using hc

theorem every_frame_has_unique_capacity (x : ConcretePakSide.Word)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x)) :
    ∃! c : ScannerCapacity x, FullFrame.toScannerPath F.1 = capacityScannerPath x c := by
  obtain ⟨c, hc⟩ := every_frame_has_capacity x F
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact capacityScannerPath_injective x (hd.symm.trans hc)

theorem entire_capacity_fibre_weight (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x))
    (hc : FullFrame.toScannerPath F.1 = capacityScannerPath x c) :
    PakWeightedFullFrameStandardFirstBranch.frameIdentityWeight F.1 =
      2 ^ (scannerCapacityCount x - c.val - 1) := by
  rw [PakWeightedFullFrameStandardFirstBranch.frame_weight_eq_scanner_weight, hc]
  exact PakCapacityScannerIdentityWeight.capacity_path_weight x c

end PakFixedPolyomino.PakSlotOneFrameCapacityReadbackStandard
