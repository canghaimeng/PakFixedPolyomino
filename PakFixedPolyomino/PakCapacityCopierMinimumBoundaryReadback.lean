import PakFixedPolyomino.PakSlotOneCopierOriginReadbackStandard
import PakFixedPolyomino.PakGeneralCapacityParserCopierFront

/-! The original successful copier history forces the exact necessary reserve
when its actual initial row has the capacity tail AND the physical right
boundary hash. Retain the left hash as copier junk and the right hash as
exterior. CapacityInitialCells has length side-2, while the trimmed window
has length side-1; omitting the final boundary cannot instantiate ALLframes.
The all-frame capacity-to-row equality is supplied by separate readback. -/
namespace PakFixedPolyomino.PakCapacityCopierMinimumBoundaryReadback
open MStarConcreteAlphabet MStarOuterProgram
open PakSlotOneScannerMultiplicity PakGeneralCapacityParserCopierFront

theorem capacity_tail_without_boundary_impossible (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x))
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells zero one work (ConcretePakSide.encodedWord x) ++
        capacityParserTail x cap) : False := by
  have hn := PakMStarCouplingCorrectness.FullFrame.height_ge_two F.1
  have hlen : ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).length =
      ConcretePakSide.sideValue x - 1 := by
    simp only [List.length_cons, PakSlotOneParserDecode.slotOneTrimmedZipper,
      PakSlotOneParserDecode.slotOneTimeOneZipper, PakOuterParserReflection.windowZipper]
    rw [PakSlotOneParserDecodeStandard.slotOne_timeOne_headIndex_eq_one F]
    simp only [List.length_drop, PakOuterParserReflection.windowCells, List.length_ofFn]
    omega
  have hsize := congrArg List.length hprefix
  rw [← capacityInitialCells_eq_parserInput_append_tail,
    PakGeneralCapacityInitialWindow.capacityInitialCells_length,
    PakSideScanner.sideScannerBits_length, hlen] at hsize
  omega

theorem frame_capacity_tail_with_boundary_forces_minimum (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame (ConcretePakSide.sideValue x))
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells zero one work (ConcretePakSide.encodedWord x) ++
        (capacityParserTail x cap ++ [Tape.hash])) :
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val := by
  obtain ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hcopy, hseedApply, hseedState, hrun⟩ :=
    PakSlotOneCopierOriginReadbackStandard.slotOne_copyStart_origin
      F x (capacityParserTail x cap ++ [Tape.hash]) hprefix
  rw [hcopy] at hseedApply
  have hseed : MStarCopierExecution.Result.running .seedCell
      (PakOuterParserReflection.windowZipper (ConcretePakSide.sideValue x) seedConfig seedHead) =
      PakCopierReserveLowerBound.rawCopierSeed x cap.val
        (capacityCopierJunk x ++ [Tape.hash]) (capacityHashTail x cap ++ [Tape.hash]) := by
    apply congrArg (MStarCopierExecution.Result.running .seedCell)
    apply Option.some.inj
    simpa [PakSlotOneParserDecode.appendLeftHash, MStarParserExecution.extendRight,
      MStarConcreteAlphabet.finalZipper, capacityParserTail,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
      PakCopierReserveLowerBound.rawCopierSeed, capacityCopierJunk,
      MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      List.append_assoc] using hseedApply.symm
  apply PakCopierReserveLowerBound.successful_rawCopier_forces_minimum x cap.val
    (capacityCopierJunk x ++ [Tape.hash]) (capacityHashTail x cap ++ [Tape.hash])
  refine ⟨fuel, out, ?_⟩
  rw [← hseed]
  exact hrun

end PakFixedPolyomino.PakCapacityCopierMinimumBoundaryReadback
