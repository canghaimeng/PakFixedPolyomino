import PakFixedPolyomino.PakScannerPathRawStandard
import PakFixedPolyomino.MStarParserOrderedLengthStandard

/-! Ordered shape and encoded-prefix readback for EVERY unchanged literal
slot-one frame, retaining the original buffer prefix and trimmed zipper. -/
namespace PakFixedPolyomino.PakScannerRawShapeStandard
open MStarParserTailSoundness PakScannerRawShape

theorem scannerBufferPrefix_ordered {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ (k : ℕ) (hk : k + 1 ≤ n),
      OrderedScannerBuffers (scannerBufferPrefix P (k + 1) hk)
        (bufferStage (P.states ⟨k + 1, by omega⟩).centre) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hlegal : ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom
          (P.states ⟨1, by omega⟩) (n.testBit 0) := by
        rw [← P.bottom]
        simpa using P.legal ⟨0, by omega⟩
      exact .snoc .nil _ rfl
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hok := PakScannerPathRawStandard.scannerPath_state_succ_rawState P k (by omega)
      let jpos : Fin (n + 1) := ⟨k + 1, by have := hk; omega⟩
      have hphase := PakScannerPathRawStandard.scannerPath_phase_ne_bot_of_pos P jpos (by simp [jpos])
      have hedge := PakScannerKernelRawInvariantFacts.legal_edge_stage_step
        (P.states ⟨k + 1, by omega⟩) (P.states ⟨k + 2, by omega⟩)
        (n.testBit (k + 1)) hok hphase (by
          simpa using P.legal ⟨k + 1, by omega⟩)
      exact .snoc hprev _ hedge

theorem slotOneTrimmedZipper_cells_eq_drop {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      (PakOuterParserReflection.windowCells n
        ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)).drop 1 := by
  unfold PakSlotOneParserDecode.slotOneTrimmedZipper
    PakSlotOneParserDecode.slotOneTimeOneZipper
    PakOuterParserReflection.windowZipper
  rw [PakSlotOneParserDecodeStandard.slotOne_timeOne_headIndex_eq_one F]
  dsimp
  let c := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  let cells := PakOuterParserReflection.windowCells n c
  change c.tape 1 :: cells.drop 2 = cells.drop 1
  have hlen : 1 < cells.length := by
    simp [cells, PakOuterParserReflection.windowCells]
    have := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
    omega
  calc
    c.tape 1 :: cells.drop 2 = cells[1] :: cells.drop 2 := by
      simp [cells, PakOuterParserReflection.windowCells]
    _ = cells.drop 1 := (List.drop_eq_getElem_cons hlen).symm

theorem slotOneTrimmedZipper_cells_eq_scannerBufferPrefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      (scannerBufferPrefix
        (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1)
        (n - 1) (Nat.sub_le n 1)).map scannerTapeLetter := by
  have hwidth :=
    (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
  rw [slotOneTrimmedZipper_cells_eq_drop F]
  rw [windowCells_drop_eq_ofFn n 1 _ (by omega)]
  rw [scannerBufferPrefix_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [Function.comp_apply]
  let j : Fin n := ⟨i.1 + 1, by
    have := i.2
    omega⟩
  have htape := slotOne_timeOne_tape_eq_scannerBuffer F j
  simpa [scannerTapeLetter, j] using htape

theorem slotOneTrimmedZipper_ordered_tape_shape {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ core : List MStarULogAssembly.CoreTape, ∃ hasRightEnd : Bool,
      ∃ hashes : ℕ,
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
            (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
          core.map MStarOuterProgram.Tape.core ++
            (if hasRightEnd then
              [MStarOuterProgram.Tape.scratch ⟨2, by decide⟩]
            else []) ++
            List.replicate hashes MStarOuterProgram.Tape.hash := by
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have hwidth :=
    (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
  have hordered₀ := scannerBufferPrefix_ordered P (n - 2) (by omega)
  have hindex : n - 2 + 1 = n - 1 := by omega
  have hordered : OrderedScannerBuffers
      (scannerBufferPrefix P (n - 1) (Nat.sub_le n 1))
      (bufferStage (P.states ⟨n - 1, by omega⟩).centre) := by
    simpa [hindex] using hordered₀
  rcases hordered.decompose with
    ⟨buffers, hasRightEnd, hashes, hshape, hcore, hstage⟩
  refine ⟨buffers.map scannerCoreLetter, hasRightEnd, hashes, ?_⟩
  rw [slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F, hshape]
  simp only [List.map_append, List.map_map]
  have hcoreMap : buffers.map scannerTapeLetter =
      buffers.map (fun b => MStarOuterProgram.Tape.core (scannerCoreLetter b)) := by
    apply List.map_congr_left
    intro b hb
    exact scannerTapeLetter_eq_core_of_stage_core b (hcore b hb)
  rw [hcoreMap]
  cases hasRightEnd <;>
    simp [scannerTapeLetter, PakCouplingGenerated.bufferCell,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      OneTapeTableau.cellLetter, Function.comp_def]

theorem slotOneTrimmedZipper_hasEncodedPrefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    HasEncodedPrefix (PakSlotOneParserDecode.slotOneTrimmedZipper F) := by
  obtain ⟨cores, rightEnd, hashes, hshape⟩ := slotOneTrimmedZipper_ordered_tape_shape F
  have haccept : MStarParserSoundness.CanAcceptResult
      (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTrimmedZipper F)) := by
    rw [← PakSlotOneParserDecodeStandard.trimmed_zipper_eq_original F]
    exact PakSlotOneParserDecodeStandard.slotOneTrimmedZipper_canAccept F
  apply MStarParserOrderedLengthStandard.ordered_empty_left_zipper_hasEncodedPrefix
    (PakSlotOneParserDecode.slotOneTrimmedZipper F) rfl cores rightEnd hashes
  · simpa [MStarParserOrderedLength.OrderedScannerTail] using hshape
  · exact haccept

end PakFixedPolyomino.PakScannerRawShapeStandard
