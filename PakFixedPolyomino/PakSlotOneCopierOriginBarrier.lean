import PakFixedPolyomino.PakSlotOneCopierRightEndReflection
import PakFixedPolyomino.PakSlotOneCopierMarkRBarrier
import PakFixedPolyomino.PakSlotOneMarkRTailProvenance

/-! # Slot-one copier origin/barrier composition -/

namespace PakFixedPolyomino.PakSlotOneCopierOriginBarrier

open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode MStarCopierExecution

theorem encodedPrefix_tail_has_two_work_prefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List ConcreteTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail) :
    ∃ external,
      tail = Tape.core work :: Tape.core work :: external := by
  rcases PakSlotOneCopierRightEndReflection.slotOne_copyStart_origin
      F x tail hprefix with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hcopy, hseedApply, hseedState, hrun⟩
  rcases PakSlotOneCopierMarkRBarrier.copyEntry_successful_seed_has_two_work_prefix
      (PakOuterParserReflection.windowZipper n copyConfig copyHead)
      (PakOuterParserReflection.windowZipper n seedConfig seedHead)
      out fuel hseedApply hrun with ⟨source, external, hseed⟩
  rw [hcopy] at hseedApply
  rw [hseed] at hseedApply
  cases htail : tail with
  | nil =>
      simp [PakSlotOneParserDecode.appendLeftHash,
        MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
        MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
        htail] at hseedApply
  | cons y ys =>
      let expectedCopy := PakSlotOneParserDecode.appendLeftHash
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse) tail)
      have hseedEq :
          MStarParserExecution.Zipper.mk
            (Tape.markL :: expectedCopy.leftRev) y ys =
          MStarParserExecution.Zipper.mk
            (Tape.markL :: source) (Tape.core work)
              (Tape.core work :: external) := by
        apply Option.some.inj
        simpa [PakSlotOneParserDecode.appendLeftHash,
          MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
          MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
          htail, expectedCopy] using hseedApply
      have hfocus := congrArg
        (fun z : MStarParserExecution.Zipper ConcreteTape => z.focus) hseedEq
      have hright := congrArg
        (fun z : MStarParserExecution.Zipper ConcreteTape => z.right) hseedEq
      refine ⟨external, ?_⟩
      change y = Tape.core work at hfocus
      change ys = Tape.core work :: external at hright
      rw [hfocus, hright]

def copiedPrefixCore (x : ConcretePakSide.Word) : List CoreTape :=
  (ConcretePakSide.encodedWord x).reverse.map
      (fun b => if b then one else zero) ++
    [work, work, work]

theorem encodedPrefix_external_is_ordered {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List ConcreteTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail) :
    ∃ external remaining hasRightEnd hashes,
      tail = Tape.core work :: Tape.core work :: external ∧
      external = MStarParserOrderedLength.OrderedScannerTail
        remaining hasRightEnd hashes := by
  rcases encodedPrefix_tail_has_two_work_prefix F x tail hprefix with
    ⟨external, htail⟩
  rcases PakScannerRawShape.slotOneTrimmedZipper_ordered_tape_shape F with
    ⟨cores, hasRightEnd, hashes, hordered⟩
  have hordered' :
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserOrderedLength.OrderedScannerTail
          cores hasRightEnd hashes := by
    simpa [MStarParserOrderedLength.OrderedScannerTail] using hordered
  have hfactor : MStarParserOrderedLength.OrderedScannerTail
      cores hasRightEnd hashes =
      (copiedPrefixCore x).map Tape.core ++ external := by
    rw [← hordered', hprefix, htail]
    simp [copiedPrefixCore, MStarParserExecution.inputCells,
      MStarParserExecution.bitCell, List.map_append, List.map_map,
      Function.comp_def, List.append_assoc]
  rcases MStarParserOrderedLength.OrderedScannerTail_prefix_cancel
      (copiedPrefixCore x) cores hasRightEnd hashes external hfactor with
    ⟨remaining, hcores, hexternal⟩
  exact ⟨external, remaining, hasRightEnd, hashes, htail, hexternal⟩

theorem rightEnd_mem_orderedScannerTail_iff
    (cores : List CoreTape) (hasRightEnd : Bool) (hashes : ℕ) :
    MStarCopierMicrocode.rightEnd ∈
        MStarParserOrderedLength.OrderedScannerTail
          cores hasRightEnd hashes ↔
      hasRightEnd = true := by
  cases hasRightEnd <;>
    simp [MStarParserOrderedLength.OrderedScannerTail,
      MStarCopierMicrocode.rightEnd]

theorem slotOne_installedMarkR_run {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (rawTail : List ConcreteTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ rawTail) :
    ∃ source external remainingCores hasRightEnd hashes remainingFuel out,
      external = MStarParserOrderedLength.OrderedScannerTail
        remainingCores hasRightEnd hashes ∧
      rawTail = Tape.core work :: Tape.core work :: external ∧
      .markR ∉ source ∧
      MStarCopierExecution.run remainingFuel
        (MStarCopierExecution.Result.running (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩) =
          MStarCopierExecution.Result.groupReady out := by
  rcases encodedPrefix_external_is_ordered F x rawTail hprefix with
    ⟨external, remainingCores, hasRightEnd, hashes, htail, hexternal⟩
  rcases PakSlotOneCopierRightEndReflection.slotOne_copyStart_origin
      F x rawTail hprefix with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hcopy, hseedApply, hseedState, hrun⟩
  let expectedCopy := PakSlotOneParserDecode.appendLeftHash
    (MStarParserExecution.extendRight
      (MStarConcreteAlphabet.finalZipper x.reverse) rawTail)
  let source := expectedCopy.leftRev
  have hseedShape : PakOuterParserReflection.windowZipper n seedConfig seedHead =
      ⟨.markL :: source, Tape.core work, Tape.core work :: external⟩ := by
    rw [hcopy] at hseedApply
    symm
    apply Option.some.inj
    simpa [expectedCopy, source, htail,
      PakSlotOneParserDecode.appendLeftHash,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo] using
      hseedApply
  have hmark : MStarCopierExecution.run 4
      (MStarCopierExecution.Result.running .seedCell
        ⟨.markL :: source, Tape.core work, Tape.core work :: external⟩) =
      MStarCopierExecution.Result.running (.findOld 0)
        ⟨.markL :: source, cellA, .markR :: external⟩ :=
    PakSlotOneCopierMarkRBarrier.seed_markR_install_preserves_tail source external
  have hrun' : MStarCopierExecution.run fuel
      (MStarCopierExecution.Result.running .seedCell
        ⟨.markL :: source, Tape.core work, Tape.core work :: external⟩) =
      MStarCopierExecution.Result.groupReady out := by
    rw [← hseedShape]
    exact hrun
  have hfour : 4 ≤ fuel := by
    by_contra hnot
    have hle : fuel ≤ 4 := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hbad : MStarCopierExecution.run 4
        (MStarCopierExecution.Result.running .seedCell
          ⟨.markL :: source, Tape.core work, Tape.core work :: external⟩) =
        MStarCopierExecution.Result.groupReady out := by
      rw [hd, MStarCopierExecution.run_add, hrun',
        MStarCopierExecution.groupReady_absorbing]
    rw [hmark] at hbad
    cases hbad
  obtain ⟨remainingFuel, hfuel⟩ := Nat.exists_eq_add_of_le hfour
  have hremaining : MStarCopierExecution.run remainingFuel
      (MStarCopierExecution.Result.running (.findOld 0)
        ⟨.markL :: source, cellA, .markR :: external⟩) =
      MStarCopierExecution.Result.groupReady out := by
    rw [← hmark, ← MStarCopierExecution.run_add, ← hfuel]
    exact hrun'
  have hsourceClean : Tape.markR ∉ source := by
    have hendpoint : (Tape.markR : ConcreteTape) ≠
        MStarParserMicrocode.endpointMark := by native_decide
    have hpayloadZero : (MStarParserMicrocode.payloadZero : ConcreteTape) ≠
        Tape.markR := by native_decide
    have hpayloadOne : (MStarParserMicrocode.payloadOne : ConcreteTape) ≠
        Tape.markR := by native_decide
    have hsepLen : (Tape.markR : ConcreteTape) ≠
        MStarParserMicrocode.sepLen := by native_decide
    have hpairedLen : (Tape.markR : ConcreteTape) ≠
        MStarParserMicrocode.pairedLen := by native_decide
    have hsepPad : (Tape.markR : ConcreteTape) ≠
        MStarParserMicrocode.sepPad := by native_decide
    have hpadDone : (Tape.markR : ConcreteTape) ≠
        MStarParserMicrocode.padDone := by native_decide
    simp [source, expectedCopy, PakSlotOneParserDecode.appendLeftHash,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarConcreteAlphabet.payloadMarker,
      MStarConcreteAlphabet.pairingPad, hendpoint, hpayloadZero, hpayloadOne,
      hsepLen, hpairedLen, hsepPad, hpadDone]
  exact ⟨source, external, remainingCores, hasRightEnd, hashes,
    remainingFuel, out, hexternal, htail, hsourceClean, hremaining⟩

/-- The optional scanner terminator in the ordered external suffix is present:
the successful copier run can only read its `rightEnd` from that suffix. -/
theorem slotOne_encodedPrefix_tail_hasRightEnd {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (rawTail : List ConcreteTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ rawTail) :
    ∃ source external remainingCores hashes remainingFuel out,
      external = MStarParserOrderedLength.OrderedScannerTail
        remainingCores true hashes ∧
      rawTail = Tape.core work :: Tape.core work :: external ∧
      .markR ∉ source ∧
      MStarCopierExecution.run remainingFuel
        (MStarCopierExecution.Result.running (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩) =
        MStarCopierExecution.Result.groupReady out := by
  rcases slotOne_installedMarkR_run F x rawTail hprefix with
    ⟨source, external, remainingCores, hasRightEnd, hashes,
      remainingFuel, out, hexternal, htail, hsource, hrun⟩
  have hmem :=
    PakSlotOneMarkRTailProvenance.run_from_installedMarkR_readsRightEnd_mem_tail
      source external remainingFuel out hsource hrun
  have hmem' : rightEnd ∈
      MStarParserOrderedLength.OrderedScannerTail
        remainingCores hasRightEnd hashes := by
    rw [← hexternal]
    exact hmem
  have htrue := (rightEnd_mem_orderedScannerTail_iff
    remainingCores hasRightEnd hashes).mp hmem'
  subst hasRightEnd
  exact ⟨source, external, remainingCores, hashes, remainingFuel, out,
    hexternal, htail, hsource, hrun⟩

/-- Zero-parameter slot-one terminator witness extracted directly from an
arbitrary slot-one full frame. -/
theorem slotOne_hasRightEnd {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ x rawTail source external remainingCores hashes remainingFuel out,
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++ rawTail ∧
      external = MStarParserOrderedLength.OrderedScannerTail
        remainingCores true hashes ∧
      rawTail = Tape.core work :: Tape.core work :: external ∧
      .markR ∉ source ∧
      MStarCopierExecution.run remainingFuel
        (MStarCopierExecution.Result.running (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩) =
        MStarCopierExecution.Result.groupReady out := by
  rcases MStarParserOrderedLength.slotOneTrimmedZipper_hasEncodedPrefix F with
    ⟨x, rawTail, hprefix⟩
  rcases slotOne_encodedPrefix_tail_hasRightEnd F x rawTail hprefix with
    ⟨source, external, remainingCores, hashes, remainingFuel, out,
      hexternal, htail, hsource, hrun⟩
  exact ⟨x, rawTail, source, external, remainingCores, hashes,
    remainingFuel, out, hprefix, hexternal, htail, hsource, hrun⟩

end PakFixedPolyomino.PakSlotOneCopierOriginBarrier
