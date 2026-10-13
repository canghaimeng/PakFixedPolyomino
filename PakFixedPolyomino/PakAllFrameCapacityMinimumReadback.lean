import PakFixedPolyomino.PakAllFrameCapacityInitialReadback
import PakFixedPolyomino.PakCapacityFrameRowFromTimeOne
import PakFixedPolyomino.PakCapacityOuterFrontDeterministicPrefix

/-! EVERY original capacity fibre forces the necessary copier workspace.
The row includes the physical right boundary hash. Actual parser/copier
cancellation therefore needs no supplied workspace or row certificate.
This does not identify fibre counts with source accepting leaves. -/
namespace PakFixedPolyomino.PakAllFrameCapacityMinimumReadback
open PakAllFrameCapacityWeightedPartition PakSlotOneScannerMultiplicity
open PakGeneralCapacityInitialWindow PakCapacityOuterFrontDeterministicPrefix
open MStarFixedWidthFirstHitEquiv

theorem fibre_trimmed_row (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F.1).focus ::
      (PakSlotOneParserDecode.slotOneTrimmedZipper F.1).right =
        capacityInitialCells x cap ++ [MStarOuterProgram.Tape.hash] :=
  PakCapacityFrameRowFromTimeOne.trimmed_row_of_timeOne x cap F.1
    (PakAllFrameCapacityInitialReadback.fibre_timeOneConfig x cap F)

theorem fibre_minimum (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) :
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val :=
  PakCapacityFrameRowFromTimeOne.minimum_of_timeOne x cap F.1
    (PakAllFrameCapacityInitialReadback.fibre_timeOneConfig x cap F)

theorem every_frame_minimum (x : ConcretePakSide.Word) (F : Frames x) :
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤
      (frameCapacity x F).val :=
  fibre_minimum x (frameCapacity x F) ⟨F, rfl⟩

theorem insufficient_capacity_isEmpty (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hshort : cap.val < PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length) :
    IsEmpty (CapacityFibre x cap) :=
  ⟨fun F => (Nat.not_le_of_lt hshort) (fibre_minimum x cap F)⟩

theorem insufficient_capacity_count_zero (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hshort : cap.val < PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length) :
    capacityFibreCount x cap = 0 :=
  Nat.card_eq_zero.mpr (Or.inl (insufficient_capacity_isEmpty x cap hshort))

theorem fibre_front_cancellation (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (F : CapacityFibre x cap) :
    ∃ d labels,
      PakGeneralCapacityOuterFrontStandard.CapacitySideCopierRealize x cap
        (fibre_minimum x cap F) (groupResult x cap) d ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      Prefix labels (capacityEncodedParserConfig x cap) d ∧
      d.state = .sim MStarULogAssembly.data.uStart ∧
      (∀ T, Nonempty (FirstHitWordsAtMost (capacityEncodedParserConfig x cap)
        (labels.length + T) ≃ FirstHitWordsAtMost d T)) ∧
      (∀ T, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap)
        (labels.length + T)) = Nat.card (FirstHitWordsAtMost d T)) ∧
      (∀ B, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap) B) =
        if labels.length ≤ B then Nat.card (FirstHitWordsAtMost d (B - labels.length)) else 0) ∧
      (∀ B, B < labels.length →
        Nat.card (FirstHitWordsAtMost (capacityEncodedParserConfig x cap) B) = 0) :=
  capacity_outer_front_all_word_cancellation x cap (fibre_minimum x cap F)

def all_frame_capacity_minimum_spec : Prop :=
  (∀ (x : ConcretePakSide.Word) (F : Frames x),
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤
      (frameCapacity x F).val) ∧
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x),
    cap.val < PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length →
      IsEmpty (CapacityFibre x cap) ∧ capacityFibreCount x cap = 0) ∧
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (F : CapacityFibre x cap),
    ∃ d labels, Prefix labels (capacityEncodedParserConfig x cap) d ∧
      d.state = .sim MStarULogAssembly.data.uStart ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      (∀ B, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap) B) =
        if labels.length ≤ B then Nat.card (FirstHitWordsAtMost d (B - labels.length)) else 0))

theorem all_frame_capacity_minimum_spec_holds : all_frame_capacity_minimum_spec := by
  refine ⟨every_frame_minimum, ?_, ?_⟩
  · exact fun x cap h => ⟨insufficient_capacity_isEmpty x cap h,
      insufficient_capacity_count_zero x cap h⟩
  · intro x cap F
    obtain ⟨d, labels, hd, hb, hp, hs, he, hc, hall, hshort⟩ :=
      fibre_front_cancellation x cap F
    exact ⟨d, labels, hp, hs, hb, hall⟩

end PakFixedPolyomino.PakAllFrameCapacityMinimumReadback
