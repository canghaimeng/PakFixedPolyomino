import PakFixedPolyomino.PakAllCapacityFrameParserWordBijection
import PakFixedPolyomino.PakCapacityFrontFramedEndpoint

/-! Exact ALL original fibre count at the actual deterministic front length.
Every capacity is retained, including copier shortages and too-short square
deadlines. Framing guards, spatial realization and word inverses are internal. -/
namespace PakFixedPolyomino.PakAllCapacityFrameFramedCount
open PakSlotOneScannerMultiplicity PakGeneralCapacityInitialWindow
open PakAllFrameCapacityWeightedPartition PakAllCapacityFrameParserWordBijection
open PakCapacityFrontFramedEndpoint PakCapacityOuterFrontDeterministicPrefix
open PakOuterULogBridge MStarFixedWidthFirstHitEquiv

theorem minimum_front_framed (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      (∀ B, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap) B) =
        if labels.length ≤ B then
          Nat.card (FirstHitWordsAtMost
            (anchoredFramedULogConfig ULogControl.qStart origin
              (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
            (B - labels.length)) else 0) := by
  obtain ⟨d, labels, hd, hb, hp, hs, he, hc, hall, hshort⟩ :=
    capacity_outer_front_all_word_cancellation x cap hmin
  obtain ⟨origin, hdframe⟩ := group_realize_framed x cap hmin d hd
  exact ⟨origin, labels, hdframe ▸ hp, hb, hdframe ▸ hall⟩

theorem minimum_fibre_front_count (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      capacityFibreCount x cap =
        if labels.length ≤ ConcretePakSide.sideValue x - 1 then
          Nat.card (FirstHitWordsAtMost
            (anchoredFramedULogConfig ULogControl.qStart origin
              (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
            (ConcretePakSide.sideValue x - 1 - labels.length)) else 0 := by
  obtain ⟨origin, labels, hp, hb, hall⟩ := minimum_front_framed x cap hmin
  exact ⟨origin, labels, hp, hb,
    (capacity_fibre_count_eq_all_parser_words x cap).trans
      (hall (ConcretePakSide.sideValue x - 1))⟩

theorem all_fibre_front_count_cases (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    (cap.val < PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length →
      capacityFibreCount x cap = 0) ∧
    (PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val →
      ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
        Prefix labels (capacityEncodedParserConfig x cap)
          (anchoredFramedULogConfig ULogControl.qStart origin
            (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
        labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
        capacityFibreCount x cap =
          if labels.length ≤ ConcretePakSide.sideValue x - 1 then
            Nat.card (FirstHitWordsAtMost
              (anchoredFramedULogConfig ULogControl.qStart origin
                (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
              (ConcretePakSide.sideValue x - 1 - labels.length)) else 0) :=
  ⟨PakAllFrameCapacityMinimumReadback.insufficient_capacity_count_zero x cap,
    minimum_fibre_front_count x cap⟩

def all_capacity_frame_framed_count_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x),
    (cap.val < PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length →
      capacityFibreCount x cap = 0) ∧
    (PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val →
      ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
        Prefix labels (capacityEncodedParserConfig x cap)
          (anchoredFramedULogConfig ULogControl.qStart origin
            (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
        labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
        capacityFibreCount x cap =
          if labels.length ≤ ConcretePakSide.sideValue x - 1 then
            Nat.card (FirstHitWordsAtMost
              (anchoredFramedULogConfig ULogControl.qStart origin
                (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
              (ConcretePakSide.sideValue x - 1 - labels.length)) else 0)

theorem all_capacity_frame_framed_count_spec_holds : all_capacity_frame_framed_count_spec :=
  all_fibre_front_count_cases

end PakFixedPolyomino.PakAllCapacityFrameFramedCount
