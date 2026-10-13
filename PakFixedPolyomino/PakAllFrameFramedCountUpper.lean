import PakFixedPolyomino.PakAllFrameChronologicalSuffixInjectivity
import PakFixedPolyomino.PakCapacityFrontFramedEndpoint

/-! ALL capacity-fibre counts are bounded by the ALL framed interpreter
first-hit carrier at the exact remaining chronological deadline. Zero fibres
and short capacities are retained; no canonical-image count is substituted. -/
namespace PakFixedPolyomino.PakAllFrameFramedCountUpper
open PakAllFrameCapacityWeightedPartition PakSlotOneScannerMultiplicity
open PakGeneralCapacityInitialWindow PakCapacityOuterFrontDeterministicPrefix
open PakCapacityFrontFramedEndpoint PakOuterULogBridge MStarFixedWidthFirstHitEquiv

theorem fibre_count_pos (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) : 0 < capacityFibreCount x cap := by
  letI : Nonempty (CapacityFibre x cap) := ⟨F⟩
  exact Nat.card_pos

theorem fibre_front_framed_upper (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) :
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ ConcretePakSide.sideValue x - 1 ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      capacityFibreCount x cap ≤ Nat.card (FirstHitWordsAtMost
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
        (ConcretePakSide.sideValue x - 1 - labels.length)) := by
  obtain ⟨origin, labels, hp, hb, hall⟩ := fibre_front_framed x cap F
  have hu := PakAllFrameChronologicalSuffixInjectivity.fibre_suffix_card_le x cap
  have hwidth : labels.length ≤ ConcretePakSide.sideValue x - 1 := by
    by_contra hshort
    have hz := hall (ConcretePakSide.sideValue x - 1)
    rw [if_neg hshort] at hz
    have hpos := fibre_count_pos x cap F
    rw [hz] at hu
    omega
  refine ⟨origin, labels, hp, hwidth, hb, ?_⟩
  have he := hall (ConcretePakSide.sideValue x - 1)
  rw [if_pos hwidth] at he
  exact hu.trans_eq he

theorem every_capacity_count_zero_or_framed_upper (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) :
    capacityFibreCount x cap = 0 ∨
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ ConcretePakSide.sideValue x - 1 ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      capacityFibreCount x cap ≤ Nat.card (FirstHitWordsAtMost
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
        (ConcretePakSide.sideValue x - 1 - labels.length)) := by
  classical
  by_cases hz : capacityFibreCount x cap = 0
  · exact Or.inl hz
  · right
    have hn : Nonempty (CapacityFibre x cap) :=
      (Nat.card_ne_zero.mp hz).1
    obtain ⟨F⟩ := hn
    exact fibre_front_framed_upper x cap F

end PakFixedPolyomino.PakAllFrameFramedCountUpper
