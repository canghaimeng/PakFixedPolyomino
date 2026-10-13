import PakFixedPolyomino.PakCapacityOuterFrontParserPrefix
import PakFixedPolyomino.PakOuterFirstHitPrefix

/-! Instantiate ALL first-hit cancellation using the internally constructed
literal capacity parser/copier trace. The minimum successful workspace is an
explicit local premise; frame-derived necessity and the source census remain
separate. Cutoffs use actual occupied prefix length, not its fuel upper bound. -/
namespace PakFixedPolyomino.PakCapacityOuterFrontDeterministicPrefix
open FiniteOneTapeSemantics
open PakGeneralCapacityInitialWindow PakSlotOneScannerMultiplicity
open PakGeneralCapacityOuterFrontStandard PakGeneralCapacityParserCopierFront
open PakOuterFirstHitPrefix MStarFixedWidthFirstHitEquiv

abbrev OuterConfig := PakParserOuterBridge.OuterConfig
abbrev OuterArrow := PakParserOuterBridge.OuterArrow
abbrev Prefix := DeterministicPrefix MStarULogAssembly.program
  MStarOuterProgram.movable MStarOuterProgram.State.accept

abbrev groupResult (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :=
  MStarCopierExecution.Result.groupReady
    (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
      (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.val)
      (capacityCopierJunk x) (capacityHashTail x cap))

theorem parserPrefix_deterministic {c d : OuterConfig} {labels : List OuterArrow}
    (h : PakCapacityOuterFrontParserPrefix.ParserPrefix labels c d) :
    Prefix labels c d := by
  induction h with
  | nil c => exact .nil c
  | @cons c mid finish labels a hs hp tail ih =>
      obtain ⟨q, hq⟩ := hp
      refine .cons hs ?_ ?_ ih
      · rw [hq]
        exact parser_state_ne_accept
      · intro b next hb
        exact (parser_occupied_arrow_unique c q a b mid next hq hs hb).1.symm

theorem capacity_outer_front_deterministic_prefix (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d labels, CapacitySideCopierRealize x cap hmin (groupResult x cap) d ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      Prefix labels (capacityEncodedParserConfig x cap) d := by
  obtain ⟨d, labels, hd, hb, hp⟩ :=
    PakCapacityOuterFrontParserPrefix.capacity_outer_front_parser_prefix x cap hmin
  exact ⟨d, labels, hd, hb, parserPrefix_deterministic hp⟩

theorem groupRealize_state (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val)
    (d : OuterConfig) (h : CapacitySideCopierRealize x cap hmin (groupResult x cap) d) :
    d.state = .sim MStarULogAssembly.data.uStart := by
  obtain ⟨origin, rfl⟩ := h.2
  rfl

noncomputable def firstHitPrefixEquiv {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (T : Nat) :
    FirstHitWordsAtMost c (labels.length + T) ≃ FirstHitWordsAtMost d T :=
  (firstAcceptingWords_equiv_firstHit c (labels.length + T)).symm.trans
    ((firstHit_prefix_equiv h).trans (firstAcceptingWords_equiv_firstHit d T))

theorem firstHitPrefix_count {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (T : Nat) :
    Nat.card (FirstHitWordsAtMost c (labels.length + T)) =
      Nat.card (FirstHitWordsAtMost d T) :=
  Nat.card_congr (firstHitPrefixEquiv h T)

theorem firstHitPrefix_short_zero {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (B : Nat) (hB : B < labels.length) :
    Nat.card (FirstHitWordsAtMost c B) = 0 := by
  rw [← Nat.card_congr (firstAcceptingWords_equiv_firstHit c B)]
  exact firstHit_short_zero h hB

noncomputable def fixedWidthPrefixEquiv {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (hc : c.state ≠ .accept) (T : Nat) :
    AcceptedWordsAtLength c (labels.length + T) ≃ FirstHitWordsAtMost d T :=
  (fixedWidthFirstHitEquiv c hc (labels.length + T)).trans (firstHitPrefixEquiv h T)

theorem fixedWidthPrefix_count_sub {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (hc : c.state ≠ .accept) (B : Nat)
    (hB : labels.length ≤ B) :
    Nat.card (AcceptedWordsAtLength c B) =
      Nat.card (FirstHitWordsAtMost d (B - labels.length)) := by
  have hb : labels.length + (B - labels.length) = B := by omega
  simpa only [hb] using Nat.card_congr (fixedWidthPrefixEquiv h hc (B - labels.length))

theorem fixedWidthPrefix_short_zero {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (hc : c.state ≠ .accept) (B : Nat)
    (hB : B < labels.length) : Nat.card (AcceptedWordsAtLength c B) = 0 := by
  rw [fixed_width_count_eq_first_hit_count c hc B]
  exact firstHitPrefix_short_zero h B hB

theorem fixedWidthPrefix_all_cutoffs {c d : OuterConfig} {labels : List OuterArrow}
    (h : Prefix labels c d) (hc : c.state ≠ .accept) (B : Nat) :
    Nat.card (AcceptedWordsAtLength c B) =
      if labels.length ≤ B then Nat.card (FirstHitWordsAtMost d (B - labels.length)) else 0 := by
  split_ifs with hb
  · exact fixedWidthPrefix_count_sub h hc B hb
  · exact fixedWidthPrefix_short_zero h hc B (by omega)

theorem capacity_outer_front_all_word_cancellation (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d labels, CapacitySideCopierRealize x cap hmin (groupResult x cap) d ∧
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
        Nat.card (FirstHitWordsAtMost (capacityEncodedParserConfig x cap) B) = 0) := by
  obtain ⟨d, labels, hd, hb, hp⟩ := capacity_outer_front_deterministic_prefix x cap hmin
  have hc : (capacityEncodedParserConfig x cap).state ≠ .accept := by
    change MStarOuterProgram.State.parser MStarULogAssembly.data.parserStart ≠ .accept
    exact parser_state_ne_accept
  refine ⟨d, labels, hd, hb, hp, groupRealize_state x cap hmin d hd, ?_, ?_, ?_, ?_⟩
  · exact fun T => ⟨firstHitPrefixEquiv hp T⟩
  · intro T
    exact Nat.card_congr (fixedWidthPrefixEquiv hp hc T)
  · exact fun B => fixedWidthPrefix_all_cutoffs hp hc B
  · exact fun B hB => firstHitPrefix_short_zero hp B hB

def capacity_front_cancellation_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val),
    ∃ d labels, CapacitySideCopierRealize x cap hmin (groupResult x cap) d ∧
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
        Nat.card (FirstHitWordsAtMost (capacityEncodedParserConfig x cap) B) = 0)

theorem capacity_front_cancellation_spec_holds : capacity_front_cancellation_spec :=
  capacity_outer_front_all_word_cancellation

end PakFixedPolyomino.PakCapacityOuterFrontDeterministicPrefix
