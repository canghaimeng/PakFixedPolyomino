import PakFixedPolyomino.PakCapacityFrameWordReadback
import PakFixedPolyomino.PakAllFrameChronologicalSuffixInjectivity

/-! EVERY original capacity fibre is equivalent to EVERY original accepting
parser word of its physical deadline. The forward frame is constructed from
the actual word; no canonical-image or supplied inverse/count certificate. -/
namespace PakFixedPolyomino.PakAllCapacityFrameParserWordBijection
noncomputable section
open PakMStarCouplingCorrectness PakGeneralCapacityInitialWindow
open PakSlotOneScannerMultiplicity PakAllFrameCapacityWeightedPartition
open PakCapacityAcceptedWordFullFrame PakCapacityFrameWordReadback
open PakAllFrameChronologicalSuffixInjectivity PakFullFrameTableauReadback
open PakScannerBaselineAutomaton MStarFullFrameFirstHitReadback
open MStarFixedWidthFirstHitEquiv FiniteOneTapeSemantics

def parserFullWord (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :
    AcceptedWordsAtLength (capacityEncodedStartConfig x c) (ConcretePakSide.sideValue x) := by
  refine ⟨PakEncodedStart.startOneArrow :: w.1, ?_, ?_⟩
  · simp only [List.length_cons, w.2.1]
    have := PakSideScanner.sideValue_pos x
    omega
  · obtain ⟨d, hr, hd⟩ := w.2.2
    exact ⟨d, by
      rw [run_cons, capacityEncodedStart_slotOne_step, Option.bind_some]
      exact hr, hd⟩

def acceptedWordFrame (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedStartConfig x c) (ConcretePakSide.sideValue x)) :
    FullFrame (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) :=
  capacityAcceptedWordFullFrame x c w.1 (Classical.choose w.2.2)
    (Classical.choose_spec w.2.2).1 (Classical.choose_spec w.2.2).2 w.2.1

theorem accepted_word_frame_scanner (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedStartConfig x c) (ConcretePakSide.sideValue x)) :
    FullFrame.toScannerPath (acceptedWordFrame x c w) = capacityScannerPath x c :=
  capacity_frame_scanner _ _ _ _ _ _ _

theorem accepted_word_frame_word (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedStartConfig x c) (ConcretePakSide.sideValue x)) :
    frameWord (acceptedWordFrame x c w) = w.1 :=
  capacity_frame_word _ _ _ _ _ _ _

def parserWordToSlotOne (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) : Frames x := by
  let F := acceptedWordFrame x c (parserFullWord x c w)
  refine ⟨F, ?_⟩
  have hword : frameWord F = PakEncodedStart.startOneArrow :: w.1 :=
    accepted_word_frame_word x c (parserFullWord x c w)
  have hzero := congrArg (fun l : List MStarULogAssembly.Arrow => l[0]?) hword
  have hfirst : (FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩ =
      PakEncodedStart.startOneArrow := by
    simpa only [frameWord, List.getElem?_ofFn, dif_pos F.width_pos,
      List.getElem?_cons_zero, Option.some.injEq] using hzero
  change ((FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 1
  rw [hfirst]
  rfl

theorem parser_word_slot_one_scanner (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :
    FullFrame.toScannerPath (parserWordToSlotOne x c w).1 = capacityScannerPath x c :=
  accepted_word_frame_scanner x c (parserFullWord x c w)

theorem parser_word_slot_one_capacity (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :
    frameCapacity x (parserWordToSlotOne x c w) = c := by
  apply capacityScannerPath_injective x
  exact (frame_capacity_spec x _).symm.trans (parser_word_slot_one_scanner x c w)

def parserWordToFibre (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) : CapacityFibre x c :=
  ⟨parserWordToSlotOne x c w, parser_word_slot_one_capacity x c w⟩

theorem parser_word_to_fibre_word (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :
    frameWord (parserWordToFibre x c w).1.1 = PakEncodedStart.startOneArrow :: w.1 :=
  accepted_word_frame_word x c (parserFullWord x c w)

theorem suffix_forward_inverse (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (w : AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :
    fibreSuffixWord x c (parserWordToFibre x c w) = w := by
  apply Subtype.ext
  rw [fibre_suffix_val, parser_word_to_fibre_word]
  simp

theorem forward_suffix_inverse (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    parserWordToFibre x c (fibreSuffixWord x c F) = F := by
  apply fibre_suffix_injective x c
  exact suffix_forward_inverse x c _

def allCapacityFrameParserWordEquiv (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    CapacityFibre x c ≃ AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1) where
  toFun := fibreSuffixWord x c
  invFun := parserWordToFibre x c
  left_inv := forward_suffix_inverse x c
  right_inv := suffix_forward_inverse x c

theorem capacity_fibre_count_eq_all_parser_words (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    capacityFibreCount x c = Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1)) :=
  Nat.card_congr (allCapacityFrameParserWordEquiv x c)

def all_capacity_frame_parser_bijection_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x),
    ∃ e : CapacityFibre x c ≃ AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1),
      (∀ F, e F = fibreSuffixWord x c F) ∧
      (∀ w, frameWord (e.symm w).1.1 = PakEncodedStart.startOneArrow :: w.1) ∧
      capacityFibreCount x c = Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x c)
        (ConcretePakSide.sideValue x - 1))

theorem all_capacity_frame_parser_bijection_spec_holds :
    all_capacity_frame_parser_bijection_spec := by
  intro x c
  exact ⟨allCapacityFrameParserWordEquiv x c, fun _ => rfl,
    parser_word_to_fibre_word x c, capacity_fibre_count_eq_all_parser_words x c⟩

end
end PakFixedPolyomino.PakAllCapacityFrameParserWordBijection
