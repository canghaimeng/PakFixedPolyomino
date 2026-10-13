import PakFixedPolyomino.PakAllFrameCapacityInitialReadback
import PakFixedPolyomino.MStarFullFrameFirstHitReadback
import PakFixedPolyomino.PakSlotZeroFullFrameStandardBijection

/-! EVERY original square FullFrame is recovered from its scanner path and
entire occupied-arrow chronology. EVERY CapacityFibre maps injectively into
the original parser-config AcceptedWordsAtLength of length sideValue-1 by
dropping the actual first slot-one start arrow. -/

namespace PakFixedPolyomino.PakAllFrameChronologicalSuffixInjectivity

open PakAllFrameCapacityInitialReadback
open PakAllFrameCapacityWeightedPartition
open PakGeneralCapacityInitialWindow
open PakFullFrameTableauReadback
open PakScannerBaselineAutomaton
open PakSlotOneScannerMultiplicity
open PakMStarCouplingCorrectness
open PakSlotOneFullFrameReflection
open FiniteOneTapeSemantics
open MStarFullFrameFirstHitReadback
open MStarFixedWidthFirstHitEquiv
open PakSlotZeroFullFrameStandardBijection
open PakFullFrameTableauRoundtrip

theorem list_eq_get_cons_drop {α : Type*} (l : List α) (h : 0 < l.length) :
    l = l[0] :: l.drop 1 := by
  cases l with
  | nil => simp at h
  | cons a as => simp

theorem frameWord_arrow_eq {n : ℕ} (F G : FullFrame n n)
    (hword : frameWord F = frameWord G) :
    (FullFrame.toUniformWindowedRun F).arrow =
      (FullFrame.toUniformWindowedRun G).arrow := by
  funext t
  have hF : (frameWord F)[t.1]'(by simpa [frame_word_length] using t.2) =
      (FullFrame.toUniformWindowedRun F).arrow t := by
    simp [frameWord, List.getElem_ofFn]
  have hG : (frameWord G)[t.1]'(by simpa [frame_word_length] using t.2) =
      (FullFrame.toUniformWindowedRun G).arrow t := by
    simp [frameWord, List.getElem_ofFn]
  have hidx :
      (frameWord F)[t.1]'(by simpa [frame_word_length] using t.2) =
        (frameWord G)[t.1]'(by simpa [frame_word_length] using t.2) := by
    simp [hword]
  exact hF.symm.trans (hidx.trans hG)

theorem config_eq_of_same_path_and_arrows {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G)
    (harrow : (FullFrame.toUniformWindowedRun F).arrow =
      (FullFrame.toUniformWindowedRun G).arrow)
    (k : Fin (n + 1)) :
    (FullFrame.toUniformWindowedRun F).config k =
      (FullFrame.toUniformWindowedRun G).config k := by
  let RF := FullFrame.toUniformWindowedRun F
  let RG := FullFrame.toUniformWindowedRun G
  have hzero := east_before_eq_of_same_path F G hpath
  have aux : ∀ m (hm : m < n + 1), RF.config ⟨m, hm⟩ = RG.config ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; exact hzero
    | succ m ih =>
        intro hm
        have hm' : m < n := Nat.lt_of_succ_lt_succ hm
        have hF := RF.step ⟨m, hm'⟩
        have hG := RG.step ⟨m, hm'⟩
        apply step_label_deterministic MStarULogAssembly.program
          MStarOuterProgram.movable (RF.config ⟨m, Nat.lt_succ_of_lt hm'⟩)
          (RF.config ⟨m + 1, hm⟩) (RG.config ⟨m + 1, hm⟩)
          (RF.arrow ⟨m, hm'⟩)
        · simpa using hF
        · have ih' := ih (Nat.lt_succ_of_lt hm')
          have ha : RF.arrow ⟨m, hm'⟩ = RG.arrow ⟨m, hm'⟩ := congrFun harrow _
          rw [ih', ha]
          simpa using hG
  exact aux k.1 k.2

theorem headIndex_eq_of_config {n : ℕ} (F G : FullFrame n n)
    (hcfg : (FullFrame.toUniformWindowedRun F).config =
      (FullFrame.toUniformWindowedRun G).config)
    (k : Fin (n + 1)) :
    (FullFrame.toUniformWindowedRun F).head_index k =
      (FullFrame.toUniformWindowedRun G).head_index k := by
  let RF := FullFrame.toUniformWindowedRun F
  let RG := FullFrame.toUniformWindowedRun G
  have hF := RF.head_eq k
  have hG := RG.head_eq k
  apply Fin.ext
  change (RF.head_index k).1 = (RG.head_index k).1
  have hcfgk : RF.config k = RG.config k := congrFun hcfg k
  rw [hcfgk] at hF
  change (RG.config k).head = 0 + (RF.head_index k).1 at hF
  change (RG.config k).head = 0 + (RG.head_index k).1 at hG
  omega

theorem uniformRun_ext {n : ℕ}
    (R S : UniformWindowedMStarRun n n)
    (hconfig : R.config = S.config) (harrow : R.arrow = S.arrow)
    (horigin : R.origin = S.origin) (hhead : R.head_index = S.head_index) :
    R = S := by
  cases R
  cases S
  simp only at hconfig harrow horigin hhead ⊢
  subst_vars
  rfl

theorem uniformRun_eq_of_path_and_frameWord {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G)
    (hword : frameWord F = frameWord G) :
    FullFrame.toUniformWindowedRun F = FullFrame.toUniformWindowedRun G := by
  let RF := FullFrame.toUniformWindowedRun F
  let RG := FullFrame.toUniformWindowedRun G
  have harrow := frameWord_arrow_eq F G hword
  have hcfg : RF.config = RG.config := by
    funext k
    exact config_eq_of_same_path_and_arrows F G hpath harrow k
  have hhead : RF.head_index = RG.head_index := by
    funext k
    exact headIndex_eq_of_config F G hcfg k
  have horigin : RF.origin = RG.origin := rfl
  exact uniformRun_ext RF RG hcfg harrow horigin hhead

theorem fullFrame_eq_of_path_and_frameWord {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G)
    (hword : frameWord F = frameWord G) : F = G := by
  have hrun := uniformRun_eq_of_path_and_frameWord F G hpath hword
  have htableau : tableauProjection F.tiling = tableauProjection G.tiling := by
    calc
      tableauProjection F.tiling =
          (FullFrame.toUniformWindowedRun F).tableauTiling :=
            FullFrame.tableauProjection_eq_roundtrip F
      _ = (FullFrame.toUniformWindowedRun G).tableauTiling :=
            congrArg UniformWindowedMStarRun.tableauTiling hrun
      _ = tableauProjection G.tiling :=
            (FullFrame.tableauProjection_eq_roundtrip G).symm
  apply FullFrame.ext
  apply coupledTiling_ext_of_projections
  · exact amplifierProjection_eq_of_fullFrames F G
  · exact rippleProjection_eq_of_fullFrames F G
  · exact htableau
  · exact scannerProjection_eq_of_same_path F G hpath

theorem frameWord_eq_cons_drop {n : ℕ} (F : FullFrame n n) (hn : 0 < n) :
    frameWord F =
      (FullFrame.toUniformWindowedRun F).arrow ⟨0, hn⟩ ::
        (frameWord F).drop 1 := by
  have hlen : 0 < (frameWord F).length := by
    simpa [frame_word_length] using hn
  have hcons := list_eq_get_cons_drop (frameWord F) hlen
  have hget :
      (frameWord F)[0]'(by simpa [frame_word_length] using hn) =
        (FullFrame.toUniformWindowedRun F).arrow ⟨0, hn⟩ := by
    simp [frameWord, List.getElem_ofFn]
  simpa [hget] using hcons

theorem fibre_suffix_length (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    ((frameWord F.1.1).drop 1).length = ConcretePakSide.sideValue x - 1 := by
  have hlen := frame_word_length F.1.1
  simp [hlen]

theorem fibre_suffix_run (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    ∃ d, run MStarULogAssembly.program MStarOuterProgram.movable
        ((frameWord F.1.1).drop 1) (capacityEncodedParserConfig x c) =
          some d ∧ d.state = MStarOuterProgram.State.accept := by
  let n := ConcretePakSide.sideValue x
  let RF := FullFrame.toUniformWindowedRun F.1.1
  have hn : 0 < n := PakSideScanner.sideValue_pos x
  have hcons := frameWord_eq_cons_drop F.1.1 hn
  have hidx : (⟨0, hn⟩ : Fin n) = ⟨0, F.1.1.width_pos⟩ := Fin.ext rfl
  have harrow :
      RF.arrow ⟨0, hn⟩ = PakEncodedStart.startOneArrow := by
    rw [hidx]
    exact fibre_firstArrow x c F
  have hcfg0 : RF.config ⟨0, Nat.zero_lt_succ n⟩ =
      capacityEncodedStartConfig x c := fibre_firstConfig x c F
  have hfull := frame_word_run F.1.1
  rw [hcons, harrow, run_cons] at hfull
  have hstep :
      step MStarULogAssembly.program MStarOuterProgram.movable
        (RF.config ⟨0, Nat.zero_lt_succ n⟩) PakEncodedStart.startOneArrow =
          some (capacityEncodedParserConfig x c) := by
    rw [hcfg0]
    exact capacityEncodedStart_slotOne_step x c
  rw [hstep, Option.bind_some] at hfull
  exact ⟨RF.config ⟨n, Nat.lt_succ_self n⟩, hfull, RF.final_accept⟩

noncomputable def fibreSuffixWord (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (F : CapacityFibre x c) :
    AcceptedWordsAtLength (capacityEncodedParserConfig x c)
      (ConcretePakSide.sideValue x - 1) :=
  ⟨(frameWord F.1.1).drop 1, fibre_suffix_length x c F,
    fibre_suffix_run x c F⟩

theorem fibre_suffix_val (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    (fibreSuffixWord x c F).1 = (frameWord F.1.1).drop 1 := rfl

theorem fibre_suffix_injective (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    Function.Injective (fibreSuffixWord x c) := by
  intro F G hFG
  have hdrop : (frameWord F.1.1).drop 1 = (frameWord G.1.1).drop 1 :=
    congrArg Subtype.val hFG
  have hn : 0 < ConcretePakSide.sideValue x :=
    PakSideScanner.sideValue_pos x
  have hFcons := frameWord_eq_cons_drop F.1.1 hn
  have hGcons := frameWord_eq_cons_drop G.1.1 hn
  have hidxF : (⟨0, hn⟩ : Fin (ConcretePakSide.sideValue x)) =
      ⟨0, F.1.1.width_pos⟩ := Fin.ext rfl
  have hidxG : (⟨0, hn⟩ : Fin (ConcretePakSide.sideValue x)) =
      ⟨0, G.1.1.width_pos⟩ := Fin.ext rfl
  have hAF :
      (FullFrame.toUniformWindowedRun F.1.1).arrow ⟨0, hn⟩ =
        PakEncodedStart.startOneArrow := by
    rw [hidxF]; exact fibre_firstArrow x c F
  have hAG :
      (FullFrame.toUniformWindowedRun G.1.1).arrow ⟨0, hn⟩ =
        PakEncodedStart.startOneArrow := by
    rw [hidxG]; exact fibre_firstArrow x c G
  have hword : frameWord F.1.1 = frameWord G.1.1 := by
    rw [hFcons, hGcons, hAF, hAG, hdrop]
  have hpath :
      FullFrame.toScannerPath F.1.1 = FullFrame.toScannerPath G.1.1 :=
    (fibre_scanner_eq x c F).trans (fibre_scanner_eq x c G).symm
  have hFF : F.1.1 = G.1.1 :=
    fullFrame_eq_of_path_and_frameWord F.1.1 G.1.1 hpath hword
  apply Subtype.ext
  apply Subtype.ext
  exact hFF

theorem fibre_suffix_card_le (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    capacityFibreCount x c ≤
      Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x c)
        (ConcretePakSide.sideValue x - 1)) := by
  have := accepted_words_finite (capacityEncodedParserConfig x c)
    (ConcretePakSide.sideValue x - 1)
  simpa [capacityFibreCount] using
    Nat.card_le_card_of_injective (fibreSuffixWord x c)
      (fibre_suffix_injective x c)

def all_frame_chronological_suffix_spec : Prop :=
  (∀ (n : ℕ) (F G : FullFrame n n),
    FullFrame.toScannerPath F = FullFrame.toScannerPath G →
      frameWord F = frameWord G → F = G) ∧
  (∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x)
      (F : CapacityFibre x c),
    (fibreSuffixWord x c F).1 = (frameWord F.1.1).drop 1) ∧
  (∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x),
    Function.Injective (fibreSuffixWord x c)) ∧
  (∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x),
    capacityFibreCount x c ≤
      Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x c)
        (ConcretePakSide.sideValue x - 1)))

theorem all_frame_chronological_suffix_spec_holds :
    all_frame_chronological_suffix_spec :=
  ⟨fun _n F G => fullFrame_eq_of_path_and_frameWord F G,
    fun x c F => fibre_suffix_val x c F,
    fun x c => fibre_suffix_injective x c,
    fun x c => fibre_suffix_card_le x c⟩

end PakFixedPolyomino.PakAllFrameChronologicalSuffixInjectivity
