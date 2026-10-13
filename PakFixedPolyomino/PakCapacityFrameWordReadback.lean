import PakFixedPolyomino.PakCapacityAcceptedWordFullFrame
import PakFixedPolyomino.MStarFullFrameFirstHitReadback
import PakFixedPolyomino.PakFullFrameTableauRoundtrip

/-! Complete occurrence-labelled chronology and scanner readback of the
actual accepted-word frame. Token equality retains occupied slot labels. -/
namespace PakFixedPolyomino.PakCapacityFrameWordReadback
open PakMStarCouplingCorrectness PakFullFrameTableauReadback
open PakFullFrameTableauRoundtrip PakScannerBaselineAutomaton
open PakSlotZeroFullFrameStandardBijection
open PakCapacityAcceptedWordFullFrame PakSlotOneScannerMultiplicity
open MStarFullFrameFirstHitReadback MStarCapacityAcceptedWordWindow
open MStarHashWindowPersistence PakGeneralCapacityInitialWindow

theorem generated_tableau_arrow {w h : Nat} (F : FullFrame w h)
    (R : UniformWindowedMStarRun h w) (htableau : F.tableau = R.tableauTiling)
    (t : Fin w) : (FullFrame.toUniformWindowedRun F).arrow t = R.arrow t := by
  let i := reverseColumn t
  let j := (R.stepWindow t).head_index
  let Q := FullFrame.tableau_column_readback F i
  have hrev : UniformWindowedMStarRun.revTime i = t := by
    apply Fin.ext
    dsimp [UniformWindowedMStarRun.revTime, i, reverseColumn]
    omega
  have hcell : tableauAt F.tiling i j = R.tileAt t j := by
    have hc := congrFun (congrFun (congrArg Subtype.val htableau) i) j
    change tableauAt F.tiling i j = R.tileAt (UniformWindowedMStarRun.revTime i) j at hc
    simpa only [hrev] using hc
  have htoken : (tableauAt F.tiling i j).1.northToken = some (R.arrow t) := by
    rw [hcell, R.tileAt_northToken]
    simp only [j, if_pos rfl]
    rfl
  have hforced := FullFrame.tableau_column_north_token_forced F i j
  have hchoice : (if j = Q.head then some Q.arrow else none) = some (R.arrow t) :=
    hforced.symm.trans htoken
  have hj : j = Q.head := by
    by_contra hn
    simp [hn] at hchoice
  rw [if_pos hj] at hchoice
  change Q.arrow = R.arrow t
  exact Option.some.inj hchoice

theorem generated_tableau_word {w h : Nat} (F : FullFrame w h)
    (R : UniformWindowedMStarRun h w) (htableau : F.tableau = R.tableauTiling) :
    frameWord F = List.ofFn R.arrow := by
  unfold frameWord
  congr 1
  funext t
  exact generated_tableau_arrow F R htableau t

theorem scanner_path_of_projection {n : Nat} (F : FullFrame n n)
    (P : ScannerPath n) (hscan : scannerProjection F.tiling = P.toEastTiling) :
    FullFrame.toScannerPath F = P := by
  apply ScannerPath.toEastTiling_injective
  exact (FullFrame.scannerColumnReadback F).tiling_eq_pathTiling.symm.trans hscan

theorem capacity_frame_scanner (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    FullFrame.toScannerPath (capacityAcceptedWordFullFrame x cap labels d hr hd hlen) =
      capacityScannerPath x cap := by
  apply scanner_path_of_projection
  exact congrArg FrameReadout.scanner (FullTrackRunCertificate.toFullFrame_readout
    (PakGeneralCapacityFullFrameForwardStandard.capacitySquareFullTrackCertificate x cap
      (capacityAcceptedWordPaddedRun x cap labels d hr hd hlen)))

theorem capacity_frame_arrow (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x)
    (t : Fin (ConcretePakSide.sideValue x)) :
    (FullFrame.toUniformWindowedRun (capacityAcceptedWordFullFrame x cap labels d hr hd hlen)).arrow t =
      labels.get ⟨t.1, by omega⟩ :=
  (generated_tableau_arrow _ _
    (capacity_accepted_word_full_frame_tableau x cap labels d hr hd hlen) t).trans
      ((capacity_square_word_window_spec x cap labels d hr hd hlen).2.2.2 t)

theorem capacity_frame_word (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    frameWord (capacityAcceptedWordFullFrame x cap labels d hr hd hlen) = labels := by
  apply List.ext_getElem
  · rw [frame_word_length, hlen]
  · intro i hi hj
    change (List.ofFn _)[i]'hi = labels[i]'hj
    exact (List.getElem_ofFn hi).trans
      (capacity_frame_arrow x cap labels d hr hd hlen ⟨i, by omega⟩)

def capacity_word_readback_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x),
    FullFrame.toScannerPath (capacityAcceptedWordFullFrame x cap labels d hr hd hlen) =
      capacityScannerPath x cap ∧
    frameWord (capacityAcceptedWordFullFrame x cap labels d hr hd hlen) = labels

theorem capacity_word_readback_spec_holds : capacity_word_readback_spec := by
  intro x cap labels d hr hd hlen
  exact ⟨capacity_frame_scanner x cap labels d hr hd hlen,
    capacity_frame_word x cap labels d hr hd hlen⟩

end PakFixedPolyomino.PakCapacityFrameWordReadback
