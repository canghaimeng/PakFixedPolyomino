import PakFixedPolyomino.MStarCapacityAcceptedWordWindow
import PakFixedPolyomino.PakGeneralCapacityFullFrameForwardStandard
import PakFixedPolyomino.PakSlotOneFrameCapacityReadbackStandard

/-! Every actual accepting word of square length from the literal capacity
input supplies the original capacity full-frame constructor's time and east
strip contracts internally. No spatial or emission certificate is assumed. -/
namespace PakFixedPolyomino.PakCapacityAcceptedWordFullFrame
open FiniteOneTapeSemantics PakMStarCouplingCorrectness
open PakSlotOneScannerMultiplicity PakGeneralCapacityInitialWindow
open MStarHashWindowPersistence MStarCapacityAcceptedWordWindow
open PakGeneralCapacityFullFrameForward

def castTime {width n m : Nat} (h : n = m)
    (W : PaddedUniformWindowedMStarRun width n) :
    PaddedUniformWindowedMStarRun width m := h ▸ W

theorem castTime_origin {width n m : Nat} (h : n = m)
    (W : PaddedUniformWindowedMStarRun width n) :
    (castTime h W).run.origin = W.run.origin := by
  subst m
  rfl

theorem castTime_config {width n m : Nat} (h : n = m)
    (W : PaddedUniformWindowedMStarRun width n) (k : Nat) (hk : k ≤ m) :
    (castTime h W).run.config ⟨k, by omega⟩ =
      W.run.config ⟨k, by omega⟩ := by
  subst m
  rfl

theorem castTime_arrow {width n m : Nat} (h : n = m)
    (W : PaddedUniformWindowedMStarRun width n) (k : Nat) (hk : k < m) :
    (castTime h W).run.arrow ⟨k, hk⟩ =
      W.run.arrow ⟨k, by omega⟩ := by
  subst m
  rfl

noncomputable def capacitySquareWordWindow (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    PaddedUniformWindowedMStarRun
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) :=
  castTime hlen (capacityAcceptedWordWindow x cap labels d hr hd)

theorem capacity_square_word_window_spec (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    let W := capacitySquareWordWindow x cap labels d hr hd hlen
    W.run.origin = 0 ∧
    W.run.config ⟨0, Nat.zero_lt_succ _⟩ = capacityEncodedStartConfig x cap ∧
    W.run.config ⟨ConcretePakSide.sideValue x, Nat.lt_succ_self _⟩ = d ∧
    (∀ t, W.run.arrow t = labels.get ⟨t.1, by omega⟩) := by
  obtain ⟨ho, hs, hf, ha⟩ := capacity_accepted_word_window_spec x cap labels d hr hd
  dsimp only [capacitySquareWordWindow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [castTime_origin]
    exact ho
  · rw [castTime_config hlen _ 0 (Nat.zero_le _)]
    exact hs
  · rw [castTime_config hlen _ (ConcretePakSide.sideValue x) (Nat.le_refl _)]
    have hi : (⟨ConcretePakSide.sideValue x, by omega⟩ : Fin (labels.length + 1)) =
        ⟨labels.length, Nat.lt_succ_self _⟩ := Fin.ext hlen.symm
    rw [hi]
    exact hf
  · intro t
    rw [castTime_arrow]
    exact ha _

theorem capacity_padded_east_old (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (W : PaddedUniformWindowedMStarRun
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x))
    (ho : W.run.origin = 0)
    (hs : W.run.config ⟨0, Nat.zero_lt_succ _⟩ = capacityEncodedStartConfig x cap)
    (j : Fin (ConcretePakSide.sideValue x)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
      ((capacityScannerPath x cap).states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      ((capacityScannerPath x cap).states ⟨j.1 + 1, by omega⟩) =
      (W.run.tableauTiling.1 (capacityEastIndex x) j).1.old := by
  have hheight := PakSideScanner.sideScannerHeight x
  have hj : j.1 < (PakSideScanner.sideScannerBits x).length + 2 := by omega
  rw [capacityScannerPath,
    PakSlotOneFrameCapacityReadbackStandard.scannerPath_cast_states hheight
      (rawCapacityScannerPath x cap) j.1 (by omega),
    PakSlotOneFrameCapacityReadbackStandard.scannerPath_cast_states hheight
      (rawCapacityScannerPath x cap) (j.1 + 1) (by omega)]
  change PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
      (PakScannerTerminal.terminalScannerState (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x) (capacityTerminalIndex x cap) j.1)
      (PakScannerTerminal.terminalScannerState (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x) (capacityTerminalIndex x cap) (j.1 + 1)) = _
  rw [capacityScannerColumn_emits_capacityInitialWindow x cap ⟨j.1, hj⟩,
    UniformWindowedMStarRun.tableauTiling_cell_old]
  have hrev : UniformWindowedMStarRun.revTime (capacityEastIndex x) =
      (⟨0, capacitySide_pos x⟩ : Fin (ConcretePakSide.sideValue x)) := by
    apply Fin.ext
    simp [UniformWindowedMStarRun.revTime, capacityEastIndex]
  rw [hrev]
  unfold WindowedMStarStep.oldStrip WindowedMStarStep.triple
    WindowedMStarStep.position WindowedMStarStep.cell capacityInitialWindow
  simp only [UniformWindowedMStarRun.stepWindow, ho, hs, Int.zero_add]
  apply CellTriple.ext
  · exact capacityInitialTableauCell_eq_configCell x cap ((j.1 : Int) - 1)
  · exact capacityInitialTableauCell_eq_configCell x cap (j.1 : Int)
  · exact capacityInitialTableauCell_eq_configCell x cap ((j.1 : Int) + 1)

noncomputable def capacityAcceptedWordPaddedRun (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    CapacitySquarePaddedRun x cap where
  padded := capacitySquareWordWindow x cap labels d hr hd hlen
  east_old := capacity_padded_east_old x cap _
    (capacity_square_word_window_spec x cap labels d hr hd hlen).1
    (capacity_square_word_window_spec x cap labels d hr hd hlen).2.1

noncomputable def capacityAcceptedWordFullFrame (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    FullFrame (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) :=
  PakGeneralCapacityFullFrameForwardStandard.capacitySquareFullFrame x cap
    (capacityAcceptedWordPaddedRun x cap labels d hr hd hlen)

theorem capacity_accepted_word_full_frame_tableau (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) (hlen : labels.length = ConcretePakSide.sideValue x) :
    (capacityAcceptedWordFullFrame x cap labels d hr hd hlen).tableau =
      (capacitySquareWordWindow x cap labels d hr hd hlen).run.tableauTiling :=
  FullTrackRunCertificate.toFullFrame_tableau _

def actual_capacity_word_frame_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (labels : List Arrow) (d : Config),
    run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d → d.state = .accept →
    ∀ hlen : labels.length = ConcretePakSide.sideValue x,
    ∃ R : CapacitySquarePaddedRun x cap,
      R.padded.run.origin = 0 ∧
      R.padded.run.config ⟨0, Nat.zero_lt_succ _⟩ = capacityEncodedStartConfig x cap ∧
      R.padded.run.config ⟨ConcretePakSide.sideValue x, Nat.lt_succ_self _⟩ = d ∧
      (∀ t, R.padded.run.arrow t = labels.get ⟨t.1, by omega⟩) ∧
      ∃ F : FullFrame (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x),
        F.tableau = R.padded.run.tableauTiling

theorem actual_capacity_word_frame_spec_holds : actual_capacity_word_frame_spec := by
  intro x cap labels d hr hd hlen
  obtain ⟨ho, hs, hf, ha⟩ := capacity_square_word_window_spec x cap labels d hr hd hlen
  exact ⟨capacityAcceptedWordPaddedRun x cap labels d hr hd hlen, ho, hs, hf, ha,
    capacityAcceptedWordFullFrame x cap labels d hr hd hlen,
    capacity_accepted_word_full_frame_tableau x cap labels d hr hd hlen⟩

end PakFixedPolyomino.PakCapacityAcceptedWordFullFrame
