import PakFixedPolyomino.PakAllFrameCapacityWeightedPartition
import PakFixedPolyomino.PakGeneralCapacityInitialWindow
import PakFixedPolyomino.PakFullFrameTableauRoundtrip
import PakFixedPolyomino.PakSlotOneParserDecodeStandard
import PakFixedPolyomino.PakFullFrameFirstBranch

/-! Exact chronological initial readback of EVERY original slot-one frame
whose scanner path is an actual capacity path. Combinatorial only. -/

namespace PakFixedPolyomino.PakAllFrameCapacityInitialReadback

open PakAllFrameCapacityWeightedPartition
open PakGeneralCapacityInitialWindow
open PakFullFrameTableauReadback
open PakScannerBaselineAutomaton
open PakSlotOneScannerMultiplicity
open PakMStarCouplingCorrectness
open PakSlotOneFullFrameReflection
open FiniteOneTapeSemantics

abbrev Frames := PakAllFrameCapacityWeightedPartition.Frames
abbrev Cfg := PakMStarCouplingCorrectness.MStarConfig

noncomputable def firstConfig (x : ConcretePakSide.Word) (F : Frames x) : Cfg :=
  (FullFrame.toUniformWindowedRun F.1).config ⟨0, Nat.zero_lt_succ _⟩

noncomputable def timeOneConfig (x : ConcretePakSide.Word) (F : Frames x) : Cfg :=
  (FullFrame.toUniformWindowedRun F.1).config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩

noncomputable def firstArrow (x : ConcretePakSide.Word) (F : Frames x) :
    MStarULogAssembly.Arrow :=
  (FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩

theorem reverseColumn_zero_eq_east {n : ℕ} (F : FullFrame n n) :
    reverseColumn (⟨0, F.width_pos⟩ : Fin n) = eastIndex F.width_pos := by
  apply Fin.ext
  simp [reverseColumn, eastIndex]

theorem firstConfig_eq_east_before (x : ConcretePakSide.Word) (F : Frames x) :
    firstConfig x F =
      (FullFrame.tableau_column_readback F.1 (eastIndex F.1.width_pos)).before := by
  change FullFrame.reverse_tableau_config F.1 ⟨0, Nat.zero_lt_succ _⟩ = _
  rw [FullFrame.reverse_tableau_config_of_lt F.1 _ F.1.width_pos]
  rw [reverseColumn_zero_eq_east F.1]

theorem mstarConfig_ext (C D : Cfg)
    (hstate : C.state = D.state) (hhead : C.head = D.head)
    (htape : C.tape = D.tape) : C = D := by
  cases C; cases D
  simp_all

theorem capacity_path_state (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (k : ℕ) (hk : k ≤ ConcretePakSide.sideValue x) :
    (capacityScannerPath x c).states ⟨k, by omega⟩ =
      PakScannerTerminal.terminalScannerState
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x)
        (capacityTerminalIndex x c) k := by
  simpa [capacityScannerPath, rawCapacityScannerPath] using
    (PakSlotOneFrameCapacityReadbackStandard.scannerPath_cast_states
      (PakSideScanner.sideScannerHeight x) (rawCapacityScannerPath x c) k hk)

theorem cellLetter_capacityInitialTableau (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int) :
    OneTapeTableau.cellLetter (capacityInitialTableauCell x c z) =
      capacityInitialTape x c z := by
  rw [capacityInitialTableauCell_eq_configCell]
  by_cases hz : z = 1
  · simp [hz, OneTapeTableau.cellLetter, capacityEncodedStartConfig]
  · simp [hz, OneTapeTableau.cellLetter, capacityEncodedStartConfig]

theorem firstConfig_eq (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : Frames x)
    (hscan : FullFrame.toScannerPath F.1 = capacityScannerPath x c) :
    firstConfig x F = capacityEncodedStartConfig x c := by
  let U := FullFrame.toUniformWindowedRun F.1
  let east := FullFrame.tableau_column_readback F.1 (eastIndex F.1.width_pos)
  have hbefore := firstConfig_eq_east_before x F
  have hstate : (firstConfig x F).state = MStarOuterProgram.State.start :=
    FullFrame.uniform_initial_state_start F.1
  have hhead : (firstConfig x F).head = 1 := by
    have heq := U.head_eq ⟨0, Nat.zero_lt_succ _⟩
    have hidx := PakSlotOneParserDecodeStandard.slotOne_timeZero_headIndex_eq_one F
    have horigin : U.origin = 0 := rfl
    change (U.config ⟨0, Nat.zero_lt_succ _⟩).head = 1
    rw [heq, horigin, hidx]
    rfl
  apply mstarConfig_ext (firstConfig x F) (capacityEncodedStartConfig x c)
    (hstate.trans rfl) (hhead.trans rfl)
  funext z
  by_cases hz : 0 ≤ z ∧ z < (ConcretePakSide.sideValue x : Int)
  · let j : Fin (ConcretePakSide.sideValue x) := ⟨z.toNat, by omega⟩
    have hzj : (j.1 : Int) = z := Int.toNat_of_nonneg hz.1
    have hex := F.1.east_emits_tableau_window j
    rcases hex with ⟨s, t, hpair, hold⟩
    have hp : FullFrame.eastPair F.1 j = (s, t) :=
      Option.some.inj ((FullFrame.eastPair_spec F.1 j).symm.trans hpair)
    have hst :
        ((FullFrame.toScannerPath F.1).states ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
          (FullFrame.toScannerPath F.1).states ⟨j.1 + 1, by omega⟩) = (s, t) :=
      (FullFrame.eastPair_eq_states F.1 j).symm.trans hp
    have hs : s = PakScannerTerminal.terminalScannerState
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x)
        (capacityTerminalIndex x c) j.1 := by
      have := congrArg Prod.fst hst
      simpa [hscan, capacity_path_state x c j.1 (Nat.le_of_lt j.2)] using this.symm
    have ht : t = PakScannerTerminal.terminalScannerState
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x)
        (capacityTerminalIndex x c) (j.1 + 1) := by
      have := congrArg Prod.snd hst
      simpa [hscan, capacity_path_state x c (j.1 + 1) (by omega)] using this.symm
    have hemit :=
      capacityScannerColumn_emits_capacityInitialWindow x c
        ⟨j.1, by have := PakSideScanner.sideScannerHeight x; omega⟩
    have hold' :
        (tableauAt F.1.tiling (eastIndex F.1.width_pos) j).1.old =
          capacityInitialWindow x c
            ⟨j.1, by have := PakSideScanner.sideScannerHeight x; omega⟩ := by
      rw [hold, hs, ht]
      exact hemit
    have htape :
        east.oldTape z =
          OneTapeTableau.cellLetter
            (capacityInitialTableauCell x c z) := by
      have hat := TableauColumnStepReadback.oldTape_at east
        (⟨z.toNat, by omega⟩ : Fin (ConcretePakSide.sideValue x))
      have hjz : (⟨z.toNat, by omega⟩ : Fin (ConcretePakSide.sideValue x)) = j := rfl
      rw [hjz] at hat
      have hzj' : (j.1 : Int) = z := hzj
      rw [← hzj']
      rw [hat, FullFrame.tableau_column_readback_oldStrip, hold']
      unfold capacityInitialWindow
      rfl
    have hcfg : (firstConfig x F).tape z = east.oldTape z := by
      rw [hbefore]
      rfl
    rw [hcfg, htape, cellLetter_capacityInitialTableau]
    rfl
  · have hz' : z < 0 ∨ (ConcretePakSide.sideValue x : Int) ≤ z := by
      push Not at hz; omega
    have hU : (firstConfig x F).tape z = MStarOuterProgram.Tape.hash := by
      have hh := U.hash_outside ⟨0, Nat.zero_lt_succ _⟩ z
      have horigin : U.origin = 0 := rfl
      rw [horigin] at hh
      exact hh (by simpa using hz')
    have hC : (capacityEncodedStartConfig x c).tape z = MStarOuterProgram.Tape.hash := by
      apply capacityInitialTape_hash_outside x c z
      have hheight := PakSideScanner.sideScannerHeight x
      cases hz' with
      | inl h => exact Or.inl h
      | inr h =>
          right
          have : ((PakSideScanner.sideScannerBits x).length + 2 : Int) =
              (ConcretePakSide.sideValue x : Int) := by
            exact_mod_cast hheight
          simpa [this] using h
    exact hU.trans hC.symm

theorem firstArrow_eq (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : Frames x)
    (hscan : FullFrame.toScannerPath F.1 = capacityScannerPath x c) :
    firstArrow x F = PakEncodedStart.startOneArrow := by
  have hcfg := firstConfig_eq x c F hscan
  have hF := slotOne_first_step F
  have hC := capacityEncodedStart_slotOne_step x c
  have hslotF : (firstArrow x F).1.2 = 1 := F.2
  have hslotC : PakEncodedStart.startOneArrow.1.2 = 1 := rfl
  have hF' :
      step MStarULogAssembly.program MStarOuterProgram.movable
        (capacityEncodedStartConfig x c) (firstArrow x F) =
          some (timeOneConfig x F) := by
    rw [← hcfg]
    exact hF
  exact arrow_eq_of_successful_steps_same_slot
    (capacityEncodedStartConfig x c) (timeOneConfig x F)
    (capacityEncodedParserConfig x c) (firstArrow x F)
    PakEncodedStart.startOneArrow hF' hC (hslotF.trans hslotC.symm)

theorem timeOneConfig_eq (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : Frames x)
    (hscan : FullFrame.toScannerPath F.1 = capacityScannerPath x c) :
    timeOneConfig x F = capacityEncodedParserConfig x c := by
  have hcfg := firstConfig_eq x c F hscan
  have harrow := firstArrow_eq x c F hscan
  have hF := slotOne_first_step F
  have hC := capacityEncodedStart_slotOne_step x c
  have hF' :
      step MStarULogAssembly.program MStarOuterProgram.movable
        (capacityEncodedStartConfig x c) PakEncodedStart.startOneArrow =
          some (timeOneConfig x F) := by
    rw [← hcfg, ← harrow]
    exact hF
  exact step_label_deterministic MStarULogAssembly.program
    MStarOuterProgram.movable (capacityEncodedStartConfig x c)
    (timeOneConfig x F) (capacityEncodedParserConfig x c)
    PakEncodedStart.startOneArrow hF' hC

theorem fibre_scanner_eq (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    FullFrame.toScannerPath F.1.1 = capacityScannerPath x c := by
  have h := frame_capacity_spec x F.1
  simpa [F.2] using h

theorem fibre_firstConfig (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    firstConfig x F.1 = capacityEncodedStartConfig x c :=
  firstConfig_eq x c F.1 (fibre_scanner_eq x c F)

theorem fibre_firstArrow (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    firstArrow x F.1 = PakEncodedStart.startOneArrow :=
  firstArrow_eq x c F.1 (fibre_scanner_eq x c F)

theorem fibre_timeOneConfig (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (F : CapacityFibre x c) :
    timeOneConfig x F.1 = capacityEncodedParserConfig x c :=
  timeOneConfig_eq x c F.1 (fibre_scanner_eq x c F)

def all_frame_capacity_initial_spec : Prop :=
  (∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x) (F : Frames x),
    FullFrame.toScannerPath F.1 = capacityScannerPath x c →
      firstConfig x F = capacityEncodedStartConfig x c ∧
        firstArrow x F = PakEncodedStart.startOneArrow ∧
          timeOneConfig x F = capacityEncodedParserConfig x c) ∧
  (∀ (x : ConcretePakSide.Word) (c : ScannerCapacity x)
      (F : CapacityFibre x c),
    firstConfig x F.1 = capacityEncodedStartConfig x c ∧
      firstArrow x F.1 = PakEncodedStart.startOneArrow ∧
        timeOneConfig x F.1 = capacityEncodedParserConfig x c)

theorem all_frame_capacity_initial_spec_holds :
    all_frame_capacity_initial_spec :=
  ⟨fun x c F hscan =>
      ⟨firstConfig_eq x c F hscan, firstArrow_eq x c F hscan,
        timeOneConfig_eq x c F hscan⟩,
    fun x c F =>
      ⟨fibre_firstConfig x c F, fibre_firstArrow x c F,
        fibre_timeOneConfig x c F⟩⟩

end PakFixedPolyomino.PakAllFrameCapacityInitialReadback
