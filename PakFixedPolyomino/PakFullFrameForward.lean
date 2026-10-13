import PakFixedPolyomino.PakParserOuterBridge

/-!
# The forward square full frame for a concrete Pak side

The scanner fixes the east-facing initial tableau strip.  A padded accepting
run with that literal first window then supplies the remaining tableau track;
the canonical amplifier and ripple tracks close it to a square full frame.
-/

namespace PakFixedPolyomino.PakFullFrameForward

open FiniteOneTapeSemantics
open PakMStarCouplingCorrectness

abbrev sideSquareSize (x : ConcretePakSide.Word) : ℕ :=
  (PakSideScanner.sideScannerBits x).length + 2

theorem sideSquareSize_pos (x : ConcretePakSide.Word) : 0 < sideSquareSize x := by
  have h := PakSideScanner.sideScannerBits_pos x
  dsimp [sideSquareSize]
  omega

theorem sideSquareSize_ge_three (x : ConcretePakSide.Word) : 3 ≤ sideSquareSize x := by
  have h := PakSideScanner.sideScannerBits_pos x
  dsimp [sideSquareSize]
  omega

/-- A square, hash-padded accepting run whose chronological first step is the
literal slot-one start step emitted by the terminal scanner. -/
structure SideSquarePaddedRun (x : ConcretePakSide.Word) where
  padded : PaddedUniformWindowedMStarRun (sideSquareSize x) (sideSquareSize x)
  initial_step : padded.run.stepWindow ⟨0, sideSquareSize_pos x⟩ =
    PakSideScannerRow.sideStartWindowedStep x

def sideSquareScannerTiling (x : ConcretePakSide.Word) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State))
      (sideSquareSize x) (sideSquareSize x) :=
  PakScannerTerminal.terminalScannerTiling (sideSquareSize x)
    (sideSquareSize_pos x) (PakSideScanner.sideScannerBits x)
    (PakSideScanner.sideScannerBits_pos x)
    (PakSideScanner.scannerTerminalIndex x)
    (PakSideScanner.scannerTerminalIndex_pos x)
    (PakSideScanner.scannerTerminalIndex_lt x)

def sideSquareEastIndex (x : ConcretePakSide.Word) : Fin (sideSquareSize x) :=
  ⟨sideSquareSize x - 1, by
    have h := sideSquareSize_pos x
    omega⟩

theorem sideSquare_revTime_east (x : ConcretePakSide.Word) :
    UniformWindowedMStarRun.revTime (sideSquareEastIndex x) =
      ⟨0, sideSquareSize_pos x⟩ := by
  apply Fin.ext
  simp [sideSquareEastIndex, UniformWindowedMStarRun.revTime]

theorem sideSquare_tableau_east_old (x : ConcretePakSide.Word)
    (R : SideSquarePaddedRun x) (j : Fin (sideSquareSize x)) :
    (R.padded.run.tableauTiling.1 (sideSquareEastIndex x) j).1.old =
      (PakSideScannerRow.sideStartWindowedStep x).oldStrip j := by
  rw [UniformWindowedMStarRun.tableauTiling_cell_old,
    sideSquare_revTime_east, R.initial_step]

theorem sideSquare_scanner_east (x : ConcretePakSide.Word)
    (j : Fin (sideSquareSize x)) :
    (sideSquareScannerTiling x).1 (sideSquareEastIndex x) j =
      some
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) j.1,
        PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) (j.1 + 1)) := by
  simp [sideSquareScannerTiling, PakScannerTerminal.terminalScannerTiling,
    PakCanonicalScanner.eastColumnTiling, PakCanonicalScanner.eastColumnCell,
    PakScannerTerminal.terminalScannerColumn, sideSquareEastIndex]

theorem sideSquare_scanner_emits_tableau_old (x : ConcretePakSide.Word)
    (R : SideSquarePaddedRun x) (j : Fin (sideSquareSize x)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) j.1)
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) (j.1 + 1)) =
      (R.padded.run.tableauTiling.1 (sideSquareEastIndex x) j).1.old := by
  rw [sideSquare_tableau_east_old]
  exact PakSideScannerRow.sideScanner_emits_startOldStrip x j

/-- The terminal column satisfies the scanner part of an east coupling at
each of its three geometric phases.  Keeping the endpoint cases explicit is
important: the bottom and top states are not ordinary `mid` states. -/
theorem terminalScannerColumn_activityCoupledStep
    (bits : List Bool) (hbits : 0 < bits.length) (terminal : ℕ)
    (hterminal : 0 < terminal) (hbound : terminal < bits.length)
    (topBit : Bool) (j : Fin (bits.length + 2)) :
    ConcretePakScanner.ActivityCoupledStep
      (decide (j.1 = 0)) (decide (j.1 = bits.length + 1))
      (PakScannerTerminal.terminalScannerColumn bits hbits terminal j)
      (if j.1 < terminal then
          PakScannerPath.scannerBit bits false topBit j
       else if j.1 = terminal then false
       else if j.1 < bits.length then false
       else if j.1 = bits.length then false else topBit) := by
  rcases PakScannerTerminal.terminalScannerColumn_legal bits hbits terminal
      hterminal hbound topBit j with ⟨s, t, hcolumn, hlegal⟩
  have hpair :
      (PakScannerTerminal.terminalScannerState bits hbits terminal j.1,
        PakScannerTerminal.terminalScannerState bits hbits terminal (j.1 + 1)) =
        (s, t) := by
    exact Option.some.inj (by
      simpa [PakScannerTerminal.terminalScannerColumn] using hcolumn)
  have hs : PakScannerTerminal.terminalScannerState bits hbits terminal j.1 = s :=
    congrArg Prod.fst hpair
  have ht : PakScannerTerminal.terminalScannerState bits hbits terminal (j.1 + 1) = t :=
    congrArg Prod.snd hpair
  subst s
  subst t
  refine ⟨_, _, by simpa [PakScannerTerminal.terminalScannerColumn] using hcolumn,
    hlegal, ?_, ?_⟩
  · by_cases hbottom : j.1 = 0
    · simp [hbottom, PakScannerTerminal.terminalScannerState,
        PakCouplingGenerated.scannerBottom, ConcretePakScanner.PhaseCoupled]
    · by_cases htop : j.1 = bits.length + 1
      · have hnotzero : bits.length + 1 ≠ 0 := by omega
        have hnotmid : ¬ bits.length + 1 ≤ terminal := by omega
        have hnotlen : ¬ bits.length + 1 ≤ bits.length := by omega
        simp [htop, hbottom, hnotzero, hnotmid, hnotlen,
          PakScannerTerminal.terminalScannerState,
          PakScannerTerminal.terminalTopState,
          ConcretePakScanner.PhaseCoupled]
      · have hjle : j.1 ≤ bits.length := by omega
        by_cases hmid : j.1 ≤ terminal
        · simp [hbottom, htop, hmid,
            PakScannerTerminal.terminalScannerState,
            PakScannerPath.midState, ConcretePakScanner.PhaseCoupled]
        · simp [hbottom, htop, hmid, hjle,
            PakScannerTerminal.terminalScannerState,
            PakScannerTerminal.terminalTailState,
            ConcretePakScanner.PhaseCoupled]
  · by_cases hbottom : j.1 = 0
    · simp [hbottom, PakScannerTerminal.terminalScannerState,
        PakCouplingGenerated.scannerBottom, ConcretePakScanner.LookaheadCoupled]
    · by_cases htop : j.1 = bits.length + 1
      · have hnotzero : bits.length + 1 ≠ 0 := by omega
        have hnotmid : ¬ bits.length + 1 ≤ terminal := by omega
        have hnotlen : ¬ bits.length + 1 ≤ bits.length := by omega
        simp [htop, hbottom, hnotzero, hnotmid, hnotlen,
          PakScannerTerminal.terminalScannerState,
          PakScannerTerminal.terminalTopState,
          ConcretePakScanner.LookaheadCoupled]
      · have hjle : j.1 ≤ bits.length := by omega
        by_cases hmid : j.1 ≤ terminal
        · simp [hbottom, htop, hmid,
            PakScannerTerminal.terminalScannerState,
            PakScannerPath.midState, ConcretePakScanner.LookaheadCoupled]
        · simp [hbottom, htop, hmid, hjle,
            PakScannerTerminal.terminalScannerState,
            PakScannerTerminal.terminalTailState,
            ConcretePakScanner.LookaheadCoupled]

/-- The padded left endpoint gives the complete literal south sentinel at
every tableau time. -/
theorem padded_tableau_south_sentinel {width n : ℕ}
    (P : PaddedUniformWindowedMStarRun width n) (i : Fin n) :
    PakCouplingGenerated.southSentinel MStarULogAssembly.boundaryData Fixed.Machine
      (P.run.tableauTiling.1 i
        ⟨0, Nat.lt_of_lt_of_le (by decide) P.run.width_ge_three⟩) := by
  let j : Fin width := ⟨0, Nat.lt_of_lt_of_le (by decide) P.run.width_ge_three⟩
  let t : Fin n := UniformWindowedMStarRun.revTime i
  let tn : Fin (n + 1) := ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  let tn' : Fin (n + 1) := ⟨t.1 + 1, by omega⟩
  have hleft_old := P.left_endpoint_hash tn
  have hleft_new := P.left_endpoint_hash tn'
  have hout_old := P.run.hash_outside tn (P.run.origin - 1) (Or.inl (by omega))
  have hout_new := P.run.hash_outside tn' (P.run.origin - 1) (Or.inl (by omega))
  have hhead_old : P.run.origin ≠ (P.run.config tn).head := by
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_left tn
    omega
  have hhead_old_minus : P.run.origin - 1 ≠ (P.run.config tn).head := by
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_left tn
    omega
  have hhead_new : P.run.origin ≠ (P.run.config tn').head := by
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_left tn'
    omega
  have hhead_new_minus : P.run.origin - 1 ≠ (P.run.config tn').head := by
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_left tn'
    omega
  have hold_minus :
      ((P.run.stepWindow t).oldStrip j).minus =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.oldStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn,
      hhead_old_minus, hout_old, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hold_center :
      ((P.run.stepWindow t).oldStrip j).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.oldStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn,
      hhead_old, hleft_old, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hnew_minus :
      ((P.run.stepWindow t).newStrip j).minus =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.newStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn',
      hhead_new_minus, hout_new, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hnew_center :
      ((P.run.stepWindow t).newStrip j).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.newStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn',
      hhead_new, hleft_new, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hbits_old := (P.run.tileAt_bits t j).1
  have hbits_new := (P.run.tileAt_bits t j).2.2.1
  have hminus_old : P.run.oldMinusBit t j = false := by
    unfold UniformWindowedMStarRun.oldMinusBit UniformWindowedMStarRun.orderBit
    simp [UniformWindowedMStarRun.stepWindow, WindowedMStarStep.position, j, t, tn]
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_left tn
    omega
  have hminus_new : P.run.newMinusBit t j = false := by
    unfold UniformWindowedMStarRun.newMinusBit UniformWindowedMStarRun.orderBit
    simp [UniformWindowedMStarRun.stepWindow, WindowedMStarStep.position, j, t, tn']
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_left tn'
    omega
  have htoken := P.run.tileAt_southToken t j
  have hjright : j ≠ (P.run.stepWindow t).headRightIndex := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [j, WindowedMStarStep.headRightIndex] at hval
    have hpos := P.run.head_interior_left tn
    omega
  unfold PakCouplingGenerated.southSentinel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [UniformWindowedMStarRun.tableauTiling_cell_old]
    simpa [j, t] using hold_minus
  · rw [UniformWindowedMStarRun.tableauTiling_cell_old]
    simpa [j, t] using hold_center
  · rw [UniformWindowedMStarRun.tableauTiling_cell_new]
    simpa [j, t] using hnew_minus
  · rw [UniformWindowedMStarRun.tableauTiling_cell_new]
    simpa [j, t] using hnew_center
  · change (P.run.tileAt t j).1.oldMinusBit = false
    rw [hbits_old, hminus_old]
  · change (P.run.tileAt t j).1.newMinusBit = false
    rw [hbits_new, hminus_new]
  · change (P.run.tileAt t j).1.southToken = none
    rw [htoken, if_neg hjright]

/-- The padded right endpoint gives the complete literal north sentinel at
every tableau time. -/
theorem padded_tableau_north_sentinel {width n : ℕ}
    (P : PaddedUniformWindowedMStarRun width n) (i : Fin n) :
    PakCouplingGenerated.northSentinel MStarULogAssembly.boundaryData Fixed.Machine
      (P.run.tableauTiling.1 i
        ⟨width - 1, by have h := P.run.width_ge_three; omega⟩) := by
  let j : Fin width := ⟨width - 1, by have h := P.run.width_ge_three; omega⟩
  let t : Fin n := UniformWindowedMStarRun.revTime i
  let tn : Fin (n + 1) := ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  let tn' : Fin (n + 1) := ⟨t.1 + 1, by omega⟩
  have hright_old := P.right_endpoint_hash tn
  have hright_new := P.right_endpoint_hash tn'
  have hout_old := P.run.hash_outside tn (P.run.origin + width) (Or.inr (by omega))
  have hout_new := P.run.hash_outside tn' (P.run.origin + width) (Or.inr (by omega))
  have hlast : width - 1 + 1 = width := by
    have h := P.run.width_ge_three
    omega
  have hright_pos : P.run.origin + ((width - 1 : ℕ) : Int) + 1 =
      P.run.origin + width := by
    push_cast
    omega
  have hhead_old : P.run.origin + (width - 1 : ℕ) ≠ (P.run.config tn).head := by
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_right tn
    omega
  have hhead_old_plus : P.run.origin + width ≠ (P.run.config tn).head := by
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_right tn
    omega
  have hhead_new : P.run.origin + (width - 1 : ℕ) ≠ (P.run.config tn').head := by
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_right tn'
    omega
  have hhead_new_plus : P.run.origin + width ≠ (P.run.config tn').head := by
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_right tn'
    omega
  have hold_center :
      ((P.run.stepWindow t).oldStrip j).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.oldStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn,
      hhead_old, hright_old, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hold_plus :
      ((P.run.stepWindow t).oldStrip j).plus =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.oldStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn,
      hlast, hright_pos, hhead_old_plus, hout_old, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hnew_center :
      ((P.run.stepWindow t).newStrip j).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.newStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn',
      hhead_new, hright_new, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hnew_plus :
      ((P.run.stepWindow t).newStrip j).plus =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
    simp [WindowedMStarStep.newStrip, WindowedMStarStep.triple,
      WindowedMStarStep.cell, WindowedMStarStep.position,
      UniformWindowedMStarRun.stepWindow, j, t, tn',
      hlast, hright_pos, hhead_new_plus, hout_new, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  have hbits_old := (P.run.tileAt_bits t j).2.1
  have hbits_new := (P.run.tileAt_bits t j).2.2.2
  have hplus_old : P.run.oldPlusBit t j = true := by
    unfold UniformWindowedMStarRun.oldPlusBit UniformWindowedMStarRun.orderBit
    simp [UniformWindowedMStarRun.stepWindow, WindowedMStarStep.position, j, t, tn]
    rw [P.run.head_eq tn]
    have h := P.run.head_interior_right tn
    omega
  have hplus_new : P.run.newPlusBit t j = true := by
    unfold UniformWindowedMStarRun.newPlusBit UniformWindowedMStarRun.orderBit
    simp [UniformWindowedMStarRun.stepWindow, WindowedMStarStep.position, j, t, tn']
    rw [P.run.head_eq tn']
    have h := P.run.head_interior_right tn'
    omega
  have htoken := P.run.tileAt_northToken t j
  have hjhead : j ≠ (P.run.stepWindow t).head_index := by
    intro h
    have hval := congrArg Fin.val h
    change width - 1 = (P.run.head_index tn).1 at hval
    have hpos := P.run.head_interior_right tn
    omega
  unfold PakCouplingGenerated.northSentinel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [UniformWindowedMStarRun.tableauTiling_cell_old]
    simpa [j, t] using hold_center
  · rw [UniformWindowedMStarRun.tableauTiling_cell_old]
    simpa [j, t] using hold_plus
  · rw [UniformWindowedMStarRun.tableauTiling_cell_new]
    simpa [j, t] using hnew_center
  · rw [UniformWindowedMStarRun.tableauTiling_cell_new]
    simpa [j, t] using hnew_plus
  · change (P.run.tileAt t j).1.oldPlusBit = true
    rw [hbits_old, hplus_old]
  · change (P.run.tileAt t j).1.newPlusBit = true
    rw [hbits_new, hplus_new]
  · change (P.run.tileAt t j).1.northToken = none
    rw [htoken, if_neg hjhead]

namespace WindowedMStarStep

theorem acceptingWindow_newStrip_of_after_accept {width : ℕ}
    (S : WindowedMStarStep width)
    (hstate : S.after.state = MStarOuterProgram.State.accept)
    (j : Fin width) :
    PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
      (S.newStrip j) := by
  have hcell (z : Int) :
      PakCouplingGenerated.cellAccepting MStarULogAssembly.boundaryData
        (S.cell S.after z) := by
    unfold PakCouplingGenerated.cellAccepting WindowedMStarStep.cell
    by_cases hz : z = S.after.head
    · simp [hz, hstate, MStarULogAssembly.boundaryData,
        MStarOuterProgram.boundaryData]
    · simp [hz]
  exact ⟨by simpa [WindowedMStarStep.newStrip,
      WindowedMStarStep.triple] using hcell (S.position j - 1),
    by simpa [WindowedMStarStep.newStrip,
      WindowedMStarStep.triple] using hcell (S.position j),
    by simpa [WindowedMStarStep.newStrip,
      WindowedMStarStep.triple] using hcell (S.position j + 1)⟩

end WindowedMStarStep

theorem SideSquarePaddedRun.tableau_west_new_accepting
    {x : ConcretePakSide.Word} (R : SideSquarePaddedRun x)
    (j : Fin (sideSquareSize x)) :
    PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
      (R.padded.run.tableauTiling.1 ⟨0, sideSquareSize_pos x⟩ j).1.new := by
  rw [UniformWindowedMStarRun.tableauTiling_cell_new]
  apply WindowedMStarStep.acceptingWindow_newStrip_of_after_accept
  simpa [UniformWindowedMStarRun.stepWindow,
    UniformWindowedMStarRun.revTime] using R.padded.run.final_accept

noncomputable def sideSquareFullTrackCertificate (x : ConcretePakSide.Word)
    (R : SideSquarePaddedRun x) : FullTrackRunCertificate R.padded where
  time_pos := sideSquareSize_pos x
  amplifier := PakRippleCanonical.canonicalFullAmpTiling Fixed.Q
    (sideSquareSize x) (sideSquareSize x)
  ripple := PakRippleCanonical.canonicalTiling (sideSquareSize x) (sideSquareSize x)
  scanner := sideSquareScannerTiling x
  coupled := by
    intro i j
    change ConcreteWProd.FiveCouplingTable.accepts Fixed.Machine Fixed.Q
      (MStarULogAssembly.fiveCouplings Fixed.Q) _
    apply (PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q _).mpr
    have hfinal := R.padded.run.final_accept
    have hleft := R.padded.left_endpoint_hash
    have hright := R.padded.right_endpoint_hash
    have heast_scan := sideSquare_scanner_east x j
    have heast_old := sideSquare_scanner_emits_tableau_old x R j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hwest
      have hi : i.1 = 0 := by
        simpa [PakCouplingGenerated.amp,
          PakRippleCanonical.canonicalFullAmpTiling,
          PakRippleCanonical.canonicalFullAmpCell] using hwest
      have hi0 : i = ⟨0, sideSquareSize_pos x⟩ := Fin.ext hi
      subst i
      refine ⟨PakRippleCanonical.canonicalTiling_west
        (sideSquareSize x) (sideSquareSize x) j (sideSquareSize_pos x),
        R.tableau_west_new_accepting j, ?_⟩
      have hbits := PakSideScanner.sideScannerBits_pos x
      simp [PakCouplingGenerated.scan, sideSquareScannerTiling, PakScannerTerminal.terminalScannerTiling,
        PakCanonicalScanner.eastColumnTiling,
        PakCanonicalScanner.eastColumnCell, hbits.ne']
    · intro heast
      have hi : i = sideSquareEastIndex x := by
        apply Fin.ext
        change decide (i.1 + 1 = sideSquareSize x) = true at heast
        have hival : i.1 + 1 = sideSquareSize x := decide_eq_true_eq.mp heast
        have hival' : i.1 = (PakSideScanner.sideScannerBits x).length + 1 := by
          dsimp [sideSquareSize] at hival
          omega
        change i.1 = (sideSquareEastIndex x).1
        dsimp [sideSquareEastIndex, sideSquareSize]
        exact hival'
      subst i
      have hripple :
          xor ((PakRippleCanonical.canonicalTiling (sideSquareSize x)
            (sideSquareSize x)).1 (sideSquareEastIndex x) j).1
            ((PakRippleCanonical.canonicalTiling (sideSquareSize x)
              (sideSquareSize x)).1 (sideSquareEastIndex x) j).2 =
            (sideSquareSize x).testBit j.1 := by
        simpa [sideSquareEastIndex, rippleTile] using
          PakRippleCanonical.canonicalTiling_east (sideSquareSize x)
            (sideSquareSize x) (sideSquareSize_pos x) j
      refine ⟨?_, ?_⟩
      · have hactivity := terminalScannerColumn_activityCoupledStep
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x)
            (PakSideScanner.scannerTerminalIndex_pos x)
            (PakSideScanner.scannerTerminalIndex_lt x) false j
        rw [PakSideScanner.sideScannerTerminalBit_eq_testBit x j] at hactivity
        have hripple' :
            xor ((PakRippleCanonical.canonicalTiling (sideSquareSize x)
              (sideSquareSize x)).1 (sideSquareEastIndex x) j).1
              ((PakRippleCanonical.canonicalTiling (sideSquareSize x)
                (sideSquareSize x)).1 (sideSquareEastIndex x) j).2 =
              (ConcretePakSide.sideValue x).testBit j.1 := by
          simpa [sideSquareSize, PakSideScanner.sideScannerHeight] using hripple
        rw [← hripple'] at hactivity
        simpa [PakCouplingGenerated.amp, PakCouplingGenerated.ripple,
          PakCouplingGenerated.scan, PakRippleCanonical.canonicalFullAmpTiling,
          PakRippleCanonical.canonicalFullAmpCell, sideSquareScannerTiling,
          PakScannerTerminal.terminalScannerTiling,
          PakCanonicalScanner.eastColumnTiling,
          PakCanonicalScanner.eastColumnCell, sideSquareEastIndex,
          sideSquareSize] using hactivity
      · refine ⟨PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) j.1,
            PakScannerTerminal.terminalScannerState
              (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
              (PakSideScanner.scannerTerminalIndex x) (j.1 + 1),
            sideSquare_scanner_east x j, ?_⟩
        apply (PakCouplingGenerated.emittedMatches_iff_eq
          MStarULogAssembly.boundaryData _ _ _).mpr
        exact heast_old.symm
    · intro hsouth
      have hj : j = ⟨0, sideSquareSize_pos x⟩ := by
        apply Fin.ext
        change decide (j.1 = 0) = true at hsouth
        exact decide_eq_true_eq.mp hsouth
      subst j
      refine ⟨PakRippleCanonical.canonicalTiling_south
          (sideSquareSize x) (sideSquareSize x) i (sideSquareSize_pos x),
        padded_tableau_south_sentinel R.padded i, ?_⟩
      intro heast'
      have hi : i = sideSquareEastIndex x := by
        apply Fin.ext
        change decide (i.1 + 1 = sideSquareSize x) = true at heast'
        have hival : i.1 + 1 = sideSquareSize x := decide_eq_true_eq.mp heast'
        have hival' : i.1 = (PakSideScanner.sideScannerBits x).length + 1 := by
          dsimp [sideSquareSize] at hival
          omega
        change i.1 = (sideSquareEastIndex x).1
        dsimp [sideSquareEastIndex, sideSquareSize]
        exact hival'
      subst i
      refine ⟨PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) 1, ?_⟩
      change (sideSquareScannerTiling x).1 (sideSquareEastIndex x)
          ⟨0, sideSquareSize_pos x⟩ =
        some (PakCouplingGenerated.scannerBottom,
          PakScannerTerminal.terminalScannerState (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) 1)
      simpa [PakScannerTerminal.terminalScannerState,
        PakCouplingGenerated.scannerBottom] using
        sideSquare_scanner_east x ⟨0, sideSquareSize_pos x⟩
    · intro hnorth
      have hj : j.1 = (PakSideScanner.sideScannerBits x).length + 1 := by
        change decide (j.1 + 1 = sideSquareSize x) = true at hnorth
        have htop : j.1 + 1 = sideSquareSize x := decide_eq_true_eq.mp hnorth
        dsimp [sideSquareSize] at htop
        omega
      let top : Fin (sideSquareSize x) :=
        ⟨(PakSideScanner.sideScannerBits x).length + 1,
          by dsimp [sideSquareSize]; omega⟩
      have hjTop : j = top := Fin.eq_of_val_eq hj
      have hsent : PakCouplingGenerated.northSentinel
          MStarULogAssembly.boundaryData Fixed.Machine (R.padded.run.tableauTiling.1 i j) := by
        rw [hjTop]
        simpa [top, sideSquareSize] using padded_tableau_north_sentinel R.padded i
      refine ⟨?_, hsent, ?_⟩
      · simp only [PakCouplingGenerated.ripple]
        have hpow : i.1 <
            2 ^ ((PakSideScanner.sideScannerBits x).length + 1) := by
          have hi := i.2
          dsimp [sideSquareSize] at hi
          have hk : (PakSideScanner.sideScannerBits x).length + 1 <
              2 ^ ((PakSideScanner.sideScannerBits x).length + 1) :=
            Nat.lt_two_pow_self
          omega
        have htest : i.1.testBit
            ((PakSideScanner.sideScannerBits x).length + 1) = false :=
          Nat.testBit_eq_false_of_lt hpow
        change (((PakRippleCanonical.canonicalTiling (sideSquareSize x)
            (sideSquareSize x)).1 i j).1 &&
            ((PakRippleCanonical.canonicalTiling (sideSquareSize x)
              (sideSquareSize x)).1 i j).2) = false
        simp [Bool.and_eq_false_iff, PakRippleCanonical.canonicalTiling,
          PakRippleCanonical.canonicalCell, PakRippleCanonical.rippleBit,
          PakRippleCanonical.rippleCarry, hj, sideSquareSize, htest]
      · intro heast'
        have hi : i = sideSquareEastIndex x := by
          apply Fin.ext
          change decide (i.1 + 1 = sideSquareSize x) = true at heast'
          have hival : i.1 + 1 = sideSquareSize x := decide_eq_true_eq.mp heast'
          have hival' : i.1 = (PakSideScanner.sideScannerBits x).length + 1 := by
            dsimp [sideSquareSize] at hival
            omega
          change i.1 = (sideSquareEastIndex x).1
          dsimp [sideSquareEastIndex, sideSquareSize]
          exact hival'
        subst i
        have hnot : ¬ (PakSideScanner.sideScannerBits x).length + 1 <
            PakSideScanner.scannerTerminalIndex x := by
          have hlt := PakSideScanner.scannerTerminalIndex_lt x
          omega
        have hnotTop : ¬ (PakSideScanner.sideScannerBits x).length <
            PakSideScanner.scannerTerminalIndex x := by
          have hlt := PakSideScanner.scannerTerminalIndex_lt x
          omega
        refine ⟨PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x)
              ((PakSideScanner.sideScannerBits x).length + 1),
            ConcretePakScanner.topNorth, ?_, ?_⟩
        · change (sideSquareScannerTiling x).1 (sideSquareEastIndex x) j =
              some (PakScannerTerminal.terminalScannerState
                (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
                (PakSideScanner.scannerTerminalIndex x)
                ((PakSideScanner.sideScannerBits x).length + 1),
                ConcretePakScanner.topNorth)
          rw [hjTop]
          convert sideSquare_scanner_east x top using 1 <;>
            simp [top, PakScannerTerminal.terminalScannerState,
              PakScannerTerminal.terminalTopState,
              PakSideScanner.scannerTerminalIndex_lt x, hnot]
        · simp [top, PakScannerTerminal.terminalScannerState,
            PakScannerTerminal.terminalTopState,
            PakSideScanner.scannerTerminalIndex_lt x,
            PakCouplingGenerated.scannerTopSouth, hnot, hnotTop]
    · intro hnonEast
      simp_all [PakRippleCanonical.canonicalFullAmpTiling,
        PakRippleCanonical.canonicalFullAmpCell, sideSquareScannerTiling,
        PakScannerTerminal.terminalScannerTiling,
        PakCanonicalScanner.eastColumnTiling,
        PakCanonicalScanner.eastColumnCell,
        PakScannerTerminal.terminalScannerColumn,
        PakCouplingGenerated.amp, PakCouplingGenerated.ripple,
        PakCouplingGenerated.tableau, PakCouplingGenerated.scan]
  west_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_west Fixed.Q
      (sideSquareSize x) (sideSquareSize x) (sideSquareSize_pos x) j
  east_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_east Fixed.Q
      (sideSquareSize x) (sideSquareSize x) (sideSquareSize_pos x) j
  south_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_south Fixed.Q
      (sideSquareSize x) (sideSquareSize x) i (by
        have h := sideSquareSize_ge_three x
        omega)
  north_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_north Fixed.Q
      (sideSquareSize x) (sideSquareSize x) i (by
        have h := sideSquareSize_ge_three x
        omega)

/-- The literal square frame determined by a padded side run. -/
noncomputable def sideSquareFullFrame (x : ConcretePakSide.Word)
    (R : SideSquarePaddedRun x) : FullFrame (sideSquareSize x) (sideSquareSize x) :=
  (sideSquareFullTrackCertificate x R).toFullFrame

end PakFixedPolyomino.PakFullFrameForward
