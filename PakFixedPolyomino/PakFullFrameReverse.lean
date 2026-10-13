import PakFixedPolyomino.PakSideScannerRow
import Mathlib.Tactic

/-!
# Boundary facts for full-frame readback

The local scanner relation is deliberately nondeterministic. This file
extracts the global east-column path and its parser/copier-row consequence.
-/

namespace PakFixedPolyomino.PakMStarCouplingCorrectness

open ConcretePakSide

/-- Reindex a side-square row as a row of its scanner column. -/
def sideScannerIndex (x : Word) (j : Fin (sideValue x)) :
    Fin ((PakSideScanner.sideScannerBits x).length + 2) :=
  Fin.cast (PakSideScanner.sideScannerHeight x).symm j

@[simp] theorem sideScannerIndex_val (x : Word) (j : Fin (sideValue x)) :
    (sideScannerIndex x j).1 = j.1 := rfl

/-- The east coupling supplies a marked legal scanner edge with the literal
ripple east colour as its label. -/
theorem FullFrame.east_scanner_legal {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) :
    ∃ s t : ConcretePakScanner.State,
      scannerAt F.tiling (eastIndex F.width_pos) j = some (s, t) ∧
        ConcretePakScanner.LegalScan s t
          (rippleTile (rippleAt F.tiling (eastIndex F.width_pos) j)).east := by
  have heast := F.boundary.2.1 j
  have hlocal := ((coupledAt_iff F.tiling (eastIndex F.width_pos) j).2.1 heast).1
  change ConcretePakScanner.ActivityCoupledStep
    (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive
    (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive
    (scannerAt F.tiling (eastIndex F.width_pos) j)
    (xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
      (rippleAt F.tiling (eastIndex F.width_pos) j).2) at hlocal
  rcases hlocal with ⟨s, t, hscan, hlegal, _⟩
  exact ⟨s, t, hscan, by simpa [rippleTile] using hlegal⟩

/-- Adjacent marked east cells share their scanner state through vertical Wang
matching. This is the global path condition, not a local uniqueness premise. -/
theorem FullFrame.east_scanner_successor {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) (hj : j.1 + 1 < h)
    {s t s' t' : ConcretePakScanner.State}
    (hscan : scannerAt F.tiling (eastIndex F.width_pos) j = some (s, t))
    (hnext : scannerAt F.tiling (eastIndex F.width_pos) ⟨j.1 + 1, hj⟩ =
      some (s', t')) :
    t = s' := by
  have hmatch := (scannerProjection F.tiling).2.2
    (eastIndex F.width_pos) j hj
  change (scannerTile (scannerAt F.tiling (eastIndex F.width_pos) j)).north =
    (scannerTile (scannerAt F.tiling (eastIndex F.width_pos)
      ⟨j.1 + 1, hj⟩)).south at hmatch
  simpa [scannerTile, hscan, hnext] using hmatch

/-- A marked scanner cell has only one pair of endpoint states. Together with
`east_scanner_successor`, this is the column induction interface. -/
theorem FullFrame.east_scanner_cell_unique {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) {s t s' t' : ConcretePakScanner.State}
    (hscan : scannerAt F.tiling (eastIndex F.width_pos) j = some (s, t))
    (hscan' : scannerAt F.tiling (eastIndex F.width_pos) j = some (s', t')) :
    s = s' ∧ t = t' := by
  have hpairs : (s, t) = (s', t') := Option.some.inj (hscan.symm.trans hscan')
  exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- Once a global column induction has identified the east scanner with the
terminal column, the east emission table recovers the marked parser/copier
start row itself (rather than merely an equivalent readout record). -/
theorem FullFrame.east_oldStrip_eq_sideInitialWindow (x : Word)
    (F : FullFrame (sideValue x) (sideValue x))
    (hterminal : ∀ j : Fin (sideValue x),
      scannerAt F.tiling (eastIndex F.width_pos) j =
        some
          (PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) (sideScannerIndex x j).1,
           PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) ((sideScannerIndex x j).1 + 1)))
    (j : Fin (sideValue x)) :
    (tableauAt F.tiling (eastIndex F.width_pos) j).1.old =
      PakSideScannerRow.sideInitialWindow x (sideScannerIndex x j) := by
  rcases F.east_emits_tableau_window j with ⟨s, t, hscan, hold⟩
  have hpairs : (s, t) =
      (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) (sideScannerIndex x j).1,
       PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) ((sideScannerIndex x j).1 + 1)) :=
    Option.some.inj (hscan.symm.trans (hterminal j))
  have hs : s = PakScannerTerminal.terminalScannerState
      (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
      (PakSideScanner.scannerTerminalIndex x) (sideScannerIndex x j).1 := by
    simpa using congrArg Prod.fst hpairs
  have ht : t = PakScannerTerminal.terminalScannerState
      (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
      (PakSideScanner.scannerTerminalIndex x) ((sideScannerIndex x j).1 + 1) := by
    simpa using congrArg Prod.snd hpairs
  rw [hs, ht] at hold
  calc
    (tableauAt F.tiling (eastIndex F.width_pos) j).1.old =
        PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
          (PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) (sideScannerIndex x j).1)
          (PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
            (PakSideScanner.scannerTerminalIndex x) ((sideScannerIndex x j).1 + 1)) := hold
    _ = PakSideScannerRow.sideInitialWindow x (sideScannerIndex x j) :=
      PakSideScannerRow.terminalScannerColumn_emits_sideInitialWindow x
        (sideScannerIndex x j)

end PakFixedPolyomino.PakMStarCouplingCorrectness
