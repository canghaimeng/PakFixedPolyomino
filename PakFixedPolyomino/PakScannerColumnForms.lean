import PakFixedPolyomino.PakFullFrameRippleClassify
import PakFixedPolyomino.PakScannerPath
import PakFixedPolyomino.PakScannerTerminal
import Mathlib.Tactic

/-!
# The two honest forms of an east scanner column

`LegalScan` is intentionally nondeterministic.  In particular, the terminal
edge is optional: a legal east column is not entitled to a terminal readback
until a separate tableau invariant has selected one.  This file records the
two canonical alternatives, and the exact extra hypothesis required to use
them for a full frame.
-/

namespace PakFixedPolyomino.PakScannerColumnForms

open PakMStarCouplingCorrectness
open ConcretePakScanner

/-- The `mid`/`preTop` path with no copier endpoint. -/
def NoTerminalColumn (bits : List Bool) (hbits : 0 < bits.length)
    (column : Fin (bits.length + 2) → ScannerTile State) : Prop :=
  column = PakScannerPath.scannerColumn bits hbits

/-- A path with one explicit terminal edge. -/
def TerminalColumn (bits : List Bool) (hbits : 0 < bits.length)
    (column : Fin (bits.length + 2) → ScannerTile State) : Prop :=
  ∃ terminal : ℕ, 0 < terminal ∧ terminal < bits.length ∧
    column = PakScannerTerminal.terminalScannerColumn bits hbits terminal

/-- The constructive sum of the only two canonical scanner path forms. -/
def ScannerColumnForm (bits : List Bool) (hbits : 0 < bits.length)
    (column : Fin (bits.length + 2) → ScannerTile State) : Prop :=
  NoTerminalColumn bits hbits column ∨ TerminalColumn bits hbits column

/-- Every admissible terminal index supplies the terminal summand. -/
theorem terminalScannerColumn_terminal (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal) (hbound : terminal < bits.length) :
    TerminalColumn bits hbits
      (PakScannerTerminal.terminalScannerColumn bits hbits terminal) :=
  ⟨terminal, hterminal, hbound, rfl⟩

/-- The ordinary path is a legal no-terminal column for its literal labels. -/
theorem scannerColumn_no_terminal_legal
    (bits : List Bool) (hbits : 0 < bits.length) (topBit : Bool)
    (j : Fin (bits.length + 2)) :
    ∃ s t : State,
      PakScannerPath.scannerColumn bits hbits j = some (s, t) ∧
        LegalScan s t (PakScannerPath.scannerBit bits false topBit j) :=
  PakFullFrameRippleClassify.scannerColumn_legal_without_terminal bits hbits topBit j

/-- `dataCell` is built only from ordinary data and hash/work buffers; it
never manufactures the explicit copier endpoint. -/
theorem dataCell_ne_rightEnd (bits : List Bool) (k : ℕ) :
    PakScannerPath.dataCell bits k ≠ .rightEnd := by
  cases k with
  | zero =>
      change headBuffer (bits.getD 0 false) ≠ .rightEnd
      cases bits.getD 0 false <;> simp [headBuffer]
  | succ k =>
      change newMid (bits.getD (k + 1) false)
        (PakScannerPath.suffixMode bits (k + 2)) ≠ .rightEnd
      cases bits.getD (k + 1) false <;>
        cases PakScannerPath.suffixMode bits (k + 2) <;> decide

/-- An admissible terminal path cannot be confused with the all-`mid` path:
at the terminal edge its north state has mode `tail`, whereas the ordinary
path retains the right-to-left `suffixMode`, which is never `tail`. -/
theorem scannerColumn_ne_terminalScannerColumn
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (_hterminal : 0 < terminal) (hbound : terminal < bits.length) :
    PakScannerPath.scannerColumn bits hbits ≠
      PakScannerTerminal.terminalScannerColumn bits hbits terminal := by
  intro heq
  let j : Fin (bits.length + 2) := ⟨terminal, by omega⟩
  have hcell := congrFun heq j
  have hpairs :
      (PakScannerPath.scannerState bits hbits terminal,
        PakScannerPath.scannerState bits hbits (terminal + 1)) =
      (PakScannerTerminal.terminalScannerState bits hbits terminal terminal,
        PakScannerTerminal.terminalScannerState bits hbits terminal (terminal + 1)) := by
    simpa [PakScannerPath.scannerColumn,
      PakScannerTerminal.terminalScannerColumn] using Option.some.inj hcell
  have hmode := congrArg (fun p : State × State => p.2.mode) hpairs
  have hbad : PakScannerPath.suffixMode bits (terminal + 1) = .tail := by
    simpa [PakScannerPath.scannerState, PakScannerTerminal.terminalScannerState,
      PakScannerPath.midState, PakScannerTerminal.terminalTailState,
      hbound] using hmode
  exact PakScannerPath.suffixMode_ne_tail bits (terminal + 1) hbad

/-- The location of an admissible `terminal` edge is recoverable from its
column: the first `tail` state occurs immediately above that index. -/
theorem terminalScannerColumn_terminal_unique
    (bits : List Bool) (hbits : 0 < bits.length)
    {terminal₁ terminal₂ : ℕ}
    (hpos₁ : 0 < terminal₁) (hbound₁ : terminal₁ < bits.length)
    (hpos₂ : 0 < terminal₂) (hbound₂ : terminal₂ < bits.length)
    (heq : PakScannerTerminal.terminalScannerColumn bits hbits terminal₁ =
      PakScannerTerminal.terminalScannerColumn bits hbits terminal₂) :
    terminal₁ = terminal₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let j : Fin (bits.length + 2) := ⟨terminal₁ + 1, by omega⟩
    have hcell := congrFun heq j
    have hpairs := Option.some.inj hcell
    have hmode := congrArg (fun p : State × State => p.1.mode) hpairs
    dsimp [j] at hmode
    have hnotzero : terminal₁ + 1 ≠ 0 := by omega
    have hnotle : ¬ terminal₁ + 1 ≤ terminal₁ := by omega
    have hlelen : terminal₁ + 1 ≤ bits.length := by omega
    have hle₂ : terminal₁ + 1 ≤ terminal₂ := by omega
    have hbad : .tail = PakScannerPath.suffixMode bits (terminal₁ + 1) := by
      simpa [PakScannerTerminal.terminalScannerColumn,
        PakScannerTerminal.terminalScannerState, PakScannerPath.midState,
        PakScannerTerminal.terminalTailState, hpos₁, hbound₁, hpos₂,
        hbound₂, hlt, hnotzero, hnotle, hlelen, hle₂] using hmode
    exact PakScannerPath.suffixMode_ne_tail bits (terminal₁ + 1) hbad.symm
  · let j : Fin (bits.length + 2) := ⟨terminal₂ + 1, by omega⟩
    have hcell := congrFun heq j
    have hpairs := Option.some.inj hcell
    have hmode := congrArg (fun p : State × State => p.1.mode) hpairs
    dsimp [j] at hmode
    have hnotzero : terminal₂ + 1 ≠ 0 := by omega
    have hle₁ : terminal₂ + 1 ≤ terminal₁ := by omega
    have hnotle : ¬ terminal₂ + 1 ≤ terminal₂ := by omega
    have hlelen : terminal₂ + 1 ≤ bits.length := by omega
    have hbad : PakScannerPath.suffixMode bits (terminal₂ + 1) = .tail := by
      simpa [PakScannerTerminal.terminalScannerColumn,
        PakScannerTerminal.terminalScannerState, PakScannerPath.midState,
        PakScannerTerminal.terminalTailState, hpos₁, hbound₁, hpos₂,
        hbound₂, hgt, hnotzero, hle₁, hnotle, hlelen] using hmode
    exact PakScannerPath.suffixMode_ne_tail bits (terminal₂ + 1) hbad

/-- The two alternatives are disjoint, while the terminal parameter in the
right summand is unique. -/
theorem scannerColumnForm_disjoint
    (bits : List Bool) (hbits : 0 < bits.length)
    (column : Fin (bits.length + 2) → ScannerTile State)
    (hno : NoTerminalColumn bits hbits column)
    (hterminal : TerminalColumn bits hbits column) : False := by
  rcases hterminal with ⟨terminal, hpos, hbound, hcolumn⟩
  apply scannerColumn_ne_terminalScannerColumn bits hbits terminal hpos hbound
  rw [← hno, hcolumn]

/-- The old tableau window forced by alternative A.  This is deliberately an
exact buffer-level description: unlike the terminal alternative, it contains
only `dataCell`/`hash` output and hence has no `rightEnd` endpoint. -/
def noTerminalOldWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length)
    (j : Fin (bits.length + 2)) :
    CellTriple (TableauCell MachineState Tape) :=
  { minus := PakCouplingGenerated.bufferCell B
      (PakScannerPath.scannerState bits hbits j.1).left
    center := PakCouplingGenerated.bufferCell B
      (PakScannerPath.scannerState bits hbits j.1).centre
    plus := PakCouplingGenerated.bufferCell B
      (PakScannerPath.scannerState bits hbits (j.1 + 1)).centre }

/-- A full-frame east cell in alternative A emits exactly the ordinary path
window above.  Thus a tableau readback that demands a `rightEnd` can rule out
this branch, but horizontal coupling and `LegalScan` alone cannot. -/
theorem FullFrame.east_no_terminal_oldWindow
    {w : ℕ} (F : FullFrame w w) (bits : List Bool) (hbits : 0 < bits.length)
    (hheight : w = bits.length + 2)
    (hno : NoTerminalColumn bits hbits
      (fun j : Fin (bits.length + 2) =>
        scannerAt F.tiling (eastIndex F.width_pos) (Fin.cast hheight.symm j)))
    (j : Fin (bits.length + 2)) :
    (tableauAt F.tiling (eastIndex F.width_pos) (Fin.cast hheight.symm j)).1.old =
      noTerminalOldWindow MStarULogAssembly.boundaryData bits hbits j := by
  rcases F.east_emits_tableau_window (Fin.cast hheight.symm j) with
    ⟨s, t, hscan, hold⟩
  have hcanonical := congrFun hno j
  have hpairs : (s, t) =
      (PakScannerPath.scannerState bits hbits j.1,
        PakScannerPath.scannerState bits hbits (j.1 + 1)) := by
    rw [hcanonical] at hscan
    simpa [PakScannerPath.scannerColumn] using hscan.symm
  rw [hold]
  cases hpairs
  rfl

end PakFixedPolyomino.PakScannerColumnForms
