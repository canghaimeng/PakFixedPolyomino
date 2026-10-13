import PakFixedPolyomino.PakScannerPath
import Mathlib.Tactic

/-!
# A scanner column with an explicit copier endpoint

The side word is much wider than the parser/copy workspace.  The scanner
therefore has one finite terminal letter: after the exact parser/copier
reserve it emits `rightEnd`, and then emits hashes up to the omitted high
bits.  The terminal and tail clauses are part of the finite scanner table;
they are not a post-hoc tape rewrite.
-/

namespace PakFixedPolyomino.PakScannerTerminal

open ConcretePakScanner
open PakScannerPath

variable {MachineState Tape : Type*}

def terminalDataCell (bits : List Bool) (terminal k : ℕ) : Buffer :=
  if k < terminal then dataCell bits k
  else if k = terminal then .rightEnd
  else .hash

def terminalTailState (bits : List Bool) (terminal j : ℕ) : State :=
  { phase := .mid
    left := if j = 1 then .hash else terminalDataCell bits terminal (j - 2)
    centre := terminalDataCell bits terminal (j - 1)
    lookahead := .lh0
    mode := .tail }

def terminalTopState (bits : List Bool) (terminal : ℕ) : State :=
  { phase := .top
    left := terminalDataCell bits terminal (bits.length - 1)
    centre := .hash
    lookahead := .lh1
    mode := .high }

def terminalScannerState (bits : List Bool) (_hbits : 0 < bits.length)
    (terminal k : ℕ) : State :=
  if k = 0 then PakCouplingGenerated.scannerBottom
  else if k ≤ terminal then midState bits k
  else if k ≤ bits.length then terminalTailState bits terminal k
  else if k = bits.length + 1 then terminalTopState bits terminal
  else ConcretePakScanner.topNorth

def terminalScannerColumn (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) : Fin (bits.length + 2) → ScannerTile State :=
  fun j => some (terminalScannerState bits hbits terminal j.1,
    terminalScannerState bits hbits terminal (j.1 + 1))

def terminalScannerTapeCell
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (terminal : ℕ) (z : Int) :
    TableauCell MachineState Tape :=
  if z ≤ 0 then .plain B.hash
  else if Int.toNat (z - 1) < bits.length then
    PakCouplingGenerated.bufferCell B
      (terminalDataCell bits terminal (Int.toNat (z - 1)))
  else .plain B.hash

def terminalScannerTapeWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (terminal : ℕ) (j : Fin (bits.length + 2)) :
    CellTriple (TableauCell MachineState Tape) :=
  { minus := terminalScannerTapeCell B bits terminal (j.1 - 1)
    center := terminalScannerTapeCell B bits terminal j.1
    plus := terminalScannerTapeCell B bits terminal (j.1 + 1) }

theorem terminalDataCell_lt (bits : List Bool) (terminal k : ℕ)
    (hk : k < terminal) : terminalDataCell bits terminal k = dataCell bits k := by
  simp [terminalDataCell, hk]

theorem terminalDataCell_eq (bits : List Bool) (terminal : ℕ) :
    terminalDataCell bits terminal terminal = .rightEnd := by
  simp [terminalDataCell]

theorem terminalDataCell_gt (bits : List Bool) (terminal k : ℕ)
    (hk : terminal < k) : terminalDataCell bits terminal k = .hash := by
  have hnot : ¬ k < terminal := by omega
  simp [terminalDataCell, hk, hnot, Nat.ne_of_gt hk]

theorem terminal_edge_legal (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length) :
    LegalScan (midState bits terminal)
      (terminalTailState bits terminal (terminal + 1)) false := by
  refine ⟨.terminal, ?_⟩
  have hidx : terminal + 1 - 2 = terminal - 1 := by omega
  have hterm0 : terminal ≠ 0 := by omega
  have htm1 : terminal - 1 < terminal := by omega
  have hmode := suffixMode_ne_tail bits terminal
  have hmodeCases : suffixMode bits terminal = .high ∨
      suffixMode bits terminal = .binary := by
    cases hm : suffixMode bits terminal <;> simp_all
  simp [LegalClause, Shift, midState, terminalTailState,
    terminalDataCell, hterminal, hbound, hidx, hterm0, htm1, hmodeCases]

theorem terminal_tail_legal (bits : List Bool) (hbits : 0 < bits.length)
    (terminal j : ℕ) (hbound : terminal < bits.length)
    (hj : terminal + 1 ≤ j) :
    LegalScan (terminalTailState bits terminal j)
      (terminalTailState bits terminal (j + 1)) false := by
  refine ⟨.tail, ?_⟩
  have hzero : j ≠ 0 := by omega
  have hnext1 : j + 1 ≠ 1 := by omega
  have hidx : j + 1 - 2 = j - 1 := by omega
  have hnext : terminal < j := by omega
  have hnotbefore : ¬ j < terminal := by omega
  simp [LegalClause, Shift, terminalTailState, terminalDataCell,
    hzero, hnext1, hidx, hnext, hnotbefore, Nat.ne_of_gt hnext]

theorem terminal_mid_top_legal (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hbound : terminal < bits.length) :
    LegalScan (terminalTailState bits terminal bits.length)
      (terminalTopState bits terminal) false := by
  refine ⟨.preTop, ?_⟩
  have hlen : terminal < bits.length := hbound
  simp [LegalClause, Shift, terminalTailState, terminalTopState,
    terminalDataCell, hlen]

theorem terminal_top_cap_legal (bits : List Bool) (terminal : ℕ)
    (hbound : terminal < bits.length) (b : Bool) :
    LegalScan (terminalTopState bits terminal) ConcretePakScanner.topNorth b := by
  refine ⟨.top, ?_⟩
  simp [LegalClause, Shift, terminalTopState, ConcretePakScanner.topNorth]

theorem terminalScannerColumn_vertical (bits : List Bool)
    (hbits : 0 < bits.length) (terminal : ℕ)
    (j : Fin (bits.length + 2)) (hj : j.1 + 1 < bits.length + 2) :
    (scannerTile (terminalScannerColumn bits hbits terminal j)).north =
      (scannerTile
        (terminalScannerColumn bits hbits terminal ⟨j.1 + 1, hj⟩)).south := by
  rfl

theorem terminalScannerColumn_legal (bits : List Bool)
    (hbits : 0 < bits.length) (terminal : ℕ)
    (hterminal : 0 < terminal) (hbound : terminal < bits.length)
    (topBit : Bool) (j : Fin (bits.length + 2)) :
    ∃ s t : State,
      terminalScannerColumn bits hbits terminal j = some (s, t) ∧
        LegalScan s t
          (if j.1 < terminal then scannerBit bits false topBit j
           else if j.1 = terminal then false
           else if j.1 < bits.length then false
           else if j.1 = bits.length then false else topBit) := by
  by_cases hzero : j.1 = 0
  · have hone : 1 ≤ bits.length := by omega
    have hjlt : j.1 < terminal := by omega
    have hget : bits.getD j.1 false = bits.getD 0 false := by rw [hzero]
    have hterm0 : terminal ≠ 0 := by omega
    have hbit :
        (if j.1 < terminal then scannerBit bits false topBit j
         else if j.1 = terminal then false
          else if j.1 < bits.length then false
         else if j.1 = bits.length then false else topBit) =
          scannerBit bits false topBit j := by simp [hzero, hjlt, hterm0]
    refine ⟨PakCouplingGenerated.scannerBottom, midState bits 1, ?_, ?_⟩
    · simp [terminalScannerColumn, terminalScannerState, hzero, hone,
        hterminal, hterm0]
    · rw [hbit]
      simpa [scannerBit, hzero, hbits, hget] using bottom_mid_legal bits
  · by_cases hbefore : j.1 < terminal
    · have hjle : j.1 ≤ terminal := by omega
      have hnext0 : j.1 + 1 ≠ 0 := by omega
      have hnextle : j.1 + 1 ≤ terminal := by omega
      have hjbits : j.1 < bits.length := by omega
      have hbit :
          (if j.1 < terminal then scannerBit bits false topBit j
           else if j.1 = terminal then false
           else if j.1 < bits.length then false
           else if j.1 = bits.length then false else topBit) =
            scannerBit bits false topBit j := by simp [hbefore, hjbits]
      refine ⟨midState bits j.1, midState bits (j.1 + 1), ?_, ?_⟩
      · simp [terminalScannerColumn, terminalScannerState, hzero,
          hbefore, hjle, hnext0, hnextle]
      · rw [hbit]
        simpa [scannerBit, hjbits] using
          mid_mid_legal bits j.1 (by omega)
    · by_cases hterm : j.1 = terminal
      · have hterm0 : terminal ≠ 0 := by omega
        have hnextle : terminal + 1 ≤ bits.length := by omega
        have hnextnotle : ¬ terminal + 1 ≤ terminal := by omega
        have hbit :
            (if j.1 < terminal then scannerBit bits false topBit j
             else if j.1 = terminal then false
             else if j.1 < bits.length then false
             else if j.1 = bits.length then false else topBit) = false := by
          simp [hterm]
        refine ⟨midState bits terminal,
            terminalTailState bits terminal (terminal + 1), ?_, ?_⟩
        · simp [terminalScannerColumn, terminalScannerState, hzero,
            hbefore, hterm, hterminal, hterm0, hnextle, hnextnotle]
        · rw [hbit]
          exact terminal_edge_legal bits hbits terminal hterminal hbound
      · by_cases htail : j.1 < bits.length
        · have hjle : j.1 ≤ bits.length := by omega
          have hnext0 : j.1 + 1 ≠ 0 := by omega
          have hnextle : j.1 + 1 ≤ bits.length := by omega
          have hjbound : terminal + 1 ≤ j.1 := by omega
          have hjnotle : ¬ j.1 ≤ terminal := by omega
          have hbit :
              (if j.1 < terminal then scannerBit bits false topBit j
               else if j.1 = terminal then false
               else if j.1 < bits.length then false
               else if j.1 = bits.length then false else topBit) = false := by
            simp [hbefore, hterm, htail]
          refine ⟨terminalTailState bits terminal j.1,
              terminalTailState bits terminal (j.1 + 1), ?_, ?_⟩
          · simp [terminalScannerColumn, terminalScannerState, hzero,
              hbefore, hterm, htail, hjle, hjnotle, hnext0, hnextle]
          · rw [hbit]
            exact terminal_tail_legal bits hbits terminal j.1 hbound hjbound
        · have hcase : j.1 = bits.length ∨ j.1 = bits.length + 1 := by
            omega
          rcases hcase with hpre | htop
          · have hlen0 : bits.length ≠ 0 := by omega
            have hle : ¬ bits.length ≤ terminal := by omega
            have hnot : ¬ bits.length < terminal := by omega
            have hbit :
                (if j.1 < terminal then scannerBit bits false topBit j
                 else if j.1 = terminal then false
                 else if j.1 < bits.length then false
                 else if j.1 = bits.length then false else topBit) = false := by
              simp [hpre, hle, hnot]
            refine ⟨terminalTailState bits terminal bits.length,
                terminalTopState bits terminal, ?_, ?_⟩
            · simp [terminalScannerColumn, terminalScannerState, hzero,
                hbefore, hterm, htail, hpre, hbound, hlen0, hle, hnot]
            · rw [hbit]
              exact terminal_mid_top_legal bits hbits terminal hbound
          · have htop0 : bits.length + 1 ≠ 0 := by omega
            have htopmid : ¬ bits.length + 1 ≤ terminal := by omega
            have hcap0 : bits.length + 2 ≠ 0 := by omega
            have hcapmid : ¬ bits.length + 2 ≤ bits.length := by omega
            have hcapTop : bits.length + 2 ≠ bits.length + 1 := by omega
            have htoplt : ¬ bits.length + 1 < terminal := by omega
            have htopne : bits.length + 1 ≠ terminal := by omega
            have hbit :
                (if j.1 < terminal then scannerBit bits false topBit j
                 else if j.1 = terminal then false
                 else if j.1 < bits.length then false
                 else if j.1 = bits.length then false else topBit) = topBit := by
              simp [htop, htoplt, htopne]
            refine ⟨terminalTopState bits terminal,
                ConcretePakScanner.topNorth, ?_, ?_⟩
            · simp [terminalScannerColumn, terminalScannerState, hzero,
                hbefore, hterm, htail, htop, htop0, htopmid, hcap0,
                hcapmid, hcapTop, htoplt, htopne]
            · rw [hbit]
              exact terminal_top_cap_legal bits terminal hbound topBit

def terminalScannerTiling (w : ℕ) (hw : 0 < w) (bits : List Bool)
    (hbits : 0 < bits.length) (terminal : ℕ)
    (hterminal : 0 < terminal) (hbound : terminal < bits.length) :
    OpenWangTiling (scannerTile (S := State)) w (bits.length + 2) :=
  PakCanonicalScanner.eastColumnTiling hw
    (terminalScannerColumn bits hbits terminal)
    (terminalScannerColumn_vertical bits hbits terminal)

end PakFixedPolyomino.PakScannerTerminal
