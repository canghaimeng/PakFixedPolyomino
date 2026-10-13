import PakFixedPolyomino.PakScannerTerminal
import PakFixedPolyomino.WangIdentityRefinement

/-! A fixed local identity refinement: exactly two identities at a marked
scanner tile whose source is tail-mode hash, one at every other tile. The
weight of the actual terminal column is its true exterior hash-tail power. -/
namespace PakFixedPolyomino.PakScannerTailIdentityWeights
open ConcretePakScanner PakScannerPath PakScannerTerminal

def tailIdentityCopies : ScannerTile State → Nat
  | none => 1
  | some (s, _) => if s.mode = .tail ∧ s.centre = .hash then 2 else 1

def rowIdentityCopies (bits : List Bool) (positive : 0 < bits.length)
    (terminal row : Nat) : Nat :=
  tailIdentityCopies (some (terminalScannerState bits positive terminal row,
    terminalScannerState bits positive terminal (row + 1)))

theorem row_identity_copies (bits : List Bool) (positive : 0 < bits.length)
    (terminal row : Nat) (bound : terminal < bits.length) :
    rowIdentityCopies bits positive terminal row =
      if terminal + 2 ≤ row ∧ row ≤ bits.length then 2 else 1 := by
  by_cases zero : row = 0
  · subst row
    simp [rowIdentityCopies, terminalScannerState, tailIdentityCopies,
      PakCouplingGenerated.scannerBottom]
  · by_cases before : row ≤ terminal
    · have mode := suffixMode_ne_tail bits row
      have no : ¬ (terminal + 2 ≤ row ∧ row ≤ bits.length) := by omega
      simp [rowIdentityCopies, terminalScannerState, zero, before,
        tailIdentityCopies, midState, mode, no]
    · by_cases inside : row ≤ bits.length
      · have predecessor : terminal ≤ row - 1 := by omega
        by_cases endpoint : row - 1 = terminal
        · have no : ¬ (terminal + 2 ≤ row ∧ row ≤ bits.length) := by omega
          simp [rowIdentityCopies, terminalScannerState, zero, before, inside,
            tailIdentityCopies, terminalTailState, endpoint, terminalDataCell, no]
          omega
        · have past : terminal < row - 1 := by omega
          have yes : terminal + 2 ≤ row ∧ row ≤ bits.length := by omega
          simp [rowIdentityCopies, terminalScannerState, zero, before, inside,
            tailIdentityCopies, terminalTailState,
            terminalDataCell_gt bits terminal (row - 1) past, yes]
      · have no : ¬ (terminal + 2 ≤ row ∧ row ≤ bits.length) := by omega
        by_cases top : row = bits.length + 1
        · have notAfter : ¬ bits.length < terminal := by omega
          simp [rowIdentityCopies, terminalScannerState, zero, before, inside, top,
            tailIdentityCopies, terminalTopState, no, notAfter]
        · simp [rowIdentityCopies, terminalScannerState, zero, before, inside, top,
            tailIdentityCopies, ConcretePakScanner.topNorth, no]

def terminalIdentityWeight (bits : List Bool) (positive : 0 < bits.length)
    (terminal : Nat) : Nat :=
  ∏ row ∈ Finset.range (bits.length + 2), rowIdentityCopies bits positive terminal row

theorem terminal_identity_weight (bits : List Bool) (positive : 0 < bits.length)
    (terminal : Nat) (bound : terminal < bits.length) :
    terminalIdentityWeight bits positive terminal = 2 ^ (bits.length - terminal - 1) := by
  have cells : (Finset.range (bits.length + 2)).filter
      (fun row => terminal + 2 ≤ row ∧ row ≤ bits.length) =
      Finset.Icc (terminal + 2) bits.length := by
    ext row
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  unfold terminalIdentityWeight
  simp_rw [row_identity_copies bits positive terminal _ bound]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [cells, Nat.card_Icc]
  have count : bits.length + 1 - (terminal + 2) = bits.length - terminal - 1 := by omega
  rw [count]

end PakFixedPolyomino.PakScannerTailIdentityWeights
