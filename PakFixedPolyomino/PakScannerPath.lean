import PakFixedPolyomino.PakEncodedStart
import Mathlib.Tactic

/-!
# The parametric literal scanner path

For a finite low-to-high bit word, this module builds the scanner states used
between the bottom `bot` clause and the top/cap clauses.  The mode is computed
from right to left, exactly as required by `ModeOut`; consequently the cells
after the most significant one become literal `work` cells.
-/

namespace PakFixedPolyomino.PakScannerPath

open ConcretePakScanner

/-- The mode of the source state at a given bit position, computed from the
remaining more-significant input bits. -/
def suffixMode (bits : List Bool) (j : ℕ) : Mode :=
  (bits.drop j).foldr (fun b m => modeOut b m) .high

theorem suffixMode_step (bits : List Bool) (j : ℕ) :
    suffixMode bits j =
      modeOut (bits.getD j false) (suffixMode bits (j + 1)) := by
  induction bits generalizing j with
  | nil =>
      cases j <;> rfl
  | cons b bits ih =>
      cases j with
      | zero => rfl
      | succ j => simpa [suffixMode] using ih j

theorem suffixMode_length (bits : List Bool) :
    suffixMode bits bits.length = .high := by
  simp [suffixMode]

private theorem foldMode_ne_tail (bits : List Bool) :
    bits.foldr (fun b m => modeOut b m) .high ≠ .tail := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
      cases htail : bits.foldr (fun b m => modeOut b m) .high <;>
        cases b <;> simp_all [List.foldr, modeOut]

theorem suffixMode_ne_tail (bits : List Bool) (j : ℕ) :
    suffixMode bits j ≠ .tail := by
  unfold suffixMode
  exact foldMode_ne_tail (bits.drop j)

private theorem foldMode_binary_of_true_mem (bits : List Bool)
    (htrue : true ∈ bits) :
    bits.foldr (fun b m => modeOut b m) .high = .binary := by
  induction bits with
  | nil => simp at htrue
  | cons b bits ih =>
      simp only [List.mem_cons] at htrue
      rcases htrue with h | h
      · subst b
        cases htail : bits.foldr (fun b m => modeOut b m) .high with
        | high =>
            simp only [List.foldr]
            rw [htail]
            rfl
        | binary =>
            simp only [List.foldr]
            rw [htail]
            rfl
        | tail => exact (foldMode_ne_tail bits htail).elim
      · have htail := ih h
        simp [htail]
        cases b <;> rfl

/-- A true bit at or above a position irreversibly switches the backwards
mode fold to binary. -/
theorem suffixMode_binary_of_true_mem (bits : List Bool) (j : ℕ)
    (htrue : true ∈ bits.drop j) : suffixMode bits j = .binary :=
  foldMode_binary_of_true_mem _ htrue

/-- The physical cell at data position `k`: the first one is the marked
start cell; all later ones are exactly the `NewMid` output prescribed by the
target mode. -/
def dataCell (bits : List Bool) : ℕ → Buffer
  | 0 => headBuffer (bits.getD 0 false)
  | k + 1 => newMid (bits.getD (k + 1) false) (suffixMode bits (k + 2))

/-- The mid-phase state immediately above data position `j - 1`.  It is used
only for positive `j` not exceeding `bits.length`. -/
def midState (bits : List Bool) (j : ℕ) : State :=
  { phase := .mid
    left := if j = 1 then .hash else dataCell bits (j - 2)
    centre := dataCell bits (j - 1)
    lookahead := .lh0
    mode := suffixMode bits j }

def topState (bits : List Bool) : State :=
  { phase := .top
    left := dataCell bits (bits.length - 1)
    centre := .hash
    lookahead := .lh1
    mode := .high }

/-- The bottom edge starts the scanner and introduces the marked first cell. -/
theorem bottom_mid_legal (bits : List Bool) :
    LegalScan PakCouplingGenerated.scannerBottom (midState bits 1)
      (bits.getD 0 false) := by
  refine ⟨.bot, ?_⟩
  simp [LegalClause, Shift, midState, dataCell,
    PakCouplingGenerated.scannerBottom]

/-- Every internal mid edge is a literal scanner rule.  The source/target
mode equality is the right-to-left recurrence above, not an assumption. -/
theorem mid_mid_legal (bits : List Bool) (j : ℕ) (hj : 0 < j) :
    LegalScan (midState bits j) (midState bits (j + 1))
      (bits.getD j false) := by
  refine ⟨.mid, ?_⟩
  unfold LegalClause Shift
  rcases j with _ | j
  · simp at hj
  constructor
  · simp [midState, dataCell]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [midState, dataCell]
  · exact suffixMode_step bits (j + 1)

/-- Once the data word is exhausted, the pre-top scanner clause closes it
with a literal hash. -/
theorem mid_top_legal (bits : List Bool) (hbits : 0 < bits.length) :
    LegalScan (midState bits bits.length) (topState bits) false := by
  refine ⟨.preTop, ?_⟩
  simp [LegalClause, Shift, midState, topState, suffixMode_length, hbits]

/-- The cap edge is independent of its ripple bit, exactly as in the finite
scanner table. -/
theorem top_cap_legal (bits : List Bool) (b : Bool) :
    LegalScan (topState bits) ConcretePakScanner.topNorth b := by
  refine ⟨.top, ?_⟩
  simp [LegalClause, Shift, topState, ConcretePakScanner.topNorth]

/-- The shared state sequence behind the scanner path.  Sharing its adjacent
states makes the vertical Wang match definitional rather than a dependent
index rewrite. -/
def scannerState (bits : List Bool) (_hbits : 0 < bits.length) (k : ℕ) : State :=
  if k = 0 then PakCouplingGenerated.scannerBottom
  else if k ≤ bits.length then midState bits k
  else if k = bits.length + 1 then topState bits
  else ConcretePakScanner.topNorth

/-- The complete vertical scanner column for a nonempty data word. -/
def scannerColumn (bits : List Bool) (hbits : 0 < bits.length)
    (j : Fin (bits.length + 2)) : ScannerTile State :=
  some (scannerState bits hbits j.1, scannerState bits hbits (j.1 + 1))

theorem scannerColumn_vertical (bits : List Bool) (hbits : 0 < bits.length)
    (j : Fin (bits.length + 2)) (hj : j.1 + 1 < bits.length + 2) :
    (scannerTile (scannerColumn bits hbits j)).north =
      (scannerTile (scannerColumn bits hbits ⟨j.1 + 1, hj⟩)).south := by
  rfl

/-- The ripple bit read by each scanner edge.  The last two labels are kept
separate because `preTop` requires zero while `top` ignores its label. -/
def scannerBit (bits : List Bool) (preTopBit topBit : Bool)
    (j : Fin (bits.length + 2)) : Bool :=
  if j.1 < bits.length then bits.getD j.1 false
  else if j.1 = bits.length then preTopBit else topBit

theorem scannerColumn_legal (bits : List Bool) (hbits : 0 < bits.length)
    (topBit : Bool) (j : Fin (bits.length + 2)) :
    ∃ s t : State,
      scannerColumn bits hbits j = some (s, t) ∧
        LegalScan s t (scannerBit bits false topBit j) := by
  by_cases hzero : j.1 = 0
  · have hone : 1 ≤ bits.length := by omega
    have hjlt : j.1 < bits.length := by omega
    have hget : bits.getD j.1 false = bits.getD 0 false := by
      rw [hzero]
    refine ⟨PakCouplingGenerated.scannerBottom, midState bits 1, ?_, ?_⟩
    · simp [scannerColumn, scannerState, hzero, hone]
    · simpa only [scannerBit, if_pos hjlt, hget] using bottom_mid_legal bits
  · by_cases hmid : j.1 < bits.length
    · refine ⟨midState bits j.1, midState bits (j.1 + 1), ?_, ?_⟩
      have hjle : j.1 ≤ bits.length := by omega
      have hnext0 : j.1 + 1 ≠ 0 := by omega
      have hnextle : j.1 + 1 ≤ bits.length := by omega
      · simp [scannerColumn, scannerState, hzero, hjle, hnext0, hnextle]
      · simpa [scannerBit, hmid] using mid_mid_legal bits j.1 (by omega)
    · have hpre : j.1 = bits.length ∨ j.1 = bits.length + 1 := by omega
      rcases hpre with hpre | htop
      · have hlen0 : bits.length ≠ 0 := by omega
        have htop0 : bits.length + 1 ≠ 0 := by omega
        have htopmid : ¬ bits.length + 1 ≤ bits.length := by omega
        refine ⟨midState bits bits.length, topState bits, ?_, ?_⟩
        · simp [scannerColumn, scannerState, hpre, hlen0, htop0, htopmid]
        · simpa [scannerBit, hpre] using mid_top_legal bits hbits
      · have htop0 : bits.length + 1 ≠ 0 := by omega
        have htopmid : ¬ bits.length + 1 ≤ bits.length := by omega
        have hcap0 : bits.length + 2 ≠ 0 := by omega
        have hcapmid : ¬ bits.length + 2 ≤ bits.length := by omega
        have hcapTop : bits.length + 2 ≠ bits.length + 1 := by omega
        refine ⟨topState bits, ConcretePakScanner.topNorth, ?_, ?_⟩
        · simp [scannerColumn, scannerState, htop, htop0, htopmid,
            hcap0, hcapmid, hcapTop]
        · simpa [scannerBit, htop] using top_cap_legal bits topBit

/-- Place the constructed scanner column at the east side of an arbitrary
positive rectangle. -/
def scannerTiling (w : ℕ) (hw : 0 < w) (bits : List Bool)
    (hbits : 0 < bits.length) :
    OpenWangTiling (scannerTile (S := State)) w (bits.length + 2) :=
  PakCanonicalScanner.eastColumnTiling hw (scannerColumn bits hbits)
    (scannerColumn_vertical bits hbits)

end PakFixedPolyomino.PakScannerPath
