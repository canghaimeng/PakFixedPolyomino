import PakFixedPolyomino.ULogSourceObliviousRLCellExecution
import PakFixedPolyomino.ULogSourceObliviousLRWindowExecution
import Mathlib.Tactic

/-!
# Literal complete right-to-left window of the finite oblivious scanner

From `.skipRL a false ⟨nt-1⟩` at coordinate `W` on `windowTape u`, the
chronological reverse concatenation of every cell's `skipRLBitArrows` block
and `updateRLFlagArrow`, followed by `skipRLLeftBoundaryArrow`, has length
`W+1` and ends at `.atLeft a.target` at coordinate `0` on
`windowTape (rlWindow u a hleft)`.  Symbols are already the LR-updated
letters; only flags move, and every `updateRL` value is derived from the
unique original mark.  This is the RL intermediate window, not the original
Pak theorem.
-/

namespace PakFixedPolyomino.ULogSourceObliviousRLWindowExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceOneHotBlocks
open ULogSourceObliviousWindow
open ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution
open ULogSourceObliviousRLCellExecution
open ULogSourceObliviousLRWindowExecution

variable {ns nt : ℕ}

/-! ## Intermediate LogicalWindow after the RL pass -/

def rlWindow (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val) : LogicalWindow nt :=
  { cells := u.cells
    head :=
      if h : a.move = .left then
        ⟨u.head.val - 1, by
          have := hleft h
          have : u.head.val - 1 < u.cells.length := by omega
          simpa using this⟩
      else
        ⟨u.head.val, by simp⟩ }

@[simp] theorem rlWindow_cells (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    (rlWindow u a hleft).cells = u.cells := rfl

@[simp] theorem rlWindow_cells_length (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    (rlWindow u a hleft).cells.length = u.cells.length := rfl

theorem rlWindow_windowWidth (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    windowWidth (rlWindow u a hleft) = windowWidth u := by
  simp [windowWidth, LogicalWindow.encode, rlWindow]

theorem rlWindow_head_left (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (hmove : a.move = .left) :
    (rlWindow u a hleft).head.val = u.head.val - 1 := by
  simp [rlWindow, hmove]

theorem rlWindow_head_not_left (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (hmove : a.move ≠ .left) :
    (rlWindow u a hleft).head.val = u.head.val := by
  simp [rlWindow, hmove]

theorem rlArmed_last (u : LogicalWindow nt) (a : BoundedAction ns nt) :
    rlArmed u a (u.cells.length - 1) = false := by
  have hne : u.cells.length ≠ u.head.val := Nat.ne_of_gt u.head.isLt
  have hpos := window_cells_pos u
  have hidx : (u.cells.length - 1) + 1 = u.cells.length := by omega
  simp [rlArmed, hidx, hne]

theorem rlCarry_zero (u : LogicalWindow nt) (a : BoundedAction ns nt) :
    decide (a.move = .left ∧ u.cells.length - 0 = u.head.val) = false := by
  have hne : u.cells.length ≠ u.head.val := Nat.ne_of_gt u.head.isLt
  simp [hne]

theorem rlCarry_all (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    decide (a.move = .left ∧
      u.cells.length - u.cells.length = u.head.val) = false := by
  by_cases hmove : a.move = .left
  · have := hleft hmove
    simp [hmove]
    omega
  · simp [hmove]

theorem rlCarry_eq_rlArmed (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (r : ℕ) (hr : r < u.cells.length) :
    decide (a.move = .left ∧ u.cells.length - r = u.head.val) =
      rlArmed u a (u.cells.length - 1 - r) := by
  have hidx : u.cells.length - r = (u.cells.length - 1 - r) + 1 := by omega
  simp [rlArmed, hidx]

theorem rlCarry_succ_eq_out (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (r : ℕ) (hr : r < u.cells.length) :
    decide (a.move = .left ∧ u.cells.length - (r + 1) = u.head.val) =
      decide (a.move = .left ∧ u.cells.length - 1 - r = u.head.val) := by
  have hidx : u.cells.length - (r + 1) = u.cells.length - 1 - r := by omega
  simp [hidx]

/-! ## Derived flag update at the unique original mark -/

theorem updateRL_window_cell (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (k : Fin u.cells.length) :
    updateRL a (rlArmed u a k.val)
      (tapeOfBit (decide (k.val = u.head.val))) =
      some (tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)),
        decide (a.move = .left ∧ k.val = u.head.val)) := by
  have hxvalid :
      validBit (tapeOfBit (decide (k.val = u.head.val))) = true :=
    validBit_tapeOfBit _
  unfold updateRL
  simp [hxvalid]
  by_cases hmove : a.move = .left
  · have hnew := rlWindow_head_left u a hleft hmove
    have hpos := hleft hmove
    simp only [rlArmed, hmove, decide_true, Bool.true_and, hnew]
    by_cases hk0 : k.val = u.head.val
    · have hk1 : k.val + 1 ≠ u.head.val := by omega
      have hne : ¬ u.head.val = u.head.val - 1 := by omega
      simp [hk0, hk1, hne, tapeOfBit, one, zero]
    · by_cases hk1 : k.val + 1 = u.head.val
      · have heq : k.val = u.head.val - 1 := by omega
        have hplus : u.head.val - 1 + 1 = u.head.val :=
          Nat.sub_add_cancel hpos
        have hne : ¬ u.head.val - 1 = u.head.val := by omega
        simp [hk0, hk1, heq, hplus, hne, tapeOfBit, one, zero]
      · have hne : ¬ k.val = u.head.val - 1 := by omega
        simp [hk0, hk1, hne, tapeOfBit, one, zero]
  · have hnew := rlWindow_head_not_left u a hleft hmove
    simp [rlArmed, hmove, hnew]

/-! ## Physical flag coordinates and successive flag writes -/

def rlFlagInt (nt k : ℕ) : Int := ((1 + k * (nt + 1) : ℕ) : Int)

theorem rlFlagInt_inj {nt k1 k2 : ℕ}
    (h : rlFlagInt nt k1 = rlFlagInt nt k2) : k1 = k2 := by
  have hN : 1 + k1 * (nt + 1) = 1 + k2 * (nt + 1) := Int.ofNat_inj.mp h
  have : k1 * (nt + 1) = k2 * (nt + 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos nt) this

theorem rlBitInt_ne_flagInt {nt : ℕ} (k k' : ℕ) (i : Fin nt) :
    ((1 + k * (nt + 1) + 1 + i.val : ℕ) : Int) ≠ rlFlagInt nt k' := by
  intro h
  have hN : 1 + k * (nt + 1) + 1 + i.val = 1 + k' * (nt + 1) :=
    Int.ofNat_inj.mp h
  have heq : k * (nt + 1) + (1 + i.val) = k' * (nt + 1) := by omega
  have hi : 1 + i.val < nt + 1 := by omega
  rcases Nat.lt_trichotomy k k' with hlt | heq' | hgt
  · have hle : k * (nt + 1) ≤ k' * (nt + 1) :=
      Nat.mul_le_mul_right (nt + 1) (Nat.le_of_lt hlt)
    have hdiff : 1 + i.val = k' * (nt + 1) - k * (nt + 1) := by omega
    have hdist :
        k' * (nt + 1) - k * (nt + 1) = (k' - k) * (nt + 1) :=
      (Nat.mul_sub_right_distrib k' k (nt + 1)).symm
    rw [hdist] at hdiff
    have hpos : 1 ≤ k' - k := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
    have hge : nt + 1 ≤ (k' - k) * (nt + 1) :=
      Nat.le_mul_of_pos_left (nt + 1) hpos
    exact Nat.lt_irrefl _ (hdiff ▸ lt_of_lt_of_le hi hge)
  · subst heq'
    omega
  · have : k' * (nt + 1) ≤ k * (nt + 1) :=
      Nat.mul_le_mul_right (nt + 1) (Nat.le_of_lt hgt)
    omega

def rlUpdatedTape (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) : ℕ → Int → Phys
  | 0 => windowTape u exterior
  | r + 1 =>
      Function.update (rlUpdatedTape u a hleft exterior r)
        (rlFlagInt nt (u.cells.length - 1 - r))
        (tapeOfBit (decide
          (u.cells.length - 1 - r = (rlWindow u a hleft).head.val)))

theorem rlUpdatedTape_zero (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    rlUpdatedTape u a hleft exterior 0 = windowTape u exterior := rfl

theorem rlUpdatedTape_succ (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) :
    rlUpdatedTape u a hleft exterior (r + 1) =
      Function.update (rlUpdatedTape u a hleft exterior r)
        (rlFlagInt nt (u.cells.length - 1 - r))
        (tapeOfBit (decide
          (u.cells.length - 1 - r = (rlWindow u a hleft).head.val))) :=
  rfl

theorem rlUpdatedTape_preserve (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length) (z : Int)
    (hz : ∀ j : ℕ, j < r → z ≠ rlFlagInt nt (u.cells.length - 1 - j)) :
    rlUpdatedTape u a hleft exterior r z = windowTape u exterior z := by
  induction r generalizing z with
  | zero => rfl
  | succ r ih =>
      rw [rlUpdatedTape_succ]
      have hne := hz r (Nat.lt_succ_self r)
      rw [Function.update_of_ne hne]
      exact ih (Nat.le_of_succ_le hr) z
        (fun j hj => hz j (Nat.lt_succ_of_lt hj))

theorem rlUpdatedTape_at_flag (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length)
    (k : Fin u.cells.length) (hk : u.cells.length - r ≤ k.val) :
    rlUpdatedTape u a hleft exterior r (rlFlagInt nt k.val) =
      tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)) := by
  induction r generalizing k with
  | zero =>
      have : u.cells.length ≤ k.val := by simpa using hk
      have : k.val < u.cells.length := k.isLt
      omega
  | succ r ih =>
      rw [rlUpdatedTape_succ]
      by_cases hkeq : k.val = u.cells.length - 1 - r
      · have hcoord : rlFlagInt nt k.val = rlFlagInt nt (u.cells.length - 1 - r) := by
          simp [rlFlagInt, hkeq]
        have hup :
            Function.update (rlUpdatedTape u a hleft exterior r)
              (rlFlagInt nt (u.cells.length - 1 - r))
              (tapeOfBit (decide
                (u.cells.length - 1 - r = (rlWindow u a hleft).head.val)))
              (rlFlagInt nt (u.cells.length - 1 - r)) =
            tapeOfBit (decide
              (u.cells.length - 1 - r = (rlWindow u a hleft).head.val)) := by
          simp [Function.update]
        rw [hcoord, hup, hkeq]
      · have hk' : u.cells.length - r ≤ k.val := by omega
        have hne : rlFlagInt nt k.val ≠
            rlFlagInt nt (u.cells.length - 1 - r) := by
          intro h
          exact hkeq (rlFlagInt_inj h)
        rw [Function.update_of_ne hne]
        exact ih (Nat.le_of_succ_le hr) k hk'

theorem rlUpdatedTape_bit (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length)
    (k : Fin u.cells.length) (i : Fin nt) :
    rlUpdatedTape u a hleft exterior r
        ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) =
      windowTape u exterior
        ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) := by
  refine rlUpdatedTape_preserve u a hleft exterior r hr _ ?_
  intro j hj heq
  exact rlBitInt_ne_flagInt k.val (u.cells.length - 1 - j) i heq

theorem windowTape_eq_off_flags (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (z : Int)
    (hz : ∀ k : Fin u.cells.length, z ≠ rlFlagInt nt k.val) :
    windowTape u exterior z =
      windowTape (rlWindow u a hleft) exterior z := by
  have hW : windowWidth (rlWindow u a hleft) = windowWidth u :=
    rlWindow_windowWidth u a hleft
  by_cases hneg : z < 0
  · rw [windowTape_exterior u exterior z (Or.inl hneg),
      windowTape_exterior (rlWindow u a hleft) exterior z (Or.inl hneg)]
  · by_cases hbig : (windowWidth u + 1 : Int) < z
    · have hbig' : (windowWidth (rlWindow u a hleft) + 1 : Int) < z := by
        simpa [hW] using hbig
      rw [windowTape_exterior u exterior z (Or.inr hbig),
        windowTape_exterior (rlWindow u a hleft) exterior z (Or.inr hbig')]
    · have hnn : 0 ≤ z := le_of_not_gt hneg
      have hle : z ≤ (windowWidth u + 1 : Int) := le_of_not_gt hbig
      have hzNat : z = (z.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
      have hi : z.toNat ≤ windowWidth u + 1 := by
        have h := Int.toNat_le_toNat hle
        simpa using h
      set i := z.toNat with hi_def
      rw [hzNat]
      by_cases h0 : i = 0
      · have hz0 : ((0 : ℕ) : Int) = (0 : Int) := rfl
        rw [h0, hz0, windowTape_left, windowTape_left]
      · by_cases hlast : i = windowWidth u + 1
        · have hzW : (i : Int) = (windowWidth u + 1 : Int) := by
            simp [hlast]
          rw [hzW, windowTape_right]
          have hzW' :
              (windowWidth (rlWindow u a hleft) + 1 : Int) =
                (windowWidth u + 1 : Int) := by
            simp [hW]
          rw [← hzW', windowTape_right]
        · have hi1 : 1 ≤ i := by omega
          have hiW : i ≤ windowWidth u := by omega
          have hj : i - 1 < windowWidth u := by omega
          have hj' : i - 1 < windowWidth (rlWindow u a hleft) := by
            simpa [hW] using hj
          have hpos : (i : Int) = ((i - 1 : ℕ) : Int) + 1 := by
            have hi' : 0 < i := hi1
            have hcast : ((i - 1 : ℕ) : Int) + 1 = ((i - 1 + 1 : ℕ) : Int) := by
              simp [Nat.cast_add, Nat.cast_one]
            have hi'' : i - 1 + 1 = i := Nat.sub_add_cancel hi1
            rw [hcast, hi'']
          rw [hpos, windowTape_encode u exterior (i - 1) hj,
            windowTape_encode (rlWindow u a hleft) exterior (i - 1) hj']
          let k := (i - 1) / (nt + 1)
          let rmod := (i - 1) % (nt + 1)
          have hdiv0 : (nt + 1) * k + rmod = i - 1 :=
            Nat.div_add_mod (i - 1) (nt + 1)
          have hdiv : k * (nt + 1) + rmod = i - 1 := by
            rw [Nat.mul_comm]; exact hdiv0
          have hr : rmod < nt + 1 := Nat.mod_lt (i - 1) (Nat.succ_pos _)
          have hk : k < u.cells.length := by
            have hjW : i - 1 < u.cells.length * (nt + 1) := by
              rw [← windowWidth_eq]; exact hj
            have hkm : k * (nt + 1) < u.cells.length * (nt + 1) := by
              have : k * (nt + 1) ≤ i - 1 := by
                have hle := Nat.div_mul_le_self (i - 1) (nt + 1)
                simpa [Nat.mul_comm, k] using hle
              exact lt_of_le_of_lt this hjW
            exact Nat.lt_of_mul_lt_mul_right hkm
          rcases Nat.eq_zero_or_pos rmod with hr0 | hrpos
          · have hi_eq : i = 1 + k * (nt + 1) := by omega
            have hflag : z = rlFlagInt nt k := by
              rw [hzNat, hi_eq]
              rfl
            exact (hz ⟨k, hk⟩ hflag).elim
          · have hjbit : rmod - 1 < nt := by omega
            have hidx : k * (nt + 1) + 1 + (rmod - 1) = i - 1 := by omega
            have hu := encode_cell_bit u ⟨k, hk⟩ ⟨rmod - 1, hjbit⟩
            have hrl := encode_cell_bit (rlWindow u a hleft)
              ⟨k, by simpa using hk⟩ ⟨rmod - 1, hjbit⟩
            simp_rw [hidx] at hu hrl
            rw [hu, hrl]
            simp [rlWindow, List.get_eq_getElem]

theorem rlUpdatedTape_all (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    rlUpdatedTape u a hleft exterior u.cells.length =
      windowTape (rlWindow u a hleft) exterior := by
  funext z
  by_cases hflag : ∃ k : Fin u.cells.length, z = rlFlagInt nt k.val
  · obtain ⟨k, hkz⟩ := hflag
    rw [hkz, rlUpdatedTape_at_flag u a hleft exterior u.cells.length le_rfl k
      (by simp)]
    have hklen : k.val < (rlWindow u a hleft).cells.length := by
      simpa using k.isLt
    have h := windowTape_cell_flag (rlWindow u a hleft) exterior ⟨k.val, hklen⟩
    simpa [rlFlagInt] using h.symm
  · have hz : ∀ k : Fin u.cells.length, z ≠ rlFlagInt nt k.val := by
      intro k hk; exact hflag ⟨k, hk⟩
    have hpres : ∀ j : ℕ, j < u.cells.length →
        z ≠ rlFlagInt nt (u.cells.length - 1 - j) := by
      intro j hj heq
      have kj : u.cells.length - 1 - j < u.cells.length := by omega
      exact hz ⟨u.cells.length - 1 - j, kj⟩ heq
    rw [rlUpdatedTape_preserve u a hleft exterior u.cells.length le_rfl z hpres]
    exact windowTape_eq_off_flags u a hleft exterior z hz

/-! ## Chronological reverse-cell arrows -/

theorem cellBits_ne_blank (w : LogicalWindow nt) (k : Fin w.cells.length) :
    ∀ y ∈ cellBits w k, y ≠ ULogSourceOneHotReader.blank := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨b, _, rfl⟩
  exact tapeOfBit_ne_blank b

def rlCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (k : Fin u.cells.length) : List (ScanArrow p hnt blank) :=
  cellArrows p hnt blank a (rlArmed u a k.val)
    (tapeOfBit (decide (k.val = u.head.val)))
    (tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)))
    (decide (a.move = .left ∧ k.val = u.head.val))
    (updateRL_window_cell u a hleft k)
    (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
    (cellBits_ne_blank u k)

@[simp] theorem rlCellArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (k : Fin u.cells.length) :
    (rlCellArrows p hnt blank a u hleft k).length = nt + 1 := by
  simp [rlCellArrows]

def rlInteriorArrowsTake (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (r : ℕ) (hr : r ≤ u.cells.length) : List (ScanArrow p hnt blank) :=
  (List.ofFn fun j : Fin r =>
    rlCellArrows p hnt blank a u hleft
      ⟨u.cells.length - 1 - j.val, by omega⟩).flatten

def rlInteriorArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    List (ScanArrow p hnt blank) :=
  rlInteriorArrowsTake p hnt blank a u hleft u.cells.length le_rfl

def rlWindowArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    List (ScanArrow p hnt blank) :=
  rlInteriorArrows p hnt blank a u hleft ++
    [skipRLLeftBoundaryArrow p hnt blank a]

theorem rlInteriorArrowsTake_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (r : ℕ) (hr : r ≤ u.cells.length) :
    (rlInteriorArrowsTake p hnt blank a u hleft r hr).length =
      r * (nt + 1) := by
  unfold rlInteriorArrowsTake
  rw [List.length_flatten, List.map_ofFn]
  have hrep :
      (List.ofFn (List.length ∘ fun j : Fin r =>
        rlCellArrows p hnt blank a u hleft
          ⟨u.cells.length - 1 - j.val, by omega⟩)) =
        List.replicate r (nt + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp [Function.comp, rlCellArrows_length]
  rw [hrep, sum_replicate_nat]

theorem rlInteriorArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    (rlInteriorArrows p hnt blank a u hleft).length = windowWidth u := by
  simp [rlInteriorArrows, rlInteriorArrowsTake_length, windowWidth]

theorem rlWindowArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    (rlWindowArrows p hnt blank a u hleft).length = windowWidth u + 1 := by
  simp [rlWindowArrows, rlInteriorArrows_length]

theorem rlInteriorArrowsTake_succ (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (r : ℕ) (hr : r < u.cells.length) :
    rlInteriorArrowsTake p hnt blank a u hleft (r + 1) (Nat.succ_le_of_lt hr) =
      rlInteriorArrowsTake p hnt blank a u hleft r (Nat.le_of_lt hr) ++
        rlCellArrows p hnt blank a u hleft
          ⟨u.cells.length - 1 - r, by omega⟩ := by
  unfold rlInteriorArrowsTake
  rw [ofFn_snoc]
  simp [List.flatten_append]

/-! ## Cell-boundary configurations -/

def rlStart (hnt : 0 < nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (exterior : Int → Phys) : ScanCfg ns nt :=
  { state := .skipRL a false ⟨nt - 1, by omega⟩
    head := (windowWidth u : Int)
    tape := windowTape u exterior }

def rlMid (hnt : 0 < nt) (u : LogicalWindow nt) (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (_hr : r ≤ u.cells.length) :
    ScanCfg ns nt :=
  { state := .skipRL a
      (decide (a.move = .left ∧ u.cells.length - r = u.head.val))
      ⟨nt - 1, by omega⟩
    head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
    tape := rlUpdatedTape u a hleft exterior r }

theorem rlMid_zero (hnt : 0 < nt) (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    rlMid hnt u a hleft exterior 0 (Nat.zero_le _) =
      rlStart hnt a u exterior := by
  apply cfg_ext
  · simp only [rlMid, rlStart]
    rw [rlCarry_zero]
  · have hhead :
        ((u.cells.length * (nt + 1) : ℕ) : Int) = (windowWidth u : Int) := by
      simp [windowWidth]
    simpa [rlMid, rlStart] using hhead
  · simp [rlMid, rlStart, rlUpdatedTape_zero]

theorem rl_base_head (nt k : ℕ) :
    ((2 + k * (nt + 1) : ℕ) : Int) + (nt : Int) - 1 =
      (((k + 1) * (nt + 1) : ℕ) : Int) := by
  have h1 : ((2 + k * (nt + 1) : ℕ) : Int) + (nt : Int) =
      ((2 + k * (nt + 1) + nt : ℕ) : Int) := by
    simp [Nat.cast_add]
  rw [h1]
  have h2 : 2 + k * (nt + 1) + nt = (k + 1) * (nt + 1) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [h2, Nat.cast_add, Nat.cast_one]
  omega

theorem rl_base_flag (nt k : ℕ) :
    ((2 + k * (nt + 1) : ℕ) : Int) - 1 = rlFlagInt nt k := by
  have : 2 + k * (nt + 1) = 1 + k * (nt + 1) + 1 := by omega
  rw [this, Nat.cast_add, Nat.cast_one]
  simp [rlFlagInt]

theorem rl_base_end (nt k : ℕ) :
    ((2 + k * (nt + 1) : ℕ) : Int) - 2 =
      ((k * (nt + 1) : ℕ) : Int) := by
  have : 2 + k * (nt + 1) = k * (nt + 1) + 2 := by omega
  rw [this, Nat.cast_add]
  omega

theorem rl_base_bit (nt k : ℕ) (i : Fin nt) :
    ((2 + k * (nt + 1) : ℕ) : Int) + (i.val : Int) =
      ((1 + k * (nt + 1) + 1 + i.val : ℕ) : Int) := by
  have : 2 + k * (nt + 1) = 1 + k * (nt + 1) + 1 := by omega
  rw [this]
  simp [Nat.cast_add, Nat.cast_one]

theorem rlMid_read_flag (hnt : 0 < nt) (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r < u.cells.length) :
    (rlMid hnt u a hleft exterior r (Nat.le_of_lt hr)).tape
      (rlFlagInt nt (u.cells.length - 1 - r)) =
      tapeOfBit (decide (u.cells.length - 1 - r = u.head.val)) := by
  let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
  have hpres :
      ∀ j : ℕ, j < r → rlFlagInt nt k.val ≠
        rlFlagInt nt (u.cells.length - 1 - j) := by
    intro j hj heq
    have : k.val = u.cells.length - 1 - j := rlFlagInt_inj heq
    simp [k] at this
    omega
  have ht :=
    rlUpdatedTape_preserve u a hleft exterior r (Nat.le_of_lt hr)
      (rlFlagInt nt k.val) hpres
  simp only [rlMid]
  rw [ht]
  simpa [rlFlagInt, k] using windowTape_cell_flag u exterior k

theorem rlMid_read_bits (hnt : 0 < nt) (u : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r < u.cells.length) :
    ∀ i : Fin nt,
      (rlMid hnt u a hleft exterior r (Nat.le_of_lt hr)).tape
        (((2 + (u.cells.length - 1 - r) * (nt + 1) : ℕ) : Int) +
          (i.val : Int)) =
        (cellBits u ⟨u.cells.length - 1 - r, by omega⟩).get
          ⟨i.val, by simp [cellBits, encodeOneHot_length]⟩ := by
  intro i
  let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
  simp only [rlMid]
  rw [rl_base_bit nt k.val i,
    rlUpdatedTape_bit u a hleft exterior r (Nat.le_of_lt hr) k i]
  simpa [cellBits, List.get_eq_getElem, List.getElem_map, k] using
    windowTape_cell_bit u exterior k i

/-! ## Interior induction -/

theorem rl_take_cells (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys)
    (r : ℕ) (hr : r ≤ u.cells.length) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (rlInteriorArrowsTake p hnt blank a u hleft r hr)
      (rlStart hnt a u exterior) =
      some (rlMid hnt u a hleft exterior r hr) := by
  induction r with
  | zero =>
      simp [rlInteriorArrowsTake, FiniteOneTapeSemantics.run_nil]
      exact (rlMid_zero hnt u a hleft exterior).symm
  | succ r ih =>
      have hr' : r < u.cells.length := by omega
      have hle : r ≤ u.cells.length := Nat.le_of_lt hr'
      rw [rlInteriorArrowsTake_succ p hnt blank a u hleft r hr',
        run_append p hnt blank, ih hle]
      simp only [Option.bind_some]
      let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
      have hrun :=
        cell_run p hnt blank a (rlArmed u a k.val)
          (tapeOfBit (decide (k.val = u.head.val)))
          (tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)))
          (decide (a.move = .left ∧ k.val = u.head.val))
          (updateRL_window_cell u a hleft k)
          (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
          (cellBits_ne_blank u k)
          (rlMid hnt u a hleft exterior r hle)
          (by
            simp [rlMid, k, rlCarry_eq_rlArmed u a r hr'])
          ((2 + k.val * (nt + 1) : ℕ) : Int)
          (by
            simp only [rlMid]
            have hidx : u.cells.length - r = k.val + 1 := by
              change u.cells.length - r = u.cells.length - 1 - r + 1
              omega
            have hhead := rl_base_head nt k.val
            rw [hidx]
            exact hhead.symm)
          (by
            intro i
            simpa [k] using rlMid_read_bits hnt u a hleft exterior r hr' i)
          (by
            have hf := rlMid_read_flag hnt u a hleft exterior r hr'
            have hcoord := (rl_base_flag nt k.val).symm
            simpa [k, hcoord] using hf)
      have harrows :
          rlCellArrows p hnt blank a u hleft k =
            cellArrows p hnt blank a (rlArmed u a k.val)
              (tapeOfBit (decide (k.val = u.head.val)))
              (tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)))
              (decide (a.move = .left ∧ k.val = u.head.val))
              (updateRL_window_cell u a hleft k)
              (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
              (cellBits_ne_blank u k) :=
        rfl
      rw [harrows, hrun]
      apply congrArg some
      apply cfg_ext
      · simp [rlMid, k, rlCarry_succ_eq_out u a r hr']
      · simp only [rlMid]
        have hidx : u.cells.length - (r + 1) = k.val := by
          change u.cells.length - (r + 1) = u.cells.length - 1 - r
          omega
        have hend := rl_base_end nt k.val
        rw [hidx]
        exact hend
      · have hp : ((2 + k.val * (nt + 1) : ℕ) : Int) - 1 =
            rlFlagInt nt (u.cells.length - 1 - r) := by
          simpa [k] using rl_base_flag nt k.val
        simp only [rlMid]
        rw [rlUpdatedTape_succ, hp]

theorem rl_interior_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (rlInteriorArrows p hnt blank a u hleft)
      (rlStart hnt a u exterior) =
      some {
        state := .skipRL a false ⟨nt - 1, by omega⟩
        head := (0 : Int)
        tape := windowTape (rlWindow u a hleft) exterior } := by
  unfold rlInteriorArrows
  apply Eq.trans (rl_take_cells p hnt blank a u hleft exterior
    u.cells.length le_rfl)
  apply congrArg some
  apply cfg_ext
  · simp only [rlMid]
    rw [rlCarry_all u a hleft]
  · simp [rlMid]
  · exact rlUpdatedTape_all u a hleft exterior

theorem rl_window_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (rlWindowArrows p hnt blank a u hleft)
      (rlStart hnt a u exterior) =
      some {
        state := .atLeft a.target
        head := (0 : Int)
        tape := windowTape (rlWindow u a hleft) exterior } := by
  rw [rlWindowArrows, run_append p hnt blank, rl_interior_run]
  simp only [Option.bind_some, FiniteOneTapeSemantics.run_cons,
    FiniteOneTapeSemantics.run_nil]
  have hstep :=
    skipRLLeftBoundaryArrow_step p hnt blank a
      { state := .skipRL a false ⟨nt - 1, by omega⟩
        head := (0 : Int)
        tape := windowTape (rlWindow u a hleft) exterior }
      rfl
      (windowTape_left (rlWindow u a hleft) exterior)
  rw [hstep]
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl

theorem rl_pre_boundary (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (rlInteriorArrows p hnt blank a u hleft)
      (rlStart hnt a u exterior) =
      some {
        state := .skipRL a false ⟨nt - 1, by omega⟩
        head := (0 : Int)
        tape := windowTape (rlWindow u a hleft) exterior } :=
  rl_interior_run p hnt blank a u hleft exterior

theorem rl_cell_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys)
    (r : ℕ) (hr : r ≤ u.cells.length) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (rlInteriorArrowsTake p hnt blank a u hleft r hr)
        (rlStart hnt a u exterior) = some c' ∧
      c'.state = .skipRL a
        (decide (a.move = .left ∧ u.cells.length - r = u.head.val))
        ⟨nt - 1, by omega⟩ ∧
      c'.head = (((u.cells.length - r) * (nt + 1) : ℕ) : Int) ∧
      c'.tape = rlUpdatedTape u a hleft exterior r := by
  refine ⟨rlMid hnt u a hleft exterior r hr, ?_, rfl, rfl, rfl⟩
  exact rl_take_cells p hnt blank a u hleft exterior r hr

theorem rl_window_block (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (rlWindowArrows p hnt blank a u hleft)
        (rlStart hnt a u exterior) = some c' ∧
      c'.state = .atLeft a.target ∧
      c'.head = (0 : Int) ∧
      c'.tape = windowTape (rlWindow u a hleft) exterior ∧
      (rlWindowArrows p hnt blank a u hleft).length = windowWidth u + 1 ∧
      (rlInteriorArrows p hnt blank a u hleft).length = windowWidth u := by
  refine ⟨{ state := .atLeft a.target
            head := (0 : Int)
            tape := windowTape (rlWindow u a hleft) exterior },
    ?_, rfl, rfl, rfl, rlWindowArrows_length p hnt blank a u hleft,
    rlInteriorArrows_length p hnt blank a u hleft⟩
  exact rl_window_run p hnt blank a u hleft exterior

end PakFixedPolyomino.ULogSourceObliviousRLWindowExecution
