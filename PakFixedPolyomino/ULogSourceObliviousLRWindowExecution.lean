import PakFixedPolyomino.ULogSourceObliviousLRCellExecution
import Mathlib.Tactic

/-!
# Literal complete left-to-right window of the finite oblivious scanner

From `.updateLRFlag a false` at coordinate `1` on `windowTape w`, the
chronological concatenation of every cell's flag arrow and `skipLRArrows`
block, followed by `updateLRFlagRightBoundaryArrow`, has length `W+1` and
ends at `.skipRL a false ⟨nt-1⟩` at coordinate `W` on
`windowTape (lrWindow w a hright)`.  Armed bits and flag writes are derived
from the unique original mark.  This is the LR intermediate window, not an
RL pass and not the original Pak theorem.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLRWindowExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceOneHotBlocks
open ULogSourceObliviousWindow
open ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution
open ULogSourceObliviousLRBlockExecution
open ULogSourceObliviousLRCellExecution

variable {ns nt : ℕ}

theorem cfg_ext (c₁ c₂ : ScanCfg ns nt)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-! ## Intermediate LogicalWindow after the LR pass -/

def lrWindow (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    LogicalWindow nt :=
  { cells := w.cells.set w.head a.write
    head :=
      if h : a.move = .right then
        ⟨w.head.val + 1, by
          have hlen : (w.cells.set w.head a.write).length = w.cells.length := by
            simp
          have := hright h
          simpa [hlen] using this⟩
      else
        ⟨w.head.val, by simp⟩ }

@[simp] theorem lrWindow_cells_length (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    (lrWindow w a hright).cells.length = w.cells.length := by
  simp [lrWindow]

theorem lrWindow_windowWidth (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    windowWidth (lrWindow w a hright) = windowWidth w := by
  simp [windowWidth, lrWindow]

theorem lrWindow_head_right (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hmove : a.move = .right) :
    (lrWindow w a hright).head.val = w.head.val + 1 := by
  simp [lrWindow, hmove]

theorem lrWindow_head_not_right (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hmove : a.move ≠ .right) :
    (lrWindow w a hright).head.val = w.head.val := by
  simp [lrWindow, hmove]

theorem lrArmed_zero (w : LogicalWindow nt) (a : BoundedAction ns nt) :
    lrArmed w a 0 = false := by
  simp [lrArmed]

theorem lrArmed_length (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    lrArmed w a w.cells.length = false := by
  by_cases hmove : a.move = .right
  · have := hright hmove
    simp [lrArmed, hmove]
    omega
  · simp [lrArmed, hmove]

/-! ## Encode block access -/

theorem ofFn_snoc {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) :
    List.ofFn f =
      List.ofFn (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ++
        [f ⟨n, Nat.lt_succ_self n⟩] := by
  refine List.ext_getElem (by simp) ?_
  intro i hi hi2
  by_cases h : i < n
  · have hlen :
        i < (List.ofFn (fun i : Fin n =>
          f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).length := by
      simpa [List.length_ofFn]
    have hcomb : i < (List.ofFn (fun i : Fin n =>
        f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ++
        [f ⟨n, Nat.lt_succ_self n⟩]).length := hi2
    rw [List.getElem_append_left (as := List.ofFn (fun i : Fin n =>
        f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (bs := [f ⟨n, Nat.lt_succ_self n⟩]) hlen (h' := hcomb)]
    simp only [List.getElem_ofFn]
  · have hi' : i < n + 1 := by simpa [List.length_ofFn] using hi
    have hi_eq : i = n := Nat.eq_of_lt_succ_of_not_lt hi' h
    subst i
    have hge :
        (List.ofFn (fun i : Fin n =>
          f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).length ≤ n := by
      simp [List.length_ofFn]
    rw [List.getElem_append_right
      (as := List.ofFn (fun i : Fin n =>
        f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (bs := [f ⟨n, Nat.lt_succ_self n⟩]) (i := n) hge (h₂ := hi2)]
    simp only [List.length_ofFn, Nat.sub_self]
    have hL : (List.ofFn f)[n] = f ⟨n, hi'⟩ := by
      simp only [List.getElem_ofFn]
    exact hL.trans rfl.symm

theorem mul_add_lt_mul {k n m j : ℕ} (hk : k < n) (hj : j < m) :
    k * m + j < n * m := by
  have h1 : k * m + j < (k + 1) * m := by
    have : k * m + j < k * m + m := Nat.add_lt_add_left hj _
    simpa [Nat.succ_mul] using this
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right m (Nat.succ_le_of_lt hk))

theorem append_left_get {α : Type*} (as bs : List α) (i : ℕ)
    (hi : i < as.length) :
    (as ++ bs)[i]'(by simp; omega) = as[i] :=
  List.getElem_append_left hi (h' := by simp; omega)

theorem append_right_get {α : Type*} (as bs : List α) (i : ℕ)
    (hge : as.length ≤ i) (hi : i < (as ++ bs).length) :
    (as ++ bs)[i] =
      bs[i - as.length]'(by simp at hi ⊢; omega) :=
  List.getElem_append_right (as := as) (bs := bs) (i := i) hge (h₂ := hi)

theorem encodeWindow_get_block {nt' : ℕ} (cells : List (MarkedCell nt'))
    (k : ℕ) (hk : k < cells.length) (j : ℕ) (hj : j < nt' + 1) :
    (encodeWindow cells)[k * (nt' + 1) + j]'(by
      simp only [encodeWindow_length]
      exact mul_add_lt_mul hk hj) =
      (encodeMarkedCell (cells.get ⟨k, hk⟩))[j]'(by
        simp [encodeMarkedCell_length]; omega) := by
  have hsplit (c : MarkedCell nt') (cs : List (MarkedCell nt')) :
      encodeWindow (c :: cs) = encodeMarkedCell c ++ encodeWindow cs := by
    simp [encodeWindow]
  induction cells generalizing k with
  | nil => cases hk
  | cons c cs ih =>
      cases k with
      | zero =>
          have hlen : j < (encodeMarkedCell c).length := by
            simpa [encodeMarkedCell_length] using hj
          have hget := append_left_get (encodeMarkedCell c) (encodeWindow cs) j hlen
          simpa [hsplit, List.get_cons_zero] using hget
      | succ k =>
          have hk' : k < cs.length := by
            have : k + 1 < cs.length + 1 := by simpa using hk
            omega
          have hlenC : (encodeMarkedCell c).length = nt' + 1 :=
            encodeMarkedCell_length c
          have hge : (encodeMarkedCell c).length ≤ (k + 1) * (nt' + 1) + j := by
            rw [hlenC]
            have : nt' + 1 ≤ (k + 1) * (nt' + 1) :=
              Nat.le_mul_of_pos_left (nt' + 1) (Nat.succ_pos k)
            exact Nat.le_trans this (Nat.le_add_right _ _)
          have hidx :
              (k + 1) * (nt' + 1) + j <
                (encodeMarkedCell c ++ encodeWindow cs).length := by
            have : (k + 1) * (nt' + 1) + j <
                (cs.length + 1) * (nt' + 1) := mul_add_lt_mul hk hj
            have hlen :
                (encodeMarkedCell c ++ encodeWindow cs).length =
                  (cs.length + 1) * (nt' + 1) := by
              simp [List.length_append, encodeWindow_length, hlenC]
              rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
            simpa [hlen] using this
          have hget := append_right_get (encodeMarkedCell c) (encodeWindow cs)
            ((k + 1) * (nt' + 1) + j) hge hidx
          have hsub :
              (k + 1) * (nt' + 1) + j - (encodeMarkedCell c).length =
                k * (nt' + 1) + j := by
            rw [hlenC, Nat.succ_mul]
            omega
          simp_rw [hsub] at hget
          simpa [hsplit, List.get_cons_succ] using hget.trans (ih k hk')

theorem encode_cell_flag (w : LogicalWindow nt) (k : Fin w.cells.length) :
    w.encode[k.val * (nt + 1)]'(by
      simp only [LogicalWindow.encode_length]
      exact mul_add_lt_mul k.isLt (Nat.succ_pos nt)) =
      tapeOfBit (decide (k.val = w.head.val)) := by
  have h := encodeWindow_get_block w.markedCells k.val
    (by simpa using k.isLt) 0 (Nat.succ_pos _)
  simp_rw [Nat.add_zero] at h
  have hhead := LogicalWindow.markedCells_get_head w k
  have hget :
      (encodeMarkedCell
        (w.markedCells.get ⟨k.val, by simpa using k.isLt⟩))[0]'(by
          simp [encodeMarkedCell_length]) =
        tapeOfBit
          (w.markedCells.get ⟨k.val, by simpa using k.isLt⟩).head := by
    simp [encodeMarkedCell]
  change (encodeWindow w.markedCells)[k.val * (nt + 1)] = _
  exact h.trans (hget.trans (by rw [hhead]))

theorem encode_cell_bit (w : LogicalWindow nt)
    (k : Fin w.cells.length) (i : Fin nt) :
    w.encode[k.val * (nt + 1) + 1 + i.val]'(by
      simp only [LogicalWindow.encode_length]
      have hj : 1 + i.val < nt + 1 := by omega
      have : k.val * (nt + 1) + 1 + i.val =
          k.val * (nt + 1) + (1 + i.val) := by omega
      rw [this]
      exact mul_add_lt_mul k.isLt hj) =
      tapeOfBit ((encodeOneHot (w.cells.get k)).get
        ⟨i.val, by simp [encodeOneHot_length]⟩) := by
  have h := encodeWindow_get_block w.markedCells k.val
    (by simpa using k.isLt) (1 + i.val) (by omega)
  have hidx : k.val * (nt + 1) + (1 + i.val) =
      k.val * (nt + 1) + 1 + i.val := by omega
  simp_rw [hidx] at h
  have hsym := LogicalWindow.markedCells_get_symbol w k
  have hget :
      (encodeMarkedCell
        (w.markedCells.get ⟨k.val, by simpa using k.isLt⟩))[1 + i.val]'(by
          simp [encodeMarkedCell_length]; omega) =
        tapeOfBit ((encodeOneHot
          (w.markedCells.get ⟨k.val, by simpa using k.isLt⟩).symbol).get
            ⟨i.val, by simp [encodeOneHot_length]⟩) := by
    simp only [encodeMarkedCell]
    simp_rw [Nat.add_comm 1 i.val]
    simp [List.getElem_cons_succ, List.get_eq_getElem, List.getElem_map]
  unfold LogicalWindow.encode
  refine h.trans (hget.trans ?_)
  simp [List.get_eq_getElem] at hsym ⊢
  simp [hsym]

theorem windowTape_cell_flag (w : LogicalWindow nt)
    (exterior : Int → Phys) (k : Fin w.cells.length) :
    windowTape w exterior ((1 + k.val * (nt + 1) : ℕ) : Int) =
      tapeOfBit (decide (k.val = w.head.val)) := by
  have hi : k.val * (nt + 1) < windowWidth w := by
    simp only [windowWidth, LogicalWindow.encode_length]
    exact mul_add_lt_mul k.isLt (Nat.succ_pos nt)
  have hcast :
      ((1 + k.val * (nt + 1) : ℕ) : Int) =
        ((k.val * (nt + 1) : ℕ) : Int) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, add_comm]
  rw [hcast, windowTape_encode w exterior (k.val * (nt + 1)) hi]
  exact encode_cell_flag w k

theorem windowTape_cell_bit (w : LogicalWindow nt)
    (exterior : Int → Phys) (k : Fin w.cells.length) (i : Fin nt) :
    windowTape w exterior ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) =
      tapeOfBit ((encodeOneHot (w.cells.get k)).get
        ⟨i.val, by simp [encodeOneHot_length]⟩) := by
  have hi : k.val * (nt + 1) + 1 + i.val < windowWidth w := by
    simp only [windowWidth, LogicalWindow.encode_length]
    have hj : 1 + i.val < nt + 1 := by omega
    have : k.val * (nt + 1) + 1 + i.val =
        k.val * (nt + 1) + (1 + i.val) := by omega
    rw [this]
    exact mul_add_lt_mul k.isLt hj
  have hnat :
      1 + k.val * (nt + 1) + 1 + i.val =
        k.val * (nt + 1) + 1 + i.val + 1 := by
    omega
  have hcast :
      ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) =
        ((k.val * (nt + 1) + 1 + i.val : ℕ) : Int) + 1 := by
    rw [hnat, Nat.cast_add, Nat.cast_one]
  rw [hcast, windowTape_encode w exterior (k.val * (nt + 1) + 1 + i.val) hi]
  exact encode_cell_bit w k i

/-! ## Derived flag update at the unique original mark -/

theorem updateLR_window_cell (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    updateLR a (lrArmed w a k.val)
      (tapeOfBit (decide (k.val = w.head.val))) =
      some (tapeOfBit (decide (k.val = (lrWindow w a hright).head.val)),
        lrArmed w a (k.val + 1)) := by
  have hxvalid :
      validBit (tapeOfBit (decide (k.val = w.head.val))) = true :=
    validBit_tapeOfBit _
  unfold updateLR
  simp [hxvalid]
  by_cases hmove : a.move = .right
  · have hnew := lrWindow_head_right w a hright hmove
    simp only [lrArmed, hmove, decide_true, Bool.true_and, hnew]
    by_cases hk0 : k.val = w.head.val
    · have hk1 : k.val ≠ w.head.val + 1 := by omega
      simp [hk0, hk1, tapeOfBit, one, zero]
    · by_cases hk1 : k.val = w.head.val + 1
      · have : k.val ≠ w.head.val := by omega
        simp [hk1, this, tapeOfBit, one, zero]
      · simp [hk0, hk1, tapeOfBit, one, zero]
  · have hnew := lrWindow_head_not_right w a hright hmove
    simp [lrArmed, hmove, hnew]

/-! ## writeBlock concatenation -/

theorem writeBlock_append (tape : Int → Phys) (head : Int)
    (xs ys : List Phys) :
    writeBlock (writeBlock tape head xs) (head + (xs.length : Int)) ys =
      writeBlock tape head (xs ++ ys) := by
  induction ys using List.reverseRecOn with
  | nil =>
      simp [writeBlock_nil]
  | append_singleton ys y ih =>
      have hsnoc := writeBlock_snoc (writeBlock tape head xs)
        (head + (xs.length : Int)) ys y
      have hlen :
          (head + (xs.length : Int)) + (ys.length : Int) =
            head + ((xs ++ ys).length : Int) := by
        simp; omega
      rw [← hsnoc, ih, hlen]
      simpa using writeBlock_snoc tape head (xs ++ ys) y

/-! ## Processed-cell encodings -/

def lrCellEncode (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) : List Phys :=
  encodeMarkedCell ⟨
    (lrWindow w a hright).cells.get ⟨k.val, by
      simpa using k.isLt⟩,
    decide (k.val = (lrWindow w a hright).head.val)⟩

@[simp] theorem lrCellEncode_length (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    (lrCellEncode w a hright k).length = nt + 1 := by
  simp [lrCellEncode]

def lrPrefixEncode (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) : List Phys :=
  (List.ofFn fun j : Fin k =>
    lrCellEncode w a hright ⟨j.val, by omega⟩).flatten

theorem sum_replicate_nat (n a : ℕ) :
    (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

theorem lrPrefixEncode_length (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    (lrPrefixEncode w a hright k hk).length = k * (nt + 1) := by
  unfold lrPrefixEncode
  rw [List.length_flatten, List.map_ofFn]
  have hrep :
      (List.ofFn (List.length ∘ fun j : Fin k =>
        lrCellEncode w a hright ⟨j.val, by omega⟩)) =
        List.replicate k (nt + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp [Function.comp, lrCellEncode_length]
  rw [hrep, sum_replicate_nat]

theorem lrPrefixEncode_zero (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    lrPrefixEncode w a hright 0 (Nat.zero_le _) = [] := by
  simp [lrPrefixEncode]

theorem lrPrefixEncode_succ (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k < w.cells.length) :
    lrPrefixEncode w a hright (k + 1) (Nat.succ_le_of_lt hk) =
      lrPrefixEncode w a hright k (Nat.le_of_lt hk) ++
        lrCellEncode w a hright ⟨k, hk⟩ := by
  unfold lrPrefixEncode
  rw [ofFn_snoc]
  simp [List.flatten_append]

def lrPrefixTape (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ w.cells.length) :
    Int → Phys :=
  writeBlock (windowTape w exterior) 1 (lrPrefixEncode w a hright k hk)

theorem getElem_set_eq_ite {α : Type*} (l : List α) (i : ℕ) (a : α)
    (j : ℕ) (hj : j < (l.set i a).length) :
    (l.set i a)[j] = if i = j then a else l[j]'(by simpa using hj) := by
  induction l generalizing i j with
  | nil => cases hj
  | cons x xs ih =>
      match i, j with
      | 0, 0 => rfl
      | 0, Nat.succ j =>
          simp only [List.set]
          rw [if_neg (Nat.succ_ne_zero j).symm]
          rfl
      | Nat.succ i, 0 =>
          simp only [List.set]
          rw [if_neg (Nat.succ_ne_zero i)]
          rfl
      | Nat.succ i, Nat.succ j =>
          have hj' : j < (xs.set i a).length := by
            simpa [List.length_set] using hj
          simp only [List.set, List.getElem_cons_succ, Nat.succ.injEq]
          exact ih i j hj'

theorem lrWindow_symbol (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    (lrWindow w a hright).cells.get ⟨k.val, by simpa using k.isLt⟩ =
      if k.val = w.head.val then a.write else w.cells.get k := by
  simp only [lrWindow]
  rw [List.get_eq_getElem, List.get_eq_getElem]
  have hset := getElem_set_eq_ite w.cells w.head.val a.write k.val
    (by simpa using k.isLt)
  rw [hset]
  by_cases hk : w.head.val = k.val
  · rw [if_pos hk, if_pos hk.symm]
  · rw [if_neg hk, if_neg (Ne.symm hk)]

theorem outputBits_window (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    outputBits a (decide (k.val = w.head.val))
      ((encodeOneHot (w.cells.get k)).map tapeOfBit) =
      (encodeOneHot ((lrWindow w a hright).cells.get ⟨k.val, by
        simpa using k.isLt⟩)).map tapeOfBit := by
  have hsym := lrWindow_symbol w a hright k
  simp [List.get_eq_getElem] at hsym
  by_cases hk : k.val = w.head.val
  · simp [outputBits, hk]
    simp [hk] at hsym
    simp [hsym]
  · simp [outputBits, hk]
    simp [hk] at hsym
    simp [hsym]

/-! ## Chronological arrows -/

def cellBits (w : LogicalWindow nt) (k : Fin w.cells.length) : List Phys :=
  (encodeOneHot (w.cells.get k)).map tapeOfBit

theorem cellBits_length (w : LogicalWindow nt) (k : Fin w.cells.length) :
    (cellBits w k).length = nt := by
  simp [cellBits, encodeOneHot_length]

theorem cellBits_valid (w : LogicalWindow nt) (k : Fin w.cells.length) :
    ∀ y ∈ cellBits w k, validBit y = true := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨b, _, rfl⟩
  exact validBit_tapeOfBit b

def lrCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) : List (ScanArrow p hnt blank) :=
  cellArrows p hnt blank a (lrArmed w a k.val)
    (tapeOfBit (decide (k.val = w.head.val)))
    (tapeOfBit (decide (k.val = (lrWindow w a hright).head.val)))
    (lrArmed w a (k.val + 1))
    (tapeOfBit_ne_blank _)
    (updateLR_window_cell w a hright k)
    (cellBits w k) (cellBits_length w k) (cellBits_valid w k)

@[simp] theorem lrCellArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    (lrCellArrows p hnt blank a w hright k).length = nt + 1 := by
  simp [lrCellArrows]

def lrInteriorArrowsTake (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) : List (ScanArrow p hnt blank) :=
  (List.ofFn fun j : Fin k =>
    lrCellArrows p hnt blank a w hright ⟨j.val, by omega⟩).flatten

def lrInteriorArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    List (ScanArrow p hnt blank) :=
  lrInteriorArrowsTake p hnt blank a w hright w.cells.length le_rfl

def lrWindowArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    List (ScanArrow p hnt blank) :=
  lrInteriorArrows p hnt blank a w hright ++
    [updateLRFlagRightBoundaryArrow p hnt blank a]

theorem lrInteriorArrowsTake_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    (lrInteriorArrowsTake p hnt blank a w hright k hk).length =
      k * (nt + 1) := by
  unfold lrInteriorArrowsTake
  rw [List.length_flatten, List.map_ofFn]
  have hrep :
      (List.ofFn (List.length ∘ fun j : Fin k =>
        lrCellArrows p hnt blank a w hright ⟨j.val, by omega⟩)) =
        List.replicate k (nt + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp [Function.comp, lrCellArrows_length]
  rw [hrep, sum_replicate_nat]

theorem lrInteriorArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    (lrInteriorArrows p hnt blank a w hright).length = windowWidth w := by
  simp [lrInteriorArrows, lrInteriorArrowsTake_length, windowWidth]

theorem lrWindowArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    (lrWindowArrows p hnt blank a w hright).length = windowWidth w + 1 := by
  simp [lrWindowArrows, lrInteriorArrows_length]

theorem lrInteriorArrowsTake_succ (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k < w.cells.length) :
    lrInteriorArrowsTake p hnt blank a w hright (k + 1) (Nat.succ_le_of_lt hk) =
      lrInteriorArrowsTake p hnt blank a w hright k (Nat.le_of_lt hk) ++
        lrCellArrows p hnt blank a w hright ⟨k, hk⟩ := by
  unfold lrInteriorArrowsTake
  rw [ofFn_snoc]
  simp [List.flatten_append]

/-! ## Tape identity of a fully processed prefix -/

theorem encodeWindow_append {nt' : ℕ} (xs ys : List (MarkedCell nt')) :
    encodeWindow (xs ++ ys) = encodeWindow xs ++ encodeWindow ys := by
  simp [encodeWindow, List.flatMap_append]

theorem lrPrefixEncode_eq_take (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    lrPrefixEncode w a hright k hk =
      encodeWindow ((lrWindow w a hright).markedCells.take k) := by
  induction k with
  | zero =>
      simp [lrPrefixEncode, encodeWindow]
  | succ k ih =>
      have hk' : k < w.cells.length := by omega
      have hlen :
          k < (lrWindow w a hright).markedCells.length := by
        simpa [lrWindow_cells_length] using hk'
      rw [lrPrefixEncode_succ w a hright k hk', ih (Nat.le_of_lt hk'),
        take_succ_getElem _ k hlen, encodeWindow_append]
      have hcell :
          (lrWindow w a hright).markedCells[k] =
            ⟨(lrWindow w a hright).cells.get ⟨k, by
              simpa [lrWindow_cells_length] using hk'⟩,
              decide (k = (lrWindow w a hright).head.val)⟩ := by
        simp [LogicalWindow.markedCells, List.getElem_ofFn, Fin.ext_iff]
      simp [encodeWindow, lrCellEncode, hcell]

theorem lrPrefixEncode_all (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    lrPrefixEncode w a hright w.cells.length le_rfl =
      (lrWindow w a hright).encode := by
  rw [lrPrefixEncode_eq_take]
  have hlen :
      (lrWindow w a hright).markedCells.length = w.cells.length := by
    simp [lrWindow_cells_length]
  rw [LogicalWindow.encode, ← hlen, List.take_length]

theorem writeBlock_windowTape (w w' : LogicalWindow nt)
    (exterior : Int → Phys) (hW : windowWidth w' = windowWidth w) :
    writeBlock (windowTape w exterior) 1 w'.encode =
      windowTape w' exterior := by
  funext z
  by_cases hneg : z < 0
  · have hlt : z < (1 : Int) := by omega
    rw [writeBlock_lt (windowTape w exterior) 1 w'.encode z hlt,
      windowTape_exterior w exterior z (Or.inl hneg),
      windowTape_exterior w' exterior z (Or.inl hneg)]
  · have hnn : 0 ≤ z := by omega
    by_cases hz0 : z = 0
    · subst z
      have hlt : (0 : Int) < 1 := by omega
      rw [writeBlock_lt (windowTape w exterior) 1 w'.encode 0 hlt,
        windowTape_left w exterior, windowTape_left w' exterior]
    · by_cases hmid : z < (1 + windowWidth w : Int)
      · have h0 : 0 ≤ z - 1 := by omega
        have hi : (z - 1).toNat < w'.encode.length := by
          have : z - 1 < (windowWidth w : Int) := by omega
          have hnat : (z - 1).toNat < windowWidth w :=
            (Int.toNat_lt h0).mpr this
          rw [show w'.encode.length = windowWidth w' from rfl, hW]
          exact hnat
        have hz : z = (1 : Int) + ((z - 1).toNat : Int) := by
          have := Int.toNat_of_nonneg h0
          omega
        rw [hz, writeBlock_ofNat (windowTape w exterior) 1 w'.encode
          (z - 1).toNat (by simpa [windowWidth] using hi)]
        have hi' : (z - 1).toNat < windowWidth w' := by
          simpa [windowWidth] using hi
        have hcast : (1 : Int) + ((z - 1).toNat : Int) =
            ((z - 1).toNat : Int) + 1 := by
          omega
        rw [hcast, windowTape_encode w' exterior (z - 1).toNat hi']
      · have hge : (1 + (w'.encode.length : Int)) ≤ z := by
          simp [windowWidth] at hW
          simp [windowWidth, hW] at hmid ⊢
          omega
        rw [writeBlock_ge (windowTape w exterior) 1 w'.encode z hge]
        by_cases hzR : z = (windowWidth w + 1 : Int)
        · subst z
          have hzW : (windowWidth w + 1 : Int) =
              (windowWidth w' + 1 : Int) := by
            simp [hW]
          rw [windowTape_right w exterior, hzW, windowTape_right w' exterior]
        · have hgt : (windowWidth w + 1 : Int) < z := by omega
          have hgt' : (windowWidth w' + 1 : Int) < z := by
            simp [hW]; exact hgt
          rw [windowTape_exterior w exterior z (Or.inr hgt),
            windowTape_exterior w' exterior z (Or.inr hgt')]

theorem lrPrefixTape_all (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    lrPrefixTape w a hright exterior w.cells.length le_rfl =
      windowTape (lrWindow w a hright) exterior := by
  unfold lrPrefixTape
  rw [lrPrefixEncode_all]
  exact writeBlock_windowTape w (lrWindow w a hright) exterior
    (lrWindow_windowWidth w a hright)

/-! ## Cell-boundary configurations -/

def lrStart (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (exterior : Int → Phys) : ScanCfg ns nt :=
  { state := .updateLRFlag a false
    head := 1
    tape := windowTape w exterior }

def lrMid (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ w.cells.length) :
    ScanCfg ns nt :=
  { state := .updateLRFlag a (lrArmed w a k)
    head := ((1 + k * (nt + 1) : ℕ) : Int)
    tape := lrPrefixTape w a hright exterior k hk }

theorem lrMid_zero (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    lrMid w a hright exterior 0 (Nat.zero_le _) = lrStart a w exterior := by
  apply cfg_ext
  · simp [lrMid, lrStart, lrArmed_zero]
  · simp [lrMid, lrStart]
  · simp [lrMid, lrStart, lrPrefixTape, lrPrefixEncode_zero, writeBlock_nil]

theorem lrMid_read_flag (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : Fin w.cells.length) :
    (lrMid w a hright exterior k.val (Nat.le_of_lt k.isLt)).tape
      (lrMid w a hright exterior k.val (Nat.le_of_lt k.isLt)).head =
      tapeOfBit (decide (k.val = w.head.val)) := by
  have hlen := lrPrefixEncode_length w a hright k.val (Nat.le_of_lt k.isLt)
  simp only [lrMid, lrPrefixTape]
  have hpos :
      ((1 + k.val * (nt + 1) : ℕ) : Int) =
        (1 : Int) + (lrPrefixEncode w a hright k.val
          (Nat.le_of_lt k.isLt)).length := by
    simp [hlen]
  rw [hpos, writeBlock_at_length, ← hpos]
  exact windowTape_cell_flag w exterior k

theorem lrMid_read_bits (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : Fin w.cells.length) :
    ∀ i : Fin nt,
      (lrMid w a hright exterior k.val (Nat.le_of_lt k.isLt)).tape
        ((lrMid w a hright exterior k.val (Nat.le_of_lt k.isLt)).head + 1 +
          (i.val : Int)) =
        (cellBits w k).get ⟨i.val, by simp [cellBits, encodeOneHot_length]⟩ := by
  intro i
  have hlen := lrPrefixEncode_length w a hright k.val (Nat.le_of_lt k.isLt)
  simp only [lrMid, lrPrefixTape]
  have hz :
      (1 : Int) + (lrPrefixEncode w a hright k.val
        (Nat.le_of_lt k.isLt)).length ≤
        ((1 + k.val * (nt + 1) : ℕ) : Int) + 1 + (i.val : Int) := by
    simp [hlen, Nat.cast_add, Nat.cast_one]; omega
  rw [writeBlock_ge _ _ _ _ hz]
  have hcast :
      ((1 + k.val * (nt + 1) : ℕ) : Int) + 1 + (i.val : Int) =
        ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) := by
    simp [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  simpa [cellBits, List.get_eq_getElem, List.getElem_map] using
    windowTape_cell_bit w exterior k i

/-! ## Interior induction -/

theorem lr_take_cells (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (lrInteriorArrowsTake p hnt blank a w hright k hk)
      (lrStart a w exterior) =
      some (lrMid w a hright exterior k hk) := by
  induction k with
  | zero =>
      simp [lrInteriorArrowsTake, FiniteOneTapeSemantics.run_nil]
      exact (lrMid_zero w a hright exterior).symm
  | succ k ih =>
      have hk' : k < w.cells.length := by omega
      have hle : k ≤ w.cells.length := Nat.le_of_lt hk'
      rw [lrInteriorArrowsTake_succ p hnt blank a w hright k hk',
        run_append p hnt blank, ih hle]
      simp only [Option.bind_some]
      let kk : Fin w.cells.length := ⟨k, hk'⟩
      have hrun :=
        cell_run p hnt blank a (lrArmed w a k)
          (tapeOfBit (decide (k = w.head.val)))
          (tapeOfBit (decide (k = (lrWindow w a hright).head.val)))
          (lrArmed w a (k + 1))
          (tapeOfBit_ne_blank _)
          (updateLR_window_cell w a hright kk)
          (cellBits w kk) (cellBits_length w kk) (cellBits_valid w kk)
          (lrMid w a hright exterior k hle)
          (by simp [lrMid])
          (lrMid_read_flag w a hright exterior kk)
          (lrMid_read_bits w a hright exterior kk)
      have harrows : lrCellArrows p hnt blank a w hright kk =
          cellArrows p hnt blank a (lrArmed w a k)
            (tapeOfBit (decide (k = w.head.val)))
            (tapeOfBit (decide (k = (lrWindow w a hright).head.val)))
            (lrArmed w a (k + 1))
            (tapeOfBit_ne_blank _)
            (updateLR_window_cell w a hright kk)
            (cellBits w kk) (cellBits_length w kk) (cellBits_valid w kk) :=
        rfl
      rw [harrows, hrun]
      apply congrArg some
      apply cfg_ext
      · simp [lrMid]
      · have hnat :
            1 + k * (nt + 1) + 1 + nt = 1 + (k + 1) * (nt + 1) := by
          rw [Nat.succ_mul]
          omega
        have hhead :
            ((1 + k * (nt + 1) : ℕ) : Int) + 1 + (nt : Int) =
              ((1 + (k + 1) * (nt + 1) : ℕ) : Int) := by
          have hcast :
              ((1 + k * (nt + 1) + 1 + nt : ℕ) : Int) =
                ((1 + k * (nt + 1) : ℕ) : Int) + 1 + (nt : Int) := by
            simp [Nat.cast_add, Nat.cast_one]
          rw [← hcast, hnat]
        simpa [lrMid] using hhead
      · have hlen := lrPrefixEncode_length w a hright k hle
        simp only [lrMid, lrPrefixTape]
        have hpos :
            ((1 + k * (nt + 1) : ℕ) : Int) =
              (1 : Int) + (lrPrefixEncode w a hright k hle).length := by
          simp [hlen]
        rw [hpos, writeBlock_snoc]
        have hx :
            decide (tapeOfBit (decide (k = w.head.val)) = one) =
              decide (k = w.head.val) := by
          cases decide (k = w.head.val) <;> simp [tapeOfBit, one]
        rw [hx]
        simp only [cellBits]
        rw [outputBits_window w a hright kk]
        have hpos1 :
            (1 : Int) + (lrPrefixEncode w a hright k hle).length + 1 =
              (1 : Int) +
                ((lrPrefixEncode w a hright k hle ++
                  [tapeOfBit (decide (k =
                    (lrWindow w a hright).head.val))]).length : Int) := by
          simp; omega
        rw [hpos1, writeBlock_append, lrPrefixEncode_succ w a hright k hk']
        simp [lrCellEncode, encodeMarkedCell, kk]

theorem lr_interior_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (lrInteriorArrows p hnt blank a w hright)
      (lrStart a w exterior) =
      some {
        state := .updateLRFlag a false
        head := (windowWidth w + 1 : Int)
        tape := windowTape (lrWindow w a hright) exterior } := by
  unfold lrInteriorArrows
  apply Eq.trans (lr_take_cells p hnt blank a w hright exterior
    w.cells.length le_rfl)
  apply congrArg some
  apply cfg_ext
  · simp [lrMid]
    exact lrArmed_length w a hright
  · have hhead :
        ((1 + w.cells.length * (nt + 1) : ℕ) : Int) =
          (windowWidth w + 1 : Int) := by
      simp [windowWidth, Nat.cast_add, Nat.cast_one, add_comm]
    simpa [lrMid] using hhead
  · exact lrPrefixTape_all w a hright exterior

theorem lr_window_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (lrWindowArrows p hnt blank a w hright)
      (lrStart a w exterior) =
      some {
        state := .skipRL a false ⟨nt - 1, by omega⟩
        head := (windowWidth w : Int)
        tape := windowTape (lrWindow w a hright) exterior } := by
  rw [lrWindowArrows, run_append p hnt blank, lr_interior_run]
  simp only [Option.bind_some, FiniteOneTapeSemantics.run_cons,
    FiniteOneTapeSemantics.run_nil]
  have hstep :=
    updateLRFlagRightBoundaryArrow_step p hnt blank a
      { state := .updateLRFlag a false
        head := (windowWidth w + 1 : Int)
        tape := windowTape (lrWindow w a hright) exterior }
      rfl
      (by
        simpa [lrWindow_windowWidth w a hright] using
          windowTape_right (lrWindow w a hright) exterior)
  rw [hstep]
  apply congrArg some
  apply cfg_ext
  · rfl
  · have : (windowWidth w + 1 : Int) - 1 = (windowWidth w : Int) := by
      omega
    simpa
  · rfl

theorem lr_pre_boundary (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (lrInteriorArrows p hnt blank a w hright)
      (lrStart a w exterior) =
      some {
        state := .updateLRFlag a false
        head := (windowWidth w + 1 : Int)
        tape := windowTape (lrWindow w a hright) exterior } :=
  lr_interior_run p hnt blank a w hright exterior

theorem lr_cell_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (lrInteriorArrowsTake p hnt blank a w hright k hk)
        (lrStart a w exterior) = some c' ∧
      c'.state = .updateLRFlag a (lrArmed w a k) ∧
      c'.head = ((1 + k * (nt + 1) : ℕ) : Int) ∧
      c'.tape = lrPrefixTape w a hright exterior k hk := by
  refine ⟨lrMid w a hright exterior k hk, ?_, rfl, rfl, rfl⟩
  exact lr_take_cells p hnt blank a w hright exterior k hk

theorem lr_window_block (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (lrWindowArrows p hnt blank a w hright)
        (lrStart a w exterior) = some c' ∧
      c'.state = .skipRL a false ⟨nt - 1, by omega⟩ ∧
      c'.head = (windowWidth w : Int) ∧
      c'.tape = windowTape (lrWindow w a hright) exterior ∧
      (lrWindowArrows p hnt blank a w hright).length = windowWidth w + 1 ∧
      (lrInteriorArrows p hnt blank a w hright).length = windowWidth w := by
  refine ⟨{ state := .skipRL a false ⟨nt - 1, by omega⟩
            head := (windowWidth w : Int)
            tape := windowTape (lrWindow w a hright) exterior },
    ?_, rfl, rfl, rfl, lrWindowArrows_length p hnt blank a w hright,
    lrInteriorArrows_length p hnt blank a w hright⟩
  exact lr_window_run p hnt blank a w hright exterior

end PakFixedPolyomino.ULogSourceObliviousLRWindowExecution
