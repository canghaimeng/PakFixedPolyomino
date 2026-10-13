import PakFixedPolyomino.StandardBitPairProjection
import PakFixedPolyomino.StandardBitDecrementWord
import PakFixedPolyomino.StandardBitDecrementAlignment
import PakFixedPolyomino.StandardBitMarkedCompaction
import PakFixedPolyomino.PakFixedWeightedStandardBinaryCount
import Mathlib.Tactic

/-! Physical comparison of a little-endian counter with a literal answer length. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetCompare

open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitDecrementWord
  (borrowBits zeroPrefix borrow_none_iff borrow_value borrow_length zeroPrefix_le)
open StandardBitDecrementAlignment (value_eq_original)
open StandardBitMarkedCompaction (scan_left scan_right preserve_step)
open StandardBitPairProjection
  (natInt natInt_succ natInt_pred natInt_zero natInt_ne_neg1 natInt_inj nat_ne_neg1
    toNat_ofNat update_same pairBits_marker pairBits_payload pairBits_sep pairBits_y
    unpairBits_eq_some unpairBits_none_cases drop_head_eq)
open Polynomial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def compareBits (w : List Bool) : List Bool :=
  match StandardBitMetric.unpairBits w with
  | none => [false]
  | some (x, y) => [decide (PakFixedWeightedStandardBinaryCount.value x < y.length)]

theorem compare_pair (x y : List Bool) :
    compareBits (StandardBitMetric.pairBits x y) =
      [decide (PakFixedWeightedStandardBinaryCount.value x < y.length)] := by
  simp [compareBits, unpair_pairBits]

def enc (b : Bool) : Fin 8 := if b then 1 else 0
@[simp] theorem enc_false : enc false = 0 := rfl
@[simp] theorem enc_true : enc true = 1 := rfl
def D (x : List Bool) : ℕ := 2 * x.length
def Eidx (x y : List Bool) : ℕ := 2 * x.length + 1 + y.length

def machine : DeterministicMachine 19 8 where
  rule := fun q a _ =>
    if q = 2 then some ⟨a, 3, .left⟩
    else if q = 3 then some ⟨3, 4, .right⟩
    else if q = 4 then
      if a = 1 then some ⟨6, 5, .right⟩
      else if a = 0 then some ⟨4, 6, .right⟩
      else if a = 2 then some ⟨2, 16, .left⟩
      else none
    else if q = 5 then
      if a = 0 ∨ a = 1 then some ⟨a, 4, .right⟩
      else if a = 2 then some ⟨2, 16, .left⟩
      else none
    else if q = 6 then
      if a = 0 ∨ a = 1 then some ⟨a, 6, .right⟩
      else if a = 2 then some ⟨5, 7, .left⟩
      else none
    else if q = 7 then
      if a = 4 then some ⟨4, 8, .right⟩
      else some ⟨a, 7, .left⟩
    else if q = 8 then
      if a = 6 then some ⟨6, 8, .right⟩
      else if a = 0 ∨ a = 1 then some ⟨6, 9, .left⟩
      else if a = 5 then some ⟨2, 16, .left⟩
      else none
    else if q = 9 then
      if a = 3 then some ⟨3, 10, .right⟩
      else some ⟨a, 9, .left⟩
    else if q = 10 then
      if a = 6 then some ⟨6, 11, .right⟩
      else if a = 4 then some ⟨2, 13, .right⟩
      else none
    else if q = 11 then
      if a = 0 then some ⟨1, 10, .right⟩
      else if a = 1 then some ⟨0, 12, .right⟩
      else none
    else if q = 12 then
      if a = 4 then some ⟨4, 8, .right⟩
      else some ⟨a, 12, .right⟩
    else if q = 13 then
      if a = 5 then some ⟨2, 15, .left⟩
      else some ⟨2, 13, .right⟩
    else if q = 15 then
      if a = 3 then some ⟨2, 17, .right⟩
      else some ⟨2, 15, .left⟩
    else if q = 16 then
      if a = 3 then some ⟨2, 18, .right⟩
      else some ⟨2, 16, .left⟩
    else if q = 17 then some ⟨1, 0, .stay⟩
    else if q = 18 then some ⟨0, 0, .stay⟩
    else none
  start := 2
  accept := 0
  reject := 1
  accept_ne_reject := by decide
  blank := 2
  zero := 0
  one := 1
  blank_ne_zero := by decide
  blank_ne_one := by decide
  zero_ne_one := by decide
  accept_terminal := by intros; simp
  reject_terminal := by intros; simp

@[simp] theorem machine_blank : machine.blank = 2 := rfl
@[simp] theorem machine_zero : machine.zero = 0 := rfl
@[simp] theorem machine_one : machine.one = 1 := rfl
@[simp] theorem machine_accept : machine.accept = 0 := rfl
@[simp] theorem machine_start : machine.start = 2 := rfl

theorem rule_start (a : Fin 8) :
    machine.rule 2 a 0 = some ⟨a, 3, .left⟩ := by simp [machine]
theorem rule_markL (a : Fin 8) :
    machine.rule 3 a 0 = some ⟨3, 4, .right⟩ := by simp [machine]
theorem rule_parse_one :
    machine.rule 4 1 0 = some ⟨6, 5, .right⟩ := by simp [machine]
theorem rule_parse_zero :
    machine.rule 4 0 0 = some ⟨4, 6, .right⟩ := by simp [machine]
theorem rule_parse_blank :
    machine.rule 4 2 0 = some ⟨2, 16, .left⟩ := by simp [machine]
theorem rule_pay (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 5 a 0 = some ⟨a, 4, .right⟩ := by rcases h with h | h <;> simp [machine, h]
theorem rule_pay_blank :
    machine.rule 5 2 0 = some ⟨2, 16, .left⟩ := by simp [machine]
theorem rule_y (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 6 a 0 = some ⟨a, 6, .right⟩ := by rcases h with h | h <;> simp [machine, h]
theorem rule_y_blank :
    machine.rule 6 2 0 = some ⟨5, 7, .left⟩ := by simp [machine]
theorem rule_seekSEP :
    machine.rule 7 4 0 = some ⟨4, 8, .right⟩ := by simp [machine]
theorem rule_seekSEP_not (a : Fin 8) (h : a ≠ 4) :
    machine.rule 7 a 0 = some ⟨a, 7, .left⟩ := by simp [machine, h]
theorem rule_skip6 :
    machine.rule 8 6 0 = some ⟨6, 8, .right⟩ := by simp [machine]
theorem rule_consume (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 8 a 0 = some ⟨6, 9, .left⟩ := by rcases h with h | h <;> simp [machine, h]
theorem rule_exhaust :
    machine.rule 8 5 0 = some ⟨2, 16, .left⟩ := by simp [machine]
theorem rule_seekL :
    machine.rule 9 3 0 = some ⟨3, 10, .right⟩ := by simp [machine]
theorem rule_seekL_not (a : Fin 8) (h : a ≠ 3) :
    machine.rule 9 a 0 = some ⟨a, 9, .left⟩ := by simp [machine, h]
theorem rule_mark6 :
    machine.rule 10 6 0 = some ⟨6, 11, .right⟩ := by simp [machine]
theorem rule_under :
    machine.rule 10 4 0 = some ⟨2, 13, .right⟩ := by simp [machine]
theorem rule_bit0 :
    machine.rule 11 0 0 = some ⟨1, 10, .right⟩ := by simp [machine]
theorem rule_bit1 :
    machine.rule 11 1 0 = some ⟨0, 12, .right⟩ := by simp [machine]
theorem rule_backSEP :
    machine.rule 12 4 0 = some ⟨4, 8, .right⟩ := by simp [machine]
theorem rule_back_not (a : Fin 8) (h : a ≠ 4) :
    machine.rule 12 a 0 = some ⟨a, 12, .right⟩ := by simp [machine, h]
theorem rule_cleanE :
    machine.rule 13 5 0 = some ⟨2, 15, .left⟩ := by simp [machine]
theorem rule_cleanR (a : Fin 8) (h : a ≠ 5) :
    machine.rule 13 a 0 = some ⟨2, 13, .right⟩ := by simp [machine, h]
theorem rule_trueL :
    machine.rule 15 3 0 = some ⟨2, 17, .right⟩ := by simp [machine]
theorem rule_true_not (a : Fin 8) (h : a ≠ 3) :
    machine.rule 15 a 0 = some ⟨2, 15, .left⟩ := by simp [machine, h]
theorem rule_falseL :
    machine.rule 16 3 0 = some ⟨2, 18, .right⟩ := by simp [machine]
theorem rule_false_not (a : Fin 8) (h : a ≠ 3) :
    machine.rule 16 a 0 = some ⟨2, 16, .left⟩ := by simp [machine, h]
theorem rule_emit1 (a : Fin 8) :
    machine.rule 17 a 0 = some ⟨1, 0, .stay⟩ := by simp [machine]
theorem rule_emit0 (a : Fin 8) :
    machine.rule 18 a 0 = some ⟨0, 0, .stay⟩ := by simp [machine]

set_option simprocs false

theorem read_bit (w : List Bool) (i : ℕ) (hi : i < w.length) :
    inputTape machine w i = enc w[i] := by simp [inputTape, enc, hi]

def workNat (w : List Bool) (n i : ℕ) : Fin 8 :=
  if i < n then
    if i % 2 = 0 then 6 else (if h : i < w.length then enc w[i] else 2)
  else inputTape machine w i

def workTape (w : List Bool) (n : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then workNat w n z.toNat
  else 2

def budgetNat (x y : List Bool) (k : ℕ) (u : List Bool) (i : ℕ) : Fin 8 :=
  if i < D x then
    if i % 2 = 0 then 6
    else if h : i / 2 < u.length then enc u[i / 2] else 2
  else if i = D x then 4
  else if i < D x + 1 + k then 6
  else if i < Eidx x y then
    if h : i - (D x + 1) < y.length then enc y[i - (D x + 1)] else 2
  else if i = Eidx x y then 5
  else 2

def budgetTape (x y : List Bool) (k : ℕ) (u : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then budgetNat x y k u z.toNat
  else 2

def markedTape (w : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3 else inputTape machine w z
def boundaryTape (z : Int) : Fin 8 := if z = -1 then 3 else 2
def finalConfig (b : Bool) : Configuration 19 8 :=
  ⟨0, 0, inputTape machine [b]⟩

theorem inputTape_nil : inputTape machine ([] : List Bool) = fun _ => (2 : Fin 8) := by
  funext z; unfold inputTape; by_cases hpos : 0 ≤ z <;> simp [hpos]
theorem boundary_erase_L :
    Function.update boundaryTape (-1) 2 = fun _ => (2 : Fin 8) := by
  funext z; by_cases hz : z = -1 <;> simp [Function.update_apply, boundaryTape, hz]
theorem emit_tape (b : Bool) :
    Function.update (fun _ : Int => (2 : Fin 8)) 0 (enc b) = inputTape machine [b] := by
  funext z
  by_cases hz : z = (0 : Int)
  · subst z; simp [inputTape, enc, machine]
  · rw [Function.update_of_ne hz]
    by_cases hge : 0 ≤ z
    · rw [inputTape_ge machine [b] z (by simp only [List.length_singleton]; omega)]; rfl
    · rw [inputTape_neg machine [b] z (by omega)]; rfl

theorem marked_eq_work0 (w : List Bool) : markedTape w = workTape w 0 := by
  funext z; unfold markedTape workTape workNat
  by_cases hL : z = -1; · simp [hL]
  rw [if_neg hL, if_neg hL]
  by_cases hpos : 0 ≤ z
  · rw [dif_pos hpos, if_neg (Nat.not_lt_zero _), Int.toNat_of_nonneg hpos]
  · rw [dif_neg hpos, inputTape_neg machine w z (not_le.mp hpos)]; rfl

theorem work_ge (w : List Bool) (n i : ℕ) (hi : n ≤ i) :
    workTape w n (i : Int) = inputTape machine w (i : Int) := by
  unfold workTape workNat
  rw [if_neg (nat_ne_neg1 i), dif_pos (Nat.cast_nonneg i)]
  simp [toNat_ofNat, Nat.not_lt.mpr hi]

theorem work_write_mark (w : List Bool) (n : ℕ) (he : n % 2 = 0) :
    Function.update (workTape w n) (natInt n) 6 = workTape w (n + 1) := by
  funext z
  by_cases hz : z = natInt n
  · subst z
    unfold workTape workNat
    rw [Function.update_apply, if_pos rfl, if_neg (natInt_ne_neg1 n),
      dif_pos (Nat.cast_nonneg n)]
    simp [natInt, toNat_ofNat, Nat.lt_succ_self n, he]
  · rw [Function.update_apply, if_neg hz]
    unfold workTape
    by_cases hL : z = -1; · simp [hL]
    rw [if_neg hL, if_neg hL]
    by_cases hpos : 0 ≤ z
    · rw [dif_pos hpos, dif_pos hpos]
      unfold workNat
      have hne : z.toNat ≠ n := by
        intro heq; exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
      by_cases hlt : z.toNat < n
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · rw [if_neg hlt, if_neg (by omega : ¬ z.toNat < n + 1)]
    · rw [dif_neg hpos, dif_neg hpos]

theorem work_write_keep (w : List Bool) (n : ℕ) (ho : n % 2 = 1) (hn : n < w.length) :
    Function.update (workTape w n) (natInt n) (enc w[n]) = workTape w (n + 1) := by
  funext z
  by_cases hz : z = natInt n
  · subst z
    unfold workTape workNat
    rw [Function.update_apply, if_pos rfl, if_neg (natInt_ne_neg1 n),
      dif_pos (Nat.cast_nonneg n)]
    simp [natInt, toNat_ofNat, Nat.lt_succ_self n, ho, hn]
  · rw [Function.update_apply, if_neg hz]
    unfold workTape
    by_cases hL : z = -1; · simp [hL]
    rw [if_neg hL, if_neg hL]
    by_cases hpos : 0 ≤ z
    · rw [dif_pos hpos, dif_pos hpos]
      unfold workNat
      have hne : z.toNat ≠ n := by
        intro heq; exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
      by_cases hlt : z.toNat < n
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · rw [if_neg hlt, if_neg (by omega : ¬ z.toNat < n + 1)]
    · rw [dif_neg hpos, dif_neg hpos]

theorem step_start (w : List Bool) :
    step machine 0 (initial machine w) =
      some ⟨3, -1, inputTape machine w⟩ := by
  simp [step, initial, rule_start, writtenTape, moveHead, update_same]
theorem step_markL (w : List Bool) :
    step machine 0 ⟨3, -1, inputTape machine w⟩ =
      some ⟨4, 0, markedTape w⟩ := by
  have hblank : inputTape machine w (-1) = 2 := inputTape_neg machine w (-1) (by omega)
  have htape : Function.update (inputTape machine w) (-1) 3 = markedTape w := by
    funext z; simp [Function.update_apply, markedTape]
  simp [step, hblank, rule_markL, writtenTape, moveHead, htape]
theorem setup2 (w : List Bool) :
    run machine (ticks 2) (initial machine w) =
      some ⟨4, 0, workTape w 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append, run_ticks_one, step_start,
    Option.bind_some, run_ticks_one, step_markL]
  simp [marked_eq_work0]

theorem step_parse_true (w : List Bool) (n : ℕ) (hn : n < w.length) (ht : w[n] = true)
    (he : n % 2 = 0) :
    step machine 0 ⟨4, natInt n, workTape w n⟩ =
      some ⟨5, natInt (n + 1), workTape w (n + 1)⟩ := by
  have hread : workTape w n (n : Int) = 1 := by
    rw [work_ge w n n le_rfl, read_bit w n hn, ht, enc_true]
  simp only [step, hread, rule_parse_one, writtenTape, moveHead, Option.map_some]
  rw [work_write_mark w n he, natInt_succ]

theorem step_parse_sep (w : List Bool) (n : ℕ) (hn : n < w.length) (ht : w[n] = false)
    (he : n % 2 = 0) :
    step machine 0 ⟨4, natInt n, workTape w n⟩ =
      some ⟨6, natInt (n + 1), Function.update (workTape w n) (natInt n) 4⟩ := by
  have hread : workTape w n (n : Int) = 0 := by
    rw [work_ge w n n le_rfl, read_bit w n hn, ht, enc_false]
  simp only [step, hread, rule_parse_zero, writtenTape, moveHead, Option.map_some]
  rw [natInt_succ]

theorem step_parse_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 ⟨4, natInt n, workTape w n⟩ =
      some ⟨16, natInt n - 1, Function.update (workTape w n) (natInt n) 2⟩ := by
  have hread : workTape w n (n : Int) = 2 := by
    rw [work_ge w n n le_rfl, inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn),
      machine_blank]
  simp [step, hread, rule_parse_blank, writtenTape, moveHead]

theorem step_pay (w : List Bool) (n : ℕ) (hn : n < w.length) (ho : n % 2 = 1) :
    step machine 0 ⟨5, natInt n, workTape w n⟩ =
      some ⟨4, natInt (n + 1), workTape w (n + 1)⟩ := by
  have hread : workTape w n (n : Int) = enc w[n] := by
    rw [work_ge w n n le_rfl, read_bit w n hn]
  have hbit : enc w[n] = 0 ∨ enc w[n] = 1 := by cases (w[n] : Bool) <;> simp
  simp only [step, hread, rule_pay _ hbit, writtenTape, moveHead, Option.map_some]
  rw [work_write_keep w n ho hn, natInt_succ]

theorem step_pay_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 ⟨5, natInt n, workTape w n⟩ =
      some ⟨16, natInt n - 1, Function.update (workTape w n) (natInt n) 2⟩ := by
  have hread : workTape w n (n : Int) = 2 := by
    rw [work_ge w n n le_rfl, inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn),
      machine_blank]
  simp [step, hread, rule_pay_blank, writtenTape, moveHead]

theorem parse_x (x y : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    run machine (ticks (2 * k)) ⟨4, 0, workTape (pairBits x y) 0⟩ =
      some ⟨4, natInt (2 * k), workTape (pairBits x y) (2 * k)⟩ := by
  induction k with
  | zero => simp [ticks, natInt_zero]
  | succ k ih =>
      have hk' : k < x.length := by omega
      have hlen := pairBits_length x y
      have h2 : 2 * k < (pairBits x y).length := by omega
      have h2s : 2 * k + 1 < (pairBits x y).length := by omega
      have htrue := pairBits_marker x y k hk'
      have htwo : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      have he : (2 * k) % 2 = 0 := by omega
      have ho : (2 * k + 1) % 2 = 1 := by omega
      rw [htwo, ticks_add, ticks_add, run_append, run_append, ih (by omega),
        Option.bind_some, run_ticks_one, step_parse_true (pairBits x y) (2 * k) h2 htrue he,
        Option.bind_some, run_ticks_one, step_pay (pairBits x y) (2 * k + 1) h2s ho]

def skipTape (x y : List Bool) (j : ℕ) : Int → Fin 8 :=
  Function.update (workTape (pairBits x y) (D x)) (natInt (D x)) 4

theorem skipTape_ge (x y : List Bool) (j i : ℕ) (hi : D x + 1 + j ≤ i) :
    skipTape x y j (i : Int) = inputTape machine (pairBits x y) (i : Int) := by
  unfold skipTape
  have hne : (i : Int) ≠ natInt (D x) := by
    intro h; have := (natInt_inj.mp h.symm); omega
  rw [Function.update_apply, if_neg hne, work_ge]
  omega

-- The skipTape j parameter is only used after we erase y cells; during q6 we
-- preserve y, so the tape stays skipTape x y 0 = workTape with SEP written.
theorem skip0_read_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    skipTape x y 0 (natInt (D x + 1 + j)) = enc y[j] := by
  have hidx : D x + 1 + j < (pairBits x y).length := by
    simp [D]; have := pairBits_length x y; omega
  have hy : (pairBits x y)[D x + 1 + j]'hidx = y[j] := by
    simpa [D] using pairBits_y x y j hj
  have hge : D x ≤ D x + 1 + j := by omega
  have hne : natInt (D x + 1 + j) ≠ natInt (D x) := by
    intro h; have := natInt_inj.mp h; omega
  unfold skipTape
  rw [Function.update_apply, if_neg hne, work_ge (pairBits x y) (D x) (D x + 1 + j) (by omega)]
  simpa [natInt, hy] using read_bit (pairBits x y) (D x + 1 + j) hidx

theorem step_skip_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    step machine 0 ⟨6, natInt (D x + 1 + j), skipTape x y 0⟩ =
      some ⟨6, natInt (D x + 1 + j + 1), skipTape x y 0⟩ := by
  have hread := skip0_read_y x y j hj
  have hbit : enc y[j] = 0 ∨ enc y[j] = 1 := by cases (y[j] : Bool) <;> simp
  simp only [step, hread, rule_y _ hbit, writtenTape, moveHead, Option.map_some]
  rw [← hread, update_same, natInt_succ]

theorem skip_y (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    run machine (ticks j) ⟨6, natInt (D x + 1), skipTape x y 0⟩ =
      some ⟨6, natInt (D x + 1 + j), skipTape x y 0⟩ := by
  induction j with
  | zero => simp [ticks]
  | succ j ih =>
      rw [ticks_add, run_append, ih (by omega), Option.bind_some, run_ticks_one,
        step_skip_y x y j (by omega)]
      simp [Nat.add_assoc]

def endedTape (x y : List Bool) : Int → Fin 8 :=
  Function.update (skipTape x y 0) (natInt (Eidx x y)) 5

theorem step_markE (x y : List Bool) :
    step machine 0 ⟨6, natInt (D x + 1 + y.length), skipTape x y 0⟩ =
      some ⟨7, natInt (D x + y.length), endedTape x y⟩ := by
  have hge : (pairBits x y).length ≤ D x + 1 + y.length := by simp [D, Eidx]
  have hread : skipTape x y 0 (natInt (D x + 1 + y.length)) = 2 := by
    have hne : natInt (D x + 1 + y.length) ≠ natInt (D x) := by
      intro h; have := natInt_inj.mp h; simp [D] at this; omega
    unfold skipTape
    rw [Function.update_apply, if_neg hne,
      work_ge (pairBits x y) (D x) (D x + 1 + y.length) (by omega)]
    simpa [natInt] using
      inputTape_ge machine (pairBits x y) (natInt (D x + 1 + y.length))
        (Nat.cast_le.mpr hge)
  have hD : 1 ≤ D x + 1 + y.length := by omega
  simp only [step, hread, rule_y_blank, writtenTape, moveHead, endedTape, Option.map_some]
  have hp : natInt (D x + 1 + y.length) - 1 = natInt (D x + y.length) := by
    simp [natInt]; omega
  simpa [Eidx, D, Nat.add_assoc] using hp

theorem ended_nat_ne_SEP (x y : List Bool) (i : ℕ) (hi : i ≠ D x) :
    endedTape x y (i : Int) ≠ 4 := by
  unfold endedTape skipTape
  by_cases hE : (i : Int) = natInt (Eidx x y)
  · rw [Function.update_apply, if_pos hE]; decide
  · rw [Function.update_apply, if_neg hE]
    have hS : (i : Int) ≠ natInt (D x) := fun h => hi (natInt_inj.mp h)
    rw [Function.update_apply, if_neg hS]
    unfold workTape workNat
    rw [if_neg (nat_ne_neg1 i), dif_pos (Nat.cast_nonneg i)]
    simp only [toNat_ofNat]
    by_cases hlt : i < D x
    · rw [if_pos hlt]
      by_cases he : i % 2 = 0
      · rw [if_pos he]; decide
      · rw [if_neg he]
        have hlen : i < (pairBits x y).length := by
          have := pairBits_length x y; simp [D] at hlt ⊢; omega
        rw [dif_pos hlen]; cases (pairBits x y)[i] <;> (simp [enc]; decide)
    · rw [if_neg hlt]
      by_cases hin : i < (pairBits x y).length
      · have hbit := read_bit (pairBits x y) i hin
        rw [hbit]; cases (pairBits x y)[i] <;> (simp [enc]; decide)
      · have hge : ((pairBits x y).length : Int) ≤ (i : Int) :=
          Nat.cast_le.mpr (Nat.not_lt.mp hin)
        have hblank := inputTape_ge machine (pairBits x y) (i : Int) hge
        rw [hblank]; decide

theorem ended_SEP (x y : List Bool) : endedTape x y (natInt (D x)) = 4 := by
  unfold endedTape skipTape
  have hne : natInt (D x) ≠ natInt (Eidx x y) := by
    intro h; have := natInt_inj.mp h; simp [D, Eidx] at this; omega
  rw [Function.update_apply, if_neg hne, Function.update_apply, if_pos rfl]

theorem ended_L (x y : List Bool) : endedTape x y (-1) = 3 := by
  unfold endedTape skipTape workTape
  have hne : (-1 : Int) ≠ natInt (Eidx x y) := (natInt_ne_neg1 _).symm
  have hne2 : (-1 : Int) ≠ natInt (D x) := (natInt_ne_neg1 _).symm
  rw [Function.update_apply, if_neg hne, Function.update_apply, if_neg hne2]; rfl

theorem seekSEP_not (x y : List Bool) (p : ℕ) (hp : p ≠ D x) :
    step machine 0 ⟨7, natInt p, endedTape x y⟩ =
      some ⟨7, natInt p - 1, endedTape x y⟩ := by
  have ht : endedTape x y (natInt p) ≠ 4 := ended_nat_ne_SEP x y p hp
  simp [step, rule_seekSEP_not _ ht, writtenTape, moveHead, update_same]

theorem seekSEP_to (x y : List Bool) :
    run machine (ticks (y.length + 1))
        ⟨7, natInt (D x + y.length), endedTape x y⟩ =
      some ⟨8, natInt (D x + 1), endedTape x y⟩ := by
  have hp : natInt (D x + y.length) - (y.length : Int) = natInt (D x) := by
    unfold natInt; omega
  have hwalk :
      run machine (ticks y.length) ⟨7, natInt (D x + y.length), endedTape x y⟩ =
        some ⟨7, natInt (D x), endedTape x y⟩ := by
    rw [← hp]
    apply scan_left (M := machine) (q := 7) (t := endedTape x y)
      (h := natInt (D x + y.length)) (n := y.length)
    intro i hi
    have hpos : natInt (D x + y.length) - (i : Int) = natInt (D x + y.length - i) := by
      simp [natInt]; omega
    have hne : D x + y.length - i ≠ D x := by omega
    have ht : endedTape x y (natInt (D x + y.length) - (i : Int)) ≠ 4 := by
      rw [hpos]; exact ended_nat_ne_SEP x y _ hne
    exact rule_seekSEP_not _ ht
  rw [ticks_add, run_append, hwalk, Option.bind_some, run_ticks_one]
  simp only [step, ended_SEP, rule_seekSEP, writtenTape, moveHead, Option.map_some]
  rw [← ended_SEP, update_same, natInt_succ]

theorem setup_run (x y : List Bool) :
    run machine (ticks (2 * x.length + 2 * y.length + 5))
      (initial machine (pairBits x y)) =
      some ⟨8, natInt (D x + 1), endedTape x y⟩ := by
  have hfuel : 2 * x.length + 2 * y.length + 5 =
      2 + (2 * x.length + (1 + (y.length + (1 + (y.length + 1))))) := by omega
  have hn : 2 * x.length < (pairBits x y).length := by
    have := pairBits_length x y; omega
  have hf := pairBits_sep x y
  have he : (2 * x.length) % 2 = 0 := by omega
  have hD : 2 * x.length = D x := rfl
  rw [show ticks (2 * x.length + 2 * y.length + 5) =
        ticks 2 ++ ticks (2 * x.length) ++ ticks 1 ++ ticks y.length ++ ticks 1 ++
          ticks (y.length + 1) by
      simp [hfuel, ticks_add, List.append_assoc]]
  rw [run_append, run_append, run_append, run_append, run_append,
    setup2 (pairBits x y), Option.bind_some, parse_x x y x.length le_rfl,
    Option.bind_some, run_ticks_one]
  have hsep := step_parse_sep (pairBits x y) (2 * x.length) hn hf he
  rw [hsep, Option.bind_some]
  have hsk : skipTape x y 0 = Function.update (workTape (pairBits x y) (2 * x.length))
      (natInt (2 * x.length)) 4 := rfl
  rw [← hsk, hD, skip_y x y y.length le_rfl, Option.bind_some,
    run_ticks_one, step_markE x y, Option.bind_some, seekSEP_to x y]

def wipe (t : Int → Fin 8) (k : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z ∧ k ≤ z.toNat then 2
  else t z

theorem wipe_update (t : Int → Fin 8) (p : ℕ) :
    Function.update (wipe t (p + 1)) (natInt p) 2 = wipe t p := by
  funext z
  by_cases hz : z = natInt p
  · subst z
    unfold wipe
    rw [Function.update_apply, if_pos rfl, if_neg (natInt_ne_neg1 p)]
    simp [natInt, toNat_ofNat, Nat.cast_nonneg]
  · rw [Function.update_apply, if_neg hz]
    unfold wipe
    by_cases hL : z = -1; · simp [hL]
    rw [if_neg hL, if_neg hL]
    by_cases hpos : 0 ≤ z
    · have hne : z.toNat ≠ p := by
        intro heq; exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
      by_cases hge : p + 1 ≤ z.toNat
      · have hp : p ≤ z.toNat := Nat.le_of_succ_le hge
        simp [hpos, hge, hp]
      · have hp : ¬ p ≤ z.toNat := by omega
        simp [hpos, hge, hp]
    · simp [hpos]

theorem wipe_nat_ne_L (t : Int → Fin 8) (k i : ℕ) (ht : t (i : Int) ≠ 3) :
    wipe t k (i : Int) ≠ 3 := by
  unfold wipe
  rw [if_neg (nat_ne_neg1 i)]
  by_cases hcond : 0 ≤ (i : Int) ∧ k ≤ (i : Int).toNat
  · rw [dif_pos hcond]; decide
  · rw [dif_neg hcond]; exact ht

theorem step_wipe16 (t : Int → Fin 8) (p : ℕ) (ht : t (p : Int) ≠ 3) :
    step machine 0 ⟨16, natInt p, wipe t (p + 1)⟩ =
      some ⟨16, natInt p - 1, wipe t p⟩ := by
  have hne : wipe t (p + 1) (natInt p) ≠ 3 := wipe_nat_ne_L t (p + 1) p ht
  simp [step, rule_false_not _ hne, writtenTape, moveHead, wipe_update]

theorem wipe16_to_L (t : Int → Fin 8) (p : ℕ) (ht : ∀ i : ℕ, t (i : Int) ≠ 3) :
    run machine (ticks (p + 1)) ⟨16, natInt p, wipe t (p + 1)⟩ =
      some ⟨16, -1, wipe t 0⟩ := by
  induction p with
  | zero => rw [run_ticks_one, step_wipe16 t 0 (ht 0)]; simp [natInt_zero]
  | succ p ih =>
      have hticks : ticks (p + 1 + 1) = ticks 1 ++ ticks (p + 1) := by
        have : p + 1 + 1 = 1 + (p + 1) := by omega
        rw [this, ticks_add]
      rw [hticks, run_append, run_ticks_one, step_wipe16 t (p + 1) (ht _), Option.bind_some]
      simpa [natInt_pred (p + 1) (by omega)] using ih

theorem step_wipe15 (t : Int → Fin 8) (p : ℕ) (ht : t (p : Int) ≠ 3) :
    step machine 0 ⟨15, natInt p, wipe t (p + 1)⟩ =
      some ⟨15, natInt p - 1, wipe t p⟩ := by
  have hne : wipe t (p + 1) (natInt p) ≠ 3 := wipe_nat_ne_L t (p + 1) p ht
  simp [step, rule_true_not _ hne, writtenTape, moveHead, wipe_update]

theorem wipe15_to_L (t : Int → Fin 8) (p : ℕ) (ht : ∀ i : ℕ, t (i : Int) ≠ 3) :
    run machine (ticks (p + 1)) ⟨15, natInt p, wipe t (p + 1)⟩ =
      some ⟨15, -1, wipe t 0⟩ := by
  induction p with
  | zero => rw [run_ticks_one, step_wipe15 t 0 (ht 0)]; simp [natInt_zero]
  | succ p ih =>
      have hticks : ticks (p + 1 + 1) = ticks 1 ++ ticks (p + 1) := by
        have : p + 1 + 1 = 1 + (p + 1) := by omega
        rw [this, ticks_add]
      rw [hticks, run_append, run_ticks_one, step_wipe15 t (p + 1) (ht _), Option.bind_some]
      simpa [natInt_pred (p + 1) (by omega)] using ih

theorem wipe0_boundary (t : Int → Fin 8) (hneg : ∀ z : Int, z < 0 → z ≠ -1 → t z = 2) :
    wipe t 0 = boundaryTape := by
  funext z
  unfold wipe boundaryTape
  by_cases hL : z = -1; · simp [hL]
  rw [if_neg hL, if_neg hL]
  by_cases hpos : 0 ≤ z
  · rw [dif_pos ⟨hpos, Nat.zero_le _⟩]
  · rw [dif_neg (fun h => hpos h.1), hneg z (by omega) hL]

theorem emit_false (t : Int → Fin 8)
    (hneg : ∀ z : Int, z < 0 → z ≠ -1 → t z = 2) :
    run machine (ticks 2) ⟨16, -1, wipe t 0⟩ = some (finalConfig false) := by
  have hb := wipe0_boundary t hneg
  have htape : Function.update boundaryTape (-1) 2 = inputTape machine ([] : List Bool) := by
    rw [boundary_erase_L, inputTape_nil]
  have h1 : step machine 0 ⟨16, -1, wipe t 0⟩ = some ⟨18, 0, Function.update boundaryTape (-1) 2⟩ := by
    rw [hb]
    simp [step, show boundaryTape (-1) = 3 from rfl, rule_falseL, writtenTape, moveHead]
  rw [show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append, run_ticks_one, h1, Option.bind_some,
    run_ticks_one]
  simp only [step, rule_emit0, writtenTape, moveHead, Option.map_some, finalConfig]
  rw [htape, inputTape_nil, show (0 : Fin 8) = enc false from rfl, emit_tape false]

theorem emit_true (t : Int → Fin 8)
    (hneg : ∀ z : Int, z < 0 → z ≠ -1 → t z = 2) :
    run machine (ticks 2) ⟨15, -1, wipe t 0⟩ = some (finalConfig true) := by
  have hb := wipe0_boundary t hneg
  have htape : Function.update boundaryTape (-1) 2 = inputTape machine ([] : List Bool) := by
    rw [boundary_erase_L, inputTape_nil]
  have h1 : step machine 0 ⟨15, -1, wipe t 0⟩ = some ⟨17, 0, Function.update boundaryTape (-1) 2⟩ := by
    rw [hb]
    simp [step, show boundaryTape (-1) = 3 from rfl, rule_trueL, writtenTape, moveHead]
  rw [show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append, run_ticks_one, h1, Option.bind_some,
    run_ticks_one]
  simp only [step, rule_emit1, writtenTape, moveHead, Option.map_some, finalConfig]
  rw [htape, inputTape_nil, show (1 : Fin 8) = enc true from rfl, emit_tape true]

theorem work_nat_ne_L (w : List Bool) (n i : ℕ) : workTape w n (i : Int) ≠ 3 := by
  unfold workTape workNat
  rw [if_neg (nat_ne_neg1 i), dif_pos (Nat.cast_nonneg i)]
  simp only [toNat_ofNat]
  by_cases hlt : i < n
  · rw [if_pos hlt]
    by_cases he : i % 2 = 0
    · rw [if_pos he]; decide
    · rw [if_neg he]
      by_cases hin : i < w.length
      · rw [dif_pos hin]; cases (w[i] : Bool) <;> (simp [enc]; decide)
      · rw [dif_neg hin]; decide
  · rw [if_neg hlt]
    unfold inputTape
    rw [dif_pos (Nat.cast_nonneg i)]
    simp only [toNat_ofNat]
    by_cases hin : i < w.length
    · rw [dif_pos hin]; cases (w[i] : Bool) <;> (simp [machine]; decide)
    · rw [dif_neg hin]; decide

theorem false_from (t : Int → Fin 8) (p : ℕ)
    (ht : ∀ i : ℕ, t (i : Int) ≠ 3)
    (hneg : ∀ z : Int, z < 0 → z ≠ -1 → t z = 2)
    (hL : t (-1) = 3) :
    run machine (ticks (p + 3)) ⟨16, natInt p, wipe t (p + 1)⟩ =
      some (finalConfig false) := by
  have hsplit : p + 3 = (p + 1) + 2 := by omega
  rw [show ticks (p + 3) = ticks (p + 1) ++ ticks 2 by rw [hsplit, ticks_add],
    run_append, wipe16_to_L t p ht, Option.bind_some, emit_false t hneg]

theorem true_from (t : Int → Fin 8) (p : ℕ)
    (ht : ∀ i : ℕ, t (i : Int) ≠ 3)
    (hneg : ∀ z : Int, z < 0 → z ≠ -1 → t z = 2)
    (hL : t (-1) = 3) :
    run machine (ticks (p + 3)) ⟨15, natInt p, wipe t (p + 1)⟩ =
      some (finalConfig true) := by
  have hsplit : p + 3 = (p + 1) + 2 := by omega
  rw [show ticks (p + 3) = ticks (p + 1) ++ ticks 2 by rw [hsplit, ticks_add],
    run_append, wipe15_to_L t p ht, Option.bind_some, emit_true t hneg]

theorem workTape_neg (w : List Bool) (n : ℕ) (z : Int) (hz : z < 0) (hL : z ≠ -1) :
    workTape w n z = 2 := by
  unfold workTape; rw [if_neg hL, dif_neg (not_le.mpr hz)]

theorem tape_far_blank (w : List Bool) :
    ∀ z : Int, 0 ≤ z → w.length ≤ z.toNat →
      Function.update (workTape w w.length) (natInt w.length) 2 z = 2 := by
  intro z hpos hp
  by_cases heq : z = natInt w.length
  · subst z; rw [Function.update_apply, if_pos rfl]
  · rw [Function.update_apply, if_neg heq]
    have hneL : z ≠ -1 := by intro h; subst z; omega
    unfold workTape workNat
    rw [if_neg hneL, dif_pos hpos, if_neg (Nat.not_lt.mpr hp)]
    have hzI : (w.length : Int) ≤ z := by
      have : (w.length : Int) ≤ (z.toNat : Int) := Nat.cast_le.mpr hp
      rwa [Int.toNat_of_nonneg hpos] at this
    simpa [Int.toNat_of_nonneg hpos, machine_blank] using
      inputTape_ge machine w z hzI

theorem parse_mal_from (w : List Bool) (n : ℕ) (hn : n ≤ w.length) (heven : n % 2 = 0)
    (hmal : unpairBits (w.drop n) = none) :
    ∃ p t, p ≤ w.length ∧
      run machine (ticks (w.length - n + 1)) ⟨4, natInt n, workTape w n⟩ =
        some ⟨16, natInt p - 1, t⟩ ∧
      (∀ i : ℕ, t (i : Int) ≠ 3) ∧ t (-1) = 3 ∧
      (∀ z : Int, z < 0 → z ≠ -1 → t z = 2) ∧
      (∀ z : Int, 0 ≤ z → p ≤ z.toNat → t z = 2) := by
  suffices hmain : ∀ d n, d = w.length - n → n ≤ w.length → n % 2 = 0 →
      unpairBits (w.drop n) = none →
      ∃ p t, p ≤ w.length ∧
        run machine (ticks (w.length - n + 1)) ⟨4, natInt n, workTape w n⟩ =
          some ⟨16, natInt p - 1, t⟩ ∧
        (∀ i : ℕ, t (i : Int) ≠ 3) ∧ t (-1) = 3 ∧
        (∀ z : Int, z < 0 → z ≠ -1 → t z = 2) ∧
        (∀ z : Int, 0 ≤ z → p ≤ z.toNat → t z = 2) by
    exact hmain (w.length - n) n rfl hn heven hmal
  intro d; induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hd hn heven hmal
    cases hdrop : w.drop n with
    | nil =>
        have heq : n = w.length := by have := List.drop_eq_nil_iff.mp hdrop; omega
        subst heq
        refine ⟨w.length, Function.update (workTape w w.length) (natInt w.length) 2, le_rfl, ?_, ?_, ?_, ?_, tape_far_blank w⟩
        · have hticks : w.length - w.length + 1 = 1 := by omega
          rw [hticks, run_ticks_one]; exact step_parse_blank w w.length le_rfl
        · intro i
          by_cases hz : natInt i = natInt w.length
          · rw [Function.update_apply, if_pos hz]; decide
          · rw [Function.update_apply, if_neg hz]; exact work_nat_ne_L w w.length i
        · have hne : (-1 : Int) ≠ natInt w.length := (natInt_ne_neg1 _).symm
          rw [Function.update_apply, if_neg hne]; rfl
        · intro z hz hL
          have hne : z ≠ natInt w.length := by intro h; simp [natInt] at h; omega
          rw [Function.update_apply, if_neg hne, workTape_neg w w.length z hz hL]
    | cons a rest =>
        obtain ⟨hlt, ha, htl⟩ := drop_head_eq w n a rest hdrop
        have hatrue : a = true := by
          cases a; · rw [hdrop] at hmal; simp [unpairBits] at hmal; contradiction
          rfl
        subst hatrue
        cases rest with
        | nil =>
            have hn1 : n + 1 = w.length := by
              have hlen : (w.drop n).length = 1 := by simp [hdrop]
              rw [List.length_drop] at hlen; omega
            refine ⟨w.length, Function.update (workTape w w.length) (natInt w.length) 2,
              le_rfl, ?_, ?_, ?_, ?_, tape_far_blank w⟩
            · have hticks : w.length - n + 1 = 2 := by omega
              rw [hticks, show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append, run_ticks_one,
                step_parse_true w n hlt ha heven, Option.bind_some, run_ticks_one]
              simp only [hn1]; exact step_pay_blank w w.length le_rfl
            · intro i
              by_cases hz : natInt i = natInt w.length
              · rw [Function.update_apply, if_pos hz]; decide
              · rw [Function.update_apply, if_neg hz]; exact work_nat_ne_L w w.length i
            · have hne : (-1 : Int) ≠ natInt w.length := (natInt_ne_neg1 _).symm
              rw [Function.update_apply, if_neg hne]; rfl
            · intro z hz hL
              have hne : z ≠ natInt w.length := by intro h; simp [natInt] at h; omega
              rw [Function.update_apply, if_neg hne, workTape_neg w w.length z hz hL]
        | cons b rest =>
            have hlt2 : n + 1 < w.length := by
              have hlen : (w.drop n).length = rest.length + 2 := by simp [hdrop]
              rw [List.length_drop] at hlen; omega
            have ho : (n + 1) % 2 = 1 := by omega
            obtain ⟨_, _, htl2⟩ := drop_head_eq w (n + 1) b rest htl
            have hmal' : unpairBits (w.drop (n + 2)) = none := by
              have : n + 2 = n + 1 + 1 := by omega
              rw [this, htl2]
              rw [hdrop] at hmal; simp [unpairBits] at hmal
              cases hrest : unpairBits rest with
              | none => rfl
              | some z => simp [hrest] at hmal; contradiction
            have hsplit : w.length - n + 1 = 2 + (w.length - (n + 2) + 1) := by omega
            obtain ⟨p, t, hp, hrun, ht, hL, hneg, hfar⟩ :=
              ih (w.length - (n + 2)) (by omega) (n + 2) rfl (by omega) (by omega) hmal'
            refine ⟨p, t, hp, ?_, ht, hL, hneg, hfar⟩
            rw [show ticks (w.length - n + 1) = ticks 2 ++ ticks (w.length - (n + 2) + 1) by
              rw [hsplit, ticks_add]]
            rw [run_append, show ticks 2 = ticks 1 ++ ticks 1 from rfl, run_append, run_ticks_one,
              step_parse_true w n hlt ha heven, Option.bind_some, run_ticks_one,
              step_pay w (n + 1) hlt2 ho, Option.bind_some, hrun]

theorem wipe_id (t : Int → Fin 8) (p : ℕ) (hL : t (-1) = 3)
    (hfar : ∀ z : Int, 0 ≤ z → p ≤ z.toNat → t z = 2) : wipe t p = t := by
  funext z
  unfold wipe
  by_cases hLz : z = -1; · simp [hLz, hL]
  rw [if_neg hLz]
  by_cases hcond : 0 ≤ z ∧ p ≤ z.toNat
  · rw [dif_pos hcond, hfar z hcond.1 hcond.2]
  · rw [dif_neg hcond]

theorem mal_false (w : List Bool) (h : unpairBits w = none) :
    ∃ n ≤ 2 * w.length + 6,
      run machine (ticks n) (initial machine w) = some (finalConfig false) := by
  obtain ⟨p, t, hp, hparse, ht, hL, hneg, hfar⟩ :=
    parse_mal_from w 0 (Nat.zero_le _) (by decide) (by simpa using h)
  have hhead : ({ state := (4 : Fin 19), head := (0 : Int), tape := workTape w 0 } :
      Configuration 19 8) = ⟨4, natInt 0, workTape w 0⟩ := by simp [natInt_zero]
  by_cases hz : p = 0
  · subst p
    refine ⟨2 + (w.length - 0 + 1) + 2, by omega, ?_⟩
    have hhd : natInt 0 - 1 = (-1 : Int) := by simp [natInt]
    rw [show ticks (2 + (w.length - 0 + 1) + 2) =
          ticks 2 ++ ticks (w.length - 0 + 1) ++ ticks 2 by
        simp [ticks_add, List.append_assoc]]
    rw [run_append, run_append, setup2, Option.bind_some, hhead, hparse, Option.bind_some]
    rw [hhd, show t = wipe t 0 from (wipe_id t 0 hL hfar).symm]
    exact emit_false t hneg
  · have hp0 : 1 ≤ p := Nat.pos_of_ne_zero hz
    refine ⟨2 + (w.length - 0 + 1) + ((p - 1) + 3), by omega, ?_⟩
    rw [show ticks (2 + (w.length - 0 + 1) + ((p - 1) + 3)) =
          ticks 2 ++ ticks (w.length - 0 + 1) ++ ticks ((p - 1) + 3) by
        simp [ticks_add, List.append_assoc]]
    rw [run_append, run_append, setup2, Option.bind_some, hhead, hparse, Option.bind_some]
    rw [natInt_pred p hp0, show t = wipe t p from (wipe_id t p hL hfar).symm]
    have hpe : p - 1 + 1 = p := Nat.sub_add_cancel hp0
    simpa [hpe] using false_from t (p - 1) ht hneg hL

theorem output_final (b : Bool) : Output machine [b] (finalConfig b) :=
  ⟨rfl, rfl, rfl⟩

theorem bound_linear (n : ℕ) : 2 * n + 6 ≤ 128 * (n + 1) * (n + 1) := by
  nlinarith

theorem mal_output (w : List Bool) (h : unpairBits w = none) :
    ∃ n ≤ 128 * (w.length + 1) * (w.length + 1),
      run machine (ticks n) (initial machine w) = some (finalConfig false) ∧
        Output machine (compareBits w) (finalConfig false) := by
  obtain ⟨n, hn, hrun⟩ := mal_false w h
  refine ⟨n, Nat.le_trans hn (bound_linear w.length), hrun, ?_⟩
  simpa [compareBits, h] using output_final false

theorem budget_at (x y : List Bool) (k : ℕ) (u : List Bool) (i : ℕ) :
    budgetTape x y k u (natInt i) = budgetNat x y k u i := by
  unfold budgetTape natInt
  rw [if_neg (nat_ne_neg1 i), dif_pos (Nat.cast_nonneg i), toNat_ofNat]

theorem budget_L (x y : List Bool) (k : ℕ) (u : List Bool) :
    budgetTape x y k u (-1) = 3 := rfl

theorem budget_consumed (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hj : j < k) : budgetTape x y k u (natInt (D x + 1 + j)) = 6 := by
  rw [budget_at]; unfold budgetNat
  have hne : D x + 1 + j ≠ D x := by omega
  have hlt : ¬ D x + 1 + j < D x := by omega
  have hk : D x + 1 + j < D x + 1 + k := by omega
  rw [if_neg hlt, if_neg hne, if_pos hk]

theorem budget_E (x y : List Bool) (k : ℕ) (u : List Bool) (hk : k ≤ y.length) :
    budgetTape x y k u (natInt (Eidx x y)) = 5 := by
  rw [budget_at]; unfold budgetNat
  have hlt : ¬ Eidx x y < D x := by simp [D, Eidx]; omega
  have hne : Eidx x y ≠ D x := by simp [D, Eidx]; omega
  have hk' : ¬ Eidx x y < D x + 1 + k := by simp [D, Eidx]; omega
  rw [if_neg hlt, if_neg hne, if_neg hk', if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem budget_y_cell (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hk : k ≤ j) (hj : j < y.length) :
    budgetTape x y k u (natInt (D x + 1 + j)) = enc y[j] := by
  rw [budget_at]; unfold budgetNat
  have hlt : ¬ D x + 1 + j < D x := by omega
  have hne : D x + 1 + j ≠ D x := by omega
  have hk' : ¬ D x + 1 + j < D x + 1 + k := by omega
  have hy : D x + 1 + j < Eidx x y := by simp [Eidx, D]; omega
  rw [if_neg hlt, if_neg hne, if_neg hk', if_pos hy]
  have hj' : D x + 1 + j - (D x + 1) < y.length := by omega
  rw [dif_pos hj']; simp [Nat.add_sub_cancel]

theorem skip_consumed (x y : List Bool) (k : ℕ) (u : List Bool) (_hk : k ≤ y.length) :
    run machine (ticks k) ⟨8, natInt (D x + 1), budgetTape x y k u⟩ =
      some ⟨8, natInt (D x + 1 + k), budgetTape x y k u⟩ := by
  have hs := scan_right (M := machine) (q := (8 : Fin 19)) (t := budgetTape x y k u)
    (h := natInt (D x + 1)) (n := k)
  have hc : natInt (D x + 1) + (k : Int) = natInt (D x + 1 + k) := by unfold natInt; omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hp : natInt (D x + 1) + (i : Int) = natInt (D x + 1 + i) := by unfold natInt; omega
  rw [hp, budget_consumed x y k u i hi]
  exact rule_skip6

theorem consume_write (x y : List Bool) (k : ℕ) (u : List Bool) (_hk : k < y.length) :
    Function.update (budgetTape x y k u) (natInt (D x + 1 + k)) 6 =
      budgetTape x y (k + 1) u := by
  funext z
  by_cases hz : z = natInt (D x + 1 + k)
  · subst z
    rw [Function.update_apply, if_pos rfl, budget_at]
    unfold budgetNat
    have hlt : ¬ D x + 1 + k < D x := by omega
    have hne : D x + 1 + k ≠ D x := by omega
    have hk' : D x + 1 + k < D x + 1 + (k + 1) := by omega
    rw [if_neg hlt, if_neg hne, if_pos hk']
  · rw [Function.update_apply, if_neg hz]
    unfold budgetTape
    by_cases hL : z = -1; · simp [hL]
    rw [if_neg hL, if_neg hL]
    by_cases hpos : 0 ≤ z
    · rw [dif_pos hpos, dif_pos hpos]
      unfold budgetNat
      have hne : z.toNat ≠ D x + 1 + k := by
        intro heq; exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
      by_cases h1 : z.toNat < D x
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : z.toNat = D x
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : z.toNat < D x + 1 + k
          · rw [if_pos h3, if_pos (by omega : z.toNat < D x + 1 + (k + 1))]
          · rw [if_neg h3]
            by_cases h3' : z.toNat < D x + 1 + (k + 1)
            · omega
            · rw [if_neg h3']
    · rw [dif_neg hpos, dif_neg hpos]

theorem consume_step (x y : List Bool) (k : ℕ) (u : List Bool) (hk : k < y.length) :
    step machine 0 ⟨8, natInt (D x + 1 + k), budgetTape x y k u⟩ =
      some ⟨9, natInt (D x + k), budgetTape x y (k + 1) u⟩ := by
  have hread := budget_y_cell x y k u k le_rfl hk
  have hbit : enc y[k] = 0 ∨ enc y[k] = 1 := by cases (y[k] : Bool) <;> simp
  have hhead : natInt (D x + 1 + k) - 1 = natInt (D x + k) := by unfold natInt; omega
  simp only [step, hread, rule_consume _ hbit, writtenTape, moveHead, Option.map_some]
  rw [consume_write x y k u hk, hhead]

theorem exhaust_step (x y : List Bool) (u : List Bool) :
    step machine 0 ⟨8, natInt (Eidx x y), budgetTape x y y.length u⟩ =
      some ⟨16, natInt (Eidx x y) - 1,
        Function.update (budgetTape x y y.length u) (natInt (Eidx x y)) 2⟩ := by
  have hread := budget_E x y y.length u le_rfl
  simp [step, hread, rule_exhaust, writtenTape, moveHead]

end PakFixedPolyomino.StandardBitUnaryBudgetCompare
