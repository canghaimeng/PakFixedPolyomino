import PakFixedPolyomino.StandardBitPairProjection
import Mathlib.Tactic

/-! First-component parser: physical setup to marked copyTape, and malformed wipe. -/
namespace PakFixedPolyomino.StandardBitPairFirst

open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape Config)
open StandardBitPairProjection
  (pairBits_marker pairBits_payload pairBits_sep pairBits_y
    unpairBits_none_form natInt nat_cast_succ nat_cast_pred
    nat_ne_neg1 natInt_pred natInt_zero natInt_ne_neg1 natInt_succ
    toNat_ofNat update_same drop_eq_cons drop_head_eq)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def enc (b : Bool) : Fin 8 := if b then 1 else 0
def mark (b : Bool) : Fin 8 := if b then 7 else 6
@[simp] theorem enc_false : enc false = 0 := rfl
@[simp] theorem enc_true : enc true = 1 := rfl
@[simp] theorem mark_false : mark false = 6 := rfl
@[simp] theorem mark_true : mark true = 7 := rfl
def D (x : List Bool) : ℕ := 2 * x.length + 1

def machine : DeterministicMachine 17 8 where
  rule := fun q a _ =>
    if q = 2 then some { write := a, target := 3, move := .left }
    else if q = 3 then some { write := 3, target := 4, move := .right }
    else if q = 4 then
      if a = 1 then some { write := 2, target := 5, move := .right }
      else if a = 0 then some { write := 2, target := 6, move := .right }
      else if a = 2 then some { write := 2, target := 16, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 5 then
      if a = 0 then some { write := 6, target := 4, move := .right }
      else if a = 1 then some { write := 7, target := 4, move := .right }
      else if a = 2 then some { write := 2, target := 16, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 6 then
      if a = 0 ∨ a = 1 then some { write := 2, target := 6, move := .right }
      else if a = 2 then some { write := 5, target := 7, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 7 then
      if a = 3 then some { write := 3, target := 8, move := .right }
      else some { write := a, target := 7, move := .left }
    else if q = 8 then some { write := 4, target := 9, move := .stay }
    else if q = 9 then
      if a = 6 then some { write := 2, target := 10, move := .left }
      else if a = 7 then some { write := 2, target := 11, move := .left }
      else if a = 5 then some { write := 2, target := 13, move := .left }
      else some { write := a, target := 9, move := .right }
    else if q = 10 then
      if a = 4 then some { write := 0, target := 12, move := .right }
      else some { write := a, target := 10, move := .left }
    else if q = 11 then
      if a = 4 then some { write := 1, target := 12, move := .right }
      else some { write := a, target := 11, move := .left }
    else if q = 12 then some { write := 4, target := 9, move := .stay }
    else if q = 13 then
      if a = 4 then some { write := 2, target := 14, move := .left }
      else some { write := a, target := 13, move := .left }
    else if q = 14 then
      if a = 3 then some { write := 2, target := 0, move := .right }
      else some { write := a, target := 14, move := .left }
    else if q = 15 then
      if a = 2 then some { write := 2, target := 16, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 16 then
      if a = 3 then some { write := 2, target := 0, move := .right }
      else some { write := 2, target := 16, move := .left }
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

@[simp] theorem machine_zero : machine.zero = 0 := rfl
@[simp] theorem machine_one : machine.one = 1 := rfl
@[simp] theorem machine_blank : machine.blank = 2 := rfl
@[simp] theorem machine_accept : machine.accept = 0 := rfl
@[simp] theorem machine_start : machine.start = 2 := rfl

theorem rule_start (a : Fin 8) :
    machine.rule 2 a 0 = some { write := a, target := 3, move := .left } := by simp [machine]
theorem rule_markL (a : Fin 8) :
    machine.rule 3 a 0 = some { write := 3, target := 4, move := .right } := by simp [machine]
theorem rule_parse_one :
    machine.rule 4 1 0 = some { write := 2, target := 5, move := .right } := by simp [machine]
theorem rule_parse_zero :
    machine.rule 4 0 0 = some { write := 2, target := 6, move := .right } := by simp [machine]
theorem rule_parse_blank :
    machine.rule 4 2 0 = some { write := 2, target := 16, move := .left } := by simp [machine]
theorem rule_parseBit_false :
    machine.rule 5 0 0 = some { write := 6, target := 4, move := .right } := by simp [machine]
theorem rule_parseBit_true :
    machine.rule 5 1 0 = some { write := 7, target := 4, move := .right } := by simp [machine]
theorem rule_parseBit_blank :
    machine.rule 5 2 0 = some { write := 2, target := 16, move := .left } := by simp [machine]
theorem rule_toEnd_bit (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 6 a 0 = some { write := 2, target := 6, move := .right } := by
  rcases h with h | h <;> simp [machine, h]
theorem rule_toEnd_blank :
    machine.rule 6 2 0 = some { write := 5, target := 7, move := .left } := by simp [machine]
theorem rule_seekL_L :
    machine.rule 7 3 0 = some { write := 3, target := 8, move := .right } := by simp [machine]
theorem rule_seekL_notL (a : Fin 8) (h : a ≠ 3) :
    machine.rule 7 a 0 = some { write := a, target := 7, move := .left } := by simp [machine, h]
theorem rule_markDest (a : Fin 8) :
    machine.rule 8 a 0 = some { write := 4, target := 9, move := .stay } := by simp [machine]
theorem rule_malLeft_L :
    machine.rule 16 3 0 = some { write := 2, target := 0, move := .right } := by simp [machine]
theorem rule_malLeft_notL (a : Fin 8) (h : a ≠ 3) :
    machine.rule 16 a 0 = some { write := 2, target := 16, move := .left } := by simp [machine, h]

set_option simprocs false

theorem read_bit (w : List Bool) (i : ℕ) (hi : i < w.length) :
    inputTape machine w i = enc w[i] := by simp [inputTape, enc, hi]

def copyTape (x y : List Bool) (k : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then
    if h1 : z.toNat < k ∧ z.toNat < x.length then enc x[z.toNat]
    else if z = (k : Int) then 4
    else if z = ((pairBits x y).length : Int) then 5
    else if h5 : z.toNat % 2 = 1 ∧ k ≤ z.toNat / 2 ∧ z.toNat / 2 < x.length then
      mark x[z.toNat / 2]
    else 2
  else 2

def copyConfig (x y : List Bool) (k : ℕ) : Configuration 17 8 := ⟨9, k, copyTape x y k⟩
def finalConfig (M : DeterministicMachine 17 8) (y : List Bool) : Configuration 17 8 :=
  ⟨M.accept, 0, inputTape M y⟩

def workNat (w : List Bool) (n i : ℕ) : Fin 8 :=
  if i < n then
    if i % 2 = 1 then (if h : i < w.length then mark w[i] else 2) else 2
  else inputTape machine w i

def workTape (w : List Bool) (n : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then workNat w n z.toNat
  else 2

def skipNat (x y : List Bool) (j i : ℕ) : Fin 8 :=
  if i < D x then workNat (pairBits x y) (D x) i
  else if i < D x + j then 2
  else inputTape machine (pairBits x y) i

def skipTape (x y : List Bool) (j : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then skipNat x y j z.toNat
  else 2

def endedTape (x y : List Bool) : Int → Fin 8 :=
  Function.update (skipTape x y y.length) (natInt (D x + y.length)) 5
def boundaryTape (z : Int) : Fin 8 := if z = -1 then 3 else 2
def markedTape (w : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3 else inputTape machine w z

theorem inputTape_nil : inputTape machine ([] : List Bool) = fun _ => (2 : Fin 8) := by
  funext z; unfold inputTape; by_cases hpos : 0 ≤ z <;> simp [hpos]
theorem boundary_erase_L :
    Function.update boundaryTape (-1) 2 = fun _ => (2 : Fin 8) := by
  funext z; by_cases hz : z = -1 <;> simp [Function.update_apply, boundaryTape, hz]

theorem marked_eq_work0 (w : List Bool) : markedTape w = workTape w 0 := by
  funext z; unfold markedTape workTape workNat
  by_cases hL : z = -1; · simp [hL]
  rw [if_neg hL, if_neg hL]; by_cases hpos : 0 ≤ z
  · rw [dif_pos hpos, if_neg (Nat.not_lt_zero _), Int.toNat_of_nonneg hpos]
  · rw [dif_neg hpos]; rw [inputTape_neg machine w z (not_le.mp hpos)]; rfl

theorem work_ge (w : List Bool) (n i : ℕ) (hi : n ≤ i) :
    workTape w n (i : Int) = inputTape machine w (i : Int) := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold workTape workNat
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i)]
  simp [toNat_ofNat, Nat.not_lt.mpr hi]

theorem work_write (w : List Bool) (n : ℕ) :
    Function.update (workTape w n) (natInt n)
      (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) =
      workTape w (n + 1) := by
  funext z
  by_cases hz : z = natInt n
  · subst z
    have hL : natInt n ≠ -1 := natInt_ne_neg1 n
    unfold workTape workNat
    rw [Function.update_apply, if_pos rfl, if_neg hL, dif_pos (Nat.cast_nonneg n)]
    simp [natInt, toNat_ofNat, Nat.lt_succ_self n]
  · rw [Function.update_apply, if_neg hz]
    unfold workTape
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        unfold workNat
        have hne : z.toNat ≠ n := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
        by_cases hlt : z.toNat < n
        · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
        · rw [if_neg hlt, if_neg (by omega : ¬ z.toNat < n + 1)]
      · rw [dif_neg hpos, dif_neg hpos]

theorem work_nat_ne_L (w : List Bool) (n i : ℕ) : workTape w n (i : Int) ≠ 3 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold workTape workNat inputTape
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i)]; simp [toNat_ofNat]
  split_ifs <;> try decide
  cases (w[i] : Bool) <;> decide

theorem skip_write (x y : List Bool) (j : ℕ) :
    Function.update (skipTape x y j) (natInt (D x + j)) 2 = skipTape x y (j + 1) := by
  funext z
  by_cases hz : z = natInt (D x + j)
  · subst z
    have hL : natInt (D x + j) ≠ -1 := natInt_ne_neg1 _
    have hpos : 0 ≤ natInt (D x + j) := Nat.cast_nonneg _
    unfold skipTape skipNat
    rw [Function.update_apply, if_pos rfl, if_neg hL, dif_pos hpos]
    have hto : (natInt (D x + j)).toNat = D x + j := toNat_ofNat _
    rw [hto, if_neg (by omega : ¬ D x + j < D x),
      if_pos (by omega : D x + j < D x + (j + 1))]
  · rw [Function.update_apply, if_neg hz]
    unfold skipTape
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        unfold skipNat
        have hne : z.toNat ≠ D x + j := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt heq))
        by_cases hx : z.toNat < D x
        · rw [if_pos hx, if_pos hx]
        · rw [if_neg hx, if_neg hx]
          by_cases hlt : z.toNat < D x + j
          · rw [if_pos hlt, if_pos (by omega : z.toNat < D x + (j + 1))]
          · rw [if_neg hlt, if_neg (by omega : ¬ z.toNat < D x + (j + 1))]
      · rw [dif_neg hpos, dif_neg hpos]

theorem skip_ge (x y : List Bool) (j i : ℕ) (hi : D x + j ≤ i) :
    skipTape x y j (i : Int) = inputTape machine (pairBits x y) (i : Int) := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold skipTape skipNat
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i), toNat_ofNat,
    if_neg (by omega : ¬ i < D x), if_neg (by omega : ¬ i < D x + j)]

theorem skip_nat_ne_L (x y : List Bool) (j i : ℕ) : skipTape x y j (i : Int) ≠ 3 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold skipTape skipNat
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i)]; simp [toNat_ofNat]
  by_cases hx : i < D x
  · have ht := work_nat_ne_L (pairBits x y) (D x) i
    unfold workTape at ht
    rw [if_neg hL, dif_pos (Nat.cast_nonneg i)] at ht
    simpa [hx, toNat_ofNat] using ht
  · split_ifs <;> try decide
    unfold inputTape; split_ifs <;> decide

theorem work_eq_skip0 (x y : List Bool) :
    workTape (pairBits x y) (D x) = skipTape x y 0 := by
  funext z
  unfold workTape skipTape
  by_cases hL : z = -1; · simp [hL]
  rw [if_neg hL, if_neg hL]
  by_cases hpos : 0 ≤ z
  · rw [dif_pos hpos, dif_pos hpos]; unfold skipNat
    by_cases hlt : z.toNat < D x
    · rw [if_pos hlt]
    · rw [if_neg hlt, if_neg (by omega : ¬ z.toNat < D x + 0)]
      unfold workNat; simp [hlt]
  · rw [dif_neg hpos, dif_neg hpos]

theorem step_start (w : List Bool) :
    step machine 0 (initial machine w) =
      some { state := 3, head := -1, tape := inputTape machine w } := by
  simp [step, initial, rule_start, writtenTape, moveHead, update_same]
theorem step_markL (w : List Bool) :
    step machine 0 { state := 3, head := -1, tape := inputTape machine w } =
      some { state := 4, head := 0, tape := markedTape w } := by
  have hblank : inputTape machine w (-1) = 2 := inputTape_neg machine w (-1) (by omega)
  have htape : Function.update (inputTape machine w) (-1) 3 = markedTape w := by
    funext z; simp [Function.update_apply, markedTape]
  simp [step, hblank, rule_markL, writtenTape, moveHead, htape]
theorem setup2 (w : List Bool) :
    run machine (ticks 2) (initial machine w) =
      some { state := 4, head := 0, tape := workTape w 0 } := by
  have hsplit : (2 : ℕ) = 1 + 1 := rfl
  rw [hsplit, ticks_add, run_append, run_ticks_one, step_start, Option.bind_some,
    run_ticks_one, step_markL]; simp [marked_eq_work0]

theorem step_parse_true (w : List Bool) (n : ℕ) (hn : n < w.length) (ht : w[n] = true)
    (he : n % 2 = 0) :
    step machine 0 { state := 4, head := natInt n, tape := workTape w n } =
      some { state := 5, head := natInt (n + 1), tape := workTape w (n + 1) } := by
  have hread : workTape w n (n : Int) = 1 := by
    rw [work_ge w n n le_rfl, read_bit w n hn, ht, enc_true]
  have hv : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (2 : Fin 8) := by
    simp [he]
  simp only [step, hread, rule_parse_one, writtenTape, moveHead, Option.map_some]
  rw [← hv, work_write, natInt_succ]

theorem step_parse_false (w : List Bool) (n : ℕ) (hn : n < w.length) (ht : w[n] = false)
    (he : n % 2 = 0) :
    step machine 0 { state := 4, head := natInt n, tape := workTape w n } =
      some { state := 6, head := natInt (n + 1), tape := workTape w (n + 1) } := by
  have hread : workTape w n (n : Int) = 0 := by
    rw [work_ge w n n le_rfl, read_bit w n hn, ht, enc_false]
  have hv : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (2 : Fin 8) := by
    simp [he]
  simp only [step, hread, rule_parse_zero, writtenTape, moveHead, Option.map_some]
  rw [← hv, work_write, natInt_succ]

theorem step_parse_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 { state := 4, head := natInt n, tape := workTape w n } =
      some (Config.mk 16 (natInt n - 1) (workTape w (n + 1))) := by
  have hread : workTape w n (n : Int) = 2 := by
    rw [work_ge w n n le_rfl, inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn), machine_blank]
  have hv : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (2 : Fin 8) := by
    by_cases hodd : n % 2 = 1
    · have hin : ¬ n < w.length := Nat.not_lt.mpr hn; simp [hodd, hin]
    · simp [hodd]
  simp only [step, hread, rule_parse_blank, writtenTape, moveHead, Option.map_some]
  rw [← hv, work_write]

theorem step_parseBit (w : List Bool) (n : ℕ) (hn : n < w.length) (ho : n % 2 = 1) :
    step machine 0 { state := 5, head := natInt n, tape := workTape w n } =
      some { state := 4, head := natInt (n + 1), tape := workTape w (n + 1) } := by
  have hread : workTape w n (n : Int) = enc w[n] := by
    rw [work_ge w n n le_rfl, read_bit w n hn]
  have hv : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = mark w[n] := by
    simp [ho, hn]
  cases hb : w[n]
  · simp only [step, hread, hb, enc_false, rule_parseBit_false, writtenTape, moveHead,
      Option.map_some, mark_false]
    have : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (6 : Fin 8) := by
      simpa [hb, mark_false] using hv
    rw [← this, work_write, natInt_succ]
  · simp only [step, hread, hb, enc_true, rule_parseBit_true, writtenTape, moveHead,
      Option.map_some, mark_true]
    have : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (7 : Fin 8) := by
      simpa [hb, mark_true] using hv
    rw [← this, work_write, natInt_succ]

theorem step_parseBit_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 { state := 5, head := natInt n, tape := workTape w n } =
      some (Config.mk 16 (natInt n - 1) (workTape w (n + 1))) := by
  have hread : workTape w n (n : Int) = 2 := by
    rw [work_ge w n n le_rfl, inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn), machine_blank]
  have hv : (if n % 2 = 1 then (if h : n < w.length then mark w[n] else 2) else 2) = (2 : Fin 8) := by
    by_cases hodd : n % 2 = 1
    · have hin : ¬ n < w.length := Nat.not_lt.mpr hn; simp [hodd, hin]
    · simp [hodd]
  simp only [step, hread, rule_parseBit_blank, writtenTape, moveHead, Option.map_some]
  rw [← hv, work_write]

theorem parse_x (x y : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    run machine (ticks (2 * k)) { state := 4, head := 0, tape := workTape (pairBits x y) 0 } =
      some { state := 4, head := natInt (2 * k), tape := workTape (pairBits x y) (2 * k) } := by
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
        Option.bind_some, run_ticks_one, step_parseBit (pairBits x y) (2 * k + 1) h2s ho]

theorem parse_sep (x y : List Bool) :
    step machine 0 { state := 4, head := natInt (2 * x.length), tape := workTape (pairBits x y) (2 * x.length) } =
      some { state := 6, head := natInt (D x), tape := skipTape x y 0 } := by
  have hn : 2 * x.length < (pairBits x y).length := by have := pairBits_length x y; omega
  have hf := pairBits_sep x y
  have he : (2 * x.length) % 2 = 0 := by omega
  have hstep := step_parse_false (pairBits x y) (2 * x.length) hn hf he
  have hD : 2 * x.length + 1 = D x := rfl
  rw [hD, work_eq_skip0] at hstep
  exact hstep

theorem step_skip_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    step machine 0 { state := 6, head := natInt (D x + j), tape := skipTape x y j } =
      some { state := 6, head := natInt (D x + j + 1), tape := skipTape x y (j + 1) } := by
  have hidx : D x + j < (pairBits x y).length := by
    simp [D]; have := pairBits_length x y; omega
  have hy : (pairBits x y)[D x + j]'hidx = y[j] := by
    simpa [D, Nat.add_assoc] using pairBits_y x y j hj
  have hread : skipTape x y j (natInt (D x + j)) = enc y[j] := by
    simpa [natInt, hy] using (skip_ge x y j (D x + j) le_rfl).trans (read_bit _ _ hidx)
  have hbit : enc y[j] = 0 ∨ enc y[j] = 1 := by cases (y[j] : Bool) <;> simp
  simp only [step, hread, rule_toEnd_bit _ hbit, writtenTape, moveHead, Option.map_some]
  simp only [skip_write, natInt_succ, Nat.add_assoc]

theorem skip_y (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    run machine (ticks j) { state := 6, head := natInt (D x), tape := skipTape x y 0 } =
      some { state := 6, head := natInt (D x + j), tape := skipTape x y j } := by
  induction j with
  | zero => simp [ticks]
  | succ j ih =>
      have hticks : ticks (j + 1) = ticks j ++ ticks 1 := ticks_add j 1
      rw [hticks, run_append, ih (by omega), Option.bind_some, run_ticks_one,
        step_skip_y x y j (by omega)]
      simp [Nat.add_assoc]

theorem step_markE (x y : List Bool) :
    step machine 0 { state := 6, head := natInt (D x + y.length), tape := skipTape x y y.length } =
      some { state := 7, head := natInt (D x + y.length - 1), tape := endedTape x y } := by
  have hge : (pairBits x y).length ≤ D x + y.length := by simp [D]
  have hread : skipTape x y y.length (natInt (D x + y.length)) = 2 := by
    simpa [natInt] using (skip_ge x y y.length (D x + y.length) le_rfl).trans
      (inputTape_ge machine (pairBits x y) _ (Nat.cast_le.mpr hge))
  have hD : 1 ≤ D x + y.length := by simp [D]; omega
  simp only [step, hread, rule_toEnd_blank, writtenTape, moveHead, endedTape, Option.map_some]
  simp only [natInt_pred (D x + y.length) hD]

theorem ended_nat_ne_L (x y : List Bool) (i : ℕ) : endedTape x y (i : Int) ≠ 3 := by
  unfold endedTape
  by_cases hz : natInt i = natInt (D x + y.length)
  · rw [Function.update_apply, if_pos hz]; decide
  · rw [Function.update_apply, if_neg hz]; exact skip_nat_ne_L x y y.length i

theorem ended_L (x y : List Bool) : endedTape x y (-1) = 3 := by
  unfold endedTape
  have hne : (-1 : Int) ≠ natInt (D x + y.length) := (natInt_ne_neg1 _).symm
  rw [Function.update_apply, if_neg hne]; rfl

theorem step_seekL_nat (x y : List Bool) (p : ℕ) :
    step machine 0 { state := 7, head := natInt p, tape := endedTape x y } =
      some { state := 7, head := natInt p - 1, tape := endedTape x y } := by
  have ht : endedTape x y (natInt p) ≠ 3 := ended_nat_ne_L x y p
  simp [step, rule_seekL_notL _ ht, writtenTape, moveHead, update_same]

theorem seekL_to_neg1 (x y : List Bool) (p : ℕ) :
    run machine (ticks (p + 1)) { state := 7, head := natInt p, tape := endedTape x y } =
      some { state := 7, head := -1, tape := endedTape x y } := by
  induction p with
  | zero => rw [run_ticks_one, step_seekL_nat x y 0]; simp [natInt_zero]
  | succ p ih =>
      have hticks : ticks (p + 1 + 1) = ticks 1 ++ ticks (p + 1) := by
        have : p + 1 + 1 = 1 + (p + 1) := by omega
        rw [this, ticks_add]
      rw [hticks, run_append, run_ticks_one, step_seekL_nat x y (p + 1), Option.bind_some]
      simpa [natInt_pred (p + 1) (by omega)] using ih

theorem step_seekL_boundary (x y : List Bool) :
    step machine 0 { state := 7, head := -1, tape := endedTape x y } =
      some { state := 8, head := 0, tape := endedTape x y } := by
  simp [step, ended_L, rule_seekL_L, writtenTape, moveHead, update_same]

theorem seekL_all (x y : List Bool) :
    run machine (ticks (D x + y.length + 1))
        { state := 7, head := natInt (D x + y.length - 1), tape := endedTape x y } =
      some { state := 8, head := 0, tape := endedTape x y } := by
  have hn : 1 ≤ D x + y.length := by simp [D]; omega
  rw [show ticks (D x + y.length + 1) = ticks (D x + y.length - 1 + 1) ++ ticks 1 by
        have : D x + y.length + 1 = (D x + y.length - 1 + 1) + 1 := by omega
        rw [this, ticks_add],
    run_append, seekL_to_neg1 x y (D x + y.length - 1), Option.bind_some,
    run_ticks_one, step_seekL_boundary]

theorem copyTape_of_ended (x y : List Bool) :
    Function.update (endedTape x y) (0 : Int) 4 = copyTape x y 0 := by
  funext z
  have hlen : (pairBits x y).length = D x + y.length := by simp [D, pairBits_length]
  have hEidx : natInt (D x + y.length) = ((pairBits x y).length : Int) := by simp [natInt, hlen]
  by_cases h0 : z = (0 : Int)
  · subst z
    rw [Function.update_apply, if_pos rfl]
    unfold copyTape; split_ifs <;> first | rfl | omega
  · rw [Function.update_apply, if_neg h0]; unfold endedTape
    by_cases hL : z = -1
    · rw [hL]
      have hne : (-1 : Int) ≠ natInt (D x + y.length) := (natInt_ne_neg1 _).symm
      rw [Function.update_apply, if_neg hne]; unfold skipTape copyTape; rfl
    · by_cases hE : z = natInt (D x + y.length)
      · subst z
        rw [Function.update_apply, if_pos rfl]
        unfold copyTape
        rw [if_neg (natInt_ne_neg1 _), dif_pos (Nat.cast_nonneg _)]
        have hn1E : ¬ ((natInt (D x + y.length)).toNat < 0 ∧
            (natInt (D x + y.length)).toNat < x.length) := by simp [natInt, toNat_ofNat]
        rw [dif_neg hn1E, if_neg (show natInt (D x + y.length) ≠ ((0 : ℕ) : Int) from h0), if_pos hEidx]
      · rw [Function.update_apply, if_neg hE]
        unfold skipTape copyTape
        rw [if_neg hL, if_neg hL]
        by_cases hpos : 0 ≤ z
        · rw [dif_pos hpos, dif_pos hpos]; unfold skipNat
          have hn1 : ¬ (z.toNat < 0 ∧ z.toNat < x.length) := fun h => Nat.not_lt_zero _ h.1
          have hne0 : z ≠ ((0 : ℕ) : Int) := h0
          have hneE : z ≠ ((pairBits x y).length : Int) := fun hz => hE (hz.trans hEidx.symm)
          by_cases hxD : z.toNat < D x
          · rw [if_pos hxD]; unfold workNat; rw [if_pos hxD]
            by_cases hodd : z.toNat % 2 = 1
            · have hx : z.toNat / 2 < x.length := by simp [D] at hxD; omega
              have hi : z.toNat < (pairBits x y).length := by
                have := pairBits_length x y; omega
              have hpay := pairBits_payload x y (z.toNat / 2) hx
              have hidx : z.toNat = 2 * (z.toNat / 2) + 1 := by
                have hmod := Nat.div_add_mod z.toNat 2; rw [hodd] at hmod; exact hmod.symm
              have hbits : (pairBits x y)[z.toNat]'hi = x[z.toNat / 2]'hx := by convert hpay
              rw [if_pos hodd, dif_pos hi, dif_neg hn1, if_neg hne0, if_neg hneE]
              rw [dif_pos ⟨hodd, Nat.zero_le _, hx⟩, hbits]
            · rw [if_neg hodd, dif_neg hn1, if_neg hne0, if_neg hneE]
              rw [dif_neg (fun h => hodd h.1)]
          · rw [if_neg hxD]
            by_cases hlt : z.toNat < D x + y.length
            · rw [if_pos hlt, dif_neg hn1, if_neg hne0, if_neg hneE]
              rw [dif_neg (fun h => by simp [D] at hxD; omega)]
            · rw [if_neg hlt, Int.toNat_of_nonneg hpos,
                inputTape_ge machine (pairBits x y) z (by
                  have := Int.toNat_of_nonneg hpos; omega), machine_blank,
                dif_neg hn1, if_neg hne0, if_neg hneE]
              have hnot : ¬ z.toNat / 2 < x.length := by
                have : D x + y.length ≤ z.toNat := Nat.not_lt.mp hlt
                simp only [D] at this; omega
              rw [dif_neg (fun h => hnot h.2.2)]
        · rw [dif_neg hpos, dif_neg hpos]

theorem step_markD (x y : List Bool) :
    step machine 0 { state := 8, head := 0, tape := endedTape x y } =
      some (copyConfig x y 0) := by
  simp [step, rule_markDest, writtenTape, moveHead, copyConfig, copyTape_of_ended, Option.map_some]

theorem setup_run (x y : List Bool) :
    run machine (ticks (2 * (pairBits x y).length + 5))
      (initial machine (pairBits x y)) = some (copyConfig x y 0) := by
  have hn : (pairBits x y).length = D x + y.length := by simp [D, pairBits_length]
  have hfuel : 2 * (D x + y.length) + 5 =
      2 + (2 * x.length + (1 + (y.length + (1 + ((D x + y.length + 1) + 1))))) := by
    simp [D]; omega
  rw [show ticks (2 * (pairBits x y).length + 5) =
        ticks 2 ++ ticks (2 * x.length) ++ ticks 1 ++ ticks y.length ++ ticks 1 ++
          ticks (D x + y.length + 1) ++ ticks 1 by
      simp [hn, hfuel, ticks_add, List.append_assoc]]
  rw [run_append, run_append, run_append, run_append, run_append, run_append,
    setup2 (pairBits x y), Option.bind_some, parse_x x y x.length le_rfl, Option.bind_some,
    run_ticks_one, parse_sep x y, Option.bind_some, skip_y x y y.length le_rfl,
    Option.bind_some, run_ticks_one, step_markE x y, Option.bind_some, seekL_all x y,
    Option.bind_some, run_ticks_one, step_markD]

def cleared (w : List Bool) (k : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z ∧ k ≤ z.toNat then 2
  else workTape w (w.length + 1) z

theorem cleared_length (w : List Bool) : cleared w w.length = workTape w (w.length + 1) := by
  funext z
  unfold cleared
  by_cases hL : z = -1; · simp [hL, workTape]
  rw [if_neg hL]
  by_cases hcond : 0 ≤ z ∧ w.length ≤ z.toNat
  · rw [dif_pos hcond]
    unfold workTape workNat
    rw [if_neg hL, dif_pos hcond.1]
    by_cases hlt : z.toNat < w.length + 1
    · rw [if_pos hlt]; split_ifs <;> first | rfl | omega
    · rw [if_neg hlt, Int.toNat_of_nonneg hcond.1,
        inputTape_ge machine w z (by omega), machine_blank]
  · rw [dif_neg hcond]

theorem cleared_zero (w : List Bool) : cleared w 0 = boundaryTape := by
  funext z
  unfold cleared boundaryTape
  by_cases hL : z = -1
  · simp [hL]
  · rw [if_neg hL, if_neg hL]
    by_cases hpos : 0 ≤ z
    · rw [dif_pos ⟨hpos, Nat.zero_le _⟩]
    · rw [dif_neg (fun h => hpos h.1)]
      unfold workTape; rw [if_neg hL, dif_neg hpos]

theorem cleared_update (w : List Bool) (p : ℕ) :
    Function.update (cleared w (p + 1)) (natInt p) 2 = cleared w p := by
  funext z
  by_cases hz : z = natInt p
  · subst z
    have hL : natInt p ≠ -1 := natInt_ne_neg1 p
    unfold cleared
    rw [Function.update_apply, if_pos rfl, if_neg hL]
    simp [natInt, toNat_ofNat, Nat.cast_nonneg]
  · rw [Function.update_apply, if_neg hz]
    unfold cleared
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · have hne : z.toNat ≠ p := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg Nat.cast heq))
        by_cases hge : p + 1 ≤ z.toNat
        · have hp : p ≤ z.toNat := Nat.le_of_succ_le hge
          simp [hpos, hge, hp]
        · have hp : ¬ p ≤ z.toNat := by omega
          simp [hpos, hge, hp]
      · simp [hpos]

theorem cleared_nat_ne_L (w : List Bool) (k i : ℕ) : cleared w k (i : Int) ≠ 3 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold cleared; rw [if_neg hL]
  by_cases hcond : 0 ≤ (i : Int) ∧ k ≤ (i : Int).toNat
  · rw [dif_pos hcond]; decide
  · rw [dif_neg hcond]; exact work_nat_ne_L w (w.length + 1) i

theorem step_malLeft_nat (w : List Bool) (p : ℕ) :
    step machine 0 { state := 16, head := natInt p, tape := cleared w (p + 1) } =
      some { state := 16, head := natInt p - 1, tape := cleared w p } := by
  have ht : cleared w (p + 1) (natInt p) ≠ 3 := cleared_nat_ne_L w (p + 1) p
  simp [step, rule_malLeft_notL _ ht, writtenTape, moveHead, cleared_update]

theorem malLeft_to_neg1 (w : List Bool) (p : ℕ) :
    run machine (ticks (p + 1)) { state := 16, head := natInt p, tape := cleared w (p + 1) } =
      some { state := 16, head := -1, tape := cleared w 0 } := by
  induction p with
  | zero => rw [run_ticks_one, step_malLeft_nat w 0]; simp [natInt_zero]
  | succ p ih =>
      have hticks : ticks (p + 1 + 1) = ticks 1 ++ ticks (p + 1) := by
        have : p + 1 + 1 = 1 + (p + 1) := by omega
        rw [this, ticks_add]
      rw [hticks, run_append, run_ticks_one, step_malLeft_nat w (p + 1), Option.bind_some]
      simpa [natInt_pred (p + 1) (by omega)] using ih

theorem step_malLeft_L (w : List Bool) :
    step machine 0 { state := 16, head := -1, tape := boundaryTape } =
      some (finalConfig machine []) := by
  have htape : Function.update boundaryTape (-1) 2 = inputTape machine ([] : List Bool) := by
    rw [boundary_erase_L, inputTape_nil]
  simp [step, show boundaryTape (-1) = 3 from rfl, rule_malLeft_L, writtenTape, moveHead,
    finalConfig, machine_accept, htape]

theorem malLeft_from (w : List Bool) :
    run machine (ticks (w.length + 1))
        (Config.mk 16 (natInt w.length - 1) (workTape w (w.length + 1))) =
      some (finalConfig machine []) := by
  rw [← cleared_length]
  by_cases hn : w.length = 0
  · have hhead : natInt w.length - 1 = -1 := by simp [hn, natInt]
    rw [hhead, hn, cleared_zero, run_ticks_one]; exact step_malLeft_L w
  · have hp : 1 ≤ w.length := Nat.pos_of_ne_zero hn
    have hticks : ticks (w.length + 1) = ticks (w.length - 1 + 1) ++ ticks 1 := by
      have : w.length + 1 = (w.length - 1 + 1) + 1 := by omega
      rw [this, ticks_add]
    have hcl : cleared w w.length = cleared w ((w.length - 1) + 1) := by
      simp [Nat.sub_add_cancel hp]
    rw [natInt_pred _ hp, hcl, hticks, run_append, malLeft_to_neg1 w (w.length - 1),
      Option.bind_some, run_ticks_one, cleared_zero]
    exact step_malLeft_L w

theorem parse_mal_from (w : List Bool) (n : ℕ) (hn : n ≤ w.length) (heven : n % 2 = 0)
    (hmal : unpairBits (w.drop n) = none) :
    run machine (ticks (w.length - n + 1)) { state := 4, head := natInt n, tape := workTape w n } =
      some (Config.mk 16 (natInt w.length - 1) (workTape w (w.length + 1))) := by
  suffices hmain : ∀ d n, d = w.length - n → n ≤ w.length → n % 2 = 0 →
      unpairBits (w.drop n) = none →
      run machine (ticks (w.length - n + 1)) { state := 4, head := natInt n, tape := workTape w n } =
        some (Config.mk 16 (natInt w.length - 1) (workTape w (w.length + 1))) by
    exact hmain (w.length - n) n rfl hn heven hmal
  intro d; induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hd hn heven hmal
    cases hdrop : w.drop n with
    | nil =>
        have heq : n = w.length := by have := List.drop_eq_nil_iff.mp hdrop; omega
        subst heq
        have hticks : w.length - w.length + 1 = 1 := by omega
        rw [hticks, run_ticks_one]; simpa using step_parse_blank w w.length le_rfl
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
            have hticks : w.length - n + 1 = 2 := by omega
            rw [hticks, show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append, run_ticks_one,
              step_parse_true w n hlt ha heven, Option.bind_some, run_ticks_one]
            simp only [hn1]; simpa using step_parseBit_blank w w.length le_rfl
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
            rw [show ticks (w.length - n + 1) = ticks 2 ++ ticks (w.length - (n + 2) + 1) by
              rw [hsplit, ticks_add]]
            rw [run_append, show ticks 2 = ticks 1 ++ ticks 1 from rfl, run_append, run_ticks_one,
              step_parse_true w n hlt ha heven, Option.bind_some, run_ticks_one,
              step_parseBit w (n + 1) hlt2 ho, Option.bind_some]
            exact ih (w.length - (n + 2)) (by omega) (n + 2) rfl (by omega) (by omega) hmal'

theorem mal_run (w : List Bool) (h : unpairBits w = none) :
    run machine (ticks (2 * w.length + 4)) (initial machine w) =
      some (finalConfig machine []) := by
  have hsplit : 2 * w.length + 4 = 2 + ((w.length + 1) + (w.length + 1)) := by omega
  rw [show ticks (2 * w.length + 4) = ticks 2 ++ ticks ((w.length + 1) + (w.length + 1)) by
    rw [hsplit, ticks_add]]
  rw [run_append, setup2, Option.bind_some]
  have hhead : ({ state := 4, head := 0, tape := workTape w 0 } : Configuration 17 8) =
      { state := 4, head := natInt 0, tape := workTape w 0 } := by simp [natInt_zero]
  rw [hhead]
  have hparse := parse_mal_from w 0 (Nat.zero_le _) (by decide) (by simpa using h)
  rw [show w.length - 0 + 1 = w.length + 1 by omega] at hparse
  rw [ticks_add, run_append, hparse, Option.bind_some]; exact malLeft_from w

theorem first_stage_spec (x y w : List Bool) :
    run machine (ticks (2 * (pairBits x y).length + 5)) (initial machine (pairBits x y)) =
      some (copyConfig x y 0) ∧
    (unpairBits w = none → run machine (ticks (2 * w.length + 4)) (initial machine w) =
      some (finalConfig machine [])) := ⟨setup_run x y, mal_run w⟩

end PakFixedPolyomino.StandardBitPairFirst
