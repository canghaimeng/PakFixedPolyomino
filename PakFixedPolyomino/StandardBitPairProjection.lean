import PakFixedPolyomino.StandardBitMetric
import Mathlib.Tactic

/-! # Fixed-format second-component projection

An explicit finite deterministic one-tape machine reads the globally fixed
`pairBits` encoding, erases the marked first component and separator, copies
the second component onto the origin, and accepts with a clean binary tape.
Malformed prefixes that never contain a separator are wiped to empty output.
-/

namespace PakFixedPolyomino.StandardBitPairProjection

open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape)
open Polynomial

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def secondBits (input : List Bool) : List Bool :=
  match unpairBits input with
  | some (_, y) => y
  | none => []

theorem secondBits_pair (x y : List Bool) : secondBits (pairBits x y) = y := by
  simp [secondBits, unpair_pairBits]

theorem secondBits_none {w : List Bool} (h : unpairBits w = none) :
    secondBits w = [] := by
  simp [secondBits, h]

theorem unpairBits_eq_some {w x y : List Bool} :
    unpairBits w = some (x, y) ↔ w = pairBits x y := by
  constructor
  · intro h
    induction x generalizing w y with
    | nil =>
        cases w with
        | nil => simp [unpairBits] at h
        | cons b rest =>
            cases b with
            | false =>
                simp [unpairBits] at h
                rcases h with ⟨rfl, rfl⟩
                rfl
            | true =>
                cases rest with
                | nil => simp [unpairBits] at h
                | cons _c rest =>
                    cases hrest : unpairBits rest <;> simp [unpairBits, hrest] at h
    | cons a x ih =>
        cases w with
        | nil => simp [unpairBits] at h
        | cons b rest =>
            cases b with
            | false =>
                simp [unpairBits] at h
            | true =>
                cases rest with
                | nil => simp [unpairBits] at h
                | cons c rest =>
                    simp [unpairBits] at h
                    cases hr : unpairBits rest with
                    | none => simp [hr] at h
                    | some z =>
                        simp [hr] at h
                        obtain ⟨hx, hy⟩ := h
                        subst hx
                        subst hy
                        have ih' := ih (w := rest) hr
                        simp [pairBits, ih']
  · intro h; subst h; exact unpair_pairBits x y

theorem secondBits_of_some {w x y : List Bool}
    (h : unpairBits w = some (x, y)) : secondBits w = y := by
  have hw : w = pairBits x y := (unpairBits_eq_some).1 h
  subst hw
  exact secondBits_pair x y

def enc (b : Bool) : Fin 8 := if b then 1 else 0
def D (x : List Bool) : ℕ := 2 * x.length + 1

theorem D_pos (x : List Bool) : 1 ≤ D x := by
  simp [D]

def machine : DeterministicMachine 17 8 where
  rule := fun q a _ =>
    if q = 2 then
      some { write := a, target := 3, move := .left }
    else if q = 3 then
      some { write := 3, target := 4, move := .right }
    else if q = 4 then
      if a = 1 then some { write := 2, target := 5, move := .right }
      else if a = 0 then some { write := 2, target := 6, move := .right }
      else if a = 2 then some { write := 2, target := 16, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 5 then
      if a = 0 ∨ a = 1 then some { write := 2, target := 4, move := .right }
      else if a = 2 then some { write := 2, target := 16, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 6 then
      if a = 0 ∨ a = 1 then some { write := a, target := 6, move := .right }
      else if a = 2 then some { write := 5, target := 7, move := .left }
      else some { write := 2, target := 15, move := .right }
    else if q = 7 then
      if a = 3 then some { write := 3, target := 8, move := .right }
      else some { write := a, target := 7, move := .left }
    else if q = 8 then
      some { write := 4, target := 9, move := .stay }
    else if q = 9 then
      if a = 0 then some { write := 2, target := 10, move := .left }
      else if a = 1 then some { write := 2, target := 11, move := .left }
      else if a = 5 then some { write := 2, target := 13, move := .left }
      else some { write := a, target := 9, move := .right }
    else if q = 10 then
      if a = 4 then some { write := 0, target := 12, move := .right }
      else some { write := a, target := 10, move := .left }
    else if q = 11 then
      if a = 4 then some { write := 1, target := 12, move := .right }
      else some { write := a, target := 11, move := .left }
    else if q = 12 then
      some { write := 4, target := 9, move := .stay }
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

theorem config_ext {c₁ c₂ : Configuration 17 8}
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

abbrev natInt (n : ℕ) : Int := n

theorem nat_cast_succ (n : ℕ) : (n : Int) + 1 = natInt (n + 1) := by
  simp [natInt]

theorem nat_cast_pred (n : ℕ) (h : 1 ≤ n) :
    (n : Int) - 1 = natInt (n - 1) := by
  simp [natInt]
  omega

theorem nat_ne_neg1 (n : ℕ) : (n : Int) ≠ -1 := by omega

theorem natInt_succ (n : ℕ) : natInt n + 1 = natInt (n + 1) :=
  nat_cast_succ n

theorem natInt_pred (n : ℕ) (h : 1 ≤ n) : natInt n - 1 = natInt (n - 1) :=
  nat_cast_pred n h

theorem natInt_zero : natInt 0 = 0 := rfl
theorem natInt_ne_neg1 (n : ℕ) : natInt n ≠ -1 := nat_ne_neg1 n
theorem natInt_nonneg (n : ℕ) : (0 : Int) ≤ natInt n := Nat.cast_nonneg n
theorem natInt_inj {a b : ℕ} : natInt a = natInt b ↔ a = b := Nat.cast_inj
theorem natInt_eq_zero (n : ℕ) : natInt n = 0 ↔ n = 0 := Nat.cast_eq_zero

@[simp] theorem enc_false : enc false = 0 := rfl
@[simp] theorem enc_true : enc true = 1 := rfl

theorem update_same (tape : Int → Fin 8) (h : Int) :
    Function.update tape h (tape h) = tape := by
  funext z
  by_cases hz : z = h
  · subst hz
    simp [Function.update_apply]
  · simp [Function.update_apply, hz]

theorem rule_start (a : Fin 8) :
    machine.rule 2 a 0 = some { write := a, target := 3, move := .left } := by
  simp [machine]

theorem rule_markL (a : Fin 8) :
    machine.rule 3 a 0 = some { write := 3, target := 4, move := .right } := by
  simp [machine]

theorem rule_parse_one :
    machine.rule 4 1 0 = some { write := 2, target := 5, move := .right } := by
  simp [machine]

theorem rule_parse_zero :
    machine.rule 4 0 0 = some { write := 2, target := 6, move := .right } := by
  simp [machine]

theorem rule_parse_blank :
    machine.rule 4 2 0 = some { write := 2, target := 16, move := .left } := by
  simp [machine]

theorem rule_parseBit_bit (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 5 a 0 = some { write := 2, target := 4, move := .right } := by
  rcases h with h | h <;> simp [machine, h]

theorem rule_parseBit_blank :
    machine.rule 5 2 0 = some { write := 2, target := 16, move := .left } := by
  simp [machine]

theorem rule_toEnd_bit (a : Fin 8) (h : a = 0 ∨ a = 1) :
    machine.rule 6 a 0 = some { write := a, target := 6, move := .right } := by
  rcases h with h | h <;> simp [machine, h]

theorem rule_toEnd_blank :
    machine.rule 6 2 0 = some { write := 5, target := 7, move := .left } := by
  simp [machine]

theorem rule_seekL_L :
    machine.rule 7 3 0 = some { write := 3, target := 8, move := .right } := by
  simp [machine]

theorem rule_seekL_notL (a : Fin 8) (h : a ≠ 3) :
    machine.rule 7 a 0 = some { write := a, target := 7, move := .left } := by
  simp [machine, h]

theorem rule_markDest (a : Fin 8) :
    machine.rule 8 a 0 = some { write := 4, target := 9, move := .stay } := by
  simp [machine]

theorem rule_seekSrc_zero :
    machine.rule 9 0 0 = some { write := 2, target := 10, move := .left } := by
  simp [machine]

theorem rule_seekSrc_one :
    machine.rule 9 1 0 = some { write := 2, target := 11, move := .left } := by
  simp [machine]

theorem rule_seekSrc_E :
    machine.rule 9 5 0 = some { write := 2, target := 13, move := .left } := by
  simp [machine]

theorem rule_seekSrc_else (a : Fin 8) (h0 : a ≠ 0) (h1 : a ≠ 1) (h5 : a ≠ 5) :
    machine.rule 9 a 0 = some { write := a, target := 9, move := .right } := by
  simp [machine, h0, h1, h5]

theorem rule_seekDest0_dest :
    machine.rule 10 4 0 = some { write := 0, target := 12, move := .right } := by
  simp [machine]

theorem rule_seekDest0_else (a : Fin 8) (h : a ≠ 4) :
    machine.rule 10 a 0 = some { write := a, target := 10, move := .left } := by
  simp [machine, h]

theorem rule_seekDest1_dest :
    machine.rule 11 4 0 = some { write := 1, target := 12, move := .right } := by
  simp [machine]

theorem rule_seekDest1_else (a : Fin 8) (h : a ≠ 4) :
    machine.rule 11 a 0 = some { write := a, target := 11, move := .left } := by
  simp [machine, h]

theorem rule_placeDest (a : Fin 8) :
    machine.rule 12 a 0 = some { write := 4, target := 9, move := .stay } := by
  simp [machine]

theorem rule_seekDestClean_dest :
    machine.rule 13 4 0 = some { write := 2, target := 14, move := .left } := by
  simp [machine]

theorem rule_seekDestClean_else (a : Fin 8) (h : a ≠ 4) :
    machine.rule 13 a 0 = some { write := a, target := 13, move := .left } := by
  simp [machine, h]

theorem rule_seekLClean_L :
    machine.rule 14 3 0 = some { write := 2, target := 0, move := .right } := by
  simp [machine]

theorem rule_seekLClean_notL (a : Fin 8) (h : a ≠ 3) :
    machine.rule 14 a 0 = some { write := a, target := 14, move := .left } := by
  simp [machine, h]

theorem rule_malLeft_L :
    machine.rule 16 3 0 = some { write := 2, target := 0, move := .right } := by
  simp [machine]

theorem rule_malLeft_notL (a : Fin 8) (h : a ≠ 3) :
    machine.rule 16 a 0 = some { write := 2, target := 16, move := .left } := by
  simp [machine, h]

theorem pairBits_marker (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pairBits x y)[2 * i]'(by have := pairBits_length x y; omega) = true := by
  induction x generalizing i with
  | nil => cases hi
  | cons b x ih =>
      cases i with
      | zero => simp [pairBits]
      | succ i =>
          have hi' : i < x.length := by simp at hi; omega
          have hidx : 2 * (i + 1) = 2 * i + 2 := by omega
          simpa [pairBits, List.getElem_cons_succ, hidx] using ih i hi'

theorem pairBits_payload (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pairBits x y)[2 * i + 1]'(by have := pairBits_length x y; omega) = x[i] := by
  induction x generalizing i with
  | nil => cases hi
  | cons b x ih =>
      cases i with
      | zero => simp [pairBits]
      | succ i =>
          have hi' : i < x.length := by simp at hi; omega
          have hidx : 2 * (i + 1) + 1 = 2 * i + 1 + 2 := by omega
          simpa [pairBits, List.getElem_cons_succ, hidx] using ih i hi'

theorem pairBits_sep (x y : List Bool) :
    (pairBits x y)[2 * x.length]'(by have := pairBits_length x y; omega) =
      false := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih =>
      have hidx : 2 * (x.length + 1) = 2 * x.length + 2 := by omega
      simpa [pairBits, List.getElem_cons_succ, hidx] using ih

theorem pairBits_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    (pairBits x y)[2 * x.length + 1 + j]'(by have := pairBits_length x y; omega) =
      y[j] := by
  induction x with
  | nil =>
      have hidx : 1 + j = j + 1 := by omega
      simpa [pairBits, hidx] using List.getElem_cons_succ (a := false) (as := y) (i := j)
  | cons b x ih =>
      have hidx : 2 * (x.length + 1) + 1 + j = 2 * x.length + 1 + j + 2 := by omega
      simpa [pairBits, List.getElem_cons_succ, hidx] using ih

theorem read_bit (w : List Bool) (i : ℕ) (hi : i < w.length) :
    inputTape machine w i = enc w[i] := by
  simp [inputTape, enc, hi]

theorem toNat_ofNat (n : ℕ) : ((n : Int).toNat) = n :=
  Int.toNat_natCast n

def markedTape (w : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3 else inputTape machine w z

def erasedTape (w : List Bool) (n : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z ∧ z.toNat < n then 2
  else inputTape machine w z

def copyTapeNat (x y : List Bool) (k i : ℕ) : Fin 8 :=
  if i < k then
    if h : i < y.length then enc y[i] else 2
  else if i = k then 4
  else if i < D x + k then 2
  else if i < D x + y.length then
    if h : D x ≤ i ∧ i - D x < y.length then enc y[i - D x] else 2
  else if i = D x + y.length then 5
  else 2

def copyTape (x y : List Bool) (k : ℕ) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then copyTapeNat x y k z.toNat
  else 2

def endedTape (x y : List Bool) : Int → Fin 8 :=
  Function.update (erasedTape (pairBits x y) (D x)) (natInt (D x + y.length)) 5

def takenTape (x y : List Bool) (k : ℕ) : Int → Fin 8 :=
  Function.update (copyTape x y k) (natInt (D x + k)) 2

def boundaryTape (z : Int) : Fin 8 := if z = -1 then 3 else 2

def almostFinal (y : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z ∧ z.toNat < y.length then enc y[z.toNat]
  else 2

def copyConfig (x y : List Bool) (k : ℕ) : Configuration 17 8 :=
  { state := 9, head := k, tape := copyTape x y k }

def finalConfig (y : List Bool) : Configuration 17 8 :=
  { state := 0, head := 0, tape := inputTape machine y }

theorem erased_at (w : List Bool) (n i : ℕ) (hi : i < n) :
    erasedTape w n (i : Int) = 2 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  have hcond : 0 ≤ (i : Int) ∧ (i : Int).toNat < n := by
    refine ⟨by omega, ?_⟩
    simp [toNat_ofNat]; exact hi
  unfold erasedTape
  rw [if_neg hL, dif_pos hcond]

theorem erased_ge (w : List Bool) (n i : ℕ) (hi : n ≤ i) :
    erasedTape w n (i : Int) = inputTape machine w (i : Int) := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  have hcond : ¬ (0 ≤ (i : Int) ∧ (i : Int).toNat < n) := by
    simp [toNat_ofNat]; omega
  unfold erasedTape
  rw [if_neg hL, dif_neg hcond]

theorem erased_write (w : List Bool) (n : ℕ) :
    Function.update (erasedTape w n) (n : Int) 2 = erasedTape w (n + 1) := by
  funext z
  by_cases hz : z = (n : Int)
  · subst z
    simp [Function.update_apply]
    exact (erased_at w (n + 1) n (by omega)).symm
  · simp [Function.update_apply, hz]
    unfold erasedTape
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · have hne : z.toNat ≠ n := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg Nat.cast heq))
        by_cases hlt : z.toNat < n
        · rw [dif_pos ⟨hpos, hlt⟩, dif_pos ⟨hpos, by omega⟩]
        · rw [dif_neg (by intro h; exact hlt h.2),
            dif_neg (by intro h; exact hlt (by omega))]
      · have hc : ¬ (0 ≤ z ∧ z.toNat < n) := fun h => hpos h.1
        have hc' : ¬ (0 ≤ z ∧ z.toNat < n + 1) := fun h => hpos h.1
        rw [dif_neg hc, dif_neg hc']

theorem erased_complete (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    erasedTape w n = boundaryTape := by
  funext z
  by_cases hL : z = -1
  · simp [erasedTape, boundaryTape, hL]
  · by_cases hcond : 0 ≤ z ∧ z.toNat < n
    · simp [erasedTape, boundaryTape, hL, hcond]
    · simp [erasedTape, boundaryTape, hL, hcond]
      by_cases hpos : 0 ≤ z
      · have hge : n ≤ z.toNat :=
          Nat.not_lt.mp (fun hlt => hcond ⟨hpos, hlt⟩)
        have hzle : (w.length : Int) ≤ z := by
          have h1 : (w.length : Int) ≤ (n : Int) := Nat.cast_le.mpr hn
          have h2 : (n : Int) ≤ z := by
            have hzcast := Int.toNat_of_nonneg hpos
            omega
          omega
        exact inputTape_ge machine w z hzle
      · exact inputTape_neg machine w z (not_le.mp hpos)

theorem erased_nat_ne_L (w : List Bool) (n i : ℕ) :
    erasedTape w n (i : Int) ≠ 3 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold erasedTape
  rw [if_neg hL]
  by_cases hcond : 0 ≤ (i : Int) ∧ (i : Int).toNat < n
  · rw [dif_pos hcond]; decide
  · rw [dif_neg hcond]
    simp [inputTape]
    split_ifs <;> decide

theorem marked_eq_erased0 (w : List Bool) : markedTape w = erasedTape w 0 := by
  funext z
  unfold markedTape erasedTape
  by_cases hL : z = -1
  · simp [hL]
  · rw [if_neg hL, if_neg hL]
    have hcond : ¬ (0 ≤ z ∧ z.toNat < 0) := by omega
    rw [dif_neg hcond]

theorem inputTape_nil : inputTape machine ([] : List Bool) = fun _ => (2 : Fin 8) := by
  funext z
  unfold inputTape
  by_cases hpos : 0 ≤ z
  · simp [hpos]
  · simp [hpos]

theorem boundary_erase_L :
    Function.update boundaryTape (-1) 2 = fun _ => (2 : Fin 8) := by
  funext z
  by_cases hz : z = -1
  · simp [Function.update_apply, boundaryTape, hz]
  · simp [Function.update_apply, boundaryTape, hz]

theorem step_start (w : List Bool) :
    step machine 0 (initial machine w) =
      some { state := 3, head := -1, tape := inputTape machine w } := by
  simp [step, initial, rule_start, writtenTape, moveHead, update_same]

theorem step_markL (w : List Bool) :
    step machine 0 { state := 3, head := -1, tape := inputTape machine w } =
      some { state := 4, head := 0, tape := markedTape w } := by
  have hblank : inputTape machine w (-1) = 2 :=
    inputTape_neg machine w (-1) (by omega)
  have htape :
      Function.update (inputTape machine w) (-1) 3 = markedTape w := by
    funext z
    simp [Function.update_apply, markedTape]
  simp [step, hblank, rule_markL, writtenTape, moveHead, htape]

theorem setup_run (w : List Bool) :
    run machine (ticks 2) (initial machine w) =
      some { state := 4, head := 0, tape := erasedTape w 0 } := by
  have hsplit : (2 : ℕ) = 1 + 1 := rfl
  rw [hsplit, ticks_add, run_append, run_ticks_one, step_start, Option.bind_some,
    run_ticks_one, step_markL]
  simp [marked_eq_erased0]

theorem step_parse_true (w : List Bool) (n : ℕ) (hn : n < w.length)
    (ht : w[n] = true) :
    step machine 0 { state := 4, head := natInt n, tape := erasedTape w n } =
      some { state := 5, head := natInt (n + 1), tape := erasedTape w (n + 1) } := by
  have hread : erasedTape w n (n : Int) = 1 := by
    rw [erased_ge w n n le_rfl, read_bit w n hn, ht, enc_true]
  simp [step, hread, rule_parse_one, writtenTape, moveHead, erased_write, Option.map_some]

theorem step_parse_false (w : List Bool) (n : ℕ) (hn : n < w.length)
    (hf : w[n] = false) :
    step machine 0 { state := 4, head := natInt n, tape := erasedTape w n } =
      some { state := 6, head := natInt (n + 1), tape := erasedTape w (n + 1) } := by
  have hread : erasedTape w n (n : Int) = 0 := by
    rw [erased_ge w n n le_rfl, read_bit w n hn, hf, enc_false]
  simp [step, hread, rule_parse_zero, writtenTape, moveHead, erased_write, Option.map_some]

theorem step_parse_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 { state := 4, head := n, tape := erasedTape w n } =
      some { state := 16, head := natInt n - 1, tape := erasedTape w n } := by
  have hread : erasedTape w n (n : Int) = 2 := by
    rw [erased_ge w n n le_rfl]
    exact inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn)
  simp [step, hread, rule_parse_blank, writtenTape, moveHead, update_same]

theorem step_parseBit (w : List Bool) (n : ℕ) (hn : n < w.length) :
    step machine 0 { state := 5, head := natInt n, tape := erasedTape w n } =
      some { state := 4, head := natInt (n + 1), tape := erasedTape w (n + 1) } := by
  have hread : erasedTape w n (n : Int) = 0 ∨ erasedTape w n (n : Int) = 1 := by
    rw [erased_ge w n n le_rfl, read_bit w n hn]
    cases w[n] <;> simp
  have hrule := rule_parseBit_bit _ hread
  simp [step, hrule, writtenTape, moveHead, erased_write, Option.map_some]

theorem step_parseBit_blank (w : List Bool) (n : ℕ) (hn : w.length ≤ n) :
    step machine 0 { state := 5, head := n, tape := erasedTape w n } =
      some { state := 16, head := natInt n - 1, tape := erasedTape w n } := by
  have hread : erasedTape w n (n : Int) = 2 := by
    rw [erased_ge w n n le_rfl]
    exact inputTape_ge machine w (n : Int) (Nat.cast_le.mpr hn)
  simp [step, hread, rule_parseBit_blank, writtenTape, moveHead, update_same]

theorem parse_pair_run (x y : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    run machine (ticks (2 * k))
        { state := 4, head := 0, tape := erasedTape (pairBits x y) 0 } =
      some { state := 4, head := natInt (2 * k), tape := erasedTape (pairBits x y) (2 * k) } := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
      have hilt : k < x.length := by omega
      have hlen := pairBits_length x y
      have h2 : 2 * k < (pairBits x y).length := by omega
      have h2s : 2 * k + 1 < (pairBits x y).length := by omega
      have htrue := pairBits_marker x y k hilt
      have htwo : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [htwo, ticks_add, ticks_add, run_append, run_append, ih (by omega),
        Option.bind_some, run_ticks_one, step_parse_true (pairBits x y) (2 * k) h2 htrue,
        Option.bind_some, run_ticks_one]
      exact step_parseBit (pairBits x y) (2 * k + 1) h2s

theorem parse_sep_step (x y : List Bool) :
    step machine 0
        { state := 4, head := natInt (2 * x.length), tape := erasedTape (pairBits x y) (2 * x.length) } =
      some { state := 6, head := natInt (D x), tape := erasedTape (pairBits x y) (D x) } := by
  have hlen := pairBits_length x y
  have hn : 2 * x.length < (pairBits x y).length := by omega
  have hf := pairBits_sep x y
  simpa [D] using step_parse_false (pairBits x y) (2 * x.length) hn hf

theorem parse_all (x y : List Bool) :
    run machine (ticks (D x))
        { state := 4, head := 0, tape := erasedTape (pairBits x y) 0 } =
      some { state := 6, head := natInt (D x), tape := erasedTape (pairBits x y) (D x) } := by
  have hsplit : D x = 2 * x.length + 1 := rfl
  rw [show ticks (D x) = ticks (2 * x.length + 1) from congrArg ticks hsplit,
    ticks_add, run_append, parse_pair_run x y x.length le_rfl,
    Option.bind_some, run_ticks_one, parse_sep_step x y]

theorem pairBits_y' (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    (pairBits x y)[D x + j]'(by have := pairBits_length x y; simp [D]; omega) =
      y[j] := by
  simpa [D, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pairBits_y x y j hj

theorem erased_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    erasedTape (pairBits x y) (D x) (natInt (D x + j)) = enc y[j] := by
  have hlen := pairBits_length x y
  have hi : D x + j < (pairBits x y).length := by simp [D]; omega
  rw [erased_ge (pairBits x y) (D x) (D x + j) (by omega), read_bit _ _ hi, pairBits_y' x y j hj]

theorem erased_end (x y : List Bool) :
    erasedTape (pairBits x y) (D x) (natInt (D x + y.length)) = 2 := by
  have hge : (pairBits x y).length ≤ D x + y.length := by simp [D]
  rw [erased_ge (pairBits x y) (D x) (D x + y.length) (by omega)]
  apply inputTape_ge
  exact Nat.cast_le.mpr hge

set_option simprocs false in
theorem toEnd_walk (x y : List Bool) (j : ℕ) (hj : j ≤ y.length) :
    run machine (ticks j)
        { state := 6, head := natInt (D x), tape := erasedTape (pairBits x y) (D x) } =
      some { state := 6, head := natInt (D x + j), tape := erasedTape (pairBits x y) (D x) } := by
  induction j with
  | zero => simp [ticks]
  | succ j ih =>
      have hjl : j < y.length := by omega
      rw [ticks_add, run_append, ih (by omega), Option.bind_some, run_ticks_one]
      have hread : erasedTape (pairBits x y) (D x) (natInt (D x + j)) = 0 ∨
          erasedTape (pairBits x y) (D x) (natInt (D x + j)) = 1 := by
        rw [erased_y x y j hjl]; cases y[j] <;> simp
      have hrule := rule_toEnd_bit _ hread
      simp only [step, hrule, writtenTape, moveHead, update_same, Option.map_some]
      simp only [natInt_succ, Nat.add_assoc]

theorem toEnd_mark (x y : List Bool) :
    step machine 0
        { state := 6, head := natInt (D x + y.length), tape := erasedTape (pairBits x y) (D x) } =
      some { state := 7, head := natInt (D x + y.length - 1), tape := endedTape x y } := by
  have hread := erased_end x y
  have hD := D_pos x
  simp only [step, hread, rule_toEnd_blank, writtenTape, moveHead, endedTape, Option.map_some]
  simp only [natInt_pred (D x + y.length) (by omega)]

theorem toEnd_all (x y : List Bool) :
    run machine (ticks (y.length + 1))
        { state := 6, head := natInt (D x), tape := erasedTape (pairBits x y) (D x) } =
      some { state := 7, head := natInt (D x + y.length - 1), tape := endedTape x y } := by
  rw [ticks_add, run_append, toEnd_walk x y y.length le_rfl, Option.bind_some,
    run_ticks_one, toEnd_mark]

theorem ended_L (x y : List Bool) : endedTape x y (-1) = 3 := by
  have hne : ¬ ((-1 : Int) = natInt (D x + y.length)) :=
    Ne.symm (natInt_ne_neg1 (D x + y.length))
  unfold endedTape
  rw [Function.update_apply, if_neg hne]
  simp [erasedTape]

theorem ended_nat_ne_L (x y : List Bool) (i : ℕ) : endedTape x y (i : Int) ≠ 3 := by
  unfold endedTape
  simp only [Function.update_apply]
  split_ifs
  · decide
  · exact erased_nat_ne_L _ _ i

theorem step_seekL_nat (x y : List Bool) (p : ℕ) :
    step machine 0 { state := 7, head := p, tape := endedTape x y } =
      some { state := 7, head := natInt p - 1, tape := endedTape x y } := by
  have hne := ended_nat_ne_L x y p
  have hrule := rule_seekL_notL _ hne
  simp [step, hrule, writtenTape, moveHead, update_same]

theorem seekL_to_neg1 (x y : List Bool) (p : ℕ) :
    run machine (ticks (p + 1))
        { state := 7, head := p, tape := endedTape x y } =
      some { state := 7, head := -1, tape := endedTape x y } := by
  induction p with
  | zero =>
      rw [run_ticks_one, step_seekL_nat]
      simp
  | succ p ih =>
      have hsplit : p + 1 + 1 = 1 + (p + 1) := by omega
      rw [hsplit, ticks_add, run_append, run_ticks_one, step_seekL_nat,
        Option.bind_some]
      have hhead : natInt (p + 1) - 1 = (p : Int) := by simp [natInt]
      simpa [hhead] using ih

theorem step_seekL_boundary (x y : List Bool) :
    step machine 0 { state := 7, head := -1, tape := endedTape x y } =
      some { state := 8, head := 0, tape := endedTape x y } := by
  simp [step, ended_L, rule_seekL_L, writtenTape, moveHead, update_same]

theorem seekL_all (x y : List Bool) :
    run machine (ticks (D x + y.length + 1))
        { state := 7, head := natInt (D x + y.length - 1), tape := endedTape x y } =
      some { state := 8, head := 0, tape := endedTape x y } := by
  have hD := D_pos x
  have hsplit : D x + y.length + 1 = (D x + y.length - 1 + 1) + 1 := by omega
  rw [hsplit, ticks_add, run_append, seekL_to_neg1 x y (D x + y.length - 1),
    Option.bind_some, run_ticks_one, step_seekL_boundary]

theorem copyTapeNat_dest (x y : List Bool) (k : ℕ) : copyTapeNat x y k k = 4 := by
  unfold copyTapeNat
  have : ¬ k < k := by omega
  rw [if_neg this, if_pos rfl]

theorem copyTapeNat_bit (x y : List Bool) (k i : ℕ) (hi : i < k) (hik : i < y.length) :
    copyTapeNat x y k i = enc y[i] := by
  unfold copyTapeNat
  rw [if_pos hi, dif_pos hik]

theorem copyTapeNat_gap (x y : List Bool) (k i : ℕ) (h1 : k < i) (h2 : i < D x + k) :
    copyTapeNat x y k i = 2 := by
  unfold copyTapeNat
  have hn1 : ¬ i < k := by omega
  have hn2 : ¬ i = k := by omega
  rw [if_neg hn1, if_neg hn2, if_pos h2]

theorem copyTapeNat_src (x y : List Bool) (k : ℕ) (hk : k < y.length) :
    copyTapeNat x y k (D x + k) = enc y[k] := by
  have hD := D_pos x
  unfold copyTapeNat
  have h1 : ¬ D x + k < k := by omega
  have h2 : ¬ D x + k = k := by omega
  have h3 : ¬ D x + k < D x + k := by omega
  have h4 : D x + k < D x + y.length := by omega
  have h5 : D x ≤ D x + k ∧ D x + k - D x < y.length := by omega
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, dif_pos h5]
  have h6 : D x + k - D x = k := by omega
  simp [h6]

theorem copyTapeNat_E (x y : List Bool) (k : ℕ) (hk : k ≤ y.length) :
    copyTapeNat x y k (D x + y.length) = 5 := by
  have hD := D_pos x
  unfold copyTapeNat
  have h1 : ¬ D x + y.length < k := by omega
  have h2 : ¬ D x + y.length = k := by omega
  have h3 : ¬ D x + y.length < D x + k := by omega
  have h4 : ¬ D x + y.length < D x + y.length := by omega
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos rfl]

set_option simprocs false in
theorem copyTape_of_nat (x y : List Bool) (k i : ℕ) :
    copyTape x y k (natInt i) = copyTapeNat x y k i := by
  have hL : natInt i ≠ -1 := natInt_ne_neg1 i
  have hpos : 0 ≤ natInt i := natInt_nonneg i
  unfold copyTape
  rw [if_neg hL, dif_pos hpos]
  simp [natInt, toNat_ofNat]

theorem copyTape_dest (x y : List Bool) (k : ℕ) : copyTape x y k (k : Int) = 4 := by
  simpa [natInt] using (copyTape_of_nat x y k k).trans (copyTapeNat_dest x y k)

theorem copyTape_L (x y : List Bool) (k : ℕ) : copyTape x y k (-1) = 3 := by
  simp [copyTape]

theorem copyTape_bit (x y : List Bool) (k i : ℕ) (hi : i < k) (hik : i < y.length) :
    copyTape x y k (i : Int) = enc y[i] := by
  simpa [natInt] using (copyTape_of_nat x y k i).trans (copyTapeNat_bit x y k i hi hik)

theorem copyTape_src (x y : List Bool) (k : ℕ) (hk : k < y.length) :
    copyTape x y k (natInt (D x + k)) = enc y[k] :=
  (copyTape_of_nat x y k (D x + k)).trans (copyTapeNat_src x y k hk)

theorem copyTape_E (x y : List Bool) (k : ℕ) (hk : k ≤ y.length) :
    copyTape x y k (natInt (D x + y.length)) = 5 :=
  (copyTape_of_nat x y k (D x + y.length)).trans (copyTapeNat_E x y k hk)

theorem copyTape_gap (x y : List Bool) (k i : ℕ) (h1 : k < i) (h2 : i < D x + k) :
    copyTape x y k (natInt i) = 2 :=
  (copyTape_of_nat x y k i).trans (copyTapeNat_gap x y k i h1 h2)

theorem copyTape_neg (x y : List Bool) (k : ℕ) {z : Int}
    (hL : z ≠ -1) (hpos : ¬ 0 ≤ z) : copyTape x y k z = 2 := by
  unfold copyTape
  rw [if_neg hL, dif_neg hpos]

set_option simprocs false in
theorem ended_of_nat (x y : List Bool) (i : ℕ) :
    endedTape x y (natInt i) =
      if i = D x + y.length then (5 : Fin 8)
      else erasedTape (pairBits x y) (D x) (natInt i) := by
  unfold endedTape
  rw [Function.update_apply]
  by_cases hi : i = D x + y.length
  · subst i
    rw [if_pos rfl, if_pos rfl]
  · have hne : natInt i ≠ natInt (D x + y.length) := mt natInt_inj.mp hi
    rw [if_neg hne, if_neg hi]

theorem ended_blank0 (x y : List Bool) : endedTape x y 0 = 2 := by
  have hD := D_pos x
  have hne : (0 : ℕ) ≠ D x + y.length := by omega
  have h := ended_of_nat x y 0
  simp [natInt_zero, hne] at h
  simpa [h] using erased_at (pairBits x y) (D x) 0 (by omega)

set_option simprocs false in
theorem copyTapeNat_zero_ne (x y : List Bool) (i : ℕ) (h0 : i ≠ 0) :
    copyTapeNat x y 0 i = endedTape x y (natInt i) := by
  have hD := D_pos x
  rw [ended_of_nat]
  by_cases hE : i = D x + y.length
  · subst i
    rw [if_pos rfl, copyTapeNat_E x y 0 (by omega)]
  · rw [if_neg hE]
    by_cases hg : i < D x
    · rw [copyTapeNat_gap x y 0 i (Nat.pos_of_ne_zero h0) (by omega)]
      exact (erased_at (pairBits x y) (D x) i hg).symm
    · by_cases hy : i < D x + y.length
      · have hsrc : D x ≤ i ∧ i - D x < y.length := by omega
        have hbit : copyTapeNat x y 0 i = enc y[i - D x] := by
          unfold copyTapeNat
          have hn1 : ¬ i < 0 := by omega
          have hn3 : ¬ i < D x + 0 := by omega
          rw [if_neg hn1, if_neg h0, if_neg hn3, if_pos hy, dif_pos hsrc]
        have herr : erasedTape (pairBits x y) (D x) (natInt i) = enc y[i - D x] := by
          have hj : i - D x < y.length := hsrc.2
          have hidx : D x + (i - D x) = i := by omega
          have := erased_y x y (i - D x) hj
          convert this
          rw [hidx]
        rw [hbit, herr]
      · have hge : D x ≤ i := Nat.not_lt.mp hg
        have hplen : (pairBits x y).length = D x + y.length := by
          simp [pairBits_length, D]
        have hge' : (pairBits x y).length ≤ i := by
          rw [hplen]; exact Nat.not_lt.mp hy
        have hct : copyTapeNat x y 0 i = 2 := by
          unfold copyTapeNat
          have hn1 : ¬ i < 0 := by omega
          have hn3 : ¬ i < D x + 0 := by omega
          rw [if_neg hn1, if_neg h0, if_neg hn3, if_neg hy, if_neg hE]
        rw [hct, erased_ge (pairBits x y) (D x) i hge]
        exact (inputTape_ge machine (pairBits x y) (natInt i)
          (Nat.cast_le.mpr hge')).symm

set_option simprocs false in
theorem copyTape_of_ended (x y : List Bool) :
    Function.update (endedTape x y) (0 : Int) 4 = copyTape x y 0 := by
  funext z
  by_cases hL : z = -1
  · subst z
    have hne : ¬ (-1 : Int) = (0 : Int) := by omega
    simp only [Function.update_apply, hne, ite_false]
    exact (ended_L x y).trans (copyTape_L x y 0).symm
  · by_cases hpos : 0 ≤ z
    · have hz : z = natInt z.toNat := (Int.toNat_of_nonneg hpos).symm
      rw [hz]
      by_cases h0 : z.toNat = 0
      · have hz0 : natInt z.toNat = (0 : Int) := by simp [h0, natInt]
        simp only [Function.update_apply, hz0, ite_true]
        simpa [h0, natInt] using (copyTape_dest x y 0).symm
      · have hne0 : natInt z.toNat ≠ (0 : Int) := by
          intro h; exact h0 (natInt_eq_zero _ |>.mp h)
        simp only [Function.update_apply, hne0, ite_false]
        rw [copyTape_of_nat, copyTapeNat_zero_ne x y z.toNat h0]
    · have hne0 : z ≠ (0 : Int) := by omega
      simp only [Function.update_apply, hne0, ite_false]
      have hneE : z ≠ natInt (D x + y.length) := by
        intro h
        have := natInt_nonneg (D x + y.length)
        omega
      unfold endedTape
      rw [Function.update_apply, if_neg hneE]
      unfold erasedTape
      rw [if_neg hL]
      have hc : ¬ (0 ≤ z ∧ z.toNat < D x) := fun h => hpos h.1
      rw [dif_neg hc]
      exact (inputTape_neg machine (pairBits x y) z (lt_of_not_ge hpos)).trans
        (copyTape_neg x y 0 hL hpos).symm

theorem markDest_run (x y : List Bool) :
    run machine (ticks 1)
        { state := 8, head := 0, tape := endedTape x y } =
      some (copyConfig x y 0) := by
  have hread := ended_blank0 x y
  have htape := copyTape_of_ended x y
  rw [run_ticks_one]
  simp [step, hread, rule_markDest, writtenTape, moveHead, copyConfig, htape]

def seekDestState (b : Bool) : Fin 17 := if b then 11 else 10

theorem rule_seekDest_else (b : Bool) (a : Fin 8) (h : a ≠ 4) :
    machine.rule (seekDestState b) a 0 =
      some { write := a, target := seekDestState b, move := .left } := by
  cases b <;> simp [seekDestState, machine, h]

theorem rule_seekDest_dest (b : Bool) :
    machine.rule (seekDestState b) 4 0 =
      some { write := enc b, target := 12, move := .right } := by
  cases b <;> simp [seekDestState, machine, enc]

theorem rule_take (b : Bool) :
    machine.rule 9 (enc b) 0 =
      some { write := 2, target := seekDestState b, move := .left } := by
  cases b <;> simp [machine, enc, seekDestState]

set_option simprocs false in
theorem step_seekSrc_dest (x y : List Bool) (k : ℕ) :
    step machine 0 (copyConfig x y k) =
      some { state := 9, head := natInt (k + 1), tape := copyTape x y k } := by
  have hread := copyTape_dest x y k
  have hne0 : (4 : Fin 8) ≠ 0 := by decide
  have hne1 : (4 : Fin 8) ≠ 1 := by decide
  have hne5 : (4 : Fin 8) ≠ 5 := by decide
  have hrule := rule_seekSrc_else 4 hne0 hne1 hne5
  simp only [copyConfig, step, hread, hrule, writtenTape, moveHead, Option.map_some]
  have htape : Function.update (copyTape x y k) (k : Int) 4 = copyTape x y k := by
    rw [← hread]; exact update_same _ _
  simp only [htape, natInt_succ]

set_option simprocs false in
theorem step_seekSrc_gap (x y : List Bool) (k i : ℕ)
    (h1 : k < i) (h2 : i < D x + k) :
    step machine 0 { state := 9, head := natInt i, tape := copyTape x y k } =
      some { state := 9, head := natInt (i + 1), tape := copyTape x y k } := by
  have hread := copyTape_gap x y k i h1 h2
  have hne0 : (2 : Fin 8) ≠ 0 := by decide
  have hne1 : (2 : Fin 8) ≠ 1 := by decide
  have hne5 : (2 : Fin 8) ≠ 5 := by decide
  have hrule := rule_seekSrc_else 2 hne0 hne1 hne5
  simp only [step, hread, hrule, writtenTape, moveHead, Option.map_some]
  have htape :
      Function.update (copyTape x y k) (natInt i) 2 = copyTape x y k := by
    rw [← hread]; exact update_same _ _
  simp only [htape, natInt_succ]

set_option simprocs false in
theorem seekSrc_gap_walk (x y : List Bool) (k t : ℕ) (ht : t ≤ D x - 1) :
    run machine (ticks t)
        { state := 9, head := natInt (k + 1), tape := copyTape x y k } =
      some { state := 9, head := natInt (k + 1 + t), tape := copyTape x y k } := by
  have hD := D_pos x
  induction t with
  | zero => simp [ticks]
  | succ t ih =>
      have ht' : t ≤ D x - 1 := by omega
      have h1 : k < k + 1 + t := by omega
      have h2 : k + 1 + t < D x + k := by omega
      rw [ticks_add, run_append, ih ht', Option.bind_some, run_ticks_one]
      simpa [Nat.add_assoc] using step_seekSrc_gap x y k (k + 1 + t) h1 h2

set_option simprocs false in
theorem seekSrc_run (x y : List Bool) (k : ℕ) (_hk : k ≤ y.length) :
    run machine (ticks (D x)) (copyConfig x y k) =
      some { state := 9, head := natInt (D x + k), tape := copyTape x y k } := by
  have hD := D_pos x
  have hsplit : ticks (D x) = ticks 1 ++ ticks (D x - 1) := by
    conv => lhs; rw [show D x = 1 + (D x - 1) from by omega]
    exact ticks_add 1 (D x - 1)
  have hsum : k + 1 + (D x - 1) = D x + k := by omega
  rw [hsplit, run_append, run_ticks_one, step_seekSrc_dest, Option.bind_some]
  have hwalk := seekSrc_gap_walk x y k (D x - 1) le_rfl
  rw [hsum] at hwalk
  exact hwalk

theorem step_take (x y : List Bool) (k : ℕ) (hk : k < y.length) :
    step machine 0 { state := 9, head := natInt (D x + k), tape := copyTape x y k } =
      some { state := seekDestState (y[k]), head := (natInt (D x + k) - 1), tape := takenTape x y k } := by
  have hread := copyTape_src x y k hk
  have hrule := rule_take (y[k])
  simp only [step, hread, hrule, writtenTape, moveHead, takenTape, Option.map_some]

set_option simprocs false in
theorem takenTape_dest (x y : List Bool) (k : ℕ) (_hk : k < y.length) :
    takenTape x y k (k : Int) = 4 := by
  have hD := D_pos x
  have hne' : (k : Int) ≠ natInt (D x + k) := by
    intro h
    have : k = D x + k := natInt_inj.mp h
    omega
  unfold takenTape
  rw [Function.update_apply, if_neg hne']
  exact copyTape_dest x y k

theorem takenTape_gap (x y : List Bool) (k i : ℕ) (hk : k < y.length)
    (h1 : k < i) (h2 : i < D x + k) :
    takenTape x y k (natInt i) = 2 := by
  have hD := D_pos x
  have hne : natInt i ≠ natInt (D x + k) := by
    intro h
    have : i = D x + k := natInt_inj.mp h
    omega
  unfold takenTape
  rw [Function.update_apply, if_neg hne, copyTape_gap x y k i h1 h2]

set_option simprocs false in
theorem step_seekDest_gap (b : Bool) (tape : Int → Fin 8) (i : ℕ)
    (ht : tape (natInt i) ≠ 4) :
    step machine 0 { state := seekDestState b, head := natInt i, tape } =
      some { state := seekDestState b, head := (natInt i - 1), tape } := by
  have hrule := rule_seekDest_else b _ ht
  simp only [step, hrule, writtenTape, moveHead, update_same, Option.map_some]

set_option simprocs false in
theorem seekDest_walk (b : Bool) (x y : List Bool) (k t : ℕ)
    (hk : k < y.length) (ht : t ≤ D x - 1) :
    run machine (ticks t)
        { state := seekDestState b, head := natInt (D x + k - 1), tape := takenTape x y k } =
      some { state := seekDestState b, head := natInt (D x + k - 1 - t), tape := takenTape x y k } := by
  have hD := D_pos x
  induction t with
  | zero => simp [ticks]
  | succ t ih =>
      have ht' : t ≤ D x - 1 := by omega
      rw [ticks_add, run_append, ih ht', Option.bind_some, run_ticks_one]
      have hi : k < D x + k - 1 - t := by omega
      have hj : D x + k - 1 - t < D x + k := by omega
      have hread : takenTape x y k (natInt (D x + k - 1 - t)) ≠ 4 := by
        rw [takenTape_gap x y k (D x + k - 1 - t) hk hi hj]; decide
      have hstep := step_seekDest_gap b (takenTape x y k) (D x + k - 1 - t) hread
      have hpred : natInt (D x + k - 1 - t) - 1 = natInt (D x + k - 1 - (t + 1)) := by
        have : 1 ≤ D x + k - 1 - t := by omega
        simpa [Nat.sub_add_eq] using natInt_pred (D x + k - 1 - t) this
      simpa [hpred] using hstep

theorem step_seekDest_write (b : Bool) (x y : List Bool) (k : ℕ)
    (hk : k < y.length) :
    step machine 0
        { state := seekDestState b, head := natInt k, tape := takenTape x y k } =
      some { state := 12, head := natInt (k + 1), tape := Function.update (takenTape x y k) (k : Int) (enc b) } := by
  have hread := takenTape_dest x y k hk
  have hrule := rule_seekDest_dest b
  simp only [step, hread, hrule, writtenTape, moveHead, Option.map_some]
  simp only [natInt_succ]

theorem step_placeDest (tape : Int → Fin 8) (h : Int) :
    step machine 0 { state := 12, head := h, tape } =
      some { state := 9, head := h, tape := Function.update tape h 4 } := by
  simp [step, rule_placeDest, writtenTape, moveHead]

set_option simprocs false in
theorem copyTapeNat_succ (x y : List Bool) (k i : ℕ) (hk : k < y.length) :
    copyTapeNat x y (k + 1) i =
      if i = k then enc y[k]
      else if i = k + 1 then 4
      else if i = D x + k then 2
      else copyTapeNat x y k i := by
  have hD := D_pos x
  by_cases hik : i = k
  · subst i
    have : k < k + 1 := Nat.lt_succ_self k
    simp [copyTapeNat, this, hk]
  · by_cases hik1 : i = k + 1
    · subst i
      simp [copyTapeNat, hik]
    · by_cases hs : i = D x + k
      · subst i
        have hgap : copyTapeNat x y (k + 1) (D x + k) = 2 := by
          unfold copyTapeNat
          have hn1 : ¬ D x + k < k + 1 := by omega
          have hn2 : ¬ D x + k = k + 1 := hik1
          have hp : D x + k < D x + (k + 1) := by omega
          simp [hn1, hn2, hp]
        rw [hgap, if_neg hik, if_neg hik1, if_pos rfl]
      · simp [hik, hik1, hs]
        unfold copyTapeNat
        split_ifs <;> try rfl
        all_goals omega

theorem update_natInt (f : Int → Fin 8) (i : ℕ) (a : Fin 8) (j : ℕ) :
    Function.update f (natInt i) a (natInt j) = if j = i then a else f (natInt j) := by
  simp [Function.update_apply, natInt_inj]

set_option simprocs false in
theorem takenTape_of_nat (x y : List Bool) (k i : ℕ) :
    takenTape x y k (natInt i) =
      if i = D x + k then (2 : Fin 8) else copyTapeNat x y k i := by
  unfold takenTape
  rw [update_natInt, copyTape_of_nat]

set_option simprocs false in
theorem copy_update (x y : List Bool) (k : ℕ) (hk : k < y.length) :
    Function.update
        (Function.update (takenTape x y k) (natInt k) (enc y[k]))
        (natInt (k + 1)) 4 =
      copyTape x y (k + 1) := by
  have hD := D_pos x
  funext z
  by_cases hL : z = -1
  · subst z
    have hk0 : ¬ (-1 = natInt k) := (natInt_ne_neg1 k).symm
    have hk1 : ¬ (-1 = natInt (k + 1)) := (natInt_ne_neg1 (k + 1)).symm
    have hs : ¬ (-1 = natInt (D x + k)) := (natInt_ne_neg1 (D x + k)).symm
    simp only [Function.update_apply]
    rw [if_neg hk1, if_neg hk0]
    unfold takenTape
    rw [Function.update_apply, if_neg hs]
    simp [copyTape]
  · by_cases hpos : 0 ≤ z
    · have hz : z = natInt z.toNat := (Int.toNat_of_nonneg hpos).symm
      rw [hz, copyTape_of_nat, copyTapeNat_succ x y k z.toNat hk]
      rw [update_natInt, update_natInt, takenTape_of_nat]
      split_ifs <;> first | rfl | omega
    · have hk0 : z ≠ natInt k := by
        intro h; have := natInt_nonneg k; omega
      have hk1 : z ≠ natInt (k + 1) := by
        intro h; have := natInt_nonneg (k + 1); omega
      have hs : z ≠ natInt (D x + k) := by
        intro h; have := natInt_nonneg (D x + k); omega
      simp only [Function.update_apply, hk0, hk1, takenTape, hs, ite_false]
      exact (copyTape_neg x y k hL hpos).trans (copyTape_neg x y (k + 1) hL hpos).symm

set_option simprocs false in
theorem copy_one (x y : List Bool) (k : ℕ) (hk : k < y.length) :
    run machine (ticks (2 * D x + 2)) (copyConfig x y k) =
      some (copyConfig x y (k + 1)) := by
  have hD := D_pos x
  have hsplit : 2 * D x + 2 = D x + 1 + (D x - 1) + 1 + 1 := by omega
  rw [hsplit, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, seekSrc_run x y k (le_of_lt hk), Option.bind_some,
    run_ticks_one, step_take x y k hk, Option.bind_some]
  have hpred : natInt (D x + k) - 1 = natInt (D x + k - 1) :=
    natInt_pred (D x + k) (by omega)
  simp only [hpred]
  rw [seekDest_walk y[k] x y k (D x - 1) hk le_rfl, Option.bind_some]
  have hhead : D x + k - 1 - (D x - 1) = k := by omega
  simp only [hhead]
  rw [run_ticks_one, step_seekDest_write (y[k]) x y k hk, Option.bind_some,
    run_ticks_one, step_placeDest]
  simp only [copyConfig]
  exact congrArg some (config_ext rfl (natInt_succ k) (copy_update x y k hk))

theorem copy_prefix (x y : List Bool) (k : ℕ) (hk : k ≤ y.length) :
    run machine (ticks (k * (2 * D x + 2))) (copyConfig x y 0) =
      some (copyConfig x y k) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
      have hk' : k < y.length := by omega
      have hsplit : (k + 1) * (2 * D x + 2) =
          k * (2 * D x + 2) + (2 * D x + 2) := by ring
      rw [hsplit, ticks_add, run_append, ih (by omega), Option.bind_some,
        copy_one x y k hk']

theorem copy_all (x y : List Bool) :
    run machine (ticks (y.length * (2 * D x + 2))) (copyConfig x y 0) =
      some (copyConfig x y y.length) :=
  copy_prefix x y y.length le_rfl

def erasedE (x y : List Bool) : Int → Fin 8 :=
  Function.update (copyTape x y y.length) (natInt (D x + y.length)) 2

def cleaned (y : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 3
  else if hz : 0 ≤ z ∧ z.toNat < y.length then enc y[z.toNat]
  else 2

theorem step_takeE (x y : List Bool) :
    step machine 0
        { state := 9, head := natInt (D x + y.length), tape := copyTape x y y.length } =
      some { state := 13, head := (natInt (D x + y.length) - 1), tape := erasedE x y } := by
  have hread := copyTape_E x y y.length le_rfl
  simp only [step, hread, rule_seekSrc_E, writtenTape, moveHead, erasedE, Option.map_some]

set_option simprocs false in
theorem erasedE_dest (x y : List Bool) : erasedE x y (natInt y.length) = 4 := by
  have hD := D_pos x
  have hne : natInt y.length ≠ natInt (D x + y.length) := by
    intro h; have := natInt_inj.mp h; omega
  unfold erasedE
  rw [Function.update_apply, if_neg hne]
  simpa [natInt] using copyTape_dest x y y.length

set_option simprocs false in
theorem erasedE_gap (x y : List Bool) (i : ℕ)
    (h1 : y.length < i) (h2 : i < D x + y.length) :
    erasedE x y (natInt i) = 2 := by
  have hne : natInt i ≠ natInt (D x + y.length) := by
    intro h; have := natInt_inj.mp h; omega
  unfold erasedE
  rw [Function.update_apply, if_neg hne, copyTape_gap x y y.length i h1 h2]

set_option simprocs false in
theorem step_seekDestClean_gap (tape : Int → Fin 8) (i : ℕ) (ht : tape (natInt i) ≠ 4) :
    step machine 0 { state := 13, head := natInt i, tape } =
      some { state := 13, head := (natInt i - 1), tape } := by
  have hrule := rule_seekDestClean_else _ ht
  simp only [step, hrule, writtenTape, moveHead, update_same, Option.map_some]

set_option simprocs false in
theorem seekDestClean_walk (x y : List Bool) (t : ℕ) (ht : t ≤ D x - 1) :
    run machine (ticks t)
        { state := 13, head := natInt (D x + y.length - 1), tape := erasedE x y } =
      some { state := 13, head := natInt (D x + y.length - 1 - t), tape := erasedE x y } := by
  have hD := D_pos x
  induction t with
  | zero => simp [ticks]
  | succ t ih =>
      have ht' : t ≤ D x - 1 := by omega
      rw [ticks_add, run_append, ih ht', Option.bind_some, run_ticks_one]
      have hi : y.length < D x + y.length - 1 - t := by omega
      have hj : D x + y.length - 1 - t < D x + y.length := by omega
      have hread : erasedE x y (natInt (D x + y.length - 1 - t)) ≠ 4 := by
        rw [erasedE_gap x y (D x + y.length - 1 - t) hi hj]; decide
      have hstep := step_seekDestClean_gap (erasedE x y) (D x + y.length - 1 - t) hread
      have hpred : natInt (D x + y.length - 1 - t) - 1 =
          natInt (D x + y.length - 1 - (t + 1)) := by
        have : 1 ≤ D x + y.length - 1 - t := by omega
        simpa [Nat.sub_add_eq] using natInt_pred (D x + y.length - 1 - t) this
      simpa [hpred] using hstep

theorem step_eraseDest (x y : List Bool) :
    step machine 0
        { state := 13, head := natInt y.length, tape := erasedE x y } =
      some { state := 14, head := (natInt y.length - 1), tape := Function.update (erasedE x y) (natInt y.length) 2 } := by
  have hread := erasedE_dest x y
  simp only [step, hread, rule_seekDestClean_dest, writtenTape, moveHead, Option.map_some]

set_option simprocs false in
theorem cleaned_of_nat (y : List Bool) (i : ℕ) :
    cleaned y (natInt i) = if h : i < y.length then enc y[i] else 2 := by
  unfold cleaned
  have hL : natInt i ≠ -1 := natInt_ne_neg1 i
  have hpos : 0 ≤ natInt i := natInt_nonneg i
  rw [if_neg hL]
  by_cases hi : i < y.length
  · have hc : 0 ≤ natInt i ∧ (natInt i).toNat < y.length := by
      refine ⟨hpos, ?_⟩; simp [natInt, toNat_ofNat, hi]
    rw [dif_pos hc, dif_pos hi]
    simp [natInt, toNat_ofNat]
  · have hc : ¬ (0 ≤ natInt i ∧ (natInt i).toNat < y.length) := by
      intro h
      have hlt : (natInt i).toNat < y.length := h.2
      simp [natInt, toNat_ofNat] at hlt
      exact hi hlt
    rw [dif_neg hc, dif_neg hi]

set_option simprocs false in
theorem copyTapeNat_final (x y : List Bool) (i : ℕ) :
    copyTapeNat x y y.length i =
      if i = y.length then 4
      else if i = D x + y.length then 5
      else if h : i < y.length then enc y[i]
      else if i < D x + y.length then 2
      else 2 := by
  unfold copyTapeNat
  by_cases hd : i = y.length
  · subst i
    have : ¬ y.length < y.length := by omega
    simp [this]
  · by_cases hE : i = D x + y.length
    · subst i
      have hD := D_pos x
      have hn1 : ¬ D x + y.length < y.length := by omega
      have hn2 : ¬ D x + y.length = y.length := hd
      have hn3 : ¬ D x + y.length < D x + y.length := by omega
      simp [hn1, hn2, hn3]
    · split_ifs <;> try rfl

set_option simprocs false in
theorem eraseDest_tape (x y : List Bool) :
    Function.update (erasedE x y) (natInt y.length) 2 = cleaned y := by
  have hD := D_pos x
  funext z
  by_cases hL : z = -1
  · subst z
    have hk : ¬ (-1 = natInt y.length) := (natInt_ne_neg1 y.length).symm
    have hE : ¬ (-1 = natInt (D x + y.length)) := (natInt_ne_neg1 (D x + y.length)).symm
    simp only [Function.update_apply]
    rw [if_neg hk]
    unfold erasedE
    rw [Function.update_apply, if_neg hE]
    simp [copyTape, cleaned]
  · by_cases hpos : 0 ≤ z
    · have hz : z = natInt z.toNat := (Int.toNat_of_nonneg hpos).symm
      rw [hz, cleaned_of_nat, update_natInt]
      unfold erasedE
      rw [update_natInt, copyTape_of_nat, copyTapeNat_final]
      split_ifs <;> first | rfl | omega
    · have hk : z ≠ natInt y.length := fun h => by
        have := natInt_nonneg y.length; omega
      have hE : z ≠ natInt (D x + y.length) := fun h => by
        have := natInt_nonneg (D x + y.length); omega
      simp only [Function.update_apply, hk]
      unfold erasedE
      rw [Function.update_apply, if_neg hE]
      exact (copyTape_neg x y y.length hL hpos).trans (by simp [cleaned, hL, hpos])

theorem step_seekLClean_nat (tape : Int → Fin 8) (p : ℕ) (ht : tape (natInt p) ≠ 3) :
    step machine 0 { state := 14, head := natInt p, tape } =
      some { state := 14, head := (natInt p - 1), tape } := by
  have hrule := rule_seekLClean_notL _ ht
  simp only [step, hrule, writtenTape, moveHead, update_same, Option.map_some]

theorem cleaned_nat_ne_L (y : List Bool) (i : ℕ) : cleaned y (natInt i) ≠ 3 := by
  rw [cleaned_of_nat]
  split_ifs with hi
  · have : enc y[i] ≠ 3 := by cases y[i] <;> decide
    exact this
  · decide

set_option simprocs false in
theorem seekLClean_to_neg1 (y : List Bool) (p : ℕ) :
    run machine (ticks (p + 1))
        { state := 14, head := natInt p, tape := cleaned y } =
      some { state := 14, head := -1, tape := cleaned y } := by
  induction p with
  | zero =>
      rw [run_ticks_one, step_seekLClean_nat]
      · simp
      · exact cleaned_nat_ne_L y 0
  | succ p ih =>
      have hsplit : p + 1 + 1 = 1 + (p + 1) := by omega
      rw [hsplit, ticks_add, run_append, run_ticks_one,
        step_seekLClean_nat (cleaned y) (p + 1) (cleaned_nat_ne_L y (p + 1)),
        Option.bind_some]
      have hhead : natInt (p + 1) - 1 = natInt p :=
        natInt_pred (p + 1) (by omega)
      simpa [hhead] using ih

theorem cleaned_L (y : List Bool) : cleaned y (-1) = 3 := by
  simp [cleaned]

theorem step_eraseL (y : List Bool) :
    step machine 0 { state := 14, head := -1, tape := cleaned y } =
      some (finalConfig y) := by
  have htape : Function.update (cleaned y) (-1) 2 = inputTape machine y := by
    funext z
    by_cases hL : z = -1
    · subst z
      simp [Function.update_apply, inputTape]
    · simp [Function.update_apply, hL, cleaned, inputTape]
      aesop
  simp [step, cleaned_L, rule_seekLClean_L, writtenTape, moveHead, finalConfig, htape]

theorem cleanup_from_dest (x y : List Bool) :
    run machine (ticks (D x + y.length + 1))
        { state := 13, head := natInt (D x + y.length - 1), tape := erasedE x y } =
      some (finalConfig y) := by
  have hD := D_pos x
  have hsplit : D x + y.length + 1 = (D x - 1) + 1 + (y.length + 1) := by omega
  rw [hsplit, ticks_add, ticks_add, run_append, run_append,
    seekDestClean_walk x y (D x - 1) le_rfl, Option.bind_some]
  have hhead : D x + y.length - 1 - (D x - 1) = y.length := by omega
  simp only [hhead]
  rw [run_ticks_one, step_eraseDest, Option.bind_some]
  have htape := eraseDest_tape x y
  simp only [htape]
  by_cases hy : y.length = 0
  · have hneg : natInt y.length - 1 = -1 := by simp [hy, natInt]
    simp only [hneg]
    have h1 : y.length + 1 = 1 := by omega
    rw [h1, run_ticks_one, step_eraseL]
  · have hp : 1 ≤ y.length := Nat.pos_of_ne_zero hy
    have hpred : natInt y.length - 1 = natInt (y.length - 1) :=
      natInt_pred y.length hp
    simp only [hpred]
    have hlen : y.length + 1 = (y.length - 1 + 1) + 1 := by omega
    rw [hlen, ticks_add, run_append, seekLClean_to_neg1 y (y.length - 1),
      Option.bind_some, run_ticks_one, step_eraseL]

theorem cleanup_run (x y : List Bool) :
    run machine (ticks (2 * D x + y.length + 2)) (copyConfig x y y.length) =
      some (finalConfig y) := by
  have hD := D_pos x
  have ht : 2 * D x + y.length + 2 = D x + (1 + (D x + y.length + 1)) := by omega
  rw [show ticks (2 * D x + y.length + 2) =
        ticks (D x) ++ ticks (1 + (D x + y.length + 1)) by rw [ht, ticks_add]]
  rw [run_append, seekSrc_run x y y.length le_rfl, Option.bind_some,
    ticks_add, run_append, run_ticks_one, step_takeE, Option.bind_some]
  have hpred : natInt (D x + y.length) - 1 = natInt (D x + y.length - 1) :=
    natInt_pred (D x + y.length) (by omega)
  simp only [hpred]
  exact cleanup_from_dest x y

def wellTime (x y : List Bool) : ℕ :=
  2 + D x + (y.length + 1) + (D x + y.length + 1) + 1 +
    y.length * (2 * D x + 2) + (2 * D x + y.length + 2)

theorem pair_run (x y : List Bool) :
    run machine (ticks (wellTime x y)) (initial machine (pairBits x y)) =
      some (finalConfig y) := by
  unfold wellTime
  repeat rw [ticks_add, run_append]
  rw [setup_run, Option.bind_some, parse_all, Option.bind_some, toEnd_all,
    Option.bind_some, seekL_all, Option.bind_some, markDest_run, Option.bind_some,
    copy_all, Option.bind_some, cleanup_run]

theorem pair_output (x y : List Bool) : Output machine y (finalConfig y) := by
  simp [Output, finalConfig]

noncomputable def boundPoly : Polynomial ℕ :=
  C 64 * (X + C 1) * (X + C 1)

theorem boundPoly_eval (n : ℕ) : boundPoly.eval n = 64 * (n + 1) * (n + 1) := by
  simp [boundPoly, eval_mul, eval_add, eval_C, eval_X]

theorem wellTime_le (x y : List Bool) :
    wellTime x y ≤ 64 * ((pairBits x y).length + 1) * ((pairBits x y).length + 1) := by
  have hD := D_pos x
  have hlen : (pairBits x y).length = D x + y.length := by simp [pairBits_length, D]
  unfold wellTime
  nlinarith

theorem pair_within (x y : List Bool) :
    ∃ n out, n ≤ boundPoly.eval (pairBits x y).length ∧
      run machine (ticks n) (initial machine (pairBits x y)) = some out ∧
      Output machine (secondBits (pairBits x y)) out := by
  refine ⟨wellTime x y, finalConfig y, ?_, pair_run x y, ?_⟩
  · rw [boundPoly_eval]
    exact wellTime_le x y
  · simpa [secondBits_pair] using pair_output x y

theorem unpairBits_nil : unpairBits ([] : List Bool) = none := rfl

theorem unpairBits_false (rest : List Bool) :
    unpairBits (false :: rest) = some ([], rest) := rfl

theorem unpairBits_true_nil : unpairBits [true] = none := rfl

theorem unpairBits_true_cons (b : Bool) (rest : List Bool) :
    unpairBits (true :: b :: rest) =
      (unpairBits rest).map fun z => (b :: z.1, z.2) := rfl

theorem unpairBits_none_cases (w : List Bool) (h : unpairBits w = none) :
    w = [] ∨ w = [true] ∨
      ∃ b rest, w = true :: b :: rest ∧ unpairBits rest = none := by
  cases w with
  | nil => exact Or.inl rfl
  | cons a rest =>
      cases a with
      | false => simp [unpairBits] at h
      | true =>
          cases rest with
          | nil => exact Or.inr (Or.inl rfl)
          | cons b rest =>
              simp [unpairBits] at h
              cases hr : unpairBits rest with
              | none => exact Or.inr (Or.inr ⟨b, rest, rfl, hr⟩)
              | some z => simp [hr] at h

theorem unpairBits_none_form (w : List Bool) (h : unpairBits w = none) :
    ∃ x : List Bool,
      w = List.flatMap (fun b => [true, b]) x ∨
        w = List.flatMap (fun b => [true, b]) x ++ [true] := by
  induction hl : w.length using Nat.strong_induction_on generalizing w h with
  | h n ih =>
      subst hl
      rcases unpairBits_none_cases w h with h0 | h1 | ⟨b, rest, hw, hr⟩
      · exact ⟨[], Or.inl (by simp [h0])⟩
      · exact ⟨[], Or.inr (by simp [h1])⟩
      · have hlen : rest.length < w.length := by simp [hw]
        obtain ⟨x, hx⟩ := ih rest.length hlen rest hr rfl
        rcases hx with hx | hx
        · refine ⟨b :: x, Or.inl ?_⟩
          simp [hw, hx]
        · refine ⟨b :: x, Or.inr ?_⟩
          simp [hw, hx]

theorem drop_eq_cons (w : List Bool) (n : ℕ) (hn : n < w.length) :
    w.drop n = w[n] :: w.drop (n + 1) := by
  induction n generalizing w with
  | zero =>
      cases w with
      | nil => cases hn
      | cons a rest => simp
  | succ n ih =>
      cases w with
      | nil => cases hn
      | cons a rest =>
          simpa [List.drop] using ih rest (Nat.lt_of_succ_lt_succ hn)

theorem drop_head_eq (w : List Bool) (n : ℕ) (a : Bool) (rest : List Bool)
    (h : w.drop n = a :: rest) :
    ∃ hlt : n < w.length, w[n]'hlt = a ∧ w.drop (n + 1) = rest := by
  have hlt : n < w.length := by
    have hne : w.drop n ≠ [] := by simp [h]
    exact Nat.lt_of_not_le fun hge => hne (List.drop_eq_nil_of_le hge)
  have heq := (drop_eq_cons w n hlt).symm.trans h
  exact ⟨hlt, List.cons.inj heq⟩

theorem boundary_nat (i : ℕ) : boundaryTape (natInt i) = 2 := by
  have hL : natInt i ≠ -1 := natInt_ne_neg1 i
  simp [boundaryTape, hL]

theorem boundary_nat_ne_L (i : ℕ) : boundaryTape (natInt i) ≠ 3 := by
  rw [boundary_nat]
  decide

theorem boundary_L : boundaryTape (-1) = 3 := rfl

set_option simprocs false in
theorem step_malLeft_nat (p : ℕ) :
    step machine 0 { state := 16, head := natInt p, tape := boundaryTape } =
      some { state := 16, head := (natInt p - 1), tape := boundaryTape } := by
  have ht : boundaryTape (natInt p) ≠ 3 := boundary_nat_ne_L p
  have hrule := rule_malLeft_notL _ ht
  have hread : boundaryTape (natInt p) = 2 := boundary_nat p
  have htape : Function.update boundaryTape (natInt p) 2 = boundaryTape := by
    rw [← hread]
    exact update_same boundaryTape (natInt p)
  simp [step, hrule, writtenTape, moveHead, htape]

theorem step_malLeft_L :
    step machine 0 { state := 16, head := -1, tape := boundaryTape } =
      some (finalConfig []) := by
  have htape : Function.update boundaryTape (-1) 2 = inputTape machine ([] : List Bool) := by
    rw [boundary_erase_L, inputTape_nil]
  simp [step, boundary_L, rule_malLeft_L, writtenTape, moveHead, finalConfig, htape]

set_option simprocs false in
theorem malLeft_to_neg1 (p : ℕ) :
    run machine (ticks (p + 1))
        { state := 16, head := natInt p, tape := boundaryTape } =
      some { state := 16, head := -1, tape := boundaryTape } := by
  induction p with
  | zero =>
      rw [run_ticks_one, step_malLeft_nat]
      simp
  | succ p ih =>
      have hsplit : p + 1 + 1 = 1 + (p + 1) := by omega
      rw [hsplit, ticks_add, run_append, run_ticks_one, step_malLeft_nat (p + 1),
        Option.bind_some]
      have hhead : natInt (p + 1) - 1 = natInt p :=
        natInt_pred (p + 1) (by omega)
      simpa [hhead] using ih

set_option simprocs false in
theorem malLeft_from (n : ℕ) :
    run machine (ticks (n + 1))
        { state := 16, head := (natInt n - 1), tape := boundaryTape } =
      some (finalConfig []) := by
  by_cases hn : n = 0
  · have hhead : natInt n - 1 = -1 := by simp [hn, natInt]
    subst hn
    simp only [hhead]
    rw [run_ticks_one, step_malLeft_L]
  · have hp : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hpred : natInt n - 1 = natInt (n - 1) := natInt_pred n hp
    simp only [hpred]
    have hsplit : n + 1 = (n - 1 + 1) + 1 := by omega
    rw [hsplit, ticks_add, run_append, malLeft_to_neg1 (n - 1), Option.bind_some,
      run_ticks_one, step_malLeft_L]

set_option simprocs false in
theorem parse_mal_from (w : List Bool) (n : ℕ) (hn : n ≤ w.length)
    (hmal : unpairBits (w.drop n) = none) :
    run machine (ticks (w.length - n + 1))
        { state := 4, head := natInt n, tape := erasedTape w n } =
      some { state := 16, head := (natInt w.length - 1), tape := erasedTape w w.length } := by
  suffices hmain :
      ∀ d n, d = w.length - n → n ≤ w.length → unpairBits (w.drop n) = none →
        run machine (ticks (w.length - n + 1))
            { state := 4, head := natInt n, tape := erasedTape w n } =
          some { state := 16, head := (natInt w.length - 1), tape := erasedTape w w.length } by
    exact hmain (w.length - n) n rfl hn hmal
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hd hn hmal
    cases hdrop : w.drop n with
    | nil =>
        have hnlen : w.length ≤ n := List.drop_eq_nil_iff.mp hdrop
        have heq : n = w.length := by omega
        subst heq
        have hticks : w.length - w.length + 1 = 1 := by omega
        rw [hticks, run_ticks_one]
        exact step_parse_blank w w.length le_rfl
    | cons a rest =>
        obtain ⟨hlt, ha, htl⟩ := drop_head_eq w n a rest hdrop
        have hatrue : a = true := by
          cases a with
          | false =>
              rw [hdrop] at hmal
              simp [unpairBits] at hmal
              contradiction
          | true => rfl
        subst hatrue
        cases rest with
        | nil =>
            have hd1 : w.length - n = 1 := by
              have hlen : (w.drop n).length = 1 := by simp [hdrop]
              rw [List.length_drop] at hlen
              omega
            have hn1 : n + 1 = w.length := by omega
            have hticks : w.length - n + 1 = 2 := by omega
            have htrue : w[n] = true := ha
            rw [hticks, show (2 : ℕ) = 1 + 1 from rfl, ticks_add, run_append,
              run_ticks_one, step_parse_true w n hlt htrue, Option.bind_some,
              run_ticks_one]
            simp only [hn1]
            exact step_parseBit_blank w w.length le_rfl
        | cons b rest =>
            have hlt2 : n + 1 < w.length := by
              have hlen : (w.drop n).length = rest.length + 2 := by simp [hdrop]
              rw [List.length_drop] at hlen
              omega
            have htrue : w[n] = true := ha
            obtain ⟨_, hb, htl2⟩ := drop_head_eq w (n + 1) b rest htl
            have hmal' : unpairBits (w.drop (n + 2)) = none := by
              rw [htl2]
              rw [hdrop] at hmal
              simp [unpairBits] at hmal
              cases hrest : unpairBits rest with
              | none => rfl
              | some z =>
                  simp [hrest] at hmal
                  contradiction
            have hsplit : w.length - n + 1 = 2 + (w.length - (n + 2) + 1) := by omega
            rw [show ticks (w.length - n + 1) =
                  ticks 2 ++ ticks (w.length - (n + 2) + 1) by rw [hsplit, ticks_add]]
            rw [run_append, show ticks 2 = ticks 1 ++ ticks 1 from rfl, run_append,
              run_ticks_one, step_parse_true w n hlt htrue, Option.bind_some,
              run_ticks_one, step_parseBit w (n + 1) hlt2, Option.bind_some]
            have hd' : w.length - (n + 2) < d := by omega
            exact ih (w.length - (n + 2)) hd' (n + 2) rfl (by omega) hmal'

set_option simprocs false in
theorem mal_run {w : List Bool} (h : unpairBits w = none) :
    run machine (ticks (2 * w.length + 4)) (initial machine w) =
      some (finalConfig []) := by
  have hsplit : 2 * w.length + 4 = 2 + ((w.length + 1) + (w.length + 1)) := by omega
  rw [show ticks (2 * w.length + 4) =
        ticks 2 ++ ticks ((w.length + 1) + (w.length + 1)) by rw [hsplit, ticks_add]]
  rw [run_append, setup_run, Option.bind_some]
  have hhead :
      ({ state := 4, head := 0, tape := erasedTape w 0 } : Configuration 17 8) =
        { state := 4, head := natInt 0, tape := erasedTape w 0 } := by
    simp [natInt_zero]
  rw [hhead]
  have hparse := parse_mal_from w 0 (Nat.zero_le _) (by simpa using h)
  have hlen0 : w.length - 0 + 1 = w.length + 1 := by omega
  rw [hlen0] at hparse
  rw [ticks_add, run_append, hparse, Option.bind_some]
  have htape := erased_complete w w.length le_rfl
  simp only [htape]
  exact malLeft_from w.length

theorem malTime_le (n : ℕ) : 2 * n + 4 ≤ 64 * (n + 1) * (n + 1) := by
  nlinarith

theorem secondBits_computes :
    ComputesWithin machine secondBits (fun n => boundPoly.eval n) := by
  intro w
  cases h : unpairBits w with
  | none =>
      refine ⟨2 * w.length + 4, finalConfig [], ?_, mal_run h, ?_⟩
      · simpa [boundPoly_eval] using malTime_le w.length
      · have hout : Output machine [] (finalConfig []) := by
          simp [Output, finalConfig]
        simpa [secondBits_none h] using hout
  | some p =>
      rcases p with ⟨x, y⟩
      have hw : w = pairBits x y := (unpairBits_eq_some).1 h
      subst hw
      exact pair_within x y

theorem secondBits_polyBitTime : PolyBitTime secondBits :=
  ⟨17, 8, machine, boundPoly, secondBits_computes⟩

end PakFixedPolyomino.StandardBitPairProjection
