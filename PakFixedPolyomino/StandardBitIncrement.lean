import PakFixedPolyomino.StandardBitTime
import Mathlib.Computability.Encoding

/-! # Literal little-endian increment: carry right, write true, return left. -/

namespace PakFixedPolyomino.StandardBitIncrement

open Computability StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: incrementBits bs

def truePrefix : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: bs => truePrefix bs + 1

def machine : DeterministicMachine 4 3 where
  rule := fun q a _ =>
    if q = 2 then
      if a = 1 then some { target := 2, write := 0, move := .right }
      else some { target := 3, write := 1, move := .left }
    else if q = 3 then
      if a = 2 then some { target := 0, write := 2, move := .right }
      else some { target := 3, write := a, move := .left }
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

theorem rule_scan_true : machine.rule 2 1 0 =
    some { write := 0, target := 2, move := .right } := rfl

theorem rule_scan_false : machine.rule 2 0 0 =
    some { write := 1, target := 3, move := .left } := rfl

theorem rule_scan_blank : machine.rule 2 2 0 =
    some { write := 1, target := 3, move := .left } := rfl

theorem rule_return_zero : machine.rule 3 0 0 =
    some { write := 0, target := 3, move := .left } := rfl

theorem rule_return_blank : machine.rule 3 2 0 =
    some { write := 2, target := 0, move := .right } := rfl

theorem truePrefix_le (x : List Bool) : truePrefix x ≤ x.length := by
  induction x with
  | nil => simp [truePrefix]
  | cons b bs ih =>
      cases b <;> simp [truePrefix]; omega

theorem increment_length (x : List Bool) :
    (incrementBits x).length ≤ x.length + 1 := by
  induction x with
  | nil => simp [incrementBits]
  | cons b bs ih =>
      cases b <;> simp [incrementBits]; omega

theorem incrementBits_spec (x : List Bool) :
    incrementBits x =
      List.replicate (truePrefix x) false ++ true :: x.drop (truePrefix x + 1) := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false => rfl
      | true =>
          simp [incrementBits, truePrefix, List.replicate_succ, List.cons_append, ih]

theorem increment_length_eq (x : List Bool) :
    (incrementBits x).length =
      if truePrefix x = x.length then x.length + 1 else x.length := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          simp [incrementBits, truePrefix]
      | true =>
          simp [incrementBits, truePrefix, ih]
          split_ifs <;> omega

theorem truePrefix_lt_increment_length (x : List Bool) :
    truePrefix x < (incrementBits x).length := by
  have hle := truePrefix_le x
  rw [increment_length_eq]
  split <;> omega

theorem truePrefix_get (x : List Bool) (k : ℕ) (hk : k < truePrefix x) :
    x[k]'(Nat.lt_of_lt_of_le hk (truePrefix_le x)) = true := by
  induction x generalizing k with
  | nil => simp [truePrefix] at hk
  | cons b bs ih =>
      cases b with
      | false => simp [truePrefix] at hk
      | true =>
          cases k with
          | zero => rfl
          | succ k =>
              simp only [truePrefix] at hk
              have hk' : k < truePrefix bs := by omega
              simpa using ih k hk'

theorem truePrefix_stop (x : List Bool) (h : truePrefix x < x.length) :
    x[truePrefix x] = false := by
  induction x with
  | nil => simp [truePrefix] at h
  | cons b bs ih =>
      cases b with
      | false => rfl
      | true =>
          simp only [truePrefix, List.length_cons] at h ⊢
          exact ih (by omega)

theorem incrementBits_getElem?_lt (x : List Bool) (k : ℕ) (hk : k < truePrefix x) :
    (incrementBits x)[k]? = some false := by
  have hleft : k < (List.replicate (truePrefix x) false).length := by
    simpa [List.length_replicate] using hk
  rw [incrementBits_spec, List.getElem?_append_left hleft, List.getElem?_replicate]
  simp [hk]

theorem incrementBits_getElem?_eq (x : List Bool) :
    (incrementBits x)[truePrefix x]? = some true := by
  have hleft : (List.replicate (truePrefix x) false).length ≤ truePrefix x := by
    simp [List.length_replicate]
  rw [incrementBits_spec, List.getElem?_append_right hleft]
  simp [List.length_replicate]

theorem incrementBits_getElem?_gt (x : List Bool) (i : ℕ)
    (hgt : truePrefix x < i) :
    (incrementBits x)[i]? = x[i]? := by
  have hleft : (List.replicate (truePrefix x) false).length ≤ i := by
    simp [List.length_replicate]; omega
  rw [incrementBits_spec, List.getElem?_append_right hleft]
  simp only [List.length_replicate]
  have hidx : i - truePrefix x = (i - truePrefix x - 1) + 1 := by omega
  rw [hidx, List.getElem?_cons_succ, List.getElem?_drop]
  congr 1
  omega

theorem get_of_getElem? {α} {l : List α} {i : ℕ} {a : α} {h : i < l.length}
    (heq : l[i]? = some a) : l[i] = a :=
  Option.some.inj ((List.getElem?_eq_getElem h).symm.trans heq)

theorem increment_encodePosNum (p : PosNum) :
    incrementBits (encodePosNum p) = encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit0 n _ih => rfl
  | bit1 n ih =>
      change false :: incrementBits (encodePosNum n) =
        false :: encodePosNum n.succ
      rw [ih]

theorem increment_encodeNum (n : Num) :
    incrementBits (encodeNum n) = encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos p => simpa [encodeNum, Num.succ, Num.succ'] using increment_encodePosNum p

theorem increment_encodeNat (n : ℕ) :
    incrementBits (encodeNat n) = encodeNat (n + 1) := by
  simp only [encodeNat]
  rw [Nat.cast_add, Nat.cast_one, Num.add_one]
  exact increment_encodeNum (n : Num)

def prefixTape (x : List Bool) (k : ℕ) (z : Int) : Fin 3 :=
  if 0 ≤ z ∧ z < (k : Int) then 0
  else inputTape machine x z

def scanConfig (x : List Bool) (k : ℕ) : Configuration 4 3 :=
  ⟨2, k, prefixTape x k⟩

def returnConfig (x : List Bool) (z : Int) : Configuration 4 3 :=
  ⟨3, z, inputTape machine (incrementBits x)⟩

def finalConfig (x : List Bool) : Configuration 4 3 :=
  ⟨0, 0, inputTape machine (incrementBits x)⟩

theorem scanConfig_zero (x : List Bool) : scanConfig x 0 = initial machine x := by
  unfold scanConfig initial; congr 1; funext z
  simp [prefixTape, show ¬(0 ≤ z ∧ z < 0) from by omega]

theorem prefixTape_at_head (x : List Bool) (k : ℕ) :
    prefixTape x k (k : Int) = inputTape machine x (k : Int) := by
  simp [prefixTape]

theorem prefixTape_write (x : List Bool) (k : ℕ) :
    Function.update (prefixTape x k) (k : Int) 0 = prefixTape x (k + 1) := by
  funext z
  by_cases hz : z = (k : Int)
  · subst z
    have hinside : 0 ≤ (k : Int) ∧ (k : Int) < ((k + 1 : ℕ) : Int) := by omega
    simp only [Function.update_self, prefixTape, if_pos hinside]
  · have hcond : (0 ≤ z ∧ z < ((k + 1 : ℕ) : Int)) ↔
        (0 ≤ z ∧ z < (k : Int)) := by omega
    simp only [Function.update_of_ne hz, prefixTape, hcond]

theorem scan_step (x : List Bool) (k : ℕ) (hk : k < truePrefix x) :
    step machine 0 (scanConfig x k) = some (scanConfig x (k + 1)) := by
  have hx : k < x.length := Nat.lt_of_lt_of_le hk (truePrefix_le x)
  have hread : inputTape machine x (k : Int) = 1 := by
    rw [inputTape_ofNat machine x k hx, truePrefix_get x k hk]
    rfl
  have hhead : ((k : Int) + 1) = ((k + 1 : ℕ) : Int) := by omega
  simp only [step, scanConfig, prefixTape_at_head, hread, rule_scan_true,
    Option.map_some, moveHead, writtenTape]
  rw [prefixTape_write, hhead]

theorem scan_run (x : List Bool) (k : ℕ) (hk : k ≤ truePrefix x) :
    run machine (ticks k) (initial machine x) = some (scanConfig x k) := by
  induction k with
  | zero => rw [scanConfig_zero]; rfl
  | succ k ih =>
      have hkprev : k ≤ truePrefix x := by omega
      have hklt : k < truePrefix x := by omega
      rw [ticks_add k 1, run_append, ih hkprev, Option.bind_some]
      rw [run_ticks_one]
      exact scan_step x k hklt

theorem increment_tape_nat (x : List Bool) (i : ℕ) :
    inputTape machine (incrementBits x) (i : Int) =
      if i < truePrefix x then 0
      else if i = truePrefix x then 1
      else inputTape machine x (i : Int) := by
  by_cases hlt : i < truePrefix x
  · have hi : i < (incrementBits x).length :=
      lt_trans hlt (truePrefix_lt_increment_length x)
    rw [if_pos hlt, inputTape_ofNat machine (incrementBits x) i hi,
      get_of_getElem? (incrementBits_getElem?_lt x i hlt)]
    rfl
  · rw [if_neg hlt]
    by_cases heq : i = truePrefix x
    · subst i
      have hi := truePrefix_lt_increment_length x
      rw [if_pos rfl, inputTape_ofNat machine (incrementBits x) _ hi,
        get_of_getElem? (incrementBits_getElem?_eq x)]
      rfl
    · rw [if_neg heq]
      have hgt : truePrefix x < i := by omega
      by_cases hx : i < x.length
      · have hi : i < (incrementBits x).length := by
          rw [increment_length_eq]; split <;> omega
        have hbit : (incrementBits x)[i]? = some (x[i]) :=
          (incrementBits_getElem?_gt x i hgt).trans (List.getElem?_eq_getElem hx)
        rw [inputTape_ofNat machine (incrementBits x) i hi,
          inputTape_ofNat machine x i hx, get_of_getElem? hbit]
      · have hy : (x.length : Int) ≤ (i : Int) :=
          Nat.cast_le.mpr (Nat.not_lt.mp hx)
        have hz : ((incrementBits x).length : Int) ≤ (i : Int) := by
          have hle := truePrefix_le x
          rw [increment_length_eq]
          split <;> omega
        rw [inputTape_ge machine (incrementBits x) (i : Int) hz,
          inputTape_ge machine x (i : Int) hy]

theorem increment_tape (x : List Bool) (z : Int) :
    inputTape machine (incrementBits x) z =
      if 0 ≤ z ∧ z < (truePrefix x : Int) then 0
      else if z = (truePrefix x : Int) then 1
      else inputTape machine x z := by
  by_cases hz : 0 ≤ z
  · have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg hz).symm
    rw [hz', increment_tape_nat]
    by_cases hlt : z.toNat < truePrefix x
    · have hpre : 0 ≤ (z.toNat : Int) ∧ (z.toNat : Int) < (truePrefix x : Int) :=
        ⟨Nat.cast_nonneg _, Int.ofNat_lt.mpr hlt⟩
      rw [if_pos hlt, if_pos hpre]
    · have hpre : ¬(0 ≤ (z.toNat : Int) ∧ (z.toNat : Int) < (truePrefix x : Int)) :=
        fun h => hlt (Int.ofNat_lt.mp h.2)
      rw [if_neg hlt, if_neg hpre]
      by_cases heq : z.toNat = truePrefix x
      · have heq' : (z.toNat : Int) = (truePrefix x : Int) := Int.natCast_inj.mpr heq
        rw [if_pos heq, if_pos heq']
      · have heq' : ¬(z.toNat : Int) = (truePrefix x : Int) := mt Int.natCast_inj.mp heq
        rw [if_neg heq, if_neg heq']
  · have hneg : z < 0 := by omega
    have hlt : ¬(0 ≤ z ∧ z < (truePrefix x : Int)) := by omega
    have heq : ¬ z = (truePrefix x : Int) := by omega
    rw [if_neg hlt, if_neg heq, inputTape_neg machine (incrementBits x) z hneg,
      inputTape_neg machine x z hneg]

theorem prefixTape_turn (x : List Bool) :
    Function.update (prefixTape x (truePrefix x)) (truePrefix x : Int) 1 =
      inputTape machine (incrementBits x) := by
  funext z
  by_cases hz : z = (truePrefix x : Int)
  · subst z
    rw [Function.update_self, increment_tape]
    have hpre : ¬(0 ≤ (truePrefix x : Int) ∧
        (truePrefix x : Int) < (truePrefix x : Int)) := by omega
    rw [if_neg hpre, if_pos rfl]
  · rw [Function.update_of_ne hz, prefixTape, increment_tape]
    by_cases hpre : 0 ≤ z ∧ z < (truePrefix x : Int)
    · rw [if_pos hpre, if_pos hpre]
    · rw [if_neg hpre, if_neg hpre, if_neg hz]

theorem scan_turn (x : List Bool) :
    step machine 0 (scanConfig x (truePrefix x)) =
      some (returnConfig x ((truePrefix x : Int) - 1)) := by
  by_cases hlt : truePrefix x < x.length
  · have hread : inputTape machine x (truePrefix x : Int) = 0 := by
      rw [inputTape_ofNat machine x (truePrefix x) hlt, truePrefix_stop x hlt]
      rfl
    simp only [step, scanConfig, prefixTape_at_head, hread, rule_scan_false,
      Option.map_some, moveHead, writtenTape, returnConfig]
    rw [prefixTape_turn]
  · have heq : truePrefix x = x.length := by
      have := truePrefix_le x; omega
    have hread : inputTape machine x (truePrefix x : Int) = 2 := by
      rw [heq]; exact inputTape_ge machine x _ (by rfl)
    simp only [step, scanConfig, prefixTape_at_head, hread, rule_scan_blank,
      Option.map_some, moveHead, writtenTape, returnConfig]
    rw [prefixTape_turn]

theorem return_step (x : List Bool) (k : ℕ) (hk : k < truePrefix x) :
    step machine 0 (returnConfig x (k : Int)) =
      some (returnConfig x ((k : Int) - 1)) := by
  have hi : k < (incrementBits x).length :=
    lt_trans hk (truePrefix_lt_increment_length x)
  have hread : inputTape machine (incrementBits x) (k : Int) = 0 := by
    rw [inputTape_ofNat machine (incrementBits x) k hi,
      get_of_getElem? (incrementBits_getElem?_lt x k hk)]
    rfl
  simp only [step, returnConfig, hread, rule_return_zero, Option.map_some,
    moveHead, writtenTape]
  rw [← hread, Function.update_eq_self]

theorem return_run (x : List Bool) (n : ℕ) (hn : n ≤ truePrefix x) :
    run machine (ticks n) (returnConfig x ((n : Int) - 1)) =
      some (returnConfig x (-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnlt : n < truePrefix x := by omega
      have hnle : n ≤ truePrefix x := by omega
      change run machine (0 :: ticks n)
          (returnConfig x ((n + 1 : ℕ) - (1 : Int))) = _
      have hcast : ((n + 1 : ℕ) : Int) - 1 = (n : Int) := by omega
      rw [hcast, run_cons, return_step x n hnlt, Option.bind_some]
      exact ih hnle

theorem return_finish (x : List Bool) :
    step machine 0 (returnConfig x (-1)) = some (finalConfig x) := by
  have hblank : inputTape machine (incrementBits x) (-1) = 2 :=
    inputTape_neg machine (incrementBits x) (-1) (by omega)
  simp only [step, returnConfig, hblank, rule_return_blank, Option.map_some,
    moveHead, writtenTape, finalConfig]
  rw [← hblank, Function.update_eq_self]
  rfl

theorem increment_run (x : List Bool) :
    run machine (ticks (2 * truePrefix x + 2)) (initial machine x) =
      some (finalConfig x) := by
  have htime : 2 * truePrefix x + 2 = truePrefix x + 1 + truePrefix x + 1 := by omega
  rw [htime, ticks_add, ticks_add, ticks_add, run_append, run_append, run_append,
    scan_run x (truePrefix x) le_rfl, Option.bind_some, run_ticks_one, scan_turn,
    Option.bind_some, return_run x (truePrefix x) le_rfl, Option.bind_some,
    run_ticks_one]
  exact return_finish x

theorem increment_computes :
    ComputesWithin machine incrementBits (fun n => 2 * n + 2) := by
  intro x
  refine ⟨2 * truePrefix x + 2, finalConfig x, ?_, increment_run x, rfl, rfl, rfl⟩
  have := truePrefix_le x
  change 2 * truePrefix x + 2 ≤ 2 * x.length + 2; omega

theorem increment_polyBitTime : PolyBitTime incrementBits := by
  refine ⟨4, 3, machine, Polynomial.C 2 * Polynomial.X + Polynomial.C 2, ?_⟩
  simpa using increment_computes

theorem increment_exact :
    (∀ n, incrementBits (encodeNat n) = encodeNat (n + 1)) ∧
    (∀ x, (incrementBits x).length ≤ x.length + 1) ∧
    (∀ x, run machine (ticks (2 * truePrefix x + 2)) (initial machine x) =
      some (finalConfig x)) ∧
    ComputesWithin machine incrementBits (fun n => 2 * n + 2) ∧
    PolyBitTime incrementBits :=
  ⟨increment_encodeNat, increment_length, increment_run,
    increment_computes, increment_polyBitTime⟩

end PakFixedPolyomino.StandardBitIncrement
