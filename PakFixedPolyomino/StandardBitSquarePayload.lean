import PakFixedPolyomino.StandardBitTime

/-! Ordinary 27-state Fin19 encoder of `replicate (n*n) false ++ true :: x`.
Source bits are preserved. n≤1 uses the small-copy path; n≥2 writes
n*(n-1) extra zeros then copies source after a final separator. The sixth
degree bound counts actual tape transitions. Compact loading and the
original headline remain open. -/

namespace PakFixedPolyomino.StandardBitSquarePayload

open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)
open Polynomial

def unproc : Bool → Fin 19
  | false => 3
  | true => 6

def active : Bool → Fin 19
  | false => 9
  | true => 10

def proc : Bool → Fin 19
  | false => 7
  | true => 8

def writeBit : Bool → Fin 19
  | false => 0
  | true => 1

def seekBit : Bool → Fin 27
  | false => 7
  | true => 10

def bitAt (x : List Bool) (i : Nat) : Bool :=
  if h : i < x.length then x[i] else false

@[simp] theorem bitAt_lt (x : List Bool) (i : Nat) (h : i < x.length) :
    bitAt x i = x[i] := by simp [bitAt, h]

def cursorOf (a : Fin 19) : Option (Fin 19) :=
  if a = 3 then some 11
  else if a = 6 then some 12
  else if a = 7 then some 13
  else if a = 8 then some 14
  else if a = 9 then some 15
  else if a = 10 then some 16
  else none

def baseOf (a : Fin 19) : Option (Fin 19) :=
  if a = 11 then some 3
  else if a = 12 then some 6
  else if a = 13 then some 7
  else if a = 14 then some 8
  else if a = 15 then some 9
  else if a = 16 then some 10
  else none

theorem cursorOf_unproc (b : Bool) :
    cursorOf (unproc b) = some (if b then (12 : Fin 19) else 11) := by
  cases b <;> simp [cursorOf, unproc]

theorem cursorOf_proc (b : Bool) :
    cursorOf (proc b) = some (if b then (14 : Fin 19) else 13) := by
  cases b <;> simp [cursorOf, proc]

theorem cursorOf_active (b : Bool) :
    cursorOf (active b) = some (if b then (16 : Fin 19) else 15) := by
  cases b <;> simp [cursorOf, active]

theorem baseOf_cursorOf (a c : Fin 19) (h : cursorOf a = some c) :
    baseOf c = some a := by
  unfold cursorOf at h
  split_ifs at h with h3 h6 h7 h8 h9 h10 <;> (try cases h) <;>
    (try simp [baseOf, h3]) <;> (try simp [baseOf, h6]) <;>
    (try simp [baseOf, h7]) <;> (try simp [baseOf, h8]) <;>
    (try simp [baseOf, h9]) <;> (try simp [baseOf, h10])

def machine : DeterministicMachine 27 19 where
  rule := fun q a _ =>
    if q = 2 then some { target := 3, write := a, move := .left }
    else if q = 3 then some { target := 4, write := 4, move := .right }
    else if q = 4 then
      if a = 2 then some { target := 25, write := 5, move := .left }
      else if a = 0 then some { target := 12, write := 3, move := .right }
      else if a = 1 then some { target := 12, write := 6, move := .right }
      else none
    else if q = 12 then
      if a = 2 then some { target := 25, write := 5, move := .left }
      else if a = 0 then some { target := 13, write := 3, move := .right }
      else if a = 1 then some { target := 13, write := 6, move := .right }
      else none
    else if q = 13 then
      if a = 2 then some { target := 5, write := 5, move := .left }
      else if a = 0 then some { target := 13, write := 3, move := .right }
      else if a = 1 then some { target := 13, write := 6, move := .right }
      else none
    else if q = 25 then
      if a = 4 then some { target := 26, write := 4, move := .right }
      else some { target := 25, write := a, move := .left }
    else if q = 5 then
      if a = 4 then some { target := 14, write := 4, move := .right }
      else some { target := 5, write := a, move := .left }
    else if q = 14 then
      if a = 7 ∨ a = 8 then some { target := 14, write := a, move := .right }
      else if a = 3 then some { target := 15, write := 9, move := .left }
      else if a = 6 then some { target := 15, write := 10, move := .left }
      else if a = 5 then some { target := 22, write := 5, move := .right }
      else none
    else if q = 15 then
      if a = 4 then some { target := 16, write := 4, move := .right }
      else some { target := 15, write := a, move := .left }
    else if q = 16 then
      some { target := 17, write := a, move := .right }
    else if q = 17 then
      if a = 5 then some { target := 20, write := 5, move := .left }
      else match cursorOf a with
        | some c => some { target := 18, write := c, move := .right }
        | none => none
    else if q = 18 then
      if a = 2 then some { target := 19, write := 0, move := .left }
      else some { target := 18, write := a, move := .right }
    else if q = 19 then
      match baseOf a with
        | some b => some { target := 17, write := b, move := .right }
        | none => some { target := 19, write := a, move := .left }
    else if q = 20 then
      if a = 9 then some { target := 21, write := 7, move := .left }
      else if a = 10 then some { target := 21, write := 8, move := .left }
      else some { target := 20, write := a, move := .left }
    else if q = 21 then
      if a = 4 then some { target := 14, write := 4, move := .right }
      else some { target := 21, write := a, move := .left }
    else if q = 22 then
      if a = 2 then some { target := 23, write := 2, move := .left }
      else some { target := 22, write := a, move := .right }
    else if q = 23 then
      some { target := 24, write := 17, move := .left }
    else if q = 24 then
      if a = 4 then some { target := 6, write := 18, move := .right }
      else some { target := 24, write := a, move := .left }
    else if q = 6 then
      if a = 0 then some { target := 6, write := 0, move := .right }
      else if a = 7 then some { target := 7, write := 0, move := .right }
      else if a = 8 then some { target := 10, write := 0, move := .right }
      else if a = 5 then some { target := 6, write := 0, move := .right }
      else if a = 17 then some { target := 8, write := 1, move := .left }
      else none
    else if q = 26 then
      if a = 0 then some { target := 26, write := 0, move := .right }
      else if a = 3 then some { target := 7, write := 0, move := .right }
      else if a = 6 then some { target := 10, write := 0, move := .right }
      else if a = 5 then some { target := 8, write := 1, move := .left }
      else none
    else if q = 7 then
      if a = 2 then some { target := 9, write := 0, move := .left }
      else some { target := 7, write := a, move := .right }
    else if q = 10 then
      if a = 2 then some { target := 9, write := 1, move := .left }
      else some { target := 10, write := a, move := .right }
    else if q = 9 then
      if a = 4 then some { target := 26, write := 4, move := .right }
      else if a = 18 then some { target := 6, write := 18, move := .right }
      else some { target := 9, write := a, move := .left }
    else if q = 8 then
      if a = 4 ∨ a = 18 then some { target := 0, write := 2, move := .right }
      else some { target := 8, write := a, move := .left }
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

def squarePayload (x : List Bool) : List Bool :=
  List.replicate (x.length * x.length) false ++ true :: x

def timeBound (n : Nat) : Nat := 1000 * (n + 1) ^ 6

@[simp] theorem squarePayload_length (x : List Bool) :
    (squarePayload x).length = x.length * x.length + x.length + 1 := by
  simp [squarePayload, Nat.mul_comm]
  omega

def tapeConfig (q : Fin 27) (z : Int) (t : Int → Fin 19) : Configuration 27 19 :=
  ⟨q, z, t⟩

theorem step_write (q q' : Fin 27) (z : Int) (t : Int → Fin 19)
    (a : Fin 19) (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some { write := a, target := q', move := d }) :
    step machine 0 (tapeConfig q z t) =
      some (tapeConfig q' (moveHead d z) (Function.update t z a)) := by
  simp only [step, tapeConfig, hr, Option.map_some, writtenTape]

theorem step_preserve (q q' : Fin 27) (z : Int) (t : Int → Fin 19)
    (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some { write := t z, target := q', move := d }) :
    step machine 0 (tapeConfig q z t) = some (tapeConfig q' (moveHead d z) t) := by
  rw [step_write q q' z t (t z) d hr, Function.update_eq_self]

theorem scan_right (q : Fin 27) (z : Int) (t : Int → Fin 19) (n : Nat)
    (hr : ∀ p : Nat, p < n → machine.rule q (t (z + p)) 0 =
      some { write := t (z + p), target := q, move := .right }) :
    run machine (ticks n) (tapeConfig q z t) = some (tapeConfig q (z + n) t) := by
  induction n generalizing z with
  | zero => simp [ticks, run, tapeConfig]
  | succ n ih =>
    change run machine (0 :: ticks n) (tapeConfig q z t) = _
    rw [run_cons, step_preserve q q z t .right (by simpa using hr 0 (by omega)),
      Option.bind_some]
    have ht := ih (z + 1) (by
      intro p hp
      simpa [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
        Int.add_left_comm] using hr (p + 1) (by omega))
    simpa [moveHead, Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
      Int.add_left_comm] using ht

theorem scan_left (q : Fin 27) (z : Int) (t : Int → Fin 19) (n : Nat)
    (hr : ∀ p : Nat, p < n → machine.rule q (t (z - p)) 0 =
      some { write := t (z - p), target := q, move := .left }) :
    run machine (ticks n) (tapeConfig q z t) = some (tapeConfig q (z - n) t) := by
  induction n generalizing z with
  | zero => simp [ticks, run, tapeConfig]
  | succ n ih =>
    change run machine (0 :: ticks n) (tapeConfig q z t) = _
    rw [run_cons, step_preserve q q z t .left (by simpa using hr 0 (by omega)),
      Option.bind_some]
    have ht := ih (z - 1) (by
      intro p hp
      simpa [Nat.cast_add, Nat.cast_one, Int.sub_sub, Int.add_comm] using
        hr (p + 1) (by omega))
    simpa [moveHead, Nat.cast_add, Nat.cast_one, Int.sub_sub, Int.add_comm] using ht

def seedTape (x : List Bool) (k : Nat) (z : Int) : Fin 19 :=
  if z = -1 then 4
  else if 0 ≤ z ∧ z < (k : Int) then unproc (bitAt x z.toNat)
  else inputTape machine x z

def seedConfig (x : List Bool) (k : Nat) : Configuration 27 19 :=
  ⟨if k = 0 then 4 else if k = 1 then 12 else 13, k, seedTape x k⟩

theorem seedTape_head (x : List Bool) (k : Nat) :
    seedTape x k (k : Int) = inputTape machine x (k : Int) := by
  have hn : (k : Int) ≠ -1 := by omega
  simp [seedTape, hn]

theorem seedTape_write (x : List Bool) (k : Nat) (hk : k < x.length) :
    Function.update (seedTape x k) (k : Int) (unproc x[k]) =
      seedTape x (k + 1) := by
  funext z
  by_cases hz : z = (k : Int)
  · subst z
    have hn : (k : Int) ≠ -1 := by omega
    have hi : 0 ≤ (k : Int) ∧ (k : Int) < ((k + 1 : Nat) : Int) := by omega
    simp [seedTape, hn, hi, bitAt_lt x k hk, Int.toNat_natCast]
  · have hc : (0 ≤ z ∧ z < ((k + 1 : Nat) : Int)) ↔
        (0 ≤ z ∧ z < (k : Int)) := by omega
    simp only [Function.update_of_ne hz, seedTape, hc]

theorem bootstrap (x : List Bool) :
    run machine (ticks 2) (initial machine x) = some (seedConfig x 0) := by
  have hn : inputTape machine x (-1) = 2 := inputTape_neg machine x _ (by omega)
  have h0 : seedTape x 0 = Function.update (inputTape machine x) (-1) 4 := by
    funext z
    by_cases hz : z = -1
    · subst z; simp [seedTape]
    · have hc : ¬ (0 ≤ z ∧ z < (0 : Nat)) := by omega
      simp [seedTape, hz, hc]
  change run machine (0 :: 0 :: []) (initial machine x) = _
  change (step machine 0 (tapeConfig 2 0 (inputTape machine x))).bind _ = _
  rw [step_preserve 2 3 0 (inputTape machine x) .left (by rfl), Option.bind_some]
  change (step machine 0 (tapeConfig 3 (-1) (inputTape machine x))).bind _ = _
  rw [step_write 3 4 (-1) (inputTape machine x) 4 .right (by rw [hn]; rfl),
    Option.bind_some]
  simp [run, tapeConfig, seedConfig, h0, moveHead]

theorem seed_mark4 (b : Bool) :
    machine.rule 4 (writeBit b) 0 =
      some { write := unproc b, target := 12, move := .right } := by
  cases b <;> simp [machine, writeBit, unproc]

theorem seed_mark12 (b : Bool) :
    machine.rule 12 (writeBit b) 0 =
      some { write := unproc b, target := 13, move := .right } := by
  cases b <;> simp [machine, writeBit, unproc]

theorem seed_mark13 (b : Bool) :
    machine.rule 13 (writeBit b) 0 =
      some { write := unproc b, target := 13, move := .right } := by
  cases b <;> simp [machine, writeBit, unproc]

theorem seed_step (x : List Bool) (k : Nat) (hk : k < x.length) :
    step machine 0 (seedConfig x k) = some (seedConfig x (k + 1)) := by
  have hread : seedTape x k (k : Int) = writeBit x[k] := by
    rw [seedTape_head, inputTape_ofNat machine x k hk]
    cases x[k] <;> rfl
  cases k with
  | zero =>
      change step machine 0 (tapeConfig 4 0 (seedTape x 0)) = _
      rw [step_write 4 12 0 (seedTape x 0) (unproc x[0]) .right
        (by convert seed_mark4 x[0]; exact hread)]
      simpa [seedConfig, tapeConfig, moveHead] using seedTape_write x 0 hk
  | succ k =>
      cases k with
      | zero =>
          change step machine 0 (tapeConfig 12 1 (seedTape x 1)) = _
          rw [step_write 12 13 1 (seedTape x 1) (unproc x[1]) .right
            (by convert seed_mark12 x[1]; exact hread)]
          simpa [seedConfig, tapeConfig, moveHead] using seedTape_write x 1 hk
      | succ k =>
          change step machine 0
            (tapeConfig 13 (k + 2) (seedTape x (k + 2))) = _
          rw [step_write 13 13 (k + 2) (seedTape x (k + 2)) (unproc x[k + 2])
            .right (by convert seed_mark13 x[k + 2]; exact hread)]
          apply congrArg some
          simp [seedConfig, tapeConfig, moveHead]
          constructor
          · omega
          · exact seedTape_write x (k + 2) hk

theorem seed_scan (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks k) (seedConfig x 0) = some (seedConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add k 1, run_append, ih (by omega), Option.bind_some, run_ticks_one]
    exact seed_step x k (by omega)

def epochTape (x : List Bool) (z : Int) : Fin 19 :=
  if z = -1 then 4
  else if 0 ≤ z ∧ z < (x.length : Int) then unproc (bitAt x z.toNat)
  else if z = (x.length : Int) then 5
  else inputTape machine x z

def afterSepState (n : Nat) : Fin 27 := if n ≤ 1 then 25 else 5
def afterCopySelect (n : Nat) : Fin 27 := if n ≤ 1 then 26 else 14

def epochConfig (x : List Bool) : Configuration 27 19 :=
  ⟨afterCopySelect x.length, 0, epochTape x⟩

theorem epochTape_neg1 (x : List Bool) : epochTape x (-1) = 4 := by
  simp [epochTape]

theorem epochTape_nat_ne_left (x : List Bool) (p : Nat) :
    epochTape x (p : Int) ≠ 4 := by
  have hp : (p : Int) ≠ -1 := by omega
  simp only [epochTape, hp, if_false]
  split_ifs
  · cases bitAt x _ <;> decide
  · decide
  · simp [inputTape]
    split_ifs <;> decide

theorem seed_separator (x : List Bool) :
    Function.update (seedTape x x.length) (x.length : Int) 5 = epochTape x := by
  funext z
  by_cases hz : z = (x.length : Int)
  · subst z
    have hn : (x.length : Int) ≠ -1 := by omega
    have hc : ¬ (0 ≤ (x.length : Int) ∧ (x.length : Int) < (x.length : Int)) :=
      by omega
    simp [Function.update, seedTape, epochTape, hn, hc]
  · rw [Function.update_of_ne hz]
    unfold seedTape epochTape
    by_cases hl : z = -1
    · simp [hl]
    · by_cases hrange : 0 ≤ z ∧ z < (x.length : Int)
      · simp [hl, hrange]
      · simp [hl, hrange, hz]

theorem seed_turn (x : List Bool) :
    step machine 0 (seedConfig x x.length) =
      some (tapeConfig (afterSepState x.length)
        ((x.length : Int) - 1) (epochTape x)) := by
  have hread : seedTape x x.length (x.length : Int) = 2 := by
    rw [seedTape_head]; exact inputTape_ge machine x _ (by rfl)
  have hsep := seed_separator x
  have hst : seedConfig x x.length =
      tapeConfig (if x.length = 0 then 4 else if x.length = 1 then 12 else 13)
        x.length (seedTape x x.length) := by
    simp [seedConfig, tapeConfig]
  rw [hst]
  by_cases h0 : x.length = 0
  · rw [h0] at hread hsep ⊢
    change step machine 0 (tapeConfig 4 0 (seedTape x 0)) = _
    rw [step_write 4 25 0 (seedTape x 0) 5 .left (by
      have : seedTape x 0 0 = 2 := by
        have hz : (0 : Int) = ↑(0 : Nat) := Nat.cast_zero.symm
        rw [hz]; exact hread
      rw [this]; rfl)]
    simpa [tapeConfig, moveHead, afterSepState] using hsep
  · by_cases h1 : x.length = 1
    · rw [h1] at hread hsep ⊢
      change step machine 0 (tapeConfig 12 1 (seedTape x 1)) = _
      rw [step_write 12 25 1 (seedTape x 1) 5 .left (by
        have : seedTape x 1 1 = 2 := by
          have hz : (1 : Int) = ↑(1 : Nat) := Nat.cast_one.symm
          rw [hz]; exact hread
        rw [this]; rfl)]
      simpa [tapeConfig, moveHead, afterSepState] using hsep
    · have hq : (if x.length = 0 then (4 : Fin 27) else if x.length = 1 then 12 else 13) = 13 := by
        simp [h0, h1]
      have hs : afterSepState x.length = 5 := by
        have : ¬ x.length ≤ 1 := by omega
        simp [afterSepState, this]
      rw [hq, hs, step_write 13 5 x.length (seedTape x x.length) 5 .left
        (by rw [hread]; rfl), hsep]
      rfl

theorem seed_return (x : List Bool) :
    run machine (ticks x.length)
      (tapeConfig (afterSepState x.length)
        ((x.length : Int) - 1) (epochTape x)) =
      some (tapeConfig (afterSepState x.length) (-1) (epochTape x)) := by
  have h := scan_left (afterSepState x.length) ((x.length : Int) - 1)
    (epochTape x) x.length (by
      intro p hp
      have he : (x.length : Int) - 1 - p =
          ((x.length - 1 - p : Nat) : Int) := by omega
      rw [he]
      have hne := epochTape_nat_ne_left x (x.length - 1 - p)
      unfold afterSepState
      split_ifs <;> simp [machine, hne])
  convert h using 1 <;> congr 2 <;> omega

theorem seed_finish (x : List Bool) :
    step machine 0
      (tapeConfig (afterSepState x.length) (-1) (epochTape x)) =
      some (epochConfig x) := by
  by_cases hle : x.length ≤ 1
  · have hs : afterSepState x.length = 25 := by simp [afterSepState, hle]
    have hc : afterCopySelect x.length = 26 := by simp [afterCopySelect, hle]
    rw [hs, step_preserve 25 26 (-1) (epochTape x) .right
      (by rw [epochTape_neg1]; rfl)]
    simp [epochConfig, tapeConfig, hc, moveHead]
  · have hs : afterSepState x.length = 5 := by simp [afterSepState, hle]
    have hc : afterCopySelect x.length = 14 := by simp [afterCopySelect, hle]
    rw [hs, step_preserve 5 14 (-1) (epochTape x) .right
      (by rw [epochTape_neg1]; rfl)]
    simp [epochConfig, tapeConfig, hc, moveHead]

def setupFuel (n : Nat) : Nat := 2 * n + 4

theorem setup_run (x : List Bool) :
    run machine (ticks (setupFuel x.length)) (initial machine x) =
      some (epochConfig x) := by
  have ht : setupFuel x.length = 2 + x.length + 1 + x.length + 1 := by
    unfold setupFuel; omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, bootstrap, Option.bind_some,
    seed_scan x x.length (by rfl), Option.bind_some, run_ticks_one,
    seed_turn, Option.bind_some, seed_return, Option.bind_some, run_ticks_one]
  exact seed_finish x

def finalConfig (x : List Bool) : Configuration 27 19 :=
  ⟨0, 0, inputTape machine (squarePayload x)⟩

theorem squarePayload_get (x : List Bool) (p : Nat)
    (hp : p < (squarePayload x).length) :
    (squarePayload x)[p] =
      if p < x.length * x.length then false
      else if p = x.length * x.length then true
      else bitAt x (p - x.length * x.length - 1) := by
  have hp' : p < (List.replicate (x.length * x.length) false ++ true :: x).length := by
    simpa [squarePayload] using hp
  simp only [squarePayload]
  by_cases hl : p < x.length * x.length
  · simp [List.getElem_append_left, hl]
  · have hle : x.length * x.length ≤ p := Nat.not_lt.mp hl
    rw [List.getElem_append_right (by simpa using hle)]
    by_cases he : p = x.length * x.length
    · subst p; simp
    · have hn : p - x.length * x.length ≠ 0 := by omega
      have hidx : p - x.length * x.length - 1 < x.length := by
        simp at hp'; omega
      simp [List.getElem_cons, hn, hl, he, bitAt, hidx]

theorem run_empty :
    run machine (ticks 6) (initial machine []) = some (finalConfig []) := by
  have hsetup : run machine (ticks 4) (initial machine []) =
      some (epochConfig []) := by
    simpa [setupFuel] using setup_run []
  have ht : 6 = 4 + 1 + 1 := by omega
  have hsep : epochTape [] 0 = 5 := by simp [epochTape]
  have hleft : epochTape [] (-1) = 4 := epochTape_neg1 []
  have hout : Function.update (Function.update (epochTape []) 0 1) (-1) 2 =
      inputTape machine (squarePayload []) := by
    funext z
    by_cases hl : z = -1
    · subst z; simp [inputTape]
    · rw [Function.update_of_ne hl]
      by_cases hz0 : z = (0 : Int)
      · subst z; simp [inputTape, squarePayload]
      · rw [Function.update_of_ne hz0]
        have hc : ¬ (0 ≤ z ∧ z < (0 : Int)) := by omega
        unfold epochTape
        simp [hl, hc, hz0]
        by_cases hn : z < 0
        · rw [inputTape_neg machine [] z hn,
            inputTape_neg machine (squarePayload []) z hn]
        · have hzpos : (0 : Int) ≤ z := by omega
          have hypos : ((squarePayload []).length : Int) ≤ z := by
            simp [squarePayload]; omega
          rw [inputTape_ge machine [] z hzpos,
            inputTape_ge machine (squarePayload []) z hypos]
  have hcfg : epochConfig [] = tapeConfig 26 0 (epochTape []) := by
    simp [epochConfig, tapeConfig, afterCopySelect]
  have hcell : Function.update (epochTape []) 0 1 (moveHead .left 0) = 4 := by
    have : moveHead OneTapeTableau.Move.left 0 = (-1 : Int) := rfl
    rw [this, Function.update_of_ne (by omega), hleft]
  rw [ht, ticks_add, ticks_add, run_append, run_append, hsetup, Option.bind_some,
    run_ticks_one, hcfg]
  rw [step_write 26 8 0 (epochTape []) 1 .left (by rw [hsep]; rfl),
    Option.bind_some, run_ticks_one]
  rw [step_write 8 0 (moveHead .left 0) (Function.update (epochTape []) 0 1) 2 .right
    (by rw [hcell]; rfl)]
  simp [finalConfig, tapeConfig, moveHead, hout]

theorem epochTape_src (x : List Bool) (p : Nat) (hp : p < x.length) :
    epochTape x p = unproc x[p] := by
  have hn : (p : Int) ≠ -1 := by omega
  have hr : 0 ≤ (p : Int) ∧ (p : Int) < (x.length : Int) := by omega
  simp [epochTape, hn, hr, bitAt_lt x p hp, Int.toNat_natCast]

theorem epochTape_sep (x : List Bool) : epochTape x (x.length : Int) = 5 := by
  have hn : (x.length : Int) ≠ -1 := by omega
  have hr : ¬ (0 ≤ (x.length : Int) ∧ (x.length : Int) < (x.length : Int)) :=
    by omega
  simp [epochTape, hn, hr]

theorem epochTape_blank (x : List Bool) (p : Nat) (hp : x.length < p) :
    epochTape x (p : Int) = 2 := by
  have hn : (p : Int) ≠ -1 := by omega
  have hr : ¬ (0 ≤ (p : Int) ∧ (p : Int) < (x.length : Int)) := by omega
  have hs : (p : Int) ≠ (x.length : Int) := by omega
  have hge := inputTape_ge machine x (p : Int) (by omega)
  simp only [epochTape, hn, if_false, hr, hs, hge, machine_blank]

theorem rule_small_unproc (b : Bool) :
    machine.rule 26 (unproc b) 0 =
      some { write := 0, target := seekBit b, move := .right } := by
  cases b <;> simp [machine, unproc, seekBit]

theorem rule_seek_blank (b : Bool) :
    machine.rule (seekBit b) 2 0 =
      some { write := writeBit b, target := 9, move := .left } := by
  cases b <;> simp [machine, seekBit, writeBit]

theorem rule_seek_keep (b : Bool) (a : Fin 19) (ha : a ≠ 2) :
    machine.rule (seekBit b) a 0 =
      some { write := a, target := seekBit b, move := .right } := by
  cases b <;> simp [machine, seekBit, ha]

theorem clean_output_singleton (b : Bool) :
    Function.update
      (Function.update
        (Function.update
          (Function.update (epochTape [b]) 0 0) 2 (writeBit b)) 1 1) (-1) 2 =
      inputTape machine (squarePayload [b]) := by
  funext z
  have hy : squarePayload [b] = [false, true, b] := by simp [squarePayload]
  by_cases hl : z = -1
  · subst z; simp [inputTape]
  · rw [Function.update_of_ne hl]
    by_cases hz1 : z = (1 : Int)
    · subst z
      simp [Function.update, inputTape, hy]
    · rw [Function.update_of_ne (by
        intro h; apply hz1; exact h.trans (by rfl))]
      by_cases hz2 : z = (2 : Int)
      · subst z
        simp [Function.update, inputTape, hy]
        cases b <;> simp [writeBit]
      · rw [Function.update_of_ne (by intro h; exact hz2 h)]
        by_cases hz0 : z = (0 : Int)
        · subst z
          simp [Function.update, inputTape, hy]
        · rw [Function.update_of_ne hz0]
          have hc : ¬ (0 ≤ z ∧ z < (1 : Int)) := by omega
          have hne1 : z ≠ (1 : Int) := hz1
          unfold epochTape
          simp [hl, hc, hne1]
          by_cases hn : z < 0
          · rw [inputTape_neg machine [b] z hn,
              inputTape_neg machine (squarePayload [b]) z hn]
          · have hge : ((squarePayload [b]).length : Int) ≤ z := by
              simp [hy]; omega
            have hge1 : (([b].length : Int) ≤ z) := by simp; omega
            rw [inputTape_ge machine [b] z hge1,
              inputTape_ge machine (squarePayload [b]) z hge]

theorem run_singleton (b : Bool) :
    run machine (ticks 16) (initial machine [b]) = some (finalConfig [b]) := by
  have hsetup : run machine (ticks 6) (initial machine [b]) =
      some (epochConfig [b]) := by
    simpa [setupFuel] using setup_run [b]
  have hcfg : epochConfig [b] = tapeConfig 26 0 (epochTape [b]) := by
    simp [epochConfig, tapeConfig, afterCopySelect]
  have ht : 16 = 6 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
  have hx0 : epochTape [b] 0 = unproc b := by
    simpa using epochTape_src [b] 0 Nat.zero_lt_one
  have hx1 : epochTape [b] 1 = 5 := by simpa using epochTape_sep [b]
  have hx2 : epochTape [b] 2 = 2 := by
    simpa using epochTape_blank [b] 2 Nat.one_lt_two
  have hm : epochTape [b] (-1) = 4 := epochTape_neg1 [b]
  set t1 : Int → Fin 19 := Function.update (epochTape [b]) 0 0
  set t2 : Int → Fin 19 := Function.update t1 2 (writeBit b)
  set t3 : Int → Fin 19 := Function.update t2 1 1
  have ht1_1 : t1 1 = 5 := by simp [t1, Function.update, hx1]
  have ht1_2 : t1 2 = 2 := by simp [t1, Function.update, hx2]
  have ht2_1 : t2 1 = 5 := by simp [t2, Function.update, ht1_1]
  have ht2_0 : t2 0 = 0 := by simp [t2, t1, Function.update]
  have ht2_m : t2 (-1) = 4 := by simp [t2, t1, Function.update, hm]
  have ht3_0 : t3 0 = 0 := by simp [t3, Function.update, ht2_0]
  have ht3_m : t3 (-1) = 4 := by simp [t3, Function.update, ht2_m]
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add,
    ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, run_append, run_append, run_append, run_append,
    run_append, run_append, hsetup, Option.bind_some, run_ticks_one, hcfg]
  rw [step_write 26 (seekBit b) 0 (epochTape [b]) 0 .right
    (by rw [hx0]; exact rule_small_unproc b)]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve (seekBit b) (seekBit b) 1 t1 .right
    (by rw [ht1_1]; exact rule_seek_keep b 5 (by decide))]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_write (seekBit b) 9 2 t1 (writeBit b) .left
    (by rw [ht1_2]; exact rule_seek_blank b)]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve 9 9 1 t2 .left (by rw [ht2_1]; simp [machine])]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve 9 9 0 t2 .left (by rw [ht2_0]; simp [machine])]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve 9 26 (-1) t2 .right (by rw [ht2_m]; simp [machine])]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve 26 26 0 t2 .right (by rw [ht2_0]; simp [machine])]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_write 26 8 1 t2 1 .left (by rw [ht2_1]; rfl)]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_preserve 8 8 0 t3 .left (by rw [ht3_0]; simp [machine])]
  simp [moveHead, Option.bind_some, run_ticks_one]
  rw [step_write 8 0 (-1) t3 2 .right (by rw [ht3_m]; simp [machine])]
  simp [finalConfig, tapeConfig, moveHead, t1, t2, t3, clean_output_singleton b]

def srcMark (x : List Bool) (o i : Nat) : Fin 19 :=
  if i < o then proc (bitAt x i)
  else if i = o then active (bitAt x i)
  else unproc (bitAt x i)

def cursorBit (x : List Bool) (o i : Nat) : Fin 19 :=
  if i < o then (if bitAt x i then (14 : Fin 19) else 13)
  else if i = o then (if bitAt x i then 16 else 15)
  else (if bitAt x i then 12 else 11)

def squareTape (x : List Bool) (o : Nat) (z : Int) : Fin 19 :=
  if z = -1 then 4
  else if z < 0 then 2
  else if z.toNat < x.length then
    if z.toNat < o then proc (bitAt x z.toNat) else unproc (bitAt x z.toNat)
  else if z.toNat = x.length then 5
  else if z.toNat < x.length + o * (x.length - 1) + 1 then 0
  else 2

def outerTape (x : List Bool) (o p : Nat) (z : Int) : Fin 19 :=
  if z = -1 then 4
  else if z < 0 then 2
  else if z.toNat < x.length then srcMark x o z.toNat
  else if z.toNat = x.length then 5
  else if z.toNat < x.length + o * (x.length - 1) + p + 1 then 0
  else 2

def largeTape (x : List Bool) (z : Int) : Fin 19 :=
  if z = -1 then 18
  else if z < 0 then 2
  else if z.toNat < x.length then proc (bitAt x z.toNat)
  else if z.toNat = x.length then 5
  else if z.toNat < x.length * x.length then 0
  else if z.toNat = x.length * x.length then 17
  else 2

def copyTape (x : List Bool) (k : Nat) (z : Int) : Fin 19 :=
  if z = -1 then 18
  else if z < 0 then 2
  else if z.toNat < k then 0
  else if z.toNat < x.length then proc (bitAt x z.toNat)
  else if z.toNat = x.length then 5
  else if z.toNat < x.length * x.length then 0
  else if z.toNat = x.length * x.length then 17
  else if z.toNat < x.length * x.length + k + 1 then
    writeBit (bitAt x (z.toNat - x.length * x.length - 1))
  else 2

def squareConfig (x : List Bool) (o : Nat) : Configuration 27 19 :=
  ⟨14, 0, squareTape x o⟩

def seekDist (n o : Nat) : Nat := (n - 1) * (o + 1)
def innerFuel (n o : Nat) : Nat := 2 * seekDist n o + 3

theorem nat_pred_cast (n : Nat) (h : 1 ≤ n) :
    ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega

theorem natCast_ne_neg_one (n : Nat) : (n : Int) ≠ (-1 : Int) := by
  have : (0 : Int) ≤ n := Nat.cast_nonneg n
  omega

theorem seekDist_int (n o : Nat) (hn : 1 ≤ n) :
    (seekDist n o : Int) = ((n : Int) - 1) * (↑o + 1) := by
  unfold seekDist
  rw [Nat.cast_mul, nat_pred_cast n hn, Nat.cast_add, Nat.cast_one]
def innerLoopFuel (n o : Nat) : Nat := (n - 1) * innerFuel n o
def outerFuel (n o : Nat) : Nat := 2 * o + n + 5 + innerLoopFuel n o
def finishFuel (n : Nat) : Nat := 2 * n * n + 4
def copyCycleFuel (n k : Nat) : Nat := 2 * n * n + 2 * k + 4
def copyAllFuel (n : Nat) : Nat := 2 * n * n * n + n * n + 3 * n
def sepFuel (n : Nat) : Nat := 2 * n * n + 2

theorem srcMark_cursor (x : List Bool) (o i : Nat) :
    cursorOf (srcMark x o i) = some (cursorBit x o i) := by
  by_cases hlt : i < o
  · simp [srcMark, cursorBit, hlt, cursorOf_proc]
  · by_cases heq : i = o
    · simp [srcMark, cursorBit, hlt, heq, cursorOf_active]
    · simp [srcMark, cursorBit, hlt, heq, cursorOf_unproc]

theorem srcMark_base (x : List Bool) (o i : Nat) :
    baseOf (cursorBit x o i) = some (srcMark x o i) :=
  baseOf_cursorOf _ _ (srcMark_cursor x o i)

theorem squareTape_neg1 (x : List Bool) (o : Nat) : squareTape x o (-1) = 4 := by
  simp [squareTape]

theorem squareTape_src (x : List Bool) (o i : Nat) (hi : i < x.length) :
    squareTape x o i = if i < o then proc (bitAt x i) else unproc (bitAt x i) := by
  have hn : (i : Int) ≠ -1 := by omega
  simp [squareTape, hn, Int.toNat_natCast, hi]

theorem squareTape_sep (x : List Bool) (o : Nat) :
    squareTape x o (x.length : Int) = 5 := by
  have hn : (x.length : Int) ≠ -1 := by omega
  have hneg : ¬ (x.length : Int) < 0 := by omega
  simp [squareTape, hn, hneg, Int.toNat_natCast]

theorem squareTape_nat_ne_left (x : List Bool) (o p : Nat) :
    squareTape x o (p : Int) ≠ 4 := by
  have hp : (p : Int) ≠ -1 := by omega
  simp only [squareTape, hp, if_false, Int.not_lt.mpr (Nat.cast_nonneg p),
    Int.toNat_natCast]
  split_ifs <;> first | decide | (cases bitAt x _ <;> decide)

theorem squareTape_ofNat (x : List Bool) (p : Nat) :
    squareTape x 0 (p : Int) =
      if p < x.length then unproc (bitAt x p)
      else if p = x.length then 5 else 2 := by
  have hn : (p : Int) ≠ -1 := by omega
  have hneg : ¬ (p : Int) < 0 := by omega
  simp only [squareTape, hn, if_false, hneg, Int.toNat_natCast]
  split_ifs <;> first | rfl | omega

theorem epochTape_ofNat (x : List Bool) (p : Nat) :
    epochTape x (p : Int) =
      if p < x.length then unproc (bitAt x p)
      else if p = x.length then 5 else 2 := by
  have hn : (p : Int) ≠ -1 := by omega
  have hneg : ¬ (p : Int) < 0 := by omega
  have hr : (0 ≤ (p : Int) ∧ (p : Int) < (x.length : Int)) ↔ p < x.length := by
    omega
  by_cases hp : p < x.length
  · simp [epochTape, hn, hr, hp]
  · by_cases he : p = x.length
    · simp [epochTape, hn, hr, hp, he]
    · have hge := inputTape_ge machine x (p : Int) (by omega)
      simp [epochTape, hn, hr, hp, he, hge, machine_blank]

theorem square_eq_epoch (x : List Bool) : squareTape x 0 = epochTape x := by
  funext z
  by_cases hl : z = -1
  · subst z; simp [squareTape, epochTape]
  · by_cases hn : z < 0
    · have hc : ¬ (0 ≤ z ∧ z < (x.length : Int)) := by omega
      have hne : z ≠ (x.length : Int) := by omega
      simp [squareTape, epochTape, hl, hn, hc, hne, inputTape_neg machine x z hn]
    · have hz : z = (z.toNat : Int) := (Int.toNat_of_nonneg (by omega)).symm
      rw [hz, squareTape_ofNat, epochTape_ofNat]

theorem setup_ge2 (x : List Bool) (hn : 2 ≤ x.length) :
    run machine (ticks (setupFuel x.length)) (initial machine x) =
      some (squareConfig x 0) := by
  have hs : afterCopySelect x.length = 14 := by
    simp [afterCopySelect]; omega
  have h := setup_run x
  simpa [epochConfig, squareConfig, hs, square_eq_epoch] using h

theorem outerTape_src (x : List Bool) (o p i : Nat) (hi : i < x.length) :
    outerTape x o p (i : Int) = srcMark x o i := by
  have hn : (i : Int) ≠ -1 := by omega
  have hneg : ¬ (i : Int) < 0 := by omega
  simp [outerTape, hn, hneg, Int.toNat_natCast, hi]

theorem outerTape_sep (x : List Bool) (o p : Nat) :
    outerTape x o p (x.length : Int) = 5 := by
  have hn : (x.length : Int) ≠ -1 := by omega
  have hneg : ¬ (x.length : Int) < 0 := by omega
  simp [outerTape, hn, hneg, Int.toNat_natCast]

theorem outerTape_neg1 (x : List Bool) (o p : Nat) : outerTape x o p (-1) = 4 := by
  simp [outerTape]

theorem outerTape_nat_ne_left (x : List Bool) (o p j : Nat) :
    outerTape x o p (j : Int) ≠ 4 := by
  have hj : (j : Int) ≠ -1 := by omega
  simp only [outerTape, hj, if_false, Int.not_lt.mpr (Nat.cast_nonneg j),
    Int.toNat_natCast]
  split_ifs <;> first | decide | (cases bitAt x _ <;> decide) |
    (unfold srcMark; split_ifs <;> first | decide | cases bitAt x _ <;> decide)

theorem srcMark_ne_five (x : List Bool) (o i : Nat) : srcMark x o i ≠ 5 := by
  unfold srcMark
  split_ifs <;> first | decide | (cases bitAt x i <;> decide)

theorem srcMark_ne_two (x : List Bool) (o i : Nat) : srcMark x o i ≠ 2 := by
  unfold srcMark
  split_ifs <;> first | decide | (cases bitAt x i <;> decide)

theorem cursorBit_ne_two (x : List Bool) (o i : Nat) : cursorBit x o i ≠ 2 := by
  unfold cursorBit
  split_ifs <;> decide

theorem baseOf_plain (a : Fin 19) (h : a = 0 ∨ a = 5 ∨ a = 3 ∨ a = 6 ∨
    a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10) : baseOf a = none := by
  rcases h with h | h | h | h | h | h | h | h <;> simp [baseOf, h]

theorem outerTape_nonblank (x : List Bool) (o p j : Nat)
    (hj : j < x.length + o * (x.length - 1) + p + 1) :
    outerTape x o p (j : Int) ≠ 2 := by
  have hn : (j : Int) ≠ -1 := by omega
  have hneg : ¬ (j : Int) < 0 := by omega
  simp only [outerTape, hn, if_false, hneg, Int.toNat_natCast]
  split_ifs <;> first | exact srcMark_ne_two x o j | decide | omega

theorem outerTape_blankAt (x : List Bool) (o p : Nat) :
    outerTape x o p
      ((x.length + o * (x.length - 1) + p + 1 : Nat) : Int) = 2 := by
  set j := x.length + o * (x.length - 1) + p + 1
  have hn : (j : Int) ≠ -1 := by omega
  have hneg : ¬ (j : Int) < 0 := by omega
  have hlt : ¬ j < x.length := by omega
  have he : ¬ j = x.length := by omega
  have hz : ¬ j < j := by omega
  have hlast : x.length + o * (x.length - 1) + p < j := by omega
  simp [outerTape, hn, hneg, Int.toNat_natCast, hlt, he, hz, hlast]

theorem rule_inner_mark (x : List Bool) (o i : Nat) :
    machine.rule 17 (srcMark x o i) 0 =
      some { write := cursorBit x o i, target := 18, move := .right } := by
  simp [machine, srcMark_ne_five x o i, srcMark_cursor x o i]

theorem rule_seek0_keep (a : Fin 19) (ha : a ≠ 2) :
    machine.rule 18 a 0 = some { write := a, target := 18, move := .right } := by
  simp [machine, ha]

theorem rule_ret_keep (a : Fin 19) (h : baseOf a = none) :
    machine.rule 19 a 0 = some { write := a, target := 19, move := .left } := by
  simp [machine, h]

theorem activate_tape (x : List Bool) (o : Nat) (ho : o < x.length) :
    Function.update (squareTape x o) (o : Int) (active (bitAt x o)) =
      outerTape x o 0 := by
  funext z
  by_cases hz : z = (o : Int)
  · subst z
    have hn : (o : Int) ≠ -1 := by omega
    have hneg : ¬ (o : Int) < 0 := by omega
    simp [outerTape, squareTape, hn, hneg, Int.toNat_natCast, ho, srcMark]
  · rw [Function.update_of_ne hz]
    unfold squareTape outerTape srcMark
    by_cases hl : z = -1
    · simp [hl]
    · by_cases hn : z < 0
      · simp [hl, hn]
      · have : z.toNat = o ↔ z = (o : Int) := by omega
        simp [hl, hn, this, hz]

theorem deactivate_tape (x : List Bool) (o : Nat) (ho : o < x.length)
    (hn2 : 2 ≤ x.length) :
    Function.update (outerTape x o (x.length - 1)) (o : Int) (proc (bitAt x o)) =
      squareTape x (o + 1) := by
  funext z
  by_cases hz : z = (o : Int)
  · subst z
    have hn : (o : Int) ≠ -1 := by omega
    have hneg : ¬ (o : Int) < 0 := by omega
    have hlt : o < o + 1 := by omega
    simp [outerTape, squareTape, srcMark, hn, hneg, Int.toNat_natCast, ho, hlt]
  · rw [Function.update_of_ne hz]
    by_cases hl : z = -1
    · simp [squareTape, outerTape, hl]
    · by_cases hn : z < 0
      · simp [squareTape, outerTape, hl, hn]
      · have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg (by omega)).symm
        rw [hz']
        have hne : z.toNat ≠ o := by omega
        have hmul : o * (x.length - 1) + (x.length - 1) =
            (o + 1) * (x.length - 1) := by ring
        have hbound : x.length + o * (x.length - 1) + (x.length - 1) + 1 =
            x.length + (o + 1) * (x.length - 1) + 1 := by
          calc x.length + o * (x.length - 1) + (x.length - 1) + 1
              = x.length + (o * (x.length - 1) + (x.length - 1)) + 1 := by
                simp [Nat.add_assoc]
            _ = x.length + (o + 1) * (x.length - 1) + 1 := by rw [hmul]
        simp only [squareTape, outerTape, srcMark, Int.toNat_natCast]
        split_ifs <;> first | rfl | omega | (simp [hne, hmul, hbound] at *; omega)

def cursorTape (x : List Bool) (o p i : Nat) : Int → Fin 19 :=
  Function.update (outerTape x o p) (i : Int) (cursorBit x o i)

theorem cursorTape_at (x : List Bool) (o p i : Nat) :
    cursorTape x o p i (i : Int) = cursorBit x o i := by
  simp [cursorTape]

theorem cursorTape_ne (x : List Bool) (o p i : Nat) (z : Int) (h : z ≠ (i : Int)) :
    cursorTape x o p i z = outerTape x o p z := by
  simp [cursorTape, Function.update_of_ne h]

theorem inner_mark_step (x : List Bool) (o p i : Nat) (hi : i < x.length) :
    step machine 0 (tapeConfig 17 i (outerTape x o p)) =
      some (tapeConfig 18 ((i : Int) + 1) (cursorTape x o p i)) := by
  rw [step_write 17 18 i (outerTape x o p) (cursorBit x o i) .right
    (by rw [outerTape_src x o p i hi]; exact rule_inner_mark x o i)]
  simp [tapeConfig, moveHead, cursorTape]

theorem baseOf_srcMark (x : List Bool) (o i : Nat) :
    baseOf (srcMark x o i) = none := by
  unfold srcMark proc active unproc
  split_ifs <;> cases bitAt x i <;> simp [baseOf]

theorem baseOf_outer (x : List Bool) (o p j : Nat) :
    baseOf (outerTape x o p (j : Int)) = none := by
  have hn : (j : Int) ≠ -1 := by omega
  have hneg : ¬ (j : Int) < 0 := by omega
  simp only [outerTape, hn, if_false, hneg, Int.toNat_natCast]
  split_ifs
  · exact baseOf_srcMark x o j
  · simp [baseOf]
  · simp [baseOf]
  · simp [baseOf]

theorem append_zero (x : List Bool) (o p : Nat) :
    Function.update (outerTape x o p)
      ((x.length + o * (x.length - 1) + p + 1 : Nat) : Int) 0 =
      outerTape x o (p + 1) := by
  funext z
  set j := x.length + o * (x.length - 1) + p + 1
  by_cases hz : z = (j : Int)
  · subst z
    have hn : (j : Int) ≠ -1 := by omega
    have hneg : ¬ (j : Int) < 0 := by omega
    have hlt : ¬ j < x.length := by omega
    have he : ¬ j = x.length := by omega
    have hj : j < x.length + o * (x.length - 1) + (p + 1) + 1 := by omega
    simp [Function.update, outerTape, hn, hneg, Int.toNat_natCast, hlt, he, hj]
  · rw [Function.update_of_ne hz]
    unfold outerTape
    by_cases hl : z = -1
    · simp [hl]
    · by_cases hn : z < 0
      · simp [hl, hn]
      · have hnn : 0 ≤ z := by omega
        have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg hnn).symm
        have hne : z.toNat ≠ j := by omega
        have hb : z.toNat < x.length + o * (x.length - 1) + p + 1 ↔
            z.toNat < x.length + o * (x.length - 1) + (p + 1) + 1 := by omega
        simp [hl, hn, Int.toNat_natCast, hb]

theorem seekDist_eq (n o i : Nat) (hn : 2 ≤ n) (hi : 0 < i) :
    i + 1 + seekDist n o = n + o * (n - 1) + (i - 1) + 1 := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn
  zify
  simp only [seekDist, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [nat_pred_cast n hn1, nat_pred_cast i hi]
  ring

theorem seekDist_lt (n o i p : Nat) (hn : 2 ≤ n) (hi : 0 < i)
    (hp : p < seekDist n o) :
    i + 1 + p < n + o * (n - 1) + (i - 1) + 1 :=
  lt_of_lt_of_eq (Nat.add_lt_add_left hp (i + 1)) (seekDist_eq n o i hn hi)

theorem seekDist_pos (n o : Nat) (hn : 2 ≤ n) : 0 < seekDist n o :=
  Nat.mul_pos (Nat.sub_pos_of_lt (Nat.succ_le_iff.mp hn)) (Nat.succ_pos o)

theorem inner_seek (x : List Bool) (o i : Nat)
    (hn2 : 2 ≤ x.length) (hi : 0 < i) (hin : i < x.length) :
    run machine (ticks (seekDist x.length o))
      (tapeConfig 18 ((i : Int) + 1) (cursorTape x o (i - 1) i)) =
      some (tapeConfig 18 ((i : Int) + 1 + seekDist x.length o)
        (cursorTape x o (i - 1) i)) :=
  scan_right 18 ((i : Int) + 1) (cursorTape x o (i - 1) i)
    (seekDist x.length o) (by
      intro p hp
      have he : (i : Int) + 1 + p = ((i + 1 + p : Nat) : Int) := by omega
      have hne : ((i + 1 + p : Nat) : Int) ≠ (i : Int) := by omega
      rw [he, cursorTape_ne _ _ _ _ _ hne]
      exact rule_seek0_keep _
        (outerTape_nonblank x o (i - 1) (i + 1 + p)
          (seekDist_lt x.length o i p hn2 hi hp)))

theorem cursor_write_tape (x : List Bool) (o i : Nat)
    (hn2 : 2 ≤ x.length) (hi : 0 < i) (_hin : i < x.length) :
    Function.update (cursorTape x o (i - 1) i)
        ((i + 1 + seekDist x.length o : Nat) : Int) 0 =
      cursorTape x o i i := by
  have hj := seekDist_eq x.length o i hn2 hi
  have hne : ((i + 1 + seekDist x.length o : Nat) : Int) ≠ (i : Int) := by
    omega
  simp only [cursorTape]
  rw [Function.update_comm (Ne.symm hne), hj, append_zero x o (i - 1),
    Nat.sub_add_cancel hi]

theorem inner_write (x : List Bool) (o i : Nat)
    (hn2 : 2 ≤ x.length) (hi : 0 < i) (hin : i < x.length) :
    step machine 0 (tapeConfig 18 ((i : Int) + 1 + seekDist x.length o)
        (cursorTape x o (i - 1) i)) =
      some (tapeConfig 19 ((i : Int) + seekDist x.length o)
        (cursorTape x o i i)) := by
  have hI : (i : Int) + 1 + seekDist x.length o =
      ((i + 1 + seekDist x.length o : Nat) : Int) := by omega
  have hj := seekDist_eq x.length o i hn2 hi
  have hne : ((i + 1 + seekDist x.length o : Nat) : Int) ≠ (i : Int) := by
    omega
  have hblank : cursorTape x o (i - 1) i
      ((i + 1 + seekDist x.length o : Nat) : Int) = 2 := by
    rw [cursorTape_ne _ _ _ _ _ hne, hj]
    exact outerTape_blankAt x o (i - 1)
  have hhead : moveHead .left ((i + 1 + seekDist x.length o : Nat) : Int) =
      (i : Int) + seekDist x.length o := by
    simp [moveHead]; omega
  have htape := cursor_write_tape x o i hn2 hi hin
  have hstep :=
    step_write 18 19 ((i + 1 + seekDist x.length o : Nat) : Int)
      (cursorTape x o (i - 1) i) 0 .left (by rw [hblank]; rfl)
  rw [hI, hstep]
  exact congrArg some (by rw [hhead, htape])

theorem inner_return (x : List Bool) (o i : Nat)
    (hn2 : 2 ≤ x.length) (hi : 0 < i) (hin : i < x.length) :
    run machine (ticks (seekDist x.length o))
      (tapeConfig 19 ((i : Int) + seekDist x.length o)
        (cursorTape x o i i)) =
      some (tapeConfig 19 i (cursorTape x o i i)) := by
  have h := scan_left 19 ((i : Int) + seekDist x.length o)
    (cursorTape x o i i) (seekDist x.length o) (by
      intro p hp
      have hd := seekDist_pos x.length o hn2
      have he : (i : Int) + seekDist x.length o - p =
          ((i + seekDist x.length o - p : Nat) : Int) := by omega
      have hne : ((i + seekDist x.length o - p : Nat) : Int) ≠ (i : Int) := by
        omega
      rw [he, cursorTape_ne _ _ _ _ _ hne]
      exact rule_ret_keep _ (baseOf_outer x o i _))
  simpa [tapeConfig, Int.add_sub_cancel] using h

theorem inner_restore (x : List Bool) (o i : Nat) (hin : i < x.length) :
    step machine 0 (tapeConfig 19 i (cursorTape x o i i)) =
      some (tapeConfig 17 ((i : Int) + 1) (outerTape x o i)) := by
  have hcell : cursorTape x o i i (i : Int) = cursorBit x o i :=
    cursorTape_at _ _ _ _
  have hr : machine.rule 19 (cursorBit x o i) 0 =
      some { write := srcMark x o i, target := 17, move := .right } := by
    simp [machine, srcMark_base x o i]
  rw [step_write 19 17 i (cursorTape x o i i) (srcMark x o i) .right
    (by rw [hcell]; exact hr)]
  apply congrArg some
  simp [tapeConfig, moveHead]
  funext z
  by_cases hz : z = (i : Int)
  · subst z
    simp [cursorTape, Function.update, outerTape_src x o i i hin]
  · simp [cursorTape, Function.update, hz]

theorem inner_cycle (x : List Bool) (o i : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) (hi : 0 < i) (hin : i < x.length) :
    run machine (ticks (innerFuel x.length o))
      (tapeConfig 17 i (outerTape x o (i - 1))) =
      some (tapeConfig 17 ((i : Int) + 1) (outerTape x o i)) := by
  have hd : innerFuel x.length o =
      1 + seekDist x.length o + 1 + seekDist x.length o + 1 := by
    unfold innerFuel; omega
  rw [hd, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, run_ticks_one, inner_mark_step x o (i - 1) i hin,
    Option.bind_some, inner_seek x o i hn2 hi hin, Option.bind_some,
    run_ticks_one, inner_write x o i hn2 hi hin, Option.bind_some,
    inner_return x o i hn2 hi hin, Option.bind_some, run_ticks_one]
  exact inner_restore x o i hin

theorem le_timeBound (n : Nat) :
    n ^ 4 + n ^ 3 + 9 * n ^ 2 + 7 * n + 10 ≤ 1000 * (n + 1) ^ 6 := by
  have hb : 1 ≤ n + 1 := Nat.succ_pos n
  have hx : n ≤ n + 1 := Nat.le_succ n
  have h4 : n ^ 4 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left hx 4).trans (Nat.pow_le_pow_right hb (by omega))
  have h3 : n ^ 3 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left hx 3).trans (Nat.pow_le_pow_right hb (by omega))
  have h2 : n ^ 2 ≤ (n + 1) ^ 6 :=
    (Nat.pow_le_pow_left hx 2).trans (Nat.pow_le_pow_right hb (by omega))
  have h1 : n ≤ (n + 1) ^ 6 := by
    have hpow : n + 1 ≤ (n + 1) ^ 6 := by
      simpa using Nat.pow_le_pow_right hb (by omega : 1 ≤ 6)
    exact hx.trans hpow
  have h0 : 10 ≤ 10 * (n + 1) ^ 6 := Nat.mul_le_mul_left 10 (Nat.one_le_pow 6 (n + 1) hb)
  have : n ^ 4 + n ^ 3 + 9 * n ^ 2 + 7 * n + 10 ≤
      (n + 1) ^ 6 + (n + 1) ^ 6 + 9 * (n + 1) ^ 6 + 7 * (n + 1) ^ 6 +
        10 * (n + 1) ^ 6 := by
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h4 h3) ?_) ?_) h0
    · exact Nat.mul_le_mul_left 9 h2
    · exact Nat.mul_le_mul_left 7 h1
  have heq : (n + 1) ^ 6 + (n + 1) ^ 6 + 9 * (n + 1) ^ 6 + 7 * (n + 1) ^ 6 +
      10 * (n + 1) ^ 6 = 28 * (n + 1) ^ 6 := by ring
  rw [heq] at this
  exact this.trans (Nat.mul_le_mul_right _ (by omega : 28 ≤ 1000))

theorem inner_loop (x : List Bool) (o k : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) (hk : k ≤ x.length - 1) :
    run machine (ticks (k * innerFuel x.length o))
      (tapeConfig 17 1 (outerTape x o 0)) =
      some (tapeConfig 17 ((k + 1 : Nat) : Int) (outerTape x o k)) := by
  induction k with
  | zero => simp [ticks, run]
  | succ k ih =>
    have ht : (k + 1) * innerFuel x.length o =
        k * innerFuel x.length o + innerFuel x.length o := by ring
    rw [ht, ticks_add, run_append, ih (by omega), Option.bind_some]
    have hcyc := inner_cycle x o (k + 1) hn2 ho (Nat.succ_pos k) (by omega)
    have hhd : (k + 1 : Int) + 1 = ((k + 2 : Nat) : Int) := by omega
    simpa [tapeConfig, Nat.succ_eq_add_one, hhd] using hcyc

theorem inner_all (x : List Bool) (o : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) :
    run machine (ticks (innerLoopFuel x.length o))
      (tapeConfig 17 1 (outerTape x o 0)) =
      some (tapeConfig 17 (x.length : Int) (outerTape x o (x.length - 1))) := by
  have h := inner_loop x o (x.length - 1) hn2 ho le_rfl
  have hs : x.length - 1 + 1 = x.length :=
    Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 2) hn2)
  simpa [innerLoopFuel, hs] using h

theorem rule_outer_skip (b : Bool) :
    machine.rule 14 (proc b) 0 =
      some { write := proc b, target := 14, move := .right } := by
  cases b <;> simp [machine, proc]

theorem rule_outer_take (b : Bool) :
    machine.rule 14 (unproc b) 0 =
      some { write := active b, target := 15, move := .left } := by
  cases b <;> simp [machine, unproc, active]

theorem outer_skip (x : List Bool) (o : Nat) (ho : o ≤ x.length) :
    run machine (ticks o) (squareConfig x o) =
      some (tapeConfig 14 o (squareTape x o)) := by
  have h := scan_right 14 0 (squareTape x o) o (by
    intro p hp
    have he : (0 : Int) + p = (p : Int) := by omega
    have hpl : p < x.length := by omega
    rw [he, squareTape_src x o p hpl, if_pos hp]
    exact rule_outer_skip _)
  simpa [squareConfig, tapeConfig] using h

theorem outer_take (x : List Bool) (o : Nat) (ho : o < x.length) :
    step machine 0 (tapeConfig 14 o (squareTape x o)) =
      some (tapeConfig 15 ((o : Int) - 1) (outerTape x o 0)) := by
  have hread : squareTape x o o = unproc (bitAt x o) := by
    rw [squareTape_src x o o ho]; simp
  rw [step_write 14 15 o (squareTape x o) (active (bitAt x o)) .left
    (by rw [hread]; exact rule_outer_take (bitAt x o)),
    activate_tape x o ho]
  simp [tapeConfig, moveHead]

theorem rule_ret15 (a : Fin 19) (h : a ≠ 4) :
    machine.rule 15 a 0 =
      some { write := a, target := 15, move := .left } := by
  simp [machine, h]

theorem outer_return_inner (x : List Bool) (o p : Nat) :
    run machine (ticks o)
      (tapeConfig 15 ((o : Int) - 1) (outerTape x o p)) =
      some (tapeConfig 15 (-1) (outerTape x o p)) := by
  have h := scan_left 15 ((o : Int) - 1) (outerTape x o p) o (by
    intro k hk
    have he : (o : Int) - 1 - k = ((o - 1 - k : Nat) : Int) := by omega
    rw [he]
    exact rule_ret15 _ (outerTape_nat_ne_left x o p (o - 1 - k)))
  simpa [tapeConfig] using h

theorem outer_enter (x : List Bool) (o p : Nat) :
    step machine 0 (tapeConfig 15 (-1) (outerTape x o p)) =
      some (tapeConfig 16 0 (outerTape x o p)) := by
  rw [step_preserve 15 16 (-1) (outerTape x o p) .right
    (by rw [outerTape_neg1]; rfl)]
  rfl

theorem outer_skip_first (x : List Bool) (o p : Nat) :
    step machine 0 (tapeConfig 16 0 (outerTape x o p)) =
      some (tapeConfig 17 1 (outerTape x o p)) := by
  rw [step_preserve 16 17 0 (outerTape x o p) .right (by simp [machine])]
  simp [tapeConfig, moveHead]

theorem outer_pre (x : List Bool) (o : Nat) (ho : o < x.length) :
    run machine (ticks (2 * o + 3)) (squareConfig x o) =
      some (tapeConfig 17 1 (outerTape x o 0)) := by
  have ht : 2 * o + 3 = o + 1 + o + 1 + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, outer_skip x o (le_of_lt ho), Option.bind_some,
    run_ticks_one, outer_take x o ho, Option.bind_some, outer_return_inner,
    Option.bind_some, run_ticks_one, outer_enter, Option.bind_some,
    run_ticks_one]
  exact outer_skip_first x o 0

theorem outer_hit_sep (x : List Bool) (o : Nat) (_hn2 : 2 ≤ x.length)
    (_ho : o < x.length) :
    step machine 0 (tapeConfig 17 x.length (outerTape x o (x.length - 1))) =
      some (tapeConfig 20 ((x.length : Int) - 1)
        (outerTape x o (x.length - 1))) := by
  rw [step_preserve 17 20 x.length (outerTape x o (x.length - 1)) .left
    (by rw [outerTape_sep]; simp [machine])]
  simp [tapeConfig, moveHead]

theorem srcMark_ne_nine (x : List Bool) (o i : Nat) (h : i ≠ o) :
    srcMark x o i ≠ 9 := by
  unfold srcMark; split_ifs <;> first | decide | cases bitAt x i <;> decide

theorem srcMark_ne_ten (x : List Bool) (o i : Nat) (h : i ≠ o) :
    srcMark x o i ≠ 10 := by
  unfold srcMark; split_ifs <;> first | decide | cases bitAt x i <;> decide

theorem rule_ret20 (a : Fin 19) (h9 : a ≠ 9) (h10 : a ≠ 10) :
    machine.rule 20 a 0 =
      some { write := a, target := 20, move := .left } := by
  simp [machine, h9, h10]

theorem outer_return_active (x : List Bool) (o : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) :
    run machine (ticks (x.length - 1 - o))
      (tapeConfig 20 ((x.length : Int) - 1)
        (outerTape x o (x.length - 1))) =
      some (tapeConfig 20 o (outerTape x o (x.length - 1))) := by
  have h := scan_left 20 ((x.length : Int) - 1)
    (outerTape x o (x.length - 1)) (x.length - 1 - o) (by
      intro p hp
      have he : (x.length : Int) - 1 - p =
          ((x.length - 1 - p : Nat) : Int) := by omega
      have hpos : x.length - 1 - p ≠ o := by omega
      have hpl : x.length - 1 - p < x.length := by omega
      rw [he, outerTape_src x o _ _ hpl]
      exact rule_ret20 _ (srcMark_ne_nine x o _ hpos)
        (srcMark_ne_ten x o _ hpos))
  have hend : (x.length : Int) - 1 - ↑(x.length - 1 - o) = (o : Int) := by
    omega
  simpa [tapeConfig, hend] using h

theorem rule_deact (b : Bool) :
    machine.rule 20 (active b) 0 =
      some { write := proc b, target := 21, move := .left } := by
  cases b <;> simp [machine, active, proc]

theorem outerTape_active (x : List Bool) (o p : Nat) (ho : o < x.length) :
    outerTape x o p o = active (bitAt x o) := by
  rw [outerTape_src x o p o ho]; simp [srcMark]

theorem outer_deactivate (x : List Bool) (o : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) :
    step machine 0 (tapeConfig 20 o (outerTape x o (x.length - 1))) =
      some (tapeConfig 21 ((o : Int) - 1) (squareTape x (o + 1))) := by
  rw [step_write 20 21 o (outerTape x o (x.length - 1)) (proc (bitAt x o)) .left
    (by rw [outerTape_active x o _ ho]; exact rule_deact _),
    deactivate_tape x o ho hn2]
  simp [tapeConfig, moveHead]

theorem rule_ret21 (a : Fin 19) (h : a ≠ 4) :
    machine.rule 21 a 0 =
      some { write := a, target := 21, move := .left } := by
  simp [machine, h]

theorem outer_home (x : List Bool) (o : Nat) :
    run machine (ticks o)
      (tapeConfig 21 ((o : Int) - 1) (squareTape x (o + 1))) =
      some (tapeConfig 21 (-1) (squareTape x (o + 1))) := by
  have h := scan_left 21 ((o : Int) - 1) (squareTape x (o + 1)) o (by
    intro k hk
    have he : (o : Int) - 1 - k = ((o - 1 - k : Nat) : Int) := by omega
    rw [he]
    exact rule_ret21 _ (squareTape_nat_ne_left x (o + 1) (o - 1 - k)))
  simpa [tapeConfig] using h

theorem outer_restart (x : List Bool) (o : Nat) :
    step machine 0 (tapeConfig 21 (-1) (squareTape x (o + 1))) =
      some (squareConfig x (o + 1)) := by
  rw [step_preserve 21 14 (-1) (squareTape x (o + 1)) .right
    (by rw [squareTape_neg1]; rfl)]
  simp [squareConfig, tapeConfig, moveHead]

theorem outer_post (x : List Bool) (o : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) :
    run machine (ticks (x.length + 2))
      (tapeConfig 17 x.length (outerTape x o (x.length - 1))) =
      some (squareConfig x (o + 1)) := by
  have ht : x.length + 2 = 1 + (x.length - 1 - o) + 1 + o + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, run_ticks_one, outer_hit_sep x o hn2 ho,
    Option.bind_some, outer_return_active x o hn2 ho, Option.bind_some,
    run_ticks_one, outer_deactivate x o hn2 ho, Option.bind_some, outer_home,
    Option.bind_some, run_ticks_one]
  exact outer_restart x o

theorem outer_step (x : List Bool) (o : Nat)
    (hn2 : 2 ≤ x.length) (ho : o < x.length) :
    run machine (ticks (outerFuel x.length o)) (squareConfig x o) =
      some (squareConfig x (o + 1)) := by
  have ht : outerFuel x.length o =
      2 * o + 3 + innerLoopFuel x.length o + (x.length + 2) := by
    unfold outerFuel; omega
  rw [ht, ticks_add, ticks_add, run_append, run_append, outer_pre x o ho,
    Option.bind_some, inner_all x o hn2 ho, Option.bind_some]
  exact outer_post x o hn2 ho

def squareFuel (n k : Nat) : Nat :=
  k * (k + n + 4) + (n - 1) * k * ((n - 1) * (k + 1) + 3)

theorem squareFuel_step (n k : Nat) :
    squareFuel n (k + 1) = squareFuel n k + outerFuel n k := by
  unfold squareFuel outerFuel innerLoopFuel innerFuel seekDist
  ring

theorem square_run (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k ≤ x.length) :
    run machine (ticks (squareFuel x.length k)) (squareConfig x 0) =
      some (squareConfig x k) := by
  induction k with
  | zero => simp [squareFuel, ticks, run]
  | succ k ih =>
    rw [squareFuel_step, ticks_add, run_append, ih (by omega), Option.bind_some]
    exact outer_step x k hn2 (by omega)

theorem mul_pred (n : Nat) (h : 1 ≤ n) : n + n * (n - 1) = n * n := by
  zify; rw [nat_pred_cast n h]; ring

theorem squareTape_all_proc (x : List Bool) (i : Nat) (hi : i < x.length) :
    squareTape x x.length i = proc (bitAt x i) := by
  rw [squareTape_src x x.length i hi, if_pos hi]

theorem squareTape_zero_range (x : List Bool) (p : Nat)
    (hn : 2 ≤ x.length) (hp1 : x.length < p)
    (hp2 : p < x.length * x.length + 1) :
    squareTape x x.length (p : Int) = 0 := by
  have hn1 : (p : Int) ≠ -1 := by omega
  have hneg : ¬ (p : Int) < 0 := by omega
  have hlt : ¬ p < x.length := by omega
  have he : ¬ p = x.length := by omega
  have hz : p < x.length + x.length * (x.length - 1) + 1 := by
    have hmul := mul_pred x.length (Nat.le_trans (by decide : 1 ≤ 2) hn)
    omega
  simp [squareTape, hn1, hneg, Int.toNat_natCast, hlt, he, hz]

theorem squareTape_blank_after (x : List Bool) (hn : 2 ≤ x.length) :
    squareTape x x.length ((x.length * x.length + 1 : Nat) : Int) = 2 := by
  set j := x.length * x.length + 1
  have hnn : x.length ≤ x.length * x.length :=
    Nat.le_mul_of_pos_right _ (Nat.le_trans (by decide : 1 ≤ 2) hn)
  have hmul := mul_pred x.length (Nat.le_trans (by decide : 1 ≤ 2) hn)
  have hn1 : (j : Int) ≠ -1 := natCast_ne_neg_one j
  have hneg : ¬ (j : Int) < 0 := by
    have : (0 : Int) ≤ j := Nat.cast_nonneg j
    omega
  have hlt : ¬ j < x.length :=
    Nat.not_lt.mpr (hnn.trans (Nat.le_add_right _ 1))
  have he : j ≠ x.length := by
    intro hje; omega
  have hz : ¬ j < x.length + x.length * (x.length - 1) + 1 := by
    rw [hmul]; exact Nat.not_lt.mpr le_rfl
  simp [squareTape, hn1, hneg, Int.toNat_natCast, hlt, he, hz]

theorem finish_skip (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks x.length) (squareConfig x x.length) =
      some (tapeConfig 14 x.length (squareTape x x.length)) := by
  have h := scan_right 14 0 (squareTape x x.length) x.length (by
    intro p hp
    have he : (0 : Int) + p = (p : Int) := by omega
    rw [he, squareTape_all_proc x p hp]
    exact rule_outer_skip _)
  simpa [squareConfig, tapeConfig] using h

theorem finish_sep (x : List Bool) :
    step machine 0 (tapeConfig 14 x.length (squareTape x x.length)) =
      some (tapeConfig 22 ((x.length : Int) + 1) (squareTape x x.length)) := by
  rw [step_preserve 14 22 x.length (squareTape x x.length) .right
    (by rw [squareTape_sep]; simp [machine])]
  simp [tapeConfig, moveHead]

theorem rule_fin22 (a : Fin 19) (h : a ≠ 2) :
    machine.rule 22 a 0 =
      some { write := a, target := 22, move := .right } := by
  simp [machine, h]

theorem finish_zeros (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (x.length * (x.length - 1)))
      (tapeConfig 22 ((x.length : Int) + 1) (squareTape x x.length)) =
      some (tapeConfig 22 ((x.length * x.length + 1 : Nat) : Int)
        (squareTape x x.length)) := by
  have h := scan_right 22 ((x.length : Int) + 1) (squareTape x x.length)
    (x.length * (x.length - 1)) (by
      intro p hp
      have he : (x.length : Int) + 1 + p =
          ((x.length + 1 + p : Nat) : Int) := by omega
      have hpos : x.length < x.length + 1 + p := by omega
      have hbound : x.length + 1 + p < x.length * x.length + 1 := by
        have hmul := mul_pred x.length (Nat.le_trans (by decide : 1 ≤ 2) hn2)
        omega
      rw [he, squareTape_zero_range x (x.length + 1 + p) hn2 hpos hbound]
      exact rule_fin22 _ (by decide))
  have hn1 : 1 ≤ x.length := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have hend : (x.length : Int) + 1 +
      (x.length : Int) * ((x.length - 1 : Nat) : Int) =
      (x.length : Int) * x.length + 1 := by
    rw [nat_pred_cast x.length hn1]; ring
  have hL : ↑(x.length * (x.length - 1)) =
      (x.length : Int) * ((x.length - 1 : Nat) : Int) := Nat.cast_mul _ _
  have hR : ((x.length * x.length + 1 : Nat) : Int) =
      (x.length : Int) * x.length + 1 := by
    simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  convert h
  simp [tapeConfig, hL, hend, hR]

theorem finish_blank (x : List Bool) (hn2 : 2 ≤ x.length) :
    step machine 0 (tapeConfig 22 ((x.length * x.length + 1 : Nat) : Int)
        (squareTape x x.length)) =
      some (tapeConfig 23 (x.length * x.length : Nat)
        (squareTape x x.length)) := by
  rw [step_preserve 22 23 ((x.length * x.length + 1 : Nat) : Int)
    (squareTape x x.length) .left
    (by rw [squareTape_blank_after x hn2]; simp [machine])]
  simp [tapeConfig, moveHead]

theorem finish_write17 (x : List Bool) (hn2 : 2 ≤ x.length) :
    step machine 0 (tapeConfig 23 (x.length * x.length : Nat)
        (squareTape x x.length)) =
      some (tapeConfig 24 (((x.length * x.length : Nat) : Int) - 1)
        (Function.update (squareTape x x.length)
          ((x.length * x.length : Nat) : Int) 17)) := by
  rw [step_write 23 24 (x.length * x.length : Nat) (squareTape x x.length) 17
    .left (by simp [machine])]
  simp [tapeConfig, moveHead]

theorem rule_ret24 (a : Fin 19) (h : a ≠ 4) :
    machine.rule 24 a 0 =
      some { write := a, target := 24, move := .left } := by
  simp [machine, h]

theorem finish_return (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (x.length * x.length))
      (tapeConfig 24 (((x.length * x.length : Nat) : Int) - 1)
        (Function.update (squareTape x x.length)
          ((x.length * x.length : Nat) : Int) 17)) =
      some (tapeConfig 24 (-1)
        (Function.update (squareTape x x.length)
          ((x.length * x.length : Nat) : Int) 17)) := by
  have h := scan_left 24 (((x.length * x.length : Nat) : Int) - 1)
    (Function.update (squareTape x x.length) ((x.length * x.length : Nat) : Int) 17)
    (x.length * x.length) (by
      intro p hp
      have he : ((x.length * x.length : Nat) : Int) - 1 - p =
          ((x.length * x.length - 1 - p : Nat) : Int) := by omega
      have hne : ((x.length * x.length - 1 - p : Nat) : Int) ≠
          ((x.length * x.length : Nat) : Int) := by omega
      rw [he, Function.update_of_ne hne]
      exact rule_ret24 _ (squareTape_nat_ne_left x x.length
        (x.length * x.length - 1 - p)))
  simpa [tapeConfig] using h

theorem finish_to_large (x : List Bool) (hn2 : 2 ≤ x.length) :
    Function.update
      (Function.update (squareTape x x.length)
        ((x.length * x.length : Nat) : Int) 17) (-1) 18 =
      largeTape x := by
  funext z
  set j := x.length * x.length
  have hmul := mul_pred x.length (Nat.le_trans (by decide : 1 ≤ 2) hn2)
  by_cases hl : z = -1
  · subst z; simp [largeTape, Function.update]
  · rw [Function.update_of_ne hl]
    by_cases hz : z = (j : Int)
    · subst z
      simp [Function.update]
      have hnn : (j : Int) ≠ -1 := natCast_ne_neg_one j
      have hneg : ¬ (j : Int) < 0 := by
        have : (0 : Int) ≤ j := Nat.cast_nonneg j
        omega
      have hlt : ¬ j < x.length := Nat.not_lt.mpr
        (Nat.le_mul_of_pos_right _ (Nat.le_trans (by decide : 1 ≤ 2) hn2))
      have he : ¬ j = x.length := by
        intro hje
        have hpos : 0 < x.length := Nat.le_trans (by decide : 1 ≤ 2) hn2
        have : x.length * x.length = x.length * 1 := by
          simpa [Nat.mul_one] using hje
        have : x.length = 1 := Nat.eq_of_mul_eq_mul_left hpos this
        omega
      simp only [largeTape, hnn, if_false, hneg, Int.toNat_natCast]
      split_ifs <;> first | rfl | contradiction | omega
    · rw [Function.update_of_ne hz]
      by_cases hneg : z < 0
      · simp [squareTape, largeTape, hl, hneg]
      · have hz' : z = (z.toNat : Int) :=
          (Int.toNat_of_nonneg (le_of_not_gt hneg)).symm
        rw [hz']
        have hne : z.toNat ≠ j := by
          intro hte; exact hz (by rw [hz', hte])
        simp only [squareTape, largeTape, Int.toNat_natCast]
        split_ifs <;> first | rfl | (simp [hne, hmul]; omega)

theorem finish_boundary (x : List Bool) (hn2 : 2 ≤ x.length) :
    step machine 0 (tapeConfig 24 (-1)
        (Function.update (squareTape x x.length)
          ((x.length * x.length : Nat) : Int) 17)) =
      some (tapeConfig 6 0 (largeTape x)) := by
  have hne : (-1 : Int) ≠ ((x.length * x.length : Nat) : Int) :=
    (natCast_ne_neg_one _).symm
  rw [step_write 24 6 (-1)
    (Function.update (squareTape x x.length) ((x.length * x.length : Nat) : Int) 17)
    18 .right (by rw [Function.update_of_ne hne, squareTape_neg1]; rfl),
    finish_to_large x hn2]
  simp [tapeConfig, moveHead]

theorem finish_run (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (finishFuel x.length)) (squareConfig x x.length) =
      some (tapeConfig 6 0 (largeTape x)) := by
  have hn1 : 1 ≤ x.length := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have ht : finishFuel x.length =
      x.length + 1 + x.length * (x.length - 1) + 1 + 1 +
        x.length * x.length + 1 := by
    unfold finishFuel; zify; rw [nat_pred_cast x.length hn1]; ring
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add,
    run_append, run_append, run_append, run_append, run_append, run_append,
    finish_skip x hn2, Option.bind_some, run_ticks_one, finish_sep,
    Option.bind_some, finish_zeros x hn2, Option.bind_some, run_ticks_one,
    finish_blank x hn2, Option.bind_some, run_ticks_one, finish_write17 x hn2,
    Option.bind_some, finish_return x hn2, Option.bind_some, run_ticks_one]
  exact finish_boundary x hn2


theorem n_le_nn (n : Nat) (h : 1 ≤ n) : n ≤ n * n :=
  Nat.le_mul_of_pos_right n h

theorem n_lt_nn (n : Nat) (h : 2 ≤ n) : n < n * n := by
  have hpos : 0 < n := Nat.le_trans (by decide : 1 ≤ 2) h
  have hone : 1 < n := Nat.succ_le_iff.mp h
  have : n * 1 < n * n := Nat.mul_lt_mul_of_pos_left hone hpos
  simpa [Nat.mul_one] using this

def doneTape (x : List Bool) (z : Int) : Fin 19 :=
  if z = -1 then 18
  else if z < 0 then 2
  else if z.toNat < x.length * x.length then 0
  else if z.toNat = x.length * x.length then 1
  else if z.toNat < x.length * x.length + x.length + 1 then
    writeBit (bitAt x (z.toNat - x.length * x.length - 1))
  else 2

theorem copyTape_ofNat (x : List Bool) (k p : Nat) :
    copyTape x k (p : Int) =
      if p < k then 0
      else if p < x.length then proc (bitAt x p)
      else if p = x.length then 5
      else if p < x.length * x.length then 0
      else if p = x.length * x.length then 17
      else if p < x.length * x.length + k + 1 then
        writeBit (bitAt x (p - x.length * x.length - 1))
      else 2 := by
  have hn : (p : Int) ≠ -1 := natCast_ne_neg_one p
  have hneg : ¬ (p : Int) < 0 := not_lt.mpr (Nat.cast_nonneg p)
  simp only [copyTape, hn, if_false, hneg, Int.toNat_natCast]

theorem largeTape_ofNat (x : List Bool) (p : Nat) :
    largeTape x (p : Int) =
      if p < x.length then proc (bitAt x p)
      else if p = x.length then 5
      else if p < x.length * x.length then 0
      else if p = x.length * x.length then 17
      else 2 := by
  have hn : (p : Int) ≠ -1 := natCast_ne_neg_one p
  have hneg : ¬ (p : Int) < 0 := not_lt.mpr (Nat.cast_nonneg p)
  simp only [largeTape, hn, if_false, hneg, Int.toNat_natCast]

theorem doneTape_ofNat (x : List Bool) (p : Nat) :
    doneTape x (p : Int) =
      if p < x.length * x.length then 0
      else if p = x.length * x.length then 1
      else if p < x.length * x.length + x.length + 1 then
        writeBit (bitAt x (p - x.length * x.length - 1))
      else 2 := by
  have hn : (p : Int) ≠ -1 := natCast_ne_neg_one p
  have hneg : ¬ (p : Int) < 0 := not_lt.mpr (Nat.cast_nonneg p)
  simp only [doneTape, hn, if_false, hneg, Int.toNat_natCast]

theorem copyTape_zero_eq (x : List Bool) : copyTape x 0 = largeTape x := by
  funext z
  by_cases hl : z = -1
  · subst z; rfl
  · by_cases hn : z < 0
    · simp [copyTape, largeTape, hl, hn]
    · have hz : z = (z.toNat : Int) :=
        (Int.toNat_of_nonneg (le_of_not_gt hn)).symm
      rw [hz, copyTape_ofNat, largeTape_ofNat]
      have h0 : ¬ z.toNat < 0 := Nat.not_lt_zero _
      simp only [h0, ite_false]
      by_cases hs : z.toNat < x.length
      · simp only [hs, ite_true]
      · simp only [hs, ite_false]
        by_cases he : z.toNat = x.length
        · simp only [he, ite_true]
        · simp only [he, ite_false]
          by_cases hz0 : z.toNat < x.length * x.length
          · simp only [hz0, ite_true]
          · simp only [hz0, ite_false]
            by_cases h17 : z.toNat = x.length * x.length
            · simp only [h17, ite_true]
            · simp only [h17, ite_false]
              have : ¬ z.toNat < x.length * x.length + 0 + 1 := by omega
              simp only [this, ite_false]

theorem copyTape_nonblank (x : List Bool) (k j : Nat) (_hk : k ≤ x.length)
    (hj : j < x.length * x.length + k + 1) :
    copyTape x k (j : Int) ≠ 2 := by
  rw [copyTape_ofNat]
  split_ifs <;> first | decide | cases bitAt x _ <;> decide | omega

theorem rule_large_zero :
    machine.rule 6 0 0 = some { write := 0, target := 6, move := .right } := by
  simp [machine]

theorem copy_skip (x : List Bool) (k : Nat) :
    run machine (ticks k) (tapeConfig 6 0 (copyTape x k)) =
      some (tapeConfig 6 k (copyTape x k)) := by
  have h := scan_right 6 0 (copyTape x k) k (by
    intro p hp
    have he : (0 : Int) + p = (p : Int) := by omega
    have hz : copyTape x k (p : Int) = 0 := by
      rw [copyTape_ofNat]; simp only [hp, ite_true]
    rw [he, hz]
    exact rule_large_zero)
  simpa [tapeConfig] using h

theorem rule_large_proc (b : Bool) :
    machine.rule 6 (proc b) 0 =
      some { write := 0, target := seekBit b, move := .right } := by
  cases b <;> simp [machine, proc, seekBit]

theorem copy_take (x : List Bool) (k : Nat) (hk : k < x.length) :
    step machine 0 (tapeConfig 6 k (copyTape x k)) =
      some (tapeConfig (seekBit (bitAt x k)) ((k : Int) + 1)
        (Function.update (copyTape x k) k 0)) := by
  have hread : copyTape x k k = proc (bitAt x k) := by
    rw [copyTape_ofNat]
    simp only [Nat.lt_irrefl k, hk, ite_false, ite_true]
  rw [step_write 6 (seekBit (bitAt x k)) k (copyTape x k) 0 .right
    (by rw [hread]; exact rule_large_proc _)]
  simp [tapeConfig, moveHead]

theorem copy_seek (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k < x.length) :
    run machine (ticks (x.length * x.length))
      (tapeConfig (seekBit (bitAt x k)) ((k : Int) + 1)
        (Function.update (copyTape x k) k 0)) =
      some (tapeConfig (seekBit (bitAt x k))
        ((x.length * x.length + k + 1 : Nat) : Int)
        (Function.update (copyTape x k) k 0)) := by
  have h := scan_right (seekBit (bitAt x k)) ((k : Int) + 1)
    (Function.update (copyTape x k) k 0) (x.length * x.length) (by
      intro p hp
      have he : (k : Int) + 1 + p = ((k + 1 + p : Nat) : Int) := by
        simp [Nat.cast_add, Nat.cast_one]
      have hne : ((k + 1 + p : Nat) : Int) ≠ (k : Int) := by
        have : k + 1 + p ≠ k := by omega
        exact Nat.cast_injective.ne this
      have hnb : copyTape x k (k + 1 + p) ≠ 2 :=
        copyTape_nonblank x k (k + 1 + p) (le_of_lt hk) (by
          have : k + 1 + p < x.length * x.length + k + 1 := by omega
          exact this)
      rw [he, Function.update_of_ne hne]
      cases bitAt x k <;> simp [machine, seekBit, hnb])
  have hend : (k : Int) + 1 + ↑(x.length * x.length) =
      ((x.length * x.length + k + 1 : Nat) : Int) := by
    simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    try ring
  rw [← hend]
  exact h

theorem copy_blank (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k < x.length) :
    Function.update (copyTape x k) k 0
      ((x.length * x.length + k + 1 : Nat) : Int) = 2 := by
  have hne : ((x.length * x.length + k + 1 : Nat) : Int) ≠ (k : Int) := by
    have : x.length * x.length + k + 1 ≠ k := by
      have hpos : 0 < x.length * x.length :=
        Nat.mul_pos (Nat.le_trans (by decide : 1 ≤ 2) hn2)
          (Nat.le_trans (by decide : 1 ≤ 2) hn2)
      omega
    exact Nat.cast_injective.ne this
  rw [Function.update_of_ne hne, copyTape_ofNat]
  set j := x.length * x.length + k + 1
  have h1 : ¬ j < k := Nat.not_lt.mpr (Nat.le_trans (Nat.le_add_left k _) (Nat.le_add_right _ 1))
  have h2 : ¬ j < x.length := by
    have := n_lt_nn x.length hn2
    omega
  have h3 : j ≠ x.length := by
    have := n_lt_nn x.length hn2
    omega
  have h4 : ¬ j < x.length * x.length := by omega
  have h5 : j ≠ x.length * x.length := by omega
  have h6 : ¬ j < j := Nat.lt_irrefl j
  simp only [h1, h2, h3, h4, h5, h6, ite_false]

theorem copy_append (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k < x.length) :
    Function.update (Function.update (copyTape x k) k 0)
      ((x.length * x.length + k + 1 : Nat) : Int)
      (writeBit (bitAt x k)) = copyTape x (k + 1) := by
  funext z
  set j := x.length * x.length + k + 1
  by_cases hend : z = (j : Int)
  · subst z
    simp only [Function.update_self]
    rw [copyTape_ofNat]
    have h1 : ¬ j < k + 1 := by
      have := n_le_nn x.length (Nat.le_trans (by decide : 1 ≤ 2) hn2)
      omega
    have h2 : ¬ j < x.length := by
      have := n_lt_nn x.length hn2
      omega
    have h3 : j ≠ x.length := by
      have := n_lt_nn x.length hn2
      omega
    have h4 : ¬ j < x.length * x.length := by omega
    have h5 : j ≠ x.length * x.length := by omega
    have h6 : j < x.length * x.length + (k + 1) + 1 := by omega
    have hidx : j - x.length * x.length - 1 = k := by omega
    simp only [h1, h2, h3, h4, h5, h6, hidx, ite_false, ite_true]
  · rw [Function.update_of_ne hend]
    by_cases htake : z = (k : Int)
    · subst z
      simp only [Function.update_self]
      rw [copyTape_ofNat]
      simp only [Nat.lt_succ_self k, ite_true]
    · rw [Function.update_of_ne htake]
      by_cases hl : z = -1
      · subst z; rfl
      · by_cases hn : z < 0
        · simp [copyTape, hl, hn]
        · have hz : z = (z.toNat : Int) :=
            (Int.toNat_of_nonneg (le_of_not_gt hn)).symm
          rw [hz, copyTape_ofNat, copyTape_ofNat]
          have hnej : z.toNat ≠ j := by
            intro h; exact hend (by rw [hz, h])
          have hnek : z.toNat ≠ k := by
            intro h; exact htake (by rw [hz, h])
          split_ifs <;> first | rfl | (exfalso; omega)

theorem copy_write (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k < x.length) :
    step machine 0 (tapeConfig (seekBit (bitAt x k))
        ((x.length * x.length + k + 1 : Nat) : Int)
        (Function.update (copyTape x k) k 0)) =
      some (tapeConfig 9 ((x.length * x.length + k : Nat) : Int)
        (copyTape x (k + 1))) := by
  rw [step_write (seekBit (bitAt x k)) 9
    ((x.length * x.length + k + 1 : Nat) : Int)
    (Function.update (copyTape x k) k 0) (writeBit (bitAt x k)) .left
    (by
      rw [copy_blank x k hn2 hk]
      cases bitAt x k <;> simp [machine, seekBit, writeBit]),
    copy_append x k hn2 hk]
  try
    (have hend : ((x.length * x.length + k + 1 : Nat) : Int) - 1 =
        ((x.length * x.length + k : Nat) : Int) := by
      simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      try ring
     simp [tapeConfig, moveHead, hend])

theorem rule_ret9 (a : Fin 19) (h4 : a ≠ 4) (h18 : a ≠ 18) :
    machine.rule 9 a 0 =
      some { write := a, target := 9, move := .left } := by
  simp [machine, h4, h18]

theorem copyTape_nat_ne_bound (x : List Bool) (k p : Nat) :
    copyTape x k (p : Int) ≠ 4 ∧ copyTape x k (p : Int) ≠ 18 := by
  rw [copyTape_ofNat]
  constructor <;> split_ifs <;> first | decide | cases bitAt x _ <;> decide

theorem copy_return (x : List Bool) (k : Nat) :
    run machine (ticks (x.length * x.length + k + 1))
      (tapeConfig 9 ((x.length * x.length + k : Nat) : Int)
        (copyTape x (k + 1))) =
      some (tapeConfig 9 (-1) (copyTape x (k + 1))) := by
  have h := scan_left 9 ((x.length * x.length + k : Nat) : Int)
    (copyTape x (k + 1)) (x.length * x.length + k + 1) (by
      intro p hp
      have he : ((x.length * x.length + k : Nat) : Int) - p =
          ((x.length * x.length + k - p : Nat) : Int) := by omega
      rw [he]
      have hb := copyTape_nat_ne_bound x (k + 1) (x.length * x.length + k - p)
      exact rule_ret9 _ hb.1 hb.2)
  have hend : ((x.length * x.length + k : Nat) : Int) -
      ↑(x.length * x.length + k + 1) = -1 := by
    simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    try ring
  rw [← hend]
  exact h

theorem copy_restart (x : List Bool) (k : Nat) :
    step machine 0 (tapeConfig 9 (-1) (copyTape x k)) =
      some (tapeConfig 6 0 (copyTape x k)) := by
  have hread : copyTape x k (-1) = 18 := rfl
  rw [step_preserve 9 6 (-1) (copyTape x k) .right
    (by rw [hread]; simp [machine])]
  rfl

theorem copy_cycle (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k < x.length) :
    run machine (ticks (copyCycleFuel x.length k))
      (tapeConfig 6 0 (copyTape x k)) =
      some (tapeConfig 6 0 (copyTape x (k + 1))) := by
  have ht : copyCycleFuel x.length k =
      k + 1 + x.length * x.length + 1 + (x.length * x.length + k + 1) + 1 := by
    unfold copyCycleFuel; ring
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, run_append,
    run_append, run_append, run_append, run_append, copy_skip x k,
    Option.bind_some, run_ticks_one, copy_take x k hk, Option.bind_some,
    copy_seek x k hn2 hk, Option.bind_some, run_ticks_one,
    copy_write x k hn2 hk, Option.bind_some, copy_return x k,
    Option.bind_some, run_ticks_one]
  exact copy_restart x (k + 1)

def copyFuel (n k : Nat) : Nat := 2 * n * n * k + k * k + 3 * k

theorem copyFuel_step (n k : Nat) :
    copyFuel n (k + 1) = copyFuel n k + copyCycleFuel n k := by
  unfold copyFuel copyCycleFuel; ring

theorem copy_run (x : List Bool) (k : Nat)
    (hn2 : 2 ≤ x.length) (hk : k ≤ x.length) :
    run machine (ticks (copyFuel x.length k))
      (tapeConfig 6 0 (copyTape x 0)) =
      some (tapeConfig 6 0 (copyTape x k)) := by
  induction k with
  | zero => simp [copyFuel, ticks, run]
  | succ k ih =>
    rw [copyFuel_step, ticks_add, run_append, ih (by omega), Option.bind_some]
    exact copy_cycle x k hn2 (by omega)

theorem copyTape_len (x : List Bool) (p : Nat) :
    copyTape x x.length (p : Int) =
      if p < x.length then 0
      else if p = x.length then 5
      else if p < x.length * x.length then 0
      else if p = x.length * x.length then 17
      else if p < x.length * x.length + x.length + 1 then
        writeBit (bitAt x (p - x.length * x.length - 1))
      else 2 := by
  rw [copyTape_ofNat]
  by_cases h : p < x.length
  · simp only [h, ite_true]
  · simp only [h, ite_false]

theorem drain_skip (x : List Bool) :
    run machine (ticks x.length) (tapeConfig 6 0 (copyTape x x.length)) =
      some (tapeConfig 6 x.length (copyTape x x.length)) :=
  copy_skip x x.length

theorem drain_five (x : List Bool) :
    step machine 0 (tapeConfig 6 x.length (copyTape x x.length)) =
      some (tapeConfig 6 ((x.length : Int) + 1)
        (Function.update (copyTape x x.length) (x.length : Int) 0)) := by
  have hread : copyTape x x.length (x.length : Int) = 5 := by
    rw [copyTape_len]; simp only [Nat.lt_irrefl, ite_false, ite_true]
  rw [step_write 6 6 x.length (copyTape x x.length) 0 .right
    (by rw [hread]; simp [machine])]
  simp [tapeConfig, moveHead]

theorem drain_zeros (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (x.length * x.length - x.length - 1))
      (tapeConfig 6 ((x.length : Int) + 1)
        (Function.update (copyTape x x.length) (x.length : Int) 0)) =
      some (tapeConfig 6 (x.length * x.length : Nat)
        (Function.update (copyTape x x.length) (x.length : Int) 0)) := by
  have hle : x.length + 1 ≤ x.length * x.length := by
    have := n_lt_nn x.length hn2
    omega
  have h := scan_right 6 ((x.length : Int) + 1)
    (Function.update (copyTape x x.length) (x.length : Int) 0)
    (x.length * x.length - x.length - 1) (by
      intro p hp
      have he : (x.length : Int) + 1 + p =
          ((x.length + 1 + p : Nat) : Int) := by
        simp [Nat.cast_add, Nat.cast_one]
      have hne : ((x.length + 1 + p : Nat) : Int) ≠ (x.length : Int) := by
        have : x.length + 1 + p ≠ x.length := by omega
        exact Nat.cast_injective.ne this
      have hpos : x.length + 1 + p < x.length * x.length := by
        have hsub : x.length * x.length - x.length - 1 =
            x.length * x.length - (x.length + 1) := (Nat.sub_add_eq _ _ _).symm
        omega
      rw [he, Function.update_of_ne hne, copyTape_len]
      have h1 : ¬ x.length + 1 + p < x.length := by omega
      have h2 : x.length + 1 + p ≠ x.length := by omega
      have h3 : x.length + 1 + p < x.length * x.length := hpos
      simp only [h1, h2, h3, ite_false, ite_true]
      exact rule_large_zero)
  have hend : (x.length : Int) + 1 + ↑(x.length * x.length - x.length - 1) =
      ((x.length * x.length : Nat) : Int) := by
    have hsub : x.length * x.length - x.length - 1 =
        x.length * x.length - (x.length + 1) := (Nat.sub_add_eq _ _ _).symm
    rw [hsub, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    try ring
  rw [← hend]
  exact h

theorem drain_to_done (x : List Bool) (hn2 : 2 ≤ x.length) :
    Function.update
      (Function.update (copyTape x x.length) (x.length : Int) 0)
      ((x.length * x.length : Nat) : Int) 1 = doneTape x := by
  funext z
  by_cases hl : z = -1
  · subst z
    have hne : (-1 : Int) ≠ ((x.length * x.length : Nat) : Int) :=
      (natCast_ne_neg_one _).symm
    have hns : (-1 : Int) ≠ (x.length : Int) := (natCast_ne_neg_one _).symm
    rw [Function.update_of_ne hne, Function.update_of_ne hns]
    rfl
  · by_cases hz : z = ((x.length * x.length : Nat) : Int)
    · subst z
      simp only [Function.update_self]
      rw [doneTape_ofNat]
      simp only [Nat.lt_irrefl, ite_false, ite_true]
    · rw [Function.update_of_ne hz]
      by_cases hs : z = (x.length : Int)
      · subst z
        simp only [Function.update_self]
        rw [doneTape_ofNat]
        have hlt := n_lt_nn x.length hn2
        simp only [hlt, ite_true]
      · rw [Function.update_of_ne hs]
        by_cases hn : z < 0
        · simp [copyTape, doneTape, hl, hn]
        · have hz' : z = (z.toNat : Int) :=
            (Int.toNat_of_nonneg (le_of_not_gt hn)).symm
          rw [hz', copyTape_len, doneTape_ofNat]
          have hnej : z.toNat ≠ x.length * x.length := by
            intro h; exact hz (by rw [hz', h])
          have hnes : z.toNat ≠ x.length := by
            intro h; exact hs (by rw [hz', h])
          have hnn : x.length ≤ x.length * x.length :=
            n_le_nn x.length (Nat.le_trans (by decide : 1 ≤ 2) hn2)
          have hlt := n_lt_nn x.length hn2
          split_ifs <;> first | rfl | (exfalso; omega)

theorem drain_sep (x : List Bool) (hn2 : 2 ≤ x.length) :
    step machine 0 (tapeConfig 6 (x.length * x.length : Nat)
        (Function.update (copyTape x x.length) (x.length : Int) 0)) =
      some (tapeConfig 8 (((x.length * x.length : Nat) : Int) - 1)
        (doneTape x)) := by
  have hne : ((x.length * x.length : Nat) : Int) ≠ (x.length : Int) := by
    have := n_lt_nn x.length hn2
    exact Nat.cast_injective.ne (ne_of_gt this)
  have hread : Function.update (copyTape x x.length) (x.length : Int) 0
      (x.length * x.length : Nat) = 17 := by
    rw [Function.update_of_ne hne, copyTape_len]
    have h1 : ¬ x.length * x.length < x.length :=
      Nat.not_lt.mpr (le_of_lt (n_lt_nn x.length hn2))
    have h2 : x.length * x.length ≠ x.length := ne_of_gt (n_lt_nn x.length hn2)
    have h3 : ¬ x.length * x.length < x.length * x.length := Nat.lt_irrefl _
    simp only [h1, h2, h3, ite_false, ite_true]
  rw [step_write 6 8 (x.length * x.length : Nat)
    (Function.update (copyTape x x.length) (x.length : Int) 0) 1 .left
    (by rw [hread]; simp [machine]), drain_to_done x hn2]
  rfl

theorem doneTape_nat_ne_bound (x : List Bool) (p : Nat) :
    doneTape x (p : Int) ≠ 4 ∧ doneTape x (p : Int) ≠ 18 := by
  rw [doneTape_ofNat]
  constructor <;> split_ifs <;> first | decide | cases bitAt x _ <;> decide

theorem cleanup_return (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (x.length * x.length))
      (tapeConfig 8 (((x.length * x.length : Nat) : Int) - 1) (doneTape x)) =
      some (tapeConfig 8 (-1) (doneTape x)) := by
  have h := scan_left 8 (((x.length * x.length : Nat) : Int) - 1) (doneTape x)
    (x.length * x.length) (by
      intro p hp
      have he : ((x.length * x.length : Nat) : Int) - 1 - p =
          ((x.length * x.length - 1 - p : Nat) : Int) := by
        have hpos : 0 < x.length * x.length :=
          Nat.mul_pos (Nat.le_trans (by decide : 1 ≤ 2) hn2)
            (Nat.le_trans (by decide : 1 ≤ 2) hn2)
        omega
      rw [he]
      have hb := doneTape_nat_ne_bound x (x.length * x.length - 1 - p)
      simp [machine, hb.1, hb.2])
  have hend : ((x.length * x.length : Nat) : Int) - 1 -
      (x.length * x.length : Int) = -1 := by
    simp [Nat.cast_mul]
    try ring
  rw [← hend]
  exact h

theorem clean_output (x : List Bool) (hn2 : 2 ≤ x.length) :
    Function.update (doneTape x) (-1) 2 =
      inputTape machine (squarePayload x) := by
  funext z
  by_cases hl : z = -1
  · subst z; simp [inputTape]
  · rw [Function.update_of_ne hl]
    by_cases hn : z < 0
    · simp only [doneTape, hl, hn, if_false, if_true]
      rw [inputTape_neg machine (squarePayload x) z hn, machine_blank]
    · have hz : z = (z.toNat : Int) :=
        (Int.toNat_of_nonneg (le_of_not_gt hn)).symm
      rw [hz, doneTape_ofNat]
      set p := z.toNat
      by_cases hp : p < (squarePayload x).length
      · rw [inputTape_ofNat machine (squarePayload x) p hp,
          squarePayload_get x p hp]
        by_cases hpre : p < x.length * x.length
        · simp [hpre, machine_one, machine_zero]
        · simp only [hpre, ite_false]
          by_cases he : p = x.length * x.length
          · simp [he, machine_one, machine_zero]
          · simp only [he, ite_false]
            have happ : p < x.length * x.length + x.length + 1 := by
              simpa [squarePayload_length] using hp
            simp [happ, writeBit]
            cases bitAt x (p - x.length * x.length - 1) <;> rfl
      · have hge : ((squarePayload x).length : Int) ≤ (p : Int) := by omega
        rw [inputTape_ge machine (squarePayload x) p hge, machine_blank]
        have hpre : ¬ p < x.length * x.length := by
          simp [squarePayload_length] at hp; omega
        have he : p ≠ x.length * x.length := by
          simp [squarePayload_length] at hp; omega
        have happ : ¬ p < x.length * x.length + x.length + 1 := by
          simp [squarePayload_length] at hp; omega
        simp only [hpre, he, happ, ite_false]

theorem cleanup_finish (x : List Bool) (hn2 : 2 ≤ x.length) :
    step machine 0 (tapeConfig 8 (-1) (doneTape x)) =
      some (finalConfig x) := by
  have hread : doneTape x (-1) = 18 := rfl
  rw [step_write 8 0 (-1) (doneTape x) 2 .right
    (by rw [hread]; simp [machine]), clean_output x hn2]
  rfl

theorem drain_run (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (sepFuel x.length))
      (tapeConfig 6 0 (copyTape x x.length)) =
      some (finalConfig x) := by
  have hle : x.length + 1 ≤ x.length * x.length := by
    have := n_lt_nn x.length hn2
    omega
  have ht : sepFuel x.length =
      x.length + 1 + (x.length * x.length - x.length - 1) + 1 +
        x.length * x.length + 1 := by
    unfold sepFuel
    have hsub : x.length * x.length - x.length - 1 =
        x.length * x.length - (x.length + 1) := (Nat.sub_add_eq _ _ _).symm
    rw [hsub]
    zify
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    ring
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, run_append,
    run_append, run_append, run_append, run_append, drain_skip x,
    Option.bind_some, run_ticks_one, drain_five x, Option.bind_some,
    drain_zeros x hn2, Option.bind_some, run_ticks_one, drain_sep x hn2,
    Option.bind_some, cleanup_return x hn2, Option.bind_some, run_ticks_one]
  exact cleanup_finish x hn2

theorem copyAllFuel_eq (n : Nat) : copyFuel n n = copyAllFuel n := by
  unfold copyFuel copyAllFuel; ring

theorem ge2Fuel_eq (n : Nat) (hn : 2 ≤ n) :
    setupFuel n + squareFuel n n + finishFuel n + copyAllFuel n + sepFuel n =
      n ^ 4 + n ^ 3 + 9 * n ^ 2 + 7 * n + 10 := by
  unfold setupFuel squareFuel finishFuel copyAllFuel sepFuel
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn
  zify
  simp_rw [nat_pred_cast n hn1]
  ring

theorem run_ge2 (x : List Bool) (hn2 : 2 ≤ x.length) :
    run machine (ticks (x.length ^ 4 + x.length ^ 3 + 9 * x.length ^ 2 +
        7 * x.length + 10)) (initial machine x) =
      some (finalConfig x) := by
  have ht := ge2Fuel_eq x.length hn2
  have hcopy : copyFuel x.length x.length = copyAllFuel x.length :=
    copyAllFuel_eq _
  rw [← ht, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, setup_ge2 x hn2, Option.bind_some,
    square_run x x.length hn2 le_rfl, Option.bind_some, finish_run x hn2,
    Option.bind_some]
  have hstart : tapeConfig 6 0 (largeTape x) =
      tapeConfig 6 0 (copyTape x 0) := by rw [copyTape_zero_eq]
  rw [hstart, ← hcopy, copy_run x x.length hn2 le_rfl, Option.bind_some]
  exact drain_run x hn2

theorem squarePayload_computes :
    StandardBitTime.ComputesWithin machine squarePayload timeBound := by
  intro x
  cases x with
  | nil =>
    refine ⟨6, finalConfig [], ?_, run_empty, rfl, rfl, rfl⟩
    simp [timeBound]
  | cons b xs =>
    cases xs with
    | nil =>
      refine ⟨16, finalConfig [b], ?_, run_singleton b, rfl, rfl, rfl⟩
      simp [timeBound]
    | cons c ys =>
      have hn2 : 2 ≤ (b :: c :: ys).length := by simp
      refine ⟨(b :: c :: ys).length ^ 4 + (b :: c :: ys).length ^ 3 +
          9 * (b :: c :: ys).length ^ 2 + 7 * (b :: c :: ys).length + 10,
        finalConfig (b :: c :: ys), le_timeBound (b :: c :: ys).length,
        run_ge2 (b :: c :: ys) hn2, rfl, rfl, rfl⟩

theorem squarePayload_polyBitTime : StandardBitTime.PolyBitTime squarePayload := by
  refine ⟨27, 19, machine, Polynomial.C 1000 * (Polynomial.X + 1) ^ 6, ?_⟩
  have hp : (fun n => (Polynomial.C 1000 * (Polynomial.X + 1) ^ 6).eval n) =
      timeBound := by
    funext n
    simp [timeBound, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
  rw [hp]
  exact squarePayload_computes

theorem squarePayload_exact :
    StandardBitTime.ComputesWithin machine squarePayload timeBound ∧
    (∀ x, StandardNondeterministicMachine.RunsAtMost machine x
      (timeBound x.length)) ∧
    StandardBitTime.PolyBitTime squarePayload := by
  refine ⟨squarePayload_computes, ?_, squarePayload_polyBitTime⟩
  intro x
  exact (ComputesWithin.actual_bounds machine squarePayload timeBound
    squarePayload_computes x).1

end PakFixedPolyomino.StandardBitSquarePayload
