import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.ULogBytecode

/-! A fixed 47-state, seven-symbol ordinary tape machine preserves every
raw input and appends exactly 36 times its length in zero bits. Each source
cell triggers 36 literal writes. Whole-tape cleanup and the physical quadratic
transition count are proved, including empty/allzero/highzero inputs. -/

namespace PakFixedPolyomino.StandardBitAppendThirtySixLengthZeros

open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

def markBit : Bool → Fin 7
  | false => 3
  | true => 6

def writeBit : Bool → Fin 7
  | false => 0
  | true => 1

def seekState : Bool → Fin 47
  | false => 7
  | true => 7

def bitAt (x : List Bool) (i : Nat) : Bool :=
  if h : i < x.length then x[i] else false

@[simp] theorem bitAt_lt (x : List Bool) (i : Nat) (h : i < x.length) :
    bitAt x i = x[i] := by simp [bitAt, h]

def machine : DeterministicMachine 47 7 where
  rule := fun q a _ =>
    if q = 2 then some { target := 3, write := a, move := .left }
    else if q = 3 then some { target := 4, write := 4, move := .right }
    else if q = 4 then
      if a = 2 then some { target := 5, write := 5, move := .left }
      else if a = 0 then some { target := 4, write := 3, move := .right }
      else if a = 1 then some { target := 4, write := 6, move := .right }
      else none
    else if q = 5 then
      if a = 4 then some { target := 6, write := 4, move := .right }
      else some { target := 5, write := a, move := .left }
    else if q = 6 then
      if a = 0 ∨ a = 1 then some { target := 6, write := a, move := .right }
      else if a = 3 then some { target := 7, write := 0, move := .right }
      else if a = 6 then some { target := 7, write := 1, move := .right }
      else if a = 5 then some { target := 10, write := 0, move := .right }
      else none
    else if q = 7 then
      if a = 2 then some { target := 12, write := 0, move := .right }
      else some { target := 7, write := a, move := .right }
    else if 12 ≤ q.val then
      if q = 46 then some { target := 9, write := 0, move := .left }
      else some ⟨0, ⟨(q.val + 1) % 47, Nat.mod_lt _ (by decide)⟩, .right⟩
    else if q = 10 then
      if a = 2 then some { target := 11, write := 2, move := .left }
      else some { target := 10, write := a, move := .right }
    else if q = 11 then some { target := 8, write := 2, move := .left }
    else if q = 9 then
      if a = 4 then some { target := 6, write := 4, move := .right }
      else some { target := 9, write := a, move := .left }
    else if q = 8 then
      if a = 4 then some { target := 0, write := 2, move := .right }
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

def output (x : List Bool) : List Bool := x ++ List.replicate (36 * x.length) false

@[simp] theorem output_length (x : List Bool) : (output x).length = 37 * x.length := by
  simp [output]; omega

def seedTape (x : List Bool) (k : Nat) (z : Int) : Fin 7 :=
  if z = -1 then 4
  else if 0 ≤ z ∧ z < (k : Int) then markBit (bitAt x z.toNat)
  else inputTape machine x z

def seedConfig (x : List Bool) (k : Nat) : Configuration 47 7 :=
  ⟨4, k, seedTape x k⟩

def epochTape (x : List Bool) (k : Nat) (z : Int) : Fin 7 :=
  if z = -1 then 4 else if z < 0 then 2 else
    if z.toNat < k then writeBit (bitAt x z.toNat)
    else if z.toNat < x.length then markBit (bitAt x z.toNat)
    else if z.toNat = x.length then 5
    else if z.toNat < x.length + 36 * k + 1 then 0
    else 2

def epochConfig (x : List Bool) (k : Nat) : Configuration 47 7 :=
  ⟨6, 0, epochTape x k⟩

def takenTape (x : List Bool) (k : Nat) : Int → Fin 7 :=
  Function.update (epochTape x k) (k : Int) (writeBit (bitAt x k))

def cleanTape (x : List Bool) : Int → Fin 7 :=
  Function.update (epochTape x x.length) (x.length : Int) 0

theorem seedTape_head (x : List Bool) (k : Nat) :
    seedTape x k (k : Int) = inputTape machine x (k : Int) := by
  have hn : (k : Int) ≠ -1 := by omega
  simp [seedTape, hn]

theorem seedTape_write (x : List Bool) (k : Nat) (hk : k < x.length) :
    Function.update (seedTape x k) (k : Int) (markBit x[k]) =
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

theorem epochTape_neg1 (x : List Bool) (k : Nat) : epochTape x k (-1) = 4 := by
  simp [epochTape]

theorem epochTape_nat_ne_left (x : List Bool) (k p : Nat) :
    epochTape x k (p : Int) ≠ 4 := by
  have hp : (p : Int) ≠ -1 := by omega
  simp only [epochTape, hp, if_false, Int.toNat_natCast]
  split_ifs <;> first | decide | (cases bitAt x _ <;> decide) | (cases bitAt x _ <;> decide)

theorem epochTape_processed (x : List Bool) (k p : Nat) (hp : p < k) :
    epochTape x k (p : Int) = writeBit (bitAt x p) := by
  have hn : (p : Int) ≠ -1 := by omega
  simp [epochTape, hn, hp]

theorem epochTape_unprocessed (x : List Bool) (k p : Nat)
    (hk : k ≤ p) (hp : p < x.length) :
    epochTape x k (p : Int) = markBit x[p] := by
  have hn : (p : Int) ≠ -1 := by omega
  simp [epochTape, hn, hp, Nat.not_lt.mpr hk, bitAt_lt x p hp]

theorem epochTape_separator (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    epochTape x k (x.length : Int) = 5 := by
  have hn : (x.length : Int) ≠ -1 := by omega
  simp [epochTape, hn, Nat.not_lt.mpr hk]

theorem epochTape_end (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    epochTape x k ((x.length + 36 * k + 1 : Nat) : Int) = 2 := by
  have hn : ((x.length + 36 * k + 1 : Nat) : Int) ≠ -1 := by omega
  have hk' : ¬ x.length + 36 * k + 1 < k := by omega
  have hn' : ¬ x.length + 36 * k + 1 < x.length := by omega
  have he : x.length + 36 * k + 1 ≠ x.length := by omega
  have hp : ¬ ((x.length + 36 * k + 1 : Nat) : Int) < 0 := by omega
  simp only [epochTape, hn, hp, if_false, Int.toNat_natCast, hk', hn', he,
    lt_self_iff_false]

theorem epochTape_appended (x : List Bool) (k p : Nat)
    (hn : x.length < p) (hp : p < x.length + 36 * k + 1) (hk : k ≤ x.length) :
    epochTape x k (p : Int) = 0 := by
  have hl : (p : Int) ≠ -1 := by omega
  simp only [epochTape, hl, if_false, Int.not_lt.mpr (Nat.cast_nonneg p),
    Int.toNat_natCast]
  have hk' : ¬ p < k := by omega
  have hn' : ¬ p < x.length := by omega
  have he : p ≠ x.length := by omega
  simp [hk', hn', he, hp]

def tapeConfig (q : Fin 47) (z : Int) (t : Int → Fin 7) : Configuration 47 7 :=
  ⟨q, z, t⟩

theorem step_write (q q' : Fin 47) (z : Int) (t : Int → Fin 7)
    (a : Fin 7) (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some { write := a, target := q', move := d }) :
    step machine 0 (tapeConfig q z t) =
      some (tapeConfig q' (moveHead d z) (Function.update t z a)) := by
  simp only [step, tapeConfig, hr, Option.map_some, writtenTape]

theorem step_preserve (q q' : Fin 47) (z : Int) (t : Int → Fin 7)
    (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some { write := t z, target := q', move := d }) :
    step machine 0 (tapeConfig q z t) = some (tapeConfig q' (moveHead d z) t) := by
  rw [step_write q q' z t (t z) d hr, Function.update_eq_self]

theorem scan_right (q : Fin 47) (z : Int) (t : Int → Fin 7) (n : Nat)
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

theorem scan_left (q : Fin 47) (z : Int) (t : Int → Fin 7) (n : Nat)
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

theorem seed_zero (x : List Bool) :
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

theorem seed_step (x : List Bool) (k : Nat) (hk : k < x.length) :
    step machine 0 (seedConfig x k) = some (seedConfig x (k + 1)) := by
  have hr : machine.rule 4 (seedTape x k (k : Int)) 0 =
      some { write := markBit x[k], target := 4, move := .right } := by
    rw [seedTape_head, inputTape_ofNat machine x k hk]
    cases hx : x[k] <;> simp [machine, markBit, hx]
  change step machine 0 (tapeConfig 4 k (seedTape x k)) = _
  rw [step_write 4 4 k (seedTape x k) (markBit x[k]) .right hr, seedTape_write x k hk]
  congr 2

theorem seed_scan (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks k) (seedConfig x 0) = some (seedConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add k 1, run_append, ih (by omega), Option.bind_some, run_ticks_one]
    exact seed_step x k (by omega)

theorem seed_separator (x : List Bool) :
    Function.update (seedTape x x.length) (x.length : Int) 5 =
      epochTape x 0 := by
  funext z
  by_cases hz : z = (x.length : Int)
  · subst z
    rw [Function.update_self, epochTape_separator _ _ (by omega)]
  · rw [Function.update_of_ne hz]
    by_cases hl : z = -1
    · subst z; simp [seedTape, epochTape]
    · by_cases hn : z < 0
      · have hc : ¬ (0 ≤ z ∧ z < (x.length : Int)) := by omega
        simp [seedTape, hl, hc, inputTape_neg machine x z hn, epochTape, hn]
      · have hnonneg : 0 ≤ z := by omega
        by_cases hi : z < (x.length : Int)
        · have hi' : z.toNat < x.length := by omega
          have hk : ¬ z.toNat < 0 := by omega
          simp [seedTape, hl, hnonneg, hi, epochTape, hn, hi', hk,
            bitAt_lt x z.toNat hi']
        · have hge : (x.length : Int) ≤ z := by omega
          have hi' : ¬ z.toNat < x.length := by omega
          have he : z.toNat ≠ x.length := by omega
          have hend : ¬ z.toNat < x.length + 0 + 1 := by omega
          simp [seedTape, hl, hi, inputTape_ge machine x z hge,
            epochTape, hn, hi', he, hend]

theorem seed_turn (x : List Bool) :
    step machine 0 (seedConfig x x.length) =
      some (tapeConfig 5 ((x.length : Int) - 1) (epochTape x 0)) := by
  have hread : seedTape x x.length (x.length : Int) = 2 := by
    rw [seedTape_head]; exact inputTape_ge machine x _ (by rfl)
  change step machine 0 (tapeConfig 4 x.length (seedTape x x.length)) = _
  rw [step_write 4 5 x.length (seedTape x x.length) 5 .left (by rw [hread]; rfl),
    seed_separator]
  rfl

theorem seed_return (x : List Bool) :
    run machine (ticks x.length)
      (tapeConfig 5 ((x.length : Int) - 1) (epochTape x 0)) =
      some (tapeConfig 5 (-1) (epochTape x 0)) := by
  have h := scan_left 5 ((x.length : Int) - 1) (epochTape x 0) x.length (by
    intro p hp
    have he : (x.length : Int) - 1 - p = ((x.length - 1 - p : Nat) : Int) := by
      omega
    rw [he]
    have hne := epochTape_nat_ne_left x 0 (x.length - 1 - p)
    simp [machine, hne])
  convert h using 1 <;> congr 2 <;> omega

theorem seed_finish (x : List Bool) :
    step machine 0 (tapeConfig 5 (-1) (epochTape x 0)) =
      some (epochConfig x 0) := by
  rw [step_preserve 5 6 (-1) (epochTape x 0) .right
    (by rw [epochTape_neg1]; rfl)]
  rfl

theorem setup_run (x : List Bool) :
    run machine (ticks (2 * x.length + 4)) (initial machine x) =
      some (epochConfig x 0) := by
  have ht : 2 * x.length + 4 = 2 + x.length + 1 + x.length + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, seed_zero, Option.bind_some,
    seed_scan x x.length (by rfl), Option.bind_some, run_ticks_one,
    seed_turn, Option.bind_some, seed_return, Option.bind_some, run_ticks_one]
  exact seed_finish x

theorem epochTape_nonblank (x : List Bool) (k p : Nat)
    (hk : k ≤ x.length) (hp : p < x.length + 36 * k + 1) :
    epochTape x k (p : Int) ≠ 2 := by
  have hl : (p : Int) ≠ -1 := by omega
  simp only [epochTape, hl, if_false, Int.not_lt.mpr (Nat.cast_nonneg p),
    Int.toNat_natCast]
  split_ifs <;> first | decide | (cases bitAt x _ <;> decide) | (cases bitAt x _ <;> decide) | omega

theorem takenTape_nonblank (x : List Bool) (k p : Nat)
    (hk : k < x.length) (hp : p < x.length + 36 * k + 1) :
    takenTape x k (p : Int) ≠ 2 := by
  by_cases he : p = k
  · subst p; cases hb : bitAt x k <;> simp [takenTape, writeBit, hb]
  · have hz : (p : Int) ≠ (k : Int) := by omega
    simp only [takenTape, Function.update_of_ne hz]
    exact epochTape_nonblank x k p (by omega) hp

theorem takenTape_end (x : List Bool) (k : Nat) (hk : k < x.length) :
    takenTape x k ((x.length + 36 * k + 1 : Nat) : Int) = 2 := by
  have hz : ((x.length + 36 * k + 1 : Nat) : Int) ≠ (k : Int) := by omega
  rw [takenTape, Function.update_of_ne hz, epochTape_end x k (by omega)]

def fillState (j : Nat) : Fin 47 :=
  if j = 0 then 7 else ⟨(j + 11) % 47, Nat.mod_lt _ (by decide)⟩

def blockTape (x : List Bool) (k j : Nat) (z : Int) : Fin 7 :=
  if ((x.length + 36*k + 1 : Nat) : Int) ≤ z ∧
      z < ((x.length + 36*k + 1 + j : Nat) : Int) then 0
  else takenTape x k z

def blockConfig (x : List Bool) (k j : Nat) : Configuration 47 7 :=
  if j = 36 then tapeConfig 9 ((x.length + 36*k + 35 : Nat) : Int) (blockTape x k j)
  else tapeConfig (fillState j) ((x.length + 36*k + 1 + j : Nat) : Int) (blockTape x k j)

theorem fill_rule (j : Fin 36) :
    machine.rule (fillState j.val) 2 0 =
      if j.val + 1 = 36 then some ⟨0,9,.left⟩
      else some ⟨0,fillState (j.val+1),.right⟩ := by
  fin_cases j <;> rfl

theorem blockTape_zero (x : List Bool) (k : Nat) : blockTape x k 0 = takenTape x k := by
  funext z
  have h : ¬ (((x.length+36*k+1 : Nat) : Int) ≤ z ∧
      z < ((x.length+36*k+1+0 : Nat) : Int)) := by omega
  simp [blockTape,h]

theorem blockTape_head (x : List Bool) (k j : Nat) (hk : k < x.length) :
    blockTape x k j ((x.length+36*k+1+j : Nat) : Int) = 2 := by
  have hne : ((x.length+36*k+1+j : Nat) : Int) ≠ (k : Int) := by omega
  have hl : ((x.length+36*k+1+j : Nat) : Int) ≠ -1 := by omega
  have hn : ¬ ((x.length+36*k+1+j : Nat) : Int) < 0 := by omega
  have ha : ¬ x.length+36*k+1+j < k := by omega
  have hb : ¬ x.length+36*k+1+j < x.length := by omega
  have hc : x.length+36*k+1+j ≠ x.length := by omega
  have hd : ¬ x.length+36*k+1+j < x.length+36*k+1 := by omega
  simp only [blockTape,lt_self_iff_false,and_false,if_false,takenTape]
  rw [Function.update_of_ne hne]
  simp only [epochTape,hl,hn,if_false,Int.toNat_natCast,ha,hb,hc,hd]

theorem blockTape_write (x : List Bool) (k j : Nat) :
    Function.update (blockTape x k j) ((x.length+36*k+1+j : Nat) : Int) 0 =
      blockTape x k (j+1) := by
  funext z
  by_cases he : z = ((x.length+36*k+1+j : Nat) : Int)
  · subst z
    have h : (((x.length+36*k+1 : Nat) : Int) ≤
        ((x.length+36*k+1+j : Nat) : Int) ∧
        ((x.length+36*k+1+j : Nat) : Int) <
        ((x.length+36*k+1+(j+1) : Nat) : Int)) := by omega
    simp [blockTape,h]
  · have h : (((x.length+36*k+1 : Nat) : Int) ≤ z ∧
        z < ((x.length+36*k+1+(j+1) : Nat) : Int)) ↔
        (((x.length+36*k+1 : Nat) : Int) ≤ z ∧
        z < ((x.length+36*k+1+j : Nat) : Int)) := by omega
    simp only [Function.update_of_ne he,blockTape,h]

theorem blockTape_finish (x : List Bool) (k : Nat) (hk : k < x.length) :
    blockTape x k 36 = epochTape x (k+1) := by
  funext z
  by_cases hspan : ((x.length+36*k+1 : Nat) : Int) ≤ z ∧
      z < ((x.length+36*k+1+36 : Nat) : Int)
  · rw [blockTape,if_pos hspan]
    have hz : 0 ≤ z := by omega
    have hzi : z = (z.toNat : Int) := (Int.toNat_of_nonneg hz).symm
    rw [hzi]
    exact (epochTape_appended x (k+1) z.toNat (by omega) (by omega) (by omega)).symm
  · rw [blockTape,if_neg hspan]
    by_cases htake : z = (k : Int)
    · subst z
      rw [takenTape,Function.update_self]
      exact (epochTape_processed x (k+1) k (by omega)).symm
    · rw [takenTape,Function.update_of_ne htake]
      unfold epochTape
      by_cases hleft : z = -1
      · simp [hleft]
      · by_cases hneg : z < 0
        · simp [hleft,hneg]
        · have hp : (z.toNat < k) ↔ z.toNat < k+1 := by omega
          have he : (z.toNat < x.length+36*k+1) ↔
              z.toNat < x.length+36*(k+1)+1 := by omega
          simp only [hleft,hneg,if_false,hp,he]

theorem block_step (x : List Bool) (k j : Nat) (hk : k < x.length) (hj : j < 36) :
    step machine 0 (blockConfig x k j) = some (blockConfig x k (j+1)) := by
  have hjne : j ≠ 36 := by omega
  have hr := fill_rule ⟨j,hj⟩
  simp only [blockConfig,hjne,if_false]
  by_cases hlast : j+1 = 36
  · rw [if_pos hlast] at hr
    rw [step_write (fillState j) 9 _ (blockTape x k j) 0 .left
      (by rw [blockTape_head x k j hk]; exact hr),blockTape_write]
    simp only [hlast,if_pos rfl]
    congr 2
    simp only [moveHead]
    omega
  · rw [if_neg hlast] at hr
    rw [step_write (fillState j) (fillState (j+1)) _ (blockTape x k j) 0 .right
      (by rw [blockTape_head x k j hk]; exact hr),blockTape_write]
    simp only [if_neg hlast]
    congr 2

theorem block_run (x : List Bool) (k j : Nat) (hk : k < x.length) (hj : j ≤ 36) :
    run machine (ticks j) (blockConfig x k 0) = some (blockConfig x k j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ticks_add j 1,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    exact block_step x k j hk (by omega)

theorem epoch_skip (x : List Bool) (k : Nat) :
    run machine (ticks k) (epochConfig x k) =
      some (tapeConfig 6 k (epochTape x k)) := by
  have h := scan_right 6 0 (epochTape x k) k (by
    intro p hp
    rw [Int.zero_add, epochTape_processed x k p hp]
    cases bitAt x p <;> rfl)
  simpa [epochConfig, tapeConfig] using h

theorem epoch_take (x : List Bool) (k : Nat) (hk : k < x.length) :
    step machine 0 (tapeConfig 6 k (epochTape x k)) =
      some (tapeConfig (seekState x[k]) ((k : Int) + 1) (takenTape x k)) := by
  cases hx : x[k]
  · simpa [takenTape, bitAt_lt x k hk, hx, writeBit, seekState, moveHead] using
      step_write 6 7 k (epochTape x k) 0 .right
        (by rw [epochTape_unprocessed x k k le_rfl hk, hx]; rfl)
  · simpa [takenTape, bitAt_lt x k hk, hx, writeBit, seekState, moveHead] using
      step_write 6 7 k (epochTape x k) 1 .right
        (by rw [epochTape_unprocessed x k k le_rfl hk, hx]; rfl)

theorem seek_right_rule (q : Fin 47) (a : Fin 7)
    (h : q = 7 ∨ q = 10) (ha : a ≠ 2) :
    machine.rule q a 0 = some { write := a, target := q, move := .right } := by
  rcases h with rfl | rfl <;> simp [machine, ha]

theorem seekState_or (b : Bool) : seekState b = 7 ∨ seekState b = 10 := by
  cases b <;> simp [seekState]

theorem seek_append (x : List Bool) (k : Nat) (hk : k < x.length) :
    run machine (ticks (x.length + 35*k))
      (tapeConfig (seekState x[k]) ((k : Int) + 1) (takenTape x k)) =
      some (tapeConfig (seekState x[k])
        ((x.length + 36 * k + 1 : Nat) : Int) (takenTape x k)) := by
  have hq := seekState_or x[k]
  have h := scan_right (seekState x[k]) ((k : Int) + 1) (takenTape x k)
    (x.length + 35*k) (by
      intro p hp
      have he : (k : Int) + 1 + p = ((k + 1 + p : Nat) : Int) := by omega
      rw [he]
      exact seek_right_rule _ _ hq
        (takenTape_nonblank x k (k + 1 + p) hk (by omega)))
  convert h using 1 <;> congr 2 <;> omega

theorem seek_blank_rule (b : Bool) :
    machine.rule (seekState b) 2 0 =
      some { write := 0, target := 12, move := .right } := by
  cases b <;> simp [machine, seekState, writeBit]

theorem append_turn (x : List Bool) (k : Nat) (hk : k < x.length) :
    run machine (ticks 36) (tapeConfig (seekState x[k])
      ((x.length+36*k+1 : Nat) : Int) (takenTape x k)) =
      some (tapeConfig 9 ((x.length+36*k+35 : Nat) : Int) (epochTape x (k+1))) := by
  have h := block_run x k 36 hk le_rfl
  cases hx : x[k] <;>
    simpa [blockConfig,blockTape_zero,fillState,seekState,hx,blockTape_finish x k hk] using h

theorem append_return (x : List Bool) (k : Nat) :
    run machine (ticks (x.length+36*(k+1)))
      (tapeConfig 9 ((x.length+36*k+35 : Nat) : Int) (epochTape x (k+1))) =
      some (tapeConfig 9 (-1) (epochTape x (k+1))) := by
  have h := scan_left 9 ((x.length+36*k+35 : Nat) : Int) (epochTape x (k+1))
    (x.length+36*(k+1)) (by
      intro p hp
      have he : ((x.length+36*k+35 : Nat) : Int)-p =
          ((x.length+36*k+35-p : Nat) : Int) := by omega
      rw [he]
      have hne := epochTape_nat_ne_left x (k+1) (x.length+36*k+35-p)
      simp [machine,hne])
  convert h using 1 <;> congr 2 <;> omega

theorem append_finish (x : List Bool) (k : Nat) :
    step machine 0 (tapeConfig 9 (-1) (epochTape x k)) =
      some (epochConfig x k) := by
  rw [step_preserve 9 6 (-1) (epochTape x k) .right
    (by rw [epochTape_neg1]; rfl)]
  rfl

theorem epoch_cycle (x : List Bool) (k : Nat) (hk : k < x.length) :
    run machine (ticks (2 * x.length + 72 * k + 74)) (epochConfig x k) =
      some (epochConfig x (k + 1)) := by
  have ht : 2 * x.length + 72 * k + 74 =
      k + 1 + (x.length+35*k) + 36 + (x.length+36*(k+1)) + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add,
    run_append, run_append, run_append, run_append, run_append,
    epoch_skip, Option.bind_some, run_ticks_one, epoch_take x k hk,
    Option.bind_some, seek_append x k hk, Option.bind_some,
    append_turn x k hk, Option.bind_some, append_return, Option.bind_some,
    run_ticks_one]
  exact append_finish x (k + 1)

def copyFuel (n k : Nat) : Nat := 2 * n * k + 36 * k * k + 38 * k

theorem copy_run (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks (copyFuel x.length k)) (epochConfig x 0) =
      some (epochConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ht : copyFuel x.length (k + 1) =
        copyFuel x.length k + (2 * x.length + 72 * k + 74) := by
      unfold copyFuel; ring
    rw [ht, ticks_add, run_append, ih (by omega), Option.bind_some]
    exact epoch_cycle x k (by omega)


def trimTape (x : List Bool) : Int → Fin 7 :=
  Function.update (cleanTape x) ((37 * x.length : Nat) : Int) 2

theorem cleanTape_nat_ne_left (x : List Bool) (p : Nat) :
    cleanTape x (p : Int) ≠ 4 := by
  by_cases he : p = x.length
  · subst p; simp [cleanTape]
  · have hz : (p : Int) ≠ (x.length : Int) := by omega
    rw [cleanTape, Function.update_of_ne hz]
    exact epochTape_nat_ne_left x x.length p

theorem cleanTape_nonblank (x : List Bool) (p : Nat) (hp : p < 37 * x.length + 1) :
    cleanTape x (p : Int) ≠ 2 := by
  by_cases he : p = x.length
  · subst p; simp [cleanTape]
  · have hz : (p : Int) ≠ (x.length : Int) := by omega
    rw [cleanTape, Function.update_of_ne hz]
    exact epochTape_nonblank x x.length p le_rfl (by omega)

theorem cleanTape_end (x : List Bool) : cleanTape x ((37 * x.length + 1 : Nat) : Int) = 2 := by
  have hz : ((37 * x.length + 1 : Nat) : Int) ≠ (x.length : Int) := by omega
  rw [cleanTape, Function.update_of_ne hz]
  convert epochTape_end x x.length le_rfl using 1 <;> congr 2 <;> omega

theorem trimTape_nat_ne_left (x : List Bool) (p : Nat) :
    trimTape x (p : Int) ≠ 4 := by
  by_cases he : p = 37 * x.length
  · subst p; simp [trimTape]
  · have hz : (p : Int) ≠ ((37 * x.length : Nat) : Int) := by omega
    rw [trimTape, Function.update_of_ne hz]
    exact cleanTape_nat_ne_left x p

theorem trimTape_neg1 (x : List Bool) : trimTape x (-1) = 4 := by
  have hz : (-1 : Int) ≠ ((37 * x.length : Nat) : Int) := by omega
  have hn : (-1 : Int) ≠ (x.length : Int) := by omega
  rw [trimTape, Function.update_of_ne hz, cleanTape, Function.update_of_ne hn, epochTape_neg1]

theorem cleanup_turn (x : List Bool) :
    step machine 0 (tapeConfig 6 x.length (epochTape x x.length)) =
      some (tapeConfig 10 ((x.length : Int) + 1) (cleanTape x)) := by
  exact step_write 6 10 x.length (epochTape x x.length) 0 .right
    (by rw [epochTape_separator x x.length le_rfl]; rfl)

theorem cleanup_seek (x : List Bool) :
    run machine (ticks (36*x.length))
      (tapeConfig 10 ((x.length : Int) + 1) (cleanTape x)) =
      some (tapeConfig 10 ((37 * x.length + 1 : Nat) : Int) (cleanTape x)) := by
  have h := scan_right 10 ((x.length : Int) + 1) (cleanTape x) (36*x.length) (by
    intro p hp
    have he : (x.length : Int) + 1 + p = ((x.length + 1 + p : Nat) : Int) := by omega
    have hne : cleanTape x ((x.length : Int) + 1 + p) ≠ 2 := by
      rw [he]
      exact cleanTape_nonblank x (x.length + 1 + p) (by omega)
    simp [machine, hne])
  convert h using 1 <;> congr 2 <;> omega

theorem cleanup_back (x : List Bool) :
    step machine 0 (tapeConfig 10 ((37 * x.length + 1 : Nat) : Int) (cleanTape x)) =
      some (tapeConfig 11 ((37 * x.length : Nat) : Int) (cleanTape x)) := by
  rw [step_preserve 10 11 _ (cleanTape x) .left (by rw [cleanTape_end]; rfl)]
  congr 2
  simp [moveHead]

theorem cleanup_delete (x : List Bool) :
    step machine 0 (tapeConfig 11 ((37 * x.length : Nat) : Int) (cleanTape x)) =
      some (tapeConfig 8 (((37 * x.length : Nat) : Int) - 1) (trimTape x)) := by
  exact step_write 11 8 _ (cleanTape x) 2 .left (by rfl)

theorem cleanup_return (x : List Bool) :
    run machine (ticks (37 * x.length))
      (tapeConfig 8 (((37 * x.length : Nat) : Int) - 1) (trimTape x)) =
      some (tapeConfig 8 (-1) (trimTape x)) := by
  have h := scan_left 8 (((37 * x.length : Nat) : Int) - 1) (trimTape x) (37 * x.length) (by
    intro p hp
    have he : ((37 * x.length : Nat) : Int) - 1 - p = ((37 * x.length - 1 - p : Nat) : Int) := by omega
    rw [he]
    have hne := trimTape_nat_ne_left x (37 * x.length - 1 - p)
    simp [machine, hne])
  convert h using 1 <;> congr 2 <;> omega

theorem output_get (x : List Bool) (p : Nat) (hp : p < (output x).length) :
    (output x)[p] = if h : p < x.length then x[p] else false := by
  by_cases hl : p < x.length
  · simp [output, hl, List.getElem_append_left]
  · have hle : x.length ≤ p := by omega
    simp only [output, List.getElem_append_right hle, dif_neg hl]
    simp

theorem clean_output (x : List Bool) :
    Function.update (trimTape x) (-1) 2 = inputTape machine (output x) := by
  funext z
  by_cases hl : z = -1
  · subst z; simp [inputTape]
  · rw [Function.update_of_ne hl]
    by_cases hn : z < 0
    · have htrim : z ≠ ((37 * x.length : Nat) : Int) := by omega
      have hc : z ≠ (x.length : Int) := by omega
      rw [trimTape, Function.update_of_ne htrim, cleanTape, Function.update_of_ne hc,
        inputTape_neg machine (output x) z hn]
      simp [epochTape, hl, hn]
    · have hnonneg : 0 ≤ z := by omega
      have hcast : (z.toNat : Int) = z := Int.toNat_of_nonneg hnonneg
      let p := z.toNat
      have hz : z = (p : Int) := hcast.symm
      rw [hz]
      by_cases htrim : p = 37 * x.length
      · rw [htrim, trimTape, Function.update_self,
          inputTape_ge machine (output x) _ (by simp)]
        rfl
      · have ht : (p : Int) ≠ ((37 * x.length : Nat) : Int) := by omega
        rw [trimTape, Function.update_of_ne ht]
        by_cases he : p = x.length
        · have hp : x.length < (output x).length := by simp; omega
          rw [he, cleanTape, Function.update_self, inputTape_ofNat machine (output x) _ hp,
            output_get x _ hp]
          simp
        · have hne : (p : Int) ≠ (x.length : Int) := by omega
          rw [cleanTape, Function.update_of_ne hne]
          by_cases hp : p < (output x).length
          · rw [inputTape_ofNat machine (output x) p hp, output_get x p hp]
            by_cases hprefix : p < x.length
            · rw [dif_pos hprefix, epochTape_processed x x.length p hprefix,
                bitAt_lt x p hprefix]
              cases x[p] <;> rfl
            · have happ := epochTape_appended x x.length p (by omega)
                (by simp at hp; omega) le_rfl
              rw [dif_neg hprefix, happ]
              rfl
          · rw [inputTape_ge machine (output x) p (by exact_mod_cast (Nat.le_of_not_gt hp)), machine_blank]
            have hleft : (p : Int) ≠ -1 := by omega
            have hprefix : ¬ p < x.length := by simp at hp; omega
            have hend : ¬ p < x.length + 36*x.length + 1 := by simp at hp; omega
            simp [epochTape, hleft, hprefix, he, hend]

def finalConfig (x : List Bool) : Configuration 47 7 :=
  ⟨0, 0, inputTape machine (output x)⟩

theorem cleanup_finish (x : List Bool) :
    step machine 0 (tapeConfig 8 (-1) (trimTape x)) = some (finalConfig x) := by
  rw [step_write 8 0 (-1) (trimTape x) 2 .right
    (by rw [trimTape_neg1]; rfl), clean_output]
  rfl

theorem cleanup_run (x : List Bool) :
    run machine (ticks (74 * x.length + 4)) (epochConfig x x.length) =
      some (finalConfig x) := by
  have ht : 74 * x.length + 4 = x.length + 1 + 36*x.length + 1 + 1 + 37*x.length + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add,
    run_append, run_append, run_append, run_append, run_append, run_append,
    epoch_skip, Option.bind_some, run_ticks_one, cleanup_turn, Option.bind_some,
    cleanup_seek, Option.bind_some, run_ticks_one, cleanup_back, Option.bind_some,
    run_ticks_one, cleanup_delete, Option.bind_some, cleanup_return, Option.bind_some,
    run_ticks_one]
  exact cleanup_finish x

theorem output_run (x : List Bool) :
    run machine (ticks (38 * x.length * x.length + 114 * x.length + 8))
      (initial machine x) = some (finalConfig x) := by
  have ht : 38 * x.length * x.length + 114 * x.length + 8 =
      (2 * x.length + 4) + copyFuel x.length x.length + (74 * x.length + 4) := by
    unfold copyFuel; ring
  rw [ht, ticks_add, ticks_add, run_append, run_append, setup_run,
    Option.bind_some, copy_run x x.length le_rfl, Option.bind_some, cleanup_run]

theorem output_computes :
    ComputesWithin machine output (fun n => 38 * n * n + 114 * n + 8) := by
  intro x
  exact ⟨_, finalConfig x, le_rfl, output_run x, rfl, rfl, rfl⟩

theorem output_polyBitTime : PolyBitTime output := by
  refine ⟨47, 7, machine, Polynomial.C 38 * Polynomial.X * Polynomial.X +
    Polynomial.C 114 * Polynomial.X + Polynomial.C 8, ?_⟩
  simpa using output_computes

theorem output_exact :
    (∀ x, run machine (ticks (38 * x.length * x.length + 114 * x.length + 8))
      (initial machine x) = some (finalConfig x)) ∧
    (∀ x, RunsAtMost machine x (38 * x.length * x.length + 114 * x.length + 8)) ∧
    PolyBitTime output := by
  refine ⟨output_run, ?_, output_polyBitTime⟩
  intro x
  exact halting_runsAtMost machine x _ _ (output_run x) rfl

end PakFixedPolyomino.StandardBitAppendThirtySixLengthZeros
