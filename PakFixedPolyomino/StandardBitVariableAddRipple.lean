import PakFixedPolyomino.StandardBitVariableAddRippleInterface
import PakFixedPolyomino.StandardBitMarkedCompaction
import Mathlib.Tactic

/-! Physical ripple phase of the frozen adder: states 8–25, end in 26. -/
namespace PakFixedPolyomino.StandardBitVariableAddRipple

open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape Config)
open StandardBitVariableAdd (machine enc mark D Epos addCarry xor3 maj endedTape
  bitAt update_same nat_ne_neg1 ended_L sep_y work_ge workTape workNat sepTape)
open StandardBitVariableAddRippleInterface
open StandardBitMarkedCompaction (scan_right scan_left preserve_step)
open StandardBitPairProjection (pairBits_marker pairBits_payload pairBits_sep pairBits_y
  toNat_ofNat)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def huntQ (c : Bool) : Fin 64 := if c then 9 else 8
def huntYQ (xb c : Bool) : Fin 64 :=
  if xb then (if c then 13 else 12) else (if c then 11 else 10)
def huntYdoneQ (c : Bool) : Fin 64 := if c then 15 else 14
def writeQ (sb nc : Bool) : Fin 64 :=
  if sb then (if nc then 23 else 22) else (if nc then 21 else 20)
def seekEQ (sb nc : Bool) : Fin 64 :=
  if sb then (if nc then 19 else 18) else (if nc then 17 else 16)
def retQ (nc : Bool) : Fin 64 := if nc then 25 else 24

def carryInto (x y : List Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => maj (x.getD n false) (y.getD n false) (carryInto x y n)

def tapeAt (x y : List Bool) (ix iy : ℕ) (res : List Bool) (z : Int) : Fin 32 :=
  if z = -1 then 3
  else if hz : 0 ≤ z then
    let n := z.toNat
    if n < 2 * x.length then
      if n % 2 = 0 then 2
      else if n / 2 < ix then 8 else mark (x.getD (n / 2) false)
    else if n = 2 * x.length then 4
    else if n < Epos x y then
      if n - (2 * x.length + 1) < iy then 8
      else enc (y.getD (n - (2 * x.length + 1)) false)
    else if n = Epos x y then 5
    else inputTape machine res (z - (Epos x y + 1 : ℕ))
  else 2

def epochTape (x y : List Bool) (k : ℕ) : Int → Fin 32 :=
  tapeAt x y (min k x.length) (min k y.length) ((addCarry x y false).take k)

def epochCfg (x y : List Bool) (k : ℕ) : Configuration 64 32 :=
  ⟨huntQ (carryInto x y k), 0, epochTape x y k⟩

def huntXFuel (x : List Bool) (k : ℕ) : ℕ :=
  if k < x.length then 2 * k + 2 else 2 * x.length + 1

def huntYFuel (x y : List Bool) (k : ℕ) : ℕ :=
  let start := if k < x.length then 2 * k + 2 else 2 * x.length + 1
  let target := if k < y.length then D x + k else Epos x y
  target - start + 1

def seekEFuel (x y : List Bool) (k : ℕ) : ℕ :=
  if k < y.length then Epos x y - (D x + k) else 0

def epochFuel (x y : List Bool) (k : ℕ) : ℕ :=
  huntXFuel x k + huntYFuel x y k + seekEFuel x y k + (k + 1) + (Epos x y + k + 2)

def finishFuel (x y : List Bool) : ℕ := Epos x y + 1

def sumEpochs (x y : List Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumEpochs x y n + epochFuel x y n

def rippleFuel (x y : List Bool) : ℕ :=
  sumEpochs x y (addCarry x y false).length + finishFuel x y

theorem rule_hX_skip (c : Bool) (a : Fin 32) (h : a = 2 ∨ a = 8) :
    machine.rule (huntQ c) a 0 = some ⟨a, huntQ c, .right⟩ := by
  cases c <;> rcases h with h | h <;> simp [huntQ, machine, h]

theorem rule_hX_false (c : Bool) :
    machine.rule (huntQ c) 6 0 =
      some ⟨8, huntYQ false c, .right⟩ := by
  cases c <;> simp [huntQ, huntYQ, machine]

theorem rule_hX_true (c : Bool) :
    machine.rule (huntQ c) 7 0 =
      some ⟨8, huntYQ true c, .right⟩ := by
  cases c <;> simp [huntQ, huntYQ, machine]

theorem rule_hX_sep (c : Bool) :
    machine.rule (huntQ c) 4 0 =
      some ⟨4, huntYdoneQ c, .right⟩ := by
  cases c <;> simp [huntQ, huntYdoneQ, machine]

theorem rule_hY_skip (xb c : Bool) (a : Fin 32)
    (h : a = 2 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 4) :
    machine.rule (huntYQ xb c) a 0 = some ⟨a, huntYQ xb c, .right⟩ := by
  cases xb <;> cases c <;> rcases h with h | h | h | h | h <;>
    simp [huntYQ, machine, h]

theorem rule_hY_false (xb c : Bool) :
    machine.rule (huntYQ xb c) 0 0 =
      some ⟨8, seekEQ (xor3 xb false c) (maj xb false c), .right⟩ := by
  cases xb <;> cases c <;> simp [huntYQ, seekEQ, xor3, maj, machine]

theorem rule_hY_true (xb c : Bool) :
    machine.rule (huntYQ xb c) 1 0 =
      some ⟨8, seekEQ (xor3 xb true c) (maj xb true c), .right⟩ := by
  cases xb <;> cases c <;> simp [huntYQ, seekEQ, xor3, maj, machine]

theorem rule_hY_E (xb c : Bool) :
    machine.rule (huntYQ xb c) 5 0 =
      some ⟨5, writeQ (xor3 xb false c) (maj xb false c), .right⟩ := by
  cases xb <;> cases c <;> simp [huntYQ, writeQ, xor3, maj, machine]

theorem rule_hYdone_skip (c : Bool) (a : Fin 32) (h : a = 2 ∨ a = 8) :
    machine.rule (huntYdoneQ c) a 0 = some ⟨a, huntYdoneQ c, .right⟩ := by
  cases c <;> rcases h with h | h <;> simp [huntYdoneQ, machine, h]

theorem rule_hYdone_false (c : Bool) :
    machine.rule (huntYdoneQ c) 0 0 =
      some ⟨8, seekEQ (xor3 false false c) (maj false false c), .right⟩ := by
  cases c <;> simp [huntYdoneQ, seekEQ, xor3, maj, machine]

theorem rule_hYdone_true (c : Bool) :
    machine.rule (huntYdoneQ c) 1 0 =
      some ⟨8, seekEQ (xor3 false true c) (maj false true c), .right⟩ := by
  cases c <;> simp [huntYdoneQ, seekEQ, xor3, maj, machine]

theorem rule_hYdone_E0 :
    machine.rule (huntYdoneQ false) 5 0 = some ⟨5, 26, .stay⟩ := by
  simp [huntYdoneQ, machine]

theorem rule_hYdone_E1 :
    machine.rule (huntYdoneQ true) 5 0 =
      some ⟨5, writeQ true false, .right⟩ := by
  simp [huntYdoneQ, writeQ, machine]

theorem rule_seekE_E (sb nc : Bool) :
    machine.rule (seekEQ sb nc) 5 0 = some ⟨5, writeQ sb nc, .right⟩ := by
  cases sb <;> cases nc <;> simp [seekEQ, writeQ, machine]

theorem rule_seekE_notE (sb nc : Bool) (a : Fin 32) (h : a ≠ 5) :
    machine.rule (seekEQ sb nc) a 0 = some ⟨a, seekEQ sb nc, .right⟩ := by
  cases sb <;> cases nc <;> simp [seekEQ, machine, h]

theorem rule_write_bit (sb nc : Bool) (a : Fin 32) (h : a = 0 ∨ a = 1) :
    machine.rule (writeQ sb nc) a 0 = some ⟨a, writeQ sb nc, .right⟩ := by
  cases sb <;> cases nc <;> rcases h with h | h <;> simp [writeQ, machine, h]

theorem rule_write_blank (sb nc : Bool) :
    machine.rule (writeQ sb nc) 2 0 =
      some ⟨enc sb, retQ nc, .left⟩ := by
  cases sb <;> cases nc <;> simp [writeQ, retQ, enc, machine]

theorem rule_ret_L (nc : Bool) :
    machine.rule (retQ nc) 3 0 = some ⟨3, huntQ nc, .right⟩ := by
  cases nc <;> simp [retQ, huntQ, machine]

theorem rule_ret_notL (nc : Bool) (a : Fin 32) (h : a ≠ 3) :
    machine.rule (retQ nc) a 0 = some ⟨a, retQ nc, .left⟩ := by
  cases nc <;> simp [retQ, machine, h]

set_option simprocs false

theorem Epos_gt_sep (x y : List Bool) : 2 * x.length < Epos x y := by
  simp [Epos, D]; omega

theorem D_eq (x : List Bool) : D x = 2 * x.length + 1 := rfl

theorem Epos_eq_pair (x y : List Bool) : Epos x y = (pairBits x y).length := by
  simp [Epos, D, pairBits_length]

theorem tape_L (x y : List Bool) (ix iy : ℕ) (res : List Bool) :
    tapeAt x y ix iy res (-1) = 3 := by
  simp [tapeAt]

theorem tape_neg (x y : List Bool) (ix iy : ℕ) (res : List Bool) (z : Int)
    (hL : z ≠ -1) (hpos : ¬ 0 ≤ z) :
    tapeAt x y ix iy res z = 2 := by
  unfold tapeAt
  rw [if_neg hL, dif_neg hpos]

theorem tape_nat_ne_L (x y : List Bool) (ix iy : ℕ) (res : List Bool) (i : ℕ) :
    tapeAt x y ix iy res (i : Int) ≠ 3 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i), Int.toNat_natCast]
  by_cases hx : i < 2 * x.length
  · rw [if_pos hx]
    by_cases he : i % 2 = 0
    · rw [if_pos he]; decide
    · rw [if_neg he]
      by_cases hc : i / 2 < ix
      · rw [if_pos hc]; decide
      · rw [if_neg hc]; cases (x.getD (i / 2) false) <;> (simp [mark]; decide)
  · rw [if_neg hx]
    by_cases hs : i = 2 * x.length
    · rw [if_pos hs]; decide
    · rw [if_neg hs]
      by_cases hy : i < Epos x y
      · rw [if_pos hy]
        by_cases hc : i - (2 * x.length + 1) < iy
        · rw [if_pos hc]; decide
        · rw [if_neg hc]; cases (y.getD (i - (2 * x.length + 1)) false) <;> (simp [enc]; decide)
      · rw [if_neg hy]
        by_cases hE : i = Epos x y
        · rw [if_pos hE]; decide
        · rw [if_neg hE]
          unfold inputTape
          split_ifs <;> decide

theorem tape_x_even (x y : List Bool) (ix iy : ℕ) (res : List Bool) (i : ℕ)
    (hi : i < 2 * x.length) (he : i % 2 = 0) :
    tapeAt x y ix iy res (i : Int) = 2 := by
  have hL : (i : Int) ≠ -1 := nat_ne_neg1 i
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg i), Int.toNat_natCast, if_pos hi, if_pos he]

theorem tape_x_odd_cons (x y : List Bool) (ix iy : ℕ) (res : List Bool) (j : ℕ)
    (hj : j < ix) (hjx : j < x.length) :
    tapeAt x y ix iy res ((2 * j + 1 : ℕ) : Int) = 8 := by
  have hL : ((2 * j + 1 : ℕ) : Int) ≠ -1 := nat_ne_neg1 _
  have hi : 2 * j + 1 < 2 * x.length := by omega
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg _), Int.toNat_natCast, if_pos hi,
    if_neg (by omega : ¬ (2 * j + 1) % 2 = 0),
    if_pos (by omega : (2 * j + 1) / 2 < ix)]

theorem tape_x_odd_live (x y : List Bool) (ix iy : ℕ) (res : List Bool) (j : ℕ)
    (hj : ix ≤ j) (hjx : j < x.length) :
    tapeAt x y ix iy res ((2 * j + 1 : ℕ) : Int) = mark (x.getD j false) := by
  have hL : ((2 * j + 1 : ℕ) : Int) ≠ -1 := nat_ne_neg1 _
  have hi : 2 * j + 1 < 2 * x.length := by omega
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg _), Int.toNat_natCast, if_pos hi,
    if_neg (by omega : ¬ (2 * j + 1) % 2 = 0),
    if_neg (by omega : ¬ (2 * j + 1) / 2 < ix)]
  simp [show (2 * j + 1) / 2 = j by omega]

theorem tape_sep (x y : List Bool) (ix iy : ℕ) (res : List Bool) :
    tapeAt x y ix iy res ((2 * x.length : ℕ) : Int) = 4 := by
  have hL : ((2 * x.length : ℕ) : Int) ≠ -1 := nat_ne_neg1 _
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg _), Int.toNat_natCast,
    if_neg (by omega : ¬ 2 * x.length < 2 * x.length), if_pos rfl]

theorem tape_y_cons (x y : List Bool) (ix iy : ℕ) (res : List Bool) (j : ℕ)
    (hj : j < iy) (hjy : j < y.length) :
    tapeAt x y ix iy res ((D x + j : ℕ) : Int) = 8 := by
  have hL : ((D x + j : ℕ) : Int) ≠ -1 := nat_ne_neg1 _
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg _), Int.toNat_natCast,
    if_neg (by simp [D]; omega : ¬ D x + j < 2 * x.length),
    if_neg (by simp [D]; omega : D x + j ≠ 2 * x.length),
    if_pos (by simp [Epos, D]; omega : D x + j < Epos x y),
    if_pos (by simp [D]; omega : D x + j - (2 * x.length + 1) < iy)]

theorem tape_y_live (x y : List Bool) (ix iy : ℕ) (res : List Bool) (j : ℕ)
    (hj : iy ≤ j) (hjy : j < y.length) :
    tapeAt x y ix iy res ((D x + j : ℕ) : Int) = enc (y.getD j false) := by
  have hL : ((D x + j : ℕ) : Int) ≠ -1 := nat_ne_neg1 _
  unfold tapeAt
  rw [if_neg hL, dif_pos (Nat.cast_nonneg _), Int.toNat_natCast,
    if_neg (by simp [D]; omega : ¬ D x + j < 2 * x.length),
    if_neg (by simp [D]; omega : D x + j ≠ 2 * x.length),
    if_pos (by simp [Epos, D]; omega : D x + j < Epos x y),
    if_neg (by simp [D]; omega : ¬ D x + j - (2 * x.length + 1) < iy)]
  simp [D, show D x + j - (2 * x.length + 1) = j by simp [D]]

theorem tape_E (x y : List Bool) (ix iy : ℕ) (res : List Bool) :
    tapeAt x y ix iy res (Epos x y : Int) = 5 := by
  have hsep := Epos_gt_sep x y
  unfold tapeAt
  simp [show (Epos x y : Int) ≠ -1 by omega,
    show (0 : Int) ≤ (Epos x y : Int) by omega, Int.toNat_natCast,
    show ¬ Epos x y < 2 * x.length by omega,
    show Epos x y ≠ 2 * x.length by omega,
    show ¬ Epos x y < Epos x y by omega]

theorem tape_res (x y : List Bool) (ix iy : ℕ) (res : List Bool) (i : ℕ) :
    tapeAt x y ix iy res ((Epos x y + 1 + i : ℕ) : Int) =
      inputTape machine res (i : Int) := by
  have hsep := Epos_gt_sep x y
  have hz : ((Epos x y + 1 + i : ℕ) : Int) - ((Epos x y + 1 : ℕ) : Int) = (i : Int) := by
    omega
  unfold tapeAt
  simp only [if_neg (show ((Epos x y + 1 + i : ℕ) : Int) ≠ -1 by omega),
    dif_pos (show (0 : Int) ≤ ((Epos x y + 1 + i : ℕ) : Int) by omega),
    Int.toNat_natCast,
    if_neg (show ¬ Epos x y + 1 + i < 2 * x.length by omega),
    if_neg (show Epos x y + 1 + i ≠ 2 * x.length by omega),
    if_neg (show ¬ Epos x y + 1 + i < Epos x y by omega),
    if_neg (show Epos x y + 1 + i ≠ Epos x y by omega), hz]

theorem addCarry_len_ge (x y : List Bool) (c : Bool) :
    max x.length y.length ≤ (addCarry x y c).length := by
  induction x generalizing y c with
  | nil =>
      induction y generalizing c with
      | nil => cases c <;> simp [addCarry]
      | cons b y ih =>
          simp [addCarry]; have := ih (maj false b c); omega
  | cons a x ih =>
      cases y with
      | nil => simp [addCarry]; have := ih [] (maj a false c); omega
      | cons b y => simp [addCarry]; have := ih y (maj a b c); omega

theorem addCarry_len_le (x y : List Bool) (c : Bool) :
    (addCarry x y c).length ≤ max x.length y.length + 1 := by
  induction x generalizing y c with
  | nil =>
      induction y generalizing c with
      | nil => cases c <;> simp [addCarry]
      | cons b y ih =>
          simp [addCarry, List.length_cons]
          have h := ih (maj false b c)
          have hm0 : max (0 : ℕ) y.length = y.length := max_eq_right (Nat.zero_le _)
          have hm1 : max (0 : ℕ) (y.length + 1) = y.length + 1 :=
            max_eq_right (Nat.zero_le _)
          have h' : (addCarry [] y (maj false b c)).length ≤ y.length + 1 := by
            simpa [hm0] using h
          simpa [hm1] using Nat.succ_le_succ h'
  | cons a x ih =>
      cases y with
      | nil =>
          simp [addCarry, List.length_cons]
          have h := ih [] (maj a false c)
          have hm0 : max x.length (0 : ℕ) = x.length := max_eq_left (Nat.zero_le _)
          have hm1 : max (x.length + 1) (0 : ℕ) = x.length + 1 :=
            max_eq_left (Nat.zero_le _)
          have h' : (addCarry x [] (maj a false c)).length ≤ x.length + 1 := by
            simpa [hm0] using h
          simpa [hm1] using Nat.succ_le_succ h'
      | cons b y =>
          simp [addCarry, List.length_cons]
          have h := ih y (maj a b c)
          have hm : max (x.length + 1) (y.length + 1) = max x.length y.length + 1 := by
            cases Nat.le_total x.length y.length with
            | inl hxy =>
                rw [max_eq_right hxy, max_eq_right (Nat.succ_le_succ hxy)]
            | inr hyx =>
                rw [max_eq_left hyx, max_eq_left (Nat.succ_le_succ hyx)]
          simpa [hm] using Nat.succ_le_succ h

def carryFrom (x y : List Bool) (c : Bool) : ℕ → Bool
  | 0 => c
  | n + 1 => maj (x.getD n false) (y.getD n false) (carryFrom x y c n)

theorem carryInto_from (x y : List Bool) (n : ℕ) :
    carryInto x y n = carryFrom x y false n := by
  induction n with
  | zero => simp [carryInto, carryFrom]
  | succ n ih => simp [carryInto, carryFrom, ih]

theorem carryFrom_tail_y (y : List Bool) (b c : Bool) (k : ℕ) :
    carryFrom [] (b :: y) c (k + 1) = carryFrom [] y (maj false b c) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc carryFrom [] (b :: y) c (k + 1 + 1)
          = maj false ((b :: y).getD (k + 1) false)
              (carryFrom [] (b :: y) c (k + 1)) := rfl
        _ = maj false ((b :: y).getD (k + 1) false)
              (carryFrom [] y (maj false b c) k) := by rw [ih]
        _ = maj false (y.getD k false)
              (carryFrom [] y (maj false b c) k) := by simp [List.getD]
        _ = carryFrom [] y (maj false b c) (k + 1) := rfl

theorem carryFrom_tail_x (x : List Bool) (a c : Bool) (k : ℕ) :
    carryFrom (a :: x) [] c (k + 1) = carryFrom x [] (maj a false c) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc carryFrom (a :: x) [] c (k + 1 + 1)
          = maj ((a :: x).getD (k + 1) false) false
              (carryFrom (a :: x) [] c (k + 1)) := by simp [carryFrom, List.getD]
        _ = maj ((a :: x).getD (k + 1) false) false
              (carryFrom x [] (maj a false c) k) := by rw [ih]
        _ = maj (x.getD k false) false
              (carryFrom x [] (maj a false c) k) := by simp [List.getD]
        _ = carryFrom x [] (maj a false c) (k + 1) := rfl

theorem carryFrom_tail (x y : List Bool) (a b c : Bool) (k : ℕ) :
    carryFrom (a :: x) (b :: y) c (k + 1) = carryFrom x y (maj a b c) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc carryFrom (a :: x) (b :: y) c (k + 1 + 1)
          = maj ((a :: x).getD (k + 1) false) ((b :: y).getD (k + 1) false)
              (carryFrom (a :: x) (b :: y) c (k + 1)) := rfl
        _ = maj ((a :: x).getD (k + 1) false) ((b :: y).getD (k + 1) false)
              (carryFrom x y (maj a b c) k) := by rw [ih]
        _ = maj (x.getD k false) (y.getD k false)
              (carryFrom x y (maj a b c) k) := by simp [List.getD]
        _ = carryFrom x y (maj a b c) (k + 1) := rfl

theorem carryFrom_done (x y : List Bool) (c : Bool) :
    carryFrom x y c (addCarry x y c).length = false := by
  induction x generalizing y c with
  | nil =>
      induction y generalizing c with
      | nil => cases c <;> simp [addCarry, carryFrom, maj]
      | cons b y ih =>
          simp [addCarry]
          simpa [carryFrom_tail_y] using ih (maj false b c)
  | cons a x ih =>
      cases y with
      | nil =>
          simp [addCarry]
          simpa [carryFrom_tail_x] using ih [] (maj a false c)
      | cons b y =>
          simp [addCarry]
          simpa [carryFrom_tail] using ih y (maj a b c)

theorem carryInto_done (x y : List Bool) :
    carryInto x y (addCarry x y false).length = false := by
  simpa [carryInto_from] using carryFrom_done x y false

theorem addCarry_getC (x y : List Bool) (c : Bool) (n : ℕ)
    (hn : n < (addCarry x y c).length) :
    (addCarry x y c)[n] =
      xor3 (x.getD n false) (y.getD n false) (carryFrom x y c n) := by
  induction n generalizing x y c with
  | zero =>
      cases x with
      | nil =>
          cases y with
          | nil =>
              cases c <;> simp [addCarry, xor3, carryFrom, List.getD] at hn ⊢
          | cons b y =>
              simp [addCarry, xor3, carryFrom, List.getD]
      | cons a x =>
          cases y with
          | nil => simp [addCarry, xor3, carryFrom, List.getD]
          | cons b y => simp [addCarry, xor3, carryFrom, List.getD]
  | succ n ih =>
      cases x with
      | nil =>
          cases y with
          | nil => cases c <;> simp [addCarry] at hn
          | cons b y =>
              simp [addCarry] at hn ⊢
              have h := ih [] y (maj false b c) (by omega)
              simpa [List.getD, carryFrom_tail_y] using h
      | cons a x =>
          cases y with
          | nil =>
              simp [addCarry] at hn ⊢
              have h := ih x [] (maj a false c) (by omega)
              simpa [List.getD, carryFrom_tail_x] using h
          | cons b y =>
              simp [addCarry] at hn ⊢
              have h := ih x y (maj a b c) (by omega)
              simpa [List.getD, carryFrom_tail] using h

theorem addCarry_get (x y : List Bool) (n : ℕ)
    (hn : n < (addCarry x y false).length) :
    (addCarry x y false)[n] =
      xor3 (x.getD n false) (y.getD n false) (carryInto x y n) := by
  simpa [carryInto_from] using addCarry_getC x y false n hn

theorem addCarry_suffix (x y : List Bool) (c : Bool) (k : ℕ) :
    (addCarry x y c).drop k = addCarry (x.drop k) (y.drop k) (carryFrom x y c k) := by
  induction k generalizing x y c with
  | zero => simp [carryFrom]
  | succ k ih =>
      cases x with
      | nil =>
          cases y with
          | nil =>
              cases c with
              | false => simp [addCarry, carryFrom, maj]
              | true => simp [addCarry, carryFrom, maj]
          | cons b y =>
              simp [addCarry]
              simpa [carryFrom_tail_y] using ih [] y (maj false b c)
      | cons a x =>
          cases y with
          | nil =>
              simp [addCarry]
              simpa [carryFrom_tail_x] using ih x [] (maj a false c)
          | cons b y =>
              simp [addCarry]
              simpa [carryFrom_tail] using ih x y (maj a b c)

theorem expand_carry (x y : List Bool) (c : Bool) (k : ℕ)
    (hx : x.length ≤ k) (hy : y.length ≤ k)
    (hk : k < (addCarry x y c).length) : carryFrom x y c k = true := by
  have hs := addCarry_suffix x y c k
  have hx' : x.drop k = [] := List.drop_eq_nil_of_le hx
  have hy' : y.drop k = [] := List.drop_eq_nil_of_le hy
  rw [hx', hy'] at hs
  cases hc : carryFrom x y c k with
  | false =>
      have hempty : addCarry [] [] false = [] := by simp [addCarry]
      rw [hc, hempty] at hs
      have hlen := congrArg List.length hs
      simp [List.length_drop] at hlen
      omega
  | true => rfl

theorem getD_lt {α} (l : List α) (n : ℕ) (d : α) (h : n < l.length) :
    l.getD n d = l[n] := by
  simp [List.getD, List.getElem?_eq_getElem, h]

theorem take_succ_get (l : List Bool) (n : ℕ) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  induction l generalizing n with
  | nil => cases h
  | cons a l ih =>
      cases n with
      | zero => simp
      | succ n =>
          have ih' := ih n (by simp at h; omega)
          simpa [List.take] using ih'

theorem ended_E (x y : List Bool) : endedTape x y (Epos x y : Int) = 5 := by
  simp [endedTape]

theorem ended_sep (x y : List Bool) :
    endedTape x y ((2 * x.length : ℕ) : Int) = 4 := by
  unfold endedTape
  have hne : ((2 * x.length : ℕ) : Int) ≠ (Epos x y : Int) := by
    have := Epos_gt_sep x y; omega
  rw [Function.update_of_ne hne]
  simp [sepTape]

theorem ended_x_even (x y : List Bool) (i : ℕ)
    (hi : i < 2 * x.length) (he : i % 2 = 0) :
    endedTape x y (i : Int) = 2 := by
  unfold endedTape sepTape workTape workNat
  have hE : (i : Int) ≠ (Epos x y : Int) := by
    have := Epos_gt_sep x y; omega
  have hS : (i : Int) ≠ ((2 * x.length : ℕ) : Int) := by omega
  rw [Function.update_of_ne hE, Function.update_of_ne hS,
    if_neg (nat_ne_neg1 i), dif_pos (Nat.cast_nonneg i), Int.toNat_natCast,
    if_pos hi, if_neg (by omega : i % 2 ≠ 1)]

theorem ended_x_odd (x y : List Bool) (j : ℕ) (hj : j < x.length) :
    endedTape x y ((2 * j + 1 : ℕ) : Int) = mark x[j] := by
  unfold endedTape sepTape workTape workNat
  have hE : ((2 * j + 1 : ℕ) : Int) ≠ (Epos x y : Int) := by
    have := Epos_gt_sep x y; omega
  have hS : ((2 * j + 1 : ℕ) : Int) ≠ ((2 * x.length : ℕ) : Int) := by omega
  have hlen : 2 * j + 1 < (pairBits x y).length := by
    have := pairBits_length x y; omega
  rw [Function.update_of_ne hE, Function.update_of_ne hS,
    if_neg (nat_ne_neg1 _), dif_pos (Nat.cast_nonneg _), Int.toNat_natCast,
    if_pos (by omega : 2 * j + 1 < 2 * x.length),
    if_pos (by omega : (2 * j + 1) % 2 = 1), dif_pos hlen]
  simp [pairBits_payload x y j hj]

theorem ended_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    endedTape x y ((D x + j : ℕ) : Int) = enc y[j] := by
  unfold endedTape
  have hne : ((D x + j : ℕ) : Int) ≠ (Epos x y : Int) := by
    simp [Epos, D]; omega
  rw [Function.update_of_ne hne]
  exact sep_y x y j hj

theorem ended_gt (x y : List Bool) (n : ℕ) (hn : Epos x y < n) :
    endedTape x y (n : Int) = 2 := by
  unfold endedTape sepTape
  have hsep := Epos_gt_sep x y
  have hE : (n : Int) ≠ (Epos x y : Int) := mod_cast (ne_of_gt hn)
  have hS : (n : Int) ≠ ((2 * x.length : ℕ) : Int) :=
    mod_cast (ne_of_gt (lt_trans hsep hn))
  rw [Function.update_of_ne hE, Function.update_of_ne hS,
    work_ge (pairBits x y) (2 * x.length) n (by omega)]
  exact inputTape_ge machine (pairBits x y) (n : Int)
    (by have := pairBits_length x y; simp [Epos, D] at hn ⊢; omega)

theorem epoch_init (x y : List Bool) : epochTape x y 0 = endedTape x y := by
  funext z
  have hix : min 0 x.length = 0 := Nat.min_eq_left (Nat.zero_le _)
  have hiy : min 0 y.length = 0 := Nat.min_eq_left (Nat.zero_le _)
  unfold epochTape
  rw [hix, hiy, List.take_zero]
  by_cases hL : z = -1
  · subst z; rw [tape_L, ended_L]
  · by_cases hpos : 0 ≤ z
    · have hz : z = (z.toNat : Int) := (Int.toNat_of_nonneg hpos).symm
      rw [hz]
      by_cases hx : z.toNat < 2 * x.length
      · by_cases he : z.toNat % 2 = 0
        · rw [tape_x_even x y 0 0 [] z.toNat hx he, ended_x_even x y z.toNat hx he]
        · have hj : z.toNat / 2 < x.length := by omega
          have hodd : z.toNat = 2 * (z.toNat / 2) + 1 := by omega
          rw [hodd, tape_x_odd_live x y 0 0 [] (z.toNat / 2) (Nat.zero_le _) hj,
            ended_x_odd x y (z.toNat / 2) hj, getD_lt _ _ _ hj]
      · by_cases hs : z.toNat = 2 * x.length
        · rw [hs, tape_sep, ended_sep]
        · by_cases hy : z.toNat < Epos x y
          · have hj : z.toNat - (2 * x.length + 1) < y.length := by
              simp [Epos, D] at hy ⊢; omega
            have hjy : z.toNat = D x + (z.toNat - (2 * x.length + 1)) := by simp [D]; omega
            rw [hjy, tape_y_live x y 0 0 [] (z.toNat - (2 * x.length + 1))
              (Nat.zero_le _) hj, ended_y x y _ hj, getD_lt _ _ _ hj]
          · by_cases hE : z.toNat = Epos x y
            · rw [hE, tape_E, ended_E]
            · have hn : z.toNat = Epos x y + 1 + (z.toNat - (Epos x y + 1)) := by omega
              have hgt' : Epos x y <
                  Epos x y + 1 + (z.toNat - (Epos x y + 1)) := by omega
              rw [hn, ended_gt x y _ hgt',
                tape_res x y 0 0 [] (z.toNat - (Epos x y + 1))]
              exact inputTape_ge machine [] _ (by simp)
    · rw [tape_neg x y 0 0 [] z hL hpos]
      unfold endedTape sepTape workTape
      have hE : z ≠ (Epos x y : Int) := by
        have := nat_ne_neg1 (Epos x y); omega
      have hS : z ≠ ((2 * x.length : ℕ) : Int) := by
        have := nat_ne_neg1 (2 * x.length); omega
      rw [Function.update_of_ne hE, Function.update_of_ne hS, if_neg hL, dif_neg hpos]

theorem epoch_final (x y : List Bool) :
    epochTape x y (addCarry x y false).length =
      resultTape x y (addCarry x y false) := by
  funext z
  have hxle := le_trans (le_max_left x.length y.length) (addCarry_len_ge x y false)
  have hyle := le_trans (le_max_right x.length y.length) (addCarry_len_ge x y false)
  have hix : min (addCarry x y false).length x.length = x.length := Nat.min_eq_right hxle
  have hiy : min (addCarry x y false).length y.length = y.length := Nat.min_eq_right hyle
  have ht : (addCarry x y false).take (addCarry x y false).length = addCarry x y false :=
    List.take_length
  unfold epochTape
  rw [hix, hiy, ht]
  by_cases hL : z = -1
  · subst z; simp [tapeAt, resultTape]
  · by_cases hpos : 0 ≤ z
    · have hz : z = (z.toNat : Int) := (Int.toNat_of_nonneg hpos).symm
      rw [hz]
      unfold tapeAt resultTape
      rw [if_neg (nat_ne_neg1 z.toNat), dif_pos (Nat.cast_nonneg z.toNat),
        if_neg (nat_ne_neg1 z.toNat), if_pos (Nat.cast_nonneg z.toNat),
        Int.toNat_natCast]
      by_cases hx : z.toNat < 2 * x.length
      · rw [if_pos hx, if_pos hx]
        by_cases he : z.toNat % 2 = 0
        · rw [if_pos he, if_pos he]
        · rw [if_neg he, if_neg he, if_pos (by omega : z.toNat / 2 < x.length)]
      · rw [if_neg hx, if_neg hx]
        by_cases hs : z.toNat = 2 * x.length
        · rw [if_pos hs, if_pos hs]
        · rw [if_neg hs, if_neg hs]
          by_cases hy : z.toNat < Epos x y
          · rw [if_pos hy, if_pos hy,
              if_pos (by simp [Epos, D] at hy ⊢; omega)]
          · rw [if_neg hy, if_neg hy]
    · unfold tapeAt resultTape
      rw [if_neg hL, dif_neg hpos, if_neg hL, if_neg hpos]

theorem consume_x (x y : List Bool) (ix iy : ℕ) (res : List Bool)
    (hx : ix < x.length) :
    Function.update (tapeAt x y ix iy res) ((2 * ix + 1 : ℕ) : Int) 8 =
      tapeAt x y (ix + 1) iy res := by
  funext z
  by_cases hz : z = ((2 * ix + 1 : ℕ) : Int)
  · subst z
    rw [Function.update_apply, if_pos rfl, tape_x_odd_cons]
    · omega
    · exact hx
  · rw [Function.update_apply, if_neg hz]
    unfold tapeAt
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        have hne : z.toNat ≠ 2 * ix + 1 := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg Int.ofNat heq))
        by_cases hxlt : z.toNat < 2 * x.length
        · rw [if_pos hxlt, if_pos hxlt]
          by_cases he : z.toNat % 2 = 0
          · rw [if_pos he, if_pos he]
          · rw [if_neg he, if_neg he]
            by_cases hc : z.toNat / 2 < ix
            · rw [if_pos hc, if_pos (Nat.lt_succ_of_lt hc)]
            · rw [if_neg hc]
              have : ¬ z.toNat / 2 < ix + 1 := by
                intro h
                have : z.toNat / 2 = ix := by omega
                have : z.toNat = 2 * ix ∨ z.toNat = 2 * ix + 1 := by omega
                omega
              rw [if_neg this]
        · rw [if_neg hxlt, if_neg hxlt]
      · rw [dif_neg hpos, dif_neg hpos]

theorem consume_y (x y : List Bool) (ix iy : ℕ) (res : List Bool)
    (hy : iy < y.length) :
    Function.update (tapeAt x y ix iy res) ((D x + iy : ℕ) : Int) 8 =
      tapeAt x y ix (iy + 1) res := by
  funext z
  by_cases hz : z = ((D x + iy : ℕ) : Int)
  · subst z
    rw [Function.update_apply, if_pos rfl, tape_y_cons]
    · omega
    · exact hy
  · rw [Function.update_apply, if_neg hz]
    unfold tapeAt
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        have hne : z.toNat ≠ D x + iy := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg Int.ofNat heq))
        by_cases hxlt : z.toNat < 2 * x.length
        · rw [if_pos hxlt, if_pos hxlt]
        · rw [if_neg hxlt, if_neg hxlt]
          by_cases hs : z.toNat = 2 * x.length
          · rw [if_pos hs, if_pos hs]
          · rw [if_neg hs, if_neg hs]
            by_cases hE : z.toNat < Epos x y
            · rw [if_pos hE, if_pos hE]
              by_cases hc : z.toNat - (2 * x.length + 1) < iy
              · rw [if_pos hc, if_pos (by simp [D] at hc ⊢; omega)]
              · rw [if_neg hc]
                have : ¬ z.toNat - (2 * x.length + 1) < iy + 1 := by
                  intro h
                  simp [D] at hne h ⊢
                  omega
                rw [if_neg this]
            · rw [if_neg hE, if_neg hE]
      · rw [dif_neg hpos, dif_neg hpos]

theorem inputTape_snoc (res : List Bool) (b : Bool) :
    Function.update (inputTape machine res) (res.length : Int) (enc b) =
      inputTape machine (res ++ [b]) := by
  funext z
  by_cases hz : z = (res.length : Int)
  · subst z
    rw [Function.update_apply, if_pos rfl]
    have hlen : res.length < (res ++ [b]).length := by simp
    unfold inputTape
    rw [dif_pos (Nat.cast_nonneg _), Int.toNat_natCast, dif_pos hlen]
    have hb : (res ++ [b])[res.length]'hlen = b := by
      have h := List.getElem_append_right (as := res) (bs := [b]) (i := res.length)
        (h₁ := Nat.le_refl _) (h₂ := hlen)
      simpa using h
    simp [enc, hb]
  · rw [Function.update_apply, if_neg hz]
    unfold inputTape
    by_cases hpos : 0 ≤ z
    · rw [dif_pos hpos, dif_pos hpos]
      by_cases hi : z.toNat < res.length
      · have hi' : z.toNat < (res ++ [b]).length := by simp; omega
        rw [dif_pos hi, dif_pos hi']
        simp [List.getElem_append_left hi]
      · have hne : z.toNat ≠ res.length := by
          intro heq
          exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg Int.ofNat heq))
        have hi' : ¬ z.toNat < (res ++ [b]).length := by simp; omega
        rw [dif_neg hi, dif_neg hi']
    · rw [dif_neg hpos, dif_neg hpos]

theorem write_snoc (x y : List Bool) (ix iy : ℕ) (res : List Bool) (b : Bool) :
    Function.update (tapeAt x y ix iy res)
        ((Epos x y + 1 + res.length : ℕ) : Int) (enc b) =
      tapeAt x y ix iy (res ++ [b]) := by
  funext z
  by_cases hz : z = ((Epos x y + 1 + res.length : ℕ) : Int)
  · subst z
    rw [Function.update_apply, if_pos rfl, tape_res]
    have hlen : res.length < (res ++ [b]).length := by simp
    unfold inputTape
    rw [dif_pos (Nat.cast_nonneg _), Int.toNat_natCast, dif_pos hlen]
    have hb : (res ++ [b])[res.length]'hlen = b := by
      have h := List.getElem_append_right (as := res) (bs := [b]) (i := res.length)
        (h₁ := Nat.le_refl _) (h₂ := hlen)
      simpa using h
    simp [enc, hb]
  · rw [Function.update_apply, if_neg hz]
    unfold tapeAt
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        by_cases hxlt : z.toNat < 2 * x.length
        · rw [if_pos hxlt, if_pos hxlt]
        · rw [if_neg hxlt, if_neg hxlt]
          by_cases hs : z.toNat = 2 * x.length
          · rw [if_pos hs, if_pos hs]
          · rw [if_neg hs, if_neg hs]
            by_cases hy : z.toNat < Epos x y
            · rw [if_pos hy, if_pos hy]
            · rw [if_neg hy, if_neg hy]
              by_cases hE : z.toNat = Epos x y
              · rw [if_pos hE, if_pos hE]
              · rw [if_neg hE, if_neg hE]
                have hupd := congrFun (inputTape_snoc res b)
                  (z - (Epos x y + 1 : ℕ))
                have hne : z - (Epos x y + 1 : ℕ) ≠ (res.length : Int) := by
                  intro heq
                  have hz' : z = ((Epos x y + 1 + res.length : ℕ) : Int) := by omega
                  exact hz hz'
                rw [← hupd, Function.update_of_ne hne]
      · rw [dif_neg hpos, dif_neg hpos]

theorem huntXFuel_le (x y : List Bool) (k : ℕ) :
    huntXFuel x k ≤ 2 * (pairBits x y).length + 2 := by
  unfold huntXFuel
  have := pairBits_length x y
  split_ifs <;> omega

theorem huntYFuel_le (x y : List Bool) (k : ℕ) :
    huntYFuel x y k ≤ (pairBits x y).length + 1 := by
  unfold huntYFuel
  simp [D, Epos, pairBits_length]
  split_ifs <;> omega

theorem seekEFuel_le (x y : List Bool) (k : ℕ) :
    seekEFuel x y k ≤ (pairBits x y).length := by
  unfold seekEFuel
  simp [D, Epos, pairBits_length]
  split_ifs <;> omega

theorem epochFuel_le (x y : List Bool) (k : ℕ) :
    epochFuel x y k ≤ 8 * ((pairBits x y).length + k + 2) := by
  have hn : Epos x y = (pairBits x y).length := Epos_eq_pair x y
  have h1 := huntXFuel_le x y k
  have h2 := huntYFuel_le x y k
  have h3 := seekEFuel_le x y k
  unfold epochFuel
  rw [hn]
  omega

theorem sumEpochs_le (x y : List Bool) (m : ℕ) :
    sumEpochs x y m ≤ m * (8 * ((pairBits x y).length + m + 2)) := by
  induction m with
  | zero => simp [sumEpochs]
  | succ m ih =>
      have he : epochFuel x y m ≤ 8 * ((pairBits x y).length + m + 2) :=
        epochFuel_le x y m
      have hstep : 8 * ((pairBits x y).length + m + 2) ≤
          8 * ((pairBits x y).length + (m + 1) + 2) := by omega
      have ih' : sumEpochs x y m ≤
          m * (8 * ((pairBits x y).length + (m + 1) + 2)) :=
        le_trans ih (Nat.mul_le_mul_left m hstep)
      have he' : epochFuel x y m ≤
          8 * ((pairBits x y).length + (m + 1) + 2) := le_trans he hstep
      have hsum : sumEpochs x y m + epochFuel x y m ≤
          m * (8 * ((pairBits x y).length + (m + 1) + 2)) +
            8 * ((pairBits x y).length + (m + 1) + 2) :=
        Nat.add_le_add ih' he'
      have hmul :
          m * (8 * ((pairBits x y).length + (m + 1) + 2)) +
              8 * ((pairBits x y).length + (m + 1) + 2) =
            (m + 1) * (8 * ((pairBits x y).length + (m + 1) + 2)) :=
        (Nat.succ_mul m _).symm
      simpa [sumEpochs] using hsum.trans (le_of_eq hmul)

theorem finishFuel_le (x y : List Bool) :
    finishFuel x y ≤ (pairBits x y).length + 1 := by
  simp [finishFuel, Epos, D, pairBits_length]

theorem rippleFuel_le (x y : List Bool) :
    rippleFuel x y ≤
      512 * ((pairBits x y).length + 1) * ((pairBits x y).length + 1) := by
  unfold rippleFuel
  have hm : (addCarry x y false).length ≤ (pairBits x y).length + 1 := by
    have h1 := addCarry_len_le x y false
    have h2 : max x.length y.length ≤ (pairBits x y).length := by
      simp [pairBits_length]; omega
    exact le_trans h1 (Nat.add_le_add_right h2 1)
  have hs := sumEpochs_le x y (addCarry x y false).length
  have hmul :
      (addCarry x y false).length *
          (8 * ((pairBits x y).length + (addCarry x y false).length + 2)) ≤
        ((pairBits x y).length + 1) * (8 * (2 * (pairBits x y).length + 3)) := by
    have : 8 * ((pairBits x y).length + (addCarry x y false).length + 2) ≤
        8 * (2 * (pairBits x y).length + 3) := by omega
    exact Nat.mul_le_mul hm this
  have hf := finishFuel_le x y
  have hsum : sumEpochs x y (addCarry x y false).length + finishFuel x y ≤
      ((pairBits x y).length + 1) * (8 * (2 * (pairBits x y).length + 3)) +
        ((pairBits x y).length + 1) :=
    Nat.add_le_add (le_trans hs hmul) hf
  have hfac :
      ((pairBits x y).length + 1) * (8 * (2 * (pairBits x y).length + 3)) +
          ((pairBits x y).length + 1) =
        ((pairBits x y).length + 1) *
          (8 * (2 * (pairBits x y).length + 3) + 1) := by
    simp [Nat.mul_add, Nat.mul_one]
  have hlin : 8 * (2 * (pairBits x y).length + 3) + 1 ≤
      32 * ((pairBits x y).length + 1) := by omega
  have h32 :
      ((pairBits x y).length + 1) * (8 * (2 * (pairBits x y).length + 3) + 1) ≤
        32 * ((pairBits x y).length + 1) * ((pairBits x y).length + 1) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left ((pairBits x y).length + 1) hlin
  have h512 :
      32 * ((pairBits x y).length + 1) * ((pairBits x y).length + 1) ≤
        512 * ((pairBits x y).length + 1) * ((pairBits x y).length + 1) :=
    Nat.mul_le_mul_right ((pairBits x y).length + 1)
      (Nat.mul_le_mul_right ((pairBits x y).length + 1) (by decide : 32 ≤ 512))
  exact (hsum.trans (le_of_eq hfac)).trans (h32.trans h512)

theorem step_right (q q' : Fin 64) (t : Int → Fin 32) (h : Int) (w : Fin 32)
    (hr : machine.rule q (t h) 0 = some ⟨w, q', .right⟩) :
    step machine 0 ⟨q, h, t⟩ =
      some ⟨q', h + 1, Function.update t h w⟩ := by
  simp [step, hr, writtenTape, moveHead]

theorem step_left (q q' : Fin 64) (t : Int → Fin 32) (h : Int) (w : Fin 32)
    (hr : machine.rule q (t h) 0 = some ⟨w, q', .left⟩) :
    step machine 0 ⟨q, h, t⟩ =
      some ⟨q', h - 1, Function.update t h w⟩ := by
  simp [step, hr, writtenTape, moveHead]

theorem step_stay (q q' : Fin 64) (t : Int → Fin 32) (h : Int) (w : Fin 32)
    (hr : machine.rule q (t h) 0 = some ⟨w, q', .stay⟩) :
    step machine 0 ⟨q, h, t⟩ =
      some ⟨q', h, Function.update t h w⟩ := by
  simp [step, hr, writtenTape, moveHead]

theorem skipX_lt (x y : List Bool) (k i : ℕ) (hk : k < x.length) (hi : i < 2 * k + 1) :
    epochTape x y k (i : Int) = 2 ∨ epochTape x y k (i : Int) = 8 := by
  have hix : min k x.length = k := Nat.min_eq_left (le_of_lt hk)
  have hxi : i < 2 * x.length := by omega
  unfold epochTape
  rw [hix]
  by_cases he : i % 2 = 0
  · left; exact tape_x_even x y k (min k y.length) ((addCarry x y false).take k) i hxi he
  · right
    have hi' : i = 2 * (i / 2) + 1 := by omega
    have hj : i / 2 < k := by omega
    have hjx : i / 2 < x.length := by omega
    rw [hi']
    exact tape_x_odd_cons x y k (min k y.length) ((addCarry x y false).take k)
      (i / 2) hj hjx

theorem skipX_ge (x y : List Bool) (k i : ℕ)
    (hk : x.length ≤ k) (hi : i < 2 * x.length) :
    epochTape x y k (i : Int) = 2 ∨ epochTape x y k (i : Int) = 8 := by
  have hix : min k x.length = x.length := Nat.min_eq_right hk
  unfold epochTape
  rw [hix]
  by_cases he : i % 2 = 0
  · left; exact tape_x_even x y x.length (min k y.length) ((addCarry x y false).take k) i hi he
  · right
    have hi' : i = 2 * (i / 2) + 1 := by omega
    have hj : i / 2 < x.length := by omega
    rw [hi']
    exact tape_x_odd_cons x y x.length (min k y.length) ((addCarry x y false).take k)
      (i / 2) hj hj

theorem huntX_skip_lt (x y : List Bool) (k : ℕ) (hk : k < x.length) :
    run machine (ticks (2 * k + 1))
      ⟨huntQ (carryInto x y k), 0, epochTape x y k⟩ =
      some ⟨huntQ (carryInto x y k), ((2 * k + 1 : ℕ) : Int), epochTape x y k⟩ := by
  have hs := scan_right machine (huntQ (carryInto x y k)) (epochTape x y k) 0 (2 * k + 1)
  have hc : (0 : Int) + ((2 * k + 1 : ℕ) : Int) = ((2 * k + 1 : ℕ) : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (0 : Int) + (i : Int) = (i : Int) := by omega
  rw [hh]
  have hcell := skipX_lt x y k i hk hi
  exact rule_hX_skip _ _ hcell

theorem huntX_skip_ge (x y : List Bool) (k : ℕ) (hk : x.length ≤ k) :
    run machine (ticks (2 * x.length))
      ⟨huntQ (carryInto x y k), 0, epochTape x y k⟩ =
      some ⟨huntQ (carryInto x y k), ((2 * x.length : ℕ) : Int), epochTape x y k⟩ := by
  have hs := scan_right machine (huntQ (carryInto x y k)) (epochTape x y k) 0 (2 * x.length)
  have hc : (0 : Int) + ((2 * x.length : ℕ) : Int) = ((2 * x.length : ℕ) : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (0 : Int) + (i : Int) = (i : Int) := by omega
  rw [hh]
  have hcell := skipX_ge x y k i hk hi
  exact rule_hX_skip _ _ hcell

theorem parsed_epoch0 (x y : List Bool) :
    parsedStart x y = epochCfg x y 0 := by
  simp [parsedStart, epochCfg, epoch_init, huntQ, carryInto]

end PakFixedPolyomino.StandardBitVariableAddRipple
