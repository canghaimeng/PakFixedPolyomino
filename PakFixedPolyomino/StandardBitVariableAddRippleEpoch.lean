import PakFixedPolyomino.StandardBitVariableAddRipple
import Mathlib.Tactic

/-! One physical arithmetic epoch of the frozen adder on the entire-tape foundation. States 8–25; fuel is the frozen `epochFuel`. -/
namespace PakFixedPolyomino.StandardBitVariableAddRippleEpoch

open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape Config)
open StandardBitVariableAdd (machine enc mark D Epos addCarry xor3 maj
  update_same nat_ne_neg1 read_bit machine_blank)
open StandardBitVariableAddRipple
open StandardBitMarkedCompaction (scan_right scan_left preserve_step)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub
  Int.natCast_add Int.natCast_mul
set_option simprocs false

def huntStart (x : List Bool) (k : ℕ) : ℕ :=
  if k < x.length then 2 * k + 2 else 2 * x.length + 1

def huntTarget (x y : List Bool) (k : ℕ) : ℕ :=
  if k < y.length then D x + k else Epos x y

def tapeX (x y : List Bool) (k : ℕ) : Int → Fin 32 :=
  tapeAt x y (min (k + 1) x.length) (min k y.length) ((addCarry x y false).take k)

def tapeXY (x y : List Bool) (k : ℕ) : Int → Fin 32 :=
  tapeAt x y (min (k + 1) x.length) (min (k + 1) y.length)
    ((addCarry x y false).take k)

def sumBit (x y : List Bool) (k : ℕ) : Bool :=
  xor3 (x.getD k false) (y.getD k false) (carryInto x y k)

def nextCarry (x y : List Bool) (k : ℕ) : Bool :=
  maj (x.getD k false) (y.getD k false) (carryInto x y k)

theorem succ_int (n : ℕ) : (n : Int) + 1 = ((n + 1 : ℕ) : Int) := by omega

theorem add_int (n m : ℕ) : (n : Int) + (m : Int) = ((n + m : ℕ) : Int) := by omega

theorem step_right_nat (q q' : Fin 64) (t : Int → Fin 32) (n : ℕ) (w : Fin 32)
    (hr : machine.rule q (t (n : Int)) 0 = some ⟨w, q', .right⟩) :
    step machine 0 ⟨q, (n : Int), t⟩ =
      some ⟨q', ((n + 1 : ℕ) : Int), Function.update t (n : Int) w⟩ := by
  have h := step_right q q' t (n : Int) w hr
  have hhead : (n : Int) + 1 = ((n + 1 : ℕ) : Int) := succ_int n
  rw [hhead] at h
  exact h

theorem step_left_pred (q q' : Fin 64) (t : Int → Fin 32) (n : ℕ) (w : Fin 32)
    (hn : 1 ≤ n)
    (hr : machine.rule q (t (n : Int)) 0 = some ⟨w, q', .left⟩) :
    step machine 0 ⟨q, (n : Int), t⟩ =
      some ⟨q', ((n - 1 : ℕ) : Int), Function.update t (n : Int) w⟩ := by
  have h := step_left q q' t (n : Int) w hr
  have hhead : (n : Int) - 1 = ((n - 1 : ℕ) : Int) := by omega
  rw [hhead] at h
  exact h

theorem xor3_fft : xor3 false false true = true := rfl
theorem maj_fft : maj false false true = false := rfl

theorem take_len (x y : List Bool) (k : ℕ) (hk : k < (addCarry x y false).length) :
    ((addCarry x y false).take k).length = k := by
  simp [List.length_take, Nat.min_eq_left (le_of_lt hk)]

theorem getD_ge (l : List Bool) (n : ℕ) (hn : l.length ≤ n) :
    l.getD n false = false := by
  simp [List.getD, Nat.not_lt.mpr hn]

theorem enc_01 (b : Bool) : enc b = 0 ∨ enc b = 1 := by
  cases b <;> simp [enc]

theorem enc_ne_E (b : Bool) : enc b ≠ 5 := by
  cases b <;> (simp [enc]; decide)

theorem min_lt (k n : ℕ) (h : k < n) : min k n = k :=
  Nat.min_eq_left (le_of_lt h)

theorem min_ge (k n : ℕ) (h : n ≤ k) : min k n = n :=
  Nat.min_eq_right h

theorem min_succ_lt (k n : ℕ) (h : k < n) : min (k + 1) n = k + 1 :=
  Nat.min_eq_left (Nat.succ_le_of_lt h)

theorem min_succ_ge (k n : ℕ) (h : n ≤ k) : min (k + 1) n = n :=
  Nat.min_eq_right (le_trans h (Nat.le_succ k))

theorem huntStart_le (x y : List Bool) (k : ℕ) :
    huntStart x k ≤ huntTarget x y k := by
  unfold huntStart huntTarget
  simp only [D, Epos]
  split_ifs <;> omega

theorem huntYFuel_eq (x y : List Bool) (k : ℕ) :
    huntYFuel x y k = huntTarget x y k - huntStart x k + 1 := by
  simp only [huntYFuel, huntStart, huntTarget]

theorem huntXFuel_eq (x : List Bool) (k : ℕ) : huntXFuel x k = huntStart x k := by
  simp only [huntXFuel, huntStart]

theorem nextCarry_eq (x y : List Bool) (k : ℕ) :
    nextCarry x y k = carryInto x y (k + 1) := by
  simp [nextCarry, carryInto]

theorem sumBit_get (x y : List Bool) (k : ℕ)
    (hk : k < (addCarry x y false).length) :
    sumBit x y k = (addCarry x y false)[k] := by
  simpa [sumBit] using (addCarry_get x y k hk).symm

theorem tapeX_consume (x y : List Bool) (k : ℕ) (hx : k < x.length) :
    Function.update (epochTape x y k) ((2 * k + 1 : ℕ) : Int) 8 = tapeX x y k := by
  unfold epochTape tapeX
  rw [min_lt k x.length hx, min_succ_lt k x.length hx]
  exact consume_x x y k (min k y.length) ((addCarry x y false).take k) hx

theorem tapeX_id (x y : List Bool) (k : ℕ) (hx : x.length ≤ k) :
    epochTape x y k = tapeX x y k := by
  unfold epochTape tapeX
  rw [min_ge k x.length hx, min_succ_ge k x.length hx]

theorem tapeXY_consume (x y : List Bool) (k : ℕ) (hy : k < y.length) :
    Function.update (tapeX x y k) ((D x + k : ℕ) : Int) 8 = tapeXY x y k := by
  unfold tapeX tapeXY
  rw [min_lt k y.length hy, min_succ_lt k y.length hy]
  exact consume_y x y (min (k + 1) x.length) k ((addCarry x y false).take k) hy

theorem tapeXY_id (x y : List Bool) (k : ℕ) (hy : y.length ≤ k) :
    tapeX x y k = tapeXY x y k := by
  unfold tapeX tapeXY
  rw [min_ge k y.length hy, min_succ_ge k y.length hy]

theorem tapeXY_write (x y : List Bool) (k : ℕ)
    (hk : k < (addCarry x y false).length) :
    Function.update (tapeXY x y k)
        ((Epos x y + 1 + k : ℕ) : Int) (enc (sumBit x y k)) =
      epochTape x y (k + 1) := by
  have hlen := take_len x y k hk
  have hb := sumBit_get x y k hk
  unfold tapeXY epochTape
  have hsnoc := write_snoc x y (min (k + 1) x.length) (min (k + 1) y.length)
    ((addCarry x y false).take k) (sumBit x y k)
  rw [hlen] at hsnoc
  rw [hsnoc, take_succ_get (addCarry x y false) k hk, hb]

theorem scan_right_nat (q : Fin 64) (t : Int → Fin 32) (start n : ℕ)
    (hr : ∀ i < n, machine.rule q (t ((start + i : ℕ) : Int)) 0 =
      some ⟨t ((start + i : ℕ) : Int), q, .right⟩) :
    run machine (ticks n) ⟨q, (start : Int), t⟩ =
      some ⟨q, ((start + n : ℕ) : Int), t⟩ := by
  have hs := scan_right machine q t (start : Int) n
  have hc : (start : Int) + (n : Int) = ((start + n : ℕ) : Int) := add_int start n
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (start : Int) + (i : Int) = ((start + i : ℕ) : Int) := add_int start i
  rw [hh]
  exact hr i hi

theorem scan_left_nat (q : Fin 64) (t : Int → Fin 32) (start n : ℕ)
    (hle : n ≤ start)
    (hr : ∀ i < n, machine.rule q (t ((start - i : ℕ) : Int)) 0 =
      some ⟨t ((start - i : ℕ) : Int), q, .left⟩) :
    run machine (ticks n) ⟨q, (start : Int), t⟩ =
      some ⟨q, ((start - n : ℕ) : Int), t⟩ := by
  have hs := scan_left machine q t (start : Int) n
  have hc : (start : Int) - (n : Int) = ((start - n : ℕ) : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (start : Int) - (i : Int) = ((start - i : ℕ) : Int) := by omega
  rw [hh]
  exact hr i hi

theorem scan_left_to_L (q : Fin 64) (t : Int → Fin 32) (start : ℕ)
    (hr : ∀ i < start + 1, machine.rule q (t ((start - i : ℕ) : Int)) 0 =
      some ⟨t ((start - i : ℕ) : Int), q, .left⟩) :
    run machine (ticks (start + 1)) ⟨q, (start : Int), t⟩ =
      some ⟨q, (-1 : Int), t⟩ := by
  have hs := scan_left machine q t (start : Int) (start + 1)
  have hc : (start : Int) - ((start + 1 : ℕ) : Int) = (-1 : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (start : Int) - (i : Int) = ((start - i : ℕ) : Int) := by omega
  rw [hh]
  exact hr i hi

theorem tapeX_hY_skip (x y : List Bool) (k i : ℕ)
    (hx : k < x.length) (hlo : 2 * k + 2 ≤ i) (hhi : i < huntTarget x y k) :
    tapeX x y k (i : Int) = 2 ∨ tapeX x y k (i : Int) = 6 ∨
      tapeX x y k (i : Int) = 7 ∨ tapeX x y k (i : Int) = 8 ∨
        tapeX x y k (i : Int) = 4 := by
  have hix : min (k + 1) x.length = k + 1 := min_succ_lt k x.length hx
  have htg_le : huntTarget x y k ≤ Epos x y := by
    unfold huntTarget
    split_ifs with hy
    · simp [D, Epos]; omega
    · exact le_rfl
  have hE : i < Epos x y := lt_of_lt_of_le hhi htg_le
  unfold tapeX
  rw [hix]
  by_cases hxlt : i < 2 * x.length
  · by_cases he : i % 2 = 0
    · left
      exact tape_x_even x y (k + 1) (min k y.length)
        ((addCarry x y false).take k) i hxlt he
    · have hi' : i = 2 * (i / 2) + 1 := by omega
      have hjx : i / 2 < x.length := by omega
      have hj : k + 1 ≤ i / 2 := by omega
      have hcell := tape_x_odd_live x y (k + 1) (min k y.length)
        ((addCarry x y false).take k) (i / 2) hj hjx
      rw [hi', hcell]
      cases (x.getD (i / 2) false) <;> simp [mark]
  · by_cases hs : i = 2 * x.length
    · have hi : (i : Int) = ((2 * x.length : ℕ) : Int) := by rw [hs]
      have hcell := tape_sep x y (k + 1) (min k y.length)
        ((addCarry x y false).take k)
      rw [hi]
      exact Or.inr (Or.inr (Or.inr (Or.inr hcell)))
    · have hD : 2 * x.length + 1 ≤ i := by omega
      have hj : i - (2 * x.length + 1) < y.length :=
        Nat.sub_lt_left_of_lt_add hD (by simp [Epos, D] at hE; exact hE)
      have hjy : i = D x + (i - (2 * x.length + 1)) := by simp [D]; omega
      have hiy : i - (2 * x.length + 1) < min k y.length := by
        unfold huntTarget at hhi
        by_cases hy : k < y.length
        · rw [if_pos hy] at hhi
          have hlt : i < 2 * x.length + 1 + k := by simp [D] at hhi; exact hhi
          have : i - (2 * x.length + 1) < k := Nat.sub_lt_left_of_lt_add hD hlt
          rw [min_lt k y.length hy]
          exact this
        · rw [if_neg hy] at hhi
          have : min k y.length = y.length := min_ge k y.length (le_of_not_gt hy)
          rw [this]
          exact hj
      have hcell := tape_y_cons x y (k + 1) (min k y.length)
        ((addCarry x y false).take k) (i - (2 * x.length + 1)) hiy hj
      rw [hjy, hcell]
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem tapeX_hYdone_skip (x y : List Bool) (k i : ℕ)
    (hx : x.length ≤ k) (hlo : D x ≤ i) (hhi : i < huntTarget x y k) :
    tapeX x y k (i : Int) = 2 ∨ tapeX x y k (i : Int) = 8 := by
  have hix : min (k + 1) x.length = x.length := min_succ_ge k x.length hx
  have hj : i - D x < y.length := by
    unfold huntTarget at hhi
    by_cases hy : k < y.length
    · rw [if_pos hy] at hhi
      exact lt_trans (Nat.sub_lt_left_of_lt_add hlo hhi) hy
    · rw [if_neg hy] at hhi
      have hE : i < D x + y.length := by simp [Epos] at hhi; exact hhi
      exact Nat.sub_lt_left_of_lt_add hlo hE
  have hiy : i - D x < min k y.length := by
    unfold huntTarget at hhi
    by_cases hy : k < y.length
    · rw [if_pos hy] at hhi
      have : i - D x < k := Nat.sub_lt_left_of_lt_add hlo hhi
      rw [min_lt k y.length hy]
      exact this
    · rw [if_neg hy] at hhi
      have : min k y.length = y.length := min_ge k y.length (le_of_not_gt hy)
      rw [this]
      exact hj
  have hjy : i = D x + (i - D x) := (Nat.add_sub_of_le hlo).symm
  unfold tapeX
  rw [hix]
  have hcell := tape_y_cons x y x.length (min k y.length)
    ((addCarry x y false).take k) (i - D x) hiy hj
  rw [hjy, hcell]
  right; rfl

theorem tapeXY_seek_skip (x y : List Bool) (k i : ℕ)
    (hy : k < y.length) (hlo : D x + k + 1 ≤ i) (hhi : i < Epos x y) :
    tapeXY x y k (i : Int) ≠ 5 := by
  have hiy : min (k + 1) y.length = k + 1 := min_succ_lt k y.length hy
  have hD : D x ≤ i :=
    le_trans (Nat.le_add_right (D x) (k + 1)) hlo
  have hj : i - D x < y.length := by
    have hE : i < D x + y.length := by simp [Epos] at hhi; exact hhi
    exact Nat.sub_lt_left_of_lt_add hD hE
  have hjge : k + 1 ≤ i - D x := by
    have hlo' : D x + (k + 1) ≤ i := by
      have : D x + (k + 1) = D x + k + 1 := by omega
      rwa [this]
    rw [Nat.add_comm] at hlo'
    exact (Nat.le_sub_iff_add_le hD).mpr hlo'
  have hjy : i = D x + (i - D x) := (Nat.add_sub_of_le hD).symm
  unfold tapeXY
  rw [hiy]
  have hcell := tape_y_live x y (min (k + 1) x.length) (k + 1)
    ((addCarry x y false).take k) (i - D x) hjge hj
  rw [hjy, hcell]
  exact enc_ne_E _

theorem tapeXY_res (x y : List Bool) (k i : ℕ)
    (hk : k < (addCarry x y false).length) (hi : i < k) :
    tapeXY x y k ((Epos x y + 1 + i : ℕ) : Int) = 0 ∨
      tapeXY x y k ((Epos x y + 1 + i : ℕ) : Int) = 1 := by
  have hlen := take_len x y k hk
  have hi' : i < ((addCarry x y false).take k).length := by omega
  unfold tapeXY
  rw [tape_res]
  have hbit := read_bit ((addCarry x y false).take k) i hi'
  rw [hbit]
  exact enc_01 _

theorem tapeXY_blank (x y : List Bool) (k : ℕ)
    (hk : k < (addCarry x y false).length) :
    tapeXY x y k ((Epos x y + 1 + k : ℕ) : Int) = 2 := by
  have hlen := take_len x y k hk
  unfold tapeXY
  rw [tape_res]
  have hge := inputTape_ge machine ((addCarry x y false).take k) (k : Int)
    (by simp [hlen])
  rw [machine_blank] at hge
  exact hge

theorem huntX_lt (x y : List Bool) (k : ℕ) (hx : k < x.length) :
    run machine (ticks (2 * k + 2)) (epochCfg x y k) =
      some ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((2 * k + 2 : ℕ) : Int), tapeX x y k⟩ := by
  have hfuel : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  rw [hfuel, ticks_add, epochCfg, run_append, huntX_skip_lt x y k hx,
    Option.bind_some, run_ticks_one]
  have hlive : epochTape x y k ((2 * k + 1 : ℕ) : Int) =
      mark (x.getD k false) := by
    unfold epochTape
    rw [min_lt k x.length hx]
    exact tape_x_odd_live x y k (min k y.length)
      ((addCarry x y false).take k) k (le_refl _) hx
  have hxk : x.getD k false = x[k] := getD_lt x k false hx
  rw [hxk] at hlive ⊢
  cases hxbit : (x[k] : Bool)
  · have h6 : epochTape x y k ((2 * k + 1 : ℕ) : Int) = 6 := by
      rw [hlive, hxbit]; simp [mark]
    have hstep := step_right_nat (huntQ (carryInto x y k))
      (huntYQ false (carryInto x y k)) (epochTape x y k)
      (2 * k + 1) 8 (by rw [h6]; exact rule_hX_false _)
    rw [hstep, tapeX_consume x y k hx]
  · have h7 : epochTape x y k ((2 * k + 1 : ℕ) : Int) = 7 := by
      rw [hlive, hxbit]; simp [mark]
    have hstep := step_right_nat (huntQ (carryInto x y k))
      (huntYQ true (carryInto x y k)) (epochTape x y k)
      (2 * k + 1) 8 (by rw [h7]; exact rule_hX_true _)
    rw [hstep, tapeX_consume x y k hx]

theorem huntX_ge (x y : List Bool) (k : ℕ) (hx : x.length ≤ k) :
    run machine (ticks (2 * x.length + 1)) (epochCfg x y k) =
      some ⟨huntYdoneQ (carryInto x y k), (D x : Int), tapeX x y k⟩ := by
  have hfuel : 2 * x.length + 1 = 2 * x.length + 1 := rfl
  rw [show 2 * x.length + 1 = (2 * x.length) + 1 by omega, ticks_add, epochCfg,
    run_append, huntX_skip_ge x y k hx, Option.bind_some, run_ticks_one]
  have hsep : epochTape x y k ((2 * x.length : ℕ) : Int) = 4 := by
    unfold epochTape
    rw [min_ge k x.length hx]
    exact tape_sep x y x.length (min k y.length) ((addCarry x y false).take k)
  have hstep := step_right_nat (huntQ (carryInto x y k))
    (huntYdoneQ (carryInto x y k)) (epochTape x y k)
    (2 * x.length) 4 (by rw [hsep]; exact rule_hX_sep _)
  rw [hstep]
  have ht : Function.update (epochTape x y k) ((2 * x.length : ℕ) : Int) 4 =
      epochTape x y k := by
    rw [show 4 = epochTape x y k ((2 * x.length : ℕ) : Int) from hsep.symm]
    exact update_same (epochTape x y k) ((2 * x.length : ℕ) : Int)
  have hD : ((2 * x.length + 1 : ℕ) : Int) = (D x : Int) := by simp [D]
  rw [ht, tapeX_id x y k hx, hD]

theorem huntY_lt_lt (x y : List Bool) (k : ℕ)
    (hx : k < x.length) (hy : k < y.length) :
    run machine (ticks (huntYFuel x y k))
      ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((2 * k + 2 : ℕ) : Int), tapeX x y k⟩ =
      some ⟨seekEQ (sumBit x y k) (nextCarry x y k),
        ((D x + k + 1 : ℕ) : Int), tapeXY x y k⟩ := by
  have hst : huntStart x k = 2 * k + 2 := by simp [huntStart, hx]
  have htg : huntTarget x y k = D x + k := by simp [huntTarget, hy]
  have hle : 2 * k + 2 ≤ D x + k := by
    have := huntStart_le x y k
    simpa [hst, htg] using this
  have hfuel : huntYFuel x y k = (D x + k - (2 * k + 2)) + 1 := by
    rw [huntYFuel_eq, hst, htg]
  rw [hfuel, ticks_add, run_append]
  have hscan := scan_right_nat (huntYQ (x.getD k false) (carryInto x y k))
    (tapeX x y k) (2 * k + 2) (D x + k - (2 * k + 2))
  have hadd : 2 * k + 2 + (D x + k - (2 * k + 2)) = D x + k :=
    Nat.add_sub_of_le hle
  rw [hadd] at hscan
  have hskip : run machine (ticks (D x + k - (2 * k + 2)))
      ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((2 * k + 2 : ℕ) : Int), tapeX x y k⟩ =
      some ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((D x + k : ℕ) : Int), tapeX x y k⟩ := by
    apply hscan
    intro i hi
    have hlo : 2 * k + 2 ≤ 2 * k + 2 + i := by omega
    have hhi : 2 * k + 2 + i < huntTarget x y k := by
      rw [htg]; omega
    have hcell := tapeX_hY_skip x y k (2 * k + 2 + i) hx hlo hhi
    exact rule_hY_skip (x.getD k false) (carryInto x y k) _ hcell
  rw [hskip, Option.bind_some, run_ticks_one]
  have hlive : tapeX x y k ((D x + k : ℕ) : Int) =
      enc (y.getD k false) := by
    unfold tapeX
    rw [min_lt k y.length hy]
    exact tape_y_live x y (min (k + 1) x.length) k
      ((addCarry x y false).take k) k (le_refl _) hy
  have hyk : y.getD k false = y[k] := getD_lt y k false hy
  rw [hyk] at hlive
  cases hybit : (y[k] : Bool)
  · have h0 : tapeX x y k ((D x + k : ℕ) : Int) = 0 := by
      rw [hlive, hybit]; simp [enc]
    have hstep := step_right_nat (huntYQ (x.getD k false) (carryInto x y k))
      (seekEQ (xor3 (x.getD k false) false (carryInto x y k))
        (maj (x.getD k false) false (carryInto x y k)))
      (tapeX x y k) (D x + k) 8
      (by rw [h0]; exact rule_hY_false _ _)
    rw [hstep, tapeXY_consume x y k hy]
    unfold sumBit nextCarry
    rw [getD_lt y k false hy, hybit]
  · have h1 : tapeX x y k ((D x + k : ℕ) : Int) = 1 := by
      rw [hlive, hybit]; simp [enc]
    have hstep := step_right_nat (huntYQ (x.getD k false) (carryInto x y k))
      (seekEQ (xor3 (x.getD k false) true (carryInto x y k))
        (maj (x.getD k false) true (carryInto x y k)))
      (tapeX x y k) (D x + k) 8
      (by rw [h1]; exact rule_hY_true _ _)
    rw [hstep, tapeXY_consume x y k hy]
    unfold sumBit nextCarry
    rw [getD_lt y k false hy, hybit]

theorem huntY_lt_ge (x y : List Bool) (k : ℕ)
    (hx : k < x.length) (hy : y.length ≤ k)
    (hk : k < (addCarry x y false).length) :
    run machine (ticks (huntYFuel x y k))
      ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((2 * k + 2 : ℕ) : Int), tapeX x y k⟩ =
      some ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 : ℕ) : Int), tapeXY x y k⟩ := by
  have hst : huntStart x k = 2 * k + 2 := by simp [huntStart, hx]
  have htg : huntTarget x y k = Epos x y := by simp [huntTarget, Nat.not_lt.mpr hy]
  have hle : 2 * k + 2 ≤ Epos x y := by
    have := huntStart_le x y k
    simpa [hst, htg] using this
  have hfuel : huntYFuel x y k = (Epos x y - (2 * k + 2)) + 1 := by
    rw [huntYFuel_eq, hst, htg]
  rw [hfuel, ticks_add, run_append]
  have hscan := scan_right_nat (huntYQ (x.getD k false) (carryInto x y k))
    (tapeX x y k) (2 * k + 2) (Epos x y - (2 * k + 2))
  have hadd : 2 * k + 2 + (Epos x y - (2 * k + 2)) = Epos x y :=
    Nat.add_sub_of_le hle
  rw [hadd] at hscan
  have hskip : run machine (ticks (Epos x y - (2 * k + 2)))
      ⟨huntYQ (x.getD k false) (carryInto x y k),
        ((2 * k + 2 : ℕ) : Int), tapeX x y k⟩ =
      some ⟨huntYQ (x.getD k false) (carryInto x y k),
        (Epos x y : Int), tapeX x y k⟩ := by
    apply hscan
    intro i hi
    have hlo : 2 * k + 2 ≤ 2 * k + 2 + i := by omega
    have hhi : 2 * k + 2 + i < huntTarget x y k := by
      rw [htg]; omega
    have hcell := tapeX_hY_skip x y k (2 * k + 2 + i) hx hlo hhi
    exact rule_hY_skip (x.getD k false) (carryInto x y k) _ hcell
  rw [hskip, Option.bind_some, run_ticks_one]
  have hE : tapeX x y k (Epos x y : Int) = 5 := by
    unfold tapeX
    exact tape_E x y (min (k + 1) x.length) (min k y.length)
      ((addCarry x y false).take k)
  have hstep := step_right_nat (huntYQ (x.getD k false) (carryInto x y k))
    (writeQ (xor3 (x.getD k false) false (carryInto x y k))
      (maj (x.getD k false) false (carryInto x y k)))
    (tapeX x y k) (Epos x y) 5
    (by rw [hE]; exact rule_hY_E _ _)
  rw [hstep]
  have ht : Function.update (tapeX x y k) (Epos x y : Int) 5 = tapeX x y k := by
    rw [show 5 = tapeX x y k (Epos x y : Int) from hE.symm]
    exact update_same (tapeX x y k) (Epos x y : Int)
  have hyg : y.getD k false = false := getD_ge y k hy
  rw [ht, tapeXY_id x y k hy]
  unfold sumBit nextCarry
  rw [hyg]

theorem huntY_ge_lt (x y : List Bool) (k : ℕ)
    (hx : x.length ≤ k) (hy : k < y.length) :
    run machine (ticks (huntYFuel x y k))
      ⟨huntYdoneQ (carryInto x y k), (D x : Int), tapeX x y k⟩ =
      some ⟨seekEQ (sumBit x y k) (nextCarry x y k),
        ((D x + k + 1 : ℕ) : Int), tapeXY x y k⟩ := by
  have hst : huntStart x k = D x := by
    simp [huntStart, Nat.not_lt.mpr hx, D]
  have htg : huntTarget x y k = D x + k := by simp [huntTarget, hy]
  have hle : D x ≤ D x + k := Nat.le_add_right _ _
  have hfuel : huntYFuel x y k = (D x + k - D x) + 1 := by
    rw [huntYFuel_eq, hst, htg]
  have hsub : D x + k - D x = k := by omega
  rw [hfuel, hsub, ticks_add, run_append]
  have hscan := scan_right_nat (huntYdoneQ (carryInto x y k))
    (tapeX x y k) (D x) k
  have hadd : D x + k = D x + k := rfl
  have hskip : run machine (ticks k)
      ⟨huntYdoneQ (carryInto x y k), (D x : Int), tapeX x y k⟩ =
      some ⟨huntYdoneQ (carryInto x y k), ((D x + k : ℕ) : Int), tapeX x y k⟩ := by
    apply hscan
    intro i hi
    have hlo : D x ≤ D x + i := Nat.le_add_right _ _
    have hhi : D x + i < huntTarget x y k := by
      rw [htg]; omega
    have hcell := tapeX_hYdone_skip x y k (D x + i) hx hlo hhi
    exact rule_hYdone_skip (carryInto x y k) _ hcell
  rw [hskip, Option.bind_some, run_ticks_one]
  have hlive : tapeX x y k ((D x + k : ℕ) : Int) =
      enc (y.getD k false) := by
    unfold tapeX
    rw [min_lt k y.length hy]
    exact tape_y_live x y (min (k + 1) x.length) k
      ((addCarry x y false).take k) k (le_refl _) hy
  have hyk : y.getD k false = y[k] := getD_lt y k false hy
  have hxg : x.getD k false = false := getD_ge x k hx
  rw [hyk] at hlive
  cases hybit : (y[k] : Bool)
  · have h0 : tapeX x y k ((D x + k : ℕ) : Int) = 0 := by
      rw [hlive, hybit]; simp [enc]
    have hstep := step_right_nat (huntYdoneQ (carryInto x y k))
      (seekEQ (xor3 false false (carryInto x y k))
        (maj false false (carryInto x y k)))
      (tapeX x y k) (D x + k) 8
      (by rw [h0]; exact rule_hYdone_false _)
    rw [hstep, tapeXY_consume x y k hy]
    unfold sumBit nextCarry
    rw [hxg, getD_lt y k false hy, hybit]
  · have h1 : tapeX x y k ((D x + k : ℕ) : Int) = 1 := by
      rw [hlive, hybit]; simp [enc]
    have hstep := step_right_nat (huntYdoneQ (carryInto x y k))
      (seekEQ (xor3 false true (carryInto x y k))
        (maj false true (carryInto x y k)))
      (tapeX x y k) (D x + k) 8
      (by rw [h1]; exact rule_hYdone_true _)
    rw [hstep, tapeXY_consume x y k hy]
    unfold sumBit nextCarry
    rw [hxg, getD_lt y k false hy, hybit]

theorem huntY_ge_ge (x y : List Bool) (k : ℕ)
    (hx : x.length ≤ k) (hy : y.length ≤ k)
    (hk : k < (addCarry x y false).length) :
    run machine (ticks (huntYFuel x y k))
      ⟨huntYdoneQ (carryInto x y k), (D x : Int), tapeX x y k⟩ =
      some ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 : ℕ) : Int), tapeXY x y k⟩ := by
  have hst : huntStart x k = D x := by
    simp [huntStart, Nat.not_lt.mpr hx, D]
  have htg : huntTarget x y k = Epos x y := by
    simp [huntTarget, Nat.not_lt.mpr hy]
  have hle : D x ≤ Epos x y := by simp [D, Epos]
  have hfuel : huntYFuel x y k = (Epos x y - D x) + 1 := by
    rw [huntYFuel_eq, hst, htg]
  rw [hfuel, ticks_add, run_append]
  have hscan := scan_right_nat (huntYdoneQ (carryInto x y k))
    (tapeX x y k) (D x) (Epos x y - D x)
  have hadd : D x + (Epos x y - D x) = Epos x y := Nat.add_sub_of_le hle
  rw [hadd] at hscan
  have hskip : run machine (ticks (Epos x y - D x))
      ⟨huntYdoneQ (carryInto x y k), (D x : Int), tapeX x y k⟩ =
      some ⟨huntYdoneQ (carryInto x y k), (Epos x y : Int), tapeX x y k⟩ := by
    apply hscan
    intro i hi
    have hlo : D x ≤ D x + i := Nat.le_add_right _ _
    have hhi : D x + i < huntTarget x y k := by
      rw [htg]; omega
    have hcell := tapeX_hYdone_skip x y k (D x + i) hx hlo hhi
    exact rule_hYdone_skip (carryInto x y k) _ hcell
  rw [hskip, Option.bind_some, run_ticks_one]
  have hc : carryInto x y k = true := by
    rw [carryInto_from]
    exact expand_carry x y false k hx hy hk
  have hxg : x.getD k false = false := getD_ge x k hx
  have hyg : y.getD k false = false := getD_ge y k hy
  have hE : tapeX x y k (Epos x y : Int) = 5 := by
    unfold tapeX
    exact tape_E x y (min (k + 1) x.length) (min k y.length)
      ((addCarry x y false).take k)
  have hq : huntYdoneQ (carryInto x y k) = huntYdoneQ true := by rw [hc]
  rw [hq]
  have hstep := step_right_nat (huntYdoneQ true) (writeQ true false)
    (tapeX x y k) (Epos x y) 5
    (by rw [hE]; exact rule_hYdone_E1)
  rw [hstep]
  have ht : Function.update (tapeX x y k) (Epos x y : Int) 5 = tapeX x y k := by
    rw [show 5 = tapeX x y k (Epos x y : Int) from hE.symm]
    exact update_same (tapeX x y k) (Epos x y : Int)
  have hsum : sumBit x y k = true := by
    unfold sumBit; rw [hxg, hyg, hc, xor3_fft]
  have hnc : nextCarry x y k = false := by
    unfold nextCarry; rw [hxg, hyg, hc, maj_fft]
  rw [ht, tapeXY_id x y k hy, hsum, hnc]

theorem seekE_run (x y : List Bool) (k : ℕ) (hy : k < y.length) :
    run machine (ticks (seekEFuel x y k))
      ⟨seekEQ (sumBit x y k) (nextCarry x y k),
        ((D x + k + 1 : ℕ) : Int), tapeXY x y k⟩ =
      some ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 : ℕ) : Int), tapeXY x y k⟩ := by
  have hle : D x + k + 1 ≤ Epos x y := by simp [D, Epos]; omega
  have hfuel : seekEFuel x y k = (Epos x y - (D x + k + 1)) + 1 := by
    unfold seekEFuel
    rw [if_pos hy]
    omega
  rw [hfuel, ticks_add, run_append]
  have hscan := scan_right_nat (seekEQ (sumBit x y k) (nextCarry x y k))
    (tapeXY x y k) (D x + k + 1) (Epos x y - (D x + k + 1))
  have hadd : D x + k + 1 + (Epos x y - (D x + k + 1)) = Epos x y :=
    Nat.add_sub_of_le hle
  rw [hadd] at hscan
  have hskip : run machine (ticks (Epos x y - (D x + k + 1)))
      ⟨seekEQ (sumBit x y k) (nextCarry x y k),
        ((D x + k + 1 : ℕ) : Int), tapeXY x y k⟩ =
      some ⟨seekEQ (sumBit x y k) (nextCarry x y k),
        (Epos x y : Int), tapeXY x y k⟩ := by
    apply hscan
    intro i hi
    have hlo : D x + k + 1 ≤ D x + k + 1 + i := by omega
    have hhi : D x + k + 1 + i < Epos x y := by omega
    have hne := tapeXY_seek_skip x y k (D x + k + 1 + i) hy hlo hhi
    exact rule_seekE_notE (sumBit x y k) (nextCarry x y k) _ hne
  rw [hskip, Option.bind_some, run_ticks_one]
  have hE : tapeXY x y k (Epos x y : Int) = 5 := by
    unfold tapeXY
    exact tape_E x y (min (k + 1) x.length) (min (k + 1) y.length)
      ((addCarry x y false).take k)
  have hstep := step_right_nat (seekEQ (sumBit x y k) (nextCarry x y k))
    (writeQ (sumBit x y k) (nextCarry x y k)) (tapeXY x y k)
    (Epos x y) 5 (by rw [hE]; exact rule_seekE_E _ _)
  rw [hstep]
  have ht : Function.update (tapeXY x y k) (Epos x y : Int) 5 = tapeXY x y k := by
    rw [show 5 = tapeXY x y k (Epos x y : Int) from hE.symm]
    exact update_same (tapeXY x y k) (Epos x y : Int)
  rw [ht]

theorem write_run (x y : List Bool) (k : ℕ)
    (hk : k < (addCarry x y false).length) :
    run machine (ticks (k + 1))
      ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 : ℕ) : Int), tapeXY x y k⟩ =
      some ⟨retQ (nextCarry x y k), ((Epos x y + k : ℕ) : Int),
        epochTape x y (k + 1)⟩ := by
  rw [ticks_add (k) 1, run_append]
  have hscan := scan_right_nat (writeQ (sumBit x y k) (nextCarry x y k))
    (tapeXY x y k) (Epos x y + 1) k
  have hadd : Epos x y + 1 + k = Epos x y + 1 + k := rfl
  have hskip : run machine (ticks k)
      ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 : ℕ) : Int), tapeXY x y k⟩ =
      some ⟨writeQ (sumBit x y k) (nextCarry x y k),
        ((Epos x y + 1 + k : ℕ) : Int), tapeXY x y k⟩ := by
    apply hscan
    intro i hi
    have hcell := tapeXY_res x y k i hk hi
    exact rule_write_bit (sumBit x y k) (nextCarry x y k) _ hcell
  rw [hskip, Option.bind_some, run_ticks_one]
  have hblank := tapeXY_blank x y k hk
  have hstep := step_left_pred (writeQ (sumBit x y k) (nextCarry x y k))
    (retQ (nextCarry x y k)) (tapeXY x y k)
    (Epos x y + 1 + k) (enc (sumBit x y k))
    (by omega) (by rw [hblank]; exact rule_write_blank _ _)
  rw [hstep]
  have hnk : Epos x y + 1 + k - 1 = Epos x y + k := by omega
  rw [hnk, tapeXY_write x y k hk]

theorem ret_run (x y : List Bool) (k : ℕ) (nc : Bool) :
    run machine (ticks (Epos x y + k + 2))
      ⟨retQ nc, ((Epos x y + k : ℕ) : Int), epochTape x y (k + 1)⟩ =
      some ⟨huntQ nc, 0, epochTape x y (k + 1)⟩ := by
  have hfuel : Epos x y + k + 2 = (Epos x y + k + 1) + 1 := by omega
  rw [hfuel, ticks_add, run_append]
  have hscan := scan_left_to_L (retQ nc) (epochTape x y (k + 1)) (Epos x y + k)
  have hskip : run machine (ticks (Epos x y + k + 1))
      ⟨retQ nc, ((Epos x y + k : ℕ) : Int), epochTape x y (k + 1)⟩ =
      some ⟨retQ nc, (-1 : Int), epochTape x y (k + 1)⟩ := by
    apply hscan
    intro i hi
    have hne : epochTape x y (k + 1) ((Epos x y + k - i : ℕ) : Int) ≠ 3 := by
      unfold epochTape
      exact tape_nat_ne_L x y (min (k + 1) x.length) (min (k + 1) y.length)
        ((addCarry x y false).take (k + 1)) (Epos x y + k - i)
    exact rule_ret_notL nc _ hne
  rw [hskip, Option.bind_some, run_ticks_one]
  have hL : epochTape x y (k + 1) (-1) = 3 := by
    unfold epochTape
    exact tape_L x y (min (k + 1) x.length) (min (k + 1) y.length)
      ((addCarry x y false).take (k + 1))
  have hstep := step_right (retQ nc) (huntQ nc) (epochTape x y (k + 1))
    (-1) 3 (by rw [hL]; exact rule_ret_L nc)
  rw [hstep]
  have ht : Function.update (epochTape x y (k + 1)) (-1) 3 =
      epochTape x y (k + 1) := by
    rw [show 3 = epochTape x y (k + 1) (-1) from hL.symm]
    exact update_same (epochTape x y (k + 1)) (-1)
  have hhead : (-1 : Int) + 1 = (0 : Int) := by omega
  rw [ht, hhead]

theorem epochFuel_split (x y : List Bool) (k : ℕ) :
    epochFuel x y k =
      huntXFuel x k + (huntYFuel x y k +
        (seekEFuel x y k + ((k + 1) + (Epos x y + k + 2)))) := by
  simp only [epochFuel]
  omega

theorem epoch_run (x y : List Bool) (k : Nat)
    (hk : k < (addCarry x y false).length) :
    run machine (ticks (epochFuel x y k)) (epochCfg x y k) =
      some (epochCfg x y (k + 1)) := by
  rw [epochFuel_split, ticks_add, run_append]
  by_cases hx : k < x.length
  · have hxf : huntXFuel x k = 2 * k + 2 := by simp [huntXFuel, hx]
    rw [hxf, huntX_lt x y k hx, Option.bind_some, ticks_add, run_append]
    by_cases hy : k < y.length
    · rw [huntY_lt_lt x y k hx hy, Option.bind_some, ticks_add, run_append,
        seekE_run x y k hy, Option.bind_some, ticks_add, run_append,
        write_run x y k hk, Option.bind_some, ret_run x y k (nextCarry x y k)]
      simp [epochCfg, nextCarry_eq]
    · have hyg : y.length ≤ k := le_of_not_gt hy
      have hse : seekEFuel x y k = 0 := by simp [seekEFuel, hy]
      rw [huntY_lt_ge x y k hx hyg hk, Option.bind_some, hse, ticks_add,
        show ticks 0 = [] by simp [ticks], run_append, run_nil, Option.bind_some,
        ticks_add, run_append, write_run x y k hk, Option.bind_some,
        ret_run x y k (nextCarry x y k)]
      simp [epochCfg, nextCarry_eq]
  · have hxg : x.length ≤ k := le_of_not_gt hx
    have hxf : huntXFuel x k = 2 * x.length + 1 := by simp [huntXFuel, hx]
    rw [hxf, huntX_ge x y k hxg, Option.bind_some, ticks_add, run_append]
    by_cases hy : k < y.length
    · rw [huntY_ge_lt x y k hxg hy, Option.bind_some, ticks_add, run_append,
        seekE_run x y k hy, Option.bind_some, ticks_add, run_append,
        write_run x y k hk, Option.bind_some, ret_run x y k (nextCarry x y k)]
      simp [epochCfg, nextCarry_eq]
    · have hyg : y.length ≤ k := le_of_not_gt hy
      have hse : seekEFuel x y k = 0 := by simp [seekEFuel, hy]
      rw [huntY_ge_ge x y k hxg hyg hk, Option.bind_some, hse, ticks_add,
        show ticks 0 = [] by simp [ticks], run_append, run_nil, Option.bind_some,
        ticks_add, run_append, write_run x y k hk, Option.bind_some,
        ret_run x y k (nextCarry x y k)]
      simp [epochCfg, nextCarry_eq]

end PakFixedPolyomino.StandardBitVariableAddRippleEpoch
