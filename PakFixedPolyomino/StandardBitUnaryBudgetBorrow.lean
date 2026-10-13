import PakFixedPolyomino.StandardBitUnaryBudgetCompare
import Mathlib.Tactic

/-! One physical interleaved borrow of a same-width counter on the frozen
19-state comparator. Entire Int tapes, fuel exactly `D x + 1`. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetBorrow

open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitUnaryBudgetCompare
open StandardBitDecrementWord
  (borrowBits zeroPrefix borrow_none_iff borrow_value borrow_length
    zeroPrefix_le zeroPrefix_get zeroPrefix_stop borrow_layout)
open StandardBitDecrementAlignment (value_eq_original)
open StandardBitMarkedCompaction (scan_right)
open StandardBitPairProjection
  (natInt natInt_succ natInt_ne_neg1 natInt_inj nat_ne_neg1
    toNat_ofNat update_same)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000
set_option simprocs false
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def pref (u : List Bool) (n : ℕ) : List Bool :=
  List.replicate n true ++ u.drop n

theorem pref_zero (u : List Bool) : pref u 0 = u := by
  simp [pref]

theorem pref_length_le (u : List Bool) (n : ℕ) (hn : n ≤ u.length) :
    (pref u n).length = u.length := by
  simp [pref, List.length_drop, Nat.add_sub_cancel' hn]

theorem pref_all (u : List Bool) :
    pref u u.length = List.replicate u.length true := by
  simp [pref, List.drop_length]

theorem pref_get_lt (u : List Bool) (n i : ℕ) (hi : i < n) (hn : n ≤ u.length) :
    (pref u n)[i]'(by rw [pref_length_le u n hn]; omega) = true := by
  unfold pref
  have hleft : i < (List.replicate n true).length := by simpa
  rw [List.getElem_append_left hleft, List.getElem_replicate]

theorem pref_get_ge (u : List Bool) (n i : ℕ) (hni : n ≤ i) (hi : i < u.length) :
    (pref u n)[i]'(by rw [pref_length_le u n (le_trans hni (le_of_lt hi))]; exact hi) =
      u[i] := by
  unfold pref
  have hge : (List.replicate n true).length ≤ i := by simpa
  rw [List.getElem_append_right hge]
  simp only [List.length_replicate, List.getElem_drop]
  congr 1
  omega

theorem pref_succ (u : List Bool) (n : ℕ) (hn : n < u.length) :
    (pref u n).set n true = pref u (n + 1) := by
  unfold pref
  have hge : (List.replicate n true).length ≤ n := by simp
  rw [List.set_append_right n true hge]
  simp only [List.length_replicate, Nat.sub_self]
  rw [List.drop_eq_getElem_cons (i := n) hn]
  change List.replicate n true ++ ([true] ++ u.drop (n + 1)) = _
  rw [← List.append_assoc]
  simp [List.replicate_succ']

theorem pref_set_false (u : List Bool) (t : ℕ) (ht : t < u.length) :
    (pref u t).set t false =
      List.replicate t true ++ false :: u.drop (t + 1) := by
  unfold pref
  have hge : (List.replicate t true).length ≤ t := by simp
  rw [List.set_append_right t false hge]
  simp only [List.length_replicate, Nat.sub_self]
  rw [List.drop_eq_getElem_cons (i := t) ht]
  rfl

theorem some_lt {u v : List Bool} (hb : borrowBits u = some v) :
    zeroPrefix u < u.length := by
  have hne : zeroPrefix u ≠ u.length := by
    intro he
    rw [borrow_layout, if_pos he] at hb
    cases hb
  have := zeroPrefix_le u
  omega

theorem some_word {u v : List Bool} (hb : borrowBits u = some v) :
    v = (pref u (zeroPrefix u)).set (zeroPrefix u) false := by
  have hlt := some_lt hb
  have hne : zeroPrefix u ≠ u.length := by omega
  rw [borrow_layout, if_neg hne] at hb
  injection hb with hv
  rw [← hv]
  exact (pref_set_false u (zeroPrefix u) hlt).symm

theorem none_len (u : List Bool) (hb : borrowBits u = none) :
    zeroPrefix u = u.length := by
  rw [borrow_layout] at hb
  split_ifs at hb with h
  · exact h
  · cases hb

theorem none_false (u : List Bool) (hb : borrowBits u = none) :
    ∀ i : ℕ, (hi : i < u.length) → u[i] = false := by
  intro i hi
  have hz := none_len u hb
  exact zeroPrefix_get u i (by omega)

theorem budget_marker (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hj : 2 * j < D x) :
    budgetTape x y k u (natInt (2 * j)) = 6 := by
  rw [budget_at]; unfold budgetNat
  rw [if_pos hj, if_pos (by omega : (2 * j) % 2 = 0)]

theorem budget_payload (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hj : j < u.length) (hw : u.length = x.length) :
    budgetTape x y k u (natInt (2 * j + 1)) = enc u[j] := by
  rw [budget_at]; unfold budgetNat
  have hlt : 2 * j + 1 < D x := by simp [D]; omega
  rw [if_pos hlt, if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
  have hd : (2 * j + 1) / 2 = j := by omega
  rw [dif_pos (by omega : (2 * j + 1) / 2 < u.length)]
  simp [hd]

theorem budget_SEP (x y : List Bool) (k : ℕ) (u : List Bool) :
    budgetTape x y k u (natInt (D x)) = 4 := by
  rw [budget_at]; unfold budgetNat
  rw [if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem budget_ne_SEP_lt (x y : List Bool) (k : ℕ) (u : List Bool) (i : ℕ)
    (hi : i < D x) : budgetTape x y k u (natInt i) ≠ 4 := by
  rw [budget_at]; unfold budgetNat
  rw [if_pos hi]
  by_cases he : i % 2 = 0
  · rw [if_pos he]; decide
  · rw [if_neg he]
    by_cases hu : i / 2 < u.length
    · rw [dif_pos hu]; cases u[i / 2] <;> (simp [enc]; decide)
    · rw [dif_neg hu]; decide

theorem budget_set (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ) (b : Bool)
    (hj : j < u.length) (hw : u.length = x.length) :
    Function.update (budgetTape x y k u) (natInt (2 * j + 1)) (enc b) =
      budgetTape x y k (u.set j b) := by
  funext z
  by_cases hz : z = natInt (2 * j + 1)
  · subst z
    rw [Function.update_apply, if_pos rfl, budget_at]
    unfold budgetNat
    have hlt : 2 * j + 1 < D x := by simp [D]; omega
    rw [if_pos hlt, if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
    have hd : (2 * j + 1) / 2 = j := by omega
    have hlen : (u.set j b).length = u.length := List.length_set
    rw [dif_pos (by omega : (2 * j + 1) / 2 < (u.set j b).length)]
    simp [hd]
  · rw [Function.update_apply, if_neg hz]
    unfold budgetTape
    by_cases hL : z = -1
    · simp [hL]
    · rw [if_neg hL, if_neg hL]
      by_cases hpos : 0 ≤ z
      · rw [dif_pos hpos, dif_pos hpos]
        unfold budgetNat
        by_cases h1 : z.toNat < D x
        · rw [if_pos h1, if_pos h1]
          by_cases he : z.toNat % 2 = 0
          · rw [if_pos he, if_pos he]
          · rw [if_neg he, if_neg he]
            have hjdiv : z.toNat / 2 < u.length := by
              simp [D] at h1; omega
            have hjdiv' : z.toNat / 2 < (u.set j b).length := by
              simpa [List.length_set] using hjdiv
            rw [dif_pos hjdiv, dif_pos hjdiv']
            have hne : z.toNat / 2 ≠ j := by
              intro heq
              have : z.toNat = 2 * j + 1 := by omega
              exact hz ((Int.toNat_of_nonneg hpos).symm.trans (congrArg natInt this))
            simp [List.getElem_set, Ne.symm hne]
        · rw [if_neg h1, if_neg h1]
      · rw [dif_neg hpos, dif_neg hpos]

theorem step_mark (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hj : 2 * j < D x) :
    step machine 0 ⟨10, natInt (2 * j), budgetTape x y k u⟩ =
      some ⟨11, natInt (2 * j + 1), budgetTape x y k u⟩ := by
  have hread := budget_marker x y k u j hj
  simp only [step, hread, rule_mark6, writtenTape, moveHead, Option.map_some]
  rw [← hread, update_same, natInt_succ]

theorem step_bit0 (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hw : u.length = x.length) (hj : j < u.length) (hf : u[j] = false) :
    step machine 0 ⟨11, natInt (2 * j + 1), budgetTape x y k u⟩ =
      some ⟨10, natInt (2 * j + 2), budgetTape x y k (u.set j true)⟩ := by
  have hread : budgetTape x y k u (natInt (2 * j + 1)) = 0 := by
    rw [budget_payload x y k u j hj hw, hf, enc_false]
  simp only [step, hread, rule_bit0, writtenTape, moveHead, Option.map_some]
  rw [show (1 : Fin 8) = enc true from rfl, budget_set x y k u j true hj hw,
    natInt_succ]

theorem step_bit1 (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hw : u.length = x.length) (hj : j < u.length) (ht : u[j] = true) :
    step machine 0 ⟨11, natInt (2 * j + 1), budgetTape x y k u⟩ =
      some ⟨12, natInt (2 * j + 2), budgetTape x y k (u.set j false)⟩ := by
  have hread : budgetTape x y k u (natInt (2 * j + 1)) = 1 := by
    rw [budget_payload x y k u j hj hw, ht, enc_true]
  simp only [step, hread, rule_bit1, writtenTape, moveHead, Option.map_some]
  rw [show (0 : Fin 8) = enc false from rfl, budget_set x y k u j false hj hw,
    natInt_succ]

theorem step_under (x y : List Bool) (k : ℕ) (u : List Bool) :
    step machine 0 ⟨10, natInt (D x), budgetTape x y k u⟩ =
      some ⟨13, natInt (D x + 1),
        Function.update (budgetTape x y k u) (natInt (D x)) 2⟩ := by
  have hread := budget_SEP x y k u
  simp only [step, hread, rule_under, writtenTape, moveHead, Option.map_some]
  rw [natInt_succ]

theorem step_backSEP (x y : List Bool) (k : ℕ) (u : List Bool) :
    step machine 0 ⟨12, natInt (D x), budgetTape x y k u⟩ =
      some ⟨8, natInt (D x + 1), budgetTape x y k u⟩ := by
  have hread := budget_SEP x y k u
  simp only [step, hread, rule_backSEP, writtenTape, moveHead, Option.map_some]
  rw [← hread, update_same, natInt_succ]

theorem step_zero (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hw : u.length = x.length) (hj : j < u.length) (hf : u[j] = false) :
    run machine (ticks 2) ⟨10, natInt (2 * j), budgetTape x y k u⟩ =
      some ⟨10, natInt (2 * j + 2), budgetTape x y k (u.set j true)⟩ := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  have hjD : 2 * j < D x := by simp [D]; omega
  rw [show ticks 2 = ticks 1 ++ ticks 1 by rw [h2, ticks_add]]
  rw [run_append, run_ticks_one, step_mark x y k u j hjD, Option.bind_some,
    run_ticks_one, step_bit0 x y k u j hw hj hf]

theorem step_one (x y : List Bool) (k : ℕ) (u : List Bool) (j : ℕ)
    (hw : u.length = x.length) (hj : j < u.length) (ht : u[j] = true) :
    run machine (ticks 2) ⟨10, natInt (2 * j), budgetTape x y k u⟩ =
      some ⟨12, natInt (2 * j + 2), budgetTape x y k (u.set j false)⟩ := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  have hjD : 2 * j < D x := by simp [D]; omega
  rw [show ticks 2 = ticks 1 ++ ticks 1 by rw [h2, ticks_add]]
  rw [run_append, run_ticks_one, step_mark x y k u j hjD, Option.bind_some,
    run_ticks_one, step_bit1 x y k u j hw hj ht]

theorem walk_zeros (x y : List Bool) (k : ℕ) (u : List Bool) (t : ℕ)
    (hw : u.length = x.length) (ht : t ≤ u.length)
    (hf : ∀ i : ℕ, (hi : i < t) → u[i]'(Nat.lt_of_lt_of_le hi ht) = false) :
    run machine (ticks (2 * t)) ⟨10, 0, budgetTape x y k u⟩ =
      some ⟨10, natInt (2 * t), budgetTape x y k (pref u t)⟩ := by
  induction t with
  | zero => simp [ticks, pref_zero, natInt]
  | succ t ih =>
      have ht' : t < u.length := by omega
      have hf0 : u[t]'(ht') = false := hf t (Nat.lt_succ_self t)
      have hlen : (pref u t).length = x.length := by
        rw [pref_length_le u t (le_of_lt ht'), hw]
      have hfalse : (pref u t)[t]'(by rw [pref_length_le u t (le_of_lt ht')]; exact ht') =
          false := by
        have hg := pref_get_ge u t t le_rfl ht'
        exact hg.trans hf0
      rw [show 2 * (t + 1) = 2 * t + 2 by omega, ticks_add, run_append,
        ih (by omega) (fun i hi => hf i (Nat.lt_trans hi (Nat.lt_succ_self t))),
        Option.bind_some]
      have hstep := step_zero x y k (pref u t) t hlen
        (by rw [pref_length_le u t (le_of_lt ht')]; exact ht') hfalse
      rw [pref_succ u t ht'] at hstep
      exact hstep

theorem back_to_SEP (x y : List Bool) (k : ℕ) (u : List Bool) (p : ℕ)
    (hp : p ≤ D x) :
    run machine (ticks (D x - p)) ⟨12, natInt p, budgetTape x y k u⟩ =
      some ⟨12, natInt (D x), budgetTape x y k u⟩ := by
  have hs := scan_right (M := machine) (q := (12 : Fin 19))
    (t := budgetTape x y k u) (h := natInt p) (n := D x - p)
  have hc : natInt p + ((D x - p : ℕ) : Int) = natInt (D x) := by
    unfold natInt; omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hp' : natInt p + (i : Int) = natInt (p + i) := by unfold natInt; omega
  rw [hp']
  have hlt : p + i < D x := by omega
  exact rule_back_not _ (budget_ne_SEP_lt x y k u (p + i) hlt)

theorem borrow_value_original {u v : List Bool}
    (hb : borrowBits u = some v) :
    v.length = u.length ∧
    PakFixedWeightedStandardBinaryCount.value v + 1 =
      PakFixedWeightedStandardBinaryCount.value u := by
  refine ⟨borrow_length hb, ?_⟩
  rw [← value_eq_original, ← value_eq_original]
  exact borrow_value hb

theorem borrow_success (x y u v : List Bool) (k : Nat)
    (hk : k ≤ y.length) (hwidth : u.length = x.length)
    (hb : borrowBits u = some v) :
    run machine (ticks (D x + 1)) ⟨10, 0, budgetTape x y k u⟩ =
      some ⟨8, ((D x + 1 : Nat) : Int), budgetTape x y k v⟩ := by
  set t := zeroPrefix u
  have hlt := some_lt hb
  have hv := some_word hb
  have hlenp : (pref u t).length = x.length := by
    rw [pref_length_le u t (le_of_lt hlt), hwidth]
  have htp : t < (pref u t).length := by
    rw [pref_length_le u t (le_of_lt hlt)]; exact hlt
  have htrue : (pref u t)[t]'(htp) = true := by
    have hg := pref_get_ge u t t le_rfl hlt
    exact hg.trans (zeroPrefix_stop u hlt)
  have hle : 2 * t + 2 ≤ D x := by simp [D]; omega
  have hfuel : D x + 1 = (2 * t + 2) + ((D x - (2 * t + 2)) + 1) := by omega
  rw [show ticks (D x + 1) =
        ticks (2 * t + 2) ++ ticks (D x - (2 * t + 2)) ++ ticks 1 by
      simp [hfuel, ticks_add, List.append_assoc]]
  rw [ticks_add (2 * t) 2]
  rw [run_append, run_append, run_append,
    walk_zeros x y k u t hwidth (le_of_lt hlt)
      (fun i hi => zeroPrefix_get u i hi),
    Option.bind_some, step_one x y k (pref u t) t hlenp htp htrue,
    Option.bind_some]
  rw [← hv]
  have hscan := back_to_SEP x y k v (2 * t + 2) hle
  rw [hscan, Option.bind_some, run_ticks_one, step_backSEP]

theorem borrow_underflow (x y u : List Bool) (k : Nat)
    (hk : k ≤ y.length) (hwidth : u.length = x.length)
    (hb : borrowBits u = none) :
    run machine (ticks (D x + 1)) ⟨10, 0, budgetTape x y k u⟩ =
      some ⟨13, ((D x + 1 : Nat) : Int),
        Function.update (budgetTape x y k (List.replicate x.length true))
          ((D x : Nat) : Int) 2⟩ := by
  have hz := none_len u hb
  have hf : ∀ i : ℕ, (hi : i < u.length) →
      u[i]'(hi) = false := none_false u hb
  have hfuel : D x + 1 = 2 * x.length + 1 := by simp [D]
  rw [show ticks (D x + 1) = ticks (2 * x.length) ++ ticks 1 by
      simp [hfuel, ticks_add]]
  rw [run_append]
  have hwalk := walk_zeros x y k u u.length hwidth le_rfl
    (fun i hi => hf i (by omega : i < u.length))
  rw [show 2 * u.length = 2 * x.length by omega] at hwalk
  rw [hwalk, Option.bind_some, run_ticks_one]
  rw [pref_all, hwidth]
  have hD : natInt (2 * x.length) = natInt (D x) := rfl
  rw [hD]
  exact step_under x y k (List.replicate x.length true)

end PakFixedPolyomino.StandardBitUnaryBudgetBorrow
