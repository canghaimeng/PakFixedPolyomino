import PakFixedPolyomino.StandardBitReverse

/-! Exact ordinary cleanup of the fully marked reversal tape. This module
proves the whole integer tape is restored; the swap epochs are separate. -/
namespace PakFixedPolyomino.StandardBitReverseCleanup
open StandardNondeterministicMachine StandardBitTime StandardBitReverse
open FiniteOneTapeSemantics (moveHead)
set_option maxHeartbeats 800000

def markedTape (y : List Bool) (z : Int) : Fin 8 :=
  if z = -1 then 5
  else if z = (y.length : Int) then 6
  else if h : 0 ≤ z ∧ z.toNat < y.length then marked y[z.toNat] else 2

def cleanTape (y : List Bool) (k : Nat) (z : Int) : Fin 8 :=
  if z = -1 then 5
  else if h : 0 ≤ z ∧ z.toNat < y.length then
    if z.toNat < k then marked y[z.toNat] else bit y[z.toNat]
  else 2

theorem inputTape_shape (y : List Bool) (z : Int) : inputTape machine y z =
    if h : 0 ≤ z ∧ z.toNat < y.length then bit y[z.toNat] else 2 := by
  by_cases h : 0 ≤ z ∧ z.toNat < y.length
  · simp only [dif_pos h,inputTape,dif_pos h.1,dif_pos h.2]
    cases y[z.toNat] <;> rfl
  · by_cases hz : 0 ≤ z
    · have hi : ¬z.toNat < y.length := fun hi => h ⟨hz,hi⟩
      simp [inputTape,h,hz,hi,machine]
    · simp [inputTape,h,hz,machine]

theorem markedTape_nat (y : List Bool) (i : Nat) (hi : i < y.length) :
    markedTape y i = marked y[i] := by
  have hL : (i : Int) ≠ -1 := by omega
  have hR : (i : Int) ≠ (y.length : Int) := by omega
  simp [markedTape,hL,hR,hi]

theorem markedTape_right (y : List Bool) : markedTape y y.length = 6 := by
  have h : (y.length : Int) ≠ -1 := by omega
  simp [markedTape,h]

theorem cleanTape_nat (y : List Bool) (k i : Nat) (hi : i < y.length) :
    cleanTape y k i = if i < k then marked y[i] else bit y[i] := by
  have h : (i : Int) ≠ -1 := by omega
  simp [cleanTape,h,hi]

theorem cleanTape_zero (y : List Bool) : cleanTape y 0 = tapeL y := by
  funext z
  unfold tapeL
  rw [inputTape_shape]
  simp [cleanTape]

theorem markedTape_erase_right (y : List Bool) :
    Function.update (markedTape y) (y.length : Int) 2 = cleanTape y y.length := by
  funext z
  by_cases hR : z = (y.length : Int)
  · subst z
    have hL : (y.length : Int) ≠ -1 := by omega
    simp [cleanTape,hL]
  · simp only [Function.update_of_ne hR]
    unfold markedTape cleanTape
    by_cases hL : z = -1
    · simp [hL]
    · simp only [if_neg hL,if_neg hR]
      split_ifs <;> simp_all

theorem unmark_write (y : List Bool) (k : Nat) (hk : k < y.length) :
    Function.update (cleanTape y (k+1)) (k : Int) (bit y[k]) = cleanTape y k := by
  funext z
  by_cases he : z = (k : Int)
  · subst z
    rw [Function.update_self,cleanTape_nat y k k hk]
    simp
  · rw [Function.update_of_ne he]
    unfold cleanTape
    by_cases hL : z = -1
    · simp [hL]
    · simp only [if_neg hL]
      by_cases hz : 0 ≤ z ∧ z.toNat < y.length
      · have hne : z.toNat ≠ k := by
          intro h
          exact he ((Int.toNat_of_nonneg hz.1).symm.trans (congrArg Nat.cast h))
        have ht : z.toNat < k+1 ↔ z.toNat < k := by omega
        simp only [dif_pos hz]
        exact if_congr ht rfl rfl
      · simp [hz]

theorem unmark_step (y : List Bool) (k : Nat) (hk : k < y.length) :
    step machine 0 (tapeConfig 13 k (cleanTape y (k+1))) =
      some (tapeConfig 13 ((k : Int)-1) (cleanTape y k)) := by
  have hread : cleanTape y (k+1) k = marked y[k] := by
    rw [cleanTape_nat y (k+1) k hk]; simp
  have hstep := step_write 13 13 k (cleanTape y (k+1)) (bit y[k]) .left
    (by simpa [hread] using rule13_marked y[k])
  simpa [moveHead,unmark_write y k hk] using hstep

theorem unmark_run (y : List Bool) (m : Nat) (hm : m ≤ y.length) :
    run machine (ticks m) (tapeConfig 13 ((m : Int)-1) (cleanTape y m)) =
      some (tapeConfig 13 (-1) (cleanTape y 0)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hh : ((m+1 : Nat) : Int)-1 = (m : Int) := by omega
    change run machine (0::ticks m) _ = _
    rw [hh,run_cons,unmark_step y m (by omega),Option.bind_some]
    exact ih (by omega)

theorem scan_marked_run (y : List Bool) :
    run machine (ticks y.length) (tapeConfig 6 0 (markedTape y)) =
      some (tapeConfig 6 y.length (markedTape y)) := by
  have hh : (0 : Int)+y.length = y.length := by omega
  rw [← hh]
  refine scan_right 6 0 (markedTape y) y.length ?_
  intro p hp
  simpa only [Int.zero_add,markedTape_nat y p hp] using rule6_marked y[p]

theorem cleanup_turn (y : List Bool) :
    step machine 0 (tapeConfig 6 y.length (markedTape y)) =
      some (tapeConfig 13 ((y.length : Int)-1) (cleanTape y y.length)) := by
  have hstep := step_write 6 13 y.length (markedTape y) 2 .left
    (by simpa [markedTape_right] using rule6_sentR)
  simpa [moveHead,markedTape_erase_right] using hstep

theorem cleanup_end (y : List Bool) :
    step machine 0 (tapeConfig 13 (-1) (cleanTape y 0)) =
      some (tapeConfig 0 0 (inputTape machine y)) := by
  have ht : Function.update (cleanTape y 0) (-1) 2 = inputTape machine y := by
    rw [cleanTape_zero]
    funext z
    by_cases h : z = -1
    · subst z
      simp [Function.update_self,inputTape_neg machine y (-1) (by omega)]
    · simp [Function.update_of_ne h,tapeL,h]
  have hread : cleanTape y 0 (-1) = 5 := by simp [cleanTape]
  have hstep := step_write 13 0 (-1) (cleanTape y 0) 2 .right
    (by simpa [hread] using rule13_sent)
  simpa [moveHead,ht] using hstep

theorem cleanup_marked_run (y : List Bool) :
    run machine (ticks (2*y.length+2)) (tapeConfig 6 0 (markedTape y)) =
      some (tapeConfig 0 0 (inputTape machine y)) := by
  have hf : 2*y.length+2 = y.length+1+y.length+1 := by omega
  rw [hf,ticks_add,ticks_add,ticks_add,run_append,run_append,run_append,
    scan_marked_run,Option.bind_some,run_ticks_one,cleanup_turn,Option.bind_some,
    unmark_run y y.length le_rfl,Option.bind_some,run_ticks_one,cleanup_end]

theorem epochTape_fully_marked (x : List Bool) (k : Nat) (hk : x.length ≤ 2*k) :
    epochTape x k = markedTape x.reverse := by
  funext z
  by_cases hL : z = -1
  · simp [epochTape,markedTape,hL]
  · by_cases hR : z = (x.length : Int)
    · simp [epochTape,markedTape,hR,List.length_reverse]
    · by_cases hz : 0 ≤ z ∧ z.toNat < x.length
      · have hmark : z.toNat < k ∨ x.length-k ≤ z.toNat := by omega
        simp only [epochTape,markedTape,hL,hR,List.length_reverse,if_false,
          dif_pos hz,if_pos hmark,List.getElem_reverse]
      · simp [epochTape,markedTape,hL,hR,hz,List.length_reverse]

theorem cleanup_run (x : List Bool) (k : Nat) (hk : x.length ≤ 2*k) :
    run machine (ticks (cleanupFuel x.length)) (epochConfig x k) = some (finalConfig x) := by
  have ht := epochTape_fully_marked x k hk
  simpa [cleanupFuel,epochConfig,tapeConfig,ht,finalConfig] using cleanup_marked_run x.reverse

end PakFixedPolyomino.StandardBitReverseCleanup
