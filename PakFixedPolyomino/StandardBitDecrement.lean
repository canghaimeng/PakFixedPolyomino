import PakFixedPolyomino.StandardBitDecrementWord
import PakFixedPolyomino.StandardBitMarkedCompaction
import PakFixedPolyomino.StandardBitIncrement

/-! Eight states and four symbols implement saturated little-endian decrement.
The high zero digits of positive raw words are retained literally. -/
namespace PakFixedPolyomino.StandardBitDecrement
open StandardNondeterministicMachine StandardBitTime StandardBitDecrementWord
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitMarkedCompaction (scan_right scan_left)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def machine : DeterministicMachine 8 4 where
  rule := fun q a _ =>
    if q = 2 then some ⟨a,3,.left⟩
    else if q = 3 then some ⟨3,4,.right⟩
    else if q = 4 then
      if a = 0 then some ⟨1,4,.right⟩
      else if a = 1 then some ⟨0,5,.right⟩
      else some ⟨2,7,.left⟩
    else if q = 5 then
      if a = 2 then some ⟨2,6,.left⟩ else some ⟨a,5,.right⟩
    else if q = 6 then
      if a = 3 then some ⟨2,0,.right⟩ else some ⟨a,6,.left⟩
    else if q = 7 then
      if a = 3 then some ⟨2,0,.right⟩ else some ⟨2,7,.left⟩
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

def marked (y : List Bool) : Int → Fin 4 := Function.update (inputTape machine y) (-1) 3
def phaseTape (x : List Bool) (k : Nat) : Int → Fin 4 :=
  Function.update (fun z => if 0 ≤ z ∧ z.toNat < k then 1 else inputTape machine x z) (-1) 3
def scanConfig (x : List Bool) (k : Nat) : Configuration 8 4 := ⟨4,k,phaseTape x k⟩
def finalConfig (y : List Bool) : Configuration 8 4 := ⟨0,0,inputTape machine y⟩

theorem phase_read (x : List Bool) (k : Nat) :
    phaseTape x k (k : Int) = inputTape machine x (k : Int) := by
  simp [phaseTape,Function.update_apply]

theorem phase_write (x : List Bool) (k : Nat) :
    Function.update (phaseTape x k) (k : Int) 1 = phaseTape x (k+1) := by
  funext z
  by_cases hL : z = -1
  · subst z
    simp [phaseTape,Function.update_apply]
  · by_cases hk : z = (k : Int)
    · subst z
      simp [phaseTape,Function.update_apply]
    · have hc : (0 ≤ z ∧ z.toNat < k+1) ↔ (0 ≤ z ∧ z.toNat < k) := by
        by_cases hz : 0 ≤ z
        · have hn : z.toNat ≠ k := by omega
          omega
        · simp [hz]
      simp only [Function.update_apply,if_neg hk,phaseTape,if_neg hL,hc]

theorem setup_run (x : List Bool) :
    run machine (ticks 2) (initial machine x) = some (scanConfig x 0) := by
  have ht : Function.update (inputTape machine x) 0 (inputTape machine x 0) = inputTape machine x :=
    Function.update_eq_self_iff.mpr rfl
  have hu : phaseTape x 0 = marked x := by simp [phaseTape,marked]
  simp [ticks,run,step,machine,initial,scanConfig,moveHead,writtenTape,ht,hu,marked]

theorem scan_step (x : List Bool) (k : Nat) (hk : k < zeroPrefix x) :
    step machine 0 (scanConfig x k) = some (scanConfig x (k+1)) := by
  have hl : k < x.length := hk.trans_le (zeroPrefix_le x)
  have hr : inputTape machine x (k : Int) = 0 := by
    rw [inputTape_ofNat machine x k hl,zeroPrefix_get x k hk]
    rfl
  have hq : machine.rule 4 0 0 = some ⟨1,4,.right⟩ := by simp [machine]
  have hh : (k : Int)+1 = ((k+1 : Nat) : Int) := by omega
  simp only [step,scanConfig,phase_read,hr,hq,Option.map_some,moveHead,writtenTape,phase_write,hh]

theorem scan_run (x : List Bool) (k : Nat) (hk : k ≤ zeroPrefix x) :
    run machine (ticks k) (scanConfig x 0) = some (scanConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one,scan_step x k (by omega)]

theorem positive_tape_nat (x : List Bool) (h : zeroPrefix x < x.length) (i : Nat) :
    inputTape machine (decrementBits x) (i : Int) =
      if i < zeroPrefix x then 1 else if i = zeroPrefix x then 0 else inputTape machine x (i : Int) := by
  by_cases hl : i < zeroPrefix x
  · have ho : i < (decrementBits x).length := by rw [decrement_length h]; omega
    have hb := StandardBitIncrement.get_of_getElem? (h := ho) (decrement_get_lt h i hl)
    rw [if_pos hl,inputTape_ofNat machine _ i ho,hb]
    rfl
  · rw [if_neg hl]
    by_cases he : i = zeroPrefix x
    · subst i
      have ho : zeroPrefix x < (decrementBits x).length := by rw [decrement_length h]; exact h
      have hb := StandardBitIncrement.get_of_getElem? (h := ho) (decrement_get_eq h)
      rw [if_pos rfl,inputTape_ofNat machine _ _ ho,hb]
      rfl
    · rw [if_neg he]
      by_cases hi : i < x.length
      · have ho : i < (decrementBits x).length := by rw [decrement_length h]; exact hi
        have hb := StandardBitIncrement.get_of_getElem? (h := ho)
          ((decrement_get_gt h i (by omega)).trans (List.getElem?_eq_getElem hi))
        rw [inputTape_ofNat machine _ i ho,inputTape_ofNat machine x i hi,hb]
      · rw [inputTape_ge machine _ _ (by rw [decrement_length h]; exact_mod_cast Nat.not_lt.mp hi),
          inputTape_ge machine x _ (by exact_mod_cast Nat.not_lt.mp hi)]

theorem phase_turn (x : List Bool) (h : zeroPrefix x < x.length) :
    Function.update (phaseTape x (zeroPrefix x)) (zeroPrefix x : Int) 0 = marked (decrementBits x) := by
  funext z
  by_cases hL : z = -1
  · subst z
    have hp : (-1 : Int) ≠ (zeroPrefix x : Int) := by omega
    simp only [Function.update_apply,if_neg hp,phaseTape,marked,ite_true]
  · by_cases hz : 0 ≤ z
    · lift z to Nat using hz with i
      have hLi : (i : Int) ≠ -1 := by omega
      simp only [Function.update_apply,phaseTape,marked,if_neg hLi,positive_tape_nat x h i]
      by_cases hi : i = zeroPrefix x
      · subst i
        simp
      · have hc : (i : Int) ≠ (zeroPrefix x : Int) := by omega
        simp only [if_neg hc]
        have hz' : 0 ≤ (i : Int) := by omega
        simp only [hz',Int.toNat_natCast,true_and,if_neg hi]
    · have hp : z ≠ (zeroPrefix x : Int) := by omega
      simp only [Function.update_apply,if_neg hp,phaseTape,marked,if_neg hL,
        show ¬(0 ≤ z ∧ z.toNat < zeroPrefix x) by omega,if_false]
      rw [inputTape_neg machine x z (by omega),inputTape_neg machine (decrementBits x) z (by omega)]

theorem positive_turn (x : List Bool) (h : zeroPrefix x < x.length) :
    step machine 0 (scanConfig x (zeroPrefix x)) =
      some ⟨5,((zeroPrefix x+1 : Nat) : Int),marked (decrementBits x)⟩ := by
  have hr : inputTape machine x (zeroPrefix x : Int) = 1 := by
    rw [inputTape_ofNat machine x _ h,zeroPrefix_stop x h]
    rfl
  have hq : machine.rule 4 1 0 = some ⟨0,5,.right⟩ := by simp [machine]
  have hh : (zeroPrefix x : Int)+1 = ((zeroPrefix x+1 : Nat) : Int) := by omega
  simp only [step,scanConfig,phase_read,hr,hq,Option.map_some,moveHead,writtenTape,phase_turn x h,hh]

theorem marked_nat (y : List Bool) (i : Nat) :
    marked y (i : Int) = inputTape machine y (i : Int) := by
  rw [marked,Function.update_of_ne (by omega)]

theorem marked_not_L (y : List Bool) (i : Nat) : marked y (i : Int) ≠ 3 := by
  rw [marked_nat]
  by_cases hi : i < y.length
  · rw [inputTape_ofNat machine y i hi]
    cases y[i] <;> decide
  · rw [inputTape_ge machine y _ (by omega)]
    decide

theorem marked_not_blank (y : List Bool) (i : Nat) (hi : i < y.length) :
    marked y (i : Int) ≠ 2 := by
  rw [marked_nat,inputTape_ofNat machine y i hi]
  cases y[i] <;> decide

theorem seek_end_run (y : List Bool) (h : Nat) (hh : h ≤ y.length) :
    run machine (ticks (y.length-h)) ⟨5,h,marked y⟩ =
      some ⟨5,y.length,marked y⟩ := by
  have hs := scan_right machine 5 (marked y) (h : Int) (y.length-h)
  have hc : (h : Int)+((y.length-h : Nat) : Int) = (y.length : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hc' : (h : Int)+(i : Int) = ((h+i : Nat) : Int) := by omega
  rw [hc']
  simp [machine]
  simpa only [Nat.cast_add] using marked_not_blank y (h+i) (by omega)

theorem end_turn (y : List Bool) :
    step machine 0 ⟨5,y.length,marked y⟩ = some ⟨6,(y.length : Int)-1,marked y⟩ := by
  have hr : marked y (y.length : Int) = 2 := by
    rw [marked_nat,inputTape_ge machine y _ (by omega)]
    rfl
  have hq : machine.rule 5 2 0 = some ⟨2,6,.left⟩ := by simp [machine]
  have ht : Function.update (marked y) (y.length : Int) 2 = marked y :=
    Function.update_eq_self_iff.mpr hr.symm
  simp only [step,hr,hq,Option.map_some,moveHead,writtenTape,ht]

theorem return_run (y : List Bool) :
    run machine (ticks y.length) ⟨6,(y.length : Int)-1,marked y⟩ =
      some ⟨6,-1,marked y⟩ := by
  have hs := scan_left machine 6 (marked y) ((y.length : Int)-1) y.length
  have hc : (y.length : Int)-1-(y.length : Int) = -1 := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hc' : (y.length : Int)-1-(i : Int) = ((y.length-1-i : Nat) : Int) := by omega
  rw [hc']
  simp [machine,marked_not_L y (y.length-1-i)]

theorem erase_L (y : List Bool) (q : Fin 8) (hq : q = 6 ∨ q = 7) :
    step machine 0 ⟨q,-1,marked y⟩ = some (finalConfig y) := by
  have hr : marked y (-1) = 3 := by simp [marked]
  have ht : Function.update (marked y) (-1) 2 = inputTape machine y := by
    rw [marked,Function.update_idem]
    apply Function.update_eq_self_iff.mpr
    rw [inputTape_neg machine y (-1) (by decide)]
    rfl
  have hq' : machine.rule q 3 0 = some ⟨2,0,.right⟩ := by
    rcases hq with rfl | rfl <;> simp [machine]
  simp only [step,hr,hq',Option.map_some,moveHead,writtenTape,ht,finalConfig]
  rfl

theorem finish_run (y : List Bool) (h : Nat) (hh : h ≤ y.length) :
    run machine (ticks ((y.length-h)+y.length+2)) ⟨5,h,marked y⟩ =
      some (finalConfig y) := by
  rw [show (y.length-h)+y.length+2 = (y.length-h)+1+y.length+1 by omega,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    seek_end_run y h hh,Option.bind_some,run_ticks_one,end_turn,Option.bind_some,
    return_run,Option.bind_some,run_ticks_one,erase_L y 6 (Or.inl rfl)]

def wipeTape (j : Nat) : Int → Fin 4 :=
  Function.update (fun z => if 0 ≤ z ∧ z.toNat < j then 1 else 2) (-1) 3

theorem phase_end (x : List Bool) : phaseTape x x.length = wipeTape x.length := by
  funext z
  by_cases hL : z = -1
  · subst z
    simp [phaseTape,wipeTape]
  · simp only [phaseTape,wipeTape,Function.update_apply,if_neg hL]
    split
    · rfl
    · rename_i hz
      by_cases hn : 0 ≤ z
      · rw [inputTape_ge machine x z (by omega)]
        rfl
      · rw [inputTape_neg machine x z (by omega)]
        rfl

theorem wipe_update (j : Nat) :
    Function.update (wipeTape (j+1)) (j : Int) 2 = wipeTape j := by
  funext z
  by_cases hL : z = -1
  · subst z
    have hj : (-1 : Int) ≠ (j : Int) := by omega
    simp [wipeTape,Function.update_apply,hj]
  · by_cases hj : z = (j : Int)
    · subst z
      simp [wipeTape,Function.update_apply]
    · have hc : (0 ≤ z ∧ z.toNat < j+1) ↔ (0 ≤ z ∧ z.toNat < j) := by
        by_cases hz : 0 ≤ z
        · have hn : z.toNat ≠ j := by omega
          omega
        · simp [hz]
      simp only [Function.update_apply,if_neg hj,wipeTape,if_neg hL,hc]

theorem wipe_step (j : Nat) :
    step machine 0 ⟨7,j,wipeTape (j+1)⟩ = some ⟨7,(j : Int)-1,wipeTape j⟩ := by
  have hr : wipeTape (j+1) (j : Int) = 1 := by simp [wipeTape,Function.update_apply]
  have hq : machine.rule 7 1 0 = some ⟨2,7,.left⟩ := by simp [machine]
  simp only [step,hr,hq,Option.map_some,moveHead,writtenTape,wipe_update]

theorem wipe_run (j : Nat) :
    run machine (ticks j) ⟨7,(j : Int)-1,wipeTape j⟩ = some ⟨7,-1,wipeTape 0⟩ := by
  induction j with
  | zero => simp [ticks,run]
  | succ j ih =>
    have hh : ((j+1 : Nat) : Int)-1 = (j : Int) := by omega
    have ht : ticks (j+1) = ticks 1 ++ ticks j := by
      rw [← ticks_add]
      congr 1
      omega
    rw [hh,ht,run_append,run_ticks_one,wipe_step,
      Option.bind_some,ih]

theorem zero_turn (x : List Bool) :
    step machine 0 (scanConfig x x.length) =
      some ⟨7,(x.length : Int)-1,wipeTape x.length⟩ := by
  have hr : inputTape machine x (x.length : Int) = 2 := by
    rw [inputTape_ge machine x _ (by omega)]
    rfl
  have hq : machine.rule 4 2 0 = some ⟨2,7,.left⟩ := by simp [machine]
  have hu : Function.update (phaseTape x x.length) (x.length : Int) 2 = phaseTape x x.length :=
    Function.update_eq_self_iff.mpr ((phase_read x x.length).trans hr).symm
  simp only [step,scanConfig,phase_read,hr,hq,Option.map_some,moveHead,writtenTape,hu]
  rw [phase_end]

theorem wipe_zero : wipeTape 0 = marked [] := by
  funext z
  simp [wipeTape,marked,Function.update_apply,inputTape,machine]

theorem positive_run (x : List Bool) (h : zeroPrefix x < x.length) :
    run machine (ticks (2*x.length+4)) (initial machine x) = some (finalConfig (decrementBits x)) := by
  have hn : (decrementBits x).length = x.length := decrement_length h
  have ht : 2*x.length+4 =
      2+zeroPrefix x+1+(((decrementBits x).length-(zeroPrefix x+1))+(decrementBits x).length+2) := by
    rw [hn]
    omega
  rw [ht,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    setup_run,Option.bind_some,scan_run x (zeroPrefix x) le_rfl,Option.bind_some,
    run_ticks_one,positive_turn x h,Option.bind_some,
    finish_run (decrementBits x) (zeroPrefix x+1) (by rw [hn]; omega)]

theorem zero_run (x : List Bool) (h : zeroPrefix x = x.length) :
    run machine (ticks (2*x.length+4)) (initial machine x) = some (finalConfig (decrementBits x)) := by
  rw [decrement_none h,show 2*x.length+4 = 2+x.length+1+x.length+1 by omega,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    setup_run,Option.bind_some,scan_run x x.length (by omega),Option.bind_some,
    run_ticks_one,zero_turn,Option.bind_some,wipe_run,Option.bind_some,
    run_ticks_one,wipe_zero,erase_L [] 7 (Or.inr rfl)]

theorem machine_run (x : List Bool) :
    run machine (ticks (2*x.length+4)) (initial machine x) = some (finalConfig (decrementBits x)) := by
  by_cases h : zeroPrefix x < x.length
  · exact positive_run x h
  · exact zero_run x (by have := zeroPrefix_le x; omega)

theorem machine_computes : ComputesWithin machine decrementBits (fun n => 2*n+4) := by
  intro x
  exact ⟨2*x.length+4,finalConfig (decrementBits x),le_rfl,machine_run x,rfl,rfl,rfl⟩

theorem decrement_polyBitTime : PolyBitTime decrementBits := by
  refine ⟨8,4,machine,Polynomial.C 2 * Polynomial.X + Polynomial.C 4,?_⟩
  simpa using machine_computes

theorem decrement_spec (x : List Bool) :
    value (decrementBits x) = value x-1 ∧ (decrementBits x).length ≤ x.length ∧
    run machine (ticks (2*x.length+4)) (initial machine x) = some (finalConfig (decrementBits x)) ∧
    Output machine (decrementBits x) (finalConfig (decrementBits x)) ∧
    RunsAtMost machine x (2*x.length+4) := by
  exact ⟨decrement_value x,decrement_length_le x,machine_run x,⟨rfl,rfl,rfl⟩,
    halting_runsAtMost machine x _ _ (machine_run x) rfl⟩

end PakFixedPolyomino.StandardBitDecrement
