import PakFixedPolyomino.StandardBitMarkedCompaction

/-! Physical end-marker, destination-marker and left-sentinel cleanup.
Only finite rule equalities are premises; time and whole-tape output are proved. -/
namespace PakFixedPolyomino.StandardBitMarkedCleanup
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitPairCompactionTape StandardBitMarkedCompaction
open FiniteOneTapeSemantics (moveHead writtenTape)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def CleanupRules (M : DeterministicMachine 17 8) : Prop :=
  (∀ a, M.rule 13 a 0 = if a = 4 then some ⟨2,14,.left⟩ else some ⟨a,13,.left⟩) ∧
  (∀ a, M.rule 14 a 0 = if a = 3 then some ⟨2,0,.right⟩ else some ⟨a,14,.left⟩)

def endErased (x y : List Bool) : Int → Fin 8 :=
  Function.update (tape x y x.length) ((pairBits x y).length : Int) 2

def returnTape (x : List Bool) : Int → Fin 8 :=
  Function.update (inputTape StandardBitPairProjection.machine x) (-1) 3

def finalConfig (x : List Bool) : Configuration 17 8 :=
  ⟨0,0,inputTape StandardBitPairProjection.machine x⟩

theorem complete_gap (x y : List Bool) (i : Nat)
    (hlo : x.length < i) (hhi : i < (pairBits x y).length) :
    tape x y x.length (i : Int) = 2 := by
  rw [tape_nat,complete_nat]
  have hp : ¬i < x.length := by omega
  have hd : i ≠ x.length := by omega
  have he : i ≠ (pairBits x y).length := by omega
  simp only [dif_neg hp,if_neg hd,if_neg he]

theorem seek_end_run (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) :
    run M (ticks ((pairBits x y).length-x.length)) (copyConfig x y x.length) =
      some ⟨9,((pairBits x y).length : Int),tape x y x.length⟩ := by
  have hn := pair_length_gt x y
  have hs := scan_right M 9 (tape x y x.length) (x.length : Int)
    ((pairBits x y).length-x.length)
  have hh : (x.length : Int)+(((pairBits x y).length-x.length : Nat) : Int) =
      ((pairBits x y).length : Int) := by omega
  rw [hh] at hs
  apply hs
  intro i hi
  have hc : (x.length : Int)+(i : Int) = ((x.length+i : Nat) : Int) := by omega
  rw [hc,hr.1]
  by_cases hz : i = 0
  · subst i
    simp only [Nat.add_zero,tape_dest]
    decide
  · rw [complete_gap x y (x.length+i) (by omega) (by omega)]
    decide

theorem erase_end_step (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) :
    step M 0 ⟨9,((pairBits x y).length : Int),tape x y x.length⟩ =
      some ⟨13,((pairBits x y).length : Int)-1,endErased x y⟩ := by
  have hq : M.rule 9 5 0 = some ⟨2,13,.left⟩ := by
    rw [hr.1]
    decide
  simp only [step,tape_end x y x.length le_rfl,hq,Option.map_some,moveHead,writtenTape,endErased]

theorem erased_gap (x y : List Bool) (i : Nat)
    (hlo : x.length < i) (hhi : i < (pairBits x y).length) :
    endErased x y (i : Int) = 2 := by
  have he : (i : Int) ≠ ((pairBits x y).length : Int) := by omega
  rw [endErased,Function.update_of_ne he,complete_gap x y i hlo hhi]

theorem erased_dest (x y : List Bool) : endErased x y (x.length : Int) = 4 := by
  have hn := pair_length_gt x y
  have he : (x.length : Int) ≠ ((pairBits x y).length : Int) := by omega
  rw [endErased,Function.update_of_ne he,tape_dest]

theorem find_dest_run (M : DeterministicMachine 17 8) (hr : CleanupRules M)
    (x y : List Bool) :
    run M (ticks ((pairBits x y).length-x.length-1))
      ⟨13,((pairBits x y).length : Int)-1,endErased x y⟩ =
      some ⟨13,(x.length : Int),endErased x y⟩ := by
  have hn := pair_length_gt x y
  have hs := scan_left M 13 (endErased x y) (((pairBits x y).length : Int)-1)
    ((pairBits x y).length-x.length-1)
  have hh : ((pairBits x y).length : Int)-1-
      (((pairBits x y).length-x.length-1 : Nat) : Int) = (x.length : Int) := by omega
  rw [hh] at hs
  apply hs
  intro i hi
  have hc : ((pairBits x y).length : Int)-1-(i : Int) =
      (((pairBits x y).length-1-i : Nat) : Int) := by omega
  rw [hc,erased_gap x y ((pairBits x y).length-1-i) (by omega) (by omega),hr.1]
  simp only [show (2 : Fin 8) ≠ 4 by decide,if_false]

theorem erase_dest_step (M : DeterministicMachine 17 8) (hr : CleanupRules M)
    (x y : List Bool) :
    step M 0 ⟨13,(x.length : Int),endErased x y⟩ =
      some ⟨14,(x.length : Int)-1,returnTape x⟩ := by
  have hq : M.rule 13 4 0 = some ⟨2,14,.left⟩ := by
    rw [hr.1]
    simp only [ite_true]
  have hu : Function.update (endErased x y) (x.length : Int) 2 = returnTape x :=
    complete_erase x y
  simp only [step,erased_dest,hq,Option.map_some,moveHead,writtenTape,hu]

theorem return_nat (x : List Bool) (i : Nat) :
    returnTape x (i : Int) = inputTape StandardBitPairProjection.machine x (i : Int) := by
  rw [returnTape,Function.update_of_ne (by omega)]

theorem return_not_L (x : List Bool) (i : Nat) : returnTape x (i : Int) ≠ 3 := by
  rw [return_nat]
  by_cases hi : i < x.length
  · rw [inputTape_ofNat _ x i hi]
    cases x[i] <;> decide
  · rw [inputTape_ge _ x _ (by omega),StandardBitPairProjection.machine_blank]
    decide

theorem find_L_run (M : DeterministicMachine 17 8) (hr : CleanupRules M)
    (x : List Bool) :
    run M (ticks x.length) ⟨14,(x.length : Int)-1,returnTape x⟩ =
      some ⟨14,-1,returnTape x⟩ := by
  have hs := scan_left M 14 (returnTape x) ((x.length : Int)-1) x.length
  have hh : (x.length : Int)-1-(x.length : Int) = -1 := by omega
  rw [hh] at hs
  apply hs
  intro i hi
  have hc : (x.length : Int)-1-(i : Int) = ((x.length-1-i : Nat) : Int) := by omega
  rw [hc,hr.2,if_neg (return_not_L x (x.length-1-i))]

theorem erase_L_step (M : DeterministicMachine 17 8) (hr : CleanupRules M)
    (x : List Bool) : step M 0 ⟨14,-1,returnTape x⟩ = some (finalConfig x) := by
  have hq : M.rule 14 3 0 = some ⟨2,0,.right⟩ := by
    rw [hr.2]
    simp only [ite_true]
  have ht : Function.update (returnTape x) (-1) 2 = inputTape StandardBitPairProjection.machine x := by
    rw [returnTape,Function.update_idem]
    apply Function.update_eq_self_iff.mpr
    rw [inputTape_neg _ x (-1) (by decide)]
    rfl
  have hl : returnTape x (-1) = 3 := by simp [returnTape]
  simp only [step,hl,hq,Option.map_some,moveHead,writtenTape,ht,finalConfig]
  rfl

theorem cleanup_run (M : DeterministicMachine 17 8) (hc : CycleRules M)
    (hr : CleanupRules M) (x y : List Bool) :
    run M (ticks (2*(pairBits x y).length-x.length+2)) (copyConfig x y x.length) =
      some (finalConfig x) := by
  have hn := pair_length_gt x y
  have ht : 2*(pairBits x y).length-x.length+2 =
      ((pairBits x y).length-x.length)+1+
      ((pairBits x y).length-x.length-1)+1+x.length+1 := by omega
  rw [ht,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    ticks_add,run_append,seek_end_run M hc x y,Option.bind_some,run_ticks_one,
    erase_end_step M hc x y,Option.bind_some,find_dest_run M hr x y,Option.bind_some,
    run_ticks_one,erase_dest_step M hr x y,Option.bind_some,find_L_run M hr x,
    Option.bind_some,run_ticks_one,erase_L_step M hr x]

end PakFixedPolyomino.StandardBitMarkedCleanup
