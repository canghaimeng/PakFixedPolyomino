import PakFixedPolyomino.StandardBitVariableAddRipple

/-! Actual closing scan of the frozen 64/32 adder. This starts AFTER all
arithmetic epochs, on the entire last epoch tape, and reaches state26/E.
The preceding arithmetic epochs are a separate operational obligation. -/
namespace PakFixedPolyomino.StandardBitVariableAddRippleFinish
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine addCarry D Epos update_same)
open StandardBitVariableAddRipple
open StandardBitVariableAddRippleInterface
open StandardBitMarkedCompaction (scan_right)

theorem finish_x (x y : List Bool) :
    run machine (ticks (2*x.length+1))
      (epochCfg x y (addCarry x y false).length) =
      some ⟨huntYdoneQ false,(D x : Int),epochTape x y (addCarry x y false).length⟩ := by
  let m := (addCarry x y false).length
  have hx : x.length ≤ m := (le_max_left x.length y.length).trans (addCarry_len_ge x y false)
  have hs := huntX_skip_ge x y m hx
  have ht : epochTape x y m ((2*x.length : Nat) : Int)=4 := by
    unfold epochTape
    exact tape_sep x y _ _ _
  have hc : carryInto x y m=false := carryInto_done x y
  unfold epochCfg
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  have hr := step_right (huntQ (carryInto x y m)) (huntYdoneQ (carryInto x y m))
    (epochTape x y m) ((2*x.length : Nat) : Int) 4 (by rw [ht];exact rule_hX_sep _)
  rw [hr,hc,← ht,update_same]
  congr 2

theorem finish_y (x y : List Bool) :
    run machine (ticks y.length)
      (⟨huntYdoneQ false,(D x : Int),epochTape x y (addCarry x y false).length⟩ : Configuration 64 32) =
      some ⟨huntYdoneQ false,(Epos x y : Int),epochTape x y (addCarry x y false).length⟩ := by
  let m := (addCarry x y false).length
  have hy : y.length ≤ m := (le_max_right x.length y.length).trans (addCarry_len_ge x y false)
  have hs := scan_right machine (huntYdoneQ false) (epochTape x y m) (D x : Int) y.length
  have hc : (D x : Int)+(y.length : Int)=(Epos x y : Int) := by simp [Epos]
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (D x : Int)+(i : Int)=((D x+i : Nat) : Int) := by omega
  rw [hh]
  have ht : epochTape x y m ((D x+i : Nat) : Int)=8 := by
    unfold epochTape
    rw [Nat.min_eq_right hy]
    exact tape_y_cons x y _ y.length _ i hi hi
  rw [ht]
  exact rule_hYdone_skip false 8 (Or.inr rfl)

theorem finish_end (x y : List Bool) :
    step machine 0
      (⟨huntYdoneQ false,(Epos x y : Int),epochTape x y (addCarry x y false).length⟩ : Configuration 64 32) =
      some (rippleFinal x y) := by
  have ht : epochTape x y (addCarry x y false).length (Epos x y : Int)=5 := by
    unfold epochTape
    exact tape_E x y _ _ _
  have hs := step_stay (huntYdoneQ false) 26
    (epochTape x y (addCarry x y false).length) (Epos x y : Int) 5
    (by rw [ht];exact rule_hYdone_E0)
  rw [hs,← ht,update_same,epoch_final]
  rfl

theorem finish_run (x y : List Bool) :
    run machine (ticks (finishFuel x y))
      (epochCfg x y (addCarry x y false).length)=some (rippleFinal x y) := by
  have hf : finishFuel x y=(2*x.length+1)+(y.length+1) := by simp [finishFuel,Epos,D];omega
  rw [hf,ticks_add,run_append,finish_x,Option.bind_some,ticks_add,run_append,
    finish_y,Option.bind_some,run_ticks_one,finish_end]

end PakFixedPolyomino.StandardBitVariableAddRippleFinish
