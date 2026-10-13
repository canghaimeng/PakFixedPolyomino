import PakFixedPolyomino.StandardBitVariableAddRippleEpoch
import PakFixedPolyomino.StandardBitVariableAddRippleFinish

/-! All arithmetic epochs and the actual closing scan of the frozen 64/32
adder, with complete integer-tape equality and actual transition fuel.
Ordinary parsing and canonical output cleanup are separate stages. -/
namespace PakFixedPolyomino.StandardBitVariableAddRippleClosed
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine addCarry)
open StandardBitVariableAddRipple
open StandardBitVariableAddRippleInterface (parsedStart rippleFinal)

theorem epochs_run (x y : List Bool) (k : Nat)
    (hk : k≤(addCarry x y false).length) :
    run machine (ticks (sumEpochs x y k)) (epochCfg x y 0)=some (epochCfg x y k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sumEpochs,ticks_add,run_append,ih (by omega),Option.bind_some]
    exact StandardBitVariableAddRippleEpoch.epoch_run x y k (by omega)

theorem ripple_run (x y : List Bool) :
    run machine (ticks (rippleFuel x y)) (parsedStart x y)=some (rippleFinal x y) := by
  rw [rippleFuel,ticks_add,run_append,parsed_epoch0,epochs_run x y _ le_rfl,
    Option.bind_some]
  exact StandardBitVariableAddRippleFinish.finish_run x y

theorem ripple_spec :
    (∀ x y,run machine (ticks (rippleFuel x y)) (parsedStart x y)=some (rippleFinal x y)) ∧
    (∀ x y,rippleFuel x y≤512*((StandardBitMetric.pairBits x y).length+1)^2) :=
  ⟨ripple_run,fun x y => by
    simpa only [pow_two,Nat.mul_assoc] using rippleFuel_le x y⟩

end PakFixedPolyomino.StandardBitVariableAddRippleClosed
