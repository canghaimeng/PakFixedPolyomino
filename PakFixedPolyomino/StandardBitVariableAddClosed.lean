import PakFixedPolyomino.StandardBitVariableAddRippleClosed
import PakFixedPolyomino.StandardBitVariableAddSize

/-! Ordinary addition on EVERY raw binary word, on the unchanged concrete
64-state/32-symbol machine. Parsing, every arithmetic epoch, operand wiping,
physical shifting and canonical normalization have exact tape runs. The
malformed branch emits a clean empty word. All actual transition costs are
bounded internally by one fixed polynomial in the original raw length. -/
namespace PakFixedPolyomino.StandardBitVariableAddClosed
open Computability StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitVariableAdd (machine addBits addCarry parseFuel)
open StandardBitVariableAddRipple (rippleFuel)
open StandardBitVariableAddCleanup (cleanupFuel)

def pairFuel (x y : List Bool) : Nat :=
  parseFuel x y+(rippleFuel x y+cleanupFuel x y (addCarry x y false))

theorem pair_run (x y : List Bool) :
    run machine (ticks (pairFuel x y)) (initial machine (pairBits x y))=
      some (StandardBitVariableAddNormalize.finalConfig (addCarry x y false)) := by
  rw [pairFuel,ticks_add,run_append,StandardBitVariableAddRippleInterface.parsed_run,
    Option.bind_some,ticks_add,run_append,StandardBitVariableAddRippleClosed.ripple_run,
    Option.bind_some]
  exact (StandardBitVariableAddSize.sum_cleanup_spec x y).1

theorem pair_output (x y : List Bool) :
    Output machine (addBits (pairBits x y))
      (StandardBitVariableAddNormalize.finalConfig (addCarry x y false)) :=
  (StandardBitVariableAddSize.sum_cleanup_spec x y).2.2

theorem pairFuel_le (x y : List Bool) :
    pairFuel x y≤4096*((pairBits x y).length+1)*((pairBits x y).length+1)*
      ((pairBits x y).length+1) := by
  let a := (pairBits x y).length+1
  have hp := StandardBitVariableAddSize.parseFuel_le x y
  have hr := StandardBitVariableAddRipple.rippleFuel_le x y
  have hc := StandardBitVariableAddSize.cleanup_addFuel_le x y
  have ht : pairFuel x y≤776*a*a := by unfold pairFuel;dsimp [a];nlinarith
  have ha : 0<a := Nat.succ_pos _
  calc
    pairFuel x y≤776*a*a := ht
    _≤4096*a*a := Nat.mul_le_mul_right a
      (Nat.mul_le_mul_right a (by decide : 776≤4096))
    _≤4096*a*a*a := Nat.le_mul_of_pos_right _ ha

theorem add_computes : ComputesWithin machine addBits
    (fun n => 4096*(n+1)*(n+1)*(n+1)) := by
  intro raw
  cases hu : unpairBits raw with
  | none =>
    refine ⟨2*raw.length+4,StandardBitVariableAdd.finalConfig [],
      StandardBitVariableAdd.cubic_ge_linear _,StandardBitVariableAdd.mal_run raw hu,?_⟩
    rw [StandardBitVariableAdd.add_none raw hu]
    exact ⟨rfl,rfl,rfl⟩
  | some xy =>
    rcases xy with ⟨x,y⟩
    have he := StandardBitPairProjection.unpairBits_eq_some.mp hu
    subst raw
    exact ⟨pairFuel x y,StandardBitVariableAddNormalize.finalConfig (addCarry x y false),
      pairFuel_le x y,pair_run x y,pair_output x y⟩

theorem add_polyBitTime : PolyBitTime addBits := by
  refine ⟨64,32,machine,4096*(Polynomial.X+1)*(Polynomial.X+1)*(Polynomial.X+1),?_⟩
  simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one] using add_computes

theorem add_spec : PolyBitTime addBits ∧
    ComputesWithin machine addBits (fun n => 4096*(n+1)*(n+1)*(n+1)) ∧
    (∀ x y,addBits (pairBits x y)=
      encodeNat (PakFixedWeightedStandardBinaryCount.value x+PakFixedWeightedStandardBinaryCount.value y)) ∧
    (∀ raw,unpairBits raw=none → addBits raw=[]) :=
  ⟨add_polyBitTime,add_computes,StandardBitVariableAdd.add_pair,StandardBitVariableAdd.add_none⟩

end PakFixedPolyomino.StandardBitVariableAddClosed
