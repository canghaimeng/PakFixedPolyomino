import PakFixedPolyomino.StandardBitVariableAddCleanup

/-! Literal word-length and physical cleanup bounds for the frozen adder.
These start at the exact ripple boundary; the ordinary input closure also
uses the physical ripple proof from StandardBitVariableAddRipple. -/
namespace PakFixedPolyomino.StandardBitVariableAddSize
open StandardNondeterministicMachine StandardBitTime
open StandardBitMetric (pairBits pairBits_length)
open StandardBitVariableAdd (machine addCarry addBits parseFuel Epos D)
open StandardBitVariableAddCleanup (cleanupFuel cleanup_run cleanupFuel_le)
open StandardBitVariableAddRippleInterface (resultTape)

theorem addCarry_length (x y : List Bool) (c : Bool) :
    (addCarry x y c).length≤x.length+y.length+1 := by
  induction x generalizing y c with
  | nil =>
    induction y generalizing c with
    | nil => cases c <;> simp [addCarry]
    | cons b y ih => simpa only [addCarry,List.length_cons,List.length_nil,Nat.zero_add]
        using Nat.succ_le_succ (ih (StandardBitVariableAdd.maj false b c))
  | cons a x ih =>
    cases y with
    | nil => simpa only [addCarry,List.length_cons,List.length_nil,Nat.add_zero]
        using Nat.succ_le_succ (ih [] (StandardBitVariableAdd.maj a false c))
    | cons b y =>
      have h := ih y (StandardBitVariableAdd.maj a b c)
      simp only [addCarry,List.length_cons]
      omega

theorem addCarry_length_pair (x y : List Bool) (c : Bool) :
    (addCarry x y c).length≤(pairBits x y).length := by
  have h := addCarry_length x y c
  rw [pairBits_length]
  omega

theorem parseFuel_eq (x y : List Bool) :
    parseFuel x y=2*(pairBits x y).length+4 := by
  simp only [parseFuel,pairBits_length,Epos,D]
  omega

theorem parseFuel_le (x y : List Bool) :
    parseFuel x y≤8*((pairBits x y).length+1)*((pairBits x y).length+1) := by
  rw [parseFuel_eq]
  nlinarith [Nat.zero_le ((pairBits x y).length^2)]

theorem cleanup_addFuel_le (x y : List Bool) :
    cleanupFuel x y (addCarry x y false)≤
      256*((pairBits x y).length+1)*((pairBits x y).length+1) := by
  have h := cleanupFuel_le x y (addCarry x y false)
  have hl := addCarry_length_pair x y false
  calc
    cleanupFuel x y (addCarry x y false)≤
        64*((pairBits x y).length+(addCarry x y false).length+1)*
          ((pairBits x y).length+(addCarry x y false).length+1) := h
    _≤64*(2*((pairBits x y).length+1))*(2*((pairBits x y).length+1)) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul_left 64 (by omega)) (by omega)
    _=256*((pairBits x y).length+1)*((pairBits x y).length+1) := by ring

theorem sum_cleanup_spec (x y : List Bool) :
    run machine (ticks (cleanupFuel x y (addCarry x y false)))
        ⟨26,(Epos x y : Int),resultTape x y (addCarry x y false)⟩=
      some (StandardBitVariableAddNormalize.finalConfig (addCarry x y false)) ∧
    cleanupFuel x y (addCarry x y false)≤
      256*((pairBits x y).length+1)*((pairBits x y).length+1) ∧
    Output machine (addBits (pairBits x y))
      (StandardBitVariableAddNormalize.finalConfig (addCarry x y false)) := by
  refine ⟨cleanup_run x y _,cleanup_addFuel_le x y,?_⟩
  have he : addBits (pairBits x y)=
      StandardBinaryWordNormalization.normalizeBits (addCarry x y false) := by
    rw [StandardBitVariableAdd.add_pair,StandardBitVariableAdd.addCarry_normalize]
  rw [he]
  exact (StandardBitVariableAddNormalize.normalization_spec _).2.1

end PakFixedPolyomino.StandardBitVariableAddSize
