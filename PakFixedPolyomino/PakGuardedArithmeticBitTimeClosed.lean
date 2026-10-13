import PakFixedPolyomino.StandardBitVariableAddClosed
import PakFixedPolyomino.PakWeightedDPIterationBitTime
import PakFixedPolyomino.StandardBitVariableMultiplyLoop
import PakFixedPolyomino.PakGuardedAmplifierBitTime
import PakFixedPolyomino.PakGuardedCoefficientBitTime

/-! The actual variable adder's ordinary runtime proof discharges the last
compiler premise in the concrete original guarded DP, variable multiplication
and original quadratic amplifier denominator. Every component below is now
unconditional on every raw word. Full readout and ND membership are separate. -/
namespace PakFixedPolyomino.PakGuardedArithmeticBitTimeClosed
open StandardBitTime StandardNondeterministicMachine
variable {ns nt : Nat}

theorem dp_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (PakWeightedDPIterationBitTime.dpBits M p) :=
  PakWeightedDPIterationBitTime.dp_polyBitTime M p StandardBitVariableAddClosed.add_polyBitTime

theorem multiply_polyBitTime : PolyBitTime StandardBitVariableMultiplyLoop.multiplyBits :=
  StandardBitVariableMultiplyLoop.multiply_polyBitTime StandardBitVariableAddClosed.add_polyBitTime

theorem amplifier_polyBitTime (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (PakGuardedAmplifierBitTime.denominator c M p) :=
  PakGuardedAmplifierBitTime.denominator_polyBitTime c M p StandardBitVariableAddClosed.add_polyBitTime

theorem coefficient_polyBitTime (c : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (PakGuardedCoefficientBitTime.denominator c M p) :=
  PakGuardedCoefficientBitTime.denominator_polyBitTime c M p

theorem arithmetic_spec (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (PakWeightedDPIterationBitTime.dpBits M p) ∧
    PolyBitTime StandardBitVariableMultiplyLoop.multiplyBits ∧
    ∀ c,PolyBitTime (PakGuardedAmplifierBitTime.denominator c M p) ∧
      PolyBitTime (PakGuardedCoefficientBitTime.denominator c M p) :=
  ⟨dp_polyBitTime M p,multiply_polyBitTime,fun c =>
    ⟨amplifier_polyBitTime c M p,coefficient_polyBitTime c M p⟩⟩

end PakFixedPolyomino.PakGuardedArithmeticBitTimeClosed
