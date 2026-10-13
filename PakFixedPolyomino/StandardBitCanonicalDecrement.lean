import PakFixedPolyomino.StandardBitDecrementAlignment
import PakFixedPolyomino.StandardBitNormalize
import PakFixedPolyomino.StandardBitMachineComposition

/-! Canonical saturated predecessor, with the actual decrement/normalization
runs and the one physical handoff supplied internally on every raw word. -/
namespace PakFixedPolyomino.StandardBitCanonicalDecrement
open Computability StandardNondeterministicMachine StandardBitTime StandardBitMachineComposition
open StandardBinaryWordNormalization
open StandardBitDecrementWord (decrementBits decrement_length_le)
open PakFixedWeightedStandardBinaryCount (value)

def machine : DeterministicMachine 15 10 :=
  compose StandardBitDecrement.machine StandardBitNormalize.machine

def finalConfig (w : List Bool) : Configuration 15 10 :=
  encodeConfigB (nsA := 8) (ntA := 4) StandardBitNormalize.machine
    (StandardBitNormalize.finalConfig (decrementBits w))

def fuel (w : List Bool) : Nat := 2*w.length+4+1+(2*(decrementBits w).length+2)

theorem canonical_word (w : List Bool) :
    normalizeBits (decrementBits w) = encodeNat (value w-1) := by
  rw [normalize_eq_encodeNat,StandardBitDecrementAlignment.decrement_original_value]

theorem decrement_run (w : List Bool) :
    run machine (ticks (fuel w)) (initial machine w) = some (finalConfig w) ∧
    Output machine (encodeNat (value w-1)) (finalConfig w) := by
  have h := compose_exact StandardBitDecrement.machine StandardBitNormalize.machine
    decrementBits normalizeBits w (2*w.length+4) (2*(decrementBits w).length+2)
    (StandardBitDecrement.finalConfig (decrementBits w))
    (StandardBitNormalize.finalConfig (decrementBits w))
    (StandardBitDecrement.machine_run w) ⟨rfl,rfl,rfl⟩
    (StandardBitNormalize.normalize_run (decrementBits w)) ⟨rfl,rfl,rfl⟩
  simpa only [machine,finalConfig,fuel,canonical_word] using h

theorem fuel_le (w : List Bool) : fuel w ≤ 4*w.length+7 := by
  have h := decrement_length_le w
  unfold fuel
  omega

theorem predecessor_computes :
    ComputesWithin machine (fun w => encodeNat (value w-1)) (fun n => 4*n+7) := by
  intro w
  exact ⟨fuel w,finalConfig w,fuel_le w,(decrement_run w).1,(decrement_run w).2⟩

theorem predecessor_polyBitTime : PolyBitTime (fun w => encodeNat (value w-1)) := by
  refine ⟨15,10,machine,4*Polynomial.X+7,?_⟩
  simpa using predecessor_computes

theorem canonical_decrement_bit_spec :
    PolyBitTime (fun w => encodeNat (value w-1)) ∧
    ∀ w, run machine (ticks (fuel w)) (initial machine w) = some (finalConfig w) ∧
      Output machine (encodeNat (value w-1)) (finalConfig w) ∧
      RunsAtMost machine w (4*w.length+7) :=
  ⟨predecessor_polyBitTime,fun w => ⟨(decrement_run w).1,(decrement_run w).2,
    (ComputesWithin.actual_bounds machine _ _ predecessor_computes w).1⟩⟩

end PakFixedPolyomino.StandardBitCanonicalDecrement
