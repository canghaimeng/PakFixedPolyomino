import PakFixedPolyomino.StandardBitHalve
import PakFixedPolyomino.StandardBitDecrementAlignment

/-! The physical halving primitive uses the original positional input value. -/
namespace PakFixedPolyomino.StandardBitHalveAlignment
open StandardNondeterministicMachine StandardBitTime
open StandardBitHalve (halveBits)

theorem halve_original_value (w : List Bool) :
    PakFixedWeightedStandardBinaryCount.value (halveBits w) =
      PakFixedWeightedStandardBinaryCount.value w / 2 := by
  rw [← StandardBitDecrementAlignment.value_eq_original,
    ← StandardBitDecrementAlignment.value_eq_original]
  exact StandardBitHalve.halve_value w

theorem halve_usual_bit_spec : PolyBitTime halveBits ∧ ∀ w,
    PakFixedWeightedStandardBinaryCount.value (halveBits w) =
      PakFixedWeightedStandardBinaryCount.value w / 2 ∧
    (halveBits w).length = w.length-1 ∧
    (∃ n out, n ≤ 4*w.length+4 ∧
      run StandardBitHalve.machine (ticks n) (initial StandardBitHalve.machine w) = some out ∧
      Output StandardBitHalve.machine (halveBits w) out) ∧
    RunsAtMost StandardBitHalve.machine w (4*w.length+4) := by
  refine ⟨StandardBitHalve.halve_polyBitTime,?_⟩
  intro w
  have hs := StandardBitHalve.halve_bit_spec.2 w
  exact ⟨halve_original_value w,hs.2.1,hs.2.2.1,hs.2.2.2⟩

end PakFixedPolyomino.StandardBitHalveAlignment
