import PakFixedPolyomino.StandardBitDecrement
import PakFixedPolyomino.PakFixedWeightedStandardBinaryCount

/-! The operational primitive uses exactly the original usual positional value.
This alignment retains every raw input, including arbitrary high zero digits. -/
namespace PakFixedPolyomino.StandardBitDecrementAlignment
open StandardNondeterministicMachine StandardBitTime
open StandardBitDecrementWord (decrementBits)

theorem value_eq_original (x : List Bool) :
    StandardBitDecrementWord.value x = PakFixedWeightedStandardBinaryCount.value x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [StandardBitDecrementWord.value,PakFixedWeightedStandardBinaryCount.value,ih]

theorem decrement_original_value (x : List Bool) :
    PakFixedWeightedStandardBinaryCount.value (decrementBits x) =
      PakFixedWeightedStandardBinaryCount.value x - 1 := by
  rw [← value_eq_original,← value_eq_original]
  exact StandardBitDecrementWord.decrement_value x

theorem positive_literal_length (x : List Bool)
    (hx : 0 < PakFixedWeightedStandardBinaryCount.value x) : (decrementBits x).length = x.length := by
  apply StandardBitDecrementWord.decrement_length
  by_contra h
  have he : StandardBitDecrementWord.zeroPrefix x = x.length := by
    have := StandardBitDecrementWord.zeroPrefix_le x
    omega
  have hn : StandardBitDecrementWord.borrowBits x = none := by
    rw [StandardBitDecrementWord.borrow_layout,if_pos he]
  have hv := (StandardBitDecrementWord.borrow_none_iff x).mp hn
  rw [value_eq_original] at hv
  omega

theorem decrement_usual_spec (x : List Bool) :
    PakFixedWeightedStandardBinaryCount.value (decrementBits x) =
        PakFixedWeightedStandardBinaryCount.value x - 1 ∧
    (decrementBits x).length ≤ x.length ∧
    run StandardBitDecrement.machine (ticks (2*x.length+4))
        (initial StandardBitDecrement.machine x) = some (StandardBitDecrement.finalConfig (decrementBits x)) ∧
    Output StandardBitDecrement.machine (decrementBits x) (StandardBitDecrement.finalConfig (decrementBits x)) ∧
    RunsAtMost StandardBitDecrement.machine x (2*x.length+4) ∧ PolyBitTime decrementBits := by
  have hs := StandardBitDecrement.decrement_spec x
  exact ⟨decrement_original_value x,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,
    StandardBitDecrement.decrement_polyBitTime⟩

end PakFixedPolyomino.StandardBitDecrementAlignment
