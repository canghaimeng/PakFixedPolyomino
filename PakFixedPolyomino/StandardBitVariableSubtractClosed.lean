import PakFixedPolyomino.StandardBitVariableSubtractLoop
import PakFixedPolyomino.StandardBitVariableAddClosed

/-! Ordinary saturated subtraction and strict comparison on EVERY raw input.
The actual closed adder supplies the loop's sole compiler premise internally.
All physical initialization, borrow arithmetic, frame bounds, stopping flags,
clean pairing/projections and transition costs come from the proved loop. -/
namespace PakFixedPolyomino.StandardBitVariableSubtractClosed
open Computability StandardBitTime StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value)
open StandardBitVariableSubtractLoop (subCompareBits subtractBits ltBits)

theorem subCompare_polyBitTime : PolyBitTime subCompareBits :=
  StandardBitVariableSubtractLoop.subCompare_polyBitTime
    StandardBitVariableAddClosed.add_polyBitTime

theorem subtract_polyBitTime : PolyBitTime subtractBits :=
  StandardBitVariableSubtractLoop.subtract_polyBitTime
    StandardBitVariableAddClosed.add_polyBitTime

theorem lt_polyBitTime : PolyBitTime ltBits :=
  StandardBitVariableSubtractLoop.lt_polyBitTime
    StandardBitVariableAddClosed.add_polyBitTime

theorem subtraction_comparison_spec :
    PolyBitTime subCompareBits ∧ PolyBitTime subtractBits ∧ PolyBitTime ltBits ∧
    (∀ x y,subCompareBits (pairBits x y)=
      pairBits (encodeNat (value x-value y)) [decide (value x<value y)]) ∧
    (∀ raw,unpairBits raw=none →
      subCompareBits raw=pairBits [] [false] ∧ subtractBits raw=[] ∧ ltBits raw=[false]) :=
  StandardBitVariableSubtractLoop.subtraction_comparison_spec
    StandardBitVariableAddClosed.add_polyBitTime

end PakFixedPolyomino.StandardBitVariableSubtractClosed
