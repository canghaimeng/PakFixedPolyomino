import PakFixedPolyomino.PakGuardCounterBitTimeClosed
import PakFixedPolyomino.StandardBitRetainedPairBitTime
import PakFixedPolyomino.StandardBitUnaryBudgetClosed

/-! Original macro-side versus literal-answer-length predicate on EVERY raw
word, with actual standard bit-time proved internally. Full guarded weighted
DP and the original headline remain separate obligations. -/
namespace PakFixedPolyomino.PakGuardComparatorBitTimeClosed
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open PakGuardCounterBitTimeClosed (counterBits counter_value_pair counter_polyBitTime)
open StandardBitRetainedPairBitTime (lifting lifting_pair lifting_none lifting_polyBitTime)

noncomputable def predicate {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) : Bool := StandardBitUnaryBudgetClosed.predicate (lifting (counterBits M p) raw)

theorem predicate_pair {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x y : List Bool) :
    predicate M p (pairBits x y)=decide (PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length) := by
  rw [predicate,lifting_pair,StandardBitUnaryBudgetClosed.predicate_pair,counter_value_pair]

theorem predicate_none {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) (h : unpairBits raw=none) : predicate M p raw=false := by
  rw [predicate,lifting_none _ raw h,StandardBitUnaryBudgetClosed.predicate_pair]
  simp

theorem predicate_polyBitTime {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (fun raw => [predicate M p raw]) :=
  StandardBitTimeComposition.polyBitTime_comp
    (lifting_polyBitTime _ (counter_polyBitTime M p)) StandardBitUnaryBudgetClosed.predicate_polyBitTime

theorem predicate_spec {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (fun raw => [predicate M p raw]) ∧
    (∀ x y, predicate M p (pairBits x y)=
      decide (PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length)) ∧
    (∀ raw, unpairBits raw=none → predicate M p raw=false) :=
  ⟨predicate_polyBitTime M p,predicate_pair M p,predicate_none M p⟩

end PakFixedPolyomino.PakGuardComparatorBitTimeClosed
