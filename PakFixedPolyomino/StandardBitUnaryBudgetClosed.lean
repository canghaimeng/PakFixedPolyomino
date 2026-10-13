import PakFixedPolyomino.StandardBitUnaryBudgetLoop
import PakFixedPolyomino.StandardBitUnaryBudgetBorrow

/-! The initialized ALLraw comparator, with both physical borrow premises proved.
The second operand contributes its literal word length, including high zeros. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetClosed
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitUnaryBudgetCompare

theorem compare_computes :
    ComputesWithin machine compareBits (fun n => 128*(n+1)*(n+1)) :=
  StandardBitUnaryBudgetLoop.compare_computes
    StandardBitUnaryBudgetBorrow.borrow_success StandardBitUnaryBudgetBorrow.borrow_underflow

theorem compare_polyBitTime : PolyBitTime compareBits :=
  StandardBitUnaryBudgetLoop.compare_polyBitTime
    StandardBitUnaryBudgetBorrow.borrow_success StandardBitUnaryBudgetBorrow.borrow_underflow

def predicate (w : List Bool) : Bool :=
  match unpairBits w with
  | none => false
  | some (x,y) => decide (PakFixedWeightedStandardBinaryCount.value x<y.length)

theorem compareBits_eq_singleton (w : List Bool) : compareBits w=[predicate w] := by
  unfold compareBits predicate
  cases unpairBits w with
  | none => rfl
  | some p => rcases p with ⟨x,y⟩;rfl

theorem predicate_pair (x y : List Bool) :
    predicate (pairBits x y)=decide (PakFixedWeightedStandardBinaryCount.value x<y.length) := by
  simp [predicate,unpair_pairBits]

theorem predicate_none (w : List Bool) (h : unpairBits w=none) : predicate w=false := by
  simp [predicate,h]

theorem predicate_polyBitTime : PolyBitTime (fun w => [predicate w]) := by
  have he : (fun w => [predicate w])=compareBits :=
    funext (fun w => (compareBits_eq_singleton w).symm)
  rw [he]
  exact compare_polyBitTime

theorem compare_spec :
    ComputesWithin machine compareBits (fun n => 128*(n+1)*(n+1)) ∧
    PolyBitTime compareBits ∧
    (∀ x y, compareBits (pairBits x y)=
      [decide (PakFixedWeightedStandardBinaryCount.value x<y.length)]) ∧
    (∀ w, unpairBits w=none → compareBits w=[false]) ∧
    ∀ w, RunsAtMost machine w (128*(w.length+1)*(w.length+1)) ∧
      ∀ slots out, run machine slots (initial machine w)=some out →
        -(128*(w.length+1)*(w.length+1) : Int) ≤ out.head ∧
        out.head ≤ (128*(w.length+1)*(w.length+1) : Int) ∧
        ∀ z : Int, z < -(128*(w.length+1)*(w.length+1) : Int) ∨
          (w.length : Int)+(128*(w.length+1)*(w.length+1) : Int)+1 ≤ z →
          out.tape z=machine.blank := by
  refine ⟨compare_computes,compare_polyBitTime,compare_pair,?_,?_⟩
  · intro w h;simp [compareBits,h]
  · intro w
    exact ComputesWithin.actual_bounds machine compareBits _ compare_computes w

end PakFixedPolyomino.StandardBitUnaryBudgetClosed
