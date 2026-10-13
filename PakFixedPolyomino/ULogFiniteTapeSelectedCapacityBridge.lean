import PakFixedPolyomino.ULogFiniteTapeAllCapacityOuterReadiness
import PakFixedPolyomino.ULogFiniteTapeCapacityReadiness

/-! Selected-action capacity bounds pass to the actual child ledger. The
left-exterior premise also passes to that child at every numerical capacity;
no readiness of the other labelled slot is required. -/
namespace PakFixedPolyomino.ULogFiniteTapeSelectedCapacityBridge
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapePhysicalResourceLedger
open ULogFiniteTapeAllCapacityOuterReadiness ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)
variable {ns : Nat}

theorem apply_state (z : BoundedConfig ns 3) (a : BoundedAction ns 3) :
    (applyBounded 2 z a).state = a.target := by
  cases move : a.move <;> cases left : z.leftRev <;> cases right : z.right <;>
    simp [applyBounded, move, left, right]

theorem selected_capacity_next_state (p : BoundedProgram ns 3)
    (z : BoundedConfig ns 3) (a : BoundedAction ns 3) (C : Nat)
    (ready : SemanticCapacityReady (liftConfig p z) (actionCode a) C) :
    (applyBounded 2 z a).state.val ≤
      semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
  rw [apply_state]
  cases move : a.move <;> cases right : z.right <;>
    simp [SemanticCapacityReady, semanticCapacityAfter, liftConfig,
      actionCode, move, right] at * <;> omega

theorem target_zero_capacity_ready (p : BoundedProgram ns 3)
    (z : BoundedConfig ns 3) (a : BoundedAction ns 3) (C : Nat)
    (halt : boundedHalted z = false) (current : z.state.val ≤ C)
    (target : a.target.val = 0) :
    SemanticCapacityReady (liftConfig p z) (actionCode a) C := by
  have positive : 2 ≤ C := by
    simp only [boundedHalted, decide_eq_false_iff_not] at halt
    omega
  cases move : a.move <;> cases right : z.right <;>
    simp [SemanticCapacityReady, liftConfig, actionCode, move, right, target] <;>
    omega

theorem child_outer_ready (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (C : Nat) (outer : List ULogProgram.Tape)
    (all : AllReachableOuterReady p head z C outer)
    (slot : Bool) (a : BoundedAction ns 3)
    (halt : boundedHalted z = false) (rule : p.rule z.state z.focus slot = some a) :
    AllReachableOuterReady p (moveHead a.move head) (applyBounded 2 z a)
      (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
      (semanticOuterAfter (liftConfig p z) (actionCode a) outer) := by
  intro w hf out Cf outerf path halted selected action lookup
  apply all (slot :: w) hf out Cf outerf _ halted selected action lookup
  simpa only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule] using path

end PakFixedPolyomino.ULogFiniteTapeSelectedCapacityBridge
