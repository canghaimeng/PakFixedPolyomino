import PakFixedPolyomino.ULogFiniteTapePhysicalResourceLedger
import PakFixedPolyomino.ULogFiniteTapeCapacityReadiness

/-! Selected-action capacity readiness, including the actual state bound,
passes to the suffix identified by a real resource ledger prefix. -/
namespace PakFixedPolyomino.ULogFiniteTapeSelectedCapacitySuffix
open ULogCompiler ULogFiniteTapeCapacityReadiness ULogFiniteTapePhysicalResourceLedger
open ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)
variable {ns : Nat}

theorem head_state_capacity {p : BoundedProgram ns 3} {w : List Bool}
    {head : Int} {z : BoundedConfig ns 3} {C : Nat}
    (ready : CapacityReadyRun p 2 w head z C) : z.state.val ≤ C := by
  cases ready with
  | nil bound => exact bound
  | cons _ _ bound _ _ => exact bound

theorem suffix_of_resource_run (p : BoundedProgram ns 3) (u v : List Bool)
    (head hf : Int) (z out : BoundedConfig ns 3) (C Cf : Nat)
    (outer outerf : List ULogProgram.Tape)
    (ready : CapacityReadyRun p 2 (u ++ v) head z C)
    (prefixRun : resourceRun p 2 u head z C outer = some (hf, out, Cf, outerf)) :
    CapacityReadyRun p 2 v hf out Cf := by
  induction u generalizing head z C outer with
  | nil =>
      simp only [resourceRun, Option.some.injEq, Prod.mk.injEq] at prefixRun
      rcases prefixRun with ⟨rfl, rfl, rfl, rfl⟩
      simpa only [List.nil_append] using ready
  | cons slot rest ih =>
      change CapacityReadyRun p 2 (slot :: (rest ++ v)) head z C at ready
      cases ready with
      | @cons _ _ _ _ a _ halt rule _ _ tail =>
          have next : resourceRun p 2 rest (moveHead a.move head) (applyBounded 2 z a)
              (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
              (semanticOuterAfter (liftConfig p z) (actionCode a) outer) =
                some (hf, out, Cf, outerf) := by
            simpa only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule] using prefixRun
          exact ih _ _ _ _ tail next

end PakFixedPolyomino.ULogFiniteTapeSelectedCapacitySuffix
