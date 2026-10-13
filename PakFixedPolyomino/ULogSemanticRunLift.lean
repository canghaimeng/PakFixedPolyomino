import PakFixedPolyomino.ULogAutomaticCoupledStep

/-! Pointwise semantic-cycle refinement lifts compositionally to arbitrary runs. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

theorem SemanticSlotRun.lift
    (encode : ULogSemantics.Config → Result)
    {start finish : ULogSemantics.Config} {slots : List Bool}
    (run : SemanticSlotRun start slots finish)
    (refineStep : ∀ (c c' : ULogSemantics.Config) (slot : Bool),
      ULogSemantics.stepSlot slot c = some c' →
        CoupledCycleStep slot c c' (encode c) (encode c')) :
    CoupledCycleRun start (encode start) slots finish (encode finish) := by
  induction run with
  | nil c => exact .nil c (encode c)
  | cons c c' finish slot slots step tail ih =>
      exact .cons c c' finish (encode c) (encode c') (encode finish)
        slot slots (refineStep c c' slot step) ih

theorem semanticSlotRun_has_concrete_refinement
    (encode : ULogSemantics.Config → Result)
    {start finish : ULogSemantics.Config} {slots : List Bool}
    (run : SemanticSlotRun start slots finish)
    (refineStep : ∀ (c c' : ULogSemantics.Config) (slot : Bool),
      ULogSemantics.stepSlot slot c = some c' →
        BranchedReaches slot (encode c) (encode c')) :
    ConcreteBranchedRun (encode start) slots (encode finish) := by
  have coupled := SemanticSlotRun.lift encode run
    (fun c c' slot h => ⟨h, refineStep c c' slot h⟩)
  exact coupled.concrete

end PakFixedPolyomino.ULogBootstrapExecution
