import PakFixedPolyomino.ULogAutomaticSemanticLeftBoundaryAtMost

/-! Coupled semantic/concrete labelled runs and compositional multi-cycle refinement. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

inductive SemanticSlotRun : ULogSemantics.Config → List Bool →
    ULogSemantics.Config → Prop
  | nil (c : ULogSemantics.Config) : SemanticSlotRun c [] c
  | cons (c c' finish : ULogSemantics.Config) (slot : Bool)
      (slots : List Bool)
      (step : ULogSemantics.stepSlot slot c = some c')
      (tail : SemanticSlotRun c' slots finish) :
      SemanticSlotRun c (slot :: slots) finish

inductive ConcreteBranchedRun : Result → List Bool → Result → Prop
  | nil (r : Result) : ConcreteBranchedRun r [] r
  | cons (start next finish : Result) (slot : Bool) (slots : List Bool)
      (step : BranchedReaches slot start next)
      (tail : ConcreteBranchedRun next slots finish) :
      ConcreteBranchedRun start (slot :: slots) finish

structure CoupledCycleStep (slot : Bool) (c c' : ULogSemantics.Config)
    (start finish : Result) : Prop where
  semantic : ULogSemantics.stepSlot slot c = some c'
  concrete : BranchedReaches slot start finish

inductive CoupledCycleRun : ULogSemantics.Config → Result →
    List Bool → ULogSemantics.Config → Result → Prop
  | nil (c : ULogSemantics.Config) (r : Result) :
      CoupledCycleRun c r [] c r
  | cons (c c' finishConfig : ULogSemantics.Config)
      (start next finish : Result) (slot : Bool) (slots : List Bool)
      (step : CoupledCycleStep slot c c' start next)
      (tail : CoupledCycleRun c' next slots finishConfig finish) :
      CoupledCycleRun c start (slot :: slots) finishConfig finish

theorem CoupledCycleRun.semantic
    {c finishConfig : ULogSemantics.Config} {start finish : Result}
    {slots : List Bool}
    (run : CoupledCycleRun c start slots finishConfig finish) :
    SemanticSlotRun c slots finishConfig := by
  induction run with
  | nil c r => exact .nil c
  | cons c c' finishConfig start next finish slot slots step tail ih =>
      exact .cons c c' finishConfig slot slots step.semantic ih

theorem CoupledCycleRun.concrete
    {c finishConfig : ULogSemantics.Config} {start finish : Result}
    {slots : List Bool}
    (run : CoupledCycleRun c start slots finishConfig finish) :
    ConcreteBranchedRun start slots finish := by
  induction run with
  | nil c r => exact .nil r
  | cons c c' finishConfig start next finish slot slots step tail ih =>
      exact .cons start next finish slot slots step.concrete ih

theorem SemanticSlotRun.append
    {a b c : ULogSemantics.Config} {xs ys : List Bool}
    (h₁ : SemanticSlotRun a xs b) (h₂ : SemanticSlotRun b ys c) :
    SemanticSlotRun a (xs ++ ys) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons a a' b slot slots step tail ih =>
      exact .cons a a' c slot (slots ++ ys) step (ih h₂)

theorem ConcreteBranchedRun.append
    {a b c : Result} {xs ys : List Bool}
    (h₁ : ConcreteBranchedRun a xs b) (h₂ : ConcreteBranchedRun b ys c) :
    ConcreteBranchedRun a (xs ++ ys) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons a a' b slot slots step tail ih =>
      exact .cons a a' c slot (slots ++ ys) step (ih h₂)

theorem CoupledCycleRun.append
    {a b c : ULogSemantics.Config} {ra rb rc : Result}
    {xs ys : List Bool}
    (h₁ : CoupledCycleRun a ra xs b rb)
    (h₂ : CoupledCycleRun b rb ys c rc) :
    CoupledCycleRun a ra (xs ++ ys) c rc := by
  induction h₁ with
  | nil => simpa using h₂
  | cons a a' b ra ra' rb slot slots step tail ih =>
      exact .cons a a' c ra ra' rc slot (slots ++ ys) step (ih h₂)

theorem semanticSlotRun_length
    {c finish : ULogSemantics.Config} {slots : List Bool}
    (run : SemanticSlotRun c slots finish) :
    ∃ configs : List ULogSemantics.Config,
      configs.length = slots.length + 1 ∧
        configs.head? = some c ∧ configs.getLast? = some finish := by
  induction run with
  | nil c => exact ⟨[c], by simp⟩
  | cons c c' finish slot slots step tail ih =>
      obtain ⟨configs, hlen, hhead, hlast⟩ := ih
      cases configs with
      | nil => simp at hhead
      | cons d ds =>
          exact ⟨c :: d :: ds, by simp at hlen ⊢; omega, by simp,
            by simpa using hlast⟩

end PakFixedPolyomino.ULogBootstrapExecution
