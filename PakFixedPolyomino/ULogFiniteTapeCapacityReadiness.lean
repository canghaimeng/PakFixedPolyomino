import PakFixedPolyomino.ULogFiniteTapePhysicalResourceLedger

/-! Capacity readiness from actual extension counts. An accepting logical
run can be lifted with state workspace charged by right extensions rather
than by every logical tick. This is one local resource premise, not a
physical trace, alphabet, outer-buffer, clock or full-frame theorem. -/

namespace PakFixedPolyomino.ULogFiniteTapeCapacityReadiness

open ULogCompiler ULogFiniteTapeGrowthLedger ULogFiniteTapePhysicalResourceLedger
open ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

inductive CapacityReadyRun (p : BoundedProgram ns nt) (blank : Fin nt) :
    List Bool → Int → BoundedConfig ns nt → Nat → Prop
  | nil {head : Int} {z : BoundedConfig ns nt} {C : Nat}
      (stateCapacity : z.state.val ≤ C) : CapacityReadyRun p blank [] head z C
  | cons {slot : Bool} {rest : List Bool} {head : Int}
      {z : BoundedConfig ns nt} {a : BoundedAction ns nt} {C : Nat}
      (halt : boundedHalted z = false)
      (rule : p.rule z.state z.focus slot = some a)
      (stateCapacity : z.state.val ≤ C)
      (capacity : SemanticCapacityReady (liftConfig p z) (actionCode a) C)
      (tail : CapacityReadyRun p blank rest (moveHead a.move head)
        (applyBounded blank z a) (semanticCapacityAfter (liftConfig p z) (actionCode a) C)) :
      CapacityReadyRun p blank (slot :: rest) head z C

theorem step_capacity_ready (p : BoundedProgram ns nt) (z : BoundedConfig ns nt)
    (a : BoundedAction ns nt) (C rg : Nat)
    (hc : rightCharge z a + rg + (ns - 1) ≤ C) :
    z.state.val ≤ C ∧ SemanticCapacityReady (liftConfig p z) (actionCode a) C ∧
      rg + (ns - 1) ≤ semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
  have hns : 0 < ns := lt_of_le_of_lt (Nat.zero_le z.state.val) z.state.isLt
  have hz : z.state.val ≤ ns - 1 := by omega
  have ha : a.target.val ≤ ns - 1 := by have h := a.target.isLt; omega
  rw [capacity_after_charge]
  cases hm : a.move <;> cases hr : z.right <;>
    simp [rightCharge, SemanticCapacityReady, liftConfig, actionCode, hm, hr] at * <;> omega

theorem actual_capacity_ready {p : BoundedProgram ns nt} {blank : Fin nt}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns nt} {lg rg : Nat}
    (h : GrowthRun p blank w head z hf zf lg rg) (C : Nat)
    (hc : rg + (ns - 1) ≤ C) : CapacityReadyRun p blank w head z C := by
  induction h generalizing C with
  | nil =>
      apply CapacityReadyRun.nil
      have hz := z.state.isLt
      omega
  | @cons slot rest head hf z zf a lg rg halt rule tail ih =>
      have hs := step_capacity_ready p z a C rg (by simpa [Nat.add_assoc] using hc)
      exact CapacityReadyRun.cons halt rule hs.1 hs.2.1 (ih _ hs.2.2)

theorem every_actual_capacity_ready (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns nt)
    (hrun : ULogFiniteTapeZipperRun.run p blank w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p blank w head z hf zf lg rg ∧
      (∀ C, rg + (ns - 1) ≤ C → CapacityReadyRun p blank w head z C) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p blank w head hf z zf hrun
  exact ⟨lg, rg, hg, actual_capacity_ready hg⟩

end PakFixedPolyomino.ULogFiniteTapeCapacityReadiness
