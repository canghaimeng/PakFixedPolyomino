import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
import PakFixedPolyomino.ULogAutomaticSemanticCycle

/-! Exact accounting with the physical cycle's actual capacity/outer
updates. Successful semantic execution does not imply physical readiness:
the recursive accounting here deliberately supplies no feasibility claim. -/

namespace PakFixedPolyomino.ULogFiniteTapePhysicalResourceLedger

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

theorem capacity_after_charge (p : BoundedProgram ns nt) (z : BoundedConfig ns nt)
    (a : BoundedAction ns nt) (C : Nat) :
    semanticCapacityAfter (liftConfig p z) (actionCode a) C = C - rightCharge z a := by
  cases hm : a.move <;> cases hr : z.right <;>
    simp [semanticCapacityAfter, rightCharge, actionCode, liftConfig, hm, hr]

theorem outer_after_charge (p : BoundedProgram ns nt) (z : BoundedConfig ns nt)
    (a : BoundedAction ns nt) (outer : List ULogProgram.Tape) :
    semanticOuterAfter (liftConfig p z) (actionCode a) outer = outer.drop (leftCharge z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;>
    simp [semanticOuterAfter, leftCharge, actionCode, liftConfig, hm, hl,
      List.drop_one]

def resourceRun (p : BoundedProgram ns nt) (blank : Fin nt) :
    List Bool → Int → BoundedConfig ns nt → Nat → List ULogProgram.Tape →
      Option (Int × BoundedConfig ns nt × Nat × List ULogProgram.Tape)
  | [], head, z, C, outer => some (head, z, C, outer)
  | slot :: rest, head, z, C, outer =>
      if boundedHalted z then none else
        match p.rule z.state z.focus slot with
        | none => none
        | some a => resourceRun p blank rest (moveHead a.move head) (applyBounded blank z a)
            (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
            (semanticOuterAfter (liftConfig p z) (actionCode a) outer)

theorem actual_resource_run {p : BoundedProgram ns nt} {blank : Fin nt}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns nt} {lg rg : Nat}
    (h : GrowthRun p blank w head z hf zf lg rg)
    (C : Nat) (outer : List ULogProgram.Tape) :
    resourceRun p blank w head z C outer = some (hf, zf, C - rg, outer.drop lg) := by
  induction h generalizing C outer with
  | nil => simp [resourceRun]
  | cons halt rule tail ih =>
      simp only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule]
      rw [capacity_after_charge, outer_after_charge, ih]
      simp [Nat.sub_sub, List.drop_drop]

theorem every_actual_resource_run (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns nt)
    (hrun : run p blank w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p blank w head z hf zf lg rg ∧
      (∀ C outer, resourceRun p blank w head z C outer =
        some (hf, zf, C - rg, outer.drop lg)) ∧
      leftEdge hf zf = leftEdge head z - lg ∧
      rightEdge hf zf = rightEdge head z + rg ∧
      cellCount zf = cellCount z + lg + rg ∧ lg + rg ≤ w.length := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p blank w head hf z zf hrun
  exact ⟨lg, rg, hg, actual_resource_run hg, hg.exact_ledger⟩

end PakFixedPolyomino.ULogFiniteTapePhysicalResourceLedger
