import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! Actual boundary extensions of every literal finite-tape run. A right
extension consumes one capacity cell; an internal right move consumes none.
These spatial identities do not assert physical frame feasibility or time. -/

namespace PakFixedPolyomino.ULogFiniteTapeGrowthLedger

open ULogCompiler ULogFiniteTapeZipperRun
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

def leftEdge (head : Int) (z : BoundedConfig ns nt) : Int :=
  head - z.leftRev.length

def rightEdge (head : Int) (z : BoundedConfig ns nt) : Int :=
  head + z.right.length

def cellCount (z : BoundedConfig ns nt) : Nat :=
  z.leftRev.length + 1 + z.right.length

def leftCharge (z : BoundedConfig ns nt) (a : BoundedAction ns nt) : Nat :=
  match a.move, z.leftRev with
  | .left, [] => 1
  | _, _ => 0

def rightCharge (z : BoundedConfig ns nt) (a : BoundedAction ns nt) : Nat :=
  match a.move, z.right with
  | .right, [] => 1
  | _, _ => 0

theorem step_ledger (blank : Fin nt) (head : Int)
    (z : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    leftEdge (moveHead a.move head) (applyBounded blank z a) =
      leftEdge head z - leftCharge z a ∧
    rightEdge (moveHead a.move head) (applyBounded blank z a) =
      rightEdge head z + rightCharge z a ∧
    cellCount (applyBounded blank z a) =
      cellCount z + leftCharge z a + rightCharge z a ∧
    leftCharge z a + rightCharge z a ≤ 1 := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [leftEdge, rightEdge, cellCount, leftCharge, rightCharge,
      applyBounded, moveHead, hm, hl, hr] <;> omega

inductive GrowthRun (p : BoundedProgram ns nt) (blank : Fin nt) :
    List Bool → Int → BoundedConfig ns nt → Int → BoundedConfig ns nt → Nat → Nat → Prop
  | nil (head : Int) (z : BoundedConfig ns nt) :
      GrowthRun p blank [] head z head z 0 0
  | cons {slot : Bool} {rest : List Bool} {head hf : Int}
      {z zf : BoundedConfig ns nt} {a : BoundedAction ns nt} {lg rg : Nat}
      (halt : boundedHalted z = false)
      (rule : p.rule z.state z.focus slot = some a)
      (tail : GrowthRun p blank rest (moveHead a.move head)
        (applyBounded blank z a) hf zf lg rg) :
      GrowthRun p blank (slot :: rest) head z hf zf
        (leftCharge z a + lg) (rightCharge z a + rg)

theorem GrowthRun.actual_run {p : BoundedProgram ns nt} {blank : Fin nt}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns nt} {lg rg : Nat}
    (h : GrowthRun p blank w head z hf zf lg rg) :
    run p blank w head z = some (hf, zf) := by
  induction h with
  | nil => rfl
  | cons halt rule tail ih => simpa [run, halt, rule] using ih

theorem every_actual_run (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns nt)
    (h : run p blank w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p blank w head z hf zf lg rg := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨0, 0, GrowthRun.nil head z⟩
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at h
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at h
          | some a =>
              have ht : run p blank rest (moveHead a.move head)
                  (applyBounded blank z a) = some (hf, zf) := by
                simpa [run, hh, hr] using h
              obtain ⟨lg, rg, hg⟩ := ih _ _ ht
              exact ⟨leftCharge z a + lg, rightCharge z a + rg,
                GrowthRun.cons hh hr hg⟩

theorem GrowthRun.exact_ledger {p : BoundedProgram ns nt} {blank : Fin nt}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns nt} {lg rg : Nat}
    (h : GrowthRun p blank w head z hf zf lg rg) :
    leftEdge hf zf = leftEdge head z - lg ∧
    rightEdge hf zf = rightEdge head z + rg ∧
    cellCount zf = cellCount z + lg + rg ∧ lg + rg ≤ w.length := by
  induction h with
  | nil => simp
  | @cons slot rest head hf z zf a lg rg halt rule tail ih =>
      have hs := step_ledger blank head z a
      simp only [List.length_cons, Nat.cast_add]
      rcases hs with ⟨hl, hr, hc, hb⟩
      rcases ih with ⟨il, ir, ic, ib⟩
      constructor
      · rw [il, hl]; omega
      constructor
      · rw [ir, hr]; omega
      constructor
      · omega
      · omega

theorem step_extents (blank : Fin nt) (head lo hi : Int)
    (z : BoundedConfig ns nt) (a : BoundedAction ns nt)
    (hl : lo ≤ leftEdge head z) (hr : rightEdge head z ≤ hi)
    (hh : lo ≤ moveHead a.move head ∧ moveHead a.move head ≤ hi) :
    lo ≤ leftEdge (moveHead a.move head) (applyBounded blank z a) ∧
      rightEdge (moveHead a.move head) (applyBounded blank z a) ≤ hi := by
  cases hm : a.move <;> cases hzL : z.leftRev <;> cases hzR : z.right <;>
    simp [leftEdge, rightEdge, applyBounded, moveHead, hm, hzL, hzR] at * <;> omega

theorem every_run_extents (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf lo hi : Int) (z zf : BoundedConfig ns nt)
    (hleft : lo ≤ leftEdge head z) (hright : rightEdge head z ≤ hi)
    (heads : ∀ v h out, run p blank v head z = some (h, out) → lo ≤ h ∧ h ≤ hi)
    (hrun : run p blank w head z = some (hf, zf)) :
    lo ≤ leftEdge hf zf ∧ rightEdge hf zf ≤ hi := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      exact ⟨hleft, hright⟩
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hrun
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hrun
          | some a =>
              have hone : run p blank [slot] head z =
                  some (moveHead a.move head, applyBounded blank z a) := by
                simp [run, hh, hr]
              have he := step_extents blank head lo hi z a hleft hright (heads _ _ _ hone)
              have ht : run p blank rest (moveHead a.move head)
                  (applyBounded blank z a) = some (hf, zf) := by
                simpa [run, hh, hr] using hrun
              apply ih _ _ he.1 he.2 _ ht
              intro v hv out hvRun
              apply heads (slot :: v) hv out
              simpa [run, hh, hr] using hvRun

theorem actual_growth_spec (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns nt)
    (hrun : run p blank w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p blank w head z hf zf lg rg ∧
      leftEdge hf zf = leftEdge head z - lg ∧
      rightEdge hf zf = rightEdge head z + rg ∧
      cellCount zf = cellCount z + lg + rg ∧ lg + rg ≤ w.length := by
  obtain ⟨lg, rg, h⟩ := every_actual_run p blank w head hf z zf hrun
  exact ⟨lg, rg, h, h.exact_ledger⟩

end PakFixedPolyomino.ULogFiniteTapeGrowthLedger
