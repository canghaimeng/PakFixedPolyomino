import PakFixedPolyomino.ULogCompiler
import PakFixedPolyomino.FiniteOneTapeSemantics

/-! Literal finite-tape zipper runs for any fixed finite alphabet. The
blank's code is explicitly2, as in the actual universal semantics. This
generalization supports the loader's delimiter while leaving the existing
three-symbol scanner bridge and its immutable scopes unchanged. -/

namespace PakFixedPolyomino.ULogFiniteTapeZipperRun

open ULogCompiler
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

def run (p : BoundedProgram ns nt) (blank : Fin nt) :
    List Bool → Int → BoundedConfig ns nt → Option (Int × BoundedConfig ns nt)
  | [], head, z => some (head, z)
  | slot :: rest, head, z =>
      if boundedHalted z then none else
        match p.rule z.state z.focus slot with
        | none => none
        | some a => run p blank rest (moveHead a.move head) (applyBounded blank z a)

def semanticRun : ULogSemantics.Config → List Bool → Option ULogSemantics.Config
  | c, [] => some c
  | c, slot :: rest =>
      (ULogSemantics.stepSlot slot c).bind (fun next => semanticRun next rest)

theorem run_lift (p : BoundedProgram ns nt) (blank : Fin nt)
    (hblank : blank.val = ULogSemantics.blankCode) (slots : List Bool)
    (head : Int) (z : BoundedConfig ns nt) :
    (run p blank slots head z).map (fun hz => liftConfig p hz.2) =
      semanticRun (liftConfig p z) slots := by
  induction slots generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      have hs := stepSlot_liftConfig p blank hblank slot z
      dsimp [run, semanticRun]
      cases hh : boundedHalted z with
      | true =>
          have ht : ULogSemantics.stepSlot slot (liftConfig p z) = none := by
            simpa [boundedStepSlot, hh] using hs
          simp [hh, ht]
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none =>
              have ht : ULogSemantics.stepSlot slot (liftConfig p z) = none := by
                simpa [boundedStepSlot, hh, hr] using hs
              simp [hh, ht, hr]
          | some a =>
              have ht : ULogSemantics.stepSlot slot (liftConfig p z) =
                  some (liftConfig p (applyBounded blank z a)) := by
                simpa [boundedStepSlot, hh, hr] using hs
              simp [hh, hr, ht]
              exact ih (moveHead a.move head) (applyBounded blank z a)

theorem run_append (p : BoundedProgram ns nt) (blank : Fin nt)
    (xs ys : List Bool) (head : Int) (z : BoundedConfig ns nt) :
    run p blank (xs ++ ys) head z =
      (run p blank xs head z).bind (fun hz => run p blank ys hz.1 hz.2) := by
  induction xs generalizing head z with
  | nil => simp [run]
  | cons slot rest ih =>
      dsimp [run]
      cases boundedHalted z with
      | true => simp
      | false =>
          simp
          cases p.rule z.state z.focus slot with
          | none => simp
          | some a =>
              simp
              exact ih (moveHead a.move head) (applyBounded blank z a)

end PakFixedPolyomino.ULogFiniteTapeZipperRun
