import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Literal zipper runs and extension counts are invariant under an integer
translation of the displayed physical head. The same word and zipper are
kept, including both labelled nondeterministic slots. -/
namespace PakFixedPolyomino.ULogFiniteTapeHeadTranslation
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open FiniteOneTapeSemantics (moveHead)
variable {ns nt : Nat}

theorem moveHead_add (m : OneTapeTableau.Move) (H d : Int) :
    moveHead m (H + d) = moveHead m H + d := by cases m <;> simp [moveHead] <;> omega

theorem run_add (p : BoundedProgram ns nt) (blank : Fin nt) (w : List Bool)
    (H d : Int) (z : BoundedConfig ns nt) :
    run p blank w (H + d) z = (run p blank w H z).map (fun hz => (hz.1 + d, hz.2)) := by
  induction w generalizing H z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh]
      | false =>
          cases ha : p.rule z.state z.focus slot with
          | none => simp [run, hh, ha]
          | some a =>
              simp only [run, hh, Bool.false_eq_true, if_false, ha]
              rw [moveHead_add, ih]

theorem growth_add {p : BoundedProgram ns nt} {blank : Fin nt} {w : List Bool}
    {H hf : Int} {z out : BoundedConfig ns nt} {lg rg : Nat}
    (h : GrowthRun p blank w H z hf out lg rg) (d : Int) :
    GrowthRun p blank w (H + d) z (hf + d) out lg rg := by
  induction h with
  | nil => exact GrowthRun.nil _ _
  | @cons slot rest H hf z out a lg rg hh hr tail ih =>
      apply GrowthRun.cons hh hr
      rw [moveHead_add]
      exact ih

theorem run_from_zero (p : BoundedProgram ns nt) (blank : Fin nt) (w : List Bool)
    (H hf : Int) (z out : BoundedConfig ns nt)
    (hw : run p blank w H z = some (hf, out)) :
    ∃ hf0, run p blank w 0 z = some (hf0, out) ∧ hf0 + H = hf := by
  have he := run_add p blank w 0 H z
  simp only [zero_add] at he
  rw [hw] at he
  obtain ⟨⟨h0, z0⟩, hr, hv⟩ := Option.map_eq_some_iff.mp he.symm
  have heads := (Prod.mk.inj hv).1
  have states := (Prod.mk.inj hv).2
  change z0 = out at states
  change h0 + H = hf at heads
  subst z0
  exact ⟨h0, hr, heads⟩

end PakFixedPolyomino.ULogFiniteTapeHeadTranslation
