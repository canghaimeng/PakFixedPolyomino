import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! A literal chronological head footprint inside the initially allocated
interval forces zero left and right extensions. The condition concerns all
prefixes of the given actual word, without a canonical-image assumption. -/
namespace PakFixedPolyomino.ULogFiniteTapePrefixGrowth
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open FiniteOneTapeSemantics (moveHead)
variable {ns nt : Nat}

def PrefixHeads (p : BoundedProgram ns nt) (blank : Fin nt) (w : List Bool)
    (H : Int) (z : BoundedConfig ns nt) (lo hi : Int) : Prop :=
  ∀ k ≤ w.length, ∀ hf out,
    run p blank (w.take k) H z = some (hf, out) → lo ≤ hf ∧ hf ≤ hi

theorem extents_of_prefix_heads (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (H hf lo hi : Int) (z out : BoundedConfig ns nt)
    (hl : lo ≤ leftEdge H z) (hr : rightEdge H z ≤ hi)
    (heads : PrefixHeads p blank w H z lo hi)
    (hw : run p blank w H z = some (hf, out)) :
    lo ≤ leftEdge hf out ∧ rightEdge hf out ≤ hi := by
  induction w generalizing H z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩
      exact ⟨hl, hr⟩
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hw
      | false =>
          cases ha : p.rule z.state z.focus slot with
          | none => simp [run, hh, ha] at hw
          | some a =>
              have hone : run p blank ((slot :: rest).take 1) H z =
                  some (moveHead a.move H, applyBounded blank z a) := by
                simp [run, hh, ha]
              have hs := step_extents blank H lo hi z a hl hr
                (heads 1 (by simp) _ _ hone)
              have ht : run p blank rest (moveHead a.move H) (applyBounded blank z a) =
                  some (hf, out) := by simpa [run, hh, ha] using hw
              apply ih _ _ hs.1 hs.2 _ ht
              intro k hk hmid middle hrun
              have hp : run p blank ((slot :: rest).take (k + 1)) H z = some (hmid, middle) := by
                simpa [run, hh, ha] using hrun
              exact heads (k + 1) (by simp only [List.length_cons]; omega) _ _ hp

theorem no_growth_of_prefix_heads (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (H hf : Int) (z out : BoundedConfig ns nt)
    (heads : PrefixHeads p blank w H z (leftEdge H z) (rightEdge H z))
    (hw : run p blank w H z = some (hf, out)) :
    GrowthRun p blank w H z hf out 0 0 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p blank w H hf z out hw
  have he := extents_of_prefix_heads p blank w H hf _ _ z out
    (le_refl _) (le_refl _) heads hw
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  simpa [hlg, hrg] using hg

end PakFixedPolyomino.ULogFiniteTapePrefixGrowth
