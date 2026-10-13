import PakFixedPolyomino.ULogSourceObliviousShortCycle
import PakFixedPolyomino.ULogSourceObliviousCycleTraces

/-! # All successful stopping lengths at the left boundary

Cycle divisibility and the complete logical trace are derived for EVERY raw
history ending atLeft. No length, image, intermediate endpoint or safety
premise is imposed on the compared history.
-/

namespace PakFixedPolyomino.ULogSourceObliviousStoppingGrammar

open FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousCycleInverse ULogSourceObliviousCycleTraces
open ULogSourceObliviousCompletedCyclePrefix ULogSourceObliviousShortCycle

variable {ns nt : ℕ}

theorem all_atLeft_stopping_runs
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (q : Fin ns) (w : LogicalWindow nt)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ (n : ℕ) (t : Trace p n q w),
      raw = arrows p hnt blank exterior n q w t ∧
      out = initialWindowConfig (endpoint p n q w t).1 (endpoint p n q w t).2 exterior := by
  generalize hlen : raw.length = k
  induction k using Nat.strong_induction_on generalizing q w raw out with
  | h k ih =>
      by_cases hnil : raw = []
      · subst raw
        exact ⟨0, PUnit.unit, rfl, (Option.some.inj hrun).symm⟩
      · have hfirst := nonempty_atLeft_run_cycle_lower_bound p hnt blank q w exterior
          raw out hrun hnil hleft
        obtain ⟨choice, next, hsafe, tail, hraw, htail⟩ :=
          raw_completed_cycle_prefix p hnt blank q w exterior raw out hrun hfirst hleft
        have hs : (w.applyAction? choice.action).isSome := by simp [hsafe]
        let s : SafeSourceChoice p q w := ⟨choice, hs⟩
        have hn : next = safeNext p q w s :=
          Option.some.inj (hsafe.symm.trans (safeNext_spec p q w s))
        subst next
        have hless : tail.length < k := by
          have hh := congrArg List.length hraw
          simp only [List.length_append, cycleArrows_length] at hh
          omega
        obtain ⟨n, t, hword, hout⟩ := ih tail.length hless
          s.1.action.target (safeNext p q w s) tail out htail hleft rfl
        refine ⟨n + 1, ⟨s, t⟩, ?_, hout⟩
        simpa only [arrows, safeCycleArrows, s, hword] using hraw

theorem atLeft_stopping_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (q : Fin ns) (w : LogicalWindow nt)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ n, raw.length = n * (4 * windowWidth w + 6) := by
  obtain ⟨n, t, hraw, _⟩ := all_atLeft_stopping_runs p hnt blank exterior q w raw out hrun hleft
  exact ⟨n, hraw ▸ arrows_length p hnt blank exterior n q w t⟩

end PakFixedPolyomino.ULogSourceObliviousStoppingGrammar
