import PakFixedPolyomino.ULogSourceObliviousCompletedCycle

/-! # Completed-cycle grammar inside arbitrary longer histories

A full-length successful cycle either has the safe logical endpoint or
rejects at its final left boundary. A successful continuation from the latter
is impossible. Therefore a longer raw run ending atLeft recovers its FIRST
safe cycle, without assuming an atLeft intermediate endpoint or a supplied
decomposition. This is a prefix law, not a source clock or full-frame count.
-/

namespace PakFixedPolyomino.ULogSourceObliviousCompletedCyclePrefix

open FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousInitialWindowInverse
open ULogSourceObliviousCycleExecution ULogSourceObliviousSafeSuffix
open ULogSourceObliviousOverflowExecution
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

theorem full_cycle_outcome (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : raw.length = 4 * windowWidth w + 6) :
    (∃ (choice : SourceChoice p q (w.cells.get w.head)) (next : LogicalWindow nt)
      (hsafe : w.applyAction? choice.action = some next),
      raw = cycleArrows p hnt blank q w choice next hsafe exterior ∧
        out = initialWindowConfig choice.action.target next exterior) ∨
    out.state = State.reject := by
  have hscanLen : windowWidth w + 2 ≤ raw.length := by rw [hlen]; omega
  obtain ⟨choice, tail, hraw, htail⟩ :=
    raw_scan_prefix p hnt blank q w exterior raw out hrun hscanLen
  have htlen : tail.length = 3 * windowWidth w + 4 := by
    have he := congrArg List.length hraw
    simp only [List.length_append, sourceScanArrows_length] at he
    omega
  cases hact : w.applyAction? choice.action with
  | none =>
      rcases (applyAction?_eq_none_iff w choice.action).mp hact with
        ⟨hmove, hover⟩ | ⟨hmove, hhd⟩
      · exact (unsafe_right_no_suffix_run p hnt blank q choice.action w
          hmove hover exterior tail out htail htlen).elim
      · exact Or.inr (unsafe_left_suffix_reject p hnt blank q choice.action w
          hmove hhd exterior tail out htail htlen)
  | some next =>
      obtain ⟨hsuf, hout⟩ := safe_suffix_raw_unique p hnt blank q choice.action
        w next hact exterior tail out htail htlen
      refine Or.inl ⟨choice, next, hact, ?_, ?_⟩
      · rw [cycleArrows, hraw, hsuf]
      · simpa [initialWindowConfig] using hout

theorem raw_completed_cycle_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : 4 * windowWidth w + 6 ≤ raw.length)
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ (choice : SourceChoice p q (w.cells.get w.head)) (next : LogicalWindow nt)
      (hsafe : w.applyAction? choice.action = some next)
      (tail : List (ScanArrow p hnt blank)),
      raw = cycleArrows p hnt blank q w choice next hsafe exterior ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        (initialWindowConfig choice.action.target next exterior) = some out := by
  let n := 4 * windowWidth w + 6
  have hsplit : run (program p hnt blank) (fun _ => true)
      (raw.take n ++ raw.drop n) (initialWindowConfig q w exterior) = some out := by
    simpa using hrun
  rw [ULogSourceObliviousUpdateExecution.run_append p hnt blank] at hsplit
  cases hpre : run (program p hnt blank) (fun _ => true)
      (raw.take n) (initialWindowConfig q w exterior) with
  | none => simp [hpre] at hsplit
  | some middle =>
      have htail : run (program p hnt blank) (fun _ => true) (raw.drop n) middle =
          some out := by simpa [hpre] using hsplit
      have hpreLen : (raw.take n).length = 4 * windowWidth w + 6 := by
        simp [List.length_take, n, Nat.min_eq_left hlen]
      rcases full_cycle_outcome p hnt blank q w exterior (raw.take n) middle
          hpre hpreLen with hsafe | hreject
      · obtain ⟨choice, next, hsafe, hword, hmiddle⟩ := hsafe
        refine ⟨choice, next, hsafe, raw.drop n, ?_, ?_⟩
        · rw [← hword]
          exact (List.take_append_drop n raw).symm
        · simpa [hmiddle] using htail
      · by_cases hnil : raw.drop n = []
        · rw [hnil, run_nil] at htail
          have heq : middle = out := Option.some.inj htail
          rw [heq] at hreject
          obtain ⟨r, hr⟩ := hleft
          exact (reject_ne_atLeft (hreject.symm.trans hr)).elim
        · have hnone := reject_run_nonempty p hnt blank middle (raw.drop n) hreject hnil
          rw [hnone] at htail
          cases htail

end PakFixedPolyomino.ULogSourceObliviousCompletedCyclePrefix
