import PakFixedPolyomino.ULogSourceObliviousHaltingLeaves

/-! # Literal time bounds for all successful physical prefixes

A raw run longer than one complete cycle must pass its safe endpoint: an
overflow rejection cannot continue. Repeating this argument recovers a
source trace even when the final raw endpoint is in the middle of a phase.
The ordinary source time bound then bounds EVERY successful physical word.
-/

namespace PakFixedPolyomino.ULogSourceObliviousRunTime

open FiniteOneTapeProgram FiniteOneTapeHaltingRestriction FiniteOneTapeSemantics
open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousCycleInverse ULogSourceObliviousCycleTraces
open ULogSourceObliviousCompletedCyclePrefix ULogSourceObliviousOverflowExecution
open StandardNondeterministicMachine StandardMachineZipperBridge StandardMachineWindowBridge
open ULogSourceObliviousHaltingProgram ULogSourceObliviousHaltingCounts

variable {ns nt : ℕ}

theorem extended_cycle_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : 4 * windowWidth w + 6 < raw.length) :
    ∃ (choice : ULogSourceOneHotMacroEquiv.SourceChoice p q (w.cells.get w.head))
      (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
      (tail : List (ScanArrow p hnt blank)),
      raw = cycleArrows p hnt blank q w choice next hsafe exterior ++ tail ∧
      FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) tail
        (initialWindowConfig choice.action.target next exterior) = some out := by
  let n := 4 * windowWidth w + 6
  have hsplit : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
      (raw.take n ++ raw.drop n) (initialWindowConfig q w exterior) = some out := by
    simpa using hrun
  rw [run_append p hnt blank] at hsplit
  cases hpre : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
      (raw.take n) (initialWindowConfig q w exterior) with
  | none => simp [hpre] at hsplit
  | some middle =>
      have htail : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
          (raw.drop n) middle = some out := by simpa [hpre] using hsplit
      have hpreLen : (raw.take n).length = 4 * windowWidth w + 6 := by
        simp [List.length_take, n, Nat.min_eq_left (Nat.le_of_lt hlen)]
      rcases full_cycle_outcome p hnt blank q w exterior (raw.take n) middle
          hpre hpreLen with hsafe | hreject
      · obtain ⟨choice, next, hsafe, hword, hmiddle⟩ := hsafe
        refine ⟨choice, next, hsafe, raw.drop n, ?_, ?_⟩
        · rw [← hword]
          exact (List.take_append_drop n raw).symm
        · simpa [hmiddle] using htail
      · have hne : raw.drop n ≠ [] := by
          intro he
          have hh := congrArg List.length he
          simp only [List.length_drop, List.length_nil] at hh
          dsimp [n] at hh
          omega
        rw [reject_run_nonempty p hnt blank middle (raw.drop n) hreject hne] at htail
        cases htail

theorem raw_trace_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : n * (4 * windowWidth w + 6) < raw.length) :
    ∃ (t : Trace p n q w) (tail : List (ScanArrow p hnt blank)),
      raw = arrows p hnt blank exterior n q w t ++ tail ∧
      FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) tail
        (initialWindowConfig (endpoint p n q w t).1 (endpoint p n q w t).2 exterior) =
        some out := by
  induction n generalizing q w raw out with
  | zero => exact ⟨PUnit.unit, raw, rfl, hrun⟩
  | succ n ih =>
      have hfirst : 4 * windowWidth w + 6 < raw.length := by
        rw [Nat.succ_mul] at hlen
        omega
      obtain ⟨choice, next, hsafe, rest, hraw, hrest⟩ :=
        extended_cycle_prefix p hnt blank q w exterior raw out hrun hfirst
      have hs : (w.applyAction? choice.action).isSome := by simp [hsafe]
      let s : SafeSourceChoice p q w := ⟨choice, hs⟩
      have hn : next = safeNext p q w s :=
        Option.some.inj (hsafe.symm.trans (safeNext_spec p q w s))
      subst next
      have hrestLen : n * (4 * windowWidth (safeNext p q w s) + 6) < rest.length := by
        have hh := congrArg List.length hraw
        simp only [List.length_append, cycleArrows_length] at hh
        rw [safeNext_width]
        rw [Nat.succ_mul] at hlen
        omega
      obtain ⟨t, tail, hword, htail⟩ := ih s.1.action.target (safeNext p q w s)
        rest out hrest hrestLen
      refine ⟨⟨s, t⟩, tail, ?_, htail⟩
      simpa only [arrows, safeCycleArrows, s, hword, List.append_assoc] using hraw

theorem all_original_runs_length_le (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys)
    (raw : List (Arrow (original M))) (out : ScanCfg ns nt)
    (hrun : FiniteOneTapeSemantics.run (original M) (fun _ => true) raw
      (initialWindowConfig M.start (inputWindow M x bound) exterior) = some out) :
    raw.length ≤ (bound + 1) *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) := by
  by_contra hlarge
  have hlen : (bound + 1) * (4 * windowWidth (inputWindow M x bound) + 6) < raw.length := by
    simpa only [StandardMachineScannerCounts.inputWindow_width] using Nat.lt_of_not_ge hlarge
  obtain ⟨t, tail, hword, htail⟩ := raw_trace_prefix (toBounded M)
    (Nat.zero_lt_of_lt M.blank.isLt) M.blank exterior (bound + 1) M.start
    (inputWindow M x bound) raw out hrun hlen
  have hlogical := ULogSourceObliviousLogicalRuns.slots_run (toBounded M) (bound + 1)
    M.start (inputWindow M x bound) t
  obtain ⟨actual, hactual, hactualrun, hout⟩ := run_window_inverse M
    (ULogSourceObliviousLogicalRuns.slots (toBounded M) (bound + 1) M.start
      (inputWindow M x bound) t)
    (inputOrigin bound) (inputSize x bound) (initial M x)
    (initial_headIn M x bound) _ hlogical
  have hb := htime _ actual hactualrun
  rw [ULogSourceObliviousLogicalRuns.slots_length] at hb
  omega

theorem all_halt_runs_length_le (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys)
    (raw : List (Arrow (haltProgram M))) (out : ScanCfg ns nt)
    (hrun : FiniteOneTapeSemantics.run (haltProgram M) (fun _ => true) raw
      (initialWindowConfig M.start (inputWindow M x bound) exterior) = some out) :
    raw.length ≤ (bound + 1) *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) := by
  have hinclude := (run_includeArrows (original M) (halted M) (fun _ => true) raw
    (initialWindowConfig M.start (inputWindow M x bound) exterior)).trans hrun
  have hlength := all_original_runs_length_le M x bound htime exterior
    (raw.map (includeArrow (original M) (halted M))) out hinclude
  exact (List.length_map (as := raw) (includeArrow (original M) (halted M))) ▸ hlength

end PakFixedPolyomino.ULogSourceObliviousRunTime
