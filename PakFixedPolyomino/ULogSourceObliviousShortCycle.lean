import PakFixedPolyomino.ULogSourceObliviousPhaseSources

/-! # No premature return to the left boundary

Every compared history is an arbitrary successful raw arrow list. Before the
source branch the actual deterministic prefix is independent of a choice.
After the branch the selected action is recovered from its literal arrow.
Safe and both overflow phases then exclude premature atLeft endpoints.
-/

namespace PakFixedPolyomino.ULogSourceObliviousShortCycle

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousScanInverse ULogSourceObliviousUpdateExecution
open ULogSourceObliviousWindow ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousInitialWindowInverse ULogSourceObliviousRunPrefix
open ULogSourceObliviousReturnInverse ULogSourceObliviousSafeSuffix
open ULogSourceObliviousOverflowExecution ULogSourceObliviousPhaseSources

variable {ns nt : ℕ}

theorem short_phase_no_atLeft (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (pre raw : List (ScanArrow p hnt blank)) (c out : ScanCfg ns nt)
    (hphase : NonbranchPrefix p hnt blank pre c)
    (hsources : ∀ a ∈ pre, NotAtLeft p hnt blank a)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlen : raw.length < pre.length) : ¬ ∃ q, out.state = State.atLeft q := by
  apply short_forced_prefix_excludes (program p hnt blank) (fun _ => true)
    (fun s => ∃ q, s = State.atLeft q) pre raw c out
    (nonbranchPrefix_forced p hnt blank pre c hphase) ?_ hrun hlen
  intro a ha
  rintro ⟨q, hq⟩
  exact hsources a ha q hq

theorem reject_phase_no_atLeft (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (pre raw : List (ScanArrow p hnt blank)) (c out stop : ScanCfg ns nt)
    (hphase : NonbranchPrefix p hnt blank pre c)
    (hsources : ∀ a ∈ pre, NotAtLeft p hnt blank a)
    (hpre : run (program p hnt blank) (fun _ => true) pre c = some stop)
    (hstop : stop.state = State.reject)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out) :
    ¬ ∃ q, out.state = State.atLeft q := by
  by_cases hshort : raw.length < pre.length
  · exact short_phase_no_atLeft p hnt blank pre raw c out hphase hsources hrun hshort
  · obtain ⟨tail, middle, hraw, hmiddle, htail⟩ :=
      nonbranchPrefix_split_successful_run p hnt blank pre raw c out hphase hrun
        (Nat.le_of_not_gt hshort)
    have hm : middle = stop := Option.some.inj (hmiddle.symm.trans hpre)
    subst middle
    by_cases hnil : tail = []
    · rw [hnil, run_nil] at htail
      have heq : stop = out := Option.some.inj htail
      rintro ⟨q, hq⟩
      exact reject_ne_atLeft ((heq ▸ hstop).symm.trans hq)
    · rw [reject_run_nonempty p hnt blank stop tail hstop hnil] at htail
      cases htail

theorem nonempty_atLeft_run_cycle_lower_bound
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hne : raw ≠ []) (hleft : ∃ r, out.state = State.atLeft r) :
    4 * windowWidth w + 6 ≤ raw.length := by
  by_contra hlen
  have hshort : raw.length < 4 * windowWidth w + 6 := Nat.lt_of_not_ge hlen
  let pre := preBranchArrows p hnt blank q w exterior
  have hp := preBranch_nonbranch p hnt blank q w exterior
  by_cases hbefore : raw.length < pre.length
  · cases raw with
    | nil => exact hne rfl
    | cons a rest =>
        rcases hp with ⟨hs, d, hstep, htail⟩
        cases ha : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
          (initialWindowConfig q w exterior) a with
        | none => simp [run, ha] at hrun
        | some e =>
            have he := nonbranch_success_unique p hnt blank
              (initialWindowConfig q w exterior) e d hs a
              (startScanArrow p hnt blank q) ha hstep
            subst a
            have hed := step_label_deterministic (program p hnt blank) (fun _ => true)
              _ e d _ ha hstep
            subst e
            apply short_phase_no_atLeft p hnt blank pre.tail rest d out
              htail (preBranch_tail_sources p hnt blank q w exterior) ?_ ?_ hleft
            · simpa [run, hstep] using hrun
            · simpa [pre, preBranchArrows] using hbefore
  · obtain ⟨tail, boundary, hraw, hboundary, htail⟩ :=
      nonbranchPrefix_split_successful_run p hnt blank pre raw
        (initialWindowConfig q w exterior) out hp hrun (Nat.le_of_not_gt hbefore)
    have hb : boundary = preBranchConfig q w exterior :=
      Option.some.inj (hboundary.symm.trans (preBranch_run p hnt blank q w exterior))
    subst boundary
    cases tail with
    | nil =>
        rw [run_nil] at htail
        have hout : preBranchConfig q w exterior = out := Option.some.inj htail
        obtain ⟨r, hr⟩ := hleft
        simp [← hout, preBranchConfig] at hr
    | cons b rest =>
        cases hs : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
          (preBranchConfig q w exterior) b with
        | none => simp [run, hs] at htail
        | some d =>
            have hr : run (program p hnt blank) (fun _ => true) rest d = some out := by
              simpa [run, hs] using htail
            obtain ⟨choice, hb, hd⟩ := branch_success_inverse p hnt blank q
              (w.cells.get w.head) (windowTape w exterior) (cellHead nt (w.head.val + 1))
              b d hs
            have hd' : d = postBranchConfig q choice.action w exterior := hd
            subst d
            let post := postBranchArrows p hnt blank q choice.action w exterior
            have hpost := postBranch_nonbranch p hnt blank q choice.action w exterior
            have hpostRun := postBranch_run p hnt blank q choice.action w exterior
            have hpostSources := postBranch_sources p hnt blank q choice.action w exterior
            cases hact : w.applyAction? choice.action with
            | some next =>
                let suffix := safeSuffixArrows p hnt blank q choice.action w next hact
                have hphase := nonbranchPrefix_append p hnt blank post suffix _
                  (startConfig q choice.action w exterior) hpost hpostRun
                  (safe_suffix_nonbranch p hnt blank q choice.action w next hact exterior)
                apply short_phase_no_atLeft p hnt blank (post ++ suffix) rest _ out
                  hphase ?_ hr ?_ hleft
                · intro a ha
                  rcases List.mem_append.mp ha with ha | ha
                  · exact hpostSources a ha
                  · exact safeSuffix_sources p hnt blank q choice.action w next hact a ha
                · have he := congrArg List.length hraw
                  simp only [List.length_append, List.length_cons, pre, preBranchArrows_length] at he
                  have hpartition := scan_length_partition w
                  simp only [List.length_append, post, postBranchArrows_length,
                    suffix, safeSuffixArrows_length]
                  omega
            | none =>
                rcases (applyAction?_eq_none_iff w choice.action).mp hact with
                  ⟨hmove, hover⟩ | ⟨hmove, hover⟩
                · let suffix := unsafeRightPrefix p hnt blank q choice.action w hmove hover
                  obtain ⟨tape, hsuf⟩ :=
                    unsafeRightPrefix_run p hnt blank q choice.action w hmove hover exterior
                  have hphase := nonbranchPrefix_append p hnt blank post suffix _
                    (startConfig q choice.action w exterior) hpost hpostRun
                    (unsafeRightPrefix_nonbranch p hnt blank q choice.action w hmove hover exterior)
                  apply reject_phase_no_atLeft p hnt blank (post ++ suffix) rest _ out
                    { state := .reject, head := (windowWidth w + 1 : Int), tape := tape }
                    hphase ?_ ?_ rfl hr hleft
                  · intro a ha
                    rcases List.mem_append.mp ha with ha | ha
                    · exact hpostSources a ha
                    · exact unsafeRightPrefix_sources p hnt blank q choice.action w hmove hover a ha
                  · rw [run_append p hnt blank, hpostRun, Option.bind_some]
                    exact hsuf
                · let suffix := unsafeLeftPrefix p hnt blank q choice.action w hmove hover
                  obtain ⟨tape, hsuf⟩ :=
                    unsafeLeftPrefix_run p hnt blank q choice.action w hmove hover exterior
                  have hphase := nonbranchPrefix_append p hnt blank post suffix _
                    (startConfig q choice.action w exterior) hpost hpostRun
                    (unsafeLeftPrefix_nonbranch p hnt blank q choice.action w hmove hover exterior)
                  apply reject_phase_no_atLeft p hnt blank (post ++ suffix) rest _ out
                    { state := .reject, head := 0, tape := tape }
                    hphase ?_ ?_ rfl hr hleft
                  · intro a ha
                    rcases List.mem_append.mp ha with ha | ha
                    · exact hpostSources a ha
                    · exact unsafeLeftPrefix_sources p hnt blank q choice.action w hmove hover a ha
                  · rw [run_append p hnt blank, hpostRun, Option.bind_some]
                    exact hsuf

end PakFixedPolyomino.ULogSourceObliviousShortCycle
