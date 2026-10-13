import PakFixedPolyomino.ULogSourceObliviousUpdateExecution
import PakFixedPolyomino.ULogSourceObliviousRunPrefix

/-! # Arbitrary-run converse for the literal return-to-left pass

This instantiates local deterministic phase grammar for the engineer's
actual arrow list. The raw run is unrestricted and stores no source choice,
canonicality or forward-image membership. LR/RL updates are separate.
-/

namespace PakFixedPolyomino.ULogSourceObliviousReturnInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix

variable {ns nt : ℕ}

theorem nonbranchPrefix_append (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (pre tail : List (ScanArrow p hnt blank))
    (c middle : ScanCfg ns nt)
    (hpre : NonbranchPrefix p hnt blank pre c)
    (hrun : run (program p hnt blank) (fun _ => true) pre c = some middle)
    (htail : NonbranchPrefix p hnt blank tail middle) :
    NonbranchPrefix p hnt blank (pre ++ tail) c := by
  induction pre generalizing c with
  | nil =>
      have hc : c = middle := Option.some.inj hrun
      subst middle
      exact htail
  | cons a pre ih =>
      rcases hpre with ⟨hs, d, hstep, hrest⟩
      refine ⟨hs, d, hstep, ?_⟩
      apply ih d hrest
      simpa [run, hstep] using hrun

theorem returnLeftInterior_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (xs : List Phys)
    (hxs : ∀ x ∈ xs, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .returnLeft a)
    (hhead : c.head = (xs.length : Int))
    (htape : ∀ i : Fin xs.length, c.tape (i.val + 1 : Int) = xs[i.val]) :
    NonbranchPrefix p hnt blank (returnLeftInteriorArrows p hnt blank a xs hxs) c := by
  induction xs using List.reverseRecOn generalizing c with
  | nil => simp [returnLeftInteriorArrows, NonbranchPrefix]
  | append_singleton xs x ih =>
      have hx : x ≠ ULogSourceOneHotReader.blank := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, y ≠ ULogSourceOneHotReader.blank :=
        fun y hy => hxs y (by simp [hy])
      have hread : c.tape c.head = x := by
        have := htape ⟨xs.length, by simp⟩
        simpa [hhead, List.getElem_append_right'] using this
      have harrows :
          returnLeftInteriorArrows p hnt blank a (xs ++ [x]) hxs =
            returnLeftInteriorArrow p hnt blank a x hx ::
              returnLeftInteriorArrows p hnt blank a xs hxs' := by
        simp [returnLeftInteriorArrows, List.reverse_append]
      rw [harrows]
      refine ⟨?_, { state := .returnLeft a, head := c.head - 1, tape := c.tape },
        returnLeftInteriorArrow_step p hnt blank a x hx c hstate hread, ?_⟩
      · intro q read
        simp [hstate]
      · exact ih hxs'
          (c := { state := .returnLeft a, head := c.head - 1, tape := c.tape })
          rfl (by simp [hhead]) (fun i => by
            have hi := htape ⟨i.val, by simp⟩
            simpa [List.getElem_append_left'] using hi)

theorem returnLeft_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : ULogSourceObliviousWindow.LogicalWindow nt)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (returnLeftArrows p hnt blank q a w)
      (startConfig q a w exterior) := by
  let first : ScanCfg ns nt :=
    { state := .returnLeft a, head := (windowWidth w : Int), tape := windowTape w exterior }
  let middle : ScanCfg ns nt :=
    { state := .returnLeft a, head := 0, tape := windowTape w exterior }
  have hflag : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
      (startConfig q a w exterior) (postScanBoundaryArrow p hnt blank q a) = some first := by
    have h := postScanBoundaryArrow_step p hnt blank q a
      (startConfig q a w exterior) rfl (by
        simpa [startConfig] using windowTape_right w exterior)
    simpa [first, startConfig] using h
  have hinter := returnLeftInterior_nonbranchPrefix p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx) first rfl (by simp [first, windowWidth])
    (fun i => windowTape_encode w exterior i.val (by simpa [windowWidth] using i.isLt))
  have hrun := returnLeftInterior_run p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx) first rfl (by simp [first, windowWidth])
    (fun i => windowTape_encode w exterior i.val (by simpa [windowWidth] using i.isLt))
  have hboundary : NonbranchPrefix p hnt blank [returnLeftBoundaryArrow p hnt blank a] middle := by
    refine ⟨?_, _, returnLeftBoundaryArrow_step p hnt blank a middle rfl
      (windowTape_left w exterior), trivial⟩
    intro q read
    simp [middle]
  unfold returnLeftArrows
  refine ⟨?_, first, hflag, ?_⟩
  · intro q read
    simp [startConfig]
  · exact nonbranchPrefix_append p hnt blank _ _ first middle hinter hrun hboundary

/-- Every raw successful run of this pass's exact length is the actual
return-left arrow list, with the same literal physical endpoint. -/
theorem returnLeft_raw_unique
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : ULogSourceObliviousWindow.LogicalWindow nt)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (startConfig q a w exterior) = some out)
    (hlength : raw.length = windowWidth w + 2) :
    raw = returnLeftArrows p hnt blank q a w ∧
      out = { state := .updateLRFlag a false, head := 1, tape := windowTape w exterior } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (returnLeft_nonbranchPrefix p hnt blank q a w exterior)
  obtain ⟨heq, hout⟩ := forcedPrefix_unique_successful_run
    (program p hnt blank) (fun _ => true) _ raw _ out hforced hrun
    (by simpa using hlength.symm)
  refine ⟨heq, ?_⟩
  have hforward := returnLeft_run p hnt blank q a w exterior
  exact Option.some.inj (hout.symm.trans hforward)

/-- Exact forward pass and an actual chronological prefix at the left
delimiter. -/
theorem returnLeft_exact_pass
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : ULogSourceObliviousWindow.LogicalWindow nt)
    (exterior : Int → Phys) :
    ∃ (arrows pre tail : List (ScanArrow p hnt blank)) (atZero : ScanCfg ns nt),
      arrows.length = windowWidth w + 2 ∧
      run (program p hnt blank) (fun _ => true) arrows (startConfig q a w exterior) =
        some { state := .updateLRFlag a false, head := 1, tape := windowTape w exterior } ∧
      arrows = pre ++ tail ∧
      run (program p hnt blank) (fun _ => true) pre (startConfig q a w exterior) =
        some atZero ∧ atZero.head = 0 := by
  let interior := returnLeftInteriorArrows p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx)
  refine ⟨returnLeftArrows p hnt blank q a w,
    postScanBoundaryArrow p hnt blank q a :: interior,
    [returnLeftBoundaryArrow p hnt blank a],
    { state := .returnLeft a, head := 0, tape := windowTape w exterior },
    by simp, returnLeft_run p hnt blank q a w exterior, rfl, ?_, rfl⟩
  have hflag := postScanBoundaryArrow_step p hnt blank q a
    (startConfig q a w exterior) rfl (by
      simpa [startConfig] using windowTape_right w exterior)
  have hinter := returnLeftInterior_run p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx)
    { state := .returnLeft a, head := (windowWidth w : Int), tape := windowTape w exterior }
    rfl (by simp [windowWidth])
    (fun i => windowTape_encode w exterior i.val (by simpa [windowWidth] using i.isLt))
  rw [run_cons, hflag, Option.bind_some]
  simpa [interior, startConfig] using hinter

end PakFixedPolyomino.ULogSourceObliviousReturnInverse
