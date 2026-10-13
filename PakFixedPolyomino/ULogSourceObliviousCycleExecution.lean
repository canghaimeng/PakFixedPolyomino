import PakFixedPolyomino.ULogSourceObliviousInitialWindowInverse

/-! # Actual complete safe scanner cycle and its entire head footprint

One initial scan W+2 followed by the checked return/LR/RL suffix3W+4
executes one actual logical action in precisely4W+6 physical arrows.
-/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open OneTapeTableau FiniteOneTapeProgram

variable {State Tape : Type*} [DecidableEq State] [DecidableEq Tape]

theorem run_head_nondecreasing (P : Program State Tape) (movable : Tape → Bool)
    (arrows : List (Arrow P)) (c out : Config State Tape)
    (hmoves : ∀ a ∈ arrows,
      (transition P a).move = .right ∨ (transition P a).move = .stay)
    (hrun : run P movable arrows c = some out) : c.head ≤ out.head := by
  induction arrows generalizing c with
  | nil => have := Option.some.inj hrun; subst out; exact le_rfl
  | cons a arrows ih =>
      cases hs : step P movable c a with
      | none => simp [run, hs] at hrun
      | some d =>
          have hd := step_some_head P movable c d a hs
          have hout := ih d (fun b hb => hmoves b (by simp [hb]))
            (by simpa [run, hs] using hrun)
          rcases hmoves a (by simp) with hright | hstay
          · rw [hright, moveHead] at hd; omega
          · rw [hstay, moveHead] at hd; omega

end PakFixedPolyomino.FiniteOneTapeSemantics

namespace PakFixedPolyomino.ULogSourceObliviousCycleExecution

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialCells ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousInitialWindowInverse ULogSourceObliviousWindowFootprint
open ULogSourceObliviousSafeSuffix
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

theorem readerAction_nonleft (blank : Fin nt)
    (r : ULogSourceLogicalBlockReader.State nt) (x : Phys) :
    (ULogSourceLogicalBlockReader.readerAction blank r x).move = .right ∨
      (ULogSourceLogicalBlockReader.readerAction blank r x).move = .stay := by
  cases r with
  | scan i mode =>
      cases mode with
      | fresh => simp only [ULogSourceLogicalBlockReader.readerAction]; split_ifs <;> simp
      | bits seen =>
          simp only [ULogSourceLogicalBlockReader.readerAction]
          split_ifs <;> try simp
          cases seen <;> simp
      | blanks => simp only [ULogSourceLogicalBlockReader.readerAction]; split_ifs <;> simp
  | done read => simp [ULogSourceLogicalBlockReader.readerAction]
  | reject => simp [ULogSourceLogicalBlockReader.readerAction]

theorem readArrows_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (isHead : Bool)
    (c : ReaderConfig (nt := nt)) (k : ℕ) :
    ∀ a ∈ readArrows p hnt blank q selected isHead c k,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  induction k generalizing c with
  | zero => simp [readArrows]
  | succ k ih =>
      intro a ha
      simp only [readArrows, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simpa only [transition, actionOf_readLiteralArrow, liftReaderAction] using
          readerAction_nonleft blank c.state (c.tape c.head)
      · exact ih _ a ha

theorem unmarkedCell_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ unmarkedCellArrows p hnt blank q selected tape head,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  intro a ha
  simp only [unmarkedCellArrows, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Or.inl (by simp [flagZeroArrow, transition])
  · exact readArrows_nonleft p hnt blank q selected false _ nt a ha

theorem markedCellPre_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ markedCellPreArrows p hnt blank q tape head,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  intro a ha
  simp only [markedCellPreArrows, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Or.inl (by simp [flagHeadArrow, transition, actionOf, program,
      ULogSourceObliviousScanProgram.step, deterministicAction,
      ULogSourceOneHotReader.one, ULogSourceOneHotReader.zero, ULogSourceOneHotReader.blank])
  · exact readArrows_nonleft p hnt blank q none true _ nt a ha

theorem unmarkedRange_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (start count : ℕ) :
    ∀ a ∈ unmarkedRangeArrows p hnt blank q selected w exterior start count,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  induction count with
  | zero => simp [unmarkedRangeArrows]
  | succ count ih =>
      intro a ha
      simp only [unmarkedRangeArrows, List.mem_append] at ha
      exact ha.elim (ih a) (unmarkedCell_nonleft p hnt blank q selected _ _ a)

theorem sourceScan_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) :
    ∀ a ∈ sourceScanArrows p hnt blank q w choice exterior,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  intro a ha
  simp only [sourceScanArrows, preBranchArrows, postBranchArrows,
    List.mem_append, List.mem_cons] at ha
  rcases ha with (rfl | hpre | hmarked) | rfl | hpost
  · exact Or.inl (by simp [startScanArrow, transition])
  · exact unmarkedRange_nonleft p hnt blank q none w exterior 0 w.head.val a hpre
  · exact markedCellPre_nonleft p hnt blank q _ _ a hmarked
  · exact Or.inr (by simp [transition, actionOf_branchArrow])
  · exact unmarkedRange_nonleft p hnt blank q (some choice.action) w exterior _ _ a hpost

theorem source_scan_footprint (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (sourceScanArrows p hnt blank q w choice exterior) (initialWindowConfig q w exterior) := by
  intro k hk
  have hrun := sourceScan_run p hnt blank q w choice exterior
  obtain ⟨middle, hm⟩ := run_take_exists (program p hnt blank) (fun _ => true) _ _ _ hrun k hk
  have hdrop : run (program p hnt blank) (fun _ => true)
      ((sourceScanArrows p hnt blank q w choice exterior).drop k) middle =
        some (startConfig q choice.action w exterior) := by
    rw [← List.take_append_drop k (sourceScanArrows p hnt blank q w choice exterior),
      run_append p hnt blank, hm, Option.bind_some] at hrun
    exact hrun
  have hlo := run_head_nondecreasing (program p hnt blank) (fun _ => true) _ _ middle
    (fun a ha => sourceScan_nonleft p hnt blank q w choice exterior a (List.mem_of_mem_take ha)) hm
  have hhi := run_head_nondecreasing (program p hnt blank) (fun _ => true) _ middle _
    (fun a ha => sourceScan_nonleft p hnt blank q w choice exterior a (List.mem_of_mem_drop ha)) hdrop
  exact ⟨middle, hm, hlo, hhi⟩

def cycleArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
    (exterior : Int → Phys) : List (ScanArrow p hnt blank) :=
  sourceScanArrows p hnt blank q w choice exterior ++
    safeSuffixArrows p hnt blank q choice.action w next hsafe

@[simp] theorem cycleArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (next : LogicalWindow nt)
    (hsafe : w.applyAction? choice.action = some next) (exterior : Int → Phys) :
    (cycleArrows p hnt blank q w choice next hsafe exterior).length = 4 * windowWidth w + 6 := by
  simp only [cycleArrows, List.length_append, sourceScanArrows_length, safeSuffixArrows_length]
  omega

theorem cycle_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (cycleArrows p hnt blank q w choice next hsafe exterior)
      (initialWindowConfig q w exterior) =
      some (initialWindowConfig choice.action.target next exterior) := by
  rw [cycleArrows, run_append p hnt blank, sourceScan_run, Option.bind_some]
  exact safe_suffix_run p hnt blank q choice.action w next hsafe exterior

theorem cycle_footprint (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
    (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (cycleArrows p hnt blank q w choice next hsafe exterior) (initialWindowConfig q w exterior) :=
  prefixInInterval_append p hnt blank _ _ _ _ _ _
    (source_scan_footprint p hnt blank q w choice exterior)
    (sourceScan_run p hnt blank q w choice exterior)
    (safe_suffix_prefix_interval p hnt blank q choice.action w next hsafe exterior)

theorem safe_cycle_correct (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (cycleArrows p hnt blank q w choice next hsafe exterior)
        (initialWindowConfig q w exterior) =
      some (initialWindowConfig choice.action.target next exterior) ∧
    (cycleArrows p hnt blank q w choice next hsafe exterior).length = 4 * windowWidth w + 6 ∧
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (cycleArrows p hnt blank q w choice next hsafe exterior) (initialWindowConfig q w exterior) :=
  ⟨cycle_run p hnt blank q w choice next hsafe exterior,
    cycleArrows_length p hnt blank q w choice next hsafe exterior,
    cycle_footprint p hnt blank q w choice next hsafe exterior⟩

/-- Actual scans, every raw run and every arrow prefix share one exact scope. -/
theorem initial_scan_exact (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    (∀ choice : SourceChoice p q (w.cells.get w.head),
      run (program p hnt blank) (fun _ => true) (sourceScanArrows p hnt blank q w choice exterior)
          (initialWindowConfig q w exterior) = some (startConfig q choice.action w exterior) ∧
      (sourceScanArrows p hnt blank q w choice exterior).length = windowWidth w + 2 ∧
      PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
        (sourceScanArrows p hnt blank q w choice exterior) (initialWindowConfig q w exterior)) ∧
    Nonempty (SourceChoice p q (w.cells.get w.head) ≃ RawInitialScan p hnt blank q w exterior) ∧
    ∀ (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt),
      run (program p hnt blank) (fun _ => true) raw (initialWindowConfig q w exterior) = some out →
      windowWidth w + 2 ≤ raw.length →
      ∃ (choice : SourceChoice p q (w.cells.get w.head)) (tail : List (ScanArrow p hnt blank)),
        raw = sourceScanArrows p hnt blank q w choice exterior ++ tail ∧
        run (program p hnt blank) (fun _ => true) tail
          (startConfig q choice.action w exterior) = some out :=
  ⟨fun choice => ⟨sourceScan_run p hnt blank q w choice exterior,
    sourceScanArrows_length p hnt blank q w choice exterior,
    source_scan_footprint p hnt blank q w choice exterior⟩,
    ⟨initialScanEquiv p hnt blank q w exterior⟩,
    raw_scan_prefix p hnt blank q w exterior⟩

end PakFixedPolyomino.ULogSourceObliviousCycleExecution
