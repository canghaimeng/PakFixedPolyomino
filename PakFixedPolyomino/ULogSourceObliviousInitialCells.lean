import PakFixedPolyomino.ULogSourceObliviousWindowFootprint

/-! # Actual flag/read cells of the initial whole-window scan

Reader arrows and their nonbranch prefixes are explicit. A marked cell adds
one literal occupied source slot after its deterministic read prefix.
-/

namespace PakFixedPolyomino.ULogSourceObliviousInitialCells

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix
open ULogSourceObliviousReturnInverse (nonbranchPrefix_append)
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

theorem readArrows_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (c : ReaderConfig (nt := nt)) (k : ℕ)
    (hscan : ∀ j, j < k → ∃ i mode,
      (((ULogSourceLogicalBlockReader.nextConfig blank)^[j] c).state = .scan i mode)) :
    NonbranchPrefix p hnt blank (readArrows p hnt blank q selected isHead c k)
      (embedReaderConfig q selected isHead c) := by
  induction k generalizing c with
  | zero => trivial
  | succ k ih =>
      have hscan₀ : ∃ i mode, c.state = .scan i mode := hscan 0 (by omega)
      have hscanTail : ∀ j, j < k → ∃ i mode,
          (((ULogSourceLogicalBlockReader.nextConfig blank)^[j]
            (ULogSourceLogicalBlockReader.nextConfig blank c)).state = .scan i mode) := by
        intro j hj
        obtain ⟨i, mode, hs⟩ := hscan (j + 1) (by omega)
        refine ⟨i, mode, ?_⟩
        rw [← Function.iterate_succ_apply]
        exact hs
      refine ⟨?_, _, readLiteralArrow_step p hnt blank q selected isHead c hscan₀,
        ih _ hscanTail⟩
      intro q' read
      obtain ⟨i, mode, hs⟩ := hscan₀
      simpa [embedReaderConfig, hs, liftReaderTarget]

theorem oneHot_pre_scan (blank read : Fin nt) (hnt : 0 < nt)
    (tape : Int → Phys) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∀ j, j < nt → ∃ i mode,
      (((ULogSourceLogicalBlockReader.nextConfig blank)^[j]
        (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head)).state = .scan i mode) := by
  intro j hj
  rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
    blank read hnt tape head hone j (by omega)]
  by_cases hzero : j = 0
  · subst j
    exact ⟨⟨0, hnt⟩, .fresh, by simp [ULogSourceLogicalBlockReader.oneHotExpected]⟩
  · by_cases hbefore : j ≤ read.val
    · exact ⟨⟨j, hj⟩, .bits none, by
        simp [ULogSourceLogicalBlockReader.oneHotExpected,
          ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore]⟩
    · exact ⟨⟨j, hj⟩, .bits (some read), by
        simp [ULogSourceLogicalBlockReader.oneHotExpected,
          ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore, hj]⟩

def oneHotReadArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (isHead : Bool)
    (tape : Int → Phys) (head : Int) : List (ScanArrow p hnt blank) :=
  readArrows p hnt blank q selected isHead
    (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head) nt

@[simp] theorem oneHotReadArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (tape : Int → Phys) (head : Int) :
    (oneHotReadArrows p hnt blank q selected isHead tape head).length = nt := by
  simp [oneHotReadArrows]

theorem oneHotReadArrows_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (tape : Int → Phys) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    run (program p hnt blank) (fun _ => true)
      (oneHotReadArrows p hnt blank q selected isHead tape head)
      { state := .read q selected isHead (.scan ⟨0, hnt⟩ .fresh)
        head := head, tape := tape } =
      some { state := if isHead then .branch q read else .flag q selected
             head := head + nt, tape := tape } := by
  have hr := read_exact_run p hnt blank q selected isHead
    (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head) nt
    (oneHot_pre_scan blank read hnt tape head hone)
  rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
    blank read hnt tape head hone nt le_rfl] at hr
  simpa [oneHotReadArrows, embedReaderConfig, liftReaderTarget,
    ULogSourceLogicalBlockReader.initialConfig,
    ULogSourceLogicalBlockReader.oneHotExpected,
    ULogSourceLogicalBlockReader.oneHotStage_terminal] using hr

theorem oneHotReadArrows_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (tape : Int → Phys) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    NonbranchPrefix p hnt blank
      (oneHotReadArrows p hnt blank q selected isHead tape head)
      { state := .read q selected isHead (.scan ⟨0, hnt⟩ .fresh)
        head := head, tape := tape } := by
  simpa [oneHotReadArrows, embedReaderConfig, liftReaderTarget,
    ULogSourceLogicalBlockReader.initialConfig] using
    readArrows_nonbranch p hnt blank q selected isHead
      (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head) nt
      (oneHot_pre_scan blank read hnt tape head hone)

def unmarkedCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (tape : Int → Phys) (head : Int) : List (ScanArrow p hnt blank) :=
  flagZeroArrow p hnt blank q selected ::
    oneHotReadArrows p hnt blank q selected false tape (head + 1)

def markedCellPreArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (tape : Int → Phys) (head : Int) : List (ScanArrow p hnt blank) :=
  flagHeadArrow p hnt blank q ::
    oneHotReadArrows p hnt blank q none true tape (head + 1)

def markedCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank read : Fin nt)
    (q : Fin ns) (choice : SourceChoice p q read) (tape : Int → Phys) (head : Int) :
    List (ScanArrow p hnt blank) :=
  markedCellPreArrows p hnt blank q tape head ++
    [branchArrow p hnt blank q read (tape (head + 1 + nt))
      choice.slot choice.action choice.occupied]

@[simp] theorem unmarkedCellArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (tape : Int → Phys) (head : Int) :
    (unmarkedCellArrows p hnt blank q selected tape head).length = nt + 1 := by
  simp [unmarkedCellArrows]

@[simp] theorem markedCellPreArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (tape : Int → Phys) (head : Int) :
    (markedCellPreArrows p hnt blank q tape head).length = nt + 1 := by
  simp [markedCellPreArrows]

@[simp] theorem markedCellArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (choice : SourceChoice p q read)
    (tape : Int → Phys) (head : Int) :
    (markedCellArrows p hnt blank read q choice tape head).length = nt + 2 := by
  simp [markedCellArrows]

theorem unmarkedCell_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank read : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (tape : Int → Phys) (head : Int)
    (hflag : tape head = zero)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape (head + 1)) :
    run (program p hnt blank) (fun _ => true)
      (unmarkedCellArrows p hnt blank q selected tape head)
      { state := .flag q selected, head := head, tape := tape } =
      some { state := .flag q selected, head := head + 1 + nt, tape := tape } := by
  rw [unmarkedCellArrows, run_cons,
    flagZeroArrow_step p hnt blank q selected _ rfl hflag, Option.bind_some]
  simpa using oneHotReadArrows_run p hnt blank read q selected false tape (head + 1) hone

theorem unmarkedCell_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (tape : Int → Phys) (head : Int) (hflag : tape head = zero)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape (head + 1)) :
    NonbranchPrefix p hnt blank (unmarkedCellArrows p hnt blank q selected tape head)
      { state := .flag q selected, head := head, tape := tape } := by
  refine ⟨?_, _, flagZeroArrow_step p hnt blank q selected _ rfl hflag,
    oneHotReadArrows_nonbranch p hnt blank read q selected false tape (head + 1) hone⟩
  intro q' read'; simp

theorem markedCellPre_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank read : Fin nt)
    (q : Fin ns) (tape : Int → Phys) (head : Int) (hflag : tape head = one)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape (head + 1)) :
    run (program p hnt blank) (fun _ => true) (markedCellPreArrows p hnt blank q tape head)
      { state := .flag q none, head := head, tape := tape } =
      some { state := .branch q read, head := head + 1 + nt, tape := tape } := by
  rw [markedCellPreArrows, run_cons,
    flagHeadArrow_step p hnt blank q _ rfl hflag, Option.bind_some]
  simpa using oneHotReadArrows_run p hnt blank read q none true tape (head + 1) hone

theorem markedCellPre_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (tape : Int → Phys) (head : Int)
    (hflag : tape head = one)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape (head + 1)) :
    NonbranchPrefix p hnt blank (markedCellPreArrows p hnt blank q tape head)
      { state := .flag q none, head := head, tape := tape } := by
  refine ⟨?_, _, flagHeadArrow_step p hnt blank q _ rfl hflag,
    oneHotReadArrows_nonbranch p hnt blank read q none true tape (head + 1) hone⟩
  intro q' read'; simp

theorem markedCell_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank read : Fin nt)
    (q : Fin ns) (choice : SourceChoice p q read) (tape : Int → Phys) (head : Int)
    (hflag : tape head = one)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape (head + 1)) :
    run (program p hnt blank) (fun _ => true) (markedCellArrows p hnt blank read q choice tape head)
      { state := .flag q none, head := head, tape := tape } =
      some { state := .flag q (some choice.action), head := head + 1 + nt, tape := tape } := by
  rw [markedCellArrows, run_append p hnt blank,
    markedCellPre_run p hnt blank read q tape head hflag hone, Option.bind_some, run_cons]
  rw [branchArrow_step p hnt blank q read _ choice rfl, Option.bind_some, run_nil]

end PakFixedPolyomino.ULogSourceObliviousInitialCells
