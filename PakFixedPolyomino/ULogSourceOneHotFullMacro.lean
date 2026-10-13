import PakFixedPolyomino.ULogSourceOneHotPhaseEndpoints
import Mathlib.Tactic

/-!
# Exact full source-step macro histories

This layer concatenates the literal reader prefix, the one labelled source
choice, and the three deterministic physical phases.  The resulting list
retains every occupied arrow in chronological order.
-/

namespace PakFixedPolyomino.ULogSourceOneHotFullMacro

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPhysicalStep ULogSourceOneHotPhysicalMacro
open ULogSourceOneHotPhaseEndpoints

variable {ns nt : ℕ}

theorem run_append (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (xs ys : List (Arrow (program p hnt logicalBlank)))
    (c : Config (State ns nt) Tape) :
    run (program p hnt logicalBlank) (fun _ => true) (xs ++ ys) c =
      (run (program p hnt logicalBlank) (fun _ => true) xs c).bind
        (run (program p hnt logicalBlank) (fun _ => true) ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, run_cons]
      cases hstep : step (program p hnt logicalBlank) (fun _ => true) c x with
      | none => simp [hstep]
      | some c' => simp [hstep, ih]

theorem run_append_some (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (xs ys : List (Arrow (program p hnt logicalBlank)))
    (c d e : Config (State ns nt) Tape)
    (hxs : run (program p hnt logicalBlank) (fun _ => true) xs c = some d)
    (hys : run (program p hnt logicalBlank) (fun _ => true) ys d = some e) :
    run (program p hnt logicalBlank) (fun _ => true) (xs ++ ys) c = some e := by
  rw [run_append, hxs]
  exact hys

theorem rewind_avoids_branch (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) :
    ∀ k : ℕ, k < nt → ∀ q' read',
      ((nextMicroConfig hnt logicalBlank)^[k]
        (rewindInitial hnt q read slot a tape head)).state ≠ .branch q' read' := by
  intro k hk q' read'
  rw [iterate_rewind_expected hnt logicalBlank q read slot a tape head k (by omega)]
  simp [rewindExpected, rewindStage, hk]

theorem writer_avoids_branch (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ∀ k : ℕ, k < nt → ∀ q read,
      ((nextMicroConfig hnt logicalBlank)^[k]
        (writerInitial hnt a tape head)).state ≠ .branch q read := by
  intro k hk q read
  rw [iterate_writer_expected hnt logicalBlank a tape head k (by omega)]
  simp [writerExpected, writerStage, hk]

theorem relocate_avoids_branch (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ∀ k : ℕ, k < relocationDistance a.move nt + 1 → ∀ q read,
      ((nextMicroConfig hnt logicalBlank)^[k]
        (relocateInitial a tape head)).state ≠ .branch q read := by
  intro k hk q read
  have hk' : k ≤ relocationDistance a.move nt := by omega
  rw [iterate_relocate_expected hnt logicalBlank a tape head k hk']
  simp [relocateExpected]

/-- The literal full history for one occupied source action. -/
def fullArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt)
    (reader rewind writer relocate : List (Arrow (program p hnt logicalBlank)))
    (branch : Arrow (program p hnt logicalBlank)) :
    List (Arrow (program p hnt logicalBlank)) :=
  reader ++ (branch :: (rewind ++ (writer ++ relocate)))

def fullEndpoint (hnt : 0 < nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) : Config (State ns nt) Tape :=
  { state := .reading a.target (initialReaderState hnt)
    head := head + nt - relocationDistance a.move nt
    tape := ULogSourceOneHotWriter.writePrefix a.write head tape nt }

/-- A valid one-hot block, followed by a chosen occupied source rule, has an
actual concatenated physical history through reader, branch, rewind, writer,
and relocation.  The endpoint is the next source reader at the exact
relocated head. -/
theorem oneHot_occupied_action_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (hlive : haltedSource q = false) (slot : Fin 2)
    (a : BoundedAction ns nt) (hocc : p.rule q read (slot = 1) = some a)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (reader : List (Arrow (program p hnt logicalBlank)))
    (hreader : readerPrefix p hnt logicalBlank q tape head = some reader) :
    ∃ rewind writer relocate,
      nonbranchArrows p hnt logicalBlank
        (rewindInitial hnt q read (slot = 1) a tape (head + nt)) nt = some rewind ∧
      nonbranchArrows p hnt logicalBlank
        (writerInitial hnt a tape head) nt = some writer ∧
      nonbranchArrows p hnt logicalBlank
        (relocateInitial a
          (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
        (relocationDistance a.move nt + 1) = some relocate ∧
      run (program p hnt logicalBlank) (fun _ => true)
        (fullArrows p hnt logicalBlank reader rewind writer relocate
          (branchArrow p hnt logicalBlank q read slot (tape (head + nt)) hlive a hocc))
        { state := .reading q
            (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state,
          head := head,
          tape := tape } =
        some (fullEndpoint hnt a tape head) := by
  obtain ⟨rewind, hrewind⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank
    (rewindInitial hnt q read (slot = 1) a tape (head + nt)) nt
    (rewind_avoids_branch hnt logicalBlank q read (slot = 1) a tape (head + nt))
  obtain ⟨writer, hwriter⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank (writerInitial hnt a tape head) nt
    (writer_avoids_branch hnt logicalBlank a tape head)
  obtain ⟨relocate, hrelocate⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank
    (relocateInitial a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
    (relocationDistance a.move nt + 1)
    (relocate_avoids_branch hnt logicalBlank a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
  refine ⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, ?_⟩
  have hreaderRun := readerPrefix_oneHot_run p hnt logicalBlank read q hlive
    tape head hone reader hreader
  have hbranchRun := branchArrow_step p hnt logicalBlank q read slot a hlive hocc
    tape (head + nt)
  have hbranchInitial : ULogSourceOneHotPhysicalMacro.branchResult q read slot a tape (head + nt) =
      rewindInitial hnt q read (slot = 1) a tape (head + nt) := by
    apply config_ext <;>
      simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
  have hrewindRun := nonbranchArrows_run p hnt logicalBlank
    (rewindInitial hnt q read (slot = 1) a tape (head + nt)) nt rewind hrewind
  have hrewindEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (rewindInitial hnt q read (slot = 1) a tape (head + nt))) =
      writerInitial hnt a tape head := by
    rw [rewind_operational_terminal]
    apply config_ext <;> simp [writerInitial] <;> omega
  have hwriterRun := nonbranchArrows_run p hnt logicalBlank
    (writerInitial hnt a tape head) nt writer hwriter
  have hwriterEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (writerInitial hnt a tape head)) =
      relocateInitial a
        (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt) := by
    rw [writer_operational_terminal]
    apply config_ext
    · simp only [relocateInitial, relocateExpected]
      congr
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  have hrelocateRun := nonbranchArrows_run p hnt logicalBlank
    (relocateInitial a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
    (relocationDistance a.move nt + 1) relocate hrelocate
  have hrelocateEnd := relocate_operational_terminal hnt logicalBlank a
    (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt)
  unfold fullArrows
  apply run_append_some p hnt logicalBlank reader
    (branchArrow p hnt logicalBlank q read slot (tape (head + nt)) hlive a hocc ::
      (rewind ++ (writer ++ relocate)))
    _ _ _ hreaderRun
  rw [run_cons, hbranchRun]
  simp only [Option.bind_some]
  rw [hbranchInitial]
  apply run_append_some p hnt logicalBlank rewind (writer ++ relocate) _ _ _
  · rw [hrewindRun, hrewindEnd]
  · apply run_append_some p hnt logicalBlank writer relocate _ _ _
    · rw [hwriterRun, hwriterEnd]
    · rw [hrelocateRun, hrelocateEnd]
      rfl

/-- The designated all-blank physical block follows the same exact full
history, with its reader handoff selecting `logicalBlank`. -/
theorem blank_occupied_action_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : haltedSource q = false) (slot : Fin 2)
    (a : BoundedAction ns nt) (hocc : p.rule q logicalBlank (slot = 1) = some a)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (reader : List (Arrow (program p hnt logicalBlank)))
    (hreader : readerPrefix p hnt logicalBlank q tape head = some reader) :
    ∃ rewind writer relocate,
      nonbranchArrows p hnt logicalBlank
        (rewindInitial hnt q logicalBlank (slot = 1) a tape (head + nt)) nt = some rewind ∧
      nonbranchArrows p hnt logicalBlank
        (writerInitial hnt a tape head) nt = some writer ∧
      nonbranchArrows p hnt logicalBlank
        (relocateInitial a
          (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
        (relocationDistance a.move nt + 1) = some relocate ∧
      run (program p hnt logicalBlank) (fun _ => true)
        (fullArrows p hnt logicalBlank reader rewind writer relocate
          (branchArrow p hnt logicalBlank q logicalBlank slot
            (tape (head + nt)) hlive a hocc))
        { state := .reading q
            (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state,
          head := head,
          tape := tape } =
        some (fullEndpoint hnt a tape head) := by
  obtain ⟨rewind, hrewind⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (slot = 1) a tape (head + nt)) nt
    (rewind_avoids_branch hnt logicalBlank q logicalBlank (slot = 1) a tape (head + nt))
  obtain ⟨writer, hwriter⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank (writerInitial hnt a tape head) nt
    (writer_avoids_branch hnt logicalBlank a tape head)
  obtain ⟨relocate, hrelocate⟩ := nonbranchArrows_exists_of_avoids_branch
    p hnt logicalBlank
    (relocateInitial a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
    (relocationDistance a.move nt + 1)
    (relocate_avoids_branch hnt logicalBlank a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
  refine ⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, ?_⟩
  have hreaderRun := readerPrefix_blank_run p hnt logicalBlank q hlive
    tape head hblank reader hreader
  have hbranchRun := branchArrow_step p hnt logicalBlank q logicalBlank slot a hlive hocc
    tape (head + nt)
  have hbranchInitial :
      ULogSourceOneHotPhysicalMacro.branchResult q logicalBlank slot a tape (head + nt) =
      rewindInitial hnt q logicalBlank (slot = 1) a tape (head + nt) := by
    apply config_ext <;>
      simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
  have hrewindRun := nonbranchArrows_run p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (slot = 1) a tape (head + nt)) nt rewind hrewind
  have hrewindEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (rewindInitial hnt q logicalBlank (slot = 1) a tape (head + nt))) =
      writerInitial hnt a tape head := by
    rw [rewind_operational_terminal]
    apply config_ext <;> simp [writerInitial] <;> omega
  have hwriterRun := nonbranchArrows_run p hnt logicalBlank
    (writerInitial hnt a tape head) nt writer hwriter
  have hwriterEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (writerInitial hnt a tape head)) =
      relocateInitial a
        (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt) := by
    rw [writer_operational_terminal]
    apply config_ext
    · simp only [relocateInitial, relocateExpected]
      congr
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  have hrelocateRun := nonbranchArrows_run p hnt logicalBlank
    (relocateInitial a
      (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt))
    (relocationDistance a.move nt + 1) relocate hrelocate
  have hrelocateEnd := relocate_operational_terminal hnt logicalBlank a
    (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt)
  unfold fullArrows
  apply run_append_some p hnt logicalBlank reader
    (branchArrow p hnt logicalBlank q logicalBlank slot
      (tape (head + nt)) hlive a hocc :: (rewind ++ (writer ++ relocate)))
    _ _ _ hreaderRun
  rw [run_cons, hbranchRun]
  simp only [Option.bind_some]
  rw [hbranchInitial]
  apply run_append_some p hnt logicalBlank rewind (writer ++ relocate) _ _ _
  · rw [hrewindRun, hrewindEnd]
  · apply run_append_some p hnt logicalBlank writer relocate _ _ _
    · rw [hwriterRun, hwriterEnd]
    · rw [hrelocateRun, hrelocateEnd]
      rfl

end PakFixedPolyomino.ULogSourceOneHotFullMacro
