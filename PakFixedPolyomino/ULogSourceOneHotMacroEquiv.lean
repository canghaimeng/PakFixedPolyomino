import PakFixedPolyomino.ULogSourceOneHotFullMacro
import PakFixedPolyomino.ULogSourceOneHotMacroInverse
import Mathlib.Tactic

/-!
# Canonical packaging and raw histories for one complete source macro

The canonical package retains actual literal-arrow data for each occupied
source choice.  A separate raw-history type deliberately omits that choice,
so the later inverse theorem must recover it from literal steps.
-/

namespace PakFixedPolyomino.ULogSourceOneHotMacroEquiv

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPhysicalStep ULogSourceOneHotPhysicalMacro
open ULogSourceOneHotFullMacro
open ULogSourceOneHotMacroInverse

variable {ns nt : ℕ}

structure SourceChoice (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt) where
  slot : Fin 2
  action : BoundedAction ns nt
  occupied : p.rule q read (slot = 1) = some action

theorem SourceChoice.ext {p : BoundedProgram ns nt} {q : Fin ns} {read : Fin nt}
    {a b : SourceChoice p q read} (hslot : a.slot = b.slot) : a = b := by
  cases a
  cases b
  simp_all
  subst hslot
  rename_i action₁ occupied₁ action₂ occupied₂
  have : action₁ = action₂ := Option.some.inj (occupied₁.symm.trans occupied₂)
  subst this
  rfl

def initialPhysical (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (tape : Int → Tape) (head : Int) : Config (State ns nt) Tape :=
  { state := .reading q
      (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state
    head := head
    tape := tape }

def readerHistory (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (tape : Int → Tape) (head : Int) :
    List (Arrow (program p hnt logicalBlank)) :=
  readerArrows p hnt logicalBlank q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt

@[simp] theorem readerHistory_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (tape : Int → Tape) (head : Int) :
    readerPrefix p hnt logicalBlank q tape head =
      some (readerHistory p hnt logicalBlank q tape head) := rfl

@[simp] theorem readerHistory_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (tape : Int → Tape) (head : Int) :
    (readerHistory p hnt logicalBlank q tape head).length = nt := by
  simp [readerHistory]

structure CanonicalData (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int) where
  rewind : List (Arrow (program p hnt logicalBlank))
  writer : List (Arrow (program p hnt logicalBlank))
  relocate : List (Arrow (program p hnt logicalBlank))
  rewind_ok : nonbranchArrows p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read (choice.slot = 1)
      choice.action tape (head + nt)) nt = some rewind
  writer_ok : nonbranchArrows p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.writerInitial hnt choice.action tape head) nt = some writer
  relocate_ok : nonbranchArrows p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt))
    (relocationDistance choice.action.move nt + 1) = some relocate
  run_ok : run (program p hnt logicalBlank) (fun _ => true)
    (fullArrows p hnt logicalBlank
      (readerHistory p hnt logicalBlank q tape head) rewind writer relocate
      (branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
        choice.action choice.occupied))
    (initialPhysical hnt logicalBlank q tape head) =
      some (fullEndpoint hnt choice.action tape head)

theorem canonicalData_exists (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    Nonempty (CanonicalData p hnt logicalBlank read q hlive choice tape head) := by
  obtain ⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, hrun⟩ :=
    oneHot_occupied_action_forward p hnt logicalBlank read q hlive choice.slot
      choice.action choice.occupied tape head hone
      (readerHistory p hnt logicalBlank q tape head) rfl
  exact ⟨⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, hrun⟩⟩

noncomputable def canonicalData (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    CanonicalData p hnt logicalBlank read q hlive choice tape head :=
  Classical.choice (canonicalData_exists p hnt logicalBlank read q hlive choice tape head hone)

noncomputable def canonicalArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    List (Arrow (program p hnt logicalBlank)) :=
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  fullArrows p hnt logicalBlank (readerHistory p hnt logicalBlank q tape head)
    data.rewind data.writer data.relocate
    (branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
      choice.action choice.occupied)

structure CanonicalPhysicalMacroHistory (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) where
  choice : SourceChoice p q read
  arrows : List (Arrow (program p hnt logicalBlank))
  canonical : arrows = canonicalArrows p hnt logicalBlank read q hlive choice tape head hone
  run_ok : run (program p hnt logicalBlank) (fun _ => true) arrows
    (initialPhysical hnt logicalBlank q tape head) =
      some (fullEndpoint hnt choice.action tape head)
  /-- The unique source choice follows the fixed `nt`-arrow reader prefix. -/
  first_branch_offset : (readerHistory p hnt logicalBlank q tape head).length = nt

noncomputable def forwardHistory (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    SourceChoice p q read → CanonicalPhysicalMacroHistory p hnt logicalBlank read q hlive tape head hone :=
  fun choice =>
    let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
    { choice := choice
      arrows := canonicalArrows p hnt logicalBlank read q hlive choice tape head hone
      canonical := rfl
      run_ok := data.run_ok
      first_branch_offset := readerHistory_length p hnt logicalBlank q tape head }

/-- The branch arrow in every canonical history is recovered by the local
one-step inverse, retaining its literal slot and occupied action. -/
theorem history_branch_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (h : CanonicalPhysicalMacroHistory p hnt logicalBlank read q hlive tape head hone) :
    ∃ (slot : Fin 2) (action : BoundedAction ns nt)
      (hocc : p.rule q read (slot = 1) = some action),
      branchArrow p hnt logicalBlank q read h.choice.slot (tape (head + nt)) hlive
        h.choice.action h.choice.occupied =
      branchArrow p hnt logicalBlank q read slot (tape (head + nt)) hlive action hocc ∧
      SourceChoice.mk h.choice.slot h.choice.action h.choice.occupied =
        SourceChoice.mk slot action hocc := by
  have hstep := branchArrow_step p hnt logicalBlank q read h.choice.slot
    h.choice.action hlive h.choice.occupied tape (head + nt)
  obtain ⟨slot, action, hocc, harrow, hout⟩ := ULogSourceOneHotMacroInverse.branch_success_inverse
    p hnt logicalBlank q read hlive tape (head + nt)
    (branchArrow p hnt logicalBlank q read h.choice.slot (tape (head + nt)) hlive
      h.choice.action h.choice.occupied)
    (branchResult q read h.choice.slot h.choice.action tape (head + nt)) hstep
  refine ⟨slot, action, hocc, harrow, ?_⟩
  have hslot : h.choice.slot = slot := by
    simpa [branchArrow] using
      congrArg (fun a : Arrow (program p hnt logicalBlank) => a.1.2) harrow
  apply SourceChoice.ext hslot

noncomputable def canonicalSourceChoiceEquiv (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    SourceChoice p q read ≃ CanonicalPhysicalMacroHistory p hnt logicalBlank read q hlive tape head hone where
  toFun := forwardHistory p hnt logicalBlank read q hlive tape head hone
  invFun := CanonicalPhysicalMacroHistory.choice
  left_inv := by
    intro choice
    simp [forwardHistory]
  right_inv := by
    intro h
    rcases h with ⟨choice, arrows, canonical, run_ok, first_branch_offset⟩
    subst arrows
    rfl

/-- A choice-free legal history records an actual arrow list, its successful
run, and a literal branch arrow at the fixed reader boundary.  In contrast to
the canonical package above, it does not contain a source slot or action. -/
structure RawPhysicalMacroHistory (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int) where
  arrows : List (Arrow (program p hnt logicalBlank))
  endpoint : Config (State ns nt) Tape
  branch : Arrow (program p hnt logicalBlank)
  branch_out : Config (State ns nt) Tape
  pre : List (Arrow (program p hnt logicalBlank))
  post : List (Arrow (program p hnt logicalBlank))
  decomposes : arrows = pre ++ branch :: post
  pre_length : pre.length = nt
  /-- Choice-free finite timing alternatives for the three source moves. -/
  post_length : post.length = 2 * nt + 1 ∨
    post.length = 3 * nt + 1 ∨ post.length = 4 * nt + 1
  pre_run : run (program p hnt logicalBlank) (fun _ => true) pre
    (initialPhysical hnt logicalBlank q tape head) =
      some ({ state := .branch q read, head := head + nt, tape := tape } :
        Config (State ns nt) Tape)
  run_ok : run (program p hnt logicalBlank) (fun _ => true) arrows
    (initialPhysical hnt logicalBlank q tape head) = some endpoint
  branch_step : step (program p hnt logicalBlank) (fun _ => true)
    ({ state := .branch q read, head := head + nt, tape := tape } :
      Config (State ns nt) Tape) branch = some branch_out
  post_run : run (program p hnt logicalBlank) (fun _ => true) post branch_out = some endpoint
  /-- After the chosen branch, the remainder is deterministic micro-execution. -/
  post_no_branch : ∀ n : ℕ, n ≤ post.length → ∀ c,
    run (program p hnt logicalBlank) (fun _ => true) (post.take n) branch_out = some c →
      ∀ q' read', c.state ≠ .branch q' read'
  endpoint_reader : ∃ target, endpoint.state = .reading target (initialReaderState hnt)
  first_return : ∀ n : ℕ, n < post.length → ∀ c,
    run (program p hnt logicalBlank) (fun _ => true) (post.take n) branch_out = some c →
      ∀ target, c.state ≠ .reading target (initialReaderState hnt)

/-- The literal branch step of a raw history recovers its unique occupied
source choice without reading an action or slot from the history fields. -/
theorem raw_extract_choice (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    ∃ choice : SourceChoice p q read,
      h.branch = branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
        choice.action choice.occupied ∧
      h.branch_out = branchResult q read choice.slot choice.action tape (head + nt) := by
  obtain ⟨slot, action, hocc, harrow, hout⟩ := branch_success_inverse
    p hnt logicalBlank q read hlive tape (head + nt) h.branch h.branch_out h.branch_step
  exact ⟨⟨slot, action, hocc⟩, harrow, hout⟩

/-- The macro length is move-dependent: it comprises `nt` reader ticks, one
labelled branch, `nt` rewind ticks, `nt` writer ticks, and relocation's left
distance plus its stay handoff. -/
theorem macro_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    (canonicalArrows p hnt logicalBlank read q hlive choice tape head hone).length =
      3 * nt + relocationDistance choice.action.move nt + 2 := by
  unfold canonicalArrows
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  have hr := nonbranchArrows_length p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read (choice.slot = 1)
      choice.action tape (head + nt)) nt data.rewind data.rewind_ok
  have hw := nonbranchArrows_length p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.writerInitial hnt choice.action tape head)
    nt data.writer data.writer_ok
  have hl := nonbranchArrows_length p hnt logicalBlank
    (ULogSourceOneHotPhaseEndpoints.relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt))
    (relocationDistance choice.action.move nt + 1) data.relocate data.relocate_ok
  change (fullArrows p hnt logicalBlank
    (readerHistory p hnt logicalBlank q tape head) data.rewind data.writer data.relocate
    (branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
      choice.action choice.occupied)).length = _
  simp [fullArrows, readerHistory_length, hr, hw, hl]
  omega

end PakFixedPolyomino.ULogSourceOneHotMacroEquiv
