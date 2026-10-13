import PakFixedPolyomino.ULogSourceOneHotPaddedStep
import PakFixedPolyomino.ULogSourceOneHotRawReconstruct
import PakFixedPolyomino.ULogSourceOneHotRepresentation
import Mathlib.Tactic

namespace PakFixedPolyomino.ULogSourceOneHotPaddedMacro

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPaddedStep

variable {ns nt : ℕ}

theorem actionOf_eq_of_rule_eq
    {State' Tape' : Type*} [Fintype State'] [Fintype Tape']
    [DecidableEq State'] [DecidableEq Tape']
    (P : Program State' Tape') (arrow : Arrow P) (act : Action State' Tape')
    (h : P.rule arrow.1.1.1 arrow.1.1.2 arrow.1.2 = some act) :
    actionOf P arrow = act := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact False.elim (by simpa [h] using hnone)

theorem padded_run_append (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt)
    (xs ys : List (Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)))
    (c : Config (State ns nt) Tape) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (xs ++ ys) c =
      (run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
        xs c).bind
        (run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
          (fun _ => true) ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, run_cons]
      cases hstep : step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) c x with
      | none => simp [hstep]
      | some next => simp [hstep, ih]

def liftBaseConfig
    (c : Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) :
    Config (ULogSourceOneHotPaddedStep.State ns nt) Tape :=
  { state := .base c.state, head := c.head, tape := c.tape }

/-- Every literal base-program label remains occupied in the padded program.
At the completed relocation label the target changes to the padding handoff,
but the source/read/slot label itself is unchanged. -/
def liftBaseArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt)
    (ar : Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)) :
    Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) := by
  rcases ar with ⟨⟨⟨s, x⟩, slot⟩, har⟩
  refine ⟨⟨⟨State.base s, x⟩, slot⟩, ?_⟩
  cases s <;> fin_cases slot <;>
    simp [ULogSourceOneHotPhysicalStep.program,
      ULogSourceOneHotPhysicalStep.step,
      ULogSourceOneHotPaddedStep.program,
      ULogSourceOneHotPaddedStep.step] at har ⊢ <;> assumption

@[simp] theorem liftBaseArrow_source
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (ar : Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)) :
    (liftBaseArrow p hnt logicalBlank ar).1.1.1 = .base ar.1.1.1 := by
  rcases ar with ⟨⟨⟨s, x⟩, slot⟩, har⟩
  rfl

@[simp] theorem liftBaseArrow_read
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (ar : Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)) :
    (liftBaseArrow p hnt logicalBlank ar).1.1.2 = ar.1.1.2 := by
  rcases ar with ⟨⟨⟨s, x⟩, slot⟩, har⟩
  rfl

@[simp] theorem liftBaseArrow_slot
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (ar : Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)) :
    (liftBaseArrow p hnt logicalBlank ar).1.2 = ar.1.2 := by
  rcases ar with ⟨⟨⟨s, x⟩, slot⟩, har⟩
  rfl

def liftBaseArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt)
    (as : List (Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank))) :
    List (Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)) :=
  as.map (liftBaseArrow p hnt logicalBlank)

@[simp] theorem liftBaseArrows_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (as : List (Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank))) :
    (liftBaseArrows p hnt logicalBlank as).length = as.length := by
  simp [liftBaseArrows]

theorem readerArrows_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) : ∀ (c : Config (ULogSourceLogicalBlockReader.State nt) Tape)
      (n : ℕ) (arrow : Arrow
        (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)),
      arrow ∈ ULogSourceOneHotPhysicalMacro.readerArrows p hnt logicalBlank q c n →
      ∀ q' read',
        (transition (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)
          arrow).sourceState ≠ .branch q' read' := by
  intro c n
  induction n generalizing c with
  | zero => simp [ULogSourceOneHotPhysicalMacro.readerArrows]
  | succ n ih =>
      intro arrow hmem q' read'
      simp only [ULogSourceOneHotPhysicalMacro.readerArrows, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst arrow
        simp [ULogSourceOneHotPhysicalMacro.readArrow,
          ULogSourceOneHotPhysicalMacro.microArrow]
      · exact ih _ arrow htail q' read'

theorem liftedReaderArrows_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (tape : Int → Tape) (head : Int)
    (arrow : Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank))
    (hmem : arrow ∈ liftBaseArrows p hnt logicalBlank
      (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head)) :
    ∀ q' read',
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        arrow).sourceState ≠ .base (.branch q' read') := by
  simp only [liftBaseArrows, List.mem_map] at hmem
  rcases hmem with ⟨baseArrow, hbaseMem, rfl⟩
  intro q' read' heq
  have hne := readerArrows_source_nonbranch p hnt logicalBlank q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt
    baseArrow hbaseMem q' read'
  have heq' :
      State.base baseArrow.1.1.1 = State.base (.branch q' read') := by
    simpa [FiniteOneTapeProgram.transition] using heq
  have hinner : baseArrow.1.1.1 = .branch q' read' := by
    exact State.base.inj heq'
  exact hne (by simpa [FiniteOneTapeProgram.transition] using hinner)

theorem nonbranchArrows_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt) :
    ∀ (c : Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) (n : ℕ)
      (as : List (Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank))),
      ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank c n = some as →
      ∀ arrow, arrow ∈ as → ∀ q read,
        (transition (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)
          arrow).sourceState ≠ .branch q read := by
  intro c n
  induction n generalizing c with
  | zero =>
      intro as hgen arrow hmem
      have : as = [] := by
        simpa [ULogSourceOneHotPhysicalMacro.nonbranchArrows] using
          Option.some.inj hgen
      subst as
      simp at hmem
  | succ n ih =>
      intro as hgen arrow hmem q' read'
      rcases c with ⟨s, head, tape⟩
      cases s with
      | branch q read => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows] at hgen
      | reading q r =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.reading q r, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.readArrow,
                  ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'
      | rewind q read slot a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.rewind q read slot a i, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.rewindArrow,
                  ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'
      | writing a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.writing a i, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.writeArrow,
                  ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'
      | relocate a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.relocate a i, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.relocateArrow,
                  ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'
      | accept =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.accept, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'
      | reject =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.reject, head, tape⟩) n with
          | none => simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · simp [ULogSourceOneHotPhysicalMacro.microArrow]
              · exact ih _ tail htail arrow hmem q' read'

theorem liftedNonbranchArrows_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (c : Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) (n : ℕ)
    (as : List (Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)))
    (hgen : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank c n =
      some as) (arrow : Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank))
    (hmem : arrow ∈ liftBaseArrows p hnt logicalBlank as) :
    ∀ q read,
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        arrow).sourceState ≠ .base (.branch q read) := by
  simp only [liftBaseArrows, List.mem_map] at hmem
  rcases hmem with ⟨baseArrow, hbaseMem, rfl⟩
  intro q read heq
  have hne := nonbranchArrows_source_nonbranch p hnt logicalBlank c n as
    hgen baseArrow hbaseMem q read
  have heq' : State.base baseArrow.1.1.1 = State.base (.branch q read) := by
    simpa [FiniteOneTapeProgram.transition] using heq
  exact hne (by
    have := State.base.inj heq'
    simpa [FiniteOneTapeProgram.transition] using this)

/-- Before the completed relocation handoff, a canonical slot-zero base
microstep commutes literally with the padded state embedding. -/
theorem lift_microArrow_step_before_handoff
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (s : ULogSourceOneHotPhysicalStep.State ns nt) (tape : Int → Tape)
    (head : Int) (hs : ∀ q read, s ≠ .branch q read)
    (hrelocate : ∀ (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)),
      s = .relocate a i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1) :
    FiniteOneTapeSemantics.step
      (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseConfig
        ({ state := s, head := head, tape := tape } :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape))
      (liftBaseArrow p hnt logicalBlank
        (ULogSourceOneHotPhysicalMacro.microArrow p hnt logicalBlank s
          (tape head) hs)) =
      some (liftBaseConfig
        (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
          ({ state := s, head := head, tape := tape } :
            Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape))) := by
  cases s with
  | branch q read => exact False.elim (hs q read rfl)
  | reading q r =>
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]

  | rewind q read slot a i =>
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]
  | writing a i =>
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]
  | relocate a i =>
      have hnot := hrelocate a i rfl
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, hnot, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]
  | accept =>
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]
  | reject =>
      simp [liftBaseConfig, liftBaseArrow,
        ULogSourceOneHotPhysicalMacro.microArrow,
        ULogSourceOneHotPhysicalMacro.nextMicroConfig,
        ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
        baseMicroAction, liftAction, FiniteOneTapeSemantics.step,
        FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]

/-- The unique labelled source-choice arrow commutes with the padded state
embedding; padding changes only the later relocation handoff. -/
theorem lift_branchArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hocc : p.rule q read (slot = 1) = some a)
    (tape : Int → Tape) (head : Int) :
    FiniteOneTapeSemantics.step
      (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseConfig
        ({ state := .branch q read, head := head, tape := tape } :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape))
      (liftBaseArrow p hnt logicalBlank
        (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
          slot (tape head) hlive a hocc)) =
      some (liftBaseConfig
        (ULogSourceOneHotPhysicalMacro.branchResult q read slot a tape head)) := by
  let act : Action (ULogSourceOneHotPhysicalStep.State ns nt) Tape :=
    ⟨tape head, .rewind q read (slot = 1) a ⟨0, Fin.pos read⟩, .stay⟩
  have hrule :
      (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank).rule
        (.branch q read) (tape head) slot =
      some act := by
    simp [ULogSourceOneHotPhysicalStep.program,
      ULogSourceOneHotPhysicalStep.step,
      ULogSourceOneHotPhysicalStep.branchAction, hlive, hocc, act]
  have hpaddedRule :
      (ULogSourceOneHotPaddedStep.program p hnt logicalBlank).rule
        (.base (.branch q read)) (tape head) slot =
      some (liftAction act) := by
    simp [ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
      hrule]
  have haction :
      actionOf (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc)) = liftAction act := by
    have hlook :
        (ULogSourceOneHotPaddedStep.program p hnt logicalBlank).rule
          (liftBaseArrow p hnt logicalBlank
            (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
              slot (tape head) hlive a hocc)).1.1.1
          (liftBaseArrow p hnt logicalBlank
            (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
              slot (tape head) hlive a hocc)).1.1.2
          (liftBaseArrow p hnt logicalBlank
            (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
              slot (tape head) hlive a hocc)).1.2 =
        some (liftAction act) := by
      simpa [ULogSourceOneHotPhysicalMacro.branchArrow] using hpaddedRule
    exact actionOf_eq_of_rule_eq _ _ _ hlook
  have hsource :
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc))).sourceState =
        .base (.branch q read) := by rfl
  have hread :
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc))).read = tape head := by rfl
  have htarget :
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc))).targetState =
        .base (.rewind q read (slot = 1) a ⟨0, Fin.pos read⟩) := by
    change (actionOf _ _).target = _
    rw [haction]
    rfl
  have hwrite :
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc))).write = tape head := by
    change (actionOf _ _).write = _
    rw [haction]
    rfl
  have hmove :
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (liftBaseArrow p hnt logicalBlank
          (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
            slot (tape head) hlive a hocc))).move = .stay := by
    change (actionOf _ _).move = _
    rw [haction]
    rfl
  have hbaseSource :
      (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
        slot (tape head) hlive a hocc).1.1.1 = .branch q read := rfl
  have hbaseRead :
      (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read
        slot (tape head) hlive a hocc).1.1.2 = tape head := rfl
  simp [FiniteOneTapeSemantics.step, liftBaseConfig,
    liftBaseArrow_source, liftBaseArrow_read, hbaseSource, hbaseRead,
    hsource, hread, htarget, hwrite, hmove,
    ULogSourceOneHotPhysicalMacro.branchResult,
    FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead]

/-- A generated deterministic base prefix lifts pointwise until (but not
including) the completed relocation handoff. -/
theorem lift_nonbranchArrows_run_before_handoff
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (c : Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) (n : ℕ)
    (as : List (Arrow (ULogSourceOneHotPhysicalStep.program p hnt logicalBlank)))
    (hgen : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank c n =
      some as)
    (hbefore : ∀ k, k < n → ∀ (a : BoundedAction ns nt)
      (i : Fin (2 * nt + 1)),
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k] c).state =
          .relocate a i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseArrows p hnt logicalBlank as) (liftBaseConfig c) =
      some (liftBaseConfig
        ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[n] c)) := by
  induction n generalizing c as with
  | zero =>
      have has : as = [] := by
        simpa [ULogSourceOneHotPhysicalMacro.nonbranchArrows] using
          Option.some.inj hgen
      subst as
      rfl
  | succ n ih =>
      rcases c with ⟨s, head, tape⟩
      have hcurReloc : ∀ (a : BoundedAction ns nt)
          (i : Fin (2 * nt + 1)),
          s = .relocate a i →
            ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1 := by
        intro a i heq
        exact hbefore 0 (by omega) a i (by simpa using heq)
      have htailBefore : ∀ k, k < n → ∀ (a : BoundedAction ns nt)
          (i : Fin (2 * nt + 1)),
          ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
            (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
              ⟨s, head, tape⟩)).state = .relocate a i →
            ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1 := by
        intro k hk a i heq
        apply hbefore (k + 1) (by omega) a i
        simpa only [Function.iterate_succ_apply] using heq
      cases s with
      | branch q read =>
          simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows] at hgen
      | reading q r =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.reading q r, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.reading q r, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.readArrow p hnt logicalBlank q r
                        (tape head))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.reading q r, head, tape⟩)) by
                    simpa [ULogSourceOneHotPhysicalMacro.readArrow] using
                      lift_microArrow_step_before_handoff p hnt logicalBlank
                        (.reading q r) tape head
                        (by intro q' read' heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore
      | rewind q read slot a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.rewind q read slot a i, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.rewind q read slot a i, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.rewindArrow p hnt logicalBlank
                        q read slot a i (tape head))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.rewind q read slot a i, head, tape⟩)) by
                    simpa [ULogSourceOneHotPhysicalMacro.rewindArrow] using
                      lift_microArrow_step_before_handoff p hnt logicalBlank
                        (.rewind q read slot a i) tape head
                        (by intro q' read' heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore
      | writing a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.writing a i, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.writing a i, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.writeArrow p hnt logicalBlank
                        a i (tape head))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.writing a i, head, tape⟩)) by
                    simpa [ULogSourceOneHotPhysicalMacro.writeArrow] using
                      lift_microArrow_step_before_handoff p hnt logicalBlank
                        (.writing a i) tape head
                        (by intro q' read' heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore
      | relocate a i =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.relocate a i, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.relocate a i, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.relocateArrow p hnt logicalBlank
                        a i (tape head))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.relocate a i, head, tape⟩)) by
                    simpa [ULogSourceOneHotPhysicalMacro.relocateArrow] using
                      lift_microArrow_step_before_handoff p hnt logicalBlank
                        (.relocate a i) tape head
                        (by intro q' read' heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore
      | accept =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.accept, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.accept, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.microArrow p hnt logicalBlank
                        .accept (tape head) (by intro q read heq; cases heq))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.accept, head, tape⟩)) by
                    exact lift_microArrow_step_before_handoff p hnt logicalBlank
                      .accept tape head (by intro q read heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore
      | reject =>
          cases htail : ULogSourceOneHotPhysicalMacro.nonbranchArrows p hnt logicalBlank
              (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                ⟨.reject, head, tape⟩) n with
          | none =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
          | some tail =>
              simp [ULogSourceOneHotPhysicalMacro.nonbranchArrows, htail] at hgen
              subst as
              simp only [liftBaseArrows, List.map_cons, run_cons]
              rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
                    (fun _ => true) (liftBaseConfig ⟨.reject, head, tape⟩)
                    (liftBaseArrow p hnt logicalBlank
                      (ULogSourceOneHotPhysicalMacro.microArrow p hnt logicalBlank
                        .reject (tape head) (by intro q read heq; cases heq))) =
                  some (liftBaseConfig
                    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
                      ⟨.reject, head, tape⟩)) by
                    exact lift_microArrow_step_before_handoff p hnt logicalBlank
                      .reject tape head (by intro q read heq; cases heq) hcurReloc]
              simp only [Option.bind_some]
              rw [Function.iterate_succ_apply]
              simpa [liftBaseArrows] using ih _ _ htail htailBefore

theorem iterate_liftReaderConfig (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) (n : ℕ) :
    (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[n]
        (ULogSourceOneHotPhysicalMacro.liftReaderConfig q c) =
      ULogSourceOneHotPhysicalMacro.liftReaderConfig q
        ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        _ = ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
            ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[n]
              (ULogSourceOneHotPhysicalMacro.liftReaderConfig q c)) := by
              rw [Function.iterate_succ_apply']
        _ = ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank
            (ULogSourceOneHotPhysicalMacro.liftReaderConfig q
              ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c)) := by
              rw [ih]
        _ = ULogSourceOneHotPhysicalMacro.liftReaderConfig q
            (ULogSourceLogicalBlockReader.nextConfig logicalBlank
              ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c)) :=
              ULogSourceOneHotPhysicalMacro.nextMicroConfig_liftReaderConfig
                hnt logicalBlank q hlive _
        _ = _ := by rw [Function.iterate_succ_apply']

theorem oneHot_reader_before_handoff
    (hnt : 0 < nt) (logicalBlank read : Fin nt) (q : Fin ns)
    (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∀ k, k < nt → ∀ (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)),
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        (ULogSourceOneHotPhysicalMacro.liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head))).state =
          .relocate a i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1 := by
  intro k hk a i heq
  rw [iterate_liftReaderConfig hnt logicalBlank q hlive] at heq
  obtain ⟨j, mode, hscan⟩ :=
    ULogSourceOneHotPhysicalMacro.oneHot_initial_scanning logicalBlank read hnt
      tape head hone k hk
  simp [ULogSourceOneHotPhysicalMacro.liftReaderConfig,
    ULogSourceOneHotPhysicalMacro.liftReaderControl, hscan] at heq

theorem blank_reader_before_handoff
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt →
      tape (head + i) = ULogSourceLogicalBlockReader.blank) :
    ∀ k, k < nt → ∀ (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)),
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        (ULogSourceOneHotPhysicalMacro.liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head))).state =
          .relocate a i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a.move nt ≤ i.1 := by
  intro k hk a i heq
  rw [iterate_liftReaderConfig hnt logicalBlank q hlive] at heq
  obtain ⟨j, mode, hscan⟩ :=
    ULogSourceOneHotPhysicalMacro.blank_initial_scanning logicalBlank hnt
      tape head hblank k hk
  simp [ULogSourceOneHotPhysicalMacro.liftReaderConfig,
    ULogSourceOneHotPhysicalMacro.liftReaderControl, hscan] at heq

theorem padded_oneHot_reader_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseArrows p hnt logicalBlank
        (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head))
      (liftBaseConfig
        (ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head)) =
      some (liftBaseConfig
        (Config.mk (.branch q read) (head + nt) tape :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) := by
  have hgen := ULogSourceOneHotRawReconstruct.readerHistory_nonbranchArrows
    p hnt logicalBlank read q hlive tape head hone
  let readerStart := ULogSourceOneHotPhysicalMacro.liftReaderConfig q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)
  have hrun := lift_nonbranchArrows_run_before_handoff p hnt logicalBlank
    readerStart nt
    (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head)
    (by simpa [readerStart] using hgen)
    (by simpa [readerStart] using
      oneHot_reader_before_handoff hnt logicalBlank read q hlive tape head hone)
  have hend :
      (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[nt]
        readerStart =
      (Config.mk (.branch q read) (head + nt) tape :
        Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) := by
    rw [show readerStart = ULogSourceOneHotPhysicalMacro.liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) by rfl,
      iterate_liftReaderConfig hnt logicalBlank q hlive,
      ULogSourceLogicalBlockReader.oneHot_operational_terminal
        logicalBlank read hnt tape head hone]
    rfl
  rw [hend] at hrun
  have hinitial :
      ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head =
        readerStart := by rfl
  rw [hinitial]
  exact hrun

theorem padded_blank_reader_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt →
      tape (head + i) = ULogSourceLogicalBlockReader.blank) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseArrows p hnt logicalBlank
        (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head))
      (liftBaseConfig
        (ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head)) =
      some (liftBaseConfig
        (Config.mk (.branch q logicalBlank) (head + nt) tape :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) := by
  have hgen := ULogSourceOneHotRawReconstruct.blankReaderHistory_nonbranchArrows
    p hnt logicalBlank q hlive tape head hblank
  let readerStart := ULogSourceOneHotPhysicalMacro.liftReaderConfig q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)
  have hrun := lift_nonbranchArrows_run_before_handoff p hnt logicalBlank
    readerStart nt
    (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head)
    (by simpa [readerStart] using hgen)
    (by simpa [readerStart] using
      blank_reader_before_handoff hnt logicalBlank q hlive tape head hblank)
  have hend :
      (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[nt]
        readerStart =
      (Config.mk (.branch q logicalBlank) (head + nt) tape :
        Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) := by
    rw [show readerStart = ULogSourceOneHotPhysicalMacro.liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) by rfl,
      iterate_liftReaderConfig hnt logicalBlank q hlive,
      ULogSourceLogicalBlockReader.blank_operational_terminal
        logicalBlank hnt tape head hblank]
    rfl
  rw [hend] at hrun
  have hinitial :
      ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head =
        readerStart := by rfl
  rw [hinitial]
  exact hrun

theorem post_prefix_before_handoff
    (hnt : 0 < nt) (logicalBlank read : Fin nt) (q : Fin ns)
    (slot : Bool) (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ∀ k, k < 2 * nt + ULogSourceOneHotPhysicalStep.relocationDistance a.move nt →
      ∀ (a' : BoundedAction ns nt) (i : Fin (2 * nt + 1)),
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read slot a tape
          (head + nt))).state = .relocate a' i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a'.move nt ≤ i.1 := by
  intro k hk a' i heq hdone
  have hnext :
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k + 1]
        (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read slot a tape
          (head + nt))).state =
        .reading a'.target (ULogSourceOneHotPhysicalStep.initialReaderState hnt) := by
    rw [Function.iterate_succ_apply']
    let ck :=
      (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read slot a tape
          (head + nt))
    have heq' : ck.state = .relocate a' i := by
      simpa [ck] using heq
    change (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank ck).state = _
    rcases hc : ck with ⟨state, pos, physical⟩
    rw [hc] at heq'
    change state = .relocate a' i at heq'
    subst state
    simp [ULogSourceOneHotPhysicalMacro.nextMicroConfig,
      ULogSourceOneHotPhysicalStep.microAction, hdone]
  have hnot := ULogSourceOneHotRawReconstruct.post_iterate_not_reader_before
    hnt logicalBlank q read slot a tape head (k + 1) (by omega) a'.target
  exact hnot hnext

def completedRelocationIndex (a : BoundedAction ns nt) : Fin (2 * nt + 1) :=
  ⟨ULogSourceOneHotPhysicalStep.relocationDistance a.move nt,
    by have h := ULogSourceOneHotPhaseEndpoints.relocationDistance_le a; omega⟩

def relocationHandoff (hnt : 0 < nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) : Config (State ns nt) Tape :=
  match a.move with
  | .right =>
      { state := .padding a ⟨0, by omega⟩, head := head, tape := tape }
  | .stay =>
      { state := .padding a ⟨nt, by omega⟩, head := head, tape := tape }
  | .left =>
      { state := .base (.reading a.target
          (ULogSourceOneHotPhysicalStep.initialReaderState hnt)),
        head := head, tape := tape }

/-- The final base relocation label is intercepted by the padded program and
lands at the move-specific padding handoff, with physical tape and head
unchanged. -/
theorem lift_completed_relocation_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    FiniteOneTapeSemantics.step
      (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (liftBaseConfig
        (Config.mk (.relocate a (completedRelocationIndex a)) head tape :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape))
      (liftBaseArrow p hnt logicalBlank
        (ULogSourceOneHotPhysicalMacro.relocateArrow p hnt logicalBlank a
          (completedRelocationIndex a) (tape head))) =
      some (relocationHandoff hnt a tape head) := by
  have hnt0 : nt ≠ 0 := by omega
  have hntNeDouble : nt ≠ 2 * nt := by omega
  cases hm : a.move <;>
    simp [liftBaseConfig, liftBaseArrow,
      ULogSourceOneHotPhysicalMacro.relocateArrow,
      ULogSourceOneHotPhysicalMacro.microArrow,
      ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
      baseMicroAction, relocationHandoff, completedRelocationIndex,
      ULogSourceOneHotPhysicalStep.relocationDistance, hm,
      hnt0, hntNeDouble, FiniteOneTapeSemantics.step,
      FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead,
      FiniteOneTapeProgram.transition, FiniteOneTapeProgram.actionOf]

def paddingArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt)) (x : Tape) :
    Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) :=
  ⟨((State.padding a i, x), 0), by
    simp [ULogSourceOneHotPaddedStep.program, ULogSourceOneHotPaddedStep.step,
      paddingAction]⟩

def nextPaddingConfig (hnt : 0 < nt) (a : BoundedAction ns nt)
    (c : Config (ULogSourceOneHotPaddedStep.State ns nt) Tape) :
    Config (ULogSourceOneHotPaddedStep.State ns nt) Tape :=
  let x := c.tape c.head
  let act := paddingAction hnt a (match c.state with | .padding _ i => i | _ => ⟨0, by omega⟩) x
  { state := act.target, head := moveHead act.move c.head, tape := writtenTape c act.write }

theorem paddingArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt) (i : Fin (2 * nt))
    (tape : Int → Tape) (head : Int) :
    FiniteOneTapeSemantics.step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      ({ state := .padding a i, head := head, tape := tape } :
        Config (ULogSourceOneHotPaddedStep.State ns nt) Tape)
      (paddingArrow p hnt logicalBlank a i (tape head)) =
      some (nextPaddingConfig hnt a
        ({ state := .padding a i, head := head, tape := tape } :
          Config (ULogSourceOneHotPaddedStep.State ns nt) Tape)) := by
  by_cases hlast : i.1 + 1 = 2 * nt <;>
    simp [paddingArrow, ULogSourceOneHotPaddedStep.program,
      ULogSourceOneHotPaddedStep.step, paddingAction, nextPaddingConfig,
      hlast, FiniteOneTapeSemantics.step, transition, actionOf, writtenTape, moveHead]

theorem nextPaddingConfig_not_last (hnt : 0 < nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt))
    (tape : Int → Tape) (head : Int) (hnext : i.1 + 1 < 2 * nt) :
    nextPaddingConfig hnt a
      ({ state := .padding a i, head := head, tape := tape } :
        Config (State ns nt) Tape) =
      Config.mk (State.padding a ⟨i.1 + 1, hnext⟩) head tape := by
  have hlast : i.1 + 1 ≠ 2 * nt := by omega
  simp [nextPaddingConfig, paddingAction, hlast,
    FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead]

theorem nextPaddingConfig_last (hnt : 0 < nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt))
    (tape : Int → Tape) (head : Int) (hlast : i.1 + 1 = 2 * nt) :
    nextPaddingConfig hnt a
      ({ state := .padding a i, head := head, tape := tape } :
        Config (State ns nt) Tape) =
      Config.mk (State.base (.reading a.target
        (ULogSourceOneHotPhysicalStep.initialReaderState hnt))) head tape := by
  simp [nextPaddingConfig, paddingAction, hlast,
    FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead]

/-- Literal padding ledger starting at counter `i` with the supplied fuel.
The intended call uses exactly `2*nt-i` ticks. -/
def paddingArrowsFromFuel (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) (i : ℕ) (hi : i < 2 * nt) :
    ℕ → List (Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank))
  | 0 => []
  | fuel + 1 =>
      paddingArrow p hnt logicalBlank a ⟨i, hi⟩ (tape head) ::
        if hnext : i + 1 < 2 * nt then
          paddingArrowsFromFuel p hnt logicalBlank a tape head (i + 1) hnext fuel
        else []

@[simp] theorem paddingArrowsFromFuel_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (i fuel : ℕ) (hi : i < 2 * nt) (hbound : i + fuel ≤ 2 * nt) :
    (paddingArrowsFromFuel p hnt logicalBlank a tape head i hi fuel).length = fuel := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
      simp only [paddingArrowsFromFuel, List.length_cons]
      by_cases hnext : i + 1 < 2 * nt
      · simp [hnext, ih (i := i + 1) hnext (by omega)]
      · have hfuel : fuel = 0 := by omega
        subst fuel
        simp [hnext]

/-- Exact operational execution of every remaining deterministic padding
tick, including the final handoff to the next source reader. -/
theorem paddingArrowsFromFuel_run_to_reader
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (i fuel : ℕ) (hi : i < 2 * nt) (hexact : i + fuel = 2 * nt) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (paddingArrowsFromFuel p hnt logicalBlank a tape head i hi fuel)
      (Config.mk (State.padding a ⟨i, hi⟩) head tape :
        Config (State ns nt) Tape) =
      some (Config.mk (State.base (.reading a.target
        (ULogSourceOneHotPhysicalStep.initialReaderState hnt)))
        head tape : Config (State ns nt) Tape) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
      simp only [paddingArrowsFromFuel, run_cons]
      rw [paddingArrow_step]
      by_cases hnext : i + 1 < 2 * nt
      · simp only [hnext, dite_true, Option.bind_eq_bind]
        rw [nextPaddingConfig_not_last hnt a ⟨i, hi⟩ tape head hnext]
        exact ih (i := i + 1) hnext (by omega)
      · have hlast : i + 1 = 2 * nt := by omega
        have hfuel : fuel = 0 := by omega
        subst fuel
        simp only [hnext, dite_false, run_nil]
        rw [nextPaddingConfig_last hnt a ⟨i, hi⟩ tape head hlast]
        rfl

theorem paddingArrowsFromFuel_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (i fuel : ℕ) (hi : i < 2 * nt)
    (arrow : Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank))
    (hmem : arrow ∈
      paddingArrowsFromFuel p hnt logicalBlank a tape head i hi fuel) :
    ∀ q read,
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        arrow).sourceState ≠ .base (.branch q read) := by
  induction fuel generalizing i with
  | zero => simp [paddingArrowsFromFuel] at hmem
  | succ fuel ih =>
      simp only [paddingArrowsFromFuel, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp [paddingArrow]
      · by_cases hnext : i + 1 < 2 * nt
        · simp [hnext] at htail
          exact ih (i := i + 1) hnext htail
        · simp [hnext] at htail

def paddingArrowsToReader (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) (i : Fin (2 * nt)) :
    List (Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)) :=
  paddingArrowsFromFuel p hnt logicalBlank a tape head i.1 i.2 (2 * nt - i.1)

@[simp] theorem paddingArrowsToReader_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (i : Fin (2 * nt)) :
    (paddingArrowsToReader p hnt logicalBlank a tape head i).length =
      2 * nt - i.1 := by
  apply paddingArrowsFromFuel_length
  omega

theorem paddingArrowsToReader_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (i : Fin (2 * nt)) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (paddingArrowsToReader p hnt logicalBlank a tape head i)
      ({ state := .padding a i, head := head, tape := tape } :
        Config (State ns nt) Tape) =
      some (Config.mk (State.base (.reading a.target
        (ULogSourceOneHotPhysicalStep.initialReaderState hnt)))
        head tape : Config (State ns nt) Tape) := by
  apply paddingArrowsFromFuel_run_to_reader
  exact Nat.add_sub_of_le (Nat.le_of_lt i.isLt)

def handoffPaddingArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) :
    List (Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)) :=
  match a.move with
  | .right => paddingArrowsToReader p hnt logicalBlank a tape head
      ⟨0, by omega⟩
  | .stay => paddingArrowsToReader p hnt logicalBlank a tape head
      ⟨nt, by omega⟩
  | .left => []

@[simp] theorem handoffPaddingArrows_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    (handoffPaddingArrows p hnt logicalBlank a tape head).length =
      ULogSourceOneHotPaddingArithmetic.paddingLength a.move nt := by
  cases hm : a.move <;>
    simp [handoffPaddingArrows, hm,
      ULogSourceOneHotPaddingArithmetic.paddingLength,
      ULogSourceOneHotPhysicalStep.relocationDistance] <;> omega

theorem handoffPaddingArrows_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank) (fun _ => true)
      (handoffPaddingArrows p hnt logicalBlank a tape head)
      (relocationHandoff hnt a tape head) =
      some (Config.mk
        (State.base (.reading a.target
          (ULogSourceOneHotPhysicalStep.initialReaderState hnt)))
        head tape : Config (State ns nt) Tape) := by
  cases hm : a.move with
  | left => simp [handoffPaddingArrows, relocationHandoff, hm]
  | stay =>
      simpa [handoffPaddingArrows, relocationHandoff, hm] using
        paddingArrowsToReader_run p hnt logicalBlank a tape head
          (⟨nt, by omega⟩ : Fin (2 * nt))
  | right =>
      simpa [handoffPaddingArrows, relocationHandoff, hm] using
        paddingArrowsToReader_run p hnt logicalBlank a tape head
          (⟨0, by omega⟩ : Fin (2 * nt))

theorem handoffPaddingArrows_source_nonbranch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (arrow : Arrow (ULogSourceOneHotPaddedStep.program p hnt logicalBlank))
    (hmem : arrow ∈ handoffPaddingArrows p hnt logicalBlank a tape head) :
    ∀ q read,
      (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        arrow).sourceState ≠ .base (.branch q read) := by
  cases hm : a.move with
  | left => simp [handoffPaddingArrows, hm] at hmem
  | stay =>
      exact paddingArrowsFromFuel_source_nonbranch p hnt logicalBlank a tape head
        nt (2 * nt - nt) (by omega) arrow (by
          simpa [handoffPaddingArrows, paddingArrowsToReader, hm] using hmem)
  | right =>
      exact paddingArrowsFromFuel_source_nonbranch p hnt logicalBlank a tape head
        0 (2 * nt) (by omega) arrow (by
          simpa [handoffPaddingArrows, paddingArrowsToReader, hm] using hmem)

/-- Rewind, rewrite, relocate, intercept, and pad one selected source action.
The whole deterministic post-branch suffix has the move-independent length
`4*nt+1`. -/
theorem padded_post_branch_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) :
    ∃ arrows : List (Arrow
        (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)),
      arrows.length = 4 * nt + 1 ∧
      run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) arrows
        (liftBaseConfig
          (ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read slot a tape
            (head + nt))) =
        some (liftBaseConfig
          (ULogSourceOneHotFullMacro.fullEndpoint hnt a tape head)) ∧
      (∀ arrow, arrow ∈ arrows → ∀ q' read',
        (transition (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
          arrow).sourceState ≠ .base (.branch q' read')) := by
  let distance := ULogSourceOneHotPhysicalStep.relocationDistance a.move nt
  let start := ULogSourceOneHotPhaseEndpoints.rewindInitial hnt q read slot a tape
    (head + nt)
  have hAvoidBranch : ∀ k, k < 2 * nt + distance → ∀ q' read',
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        start).state ≠ .branch q' read' := by
    intro k hk q' read'
    exact ULogSourceOneHotRawReconstruct.post_iterate_avoids_branch
      hnt logicalBlank q read slot a tape head k (by omega) q' read'
  obtain ⟨preArrows, hprefixGen⟩ :=
    ULogSourceOneHotPhysicalMacro.nonbranchArrows_exists_of_avoids_branch
      p hnt logicalBlank start (2 * nt + distance) hAvoidBranch
  have hbefore : ∀ k, k < 2 * nt + distance →
      ∀ (a' : BoundedAction ns nt) (i : Fin (2 * nt + 1)),
      ((ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[k]
        start).state = .relocate a' i →
        ¬ ULogSourceOneHotPhysicalStep.relocationDistance a'.move nt ≤ i.1 := by
    simpa [start, distance] using
      post_prefix_before_handoff hnt logicalBlank read q slot a tape head
  have hprefixRun := lift_nonbranchArrows_run_before_handoff p hnt logicalBlank
    start (2 * nt + distance) preArrows hprefixGen hbefore
  let targetTape := ULogSourceOneHotWriter.writePrefix a.write head tape nt
  let terminalHead : Int := head + nt - distance
  have hbaseTerminal :
      (ULogSourceOneHotPhysicalMacro.nextMicroConfig hnt logicalBlank)^[2 * nt + distance]
          start =
        (Config.mk (.relocate a (completedRelocationIndex a)) terminalHead targetTape :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape) := by
    have h := ULogSourceOneHotRawReconstruct.post_iterate_relocate_prefix
      hnt logicalBlank q read slot a tape head distance (by rfl)
    rw [h]
    apply ULogSourceOneHotPhaseEndpoints.config_ext
    · simp [ULogSourceOneHotPhaseEndpoints.relocateExpected,
        ULogSourceOneHotPhaseEndpoints.relocateIndex,
        completedRelocationIndex, distance]
    · simp [ULogSourceOneHotPhaseEndpoints.relocateExpected,
        terminalHead, distance]
    · simp [ULogSourceOneHotPhaseEndpoints.relocateExpected,
        targetTape, distance]
  have hprefixRun' :
      run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) (liftBaseArrows p hnt logicalBlank preArrows)
        (liftBaseConfig start) =
      some (liftBaseConfig
        (Config.mk (.relocate a (completedRelocationIndex a)) terminalHead targetTape :
          Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) := by
    simpa [hbaseTerminal] using hprefixRun
  let finalArrow := liftBaseArrow p hnt logicalBlank
    (ULogSourceOneHotPhysicalMacro.relocateArrow p hnt logicalBlank a
      (completedRelocationIndex a) (targetTape terminalHead))
  let padding := handoffPaddingArrows p hnt logicalBlank a targetTape terminalHead
  let arrows := liftBaseArrows p hnt logicalBlank preArrows ++ finalArrow :: padding
  refine ⟨arrows, ?_, ?_, ?_⟩
  · have hprefixLength := ULogSourceOneHotPhysicalMacro.nonbranchArrows_length
      p hnt logicalBlank start (2 * nt + distance) preArrows hprefixGen
    simp [arrows, finalArrow, padding, hprefixLength,
      handoffPaddingArrows_length, distance]
    have hadd := ULogSourceOneHotPaddingArithmetic.relocation_add_padding
      a.move nt
    unfold ULogSourceOneHotPaddingArithmetic.paddingLength at hadd ⊢
    omega
  · rw [show arrows = liftBaseArrows p hnt logicalBlank preArrows ++
        finalArrow :: padding by rfl,
      padded_run_append, hprefixRun']
    simp only [Option.bind_some, run_cons]
    rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
          (fun _ => true)
          (liftBaseConfig
            (Config.mk (.relocate a (completedRelocationIndex a)) terminalHead targetTape :
              Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) finalArrow =
        some (relocationHandoff hnt a targetTape terminalHead) by
          simpa [finalArrow] using
            lift_completed_relocation_step p hnt logicalBlank a targetTape terminalHead]
    simp only [Option.bind_some]
    have hpadding := handoffPaddingArrows_run p hnt logicalBlank a
      targetTape terminalHead
    simpa [padding, targetTape, terminalHead,
      ULogSourceOneHotFullMacro.fullEndpoint, liftBaseConfig, distance] using hpadding
  · intro arrow hmem q' read' heq
    simp only [arrows, List.mem_append, List.mem_cons] at hmem
    rcases hmem with hpre | hfinal | hpad
    · exact liftedNonbranchArrows_source_nonbranch p hnt logicalBlank start
        (2 * nt + distance) preArrows hprefixGen arrow hpre q' read' heq
    · subst arrow
      simp [finalArrow, FiniteOneTapeProgram.transition,
        ULogSourceOneHotPhysicalMacro.relocateArrow,
        ULogSourceOneHotPhysicalMacro.microArrow] at heq
    · exact handoffPaddingArrows_source_nonbranch p hnt logicalBlank a
        targetTape terminalHead arrow (by simpa [padding] using hpad)
        q' read' heq

theorem padded_oneHot_full_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hocc : p.rule q read (slot = 1) = some a)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∃ arrows : List (Arrow
        (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)),
      arrows.length = 5 * nt + 2 ∧
      run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) arrows
        (liftBaseConfig
          (ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head)) =
        some (liftBaseConfig (ULogSourceOneHotFullMacro.fullEndpoint hnt a tape head)) := by
  obtain ⟨post, hpostLength, hpostRun, _hpostSources⟩ := padded_post_branch_forward
    p hnt logicalBlank read q (slot = 1) a tape head
  let reader := liftBaseArrows p hnt logicalBlank
    (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head)
  let branch := liftBaseArrow p hnt logicalBlank
    (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q read slot
      (tape (head + nt)) hlive a hocc)
  let arrows := reader ++ branch :: post
  refine ⟨arrows, ?_, ?_⟩
  · simp [arrows, reader, branch, hpostLength,
      ULogSourceOneHotMacroEquiv.readerHistory_length]
    omega
  · rw [show arrows = reader ++ branch :: post by rfl, padded_run_append]
    have hreader := padded_oneHot_reader_forward p hnt logicalBlank read q
      hlive tape head hone
    rw [show reader = liftBaseArrows p hnt logicalBlank
        (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head) by rfl,
      hreader]
    simp only [Option.bind_some, run_cons]
    rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
          (fun _ => true)
          (liftBaseConfig
            (Config.mk (.branch q read) (head + nt) tape :
              Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) branch =
        some (liftBaseConfig
          (ULogSourceOneHotPhysicalMacro.branchResult q read slot a tape (head + nt))) by
          simpa [branch] using lift_branchArrow_step p hnt logicalBlank read q
            hlive slot a hocc tape (head + nt)]
    simp only [Option.bind_some]
    simpa [ULogSourceOneHotPhysicalMacro.branchResult,
      ULogSourceOneHotPhaseEndpoints.rewindInitial] using hpostRun

theorem padded_blank_full_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hocc : p.rule q logicalBlank (slot = 1) = some a)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt →
      tape (head + i) = ULogSourceLogicalBlockReader.blank) :
    ∃ arrows : List (Arrow
        (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)),
      arrows.length = 5 * nt + 2 ∧
      run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) arrows
        (liftBaseConfig
          (ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head)) =
        some (liftBaseConfig (ULogSourceOneHotFullMacro.fullEndpoint hnt a tape head)) := by
  obtain ⟨post, hpostLength, hpostRun, _hpostSources⟩ := padded_post_branch_forward
    p hnt logicalBlank logicalBlank q (slot = 1) a tape head
  let reader := liftBaseArrows p hnt logicalBlank
    (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head)
  let branch := liftBaseArrow p hnt logicalBlank
    (ULogSourceOneHotPhysicalMacro.branchArrow p hnt logicalBlank q logicalBlank
      slot (tape (head + nt)) hlive a hocc)
  let arrows := reader ++ branch :: post
  refine ⟨arrows, ?_, ?_⟩
  · simp [arrows, reader, branch, hpostLength,
      ULogSourceOneHotMacroEquiv.readerHistory_length]
    omega
  · rw [show arrows = reader ++ branch :: post by rfl, padded_run_append]
    have hreader := padded_blank_reader_forward p hnt logicalBlank q hlive
      tape head hblank
    rw [show reader = liftBaseArrows p hnt logicalBlank
        (ULogSourceOneHotMacroEquiv.readerHistory p hnt logicalBlank q tape head) by rfl,
      hreader]
    simp only [Option.bind_some, run_cons]
    rw [show step (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
          (fun _ => true)
          (liftBaseConfig
            (Config.mk (.branch q logicalBlank) (head + nt) tape :
              Config (ULogSourceOneHotPhysicalStep.State ns nt) Tape)) branch =
        some (liftBaseConfig
          (ULogSourceOneHotPhysicalMacro.branchResult q logicalBlank slot a tape
            (head + nt))) by
          simpa [branch] using lift_branchArrow_step p hnt logicalBlank logicalBlank
            q hlive slot a hocc tape (head + nt)]
    simp only [Option.bind_some]
    simpa [ULogSourceOneHotPhysicalMacro.branchResult,
      ULogSourceOneHotPhaseEndpoints.rewindInitial] using hpostRun

/-- Unified fixed-time physical source macro for an initialized one-hot block
or an untouched all-physical-blank logical block. -/
theorem padded_represented_full_forward
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank read : Fin nt)
    (q : Fin ns) (hlive : ULogSourceOneHotPhysicalStep.haltedSource q = false)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hocc : p.rule q read (slot = 1) = some a)
    (tape : Int → Tape) (head : Int)
    (hrep : _root_.PakFixedPolyomino.ULogSourceOneHotRepresentation.RepresentsAt
      logicalBlank read tape head) :
    ∃ arrows : List (Arrow
        (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)),
      arrows.length = 5 * nt + 2 ∧
      run (ULogSourceOneHotPaddedStep.program p hnt logicalBlank)
        (fun _ => true) arrows
        (liftBaseConfig
          (ULogSourceOneHotMacroEquiv.initialPhysical hnt logicalBlank q tape head)) =
        some (liftBaseConfig (ULogSourceOneHotFullMacro.fullEndpoint hnt a tape head)) := by
  rcases hrep with hone | ⟨hread, hblank⟩
  · exact padded_oneHot_full_forward p hnt logicalBlank read q hlive slot a
      hocc tape head hone
  · subst read
    exact padded_blank_full_forward p hnt logicalBlank q hlive slot a hocc
      tape head hblank

end PakFixedPolyomino.ULogSourceOneHotPaddedMacro
