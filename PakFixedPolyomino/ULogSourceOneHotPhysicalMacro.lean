import PakFixedPolyomino.ULogSourceOneHotPhysicalStep
import Mathlib.Tactic

/-!
# Chronological physical source-step histories

This layer names the literal occupied arrows used by a source-step macro:
read, one labelled source choice, rewind, write, relocate, and handoff.
The forward run proof is added against these exact lists after the active
dependency rebuild completes.
-/

namespace PakFixedPolyomino.ULogSourceOneHotPhysicalMacro

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler ULogSourceOneHotPhysicalStep

variable {ns nt : ℕ}

/-- A literal occupied slot-zero micro arrow. -/
def microArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (s : State ns nt) (x : Tape) (hs : ∀ q read, s ≠ State.branch q read) :
    Arrow (program p hnt logicalBlank) :=
  ⟨((s, x), 0), by
    cases s with
    | branch q read => exact False.elim (hs q read rfl)
    | reading q r =>
        simp [program, ULogSourceOneHotPhysicalStep.step]
    | rewind q read slot a i =>
        simp [program, ULogSourceOneHotPhysicalStep.step]
    | writing a i =>
        simp [program, ULogSourceOneHotPhysicalStep.step]
    | relocate a i =>
        simp [program, ULogSourceOneHotPhysicalStep.step]
    | accept => simp [program, ULogSourceOneHotPhysicalStep.step]
    | reject => simp [program, ULogSourceOneHotPhysicalStep.step]⟩

/-- The literal labelled branch arrow corresponding to an occupied source
slot.  Its label is kept as a `Fin 2`, preserving Boolean multiplicity. -/
def branchArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Fin 2) (x : Tape)
    (hlive : haltedSource q = false)
    (a : BoundedAction ns nt) (hocc : p.rule q read (slot = 1) = some a) :
    Arrow (program p hnt logicalBlank) :=
  ⟨((State.branch q read, x), slot), by
    change branchAction p q read slot x ≠ none
    simp [branchAction, hlive, hocc]⟩

/-- One chronological reader micro-arrow at a lifted reader state. -/
def readArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (r : ULogSourceLogicalBlockReader.State nt) (x : Tape) :
    Arrow (program p hnt logicalBlank) :=
  microArrow p hnt logicalBlank (.reading q r) x (by
    intro q' read h
    cases h)

/-- One chronological rewind micro-arrow. -/
def rewindArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (i : Fin nt) (x : Tape) : Arrow (program p hnt logicalBlank) :=
  microArrow p hnt logicalBlank (.rewind q read slot a i) x (by intro q' read h; cases h)

/-- One chronological writer micro-arrow. -/
def writeArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin nt) (x : Tape) :
    Arrow (program p hnt logicalBlank) :=
  microArrow p hnt logicalBlank (.writing a i) x (by intro q read h; cases h)

/-- One chronological relocation micro-arrow. -/
def relocateArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)) (x : Tape) :
    Arrow (program p hnt logicalBlank) :=
  microArrow p hnt logicalBlank (.relocate a i) x (by intro q read h; cases h)

/-- The phase ledger for a source action.  The eventual concrete list is
obtained by instantiating each finite index with the current configuration's
read letter; no quotienting of labels occurs. -/
structure ChronologicalPlan (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) where
  slot : Fin 2
  action : BoundedAction ns nt
  live : haltedSource q = false
  occupied : p.rule q read (slot = 1) = some action

def ChronologicalPlan.result {p : BoundedProgram ns nt} {hnt : 0 < nt}
    {logicalBlank : Fin nt} {q : Fin ns} {read : Fin nt}
    (m : ChronologicalPlan p hnt logicalBlank q read) : BoundedAction ns nt :=
  m.action

/-- Execute the unique slot-zero micro action at a nonbranch state.  This is
the configuration counterpart of `microArrow`; it is intentionally separate
from source choice, where the Boolean-labelled original rule is selected. -/
def nextMicroConfig (hnt : 0 < nt) (logicalBlank : Fin nt)
    (c : Config (State ns nt) Tape) : Config (State ns nt) Tape :=
  let x := c.tape c.head
  let act := microAction hnt logicalBlank c.state x
  { state := act.target
    head := moveHead act.move c.head
    tape := writtenTape c act.write }

/-- Embed a logical-reader control state in the physical source-step control.
Reader completion is precisely the handoff to source branching; malformed
physical blocks enter the physical reject state immediately. -/
def liftReaderControl (q : Fin ns) :
    ULogSourceLogicalBlockReader.State nt → State ns nt
  | .done a => .branch q a
  | .reject => .reject
  | r => .reading q r

/-- Lift a complete logical-reader configuration into its physical reader
phase, retaining the tape and head verbatim. -/
def liftReaderConfig (q : Fin ns)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) :
    Config (State ns nt) Tape :=
  { state := liftReaderControl q c.state
    head := c.head
    tape := c.tape }

/-- For a live source state, one physical reader microstep is exactly the
lift of one logical reader microstep. -/
theorem nextMicroConfig_liftReaderConfig (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : haltedSource q = false)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) :
    nextMicroConfig hnt logicalBlank (liftReaderConfig q c) =
      liftReaderConfig q (ULogSourceLogicalBlockReader.nextConfig logicalBlank c) := by
  rcases c with ⟨r, head, tape⟩
  cases r with
  | scan i mode =>
      simp only [liftReaderConfig, liftReaderControl, nextMicroConfig,
        microAction, hlive, Bool.false_eq_true, if_false, readerAction,
        liftReaderAction, ULogSourceLogicalBlockReader.nextConfig]
      rfl
  | done a =>
      simp [nextMicroConfig, liftReaderConfig, liftReaderControl, microAction,
        ULogSourceLogicalBlockReader.nextConfig,
        ULogSourceLogicalBlockReader.readerAction, writtenTape, moveHead]
  | reject =>
      simp [nextMicroConfig, liftReaderConfig, liftReaderControl, microAction,
        ULogSourceLogicalBlockReader.nextConfig,
        ULogSourceLogicalBlockReader.readerAction, writtenTape, moveHead]

/-- A configuration-indexed deterministic prefix of literal micro arrows.
`none` marks arrival at the sole source-choice point, so this generator can
never accidentally hide a source slot inside a micro phase. -/
def nonbranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) : Config (State ns nt) Tape → ℕ →
      Option (List (Arrow (program p hnt logicalBlank)))
  | _, 0 => some []
  | c, n + 1 =>
      match c.state with
      | .branch _ _ => none
      | .reading q r =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (readArrow p hnt logicalBlank q r (c.tape c.head) :: ·)
      | .rewind q read slot a i =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (rewindArrow p hnt logicalBlank q read slot a i (c.tape c.head) :: ·)
      | .writing a i =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (writeArrow p hnt logicalBlank a i (c.tape c.head) :: ·)
      | .relocate a i =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (relocateArrow p hnt logicalBlank a i (c.tape c.head) :: ·)
      | .accept =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (microArrow p hnt logicalBlank .accept (c.tape c.head) (by intro q read h; cases h) :: ·)
      | .reject =>
          (nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank c) n).map
            (microArrow p hnt logicalBlank .reject (c.tape c.head) (by intro q read h; cases h) :: ·)

/-- The exact chronological reader arrows corresponding to a logical reader
prefix.  Every member is a literal slot-zero physical reader arrow. -/
def readerArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) :
    Config (ULogSourceLogicalBlockReader.State nt) Tape → ℕ →
      List (Arrow (program p hnt logicalBlank))
  | _, 0 => []
  | c, n + 1 =>
      readArrow p hnt logicalBlank q c.state (c.tape c.head) ::
        readerArrows p hnt logicalBlank q
          (ULogSourceLogicalBlockReader.nextConfig logicalBlank c) n

/-- The physical reader prefix is the actual chronological list of literal
reader arrows, not merely an existence witness for a path. -/
def readerPrefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (tape : Int → Tape) (head : Int) :
    Option (List (Arrow (program p hnt logicalBlank))) :=
  some (readerArrows p hnt logicalBlank q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt)

theorem microArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (c : Config (State ns nt) Tape)
    (hs : ∀ q read, c.state ≠ State.branch q read) :
    step (program p hnt logicalBlank) (fun _ => true) c
      (microArrow p hnt logicalBlank c.state (c.tape c.head) hs) =
      some (nextMicroConfig hnt logicalBlank c) := by
  rcases c with ⟨s, head, tape⟩
  cases s with
  | branch q read => exact False.elim (hs q read rfl)
  | reading q r =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]
  | rewind q read slot a i =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]
  | writing a i =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]
  | relocate a i =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]
  | accept =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]
  | reject =>
      simp [FiniteOneTapeSemantics.step, microArrow, program,
        ULogSourceOneHotPhysicalStep.step, actionOf, transition,
        nextMicroConfig, writtenTape, moveHead]

def branchResult (q : Fin ns) (read : Fin nt) (slot : Fin 2)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    Config (State ns nt) Tape :=
  { state := .rewind q read (slot = 1) a ⟨0, by exact Fin.pos read⟩
    head := head
    tape := tape }

private theorem actionOf_eq_of_rule_eq
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

@[simp] theorem actionOf_branchArrow (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt)
    (slot : Fin 2) (x : Tape) (hlive : haltedSource q = false)
    (a : BoundedAction ns nt) (hocc : p.rule q read (slot = 1) = some a) :
    actionOf (program p hnt logicalBlank)
      (branchArrow p hnt logicalBlank q read slot x hlive a hocc) =
      ⟨x, .rewind q read (slot = 1) a ⟨0, Fin.pos read⟩, .stay⟩ := by
  apply actionOf_eq_of_rule_eq
  change (program p hnt logicalBlank).rule (.branch q read) x slot = _
  rw [branch_rule_exact p hnt logicalBlank q read slot x hlive, hocc]
  rfl

/-- The sole nondeterministic macro arrow preserves its original source slot
and enters the deterministic rewind phase without moving or changing tape. -/
theorem branchArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Fin 2)
    (a : BoundedAction ns nt) (hlive : haltedSource q = false)
    (hocc : p.rule q read (slot = 1) = some a)
    (tape : Int → Tape) (head : Int) :
    step (program p hnt logicalBlank) (fun _ => true)
      ({ state := .branch q read, head := head, tape := tape } :
        Config (State ns nt) Tape)
      (branchArrow p hnt logicalBlank q read slot (tape head) hlive a hocc) =
      some (branchResult q read slot a tape head) := by
  have haction := actionOf_branchArrow p hnt logicalBlank q read slot
    (tape head) hlive a hocc
  unfold FiniteOneTapeSemantics.step
  dsimp only
  simp only [transition]
  rw [haction]
  simp [branchArrow, transition, branchResult, writtenTape, moveHead]

theorem nonbranchArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (c : Config (State ns nt) Tape) (n : ℕ)
    (as : List (Arrow (program p hnt logicalBlank)) )
    (h : nonbranchArrows p hnt logicalBlank c n = some as) : as.length = n := by
  induction n generalizing c as with
  | zero => simpa [nonbranchArrows] using h
  | succ n ih =>
      rcases c with ⟨s, head, tape⟩
      cases s with
      | branch q read => simp [nonbranchArrows] at h
      | reading q r =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.reading q r, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              simp [ih _ _ htail]
      | rewind q read slot a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.rewind q read slot a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail => simp [nonbranchArrows, htail] at h; subst as; simp [ih _ _ htail]

      | writing a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.writing a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail => simp [nonbranchArrows, htail] at h; subst as; simp [ih _ _ htail]
      | relocate a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.relocate a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail => simp [nonbranchArrows, htail] at h; subst as; simp [ih _ _ htail]
      | accept =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.accept, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail => simp [nonbranchArrows, htail] at h; subst as; simp [ih _ _ htail]
      | reject =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.reject, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail => simp [nonbranchArrows, htail] at h; subst as; simp [ih _ _ htail]

theorem nonbranchArrows_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (c : Config (State ns nt) Tape) (n : ℕ)
    (as : List (Arrow (program p hnt logicalBlank)))
    (h : nonbranchArrows p hnt logicalBlank c n = some as) :
    run (program p hnt logicalBlank) (fun _ => true) as c =
      some ((nextMicroConfig hnt logicalBlank)^[n] c) := by
  induction n generalizing c as with
  | zero =>
      have has : as = [] := by simpa [nonbranchArrows] using Option.some.inj h
      subst as
      rfl
  | succ n ih =>
      rcases c with ⟨s, head, tape⟩
      cases s with
      | branch q read => simp [nonbranchArrows] at h
      | reading q r =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.reading q r, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.reading q r, head, tape⟩ : Config (State ns nt) Tape)
                (by intro q' read hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.reading q r, head, tape⟩
                  (readArrow p hnt logicalBlank q r (tape head)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.reading q r, head, tape⟩) by
                    simpa [readArrow] using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]
      | rewind q read slot a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank
              ⟨.rewind q read slot a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.rewind q read slot a i, head, tape⟩ :
                  Config (State ns nt) Tape)
                (by intro q' read' hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.rewind q read slot a i, head, tape⟩
                  (rewindArrow p hnt logicalBlank q read slot a i (tape head)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.rewind q read slot a i, head, tape⟩) by
                    simpa [rewindArrow] using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]
      | writing a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.writing a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.writing a i, head, tape⟩ : Config (State ns nt) Tape)
                (by intro q' read' hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.writing a i, head, tape⟩
                  (writeArrow p hnt logicalBlank a i (tape head)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.writing a i, head, tape⟩) by
                    simpa [writeArrow] using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]
      | relocate a i =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.relocate a i, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.relocate a i, head, tape⟩ : Config (State ns nt) Tape)
                (by intro q' read' hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.relocate a i, head, tape⟩
                  (relocateArrow p hnt logicalBlank a i (tape head)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.relocate a i, head, tape⟩) by
                    simpa [relocateArrow] using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]
      | accept =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.accept, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.accept, head, tape⟩ : Config (State ns nt) Tape)
                (by intro q' read' hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.accept, head, tape⟩
                  (microArrow p hnt logicalBlank .accept (tape head)
                    (by intro q read hbad; cases hbad)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.accept, head, tape⟩) by simpa using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]
      | reject =>
          cases htail : nonbranchArrows p hnt logicalBlank
            (nextMicroConfig hnt logicalBlank ⟨.reject, head, tape⟩) n with
          | none => simp [nonbranchArrows, htail] at h
          | some tail =>
              simp [nonbranchArrows, htail] at h
              subst as
              rw [run_cons]
              have hstep := microArrow_step p hnt logicalBlank
                (⟨.reject, head, tape⟩ : Config (State ns nt) Tape)
                (by intro q' read' hbad; cases hbad)
              rw [show step (program p hnt logicalBlank) (fun _ => true)
                  ⟨.reject, head, tape⟩
                  (microArrow p hnt logicalBlank .reject (tape head)
                    (by intro q read hbad; cases hbad)) =
                    some (nextMicroConfig hnt logicalBlank
                      ⟨.reject, head, tape⟩) by simpa using hstep]
              simp only [Option.bind_some]
              rw [ih _ _ htail, Function.iterate_succ_apply]

/-- If the deterministic micro-execution does not encounter source branching
in its first `n` ticks, `nonbranchArrows` returns its exact occupied arrow
ledger.  Together with `nonbranchArrows_run` and
`nonbranchArrows_length`, this turns the operational avoidance condition into
both an actual list and its exact run/length facts. -/
theorem nonbranchArrows_exists_of_avoids_branch
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (c : Config (State ns nt) Tape) (n : ℕ)
    (havoid : ∀ k : ℕ, k < n → ∀ q read,
      ((nextMicroConfig hnt logicalBlank)^[k] c).state ≠ State.branch q read) :
    ∃ as, nonbranchArrows p hnt logicalBlank c n = some as := by
  induction n generalizing c with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      have hzero := havoid 0 (by omega)
      simp only [Function.iterate_zero] at hzero
      have htailAvoid : ∀ k : ℕ, k < n → ∀ q read,
          ((nextMicroConfig hnt logicalBlank)^[k]
            (nextMicroConfig hnt logicalBlank c)).state ≠ State.branch q read := by
        intro k hk q read
        have h := havoid (k + 1) (by omega) q read
        simpa only [Function.iterate_succ_apply] using h
      rcases ih (nextMicroConfig hnt logicalBlank c) htailAvoid with ⟨tail, htail⟩
      rcases c with ⟨s, head, tape⟩
      cases s with
      | branch q read => exact False.elim (hzero q read rfl)
      | reading q r =>
          exact ⟨readArrow p hnt logicalBlank q r (tape head) :: tail, by
            simp [nonbranchArrows, htail]⟩
      | rewind q read slot a i =>
          exact ⟨rewindArrow p hnt logicalBlank q read slot a i (tape head) :: tail, by
            simp [nonbranchArrows, htail]⟩
      | writing a i =>
          exact ⟨writeArrow p hnt logicalBlank a i (tape head) :: tail, by
            simp [nonbranchArrows, htail]⟩
      | relocate a i =>
          exact ⟨relocateArrow p hnt logicalBlank a i (tape head) :: tail, by
            simp [nonbranchArrows, htail]⟩
      | accept =>
          exact ⟨microArrow p hnt logicalBlank .accept (tape head)
            (by intro q read h; cases h) :: tail, by
            simp [nonbranchArrows, htail]⟩
      | reject =>
          exact ⟨microArrow p hnt logicalBlank .reject (tape head)
            (by intro q read h; cases h) :: tail, by
            simp [nonbranchArrows, htail]⟩

@[simp] theorem readerArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) (n : ℕ) :
    (readerArrows p hnt logicalBlank q c n).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [readerArrows, ih]

/-- Execute the exact reader-arrow ledger while the logical reader remains
in a scan control at every consumed prefix. -/
theorem readerArrows_run_of_scanning (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) (n : ℕ)
    (hscan : ∀ k : ℕ, k < n → ∃ i mode,
      ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k] c).state =
        .scan i mode) :
    run (program p hnt logicalBlank) (fun _ => true)
      (readerArrows p hnt logicalBlank q c n) (liftReaderConfig q c) =
      some (liftReaderConfig q
        ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      have hzero := hscan 0 (by omega)
      simp only [Function.iterate_zero] at hzero
      rcases c with ⟨r, head, tape⟩
      rcases hzero with ⟨i, mode, hr⟩
      change r = .scan i mode at hr
      subst r
      rw [readerArrows, run_cons]
      have hstep := microArrow_step p hnt logicalBlank
        (liftReaderConfig q
          ({ state := .scan i mode, head := head, tape := tape } :
            Config (ULogSourceLogicalBlockReader.State nt) Tape))
        (by
          intro q' read hbad
          change State.reading q (.scan i mode) = State.branch q' read at hbad
          cases hbad)
      rw [show step (program p hnt logicalBlank) (fun _ => true)
          (liftReaderConfig q
            ({ state := .scan i mode, head := head, tape := tape } :
              Config (ULogSourceLogicalBlockReader.State nt) Tape))
          (readArrow p hnt logicalBlank q (.scan i mode) (tape head)) =
            some (nextMicroConfig hnt logicalBlank
              (liftReaderConfig q
                ({ state := .scan i mode, head := head, tape := tape } :
                  Config (ULogSourceLogicalBlockReader.State nt) Tape))) by
            simpa [readArrow, liftReaderConfig, liftReaderControl] using hstep]
      simp only [Option.bind_some]
      rw [nextMicroConfig_liftReaderConfig hnt logicalBlank q hlive]
      have hscan' : ∀ k : ℕ, k < n → ∃ i' mode',
          ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k]
            (ULogSourceLogicalBlockReader.nextConfig logicalBlank
              ({ state := .scan i mode, head := head, tape := tape } :
                Config (ULogSourceLogicalBlockReader.State nt) Tape))).state =
            .scan i' mode' := by
        intro k hk
        have hk' := hscan (k + 1) (by omega)
        simpa only [Function.iterate_succ_apply] using hk'
      rw [ih _ hscan']
      simp only [Function.iterate_succ_apply]

/-- Before completion, a one-hot logical reader remains in a scan state at
each consumed prefix. -/
theorem oneHot_initial_scanning (logicalBlank a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt a tape head) :
    ∀ k : ℕ, k < nt → ∃ i mode,
      ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k]
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)).state =
        .scan i mode := by
  intro k hk
  rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
    logicalBlank a hnt tape head hone k (by omega)]
  by_cases hzero : k = 0
  · subst k
    exact ⟨⟨0, hnt⟩, .fresh, by simp [ULogSourceLogicalBlockReader.oneHotExpected,
      ULogSourceLogicalBlockReader.oneHotStage_zero]⟩
  by_cases hbefore : k ≤ a.1
  · exact ⟨⟨k, hk⟩, .bits none, by
      simp [ULogSourceLogicalBlockReader.oneHotExpected,
        ULogSourceLogicalBlockReader.oneHotStage_before a hnt k
          (Nat.pos_of_ne_zero hzero) hbefore]⟩
  · have ha : a.1 < k := by omega
    exact ⟨⟨k, hk⟩, .bits (some a), by
      simp [ULogSourceLogicalBlockReader.oneHotExpected,
        ULogSourceLogicalBlockReader.oneHotStage_after a hnt k ha hk]⟩

/-- Before completion, an all-blank logical reader remains in a scan state
at each consumed prefix. -/
theorem blank_initial_scanning (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    ∀ k : ℕ, k < nt → ∃ i mode,
      ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k]
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)).state =
        .scan i mode := by
  intro k hk
  rw [ULogSourceLogicalBlockReader.iterate_blank_expected
    logicalBlank hnt tape head hblank k (by omega)]
  by_cases hzero : k = 0
  · subst k
    exact ⟨⟨0, hnt⟩, .fresh, by simp [ULogSourceLogicalBlockReader.blankExpected,
      ULogSourceLogicalBlockReader.blankStage_zero]⟩
  · exact ⟨⟨k, hk⟩, .blanks, by
      simp [ULogSourceLogicalBlockReader.blankExpected,
        ULogSourceLogicalBlockReader.blankStage_pos logicalBlank hnt k
          (Nat.pos_of_ne_zero hzero) hk]⟩

/-- The supplied reader-prefix ledger for a one-hot block reaches the exact
physical branch state.  The prefix equality pins the chronological arrows
rather than replacing them with an arbitrary witness. -/
theorem readerPrefix_oneHot_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank a : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt a tape head)
    (as : List (Arrow (program p hnt logicalBlank)))
    (hprefix : readerPrefix p hnt logicalBlank q tape head = some as) :
    run (program p hnt logicalBlank) (fun _ => true) as
      { state := .reading q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state
        head := head
        tape := tape } =
      some { state := .branch q a, head := head + nt, tape := tape } := by
  have has : as = readerArrows p hnt logicalBlank q
      (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt := by
    simpa [readerPrefix] using (Option.some.inj hprefix).symm
  subst as
  have hrun := readerArrows_run_of_scanning p hnt logicalBlank q hlive
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt
    (oneHot_initial_scanning logicalBlank a hnt tape head hone)
  rw [ULogSourceLogicalBlockReader.oneHot_operational_terminal
    logicalBlank a hnt tape head hone] at hrun
  simpa [liftReaderConfig, liftReaderControl,
    ULogSourceLogicalBlockReader.initialConfig] using hrun

/-- The actual one-hot reader prefix exists, has exactly the fixed block
width, and executes to its branch handoff. -/
theorem readerPrefix_oneHot (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank a : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt a tape head) :
    ∃ as, readerPrefix p hnt logicalBlank q tape head = some as ∧
      as.length = nt ∧
      run (program p hnt logicalBlank) (fun _ => true) as
        { state := .reading q
            (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state
          head := head
          tape := tape } =
        some { state := .branch q a, head := head + nt, tape := tape } := by
  let as := readerArrows p hnt logicalBlank q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt
  refine ⟨as, ?_, readerArrows_length p hnt logicalBlank q _ nt, ?_⟩
  · rfl
  · exact readerPrefix_oneHot_run p hnt logicalBlank a q hlive tape head hone as rfl

/-- The supplied reader-prefix ledger for an all-blank physical block reaches
the branch corresponding to its designated logical blank. -/
theorem readerPrefix_blank_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (as : List (Arrow (program p hnt logicalBlank)))
    (hprefix : readerPrefix p hnt logicalBlank q tape head = some as) :
    run (program p hnt logicalBlank) (fun _ => true) as
      { state := .reading q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state
        head := head
        tape := tape } =
      some { state := .branch q logicalBlank, head := head + nt, tape := tape } := by
  have has : as = readerArrows p hnt logicalBlank q
      (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt := by
    simpa [readerPrefix] using (Option.some.inj hprefix).symm
  subst as
  have hrun := readerArrows_run_of_scanning p hnt logicalBlank q hlive
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt
    (blank_initial_scanning logicalBlank hnt tape head hblank)
  rw [ULogSourceLogicalBlockReader.blank_operational_terminal
    logicalBlank hnt tape head hblank] at hrun
  simpa [liftReaderConfig, liftReaderControl,
    ULogSourceLogicalBlockReader.initialConfig] using hrun

/-- The all-blank reader prefix is likewise an exact `nt`-arrow history with
the designated physical branch handoff as its terminal configuration. -/
theorem readerPrefix_blank (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    ∃ as, readerPrefix p hnt logicalBlank q tape head = some as ∧
      as.length = nt ∧
      run (program p hnt logicalBlank) (fun _ => true) as
        { state := .reading q
            (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head).state
          head := head
          tape := tape } =
        some { state := .branch q logicalBlank, head := head + nt, tape := tape } := by
  let as := readerArrows p hnt logicalBlank q
    (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) nt
  refine ⟨as, ?_, readerArrows_length p hnt logicalBlank q _ nt, ?_⟩
  · rfl
  · exact readerPrefix_blank_run p hnt logicalBlank q hlive tape head hblank as rfl

end PakFixedPolyomino.ULogSourceOneHotPhysicalMacro
