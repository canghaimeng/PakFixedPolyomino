import PakFixedPolyomino.ULogSourceObliviousScanProgram
import Mathlib.Tactic

/-! # Literal execution of one fixed-width cell read -/

namespace PakFixedPolyomino.ULogSourceObliviousScanExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler ULogSourceOneHotReader ULogSourceLogicalBlockReader
open ULogSourceObliviousScanProgram

variable {ns nt : ℕ}

abbrev ReaderConfig :=
  FiniteOneTapeSemantics.Config (ULogSourceLogicalBlockReader.State nt) (Fin 3)

abbrev ScanConfig :=
  FiniteOneTapeSemantics.Config (State ns nt) (Fin 3)

/-- Canonical occupied slot-zero arrow for any deterministic scanner phase. -/
def deterministicArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (s : State ns nt) (x : Fin 3)
    (act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3))
    (hact : deterministicAction p hnt blank s x = some act) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  ⟨((s, x), (0 : Fin 2)), by
    cases s <;>
      simp [ULogSourceObliviousScanProgram.program,
        ULogSourceObliviousScanProgram.step, deterministicAction] at hact ⊢ <;>
      try simp_all⟩

@[simp] theorem actionOf_deterministicArrow
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (s : State ns nt) (x : Fin 3)
    (act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3))
    (hact : deterministicAction p hnt blank s x = some act) :
    FiniteOneTapeProgram.actionOf
      (ULogSourceObliviousScanProgram.program p hnt blank)
      (deterministicArrow p hnt blank s x act hact) = act := by
  apply ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq
  cases s <;>
    simp [deterministicArrow, ULogSourceObliviousScanProgram.program,
      ULogSourceObliviousScanProgram.step, deterministicAction] at hact ⊢ <;>
    try simp_all

theorem deterministicArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanConfig (ns := ns) (nt := nt))
    (s : State ns nt) (x : Fin 3)
    (act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3))
    (hstate : c.state = s) (hread : c.tape c.head = x)
    (hact : deterministicAction p hnt blank s x = some act) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (deterministicArrow p hnt blank s x act hact) = some {
        state := act.target
        head := FiniteOneTapeSemantics.moveHead act.move c.head
        tape := FiniteOneTapeSemantics.writtenTape c act.write } := by
  rcases c with ⟨state, head, tape⟩
  dsimp only at hstate hread ⊢
  subst state
  have htr : FiniteOneTapeProgram.transition
      (ULogSourceObliviousScanProgram.program p hnt blank)
      (deterministicArrow p hnt blank s x act hact) =
      { sourceState := s, read := x, write := act.write,
        targetState := act.target, move := act.move } := by
    unfold FiniteOneTapeProgram.transition
    rw [actionOf_deterministicArrow]
    simp [deterministicArrow]
  unfold FiniteOneTapeSemantics.step
  rw [htr]
  simp [hread]

def flagHeadArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  ⟨((State.flag q none, ULogSourceOneHotReader.one), (0 : Fin 2)), by
    simp [ULogSourceObliviousScanProgram.program,
      ULogSourceObliviousScanProgram.step, deterministicAction,
      ULogSourceOneHotReader.one, ULogSourceOneHotReader.zero,
      ULogSourceOneHotReader.blank]⟩

def flagZeroArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt)) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  deterministicArrow p hnt blank (.flag q selected)
    ULogSourceOneHotReader.zero
    ⟨ULogSourceOneHotReader.zero,
      .read q selected false (.scan ⟨0, hnt⟩ .fresh), .right⟩
    (by simp [deterministicAction, ULogSourceOneHotReader.zero,
      ULogSourceOneHotReader.one, ULogSourceOneHotReader.blank])

theorem flagZeroArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (c : ScanConfig (ns := ns) (nt := nt))
    (hstate : c.state = .flag q selected)
    (hread : c.tape c.head = ULogSourceOneHotReader.zero) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (flagZeroArrow p hnt blank q selected) = some {
        state := .read q selected false (.scan ⟨0, hnt⟩ .fresh)
        head := c.head + 1
        tape := c.tape } := by
  let act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3) :=
    ⟨ULogSourceOneHotReader.zero,
      .read q selected false (.scan ⟨0, hnt⟩ .fresh), .right⟩
  have hact : deterministicAction p hnt blank (.flag q selected)
      ULogSourceOneHotReader.zero = some act := by
    simp [act, deterministicAction, ULogSourceOneHotReader.zero,
      ULogSourceOneHotReader.one, ULogSourceOneHotReader.blank]
  have harrow : flagZeroArrow p hnt blank q selected =
      deterministicArrow p hnt blank (.flag q selected)
        ULogSourceOneHotReader.zero act hact := by
    apply Subtype.ext
    rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c
      ULogSourceOneHotReader.zero = c.tape := by
    funext z
    by_cases hz : z = c.head
    · subst z
      simp [FiniteOneTapeSemantics.writtenTape, hread]
    · simp [FiniteOneTapeSemantics.writtenTape, Function.update_of_ne hz]
  have hs := deterministicArrow_step p hnt blank c (.flag q selected)
    ULogSourceOneHotReader.zero act hstate hread hact
  rw [show act.write = ULogSourceOneHotReader.zero by rfl, htape] at hs
  simpa [act, FiniteOneTapeSemantics.moveHead] using hs

theorem flagHeadArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (c : ScanConfig (ns := ns) (nt := nt))
    (hstate : c.state = .flag q none)
    (hread : c.tape c.head = ULogSourceOneHotReader.one) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (flagHeadArrow p hnt blank q) = some {
        state := .read q none true (.scan ⟨0, hnt⟩ .fresh)
        head := c.head + 1
        tape := c.tape } := by
  rcases c with ⟨state, head, tape⟩
  dsimp only at hstate hread ⊢
  subst state
  unfold FiniteOneTapeSemantics.step
  simp [flagHeadArrow, FiniteOneTapeProgram.transition,
    FiniteOneTapeProgram.actionOf,
    ULogSourceObliviousScanProgram.program,
    ULogSourceObliviousScanProgram.step, deterministicAction,
    ULogSourceOneHotReader.one, ULogSourceOneHotReader.zero,
    ULogSourceOneHotReader.blank, hread, writtenTape, moveHead]

theorem branchArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (c : ScanConfig)
    (choice : ULogSourceOneHotMacroEquiv.SourceChoice p q read)
    (hstate : c.state = .branch q read) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (ULogSourceObliviousScanProgram.branchArrow p hnt blank q read
        (c.tape c.head) choice.slot choice.action choice.occupied) = some {
          state := .flag q (some choice.action)
          head := c.head
          tape := c.tape } := by
  rcases c with ⟨state, head, tape⟩
  dsimp only at hstate ⊢
  subst state
  have htr : FiniteOneTapeProgram.transition
      (ULogSourceObliviousScanProgram.program p hnt blank)
      (ULogSourceObliviousScanProgram.branchArrow p hnt blank q read
        (tape head) choice.slot choice.action choice.occupied) =
      { sourceState := .branch q read
        read := tape head
        write := tape head
        targetState := .flag q (some choice.action)
        move := .stay } := by
    unfold FiniteOneTapeProgram.transition
    rw [ULogSourceObliviousScanProgram.actionOf_branchArrow]
    simp [ULogSourceObliviousScanProgram.branchArrow]
  unfold FiniteOneTapeSemantics.step
  rw [htr]
  simp [writtenTape, moveHead]

def postScanBoundaryArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  deterministicArrow p hnt blank (.flag q (some a))
    ULogSourceOneHotReader.blank
    ⟨ULogSourceOneHotReader.blank, .returnLeft a, .left⟩
    (by simp [deterministicAction])

theorem postScanBoundaryArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (c : ScanConfig (ns := ns) (nt := nt))
    (hstate : c.state = .flag q (some a))
    (hread : c.tape c.head = ULogSourceOneHotReader.blank) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (postScanBoundaryArrow p hnt blank q a) = some {
        state := .returnLeft a
        head := c.head - 1
        tape := c.tape } := by
  let act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3) :=
    ⟨ULogSourceOneHotReader.blank, .returnLeft a, .left⟩
  have hact : deterministicAction p hnt blank (.flag q (some a))
      ULogSourceOneHotReader.blank = some act := by
    simp [act, deterministicAction]
  have harrow : postScanBoundaryArrow p hnt blank q a =
      deterministicArrow p hnt blank (.flag q (some a))
        ULogSourceOneHotReader.blank act hact := by
    apply Subtype.ext
    rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c
      ULogSourceOneHotReader.blank = c.tape := by
    funext z
    by_cases hz : z = c.head
    · subst z
      simp [FiniteOneTapeSemantics.writtenTape, hread]
    · simp [FiniteOneTapeSemantics.writtenTape, Function.update_of_ne hz]
  have hs := deterministicArrow_step p hnt blank c (.flag q (some a))
    ULogSourceOneHotReader.blank act hstate hread hact
  rw [show act.write = ULogSourceOneHotReader.blank by rfl, htape] at hs
  simpa [act, FiniteOneTapeSemantics.moveHead] using hs

def returnLeftBoundaryArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  deterministicArrow p hnt blank (.returnLeft a)
    ULogSourceOneHotReader.blank
    ⟨ULogSourceOneHotReader.blank, .updateLRFlag a false, .right⟩
    (by simp [deterministicAction])

theorem returnLeftBoundaryArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt)
    (c : ScanConfig (ns := ns) (nt := nt))
    (hstate : c.state = .returnLeft a)
    (hread : c.tape c.head = ULogSourceOneHotReader.blank) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (returnLeftBoundaryArrow p hnt blank a) = some {
        state := .updateLRFlag a false
        head := c.head + 1
        tape := c.tape } := by
  let act : FiniteOneTapeProgram.Action (State ns nt) (Fin 3) :=
    ⟨ULogSourceOneHotReader.blank, .updateLRFlag a false, .right⟩
  have hact : deterministicAction p hnt blank (.returnLeft a)
      ULogSourceOneHotReader.blank = some act := by
    simp [act, deterministicAction]
  have harrow : returnLeftBoundaryArrow p hnt blank a =
      deterministicArrow p hnt blank (.returnLeft a)
        ULogSourceOneHotReader.blank act hact := by
    apply Subtype.ext
    rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c
      ULogSourceOneHotReader.blank = c.tape := by
    funext z
    by_cases hz : z = c.head
    · subst z
      simp [FiniteOneTapeSemantics.writtenTape, hread]
    · simp [FiniteOneTapeSemantics.writtenTape, Function.update_of_ne hz]
  have hs := deterministicArrow_step p hnt blank c (.returnLeft a)
    ULogSourceOneHotReader.blank act hstate hread hact
  rw [show act.write = ULogSourceOneHotReader.blank by rfl, htape] at hs
  simpa [act, FiniteOneTapeSemantics.moveHead] using hs

def embedReaderConfig (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (c : ReaderConfig (nt := nt)) :
    ScanConfig (ns := ns) (nt := nt) :=
  { state := liftReaderTarget q selected isHead c.state
    head := c.head
    tape := c.tape }

def readLiteralArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (r : ULogSourceLogicalBlockReader.State nt) (x : Fin 3) :
    Arrow (ULogSourceObliviousScanProgram.program p hnt blank) :=
  ⟨((State.read q selected isHead r, x), (0 : Fin 2)), by
    simp [ULogSourceObliviousScanProgram.program,
      ULogSourceObliviousScanProgram.step, deterministicAction]⟩

@[simp] theorem actionOf_readLiteralArrow
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (r : ULogSourceLogicalBlockReader.State nt) (x : Fin 3) :
    actionOf (ULogSourceObliviousScanProgram.program p hnt blank)
      (readLiteralArrow p hnt blank q selected isHead r x) =
      liftReaderAction q selected isHead
        (ULogSourceLogicalBlockReader.readerAction blank r x) := by
  simp [readLiteralArrow, actionOf, ULogSourceObliviousScanProgram.program,
    ULogSourceObliviousScanProgram.step, deterministicAction]

theorem readLiteralArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (c : ReaderConfig (nt := nt))
    (hscan : ∃ i mode, c.state = .scan i mode) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (embedReaderConfig q selected isHead c)
      (readLiteralArrow p hnt blank q selected isHead c.state (c.tape c.head)) =
        some (embedReaderConfig q selected isHead
          (ULogSourceLogicalBlockReader.nextConfig blank c)) := by
  rcases c with ⟨cstate, chead, ctape⟩
  dsimp only at hscan ⊢
  rcases hscan with ⟨i, mode, hscan⟩
  subst cstate
  simp [FiniteOneTapeSemantics.step, embedReaderConfig,
    ULogSourceLogicalBlockReader.nextConfig, actionOf_readLiteralArrow,
    liftReaderAction, FiniteOneTapeProgram.transition, readLiteralArrow,
    FiniteOneTapeProgram.actionOf,
    ULogSourceObliviousScanProgram.program,
    ULogSourceObliviousScanProgram.step, deterministicAction,
    liftReaderTarget, writtenTape, moveHead]

def readArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) : ReaderConfig (nt := nt) → ℕ →
      List (Arrow (ULogSourceObliviousScanProgram.program p hnt blank))
  | _, 0 => []
  | c, k + 1 =>
      readLiteralArrow p hnt blank q selected isHead c.state (c.tape c.head) ::
        readArrows p hnt blank q selected isHead
          (ULogSourceLogicalBlockReader.nextConfig blank c) k

@[simp] theorem readArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (c : ReaderConfig (nt := nt)) (k : ℕ) :
    (readArrows p hnt blank q selected isHead c k).length = k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => simp [readArrows, ih]

theorem read_exact_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) (c : ReaderConfig (nt := nt)) (k : ℕ)
    (hscan : ∀ j, j < k →
      ∃ i mode,
        (((ULogSourceLogicalBlockReader.nextConfig blank)^[j] c).state =
          .scan i mode)) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (readArrows p hnt blank q selected isHead c k)
      (embedReaderConfig q selected isHead c) =
        some (embedReaderConfig q selected isHead
          ((ULogSourceLogicalBlockReader.nextConfig blank)^[k] c)) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      have hscan₀ := hscan 0 (by omega)
      have hscanTail : ∀ j, j < k →
          ∃ i mode,
            (((ULogSourceLogicalBlockReader.nextConfig blank)^[j]
              (ULogSourceLogicalBlockReader.nextConfig blank c)).state =
                .scan i mode) := by
        intro j hj
        rcases hscan (j + 1) (by omega) with ⟨i, mode, hs⟩
        refine ⟨i, mode, ?_⟩
        have hiter := Function.iterate_succ_apply
          (ULogSourceLogicalBlockReader.nextConfig blank) j c
        rw [← hiter]
        simpa [Nat.succ_eq_add_one] using hs
      rw [Function.iterate_succ_apply]
      simp only [readArrows, FiniteOneTapeSemantics.run_cons,
        readLiteralArrow_step p hnt blank q selected isHead c hscan₀]
      simpa using ih (ULogSourceLogicalBlockReader.nextConfig blank c) hscanTail

theorem read_oneHot_to_branch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns) (tape : Int → Fin 3) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∃ arrows : List (Arrow
      (ULogSourceObliviousScanProgram.program p hnt blank)),
      arrows.length = nt ∧
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true) arrows
        (embedReaderConfig q none true
          (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head)) =
        some {
          state := .branch q read
          head := head + nt
          tape := tape } := by
  let c := ULogSourceLogicalBlockReader.initialConfig blank hnt tape head
  let arrows := readArrows p hnt blank q none true c nt
  refine ⟨arrows, readArrows_length p hnt blank q none true c nt, ?_⟩
  have hscan : ∀ j, j < nt →
      ∃ i mode,
        (((ULogSourceLogicalBlockReader.nextConfig blank)^[j] c).state =
          .scan i mode) := by
    intro j hj
    rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
      blank read hnt tape head hone j (by omega)]
    by_cases hzero : j = 0
    · subst j
      exact ⟨⟨0, hnt⟩, .fresh, by
        simp [ULogSourceLogicalBlockReader.oneHotExpected]⟩
    · by_cases hbefore : j ≤ read.1
      · exact ⟨⟨j, by omega⟩, .bits none, by
          simp [ULogSourceLogicalBlockReader.oneHotExpected,
            ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore]⟩
      · exact ⟨⟨j, hj⟩, .bits (some read), by
          simp [ULogSourceLogicalBlockReader.oneHotExpected,
            ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore, hj]⟩
  rw [read_exact_run p hnt blank q none true c nt hscan]
  rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
    blank read hnt tape head hone nt le_rfl]
  simp [embedReaderConfig, liftReaderTarget,
    ULogSourceLogicalBlockReader.oneHotExpected,
    ULogSourceLogicalBlockReader.oneHotStage_terminal]

theorem read_oneHot_unmarked_to_flag
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank read : Fin nt) (q : Fin ns)
    (selected : Option (BoundedAction ns nt))
    (tape : Int → Fin 3) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∃ arrows : List (Arrow
      (ULogSourceObliviousScanProgram.program p hnt blank)),
      arrows.length = nt ∧
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true) arrows
        (embedReaderConfig q selected false
          (ULogSourceLogicalBlockReader.initialConfig blank hnt tape head)) =
        some {
          state := .flag q selected
          head := head + nt
          tape := tape } := by
  let c := ULogSourceLogicalBlockReader.initialConfig blank hnt tape head
  let arrows := readArrows p hnt blank q selected false c nt
  refine ⟨arrows, readArrows_length p hnt blank q selected false c nt, ?_⟩
  have hscan : ∀ j, j < nt →
      ∃ i mode,
        (((ULogSourceLogicalBlockReader.nextConfig blank)^[j] c).state =
          .scan i mode) := by
    intro j hj
    rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
      blank read hnt tape head hone j (by omega)]
    by_cases hzero : j = 0
    · subst j
      exact ⟨⟨0, hnt⟩, .fresh, by
        simp [ULogSourceLogicalBlockReader.oneHotExpected]⟩
    · by_cases hbefore : j ≤ read.1
      · exact ⟨⟨j, by omega⟩, .bits none, by
          simp [ULogSourceLogicalBlockReader.oneHotExpected,
            ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore]⟩
      · exact ⟨⟨j, hj⟩, .bits (some read), by
          simp [ULogSourceLogicalBlockReader.oneHotExpected,
            ULogSourceLogicalBlockReader.oneHotStage, hzero, hbefore, hj]⟩
  rw [read_exact_run p hnt blank q selected false c nt hscan]
  rw [ULogSourceLogicalBlockReader.iterate_oneHot_expected
    blank read hnt tape head hone nt le_rfl]
  simp [embedReaderConfig, liftReaderTarget,
    ULogSourceLogicalBlockReader.oneHotExpected,
    ULogSourceLogicalBlockReader.oneHotStage_terminal]

end PakFixedPolyomino.ULogSourceObliviousScanExecution
