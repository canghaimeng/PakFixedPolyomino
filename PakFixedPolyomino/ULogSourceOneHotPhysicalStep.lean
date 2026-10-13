import PakFixedPolyomino.ULogSourceLogicalBlockReader
import PakFixedPolyomino.ULogCompiler
import Mathlib.Tactic

/-!
# Physical source-step microprogram

This is the literal finite one-tape control for one source-block step.  The
block reader is called directly, source branching occurs only at `branch`,
and the rewind, writer, and relocation phases perform genuine tape-head
moves.  The next layer proves their concatenated tape roundtrip.
-/

namespace PakFixedPolyomino.ULogSourceOneHotPhysicalStep

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler

abbrev Tape := Fin 3
abbrev zero : Tape := ULogSourceLogicalBlockReader.zero
abbrev one : Tape := ULogSourceLogicalBlockReader.one
abbrev blankCell : Tape := ULogSourceLogicalBlockReader.blank
abbrev tapeOfBit : Bool → Tape := ULogSourceLogicalBlockReader.tapeOfBit

variable {ns nt : ℕ}

def relocationDistance (move : Move) (nt : ℕ) : ℕ :=
  match move with
  | .right => 0
  | .stay => nt
  | .left => 2 * nt

/-- Finite control for the concrete physical phases. -/
inductive State (ns nt : ℕ) where
  | reading : Fin ns → ULogSourceLogicalBlockReader.State nt → State ns nt
  | branch : Fin ns → Fin nt → State ns nt
  | rewind : Fin ns → Fin nt → Bool → BoundedAction ns nt → Fin nt → State ns nt
  | writing : BoundedAction ns nt → Fin nt → State ns nt
  /-- The counter includes its terminal value, needed for the `2 * nt`
  left-relocation case. -/
  | relocate : BoundedAction ns nt → Fin (2 * nt + 1) → State ns nt
  | accept
  | reject
  deriving DecidableEq, Fintype, Repr

/-- The nonterminal part of physical control.  Keeping this separate gives
the eventual bounded compiler its reserved `Fin 2` halt codes without
renumbering any microstate. -/
inductive Active (ns nt : ℕ) where
  | reading : Fin ns → ULogSourceLogicalBlockReader.State nt → Active ns nt
  | branch : Fin ns → Fin nt → Active ns nt
  | rewind : Fin ns → Fin nt → Bool → BoundedAction ns nt → Fin nt → Active ns nt
  | writing : BoundedAction ns nt → Fin nt → Active ns nt
  | relocate : BoundedAction ns nt → Fin (2 * nt + 1) → Active ns nt
  deriving DecidableEq, Fintype, Repr

def stateToReserved : State ns nt → Fin 2 ⊕ Active ns nt
  | .accept => .inl 0
  | .reject => .inl 1
  | .reading q r => .inr (.reading q r)
  | .branch q read => .inr (.branch q read)
  | .rewind q read slot a i => .inr (.rewind q read slot a i)
  | .writing a i => .inr (.writing a i)
  | .relocate a i => .inr (.relocate a i)

def reservedToState : Fin 2 ⊕ Active ns nt → State ns nt
  | .inl 0 => .accept
  | .inl 1 => .reject
  | .inr (.reading q r) => .reading q r
  | .inr (.branch q read) => .branch q read
  | .inr (.rewind q read slot a i) => .rewind q read slot a i
  | .inr (.writing a i) => .writing a i
  | .inr (.relocate a i) => .relocate a i

def reservedStateEquiv : State ns nt ≃ Fin 2 ⊕ Active ns nt where
  toFun := stateToReserved
  invFun := reservedToState
  left_inv := by intro s; cases s <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl i => fin_cases i <;> rfl
    | inr a => cases a <;> rfl

def haltedSource (q : Fin ns) : Bool := decide (q.1 < 2)

def haltedTarget (q : Fin ns) : State ns nt :=
  if q.1 = 0 then .accept else .reject

def initialReaderState (hnt : 0 < nt) : ULogSourceLogicalBlockReader.State nt :=
  .scan ⟨0, hnt⟩ .fresh

/-- Lift one literal blank-aware reader action into the integrated control.
Successful reader completion enters the sole two-slot branch state. -/
def liftReaderAction (q : Fin ns) (a : Action (ULogSourceLogicalBlockReader.State nt) Tape) :
    Action (State ns nt) Tape :=
  ⟨a.write,
    match a.target with
    | .done read => .branch q read
    | .reject => .reject
    | next => .reading q next,
    a.move⟩

def readerAction (logicalBlank : Fin nt) (q : Fin ns)
    (r : ULogSourceLogicalBlockReader.State nt) (x : Tape) : Action (State ns nt) Tape :=
  liftReaderAction q (ULogSourceLogicalBlockReader.readerAction logicalBlank r x)

/-- The unique micro action outside source rule choice. -/
def microAction (hnt : 0 < nt) (logicalBlank : Fin nt) :
    State ns nt → Tape → Action (State ns nt) Tape
  | .reading q r, x =>
      if haltedSource q then ⟨x, haltedTarget q, .stay⟩ else readerAction logicalBlank q r x
  | .rewind q read slot a i, x =>
      if hlast : i.1 + 1 = nt then
        ⟨x, .writing a ⟨0, hnt⟩, .left⟩
      else
        ⟨x, .rewind q read slot a ⟨i.1 + 1, by omega⟩, .left⟩
  | .writing a i, _ =>
      if hlast : i.1 + 1 = nt then
        ⟨tapeOfBit ((ULogSourceOneHotBlocks.encodeOneHot a.write).get
          ⟨i.1, by simpa using i.isLt⟩), .relocate a ⟨0, Nat.zero_lt_succ _⟩, .right⟩
      else
        ⟨tapeOfBit ((ULogSourceOneHotBlocks.encodeOneHot a.write).get
          ⟨i.1, by simpa using i.isLt⟩),
          .writing a ⟨i.1 + 1, by omega⟩, .right⟩
  | .relocate a i, x =>
      if hdone : relocationDistance a.move nt ≤ i.1 then
        ⟨x, .reading a.target (initialReaderState hnt), .stay⟩
      else
        ⟨x, .relocate a ⟨i.1 + 1, by
          have hdistance : relocationDistance a.move nt ≤ 2 * nt := by
            cases a.move <;> simp [relocationDistance] <;> omega
          omega⟩, .left⟩
  | .accept, x => ⟨x, .accept, .stay⟩
  | .reject, x => ⟨x, .reject, .stay⟩
  | .branch q read, x => ⟨x, .branch q read, .stay⟩

/-- The only two-slot lookup.  Its physical label is exactly the Boolean
source slot (`0 = false`, `1 = true`). -/
def branchAction (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt)
    (slot : Fin 2) (x : Tape) : Option (Action (State ns nt) Tape) :=
  if haltedSource q then
    if slot = 0 then some ⟨x, haltedTarget q, .stay⟩ else none
  else
    (p.rule q read (slot = 1)).map fun a =>
      ⟨x, .rewind q read (slot = 1) a ⟨0, by
        have : 0 < nt := Fin.pos read
        exact this⟩, .stay⟩

def step (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt) :
    State ns nt → Tape → Fin 2 → Option (Action (State ns nt) Tape)
  | .branch q read, x, slot => branchAction p q read slot x
  | s, x, slot => if slot = 0 then some (microAction hnt logicalBlank s x) else none

def program (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt) :
    Program (State ns nt) Tape where
  rule q x slot := step p hnt logicalBlank q x slot

theorem nonbranch_slot_one_empty (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (s : State ns nt) (x : Tape)
    (hs : ∀ q read, s ≠ State.branch q read) :
    (program p hnt logicalBlank).rule s x 1 = none := by
  cases s with
  | branch q read => exact False.elim (hs q read rfl)
  | reading q r => rfl
  | rewind q read slot a i => rfl
  | writing a i => rfl
  | relocate a i => rfl
  | accept => rfl
  | reject => rfl

theorem branch_rule_exact (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Fin 2) (x : Tape)
    (hlive : haltedSource q = false) :
    (program p hnt logicalBlank).rule (.branch q read) x slot =
      (p.rule q read (slot = 1)).map (fun a =>
        ⟨x, .rewind q read (slot = 1) a ⟨0, Fin.pos read⟩, .stay⟩) := by
  simp [program, step, branchAction, hlive]

/-- Source-slot dispatch itself does not move the physical head; all spatial
motion belongs to the explicit rewind/write/relocate phases. -/
theorem branch_action_head_delta (p : BoundedProgram ns nt) (q : Fin ns)
    (read : Fin nt) (slot : Fin 2) (x : Tape) (out : Action (State ns nt) Tape)
    (h : branchAction p q read slot x = some out) : out.move = .stay := by
  by_cases hhalt : haltedSource q = true
  · by_cases hslot : slot = 0
    · simp [branchAction, hhalt, hslot] at h
      subst out
      rfl
    · simp [branchAction, hhalt, hslot] at h
  · cases hrule : p.rule q read (slot = 1) with
    | none =>
        have hhalt' : haltedSource q = false := Bool.eq_false_of_not_eq_true hhalt
        simp [branchAction, hhalt', hrule] at h
    | some action =>
        have hhalt' : haltedSource q = false := Bool.eq_false_of_not_eq_true hhalt
        simp [branchAction, hhalt', hrule] at h
        subst out
        rfl

/-- Lifting the real logical-block reader preserves its move exactly. -/
@[simp] theorem liftReaderAction_move (q : Fin ns)
    (a : Action (ULogSourceLogicalBlockReader.State nt) Tape) :
    (liftReaderAction q a).move = a.move := rfl

/-- Rewind microsteps move exactly one cell left. -/
theorem rewind_head_delta (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (i : Fin nt) (x : Tape) :
    (microAction hnt logicalBlank (.rewind q read slot a i) x).move = .left := by
  by_cases hlast : i.1 + 1 = nt <;> simp [microAction, hlast]

/-- Writer microsteps move exactly one cell right and write the requested
one-hot physical letter. -/
theorem writing_head_delta (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin nt) (x : Tape) :
    (microAction hnt logicalBlank (.writing a i) x).move = .right := by
  by_cases hlast : i.1 + 1 = nt <;> simp [microAction, hlast]

/-- Relocation moves left until its prescribed block distance is exhausted,
then makes a zero-delta handoff into the next block reader. -/
theorem relocate_move_cases (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)) (x : Tape) :
    (microAction hnt logicalBlank (.relocate a i) x).move =
      if relocationDistance a.move nt ≤ i.1 then .stay else .left := by
  by_cases hdone : relocationDistance a.move nt ≤ i.1 <;>
    simp [microAction, hdone]

theorem relocation_distance_cases (a : BoundedAction ns nt) :
    relocationDistance a.move nt = 0 ∨ relocationDistance a.move nt = nt ∨
      relocationDistance a.move nt = 2 * nt := by
  cases a.move <;> simp [relocationDistance]

end PakFixedPolyomino.ULogSourceOneHotPhysicalStep
