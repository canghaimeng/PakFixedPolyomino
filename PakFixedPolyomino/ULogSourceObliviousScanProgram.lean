import PakFixedPolyomino.ULogSourceObliviousWindow
import PakFixedPolyomino.ULogSourceLogicalBlockReader
import PakFixedPolyomino.ULogSourceOneHotMacroEquiv
import PakFixedPolyomino.ULogSourceOneHotPaddedMacro
import PakFixedPolyomino.ULogCompiler
import Mathlib.Tactic

/-! # Literal branch-preserving scan of an oblivious source window

The physical head starts on the left blank delimiter.  Every logical cell is
validated at fixed width; the unique marked cell is decoded and exposes the
only two-slot branch.  After that branch the scan continues to the same right
delimiter, so the endpoint and footprint do not depend on the chosen rule.
-/

namespace PakFixedPolyomino.ULogSourceObliviousScanProgram

open OneTapeTableau FiniteOneTapeProgram
open ULogCompiler ULogSourceOneHotReader ULogSourceLogicalBlockReader

abbrev Tape := Fin 3

variable {ns nt : ℕ}

inductive State (ns nt : ℕ) where
  | atLeft : Fin ns → State ns nt
  | flag : Fin ns → Option (BoundedAction ns nt) → State ns nt
  | read : Fin ns → Option (BoundedAction ns nt) → Bool →
      ULogSourceLogicalBlockReader.State nt → State ns nt
  | branch : Fin ns → Fin nt → State ns nt
  | returnLeft : BoundedAction ns nt → State ns nt
  | updateLRFlag : BoundedAction ns nt → Bool → State ns nt
  | skipLR : BoundedAction ns nt → Bool → Bool → Fin nt → State ns nt
  | updateRLFlag : BoundedAction ns nt → Bool → State ns nt
  | skipRL : BoundedAction ns nt → Bool → Fin nt → State ns nt
  | ready : BoundedAction ns nt → State ns nt
  | reject : State ns nt
  deriving DecidableEq, Fintype, Repr

def liftReaderTarget (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (isHead : Bool) : ULogSourceLogicalBlockReader.State nt → State ns nt
  | .done read => if isHead then .branch q read else .flag q selected
  | .reject => .reject
  | r => .read q selected isHead r

def liftReaderAction (q : Fin ns)
    (selected : Option (BoundedAction ns nt)) (isHead : Bool)
    (a : Action (ULogSourceLogicalBlockReader.State nt) Tape) :
    Action (State ns nt) Tape :=
  ⟨a.write, liftReaderTarget q selected isHead a.target, a.move⟩

def validBit (x : Tape) : Bool :=
  decide (x = ULogSourceOneHotReader.zero ∨ x = ULogSourceOneHotReader.one)

/-- Left-to-right flag rewrite.  Only a right move is active in this pass. -/
def updateLR (a : BoundedAction ns nt) (armed : Bool) (x : Tape) :
    Option (Tape × Bool) :=
  if validBit x = false then none
  else if a.move = .right then
    if armed then
      if x = ULogSourceOneHotReader.zero then
        some (ULogSourceOneHotReader.one, false)
      else none
    else if x = ULogSourceOneHotReader.one then
      some (ULogSourceOneHotReader.zero, true)
    else some (x, false)
  else some (x, armed)

/-- Right-to-left flag rewrite.  Only a left move is active in this pass. -/
def updateRL (a : BoundedAction ns nt) (armed : Bool) (x : Tape) :
    Option (Tape × Bool) :=
  if validBit x = false then none
  else if a.move = .left then
    if armed then
      if x = ULogSourceOneHotReader.zero then
        some (ULogSourceOneHotReader.one, false)
      else none
    else if x = ULogSourceOneHotReader.one then
      some (ULogSourceOneHotReader.zero, true)
    else some (x, false)
  else some (x, armed)

def deterministicAction (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) : State ns nt → Tape → Option (Action (State ns nt) Tape)
  | .atLeft q, x =>
      if x = ULogSourceOneHotReader.blank then
        some ⟨x, .flag q none, .right⟩
      else some ⟨x, .reject, .stay⟩
  | .flag q selected, x =>
      if x = ULogSourceOneHotReader.blank then
        match selected with
        | some a => some ⟨x, .returnLeft a, .left⟩
        | none => some ⟨x, .reject, .stay⟩
      else if x = ULogSourceOneHotReader.zero then
        some ⟨x, .read q selected false
          (.scan ⟨0, hnt⟩ .fresh), .right⟩
      else if x = ULogSourceOneHotReader.one then
        match selected with
        | some _ => some ⟨x, .reject, .stay⟩
        | none => some ⟨x, .read q none true
            (.scan ⟨0, hnt⟩ .fresh), .right⟩
      else some ⟨x, .reject, .stay⟩
  | .read q selected isHead r, x =>
      some (liftReaderAction q selected isHead
        (ULogSourceLogicalBlockReader.readerAction blank r x))
  | .branch q read, _ => none
  | .returnLeft a, x =>
      if x = ULogSourceOneHotReader.blank then
        some ⟨x, .updateLRFlag a false, .right⟩
      else some ⟨x, .returnLeft a, .left⟩
  | .updateLRFlag a armed, x =>
      if x = ULogSourceOneHotReader.blank then
        if armed then some ⟨x, .reject, .stay⟩
        else some ⟨x, .skipRL a false ⟨nt - 1, by omega⟩, .left⟩
      else
        match updateLR a armed x with
        | none => some ⟨x, .reject, .stay⟩
        | some (write, armed') =>
            some ⟨write, .skipLR a armed' (x = ULogSourceOneHotReader.one)
              ⟨0, hnt⟩, .right⟩
  | .skipLR a armed rewrite i, x =>
      if validBit x = false then some ⟨x, .reject, .stay⟩
      else
        let write := if rewrite then
          ULogSourceOneHotReader.tapeOfBit
            ((ULogSourceOneHotBlocks.encodeOneHot a.write).get
              ⟨i.1, by simpa using i.2⟩)
        else x
        if hlast : i.1 + 1 = nt then
          some ⟨write, .updateLRFlag a armed, .right⟩
        else some ⟨write, .skipLR a armed rewrite
          ⟨i.1 + 1, by omega⟩, .right⟩
  | .updateRLFlag a armed, x =>
      match updateRL a armed x with
      | none => some ⟨x, .reject, .stay⟩
      | some (write, armed') =>
          some ⟨write, .skipRL a armed' ⟨nt - 1, by omega⟩, .left⟩
  | .skipRL a armed i, x =>
      if x = ULogSourceOneHotReader.blank then
        if armed then some ⟨x, .reject, .stay⟩
        else some ⟨x, .atLeft a.target, .stay⟩
      else if validBit x = false then some ⟨x, .reject, .stay⟩
      else if hfirst : i.1 = 0 then
        some ⟨x, .updateRLFlag a armed, .left⟩
      else some ⟨x, .skipRL a armed ⟨i.1 - 1, by omega⟩, .left⟩
  | .ready _, _ => none
  | .reject, _ => none

/-- The unique nondeterministic source-rule occurrence. -/
def branchAction (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt)
    (slot : Fin 2) (x : Tape) : Option (Action (State ns nt) Tape) :=
  (p.rule q read (slot = 1)).map fun a => ⟨x, .flag q (some a), .stay⟩

def step (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) :
    State ns nt → Tape → Fin 2 → Option (Action (State ns nt) Tape)
  | .branch q read, x, slot => branchAction p q read slot x
  | s, x, slot => if slot = 0 then deterministicAction p hnt blank s x else none

def program (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) :
    Program (State ns nt) Tape where
  rule := step p hnt blank

@[simp] theorem branch_rule (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape)
    (slot : Fin 2) :
    (program p hnt blank).rule (.branch q read) x slot =
      (p.rule q read (slot = 1)).map fun a =>
        ⟨x, .flag q (some a), .stay⟩ := rfl

theorem nonbranch_slot_one_empty (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (s : State ns nt) (x : Tape)
    (hs : ∀ q read, s ≠ .branch q read) :
    (program p hnt blank).rule s x 1 = none := by
  cases s with
  | branch q read => exact False.elim (hs q read rfl)
  | atLeft q => rfl
  | flag q selected => rfl
  | read q selected isHead r => rfl
  | returnLeft a => rfl
  | updateLRFlag a armed => rfl
  | skipLR a armed rewrite i => rfl
  | updateRLFlag a armed => rfl
  | skipRL a armed i => rfl
  | ready selected => rfl
  | reject => rfl

theorem branch_occupied_iff (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape)
    (slot : Fin 2) :
    (program p hnt blank).rule (.branch q read) x slot ≠ none ↔
      p.rule q read (slot = 1) ≠ none := by
  rw [branch_rule]
  constructor <;> intro h
  · intro hp
    simp [hp] at h
  · cases hp : p.rule q read (slot = 1) with
    | none => exact False.elim (h hp)
    | some a => simp [hp]

def branchArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hoccupied : p.rule q read (slot = 1) = some a) :
    Arrow (program p hnt blank) :=
  ⟨((State.branch q read, x), slot), by
    simp [program, step, branchAction, hoccupied]⟩

@[simp] theorem actionOf_branchArrow
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape)
    (slot : Fin 2) (a : BoundedAction ns nt)
    (hoccupied : p.rule q read (slot = 1) = some a) :
    actionOf (program p hnt blank)
      (branchArrow p hnt blank q read x slot a hoccupied) =
      ⟨x, .flag q (some a), .stay⟩ := by
  apply ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq
  simp [branchArrow, program, step, branchAction, hoccupied]

/-- Literal branch certificate retained by the oblivious scan. -/
structure PhysicalBranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape) where
  slot : Fin 2
  action : BoundedAction ns nt
  occupied : p.rule q read (slot = 1) = some action
  arrow : Arrow (program p hnt blank)
  arrow_eq : arrow = branchArrow p hnt blank q read x slot action occupied

theorem PhysicalBranch.ext_slot
    {p : BoundedProgram ns nt} {hnt : 0 < nt} {blank : Fin nt}
    {q : Fin ns} {read : Fin nt} {x : Tape}
    {a b : PhysicalBranch p hnt blank q read x}
    (hslot : a.slot = b.slot) : a = b := by
  cases a with
  | mk aslot aaction aoccupied aarrow aarrowEq =>
      cases b with
      | mk bslot baction boccupied barrow barrowEq =>
          simp only at hslot
          subst bslot
          have haction : aaction = baction :=
            Option.some.inj (aoccupied.symm.trans boccupied)
          subst baction
          have hp : aoccupied = boccupied := Subsingleton.elim _ _
          cases hp
          have harrow : aarrow = barrow := aarrowEq.trans barrowEq.symm
          cases harrow
          rfl

noncomputable def sourceChoicePhysicalBranchEquiv
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt) (x : Tape) :
    ULogSourceOneHotMacroEquiv.SourceChoice p q read ≃
      PhysicalBranch p hnt blank q read x where
  toFun c :=
    { slot := c.slot
      action := c.action
      occupied := c.occupied
      arrow := branchArrow p hnt blank q read x c.slot c.action c.occupied
      arrow_eq := rfl }
  invFun c := ⟨c.slot, c.action, c.occupied⟩
  left_inv c := by
    apply ULogSourceOneHotMacroEquiv.SourceChoice.ext
    rfl
  right_inv c := PhysicalBranch.ext_slot rfl

/-- Numerical packaging.  As with the padded local compiler, the result type
is inferred so Lean keeps the finite-state equivalence opaque. -/
noncomputable def boundedProgram (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) :=
  ofFiniteProgram (Fintype.equivFin (State ns nt)) (Equiv.refl (Fin 3))
    (program p hnt blank)

end PakFixedPolyomino.ULogSourceObliviousScanProgram
