import PakFixedPolyomino.OneTapeTableauCompiler
import Mathlib.Tactic

/-!
# Finite binary-branch one-tape programs

An executable program is a two-slot rule table.  The subtype of occupied
slots is its literal labelled-arrow alphabet.  This representation makes
finiteness and binary branching structural rather than obligations left to a
generated JSON table, and compiles directly to `TableauMachineData`.
-/

namespace PakFixedPolyomino.FiniteOneTapeProgram

open OneTapeTableau

structure Action (State Tape : Type*) where
  write : Tape
  target : State
  move : Move
  deriving DecidableEq, Repr

/-- Exactly two labelled-arrow slots for every source pair.  `none` is an
unused label, so distinct occupied slots remain distinct computation paths
even if their actions coincide. -/
structure Program (State Tape : Type*) where
  rule : State → Tape → Fin 2 → Option (Action State Tape)

abbrev Arrow {State Tape : Type*} (P : Program State Tape) :=
  {x : (State × Tape) × Fin 2 // P.rule x.1.1 x.1.2 x.2 ≠ none}

variable {State Tape : Type*}
variable [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

noncomputable instance (P : Program State Tape) : Fintype (Arrow P) := Fintype.ofFinite _
instance (P : Program State Tape) : DecidableEq (Arrow P) := inferInstance

def actionOf (P : Program State Tape) (a : Arrow P) : Action State Tape :=
  match h : P.rule a.1.1.1 a.1.1.2 a.1.2 with
  | some act => act
  | none => False.elim (a.2 h)

def transition (P : Program State Tape) (a : Arrow P) : Transition State Tape :=
  { sourceState := a.1.1.1
    read := a.1.1.2
    write := (actionOf P a).write
    targetState := (actionOf P a).target
    move := (actionOf P a).move }

@[simp] theorem transition_sourceState (P : Program State Tape) (a : Arrow P) :
    (transition P a).sourceState = a.1.1.1 := rfl

@[simp] theorem transition_read (P : Program State Tape) (a : Arrow P) :
    (transition P a).read = a.1.1.2 := rfl

theorem arrows_at_source_card_le_two
    (P : Program State Tape) (q : State) (x : Tape) :
    Fintype.card {a : Arrow P // (transition P a).sourceState = q ∧
      (transition P a).read = x} ≤ 2 := by
  let f : {a : Arrow P // (transition P a).sourceState = q ∧
      (transition P a).read = x} → Fin 2 := fun a => a.1.1.2
  have hf : Function.Injective f := by
    intro a b hi
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact a.2.1.trans b.2.1.symm
      · exact a.2.2.trans b.2.2.symm
    · exact hi
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

/-- A deterministic program occupies only slot zero. -/
def deterministic (step : State → Tape → Option (Action State Tape)) :
    Program State Tape where
  rule q x i := if i = 0 then step q x else none

theorem deterministic_slot_one_empty
    (step : State → Tape → Option (Action State Tape)) (q : State) (x : Tape) :
    (deterministic step).rule q x 1 = none := by
  rfl

/-- The literal arrow compiler consumed by the higher-block tableau. -/
def tableauData (P : Program State Tape) (movable : Tape → Bool) :
    TableauMachineData State Tape (Arrow P) :=
  OneTapeTableau.tableauMachineData (transition P) movable

@[simp] theorem tableauData_source
    (P : Program State Tape) (movable : Tape → Bool) (a : Arrow P) :
    (tableauData P movable).source a = (a.1.1.1, a.1.1.2) := rfl

end PakFixedPolyomino.FiniteOneTapeProgram
