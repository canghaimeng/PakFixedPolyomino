import PakFixedPolyomino.ULogSemanticRunLift

/-! The finite concrete interpreter as an explicit binary nondeterministic machine. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def concreteHalted : Result → Bool
  | .running _ _ => false
  | .accepted _ | .rejected | .stuck => true

def concreteAccepting : Result → Bool
  | .accepted _ => true
  | _ => false

def validStepAt (slot : Fin 2) : Result → Option Result
  | .running q z =>
      match program.rule q z.focus slot with
      | none => none
      | some _ => some (oneStepAt slot (.running q z))
  | _ => none

def concreteNext (r : Result) : List Result :=
  [validStepAt 0 r, validStepAt 1 r].filterMap id

theorem concreteAccepting_halted {r : Result}
    (h : concreteAccepting r = true) : concreteHalted r = true := by
  cases r <;> simp_all [concreteAccepting, concreteHalted]

@[simp] theorem concreteNext_length_le_two (r : Result) :
    (concreteNext r).length ≤ 2 := by
  cases h₀ : validStepAt 0 r <;> cases h₁ : validStepAt 1 r <;>
    simp [concreteNext, h₀, h₁]

def concreteMachine (start : BitString → Result) :
    BinaryNondeterministicMachine where
  Config := Result
  start := start
  next := concreteNext
  halt := concreteHalted
  accept := concreteAccepting
  accept_halts := fun _ h => concreteAccepting_halted h
  binary_branching := concreteNext_length_le_two

theorem validStepAt_some_eq_oneStepAt
    {slot : Fin 2} {r s : Result} (h : validStepAt slot r = some s) :
    oneStepAt slot r = s := by
  cases r with
  | running q z =>
      simp only [validStepAt] at h
      cases hrule : program.rule q z.focus slot <;> simp [hrule] at h
      exact h
  | accepted z => simp [validStepAt] at h
  | rejected => simp [validStepAt] at h
  | stuck => simp [validStepAt] at h

theorem validStepAt_one_nonchoose (q : State)
    (hq : q ≠ .chooseSlot) (z : Zipper Tape) :
    validStepAt 1 (.running q z) = none := by
  unfold validStepAt
  cases hrule : program.rule q z.focus 1 with
  | none => simp [validStepAt, hrule]
  | some a =>
      have hnon : program.rule q z.focus 1 ≠ none := by simp [hrule]
      have hchoose := ULogProgram.slot_one_only_choose hnon
      exact (hq hchoose.1).elim

theorem concreteNext_running_nonchoose (q : State)
    (hq : q ≠ .chooseSlot) (z : Zipper Tape) :
    concreteNext (.running q z) =
      match validStepAt 0 (.running q z) with
      | none => []
      | some s => [s] := by
  unfold concreteNext
  rw [show validStepAt 1 (.running q z) = none from
    validStepAt_one_nonchoose q hq z]
  cases h₀ : validStepAt 0 (.running q z) <;>
    simp [concreteNext, h₀]

theorem validStepAt_chooseSlot
    (slot : Bool) (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true) :
    validStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨left, head, right⟩) =
      some (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨left, head, right⟩)) := by
  cases slot <;>
    simp [validStepAt, ULogBytecode.slotIndex, chooseSlot_head_zero,
      chooseSlot_head_one, hhead]

end PakFixedPolyomino.ULogBootstrapExecution
