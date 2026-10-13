import PakFixedPolyomino.ULogBytecode
import PakFixedPolyomino.ComplexityModel
import Mathlib.Tactic

/-!
# Executable semantics of universal one-tape bytecode

This module fixes the semantic machine that the finite `U_log` interpreter
must refine.  A bytecode program has two labelled slots per source/read pair;
the universal successor list executes slot zero and slot one in that order and
therefore has length at most two with multiplicity preserved.
-/

namespace PakFixedPolyomino.ULogSemantics

open OneTapeTableau ULogBytecode

def blankCode : ℕ := 2
def acceptCode : ℕ := 0
def rejectCode : ℕ := 1
def startCode : ℕ := 2

structure Config where
  program : ProgramCode
  state : ℕ
  leftRev : List ℕ
  focus : ℕ
  right : List ℕ
  deriving DecidableEq, Repr

def halted (c : Config) : Bool := decide (c.state < 2)
def accepting (c : Config) : Bool := decide (c.state = acceptCode)

theorem accepting_halted {c : Config} (h : accepting c = true) :
    halted c = true := by
  have hs : c.state = acceptCode := by
    simpa [accepting] using h
  simp [halted, hs, acceptCode]

def applyAction (c : Config) (a : ActionCode) : Config :=
  match a.move with
  | .stay => { c with state := a.target, focus := a.write }
  | .right =>
      match c.right with
      | [] =>
          ⟨c.program, a.target, a.write :: c.leftRev, blankCode, []⟩
      | y :: ys =>
          ⟨c.program, a.target, a.write :: c.leftRev, y, ys⟩
  | .left =>
      match c.leftRev with
      | [] =>
          ⟨c.program, a.target, [], blankCode, a.write :: c.right⟩
      | y :: ys =>
          ⟨c.program, a.target, ys, y, a.write :: c.right⟩

def stepSlot (slot : Bool) (c : Config) : Option Config :=
  if halted c then none
  else (lookupRule c.program c.state c.focus slot).map (applyAction c)

def next (c : Config) : List Config :=
  [stepSlot false c, stepSlot true c].filterMap id

@[simp] theorem next_length_le_two (c : Config) : (next c).length ≤ 2 := by
  cases h₀ : stepSlot false c <;> cases h₁ : stepSlot true c <;>
    simp [next, h₀, h₁]

def bitCode : Bool → ℕ
  | false => 0
  | true => 1

def initialTape : List Bool → ℕ × List ℕ
  | [] => (blankCode, [])
  | b :: bs => (bitCode b, bs.map bitCode)

def startFrom (program : ProgramCode) (input : BitString) : Config :=
  let tape := initialTape input
  ⟨program, startCode, [], tape.1, tape.2⟩

def start (x : BitString) : Config :=
  match decodeProgramPrefix x with
  | none => ⟨[], rejectCode, [], blankCode, []⟩
  | some (program, payload) =>
      match decodePayload payload with
      | none => ⟨program, rejectCode, [], blankCode, []⟩
      | some input => startFrom program input

def machine : BinaryNondeterministicMachine where
  Config := Config
  start := start
  next := next
  halt := halted
  accept := accepting
  accept_halts := fun _ h => accepting_halted h
  binary_branching := next_length_le_two

def count (clock : ℕ → ℕ) (x : BitString) : ℕ :=
  machine.countOn clock x

theorem stepSlot_some_rule {slot : Bool} {c c' : Config}
    (h : stepSlot slot c = some c') :
    halted c = false ∧
      ∃ a, lookupRule c.program c.state c.focus slot = some a ∧
        applyAction c a = c' := by
  unfold stepSlot at h
  split at h
  · rename_i hh
    simp at h
  · rename_i hh
    have hhalt : halted c = false := by
      cases hv : halted c <;> simp_all
    cases ha : lookupRule c.program c.state c.focus slot with
    | none => simp [ha] at h
    | some a =>
      rw [ha] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨hhalt, a, rfl, h⟩

theorem next_mem_has_slot {c c' : Config} (h : c' ∈ next c) :
    (∃ hstep : stepSlot false c = some c', True) ∨
      ∃ hstep : stepSlot true c = some c', True := by
  simp [next] at h
  rcases h with h | h
  · exact Or.inl ⟨h.symm, trivial⟩
  · exact Or.inr ⟨h.symm, trivial⟩

@[simp] theorem halted_next_nil {c : Config} (h : halted c = true) :
    next c = [] := by
  simp [next, stepSlot, h]

end PakFixedPolyomino.ULogSemantics
