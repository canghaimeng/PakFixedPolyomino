import PakFixedPolyomino.ULogSourceOneHotBlocks
import PakFixedPolyomino.FiniteOneTapeSemantics
import Mathlib.Tactic

/-!
# Finite one-tape reader for fixed-width one-hot source blocks

This is the literal finite control used to read one compiler-source block.
The tape alphabet is the three physical letters `0`, `1`, and `blank`; the
program deliberately uses only rule slot zero.  A scan state remembers the
current physical bit position and, if it has already seen a one, its unique
position.
-/

namespace PakFixedPolyomino.ULogSourceOneHotReader

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogSourceOneHotBlocks

abbrev Tape := Fin 3

/-- The three physical source letters. -/
abbrev zero : Tape := 0
abbrev one : Tape := 1
abbrev blank : Tape := 2

def tapeOfBit : Bool → Tape
  | false => zero
  | true => one

/-- The finite reader control.  `scan i seen` is poised over bit `i` of the
current block.  `done` and `reject` are inert terminal controls. -/
inductive State (nt : ℕ) where
  | scan : Fin nt → Option (Fin nt) → State nt
  | done : Fin nt → State nt
  | reject : State nt
  deriving DecidableEq, Fintype, Repr

variable {nt : ℕ}

/-- Advance the scan after a syntactically valid bit.  The final cell accepts
exactly when a `1` was seen. -/
def advance (i : Fin nt) (seen : Option (Fin nt)) : State nt :=
  if hlast : i.1 + 1 = nt then
    match seen with
    | some a => .done a
    | none => .reject
  else
    .scan ⟨i.1 + 1, by omega⟩ seen

/-- The deterministic action executed at a source cell.  Every action writes
the letter it read, so a successful read never changes the tape. -/
def readerAction : State nt → Tape → Action (State nt) Tape
  | .scan i seen, x =>
      if x = zero then
        ⟨x, advance i seen, .right⟩
      else if x = one then
        match seen with
        | none => ⟨x, advance i (some i), .right⟩
        | some _ => ⟨x, .reject, .stay⟩
      else
        ⟨x, .reject, .stay⟩
  | .done a, x => ⟨x, .done a, .stay⟩
  | .reject, x => ⟨x, .reject, .stay⟩

def readerStep (q : State nt) (x : Tape) : Option (Action (State nt) Tape) :=
  some (readerAction q x)

/-- The reader uses the designated slot zero and leaves slot one empty. -/
def program : Program (State nt) Tape :=
  deterministic readerStep

def movable : Tape → Bool := fun _ => true

@[simp] theorem reader_slot_one_empty (q : State nt) (x : Tape) :
    program.rule q x 1 = none := by
  rfl

@[simp] theorem reader_slot_zero (q : State nt) (x : Tape) :
    program.rule q x 0 = some (readerAction q x) := by
  rfl

/-- The unique literal occupied arrow for a state/cell pair. -/
def literalArrow (q : State nt) (x : Tape) : Arrow (program (nt := nt)) :=
  ⟨((q, x), 0), by simp [program, deterministic, readerStep]⟩

@[simp] theorem literalArrow_source (q : State nt) (x : Tape) :
    (literalArrow q x).1.1.1 = q := rfl

@[simp] theorem literalArrow_read (q : State nt) (x : Tape) :
    (literalArrow q x).1.1.2 = x := rfl

@[simp] theorem actionOf_literalArrow (q : State nt) (x : Tape) :
    actionOf program (literalArrow q x) = readerAction q x := by
  simp [literalArrow, actionOf, program, deterministic, readerStep]

/-- There is exactly one occupied labelled slot at every source pair. -/
theorem occupied_slot_unique (q : State nt) (x : Tape) (a : Arrow program)
    (hsource : (transition program a).sourceState = q)
    (hread : (transition program a).read = x) :
    a = literalArrow q x := by
  rcases a with ⟨⟨⟨q', x'⟩, slot⟩, hoccupied⟩
  change q' = q at hsource
  change x' = x at hread
  subst q'
  subst x'
  fin_cases slot
  · rfl
  · simp [program, deterministic] at hoccupied

/-- A configuration successor for the literal action at its current head. -/
def nextConfig (c : Config (State nt) Tape) : Config (State nt) Tape :=
  let x := c.tape c.head
  let act := readerAction c.state x
  { state := act.target
    head := moveHead act.move c.head
    tape := writtenTape c act.write }

/-- The reader entry configuration.  The positive-width hypothesis is exactly
what supplies the first physical bit position. -/
def initialConfig (hnt : 0 < nt) (tape : Int → Tape) (head : Int := 0) :
    Config (State nt) Tape :=
  { state := .scan ⟨0, hnt⟩ none
    head := head
    tape := tape }

/-- The literal, occupied slot-zero arrow list for a fixed number of reader
ticks.  Its letters are read from the actual tape, so it is a genuine labelled
path rather than a quotient by coincident actions. -/
def literalArrows : Config (State nt) Tape → ℕ → List (Arrow (program (nt := nt)))
  | _, 0 => []
  | c, n + 1 => literalArrow c.state (c.tape c.head) :: literalArrows (nextConfig c) n

@[simp] theorem literalArrows_length (c : Config (State nt) Tape) (n : ℕ) :
    (literalArrows c n).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [literalArrows, ih]

theorem literalArrow_step (c : Config (State nt) Tape) :
    step program movable c (literalArrow c.state (c.tape c.head)) =
      some (nextConfig c) := by
  simp [FiniteOneTapeSemantics.step, literalArrow, actionOf, program,
    deterministic, readerStep, transition, nextConfig, movable, writtenTape,
    moveHead]

/-- The exact labelled execution of any fixed number of reader ticks. -/
theorem literal_exact_run (c : Config (State nt) Tape) (n : ℕ) :
    run program movable (literalArrows c n) c =
      some ((nextConfig^[n]) c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [literalArrows, run_cons, literalArrow_step]
      simpa using ih (nextConfig c)

/-- The physical one-hot block at the origin, with blank outside its width. -/
def oneHotTape (a : Fin nt) : Int → Tape := fun z =>
  if hz : 0 ≤ z ∧ z < (nt : Int) then
    tapeOfBit ((encodeOneHot a).get ⟨z.toNat, by
      rw [encodeOneHot_length]
      exact (Int.toNat_lt hz.1).mpr hz.2⟩)
  else blank

theorem oneHotTape_at (a : Fin nt) (i : Fin nt) :
    oneHotTape a i.1 = tapeOfBit ((encodeOneHot a).get ⟨i.1, by
      rw [encodeOneHot_length]
      exact i.isLt⟩) := by
  have hi : 0 ≤ (i.1 : Int) ∧ (i.1 : Int) < (nt : Int) := by omega
  simp [oneHotTape, hi]

/-- Decode one physical cell.  In particular, blank is not silently treated
as a zero bit. -/
def decodeTapeCell (x : Tape) : Option Bool :=
  if x = zero then some false
  else if x = one then some true
  else none

@[simp] theorem decodeTapeCell_zero : decodeTapeCell zero = some false := by
  simp [decodeTapeCell]

@[simp] theorem decodeTapeCell_one : decodeTapeCell one = some true := by
  simp [decodeTapeCell]

@[simp] theorem decodeTapeCell_blank : decodeTapeCell blank = none := by
  native_decide

@[simp] theorem decodeTapeCell_tapeOfBit (b : Bool) :
    decodeTapeCell (tapeOfBit b) = some b := by
  cases b <;> simp [tapeOfBit]

/-- Decode a physical block while retaining the fact that a blank is invalid. -/
def decodeTapeCells : List Tape → Option (List Bool)
  | [] => some []
  | x :: xs => do
      let b ← decodeTapeCell x
      let bits ← decodeTapeCells xs
      pure (b :: bits)

/-- The data-level result observed by the finite reader.  A blank or any
future non-bit physical letter is a hard rejection before one-hot decoding is
attempted. -/
def readResult (nt : ℕ) (cells : List Tape) : Option (Fin nt) := do
  let bits ← decodeTapeCells cells
  decodeOneHot nt bits

def oneHotCells (a : Fin nt) : List Tape :=
  (encodeOneHot a).map tapeOfBit

@[simp] theorem oneHotCells_length (a : Fin nt) :
    (oneHotCells a).length = nt := by
  simp [oneHotCells]

@[simp] theorem readResult_oneHotCells (a : Fin nt) :
    readResult nt (oneHotCells a) = some a := by
  have hdecode (bits : List Bool) :
      decodeTapeCells (bits.map tapeOfBit) = some bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp [decodeTapeCells, ih]
  unfold readResult oneHotCells
  rw [hdecode]
  simp

theorem decodeTapeCells_rejects_blank (pre suf : List Tape) :
    decodeTapeCells (pre ++ blank :: suf) = none := by
  induction pre with
  | nil => simp [decodeTapeCells, decodeTapeCell_blank]
  | cons x pre ih =>
      cases h : decodeTapeCell x with
      | none => simp [decodeTapeCells, h]
      | some b => simp [decodeTapeCells, h, ih]

theorem readResult_rejects_blank (nt : ℕ) (pre suf : List Tape) :
    readResult nt (pre ++ blank :: suf) = none := by
  unfold readResult
  rw [decodeTapeCells_rejects_blank]
  rfl

/-- A blank encountered while scanning enters the rejecting terminal state. -/
@[simp] theorem readerAction_blank (i : Fin nt) (seen : Option (Fin nt)) :
    (readerAction (.scan i seen) blank).target = .reject := by
  have hzero : blank ≠ zero := by native_decide
  have hone : blank ≠ one := by native_decide
  simp [readerAction, hzero, hone]

/-- A second one is rejected at the exact cell where it is observed. -/
@[simp] theorem readerAction_second_one (i a : Fin nt) :
    (readerAction (.scan i (some a)) one).target = .reject := by
  simp [readerAction]

end PakFixedPolyomino.ULogSourceOneHotReader
