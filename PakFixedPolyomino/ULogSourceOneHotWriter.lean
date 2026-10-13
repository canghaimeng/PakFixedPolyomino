import PakFixedPolyomino.ULogSourceOneHotReader
import Mathlib.Tactic

/-!
# Finite one-tape writer for fixed-width one-hot source blocks

The writer is the companion of `ULogSourceOneHotReader`.  Its target symbol
is carried in the finite control, and one slot-zero transition is taken for
each physical cell of the fixed-width block.  In particular, it never obtains
any branching from the tape contents it overwrites.
-/

namespace PakFixedPolyomino.ULogSourceOneHotWriter

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogSourceOneHotBlocks

abbrev Tape := Fin 3
abbrev zero : Tape := ULogSourceOneHotReader.zero
abbrev one : Tape := ULogSourceOneHotReader.one
abbrev blank : Tape := ULogSourceOneHotReader.blank
abbrev tapeOfBit : Bool → Tape := ULogSourceOneHotReader.tapeOfBit

/-- A writing state contains both the desired logical symbol and the physical
cell currently being written. -/
inductive State (nt : ℕ) where
  | write : Fin nt → Fin nt → State nt
  | done : Fin nt → State nt
  deriving DecidableEq, Fintype, Repr

variable {nt : ℕ}

/-- The letter required at a physical offset.  The out-of-range branch makes
this total; all execution theorems below use it only below `nt`. -/
def targetCell (a : Fin nt) (i : ℕ) : Tape :=
  if hi : i < nt then
    tapeOfBit ((encodeOneHot a).get ⟨i, by simpa using hi⟩)
  else blank

@[simp] theorem targetCell_of_lt (a : Fin nt) (i : ℕ) (hi : i < nt) :
    targetCell a i = tapeOfBit ((encodeOneHot a).get ⟨i, by simpa using hi⟩) := by
  simp [targetCell, hi]

/-- The control state after `i` writer ticks. -/
def stateAt (a : Fin nt) (i : ℕ) : State nt :=
  if hi : i < nt then .write a ⟨i, hi⟩ else .done a

/-- Advance a writing state.  The final physical cell enters `done`, while
the head still takes its mandatory right move to the next block boundary. -/
def advance (a : Fin nt) (i : Fin nt) : State nt := stateAt a (i.1 + 1)

/-- The action ignores the old letter and writes the letter determined by the
target held in control. -/
def writerAction : State nt → Tape → Action (State nt) Tape
  | .write a i, _ => ⟨targetCell a i.1, advance a i, .right⟩
  | .done a, x => ⟨x, .done a, .stay⟩

def writerStep (q : State nt) (x : Tape) : Option (Action (State nt) Tape) :=
  some (writerAction q x)

def program : Program (State nt) Tape := deterministic writerStep

def movable : Tape → Bool := fun _ => true

@[simp] theorem writer_slot_one_empty (q : State nt) (x : Tape) :
    program.rule q x 1 = none := by rfl

@[simp] theorem writer_slot_zero (q : State nt) (x : Tape) :
    program.rule q x 0 = some (writerAction q x) := by rfl

/-- The only occupied literal arrow at a source pair. -/
def literalArrow (q : State nt) (x : Tape) : Arrow (program (nt := nt)) :=
  ⟨((q, x), 0), by simp [program, deterministic, writerStep]⟩

@[simp] theorem literalArrow_source (q : State nt) (x : Tape) :
    (literalArrow q x).1.1.1 = q := rfl

@[simp] theorem literalArrow_read (q : State nt) (x : Tape) :
    (literalArrow q x).1.1.2 = x := rfl

@[simp] theorem actionOf_literalArrow (q : State nt) (x : Tape) :
    actionOf program (literalArrow q x) = writerAction q x := by
  simp [literalArrow, actionOf, program, deterministic, writerStep]

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

/-- Write the first `n` cells of a block, from left to right. -/
def writePrefix (a : Fin nt) (head : Int) (tape : Int → Tape) : ℕ → Int → Tape
  | 0 => tape
  | n + 1 => Function.update (writePrefix a head tape n) (head + n)
      (targetCell a n)

theorem writePrefix_at (a : Fin nt) (head : Int) (tape : Int → Tape)
    (n i : ℕ) (hi : i < n) :
    writePrefix a head tape n (head + i) = targetCell a i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        simp [writePrefix]
      · have hin' : i < n := by omega
        have hpos : (head + i : Int) ≠ head + n := by
          intro h
          apply hin
          omega
        rw [writePrefix, Function.update_of_ne hpos]
        exact ih i hin'

theorem writePrefix_outside (a : Fin nt) (head : Int) (tape : Int → Tape)
    (n : ℕ) (hn : n ≤ nt) (z : Int)
    (hz : z < head ∨ head + (nt : Int) ≤ z) :
    writePrefix a head tape n z = tape z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      have hn' : n ≤ nt := by omega
      have hlt : n < nt := by omega
      have hpos : z ≠ head + n := by
        rcases hz with hz | hz <;> intro h <;> subst z <;> omega
      rw [writePrefix, Function.update_of_ne hpos]
      exact ih hn' z hz

/-- The configuration obtained after a prescribed number of physical writer
ticks.  It is defined for all `n`; only `n ≤ nt` is used operationally. -/
def expectedConfig (a : Fin nt) (head : Int) (tape : Int → Tape) (n : ℕ) :
    Config (State nt) Tape :=
  { state := stateAt a n
    head := head + n
    tape := writePrefix a head tape n }

/-- The writer entry configuration.  Positive width is needed to name its
first finite physical offset. -/
def initialConfig (a : Fin nt) (hnt : 0 < nt) (tape : Int → Tape)
    (head : Int := 0) : Config (State nt) Tape :=
  { state := .write a ⟨0, hnt⟩, head := head, tape := tape }

def nextConfig (c : Config (State nt) Tape) : Config (State nt) Tape :=
  let x := c.tape c.head
  let act := writerAction c.state x
  { state := act.target
    head := moveHead act.move c.head
    tape := writtenTape c act.write }

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
    deterministic, writerStep, transition, nextConfig, movable, writtenTape,
    moveHead]

theorem literal_exact_run (c : Config (State nt) Tape) (n : ℕ) :
    run program movable (literalArrows c n) c =
      some ((nextConfig^[n]) c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [literalArrows, run_cons, literalArrow_step]
      simpa using ih (nextConfig c)

theorem nextConfig_expected (a : Fin nt) (head : Int) (tape : Int → Tape)
    (n : ℕ) (hn : n < nt) :
    nextConfig (expectedConfig a head tape n) =
      expectedConfig a head tape (n + 1) := by
  simp [nextConfig, expectedConfig, writerAction, stateAt, advance, writePrefix,
    targetCell, hn, moveHead, writtenTape]
  ring

theorem iterate_nextConfig_initial (a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) (hn : n ≤ nt) :
    (nextConfig^[n]) (initialConfig a hnt tape head) =
      expectedConfig a head tape n := by
  induction n with
  | zero => simp [initialConfig, expectedConfig, stateAt, writePrefix, hnt]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact nextConfig_expected a head tape n (by omega)

/-- Literal exact block execution: precisely `nt` occupied slot-zero arrows
overwrite the focus block and leave the head at its next boundary. -/
theorem literal_exact_block_run (a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int := 0) :
    run program movable (literalArrows (initialConfig a hnt tape head) nt)
      (initialConfig a hnt tape head) =
      some (expectedConfig a head tape nt) := by
  rw [literal_exact_run, iterate_nextConfig_initial a hnt tape head nt le_rfl]

@[simp] theorem exact_block_state (a : Fin nt) (head : Int) (tape : Int → Tape) :
    (expectedConfig a head tape nt).state = .done a := by
  simp [expectedConfig, stateAt]

@[simp] theorem exact_block_head (a : Fin nt) (head : Int) (tape : Int → Tape) :
    (expectedConfig a head tape nt).head = head + nt := rfl

/-- Each cell of the output block is exactly the corresponding encoded bit. -/
theorem exact_block_cell (a : Fin nt) (head : Int) (tape : Int → Tape)
    (i : Fin nt) :
    (expectedConfig a head tape nt).tape (head + (i.val : Int)) =
      targetCell a i.val := by
  change writePrefix a head tape nt (head + (i.val : Int)) = _
  rw [writePrefix_at a head tape nt i.val i.isLt]

/-- No tape cell outside the occupied width is changed. -/
theorem exact_block_outside (a : Fin nt) (head z : Int) (tape : Int → Tape)
    (hz : z < head ∨ head + (nt : Int) ≤ z) :
    (expectedConfig a head tape nt).tape z = tape z := by
  exact writePrefix_outside a head tape nt le_rfl z hz

/-- A data-level view of a physical block, useful at the reader/writer
boundary. -/
def blockCells (tape : Int → Tape) (head : Int) (nt : ℕ) : List Tape :=
  List.ofFn fun i : Fin nt => tape (head + i.1)

theorem exact_block_cells (a : Fin nt) (head : Int) (tape : Int → Tape) :
    blockCells (expectedConfig a head tape nt).tape head nt =
      ULogSourceOneHotReader.oneHotCells a := by
  apply List.ext_get
  · simp [blockCells, ULogSourceOneHotReader.oneHotCells]
  · intro i hi h'i
    simp only [blockCells, List.get_ofFn]
    have hbound : i < nt := by
      simpa [blockCells] using hi
    have hcell := exact_block_cell a head tape ⟨i, hbound⟩
    rw [targetCell_of_lt a i hbound] at hcell
    simpa [ULogSourceOneHotReader.oneHotCells] using hcell

/-- The reader validates an encoded logical focus, and the deterministic
writer then replaces that focus by its requested target block. -/
theorem read_then_write_focus (source target : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hfocus : blockCells tape head nt = ULogSourceOneHotReader.oneHotCells source) :
    ULogSourceOneHotReader.readResult nt (blockCells tape head nt) = some source ∧
      run program movable (literalArrows (initialConfig target hnt tape head) nt)
        (initialConfig target hnt tape head) =
          some (expectedConfig target head tape nt) ∧
      blockCells (expectedConfig target head tape nt).tape head nt =
        ULogSourceOneHotReader.oneHotCells target := by
  rw [hfocus]
  exact ⟨ULogSourceOneHotReader.readResult_oneHotCells source,
    literal_exact_block_run target hnt tape head,
    exact_block_cells target head tape⟩

/-- Every successful `nt`-tick execution has the literal slot-zero path and
the exact output configuration.  Thus the read/write boundary contributes no
hidden labelled-path multiplicity. -/
theorem successful_run_unique (c : Config (State nt) Tape) (n : ℕ)
    (as : List (Arrow program)) (out : Config (State nt) Tape)
    (hlen : as.length = n) (hrun : run program movable as c = some out) :
    as = literalArrows c n ∧ out = (nextConfig^[n]) c := by
  induction n generalizing c as out with
  | zero =>
      have has : as = [] := List.eq_nil_of_length_eq_zero hlen
      subst as
      simp at hrun
      subst out
      simp [literalArrows]
  | succ n ih =>
      cases as with
      | nil => simp at hlen
      | cons arrow tail =>
          simp only [List.length_cons] at hlen
          simp only [run_cons] at hrun
          cases hstep : step program movable c arrow with
          | none => simp [hstep] at hrun
          | some c' =>
              rw [hstep] at hrun
              have hsource := step_some_forces_source program movable c c' arrow hstep
              have harrow : arrow = literalArrow c.state (c.tape c.head) :=
                occupied_slot_unique c.state (c.tape c.head) arrow hsource.1.symm
                  hsource.2.symm
              subst arrow
              rw [literalArrow_step] at hstep
              have hc' : c' = nextConfig c := Option.some.inj hstep.symm
              subst c'
              have htailLength : tail.length = n := by omega
              obtain ⟨htail, hout⟩ := ih (nextConfig c) tail out htailLength hrun
              constructor
              · simp [literalArrows, htail]
              · rw [hout, Function.iterate_succ_apply]

theorem successful_block_run_unique (a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (as : List (Arrow program))
    (out : Config (State nt) Tape)
    (hrun : run program movable as (initialConfig a hnt tape head) = some out)
    (hlen : as.length = nt) :
    as = literalArrows (initialConfig a hnt tape head) nt ∧
      out = expectedConfig a head tape nt := by
  obtain ⟨harrows, hout⟩ := successful_run_unique
    (initialConfig a hnt tape head) nt as out hlen hrun
  exact ⟨harrows, hout.trans (iterate_nextConfig_initial a hnt tape head nt le_rfl)⟩

end PakFixedPolyomino.ULogSourceOneHotWriter
