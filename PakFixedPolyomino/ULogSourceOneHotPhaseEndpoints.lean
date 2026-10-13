import PakFixedPolyomino.ULogSourceOneHotPhysicalMacro
import PakFixedPolyomino.ULogSourceOneHotWriter
import Mathlib.Tactic

/-!
# Exact deterministic phase endpoints for the one-hot source compiler

These lemmas expose the physical head/tape effects of the deterministic
rewind, writer, and relocation phases.  They are independent of the unique
two-slot source choice and can therefore be composed without changing branch
multiplicity.
-/

namespace PakFixedPolyomino.ULogSourceOneHotPhaseEndpoints

open OneTapeTableau FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPhysicalStep ULogSourceOneHotPhysicalMacro

variable {ns nt : ℕ}

theorem config_ext {a b : Config (State ns nt) Tape}
    (hstate : a.state = b.state) (hhead : a.head = b.head)
    (htape : a.tape = b.tape) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem writtenTape_current (q : State ns nt) (tape : Int → Tape)
    (head : Int) :
    writtenTape ({ state := q, head := head, tape := tape } :
      Config (State ns nt) Tape) (tape head) = tape := by
  funext z
  by_cases hz : z = head
  · subst z
    simp [writtenTape]
  · simp [writtenTape, Function.update_of_ne hz]

def rewindStage (hnt : 0 < nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (n : ℕ) : State ns nt :=
  if hn : n < nt then .rewind q read slot a ⟨n, hn⟩
  else .writing a ⟨0, hnt⟩

@[simp] theorem rewindStage_zero (hnt : 0 < nt) (q : Fin ns) (read : Fin nt)
    (slot : Bool) (a : BoundedAction ns nt) :
    rewindStage hnt q read slot a 0 = .rewind q read slot a ⟨0, hnt⟩ := by
  simp [rewindStage, hnt]

@[simp] theorem rewindStage_terminal (hnt : 0 < nt) (q : Fin ns)
    (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt) :
    rewindStage hnt q read slot a nt = .writing a ⟨0, hnt⟩ := by
  simp [rewindStage]

def rewindExpected (hnt : 0 < nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) (n : ℕ) :
    Config (State ns nt) Tape :=
  { state := rewindStage hnt q read slot a n
    head := head - n
    tape := tape }

def rewindInitial (hnt : 0 < nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    Config (State ns nt) Tape :=
  { state := .rewind q read slot a ⟨0, hnt⟩, head := head, tape := tape }

theorem rewind_next_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) (hn : n < nt) :
    nextMicroConfig hnt logicalBlank
        (rewindExpected hnt q read slot a tape head n) =
      rewindExpected hnt q read slot a tape head (n + 1) := by
  have hstage : rewindStage hnt q read slot a n =
      .rewind q read slot a ⟨n, hn⟩ := by simp [rewindStage, hn]
  rw [show rewindExpected hnt q read slot a tape head n =
      { state := .rewind q read slot a ⟨n, hn⟩,
        head := head - n, tape := tape } by
      simp [rewindExpected, hstage]]
  unfold nextMicroConfig
  dsimp
  by_cases hlast : n + 1 = nt
  · apply config_ext <;>
      simp [microAction, hlast, rewindExpected, rewindStage, moveHead] <;> omega
  · have hnext : n + 1 < nt := by omega
    apply config_ext <;>
      simp [microAction, hlast, rewindExpected, rewindStage, hnext,
        moveHead] <;> omega

theorem iterate_rewind_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) (hn : n ≤ nt) :
    (nextMicroConfig hnt logicalBlank)^[n]
        (rewindInitial hnt q read slot a tape head) =
      rewindExpected hnt q read slot a tape head n := by
  induction n with
  | zero => simp [rewindInitial, rewindExpected, rewindStage_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact rewind_next_expected hnt logicalBlank q read slot a tape head n (by omega)

/-- Exactly `nt` rewind arrows restore the physical head to the beginning of
the focus block and enter the writer, without changing the tape. -/
theorem rewind_operational_terminal (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) :
    (nextMicroConfig hnt logicalBlank)^[nt]
        (rewindInitial hnt q read slot a tape head) =
      { state := .writing a ⟨0, hnt⟩,
        head := head - nt, tape := tape } := by
  rw [iterate_rewind_expected hnt logicalBlank q read slot a tape head nt le_rfl]
  simp [rewindExpected, rewindStage_terminal]

/-- Physical writer control after `n` literal writer ticks.  At the terminal
tick the integrated machine hands off directly to relocation instead of the
standalone writer's `done` state. -/
def writerStage (a : BoundedAction ns nt) (n : ℕ) : State ns nt :=
  if hn : n < nt then .writing a ⟨n, hn⟩
  else .relocate a ⟨0, Nat.zero_lt_succ _⟩

@[simp] theorem writerStage_zero (hnt : 0 < nt) (a : BoundedAction ns nt) :
    writerStage a 0 = .writing a ⟨0, hnt⟩ := by
  simp [writerStage, hnt]

@[simp] theorem writerStage_terminal (a : BoundedAction ns nt) :
    writerStage a nt = .relocate a ⟨0, Nat.zero_lt_succ _⟩ := by
  simp [writerStage]

/-- The integrated writer has exactly the standalone writer's tape prefix. -/
def writerExpected (a : BoundedAction ns nt) (tape : Int → Tape)
    (head : Int) (n : ℕ) : Config (State ns nt) Tape :=
  { state := writerStage a n
    head := head + n
    tape := ULogSourceOneHotWriter.writePrefix a.write head tape n }

def writerInitial (hnt : 0 < nt) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) : Config (State ns nt) Tape :=
  { state := .writing a ⟨0, hnt⟩, head := head, tape := tape }

theorem writer_next_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (n : ℕ) (hn : n < nt) :
    nextMicroConfig hnt logicalBlank (writerExpected a tape head n) =
      writerExpected a tape head (n + 1) := by
  have hstage : writerStage a n = .writing a ⟨n, hn⟩ := by
    simp [writerStage, hn]
  rw [show writerExpected a tape head n =
      { state := .writing a ⟨n, hn⟩,
        head := head + n,
        tape := ULogSourceOneHotWriter.writePrefix a.write head tape n } by
      simp [writerExpected, hstage]]
  unfold nextMicroConfig
  dsimp
  have hwrite : writtenTape (writerExpected a tape head n)
      (tapeOfBit ((ULogSourceOneHotBlocks.encodeOneHot a.write).get
        ⟨n, by simpa using hn⟩)) =
      ULogSourceOneHotWriter.writePrefix a.write head tape (n + 1) := by
    unfold writerExpected
    rw [ULogSourceOneHotWriter.writePrefix,
      ULogSourceOneHotWriter.targetCell_of_lt a.write n hn]
    rfl
  rw [show writerExpected a tape head n =
      { state := .writing a ⟨n, hn⟩,
        head := head + n,
        tape := ULogSourceOneHotWriter.writePrefix a.write head tape n } by
      simp [writerExpected, hstage]] at hwrite
  by_cases hlast : n + 1 = nt
  · have hlastInt : (n : Int) + 1 = nt := by exact_mod_cast hlast
    apply config_ext
    · simp [microAction, hlast, writerExpected, writerStage]
    · simp [microAction, hlast, writerExpected, writerStage, moveHead]
      omega
    · simpa [microAction, hlast, writerExpected, writerStage] using hwrite
  · have hnext : n + 1 < nt := by omega
    apply config_ext
    · simp [microAction, hlast, writerExpected, writerStage, hnext]
    · simp [microAction, hlast, writerExpected, writerStage, hnext, moveHead]
      push_cast
      ring
    · simpa [microAction, hlast, writerExpected, writerStage, hnext] using hwrite

theorem iterate_writer_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (n : ℕ) (hn : n ≤ nt) :
    (nextMicroConfig hnt logicalBlank)^[n] (writerInitial hnt a tape head) =
      writerExpected a tape head n := by
  induction n with
  | zero =>
      apply config_ext <;>
        simp [writerInitial, writerExpected, writerStage,
          ULogSourceOneHotWriter.writePrefix, hnt]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact writer_next_expected hnt logicalBlank a tape head n (by omega)

/-- Exactly `nt` integrated writer ticks write the target one-hot block,
advance to its right boundary, and enter relocation at offset zero. -/
theorem writer_operational_terminal (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    (nextMicroConfig hnt logicalBlank)^[nt] (writerInitial hnt a tape head) =
      { state := .relocate a ⟨0, Nat.zero_lt_succ _⟩,
        head := head + nt,
        tape := ULogSourceOneHotWriter.writePrefix a.write head tape nt } := by
  rw [iterate_writer_expected hnt logicalBlank a tape head nt le_rfl]
  simp [writerExpected, writerStage_terminal]

/-- The writer endpoint's physical focus is precisely the target one-hot
encoding supplied by the bounded action. -/
theorem writer_operational_terminal_cells (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ULogSourceOneHotWriter.blockCells
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (writerInitial hnt a tape head)).tape head nt =
      ULogSourceOneHotReader.oneHotCells a.write := by
  rw [writer_operational_terminal]
  exact ULogSourceOneHotWriter.exact_block_cells a.write head tape

/-- No cell outside the rewritten target block changes during the writer
phase. -/
theorem writer_operational_terminal_outside (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head z : Int)
    (hz : z < head ∨ head + (nt : Int) ≤ z) :
    ((nextMicroConfig hnt logicalBlank)^[nt]
      (writerInitial hnt a tape head)).tape z = tape z := by
  rw [writer_operational_terminal]
  exact ULogSourceOneHotWriter.writePrefix_outside a.write head tape nt le_rfl z hz

/-- The relocation distance always fits the finite relocation counter. -/
theorem relocationDistance_le (a : BoundedAction ns nt) :
    relocationDistance a.move nt ≤ 2 * nt := by
  cases a.move <;> simp [relocationDistance] <;> omega

def relocateIndex (a : BoundedAction ns nt) (n : ℕ)
    (hn : n ≤ relocationDistance a.move nt) : Fin (2 * nt + 1) :=
  ⟨n, by
    have hbound := relocationDistance_le (nt := nt) a
    omega⟩

/-- The relocation configuration after `n` genuine left moves. -/
def relocateExpected (a : BoundedAction ns nt) (tape : Int → Tape)
    (head : Int) (n : ℕ) (hn : n ≤ relocationDistance a.move nt) :
    Config (State ns nt) Tape :=
  { state := .relocate a (relocateIndex a n hn)
    head := head - n
    tape := tape }

def relocateInitial (a : BoundedAction ns nt) (tape : Int → Tape)
    (head : Int) : Config (State ns nt) Tape :=
  relocateExpected a tape head 0 (Nat.zero_le _)

theorem relocate_next_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (n : ℕ) (hn : n ≤ relocationDistance a.move nt)
    (hleft : n < relocationDistance a.move nt) :
    nextMicroConfig hnt logicalBlank (relocateExpected a tape head n hn) =
      relocateExpected a tape head (n + 1) (by omega) := by
  have hdone : ¬ relocationDistance a.move nt ≤ n := by omega
  unfold nextMicroConfig
  dsimp
  apply config_ext
  · simp [relocateExpected, relocateIndex, microAction, hdone]
  · simp [relocateExpected, relocateIndex, microAction, hdone, moveHead]
    push_cast
    ring
  · simpa [relocateExpected, relocateIndex, microAction, hdone] using
      (writtenTape_current (State.relocate a (relocateIndex a n hn))
        tape (head - n))

theorem iterate_relocate_expected (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (n : ℕ) (hn : n ≤ relocationDistance a.move nt) :
    (nextMicroConfig hnt logicalBlank)^[n] (relocateInitial a tape head) =
      relocateExpected a tape head n hn := by
  induction n with
  | zero =>
      apply config_ext <;>
        simp [relocateInitial, relocateExpected]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact relocate_next_expected hnt logicalBlank a tape head n (by omega) (by omega)

/-- After exactly the prescribed distance, relocation has made only left
moves, preserving the tape and landing at its terminal counter value. -/
theorem relocate_left_terminal (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    (nextMicroConfig hnt logicalBlank)^[relocationDistance a.move nt]
        (relocateInitial a tape head) =
      relocateExpected a tape head (relocationDistance a.move nt) le_rfl := by
  exact iterate_relocate_expected hnt logicalBlank a tape head
    (relocationDistance a.move nt) le_rfl

/-- The terminal relocation tick is a stay move and hands off into the next
source-block reader at the relocated head. -/
theorem relocate_handoff (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    nextMicroConfig hnt logicalBlank
      (relocateExpected a tape head (relocationDistance a.move nt) le_rfl) =
      { state := .reading a.target (initialReaderState hnt),
        head := head - relocationDistance a.move nt,
        tape := tape } := by
  unfold nextMicroConfig
  dsimp
  apply config_ext
  · simp [relocateExpected, relocateIndex, microAction]
  · simp [relocateExpected, relocateIndex, microAction, moveHead]
  · simpa [relocateExpected, relocateIndex, microAction] using
      (writtenTape_current
        (State.relocate a
          (relocateIndex a (relocationDistance a.move nt) le_rfl))
        tape (head - relocationDistance a.move nt))

/-- Relocation performs precisely `relocationDistance` left moves followed by
one stay handoff, leaving the rewritten tape untouched. -/
theorem relocate_operational_terminal (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    (nextMicroConfig hnt logicalBlank)^[relocationDistance a.move nt + 1]
        (relocateInitial a tape head) =
      { state := .reading a.target (initialReaderState hnt),
        head := head - relocationDistance a.move nt,
        tape := tape } := by
  rw [Function.iterate_succ_apply', relocate_left_terminal]
  exact relocate_handoff hnt logicalBlank a tape head

end PakFixedPolyomino.ULogSourceOneHotPhaseEndpoints
