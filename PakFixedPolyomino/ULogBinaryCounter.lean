import PakFixedPolyomino.ULogFiniteProgramZipperRunBridge

/-! A fixed six-state three-letter binary counter. The control table has no
width parameter. State2 enters ready5; ready5 marks an increment attempt;
carry3 flips low ones and seeks the first zero; return4 seeks the left blank.
Overflow enters accepting0. Only the false slot is occupied. The execution
lemmas below charge each actual one-cell transition. Exponential iteration,
compact window construction and true source deadline normalization remain
separate obligations. -/

namespace PakFixedPolyomino.ULogBinaryCounter

open ULogCompiler ULogFiniteProgramZipperRunBridge OneTapeTableau

def action (q : Fin 6) (read : Fin 3) : Option (BoundedAction 6 3) :=
  match q.val with
  | 2 => some ⟨read, 5, .stay⟩
  | 3 =>
      if read = 0 then some ⟨1, 4, .left⟩
      else if read = 1 then some ⟨0, 3, .right⟩
      else some ⟨read, 0, .stay⟩
  | 4 =>
      if read = 2 then some ⟨read, 5, .right⟩
      else some ⟨read, 4, .left⟩
  | 5 => some ⟨read, 3, .stay⟩
  | _ => none

def program : BoundedProgram 6 3 where
  rule q read slot := if slot then none else action q read

@[simp] theorem rule_true (q : Fin 6) (read : Fin 3) :
    program.rule q read true = none := rfl

theorem terminal_table : TerminalTable program := by
  intro q read slot hq
  have h : q.val = 0 ∨ q.val = 1 := by omega
  rcases h with h | h <;> simp [program, action, h]

def fromCells (q : Fin 6) (left cells : List (Fin 3)) : BoundedConfig 6 3 :=
  ⟨q, left, cells.headD 2, cells.tail⟩

@[simp] theorem fromCells_cons (q : Fin 6) (left : List (Fin 3))
    (x : Fin 3) (cells : List (Fin 3)) :
    fromCells q left (x :: cells) = ⟨q, left, x, cells⟩ := rfl

theorem step_carry_one (left cells : List (Fin 3)) :
    boundedStepSlot program (2 : Fin 3) false (fromCells 3 left (1 :: cells)) =
      some (fromCells 3 (0 :: left) cells) := by
  cases cells <;>
    simp [boundedStepSlot, boundedHalted, program, action, applyBounded, fromCells]

theorem carry_one_run (head : Int) (left cells : List (Fin 3)) :
    zipperSlotRun program [false] head (fromCells 3 left (1 :: cells)) =
      some (head + 1, fromCells 3 (0 :: left) cells) := by
  cases cells <;>
    simp [zipperSlotRun, boundedHalted, program, action, applyBounded, fromCells,
      FiniteOneTapeSemantics.moveHead]

/-- Flip exactly the low `n` one cells; the word contains exactly `n`
executed transitions. The following scanned cell remains untouched. -/
theorem carry_ones_run (n : Nat) (head : Int) (left cells : List (Fin 3)) :
    zipperSlotRun program (List.replicate n false) head
        (fromCells 3 left (List.replicate n (1 : Fin 3) ++ cells)) =
      some (head + n,
        fromCells 3 (List.replicate n (0 : Fin 3) ++ left) cells) := by
  induction n generalizing head left with
  | zero => simp [zipperSlotRun]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      change zipperSlotRun program (false :: List.replicate n false) head
        (fromCells 3 left (1 :: (List.replicate n 1 ++ cells))) = _
      have hstep :
          zipperSlotRun program (false :: List.replicate n false) head
              (fromCells 3 left (1 :: (List.replicate n 1 ++ cells))) =
            zipperSlotRun program (List.replicate n false) (head + 1)
              (fromCells 3 (0 :: left) (List.replicate n 1 ++ cells)) := by
        cases hcells : List.replicate n (1 : Fin 3) ++ cells <;>
          simp [zipperSlotRun, boundedHalted, program, action, applyBounded,
            fromCells, hcells, FiniteOneTapeSemantics.moveHead]
      rw [hstep, ih]
      apply congrArg some
      apply Prod.ext
      · push_cast; ring
      · have hlist : List.replicate n (0 : Fin 3) ++ 0 :: left =
            0 :: (List.replicate n (0 : Fin 3) ++ left) := by
          clear ih hstep
          induction n with
          | zero => rfl
          | succ n ih =>
              simpa [List.replicate_succ] using congrArg (List.cons (0 : Fin 3)) ih
        rw [hlist]

theorem carry_overflow (head : Int) (left : List (Fin 3)) :
    zipperSlotRun program [false] head (fromCells 3 left []) =
      some (head, fromCells 0 left []) := by
  simp [zipperSlotRun, boundedHalted, program, action, applyBounded, fromCells,
    FiniteOneTapeSemantics.moveHead]

theorem ready_attempt (head : Int) (left cells : List (Fin 3)) :
    zipperSlotRun program [false] head (fromCells 5 left cells) =
      some (head, fromCells 3 left cells) := by
  simp [zipperSlotRun, boundedHalted, program, action, applyBounded, fromCells,
    FiniteOneTapeSemantics.moveHead]

end PakFixedPolyomino.ULogBinaryCounter
