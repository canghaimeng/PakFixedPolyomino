import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! A fixed finite-control candidate for compact window generation. It
appends one genuine zero cell before each binary increment attempt. The
counter and output are separated by delimiter3, inserted during actual
initialization. The table depends on neither width nor generated length.
Only local transitions are proved here; the full exponential output run,
prefix bounds and source-window specialization are separate obligations. -/

namespace PakFixedPolyomino.ULogCounterPump

open ULogCompiler ULogFiniteTapeZipperRun
open FiniteOneTapeSemantics (moveHead)

def action (q : Fin 9) (read : Fin 4) : Option (BoundedAction 9 4) :=
  if q.val = 2 then
    if read = 2 then some ⟨3, 8, .left⟩ else some ⟨read, 2, .right⟩
  else if q.val = 8 then
    if read = 2 then some ⟨2, 5, .right⟩ else some ⟨read, 8, .left⟩
  else if q.val = 5 then some ⟨read, 6, .stay⟩
  else if q.val = 6 then
    if read = 2 then some ⟨0, 7, .left⟩ else some ⟨read, 6, .right⟩
  else if q.val = 7 then
    if read = 2 then some ⟨2, 3, .right⟩ else some ⟨read, 7, .left⟩
  else if q.val = 3 then
    if read = 0 then some ⟨1, 4, .left⟩
    else if read = 1 then some ⟨0, 3, .right⟩
    else if read = 3 then some ⟨3, 0, .stay⟩ else none
  else if q.val = 4 then
    if read = 2 then some ⟨2, 5, .right⟩ else some ⟨read, 4, .left⟩
  else none

def program : BoundedProgram 9 4 where
  rule := fun q read slot => if slot then none else action q read

theorem rule_true (q : Fin 9) (read : Fin 4) : program.rule q read true = none := rfl

theorem terminal_rule (q : Fin 9) (read : Fin 4) (slot : Bool)
    (hq : q.val < 2) : program.rule q read slot = none := by
  have h2 : q.val ≠ 2 := by omega
  have h3 : q.val ≠ 3 := by omega
  have h4 : q.val ≠ 4 := by omega
  have h5 : q.val ≠ 5 := by omega
  have h6 : q.val ≠ 6 := by omega
  have h7 : q.val ≠ 7 := by omega
  have h8 : q.val ≠ 8 := by omega
  simp [program, action, h2, h3, h4, h5, h6, h7, h8]

def fromCells (q : Fin 9) (left cells : List (Fin 4)) : BoundedConfig 9 4 :=
  ⟨q, left, cells.headD 2, cells.tail⟩

theorem start_append (head : Int) (left cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 5 left cells) =
      some (head, fromCells 6 left cells) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem append_right (head : Int) (left cells : List (Fin 4))
    (a : Fin 4) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 6 left (a :: cells)) =
      some (head + 1, fromCells 6 (a :: left) cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem append_write_turn (head : Int) (a : Fin 4) (left : List (Fin 4)) :
    run program 2 [false] head (fromCells 6 (a :: left) []) =
      some (head - 1, fromCells 7 left [a, 0]) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem pump_return_left (head : Int) (left cells : List (Fin 4))
    (a b : Fin 4) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 7 (b :: left) (a :: cells)) =
      some (head - 1, fromCells 7 left (b :: a :: cells)) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem pump_return_blank (head : Int) (cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 7 [] (2 :: cells)) =
      some (head + 1, fromCells 3 [2] cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem carry_one (head : Int) (left cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 3 left (1 :: cells)) =
      some (head + 1, fromCells 3 (0 :: left) cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem carry_flip_zero (head : Int) (a : Fin 4) (left cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 3 (a :: left) (0 :: cells)) =
      some (head - 1, fromCells 4 left (a :: 1 :: cells)) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem carry_delimiter_accept (head : Int) (left cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 3 left (3 :: cells)) =
      some (head, fromCells 0 left (3 :: cells)) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem counter_return_left (head : Int) (a b : Fin 4)
    (left cells : List (Fin 4)) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 4 (b :: left) (a :: cells)) =
      some (head - 1, fromCells 4 left (b :: a :: cells)) := by
  simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem counter_return_blank (head : Int) (cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 4 [] (2 :: cells)) =
      some (head + 1, fromCells 5 [2] cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

end PakFixedPolyomino.ULogCounterPump
