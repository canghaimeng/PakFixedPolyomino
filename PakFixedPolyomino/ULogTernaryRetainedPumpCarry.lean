import PakFixedPolyomino.ULogTernaryRetainedCounterPump

/-! Actual ternary carry/return and overflow equations. Counter0/1 and
internal separatorblank2 are distinguished by the literal control table.
The source suffix is arbitrary and never read during this macro. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpCarry

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open FiniteOneTapeSemantics (moveHead)

theorem zeros_snoc (n : Nat) (rest : List (Fin 3)) :
    List.replicate n (0 : Fin 3) ++ 0 :: rest =
      0 :: (List.replicate n 0 ++ rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons (0 : Fin 3)) ih

theorem carry_one (head : Int) (left cells : List (Fin 3)) :
    run program 2 [false] head (fromCells 3 left (1 :: cells)) =
      some (head + 1, fromCells 3 (0 :: left) cells) := by
  cases cells <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem carry_flip_zero (head : Int) (a : Fin 3) (left cells : List (Fin 3)) :
    run program 2 [false] head (fromCells 3 (a :: left) (0 :: cells)) =
      some (head - 1, fromCells 4 left (a :: 1 :: cells)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem carry_blank_accept (head : Int) (left cells : List (Fin 3)) :
    run program 2 [false] head (fromCells 3 left (2 :: cells)) =
      some (head, fromCells 0 left (2 :: cells)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem counter_return_left (head : Int) (a b : Fin 3)
    (left cells : List (Fin 3)) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 4 (b :: left) (a :: cells)) =
      some (head - 1, fromCells 4 left (b :: a :: cells)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem counter_return_blank (head : Int) (cells : List (Fin 3)) :
    run program 2 [false] head (fromCells 4 [] (2 :: cells)) =
      some (head + 1, fromCells 5 [2] cells) := by
  cases cells <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]


theorem carry_ones_run (n : Nat) (head : Int) (left cells : List (Fin 3)) :
    run program 2 (List.replicate n false) head
      (fromCells 3 left (List.replicate n 1 ++ cells)) =
      some (head + n, fromCells 3 (List.replicate n 0 ++ left) cells) := by
  induction n generalizing head left with
  | zero => simp [run]
  | succ n ih =>
      have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
        simp [List.replicate_succ]
      rw [hw, run_append, List.replicate_succ, List.cons_append, carry_one]
      exact (ih (head + 1) (0 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.replicate_succ, zeros_snoc]

def returnStart (n : Nat) (rest : List (Fin 3)) : BoundedConfig 10 3 :=
  match n with
  | 0 => fromCells 4 [] (2 :: rest)
  | n + 1 => fromCells 4 (List.replicate n 0 ++ [2]) (0 :: rest)

theorem carry_flip_sentinel (n : Nat) (head : Int) (cells : List (Fin 3)) :
    run program 2 [false] head
      (fromCells 3 (List.replicate n 0 ++ [2]) (0 :: cells)) =
      some (head - 1, returnStart n (1 :: cells)) := by
  cases n with
  | zero => simpa [returnStart] using carry_flip_zero head 2 [] cells
  | succ n =>
      simpa [returnStart, List.replicate_succ] using
        carry_flip_zero head 0 (List.replicate n 0 ++ [2]) cells

theorem return_zero_step (n : Nat) (head : Int) (rest : List (Fin 3)) :
    run program 2 [false] head (returnStart (n + 1) rest) =
      some (head - 1, returnStart n (0 :: rest)) := by
  cases n with
  | zero => simpa [returnStart] using counter_return_left head 0 2 [] rest (by decide)
  | succ n =>
      simpa [returnStart, List.replicate_succ] using
        counter_return_left head 0 0 (List.replicate n 0 ++ [2]) rest (by decide)

theorem return_zeros_run (n : Nat) (head : Int) (rest : List (Fin 3)) :
    run program 2 (List.replicate n false) head (returnStart n rest) =
      some (head - n, fromCells 4 [] (2 :: List.replicate n 0 ++ rest)) := by
  induction n generalizing head rest with
  | zero => simp [run, returnStart]
  | succ n ih =>
      have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
        simp [List.replicate_succ]
      rw [hw, run_append, return_zero_step]
      exact (ih (head - 1) (0 :: rest)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.replicate_succ, zeros_snoc]

theorem increment_return (n : Nat) (head : Int) (tail : List (Fin 3)) :
    run program 2 (List.replicate (2 * n + 2) false) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head, fromCells 5 [2] (List.replicate n 0 ++ 1 :: tail)) := by
  have hw : List.replicate (2 * n + 2) false =
      List.replicate n false ++ [false] ++ List.replicate n false ++ [false] := by
    have ht : 2 * n + 2 = n + 1 + n + 1 := by omega
    simp [ht, List.replicate_add]
  have hc := carry_ones_run n head [2] (0 :: tail)
  have hf : run program 2 (List.replicate n false ++ [false]) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head + n - 1, returnStart n (1 :: tail)) := by
    rw [run_append, hc]
    exact carry_flip_sentinel n (head + n) tail
  have hr : run program 2
      (List.replicate n false ++ [false] ++ List.replicate n false) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head - 1, fromCells 4 [] (2 :: List.replicate n 0 ++ 1 :: tail)) := by
    rw [run_append, hf]
    exact (return_zeros_run n (head + n - 1) (1 :: tail)).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · rfl
  rw [hw, run_append, hr]
  simpa only [Option.bind_some, Int.sub_add_cancel, List.cons_append] using
    counter_return_blank (head - 1) (List.replicate n 0 ++ 1 :: tail)

theorem overflow_accept (k : Nat) (head : Int) (tail : List (Fin 3)) :
    run program 2 (List.replicate (k + 1) false) head
      (fromCells 3 [2] (List.replicate k 1 ++ 2 :: tail)) =
      some (head + k, fromCells 0 (List.replicate k 0 ++ [2]) (2 :: tail)) := by
  rw [List.replicate_add, run_append, carry_ones_run]
  exact carry_blank_accept (head + k) (List.replicate k 0 ++ [2]) tail


end PakFixedPolyomino.ULogTernaryRetainedPumpCarry
