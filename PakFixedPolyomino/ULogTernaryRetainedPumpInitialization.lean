import PakFixedPolyomino.ULogTernaryRetainedCounterPump

/-! Actual compact ternary initialization. State 2 preserves each counter
zero RIGHT; the binary separator 1 is replaced by delimiter blank 2 and
LEFT into state 4; state 4 returns to the genuine left blank then RIGHT 5.
Source cells are unchanged. Includes k = 0 and empty source. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpInitialization

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open FiniteOneTapeSemantics (moveHead)

theorem zeros_snoc (n : Nat) (rest : List (Fin 3)) :
    List.replicate n (0 : Fin 3) ++ 0 :: rest =
      0 :: (List.replicate n 0 ++ rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons (0 : Fin 3)) ih

theorem cells_replicate_false (n : Nat) :
    cells (List.replicate n false) = List.replicate n 0 := by
  simp [cells, cell, List.map_replicate]

theorem init_right_zero (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 2 left (0 :: rest)) =
      some (head + 1, fromCells 2 (0 :: left) rest) := by
  cases rest <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem scan_zeros_run (n : Nat) (head : Int) (left rest : List (Fin 3)) :
    run program 2 (List.replicate n false) head
      (fromCells 2 left (List.replicate n 0 ++ rest)) =
        some (head + n, fromCells 2 (List.replicate n 0 ++ left) rest) := by
  induction n generalizing head left with
  | zero => simp [run]
  | succ n ih =>
    have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
      simp [List.replicate_succ]
    rw [hw, run_append, List.replicate_succ, List.cons_append, init_right_zero]
    exact (ih (head + 1) (0 :: left)).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · simp [zeros_snoc]

def returnStart (n : Nat) (rest : List (Fin 3)) : BoundedConfig 10 3 :=
  match n with
  | 0 => fromCells 4 [] (2 :: rest)
  | n + 1 => fromCells 4 (List.replicate n 0) (0 :: rest)

theorem separator_turn (n : Nat) (head : Int) (rest : List (Fin 3)) :
    run program 2 [false] head
      (fromCells 2 (List.replicate n 0) (1 :: rest)) =
        some (head - 1, returnStart n (2 :: rest)) := by
  cases n with
  | zero =>
      simp [run, program, fromCells, boundedHalted, applyBounded, moveHead,
        returnStart]
  | succ n =>
      simp [run, program, fromCells, boundedHalted, applyBounded, moveHead,
        returnStart, List.replicate_succ]

theorem return_zero_step (n : Nat) (head : Int) (rest : List (Fin 3)) :
    run program 2 [false] head (returnStart (n + 1) rest) =
      some (head - 1, returnStart n (0 :: rest)) := by
  cases n with
  | zero =>
      simp [run, program, fromCells, boundedHalted, applyBounded, moveHead,
        returnStart]
  | succ n =>
      simp [run, program, fromCells, boundedHalted, applyBounded, moveHead,
        returnStart, List.replicate_succ]

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

theorem return_blank (head : Int) (rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 4 [] (2 :: rest)) =
      some (head + 1, fromCells 5 [2] rest) := by
  cases rest <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem initialization_run (k : Nat) (source : List Bool) (head : Int) :
    run program 2 (List.replicate (2 * k + 2) false) head (initial k source) =
      some (head, fromCells 5 [2] (data (List.replicate k false) source 0)) := by
  have hw : List.replicate (2 * k + 2) false =
      List.replicate k false ++ [false] ++ List.replicate k false ++ [false] := by
    have ht : 2 * k + 2 = k + 1 + k + 1 := by omega
    simp [ht, List.replicate_add]
  have hs : run program 2 (List.replicate k false) head (initial k source) =
      some (head + k, fromCells 2 (List.replicate k 0) (1 :: cells source)) := by
    simpa [initial] using scan_zeros_run k head [] (1 :: cells source)
  have hm : run program 2 (List.replicate k false ++ [false]) head
      (initial k source) =
        some (head + k - 1, returnStart k (2 :: cells source)) := by
    rw [run_append, hs]
    exact separator_turn k (head + k) (cells source)
  have hr : run program 2
      (List.replicate k false ++ [false] ++ List.replicate k false) head
      (initial k source) =
        some (head - 1,
          fromCells 4 [] (2 :: List.replicate k 0 ++ 2 :: cells source)) := by
    rw [run_append, hm]
    exact (return_zeros_run k (head + k - 1) (2 :: cells source)).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · rfl
  have hdata : data (List.replicate k false) source 0 =
      List.replicate k 0 ++ 2 :: cells source := by
    simp [data, cells_replicate_false]
  rw [hw, run_append, hr, hdata]
  simpa only [Option.bind_some, Int.sub_add_cancel, List.cons_append] using
    return_blank (head - 1) (List.replicate k 0 ++ 2 :: cells source)

theorem initial_lift (k : Nat) (source : List Bool) :
    liftConfig program (initial k source) =
      ULogSemantics.start (input k source) := by
  have hmap :
      (sourceInput k source).map (boundedBit (0 : Fin 3) 1) =
        List.replicate k 0 ++ 1 :: cells source := by
    simp [sourceInput, boundedBit, cells, cell]
  have hi : boundedInitial (2 : Fin 10) (0 : Fin 3) 1 2 (sourceInput k source) =
      initial k source := by
    rw [initial, ← hmap]
    cases sourceInput k source <;> rfl
  have hl := liftConfig_boundedInitial program (2 : Fin 10) (0 : Fin 3) 1 2
    rfl rfl rfl rfl (sourceInput k source)
  rw [hi] at hl
  exact hl

end PakFixedPolyomino.ULogTernaryRetainedPumpInitialization
