import PakFixedPolyomino.ULogCounterPump

/-! Physical initialization inserts delimiter3 and returns to the counter.
No marker is assumed in the binary payload. All k right moves, both boundary
steps and k left moves are charged, including empty input. -/

namespace PakFixedPolyomino.ULogCounterPumpInitialization

open ULogCompiler ULogFiniteTapeZipperRun ULogCounterPump
open FiniteOneTapeSemantics (moveHead)

theorem zeros_snoc (n : Nat) (rest : List (Fin 4)) :
    List.replicate n (0 : Fin 4) ++ 0 :: rest =
      0 :: (List.replicate n 0 ++ rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons (0 : Fin 4)) ih

theorem initial_right_zero (head : Int) (left cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 2 left (0 :: cells)) =
      some (head + 1, fromCells 2 (0 :: left) cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem scan_zeros_run (n : Nat) (head : Int) (left : List (Fin 4)) :
    run program 2 (List.replicate n false) head (fromCells 2 left (List.replicate n 0)) =
      some (head + n, fromCells 2 (List.replicate n 0 ++ left) []) := by
  induction n generalizing head left with
  | zero => simp [run]
  | succ n ih =>
      have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
        simp [List.replicate_succ]
      rw [hw, run_append, List.replicate_succ, initial_right_zero]
      exact (ih (head + 1) (0 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.replicate_succ, zeros_snoc]

def returnStart (n : Nat) (rest : List (Fin 4)) : BoundedConfig 9 4 :=
  match n with
  | 0 => fromCells 8 [] (2 :: rest)
  | n + 1 => fromCells 8 (List.replicate n 0) (0 :: rest)

theorem marker_turn (n : Nat) (head : Int) :
    run program 2 [false] head (fromCells 2 (List.replicate n 0) []) =
      some (head - 1, returnStart n [3]) := by
  cases n <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded,
      moveHead, returnStart, List.replicate_succ]

theorem initial_return_zero (n : Nat) (head : Int) (rest : List (Fin 4)) :
    run program 2 [false] head (returnStart (n + 1) rest) =
      some (head - 1, returnStart n (0 :: rest)) := by
  cases n <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded,
      moveHead, returnStart, List.replicate_succ]

theorem return_zeros_run (n : Nat) (head : Int) (rest : List (Fin 4)) :
    run program 2 (List.replicate n false) head (returnStart n rest) =
      some (head - n, fromCells 8 [] (2 :: List.replicate n 0 ++ rest)) := by
  induction n generalizing head rest with
  | zero => simp [run, returnStart]
  | succ n ih =>
      have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
        simp [List.replicate_succ]
      rw [hw, run_append, initial_return_zero]
      exact (ih (head - 1) (0 :: rest)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.replicate_succ, zeros_snoc]

theorem initial_return_blank (head : Int) (cells : List (Fin 4)) :
    run program 2 [false] head (fromCells 8 [] (2 :: cells)) =
      some (head + 1, fromCells 5 [2] cells) := by
  cases cells <;>
    simp [run, program, action, fromCells, boundedHalted, applyBounded, moveHead]

theorem initialization_run (k : Nat) (head : Int) :
    run program 2 (List.replicate (2 * k + 2) false) head
      (fromCells 2 [] (List.replicate k 0)) =
      some (head, fromCells 5 [2] (List.replicate k 0 ++ [3])) := by
  have hw : List.replicate (2 * k + 2) false =
      List.replicate k false ++ [false] ++ List.replicate k false ++ [false] := by
    have ht : 2 * k + 2 = k + 1 + k + 1 := by omega
    simp [ht, List.replicate_add]
  have hs : run program 2 (List.replicate k false) head
      (fromCells 2 [] (List.replicate k 0)) =
      some (head + k, fromCells 2 (List.replicate k 0) []) := by
    simpa using scan_zeros_run k head []
  have hm : run program 2 (List.replicate k false ++ [false]) head
      (fromCells 2 [] (List.replicate k 0)) =
      some (head + k - 1, returnStart k [3]) := by
    rw [run_append, hs]
    exact marker_turn k (head + k)
  have hr : run program 2
      (List.replicate k false ++ [false] ++ List.replicate k false) head
      (fromCells 2 [] (List.replicate k 0)) =
      some (head - 1, fromCells 8 [] (2 :: List.replicate k 0 ++ [3])) := by
    rw [run_append, hm]
    exact (return_zeros_run k (head + k - 1) [3]).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · rfl
  rw [hw, run_append, hr]
  simpa only [Option.bind_some, Int.sub_add_cancel, List.cons_append] using
    initial_return_blank (head - 1) (List.replicate k 0 ++ [3])

def input (k : Nat) : List Bool := encodeInstance program (List.replicate k false)

theorem input_length (k : Nat) :
    (input k).length = (ULogBytecode.encodeProgram (compile program)).length + 2 * k + 1 := by
  simp [input, encodeInstance]
  omega

theorem initial_lift (k : Nat) :
    liftConfig program (fromCells 2 [] (List.replicate k 0)) =
      ULogSemantics.start (input k) := by
  have hi : boundedInitial (2 : Fin 9) (0 : Fin 4) 1 2 (List.replicate k false) =
      fromCells 2 [] (List.replicate k 0) := by
    cases k <;>
      simp [boundedInitial, boundedBit, fromCells, List.replicate_succ]
  have hl := liftConfig_boundedInitial program (2 : Fin 9) (0 : Fin 4) 1 2
    rfl rfl rfl rfl (List.replicate k false)
  rw [hi] at hl
  exact hl

theorem initialization_semantic_run (k : Nat) :
    semanticRun (ULogSemantics.start (input k)) (List.replicate (2 * k + 2) false) =
      some (liftConfig program (fromCells 5 [2] (List.replicate k 0 ++ [3]))) := by
  rw [← initial_lift, ← run_lift program (2 : Fin 4) rfl _ 0, initialization_run]
  rfl

end PakFixedPolyomino.ULogCounterPumpInitialization
