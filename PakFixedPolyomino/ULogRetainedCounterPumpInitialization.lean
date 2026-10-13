import PakFixedPolyomino.ULogRetainedCounterPump
import PakFixedPolyomino.ULogCounterPumpInitialization
import PakFixedPolyomino.ULogCounterPumpBinarySteps

/-! Actual compact binary initialization. The first one after k zeros is
the separator, replaced by delimiter3; the arbitrary source after it is
unchanged. No delimiter is supplied as an input-tape oracle. -/

namespace PakFixedPolyomino.ULogRetainedCounterPumpInitialization

open ULogCompiler ULogFiniteTapeZipperRun ULogCounterPump
open ULogCounterPumpBinarySteps (cells cell cells_replicate)
open ULogCounterPumpInitialization (returnStart zeros_snoc)
open FiniteOneTapeSemantics (moveHead)

theorem initial_right_zero (head : Int) (left rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 [false] head (fromCells 2 left (0 :: rest)) =
      some (head + 1, fromCells 2 (0 :: left) rest) := by
  cases rest <;>
    simp [run, ULogRetainedCounterPump.program, fromCells, boundedHalted, applyBounded, moveHead]

theorem scan_zeros_run (n : Nat) (head : Int) (left rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 (List.replicate n false) head
      (fromCells 2 left (List.replicate n 0 ++ rest)) =
        some (head + n, fromCells 2 (List.replicate n 0 ++ left) rest) := by
  induction n generalizing head left with
  | zero => simp [run]
  | succ n ih =>
    have hw : List.replicate (n + 1) false = [false] ++ List.replicate n false := by
      simp [List.replicate_succ]
    rw [hw, run_append, List.replicate_succ, List.cons_append, initial_right_zero]
    exact (ih (head + 1) (0 :: left)).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · simp [List.replicate_succ, zeros_snoc]

theorem separator_turn (n : Nat) (head : Int) (rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 [false] head
      (fromCells 2 (List.replicate n 0) (1 :: rest)) =
        some (head - 1, returnStart n (3 :: rest)) := by
  cases n <;>
    simp [run, ULogRetainedCounterPump.program, fromCells, boundedHalted,
      applyBounded, moveHead, returnStart, List.replicate_succ]

theorem return_zeros_run (n : Nat) (head : Int) (rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 (List.replicate n false) head (returnStart n rest) =
      some (head - n, fromCells 8 [] (2 :: List.replicate n 0 ++ rest)) := by
  rw [ULogRetainedCounterPump.run_off_entry _ _ _ (by cases n <;> simp [returnStart, fromCells])]
  exact ULogCounterPumpInitialization.return_zeros_run n head rest

theorem initial_return_blank (head : Int) (rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 [false] head (fromCells 8 [] (2 :: rest)) =
      some (head + 1, fromCells 5 [2] rest) := by
  rw [ULogRetainedCounterPump.run_off_entry _ _ _ (by simp [fromCells])]
  exact ULogCounterPumpInitialization.initial_return_blank head rest

theorem initialization_run (k : Nat) (head : Int) (rest : List (Fin 4)) :
    run ULogRetainedCounterPump.program 2 (List.replicate (2 * k + 2) false) head
      (fromCells 2 [] (List.replicate k 0 ++ 1 :: rest)) =
        some (head, fromCells 5 [2] (List.replicate k 0 ++ 3 :: rest)) := by
  have hw : List.replicate (2 * k + 2) false =
      List.replicate k false ++ [false] ++ List.replicate k false ++ [false] := by
    have ht : 2 * k + 2 = k + 1 + k + 1 := by omega
    simp [ht, List.replicate_add]
  have hs : run ULogRetainedCounterPump.program 2 (List.replicate k false) head
      (fromCells 2 [] (List.replicate k 0 ++ 1 :: rest)) =
        some (head + k, fromCells 2 (List.replicate k 0) (1 :: rest)) := by
    simpa using scan_zeros_run k head [] (1 :: rest)
  have hm : run ULogRetainedCounterPump.program 2 (List.replicate k false ++ [false]) head
      (fromCells 2 [] (List.replicate k 0 ++ 1 :: rest)) =
        some (head + k - 1, returnStart k (3 :: rest)) := by
    rw [run_append, hs]
    exact separator_turn k (head + k) rest
  have hr : run ULogRetainedCounterPump.program 2
      (List.replicate k false ++ [false] ++ List.replicate k false) head
      (fromCells 2 [] (List.replicate k 0 ++ 1 :: rest)) =
        some (head - 1, fromCells 8 [] (2 :: List.replicate k 0 ++ 3 :: rest)) := by
    rw [run_append, hm]
    exact (return_zeros_run k (head + k - 1) (3 :: rest)).trans <| by
      apply congrArg some
      apply Prod.ext
      · omega
      · rfl
  rw [hw, run_append, hr]
  simpa only [Option.bind_some, Int.sub_add_cancel, List.cons_append] using
    initial_return_blank (head - 1) (List.replicate k 0 ++ 3 :: rest)

theorem input_length (k : Nat) (source : List Bool) :
    (ULogRetainedCounterPump.input k source).length =
      (ULogBytecode.encodeProgram (compile ULogRetainedCounterPump.program)).length +
        2 * (k + source.length + 1) + 1 := by
  simp [ULogRetainedCounterPump.input, ULogRetainedCounterPump.sourceInput, encodeInstance]
  omega

theorem initial_lift (k : Nat) (source : List Bool) :
    liftConfig ULogRetainedCounterPump.program
      (fromCells 2 [] (List.replicate k 0 ++ 1 :: cells source)) =
        ULogSemantics.start (ULogRetainedCounterPump.input k source) := by
  have hmap : (ULogRetainedCounterPump.sourceInput k source).map (boundedBit (0 : Fin 4) 1) =
      List.replicate k 0 ++ 1 :: cells source := by
    simp [ULogRetainedCounterPump.sourceInput, boundedBit, cells, cell]
  have hi : boundedInitial (2 : Fin 9) (0 : Fin 4) 1 2
      (ULogRetainedCounterPump.sourceInput k source) =
        fromCells 2 [] (List.replicate k 0 ++ 1 :: cells source) := by
    rw [← hmap]
    cases ULogRetainedCounterPump.sourceInput k source <;> rfl
  have hl := liftConfig_boundedInitial ULogRetainedCounterPump.program
    (2 : Fin 9) (0 : Fin 4) 1 2 rfl rfl rfl rfl
    (ULogRetainedCounterPump.sourceInput k source)
  rw [hi] at hl
  exact hl

theorem initialization_semantic_run (k : Nat) (source : List Bool) :
    semanticRun (ULogSemantics.start (ULogRetainedCounterPump.input k source))
      (List.replicate (2 * k + 2) false) =
        some (liftConfig ULogRetainedCounterPump.program
          (fromCells 5 [2] (List.replicate k 0 ++ 3 :: cells source))) := by
  rw [← initial_lift, ← run_lift ULogRetainedCounterPump.program (2 : Fin 4) rfl _ 0,
    initialization_run]
  rfl

end PakFixedPolyomino.ULogRetainedCounterPumpInitialization
