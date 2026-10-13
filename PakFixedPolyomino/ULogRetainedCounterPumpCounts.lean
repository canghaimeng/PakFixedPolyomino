import PakFixedPolyomino.ULogRetainedCounterPumpIteration
import PakFixedPolyomino.ULogRetainedCounterPumpInitialization
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! ALL raw counts and endpoints from genuine compact binary initialization
of the fixed source-retaining pump. Source length is charged in every
append sweep; the accepted run is internally built, never supplied as a
certificate. Physical fixed interpretation and prefix peak are separate. -/

namespace PakFixedPolyomino.ULogRetainedCounterPumpCounts

open ULogCompiler ULogFiniteTapeZipperRun ULogCounterPump
open ULogFiniteAlphabetDeterministicRuns
open ULogRetainedCounterPump (input)

def bodyFuel (k : Nat) (source : List Bool) : Nat := (2 ^ k) ^ 2 + (2 * k + 2 * source.length + 8) * 2 ^ k - k - 3

def deadline (k : Nat) (source : List Bool) : Nat := 2 * k + 2 + bodyFuel k source

def initial (k : Nat) (source : List Bool) : BoundedConfig 9 4 := fromCells 2 [] (List.replicate k 0 ++ 1 :: ULogCounterPumpBinarySteps.cells source)

def final (k : Nat) (source : List Bool) : BoundedConfig 9 4 :=
  fromCells 0 (List.replicate k 0 ++ [2]) (3 :: (ULogCounterPumpBinarySteps.cells source ++ List.replicate (2 ^ k) 0))

def finalConfig (k : Nat) (source : List Bool) : ULogSemantics.Config := liftConfig ULogRetainedCounterPump.program (final k source)

theorem initial_lift (k : Nat) (source : List Bool) : liftConfig ULogRetainedCounterPump.program (initial k source) = ULogSemantics.start (input k source) :=
  ULogRetainedCounterPumpInitialization.initial_lift k source

theorem encoded_zipper_run (k : Nat) (source : List Bool) :
    run ULogRetainedCounterPump.program 2 (List.replicate (deadline k source) false) 0 (initial k source) =
      some ((k : Int), final k source) := by
  rw [deadline, List.replicate_add, run_append]
  rw [show run ULogRetainedCounterPump.program 2 (List.replicate (2 * k + 2) false) 0 (initial k source) = _ from
    ULogRetainedCounterPumpInitialization.initialization_run k 0 (ULogCounterPumpBinarySteps.cells source), Option.bind_some]
  simpa [bodyFuel, final] using ULogRetainedCounterPumpIteration.zero_bits_run k source 0

theorem encoded_semantic_run (k : Nat) (source : List Bool) :
    semanticRun (ULogSemantics.start (input k source)) (List.replicate (deadline k source) false) =
      some (finalConfig k source) := by
  rw [← initial_lift k source, ← run_lift ULogRetainedCounterPump.program
    (2 : Fin 4) rfl _ 0, encoded_zipper_run]
  rfl

theorem program_falseOnly : FalseOnly ULogRetainedCounterPump.program := by
  intro q a
  rfl

theorem final_accepts (k : Nat) (source : List Bool) : (final k source).state.val = 0 := rfl

theorem acceptingPaths_threshold (k T : Nat) (source : List Bool) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input k source)) =
      if deadline k source ≤ T then 1 else 0 := by
  rw [← initial_lift k source]
  exact ULogFiniteAlphabetDeterministicRuns.acceptingPaths_threshold (2 : Fin 4) rfl
    ULogRetainedCounterPump.program program_falseOnly (deadline k source) 0 (initial k source) (final k source) k
    (encoded_zipper_run k source) (final_accepts k source) T

theorem every_raw_prefix_length_le (k : Nat) (source : List Bool) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input k source)) w = some out) :
    w.length ≤ deadline k source := by
  rw [← initial_lift k source] at hw
  exact successful_semantic_length_le (2 : Fin 4) rfl ULogRetainedCounterPump.program program_falseOnly
    (deadline k source) 0 (initial k source) (final k source) k (encoded_zipper_run k source) (final_accepts k source) hw

theorem every_accepting_word_eq (k : Nat) (source : List Bool) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input k source)) w = some out) (ha : out.state = 0) :
    w = List.replicate (deadline k source) false ∧ out = finalConfig k source := by
  have hw' := hw
  rw [← initial_lift k source] at hw'
  have he := accepting_semantic_word_eq (2 : Fin 4) rfl ULogRetainedCounterPump.program program_falseOnly
    (deadline k source) 0 (initial k source) (final k source) k (encoded_zipper_run k source) (final_accepts k source) hw' ha
  refine ⟨he, ?_⟩
  rw [he, encoded_semantic_run] at hw
  exact (Option.some.inj hw).symm

theorem final_cell_count (k : Nat) (source : List Bool) :
    (finalConfig k source).leftRev.length + 1 + (finalConfig k source).right.length = k + source.length + 2 ^ k + 2 := by
  simp [finalConfig, final, fromCells, liftConfig, ULogCounterPumpBinarySteps.cells]
  omega

theorem encoded_pump_spec (k : Nat) (source : List Bool) :
    (input k source).length = (ULogBytecode.encodeProgram (compile ULogRetainedCounterPump.program)).length + 2 * (k + source.length + 1) + 1 ∧
    semanticRun (ULogSemantics.start (input k source)) (List.replicate (deadline k source) false) =
      some (finalConfig k source) ∧
    (finalConfig k source).leftRev.length + 1 + (finalConfig k source).right.length = k + source.length + 2 ^ k + 2 ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input k source)) =
      if deadline k source ≤ T then 1 else 0) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input k source)) w = some out → w.length ≤ deadline k source) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input k source)) w = some out → out.state = 0 →
      w = List.replicate (deadline k source) false ∧ out = finalConfig k source) := by
  exact ⟨ULogRetainedCounterPumpInitialization.input_length k source, encoded_semantic_run k source,
    final_cell_count k source, (fun T => acceptingPaths_threshold k T source), every_raw_prefix_length_le k source,
    every_accepting_word_eq k source⟩

end PakFixedPolyomino.ULogRetainedCounterPumpCounts
