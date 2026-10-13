import PakFixedPolyomino.ULogTernaryRetainedPumpIteration
import PakFixedPolyomino.ULogTernaryRetainedPumpInitialization
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! ALL raw counts and endpoints from actual compact binary initialization
of the fixed ternary source-retaining pump. Source length is charged in every
append sweep; the accepted run is internally built, never supplied as a
certificate. Physical fixed interpretation and prefix peak are separate. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpCounts

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open ULogFiniteAlphabetDeterministicRuns
open ULogTernaryRetainedCounterPump (input)

def bodyFuel (k : Nat) (source : List Bool) : Nat := (2 ^ k) ^ 2 + (2 * k + 2 * source.length + 8) * 2 ^ k - k - 3

def deadline (k : Nat) (source : List Bool) : Nat := 2 * k + 2 + bodyFuel k source

abbrev initial := ULogTernaryRetainedCounterPump.initial

def final (k : Nat) (source : List Bool) : BoundedConfig 10 3 :=
  fromCells 0 (List.replicate k 0 ++ [2]) (2 :: (ULogTernaryRetainedCounterPump.cells source ++ List.replicate (2 ^ k) 0))

def finalConfig (k : Nat) (source : List Bool) : ULogSemantics.Config := liftConfig ULogTernaryRetainedCounterPump.program (final k source)

theorem initial_lift (k : Nat) (source : List Bool) : liftConfig ULogTernaryRetainedCounterPump.program (initial k source) = ULogSemantics.start (input k source) :=
  ULogTernaryRetainedPumpInitialization.initial_lift k source

theorem encoded_zipper_run (k : Nat) (source : List Bool) :
    run ULogTernaryRetainedCounterPump.program 2 (List.replicate (deadline k source) false) 0 (initial k source) =
      some ((k : Int), final k source) := by
  rw [deadline, List.replicate_add, run_append]
  rw [show run ULogTernaryRetainedCounterPump.program 2 (List.replicate (2 * k + 2) false) 0 (initial k source) = _ from
    ULogTernaryRetainedPumpInitialization.initialization_run k source 0, Option.bind_some]
  simpa [bodyFuel, final, ULogTernaryRetainedCounterPump.data,
    ULogTernaryRetainedPumpIteration.cells_replicate, ULogTernaryRetainedCounterPump.cell] using ULogTernaryRetainedPumpIteration.zero_bits_run k source 0

theorem encoded_semantic_run (k : Nat) (source : List Bool) :
    semanticRun (ULogSemantics.start (input k source)) (List.replicate (deadline k source) false) =
      some (finalConfig k source) := by
  rw [← initial_lift k source, ← run_lift ULogTernaryRetainedCounterPump.program
    (2 : Fin 3) rfl _ 0, encoded_zipper_run]
  rfl

theorem program_falseOnly : FalseOnly ULogTernaryRetainedCounterPump.program := by
  intro q a
  rfl

theorem final_accepts (k : Nat) (source : List Bool) : (final k source).state.val = 0 := rfl

theorem acceptingPaths_threshold (k T : Nat) (source : List Bool) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input k source)) =
      if deadline k source ≤ T then 1 else 0 := by
  rw [← initial_lift k source]
  exact ULogFiniteAlphabetDeterministicRuns.acceptingPaths_threshold (2 : Fin 3) rfl
    ULogTernaryRetainedCounterPump.program program_falseOnly (deadline k source) 0 (initial k source) (final k source) k
    (encoded_zipper_run k source) (final_accepts k source) T

theorem every_raw_prefix_length_le (k : Nat) (source : List Bool) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input k source)) w = some out) :
    w.length ≤ deadline k source := by
  rw [← initial_lift k source] at hw
  exact successful_semantic_length_le (2 : Fin 3) rfl ULogTernaryRetainedCounterPump.program program_falseOnly
    (deadline k source) 0 (initial k source) (final k source) k (encoded_zipper_run k source) (final_accepts k source) hw

theorem every_accepting_word_eq (k : Nat) (source : List Bool) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input k source)) w = some out) (ha : out.state = 0) :
    w = List.replicate (deadline k source) false ∧ out = finalConfig k source := by
  have hw' := hw
  rw [← initial_lift k source] at hw'
  have he := accepting_semantic_word_eq (2 : Fin 3) rfl ULogTernaryRetainedCounterPump.program program_falseOnly
    (deadline k source) 0 (initial k source) (final k source) k (encoded_zipper_run k source) (final_accepts k source) hw' ha
  refine ⟨he, ?_⟩
  rw [he, encoded_semantic_run] at hw
  exact (Option.some.inj hw).symm

theorem final_cell_count (k : Nat) (source : List Bool) :
    (finalConfig k source).leftRev.length + 1 + (finalConfig k source).right.length = k + source.length + 2 ^ k + 2 := by
  simp [finalConfig, final, fromCells, liftConfig, ULogTernaryRetainedCounterPump.cells]
  omega

theorem input_length (k : Nat) (source : List Bool) :
    (input k source).length =
      (ULogBytecode.encodeProgram (compile ULogTernaryRetainedCounterPump.program)).length +
        2 * (k + source.length + 1) + 1 := by
  simp [ULogTernaryRetainedCounterPump.input, ULogTernaryRetainedCounterPump.sourceInput,
    encodeInstance, ULogBytecode.length_encodePayload]
  omega

theorem encoded_pump_spec (k : Nat) (source : List Bool) :
    (input k source).length = (ULogBytecode.encodeProgram (compile ULogTernaryRetainedCounterPump.program)).length + 2 * (k + source.length + 1) + 1 ∧
    semanticRun (ULogSemantics.start (input k source)) (List.replicate (deadline k source) false) =
      some (finalConfig k source) ∧
    (finalConfig k source).leftRev.length + 1 + (finalConfig k source).right.length = k + source.length + 2 ^ k + 2 ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input k source)) =
      if deadline k source ≤ T then 1 else 0) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input k source)) w = some out → w.length ≤ deadline k source) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input k source)) w = some out → out.state = 0 →
      w = List.replicate (deadline k source) false ∧ out = finalConfig k source) := by
  exact ⟨input_length k source, encoded_semantic_run k source,
    final_cell_count k source, (fun T => acceptingPaths_threshold k T source), every_raw_prefix_length_le k source,
    every_accepting_word_eq k source⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpCounts
