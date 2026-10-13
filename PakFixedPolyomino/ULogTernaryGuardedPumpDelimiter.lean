import PakFixedPolyomino.ULogTernaryGuardedPumpSentinelSpace
import PakFixedPolyomino.ULogTernaryCountedSourceDelimiterSpace

/-! Literal guarded generator/parser/left-sentinel/source-delimiter sequence.
One existing generated buffer zero becomes the delimiter. Every original
source bit and the remaining exponential buffer survive. This is a concrete
finite source program, not a physical loader or the fixed square theorem. -/
namespace PakFixedPolyomino.ULogTernaryGuardedPumpDelimiter
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogTernaryRetainedCounterPump (cells)

abbrev prefixStates (d c : Nat) := ULogTernaryGuardedPumpSentinel.totalStates d c
abbrev totalStates (d c : Nat) := ULogFiniteTapeGuardedStageComposition.stateCount (prefixStates d c) 24

theorem prefix_states_ge3 (d c : Nat) : 3 ≤ prefixStates d c := by
  unfold prefixStates ULogTernaryGuardedPumpSentinel.totalStates ULogFiniteTapeGuardedStageComposition.stateCount ULogTernaryGuardedPumpSentinel.parserStates
    ULogTernaryParserLeftSentinel.totalStates ULogFiniteTapeStageComposition.stateCount
    ULogTernaryParserLeftSentinel.parserStates
  omega

def program (d c : Nat) : BoundedProgram (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.program (ULogTernaryGuardedPumpSentinel.program d c) ULogTernaryCountedSourceDelimiter.program (prefix_states_ge3 d c) (by omega) .stay

def under (k d c : Nat) (x : List Bool) : List (Fin 3) :=
  ULogTernaryParserLeftSentinel.under d c x (ULogTernaryGuardedPumpSentinel.parserLeft k)

def buffer (k : Nat) : List (Fin 3) := List.replicate (2 ^ k - 1) 0

def initial (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig (ULogTernaryGuardedPumpSentinel.initial k d c x)

def final (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig (ULogTernaryCountedSourceDelimiter.finalConfig x (under k d c x) (buffer k))

def deadline (k d c : Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpSentinel.deadline k d c x + 2 + ULogTernaryCountedSourceDelimiter.deadline x.length

def prefixHead (k d c : Nat) (x : List Bool) : Int :=
  (k : Int) + 1 + (ULogTernaryNestedHeaderParser.header d c x).length

def finalHead (k d c : Nat) (x : List Bool) : Int :=
  prefixHead k d c x + x.length + 1

theorem handoff_start (k d c : Nat) (x : List Bool) :
    ULogFiniteTapeGuardedStageComposition.secondStart (by omega) (2 : Fin 3) .stay (ULogTernaryGuardedPumpSentinel.final k d c x) =
      ULogTernaryCountedSourceDelimiter.initial x (under k d c x) (buffer k) := by
  have left := ULogTernaryGuardedPumpSentinel.final_layout k d c x
  have tape : (ULogTernaryGuardedPumpSentinel.final k d c x).focus :: (ULogTernaryGuardedPumpSentinel.final k d c x).right =
      List.replicate x.length (0 : Fin 3) ++
        1 :: (cells x ++ 0 :: buffer k) := by
    rw [left.2, ULogTernaryGuardedPumpSentinel.generated_first_zero]
    simp [ULogTernaryNestedHeaderParser.counted, StandardBitRetainedPayload.payload, ULogBytecode.encodePayload, ULogBytecode.encodeNatField, cells,
      ULogTernaryRetainedCounterPump.cell, buffer, List.map_append,
      List.append_assoc]
  have state : ULogFiniteTapeGuardedStageComposition.secondStart (ms := 24) (by omega) (2 : Fin 3) .stay (ULogTernaryGuardedPumpSentinel.final k d c x) =
      ⟨2, (ULogTernaryGuardedPumpSentinel.final k d c x).leftRev, (ULogTernaryGuardedPumpSentinel.final k d c x).focus,
        (ULogTernaryGuardedPumpSentinel.final k d c x).right⟩ := rfl
  rw [state]
  unfold ULogTernaryCountedSourceDelimiter.initial
  rw [← tape, left.1]
  rfl

theorem actual_run (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    run (program d c) 2 (List.replicate (deadline k d c x) false) 0
      (initial k d c x) = some (finalHead k d c x, final k d c x) := by
  have second := ULogTernaryCountedSourceDelimiter.delimiter_run x (under k d c x) (buffer k) (prefixHead k d c x)
  have hq : run ULogTernaryCountedSourceDelimiter.program 2 (List.replicate (ULogTernaryCountedSourceDelimiter.deadline x.length) false)
      (FiniteOneTapeSemantics.moveHead .stay (prefixHead k d c x))
      (ULogFiniteTapeGuardedStageComposition.secondStart (by omega) (2 : Fin 3) .stay (ULogTernaryGuardedPumpSentinel.final k d c x)) =
        some (finalHead k d c x, ULogTernaryCountedSourceDelimiter.finalConfig x (under k d c x) (buffer k)) := by
    rw [handoff_start]
    exact second
  have both := ULogFiniteTapeGuardedStageComposition.sequential_run (ULogTernaryGuardedPumpSentinel.program d c) ULogTernaryCountedSourceDelimiter.program (prefix_states_ge3 d c)
    (by omega) .stay (2 : Fin 3) (List.replicate (ULogTernaryGuardedPumpSentinel.deadline k d c x) false)
    (List.replicate (ULogTernaryCountedSourceDelimiter.deadline x.length) false) 0 (prefixHead k d c x)
    (finalHead k d c x) (ULogTernaryGuardedPumpSentinel.initial k d c x) (ULogTernaryGuardedPumpSentinel.final k d c x)
    (ULogTernaryCountedSourceDelimiter.finalConfig x (under k d c x) (buffer k)) (ULogTernaryGuardedPumpSentinel.actual_run k d c hc x)
    (ULogTernaryGuardedPumpSentinel.final_accepts k d c x) hq
  have word : List.replicate (deadline k d c x) false =
      List.replicate (ULogTernaryGuardedPumpSentinel.deadline k d c x) false ++
        false :: false :: List.replicate (ULogTernaryCountedSourceDelimiter.deadline x.length) false := by
    unfold deadline
    rw [Nat.add_assoc, show 2 + ULogTernaryCountedSourceDelimiter.deadline x.length = ULogTernaryCountedSourceDelimiter.deadline x.length + 2 by omega,
      List.replicate_add, List.replicate_succ, List.replicate_succ]
  rw [word]
  exact both

theorem program_falseOnly (d c : Nat) : FalseOnly (program d c) :=
  ULogFiniteTapeGuardedStageCompositionRuns.program_falseOnly _ _ (prefix_states_ge3 d c)
    (by omega) .stay (ULogTernaryGuardedPumpSentinel.program_falseOnly d c)
    ULogTernaryCountedSourceDelimiterSpace.program_falseOnly

theorem final_accepts (k d c : Nat) (x : List Bool) :
    (final k d c x).state.val = 0 := by
  simp [final, ULogFiniteTapeGuardedStageComposition.rightConfig, ULogFiniteTapeGuardedStageComposition.rightState, ULogTernaryCountedSourceDelimiter.finalConfig, ULogTernaryCountedSourceDelimiter.fromCells_state]

theorem initial_lift (k d c : Nat) (x : List Bool) :
    liftConfig (program d c) (initial k d c x) = ULogSemantics.start
      (encodeInstance (program d c)
        (ULogTernaryRetainedCounterPump.sourceInput k
          (ULogTernaryGuardedPumpSentinel.source d c x))) := by
  have cell : ULogTernaryRetainedCounterPump.cell = boundedBit (0 : Fin 3) 1 := by
    funext b
    cases b <;> rfl
  have init : initial k d c x =
      boundedInitial (⟨2, by
        have h := prefix_states_ge3 d c
        unfold totalStates ULogFiniteTapeGuardedStageComposition.stateCount
        omega⟩ : Fin (totalStates d c))
        (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput k
          (ULogTernaryGuardedPumpSentinel.source d c x)) := by
    cases k <;>
      simp [initial, ULogTernaryGuardedPumpSentinel.initial,
        ULogFiniteTapeGuardedStageComposition.leftConfig,
        ULogFiniteTapeGuardedStageComposition.leftState,
        ULogTernaryRetainedCounterPump.initial, ULogTernaryRetainedCounterPump.fromCells,
        ULogTernaryRetainedCounterPump.sourceInput, ULogTernaryRetainedCounterPump.cells,
        cell, boundedInitial, boundedBit, List.replicate_succ]
  rw [init]
  exact liftConfig_boundedInitial (program d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _

theorem every_raw_length (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline k d c x :=
  ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly d c) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly d c)
      (deadline k d c x) 0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) hw⟩

theorem every_accepting_word (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline k d c x) false ∧
      hf = finalHead k d c x ∧ out = final k d c x :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly d c)
    (deadline k d c x) 0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) hw ha

theorem all_cutoff_counts (k d c T : Nat) (hc : 0 < c) (x : List Bool) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program d c) (initial k d c x)) =
      if deadline k d c x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly d c)
    (deadline k d c x) 0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) T

theorem compiled_symbols (d c : Nat) :
    ∀ r ∈ compile (program d c), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have bound := compile_rule_bounded (program d c) hr
  exact ⟨bound.2.1, bound.2.2.1⟩

end PakFixedPolyomino.ULogTernaryGuardedPumpDelimiter
