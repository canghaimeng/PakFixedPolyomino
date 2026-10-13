import PakFixedPolyomino.ULogTernaryRetainedPumpCounts
import PakFixedPolyomino.ULogTernaryParserLeftSentinel
import PakFixedPolyomino.ULogFiniteTapeGuardedStageCompositionRuns

/-! Literal ternary pump-to-parser sequencing. The pump's accept state is
a live handoff in this bytecode, so only completion of the actual parser
accepts. Two real handoff ticks visit the maximum allocated state. A positive real seed cell supplies the disposable left marker. The exponential
buffer and entire original unary length field are preserved. Source-end delimitation and physical realization remain
separate. No accepted run is supplied as a hypothesis. -/

namespace PakFixedPolyomino.ULogTernaryGuardedPumpSentinel

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogTernaryRetainedCounterPump (cells)

abbrev parserStates (d c : Nat) := ULogTernaryParserLeftSentinel.totalStates d c
abbrev totalStates (d c : Nat) := ULogFiniteTapeGuardedStageComposition.stateCount 10 (parserStates d c)

theorem parserStates_ge3 (d c : Nat) : 3 ≤ parserStates d c := by
  unfold parserStates ULogTernaryParserLeftSentinel.totalStates
    ULogFiniteTapeStageComposition.stateCount ULogTernaryParserLeftSentinel.parserStates
  omega

def program (d c : Nat) : BoundedProgram (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.program ULogTernaryRetainedCounterPump.program
    (ULogTernaryParserLeftSentinel.program d c) (by omega) (parserStates_ge3 d c) .right

def source (d c : Nat) (x : List Bool) := ULogTernaryNestedHeaderParser.nested d c x

def parserLeft (k : Nat) : List (Fin 3) := 2 :: (List.replicate k 0 ++ [2])

def parserInitial (k d c : Nat) (x : List Bool) : BoundedConfig (parserStates d c) 3 :=
  ULogTernaryParserLeftSentinel.initial d c x (parserLeft k) (List.replicate (2 ^ k) 0)

def parserFinal (k d c : Nat) (x : List Bool) : BoundedConfig (parserStates d c) 3 :=
  ULogTernaryParserLeftSentinel.final d c x (parserLeft k) (List.replicate (2 ^ k) 0)

def initial (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig (ULogTernaryRetainedCounterPump.initial k (source d c x))

def final (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig (parserFinal k d c x)

def deadline (k d c : Nat) (x : List Bool) : Nat :=
  ULogTernaryRetainedPumpCounts.deadline k (source d c x) + 2 +
    ((ULogTernaryNestedHeaderParser.header d c x).length + 5)

theorem initial_lift (k d c : Nat) (x : List Bool) :
    liftConfig (program d c) (initial k d c x) = ULogSemantics.start
      (encodeInstance (program d c) (ULogTernaryRetainedCounterPump.sourceInput k (source d c x))) := by
  have hcell : ULogTernaryRetainedCounterPump.cell = boundedBit (0 : Fin 3) 1 := by
    funext b
    cases b <;> rfl
  have hi : initial k d c x =
      boundedInitial (⟨2, by unfold totalStates ULogFiniteTapeGuardedStageComposition.stateCount; omega⟩ : Fin (totalStates d c))
        (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput k (source d c x)) := by
    cases k <;>
      simp [initial, ULogFiniteTapeGuardedStageComposition.leftConfig,
        ULogFiniteTapeGuardedStageComposition.leftState, ULogTernaryRetainedCounterPump.initial,
        ULogTernaryRetainedCounterPump.fromCells, ULogTernaryRetainedCounterPump.sourceInput,
        ULogTernaryRetainedCounterPump.cells, hcell, boundedInitial, boundedBit, List.replicate_succ]
  rw [hi]
  exact liftConfig_boundedInitial (program d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _

theorem source_nonempty (d c : Nat) (x : List Bool) : cells (source d c x) ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp [cells, source, ULogTernaryNestedHeaderParser.nested_length,
    ULogTernaryNestedHeaderParser.counted_length] at hl

theorem handoff_start (k d c : Nat) (x : List Bool) :
    ULogFiniteTapeGuardedStageComposition.secondStart (parserStates_ge3 d c)
      (2 : Fin 3) .right (ULogTernaryRetainedPumpCounts.final k (source d c x)) =
      parserInitial k d c x := by
  have hne : cells (source d c x) ++ List.replicate (2 ^ k) 0 ≠ [] := by
    simp [source_nonempty]
  cases hr : cells (source d c x) ++ List.replicate (2 ^ k) 0 with
  | nil => exact (hne hr).elim
  | cons a rest =>
      change cells (ULogTernaryNestedHeaderParser.nested d c x) ++ List.replicate (2 ^ k) 0 = a :: rest at hr
      simp [ULogFiniteTapeGuardedStageComposition.secondStart, ULogTernaryRetainedPumpCounts.final,
        ULogTernaryRetainedCounterPump.fromCells, applyBounded, parserInitial,
        ULogTernaryNestedHeaderParser.fromCells, ULogTernaryNestedHeaderParser.startState,
        ULogTernaryParserLeftSentinel.initial, ULogFiniteTapeStageComposition.leftConfig,
        ULogFiniteTapeStageComposition.leftState,
        parserLeft, source, hr]

theorem actual_run (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    run (program d c) 2 (List.replicate (deadline k d c x) false) 0 (initial k d c x) =
      some ((k : Int) + 1 + (ULogTernaryNestedHeaderParser.header d c x).length, final k d c x) := by
  have hp := ULogTernaryRetainedPumpCounts.encoded_zipper_run k (source d c x)
  have hq := ULogTernaryParserLeftSentinel.actual_run d c x
    (parserLeft k) (List.replicate (2 ^ k) 0) hc ((k : Int) + 1)
  have hq' : run (ULogTernaryParserLeftSentinel.program d c) 2
      (List.replicate ((ULogTernaryNestedHeaderParser.header d c x).length + 5) false)
      (FiniteOneTapeSemantics.moveHead .right (k : Int))
      (ULogFiniteTapeGuardedStageComposition.secondStart (parserStates_ge3 d c)
        (2 : Fin 3) .right (ULogTernaryRetainedPumpCounts.final k (source d c x))) =
      some ((k : Int) + 1 + (ULogTernaryNestedHeaderParser.header d c x).length,
        parserFinal k d c x) := by
    rw [handoff_start]
    simpa [FiniteOneTapeSemantics.moveHead, parserInitial, parserFinal, source] using hq
  have hseq := ULogFiniteTapeGuardedStageComposition.sequential_run
    ULogTernaryRetainedCounterPump.program (ULogTernaryParserLeftSentinel.program d c)
    (by omega) (parserStates_ge3 d c) .right (2 : Fin 3)
    (List.replicate (ULogTernaryRetainedPumpCounts.deadline k (source d c x)) false)
    (List.replicate ((ULogTernaryNestedHeaderParser.header d c x).length + 5) false)
    0 k ((k : Int) + 1 + (ULogTernaryNestedHeaderParser.header d c x).length)
    (ULogTernaryRetainedCounterPump.initial k (source d c x))
    (ULogTernaryRetainedPumpCounts.final k (source d c x)) (parserFinal k d c x) hp rfl hq'
  have hword : List.replicate (deadline k d c x) false =
      List.replicate (ULogTernaryRetainedPumpCounts.deadline k (source d c x)) false ++
        false :: false :: List.replicate ((ULogTernaryNestedHeaderParser.header d c x).length + 5) false := by
    unfold deadline
    rw [Nat.add_assoc, show 2 + ((ULogTernaryNestedHeaderParser.header d c x).length + 5) =
      ((ULogTernaryNestedHeaderParser.header d c x).length + 5) + 2 by omega,
      List.replicate_add, List.replicate_succ, List.replicate_succ]
  rw [hword]
  simpa only [program, initial, final] using hseq

theorem program_falseOnly (d c : Nat) : FalseOnly (program d c) :=
  ULogFiniteTapeGuardedStageCompositionRuns.program_falseOnly _ _ (by omega) (parserStates_ge3 d c)
    .right ULogTernaryRetainedPumpCounts.program_falseOnly
    (ULogTernaryParserLeftSentinel.program_falseOnly d c)

theorem final_accepts (k d c : Nat) (x : List Bool) : (final k d c x).state.val = 0 := by
  have h := ULogTernaryParserLeftSentinel.final_accepts d c x (parserLeft k) (List.replicate (2 ^ k) 0)
  simp [final, ULogFiniteTapeGuardedStageComposition.rightConfig,
    ULogFiniteTapeGuardedStageComposition.rightState, parserFinal, h]

theorem final_layout (k d c : Nat) (x : List Bool) :
    (final k d c x).leftRev =
        2 :: ULogTernaryParserLeftSentinel.under d c x (parserLeft k) ∧
      (final k d c x).focus :: (final k d c x).right =
        cells (ULogTernaryNestedHeaderParser.counted x) ++ List.replicate (2 ^ k) 0 := by
  have hne := ULogTernaryParserLeftSentinel.counted_tape_nonempty x (List.replicate (2 ^ k) 0)
  cases hr : cells (ULogTernaryNestedHeaderParser.counted x) ++ List.replicate (2 ^ k) 0 with
  | nil => exact (hne hr).elim
  | cons a rest =>
      simp [final, parserFinal, ULogTernaryParserLeftSentinel.final,
        ULogFiniteTapeGuardedStageComposition.rightConfig,
        ULogFiniteTapeStageComposition.rightConfig, ULogTernaryNestedHeaderParser.fromCells, hr]

theorem generated_first_zero (k : Nat) :
    List.replicate (2 ^ k) (0 : Fin 3) = 0 :: List.replicate (2 ^ k - 1) 0 := by
  have hpos : 0 < 2 ^ k := by positivity
  rw [← List.replicate_succ]
  congr 1
  omega

theorem every_raw_length (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline k d c x :=
  ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly d c) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly d c) (deadline k d c x)
      0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) hw⟩

theorem every_accepting_word (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline k d c x) false ∧
      hf = (k : Int) + 1 + (ULogTernaryNestedHeaderParser.header d c x).length ∧ out = final k d c x :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly d c) (deadline k d c x)
    0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) hw ha

theorem all_cutoff_counts (k d c T : Nat) (hc : 0 < c) (x : List Bool) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program d c) (initial k d c x)) =
      if deadline k d c x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly d c) (deadline k d c x)
    0 _ _ _ (actual_run k d c hc x) (final_accepts k d c x) T

def guardWord (k d c : Nat) (x : List Bool) : List Bool :=
  List.replicate (ULogTernaryRetainedPumpCounts.deadline k (source d c x)) false ++ [false]

def guard (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.guardConfig 2 .right
    (ULogTernaryRetainedPumpCounts.final k (source d c x))

theorem actual_guard_run (k d c : Nat) (x : List Bool) :
    run (program d c) 2 (guardWord k d c x) 0 (initial k d c x) =
      some ((k : Int) + 1, guard k d c x) := by
  unfold guardWord initial program
  rw [run_append, ULogFiniteTapeGuardedStageComposition.run_left
    ULogTernaryRetainedCounterPump.program (ULogTernaryParserLeftSentinel.program d c)
    (by omega) (parserStates_ge3 d c) .right (2 : Fin 3) _ 0 k _ _
    (ULogTernaryRetainedPumpCounts.encoded_zipper_run k (source d c x)), Option.bind_some]
  simpa only [FiniteOneTapeSemantics.moveHead, guard, program] using
    ULogFiniteTapeGuardedStageComposition.first_handoff_run
      ULogTernaryRetainedCounterPump.program (ULogTernaryParserLeftSentinel.program d c)
      (by omega) (parserStates_ge3 d c) .right (2 : Fin 3) k
      (ULogTernaryRetainedPumpCounts.final k (source d c x)) rfl

theorem actual_guard_state (k d c : Nat) (x : List Bool) :
    (guard k d c x).state.val = totalStates d c - 1 := by
  unfold guard
  rw [ULogFiniteTapeGuardedStageComposition.guard_state]
  simp [totalStates, ULogFiniteTapeGuardedStageComposition.stateCount]

theorem actual_guard_capacity_necessary (k d c : Nat) (x : List Bool)
    (C : Nat) (outer : List ULogProgram.Tape)
    (ready : ULogBootstrapExecution.NonClockFrameReady
      (liftConfig (program d c) (guard k d c x)) C outer) :
    totalStates d c - 1 ≤ C := by
  have hc := ready.state_le_capacity
  change (guard k d c x).state.val ≤ C at hc
  rwa [actual_guard_state] at hc

end PakFixedPolyomino.ULogTernaryGuardedPumpSentinel
