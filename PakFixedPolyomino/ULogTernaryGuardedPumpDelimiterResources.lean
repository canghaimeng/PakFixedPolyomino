import PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterSpace
import PakFixedPolyomino.ULogFiniteTapeActiveReadySuffix

/-! Exact active-readiness threshold at the real maximum-state visit after
generation/parser/sentinel and before delimitation. This is an explicit
intermediate readiness predicate; ALL raw physical rejection below this
threshold and full-frame fibres are not inferred from it. -/
namespace PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterResources
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeDeterministicFrameReadiness
open ULogTernaryGuardedPumpDelimiter
open ULogTernaryGuardedPumpDelimiterSpace (peak)

def guardWord (k d c : Nat) (x : List Bool) : List Bool :=
  List.replicate (ULogTernaryGuardedPumpSentinel.deadline k d c x) false ++ [false]

def guard (k d c : Nat) (x : List Bool) : BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.guardConfig 2 .stay
    (ULogTernaryGuardedPumpSentinel.final k d c x)

theorem actual_guard_run (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    run (program d c) 2 (guardWord k d c x) 0 (initial k d c x) =
      some (prefixHead k d c x, guard k d c x) := by
  unfold guardWord initial program
  rw [run_append, ULogFiniteTapeGuardedStageComposition.run_left
    (ULogTernaryGuardedPumpSentinel.program d c) ULogTernaryCountedSourceDelimiter.program
    (prefix_states_ge3 d c) (by omega) .stay (2 : Fin 3) _ 0 (prefixHead k d c x) _ _
    (ULogTernaryGuardedPumpSentinel.actual_run k d c hc x), Option.bind_some]
  exact ULogFiniteTapeGuardedStageComposition.first_handoff_run
    (ULogTernaryGuardedPumpSentinel.program d c) ULogTernaryCountedSourceDelimiter.program
    (prefix_states_ge3 d c) (by omega) .stay (2 : Fin 3) (prefixHead k d c x)
    (ULogTernaryGuardedPumpSentinel.final k d c x)
    (ULogTernaryGuardedPumpSentinel.final_accepts k d c x)

theorem actual_guard_state (k d c : Nat) (x : List Bool) :
    (guard k d c x).state.val = totalStates d c - 1 := by
  unfold guard
  rw [ULogFiniteTapeGuardedStageComposition.guard_state]
  simp [totalStates, ULogFiniteTapeGuardedStageComposition.stateCount]

theorem initial_cells (k d c : Nat) (x : List Bool) :
    cellCount (initial k d c x) =
      k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 1 := by
  cases k <;>
    simp [initial, ULogTernaryGuardedPumpSentinel.initial,
      ULogFiniteTapeGuardedStageComposition.leftConfig,
      ULogTernaryRetainedCounterPump.initial, ULogTernaryRetainedCounterPump.fromCells,
      ULogTernaryRetainedCounterPump.cells, cellCount, List.replicate_succ,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem guard_cells (k d c : Nat) (x : List Bool) (hc : 0 < c) :
    cellCount (guard k d c x) = peak k d c x := by
  rw [guard, ULogTernaryGuardedPumpDelimiterSpace.guard_cell_count]
  have layout := ULogTernaryGuardedPumpDelimiter.handoff_start k d c x
  have count := congrArg cellCount layout
  have unchanged : cellCount
      (ULogFiniteTapeGuardedStageComposition.secondStart (ms := 24) (by omega)
        (2 : Fin 3) .stay (ULogTernaryGuardedPumpSentinel.final k d c x)) =
      cellCount (ULogTernaryGuardedPumpSentinel.final k d c x) := rfl
  rw [unchanged, ULogTernaryCountedSourceDelimiterSpace.occupied_initial,
    ULogTernaryGuardedPumpDelimiterSpace.delimiter_occupied k d c x hc] at count
  exact count

theorem actual_guard_growth (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    GrowthRun (program d c) 2 (guardWord k d c x) 0 (initial k d c x)
      (prefixHead k d c x) (guard k d c x) 1 (2 ^ k) := by
  obtain ⟨lg, rg, growth, hl, hr⟩ := ULogTernaryGuardedPumpDelimiterSpace.every_raw_growth
    k d c hc x (guardWord k d c x) (prefixHead k d c x) (guard k d c x)
    (actual_guard_run k d c hc x)
  have cells := growth.exact_ledger.2.2.1
  rw [guard_cells k d c x hc, initial_cells] at cells
  unfold ULogTernaryGuardedPumpDelimiterSpace.peak
    ULogTernaryGuardedPumpSentinelSpace.peak at cells
  have left : lg = 1 := by omega
  have right : rg = 2 ^ k := by omega
  simpa [left, right] using growth

theorem actual_guard_resources (k d c : Nat) (hc : 0 < c) (x : List Bool) (C : Nat)
    (outer : List ULogProgram.Tape) :
    resourceRun (program d c) 2 (guardWord k d c x) 0 (initial k d c x) C outer =
      some (prefixHead k d c x, guard k d c x, C - 2 ^ k, outer.drop 1) :=
  actual_resource_run (actual_guard_growth k d c hc x) C outer

theorem whole_word_split (k d c : Nat) (x : List Bool) :
    List.replicate (deadline k d c x) false =
      guardWord k d c x ++ false ::
        List.replicate (ULogTernaryCountedSourceDelimiter.deadline x.length) false := by
  unfold deadline guardWord
  rw [Nat.add_assoc, show 2 + ULogTernaryCountedSourceDelimiter.deadline x.length =
    ULogTernaryCountedSourceDelimiter.deadline x.length + 2 by omega,
    List.replicate_add, List.replicate_succ, List.replicate_succ]
  simp

theorem active_capacity_necessary (k d c : Nat) (hc : 0 < c) (x : List Bool) (C : Nat)
    (outer : List ULogProgram.Tape)
    (active : ActiveReadyRun (program d c) (List.replicate (deadline k d c x) false)
      0 (initial k d c x) C outer) :
    2 ^ k + (totalStates d c - 1) ≤ C := by
  rw [whole_word_split] at active
  have suffix := ULogFiniteTapeActiveReadySuffix.suffix_of_resource_run (program d c)
    (guardWord k d c x)
    (false :: List.replicate (ULogTernaryCountedSourceDelimiter.deadline x.length) false)
    0 (prefixHead k d c x) (initial k d c x) (guard k d c x) C (C - 2 ^ k)
    outer (outer.drop 1) active (actual_guard_resources k d c hc x C outer)
  have ready := ULogFiniteTapeActiveReadySuffix.head_ready suffix
  have capacity := ready.state_le_capacity
  change (guard k d c x).state.val ≤ C - 2 ^ k at capacity
  rw [actual_guard_state] at capacity
  have positive : 0 < totalStates d c - 1 := by
    have h := prefix_states_ge3 d c
    unfold totalStates ULogFiniteTapeGuardedStageComposition.stateCount
    omega
  omega

theorem full_active_ready_iff (k d c : Nat) (hc : 0 < c) (x : List Bool) (C : Nat)
    (tail : List ULogProgram.Tape) :
    ActiveReadyRun (program d c) (List.replicate (deadline k d c x) false)
        0 (initial k d c x) C (MStarConcreteAlphabet.work :: tail) ↔
      2 ^ k + (totalStates d c - 1) ≤ C := by
  constructor
  · exact active_capacity_necessary k d c hc x C _
  · intro capacity
    obtain ⟨_, _, _, _, _, ready⟩ := ULogTernaryGuardedPumpDelimiterSpace.every_raw_ready
      k d c hc x (List.replicate (deadline k d c x) false)
      (finalHead k d c x) (final k d c x) (actual_run k d c hc x)
    exact (ready C tail capacity).1

end PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterResources
