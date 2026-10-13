import PakFixedPolyomino.ULogTernaryGeneratedMarginGuardCapacity
import PakFixedPolyomino.ULogFiniteTapeSelectedCapacitySuffix

/-! The real highest guard forces the sharp whole capacity from readiness
of selected actions only. A separate raw physical inverse must supply that
selected ledger; no physical shortage rejection is assumed here. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginSelectedGuardCapacity
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeCapacityReadiness
open ULogFiniteTapePhysicalResourceLedger ULogTernaryGeneratedMarginScanner
open ULogTernaryGeneratedMarginGuardCapacity
open StandardNondeterministicMachine (Machine)
variable {ns nt : Nat}

theorem accepting_selected_capacity_necessary (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) (C : Nat)
    (ready : CapacityReadyRun (program M p) 2 w 0 (initial M p x) C) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C := by
  obtain ⟨v, zq, split, _, _, _⟩ := ULogFiniteTapeGuardedStageLeafCounts.accepting_whole_split
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) w hf out word accepts
  have prefixRun := actual_resource_run (guard_prefix_growth M p x) C ([] : List ULogProgram.Tape)
  have split' : w = guardWord M p x ++ false :: v := by
    simp only [guardWord, split, List.append_assoc, List.cons_append, List.nil_append]
  rw [split'] at ready
  have tail := ULogFiniteTapeSelectedCapacitySuffix.suffix_of_resource_run (program M p)
    (guardWord M p x) (false :: v) 0 (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
    (initial M p x) (ULogTernaryGeneratedMarginGuardCapacity.guard M p x) C
    (C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1)) [] ([].drop 1) ready prefixRun
  have bound := ULogFiniteTapeSelectedCapacitySuffix.head_state_capacity tail
  have guardState : (ULogTernaryGeneratedMarginGuardCapacity.guard M p x).state.val = states M p - 1 := by
    simpa only [ULogTernaryGeneratedMarginGuardCapacity.guard, states,
      ULogFiniteTapeGuardedStageComposition.stateCount,
      Nat.add_sub_cancel] using ULogFiniteTapeGuardedStageComposition.guard_state
        (ms := scannerStates M) (2 : Fin 3) .right (ULogTernaryGeneratedMarginLoop.final M p x)
  rw [guardState] at bound
  have hs := states_ge M p
  omega

theorem shortage_no_selected_ready_accept (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat)
    (shortage : C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1)) :
    ¬ ∃ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) ∧
      out.state.val = 0 ∧ CapacityReadyRun (program M p) 2 w 0 (initial M p x) C := by
  rintro ⟨w, hf, out, word, accepts, ready⟩
  exact (Nat.not_le_of_gt shortage)
    (accepting_selected_capacity_necessary M p x w hf out word accepts C ready)

end PakFixedPolyomino.ULogTernaryGeneratedMarginSelectedGuardCapacity
