import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCounts
import PakFixedPolyomino.ULogTernaryGeneratedMarginLoopResources
import PakFixedPolyomino.ULogFiniteTapeActiveReadySuffix

/-! Every accepting ready run of the concrete whole program passes the
actual highest guard after all loader growth has been debited. This is a
necessary active-frame capacity bound, not yet arbitrary physical-run
inversion or a sufficient scanner readiness theorem. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginGuardCapacity
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger
open ULogFiniteTapeDeterministicFrameReadiness
open ULogTernaryGeneratedMarginScanner
open StandardNondeterministicMachine (Machine)
variable {ns nt : Nat}

noncomputable def guardWord (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :=
  List.replicate (ULogTernaryGeneratedMarginLoop.deadline M p x) false ++ [false]

noncomputable def guard (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    BoundedConfig (states M p) 3 :=
  ULogFiniteTapeGuardedStageComposition.guardConfig 2 .right
    (ULogTernaryGeneratedMarginLoop.final M p x)

theorem guard_prefix_run (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    run (program M p) 2 (guardWord M p x) 0 (initial M p x) =
      some (ULogTernaryGeneratedMarginLoop.head nt p x + 1, guard M p x) := by
  have hp := ULogFiniteTapeGuardedStageComposition.run_left
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right 2
    (List.replicate (ULogTernaryGeneratedMarginLoop.deadline M p x) false)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x)
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
  change run (ULogFiniteTapeGuardedStageComposition.program
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right) 2
    (guardWord M p x) 0
    (ULogFiniteTapeGuardedStageComposition.leftConfig
      (ULogTernaryGeneratedMarginLoop.initial nt p x)) =
      some (ULogTernaryGeneratedMarginLoop.head nt p x + 1,
        ULogFiniteTapeGuardedStageComposition.guardConfig 2 .right
          (ULogTernaryGeneratedMarginLoop.final M p x))
  rw [guardWord, run_append, hp, Option.bind_some]
  simpa only [guard, FiniteOneTapeSemantics.moveHead] using
    ULogFiniteTapeGuardedStageComposition.first_handoff_run
      (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
      (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right 2
      (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
      (ULogTernaryGeneratedMarginLoop.final_accepts M p x)

theorem guard_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x) = -1 ∧
    rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x) =
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source (ULogTernaryGeneratedMarginLoop.depth nt p)
          (ULogTernaryGeneratedMarginLoop.seed nt p) x).length +
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 : Nat) := by
  have he := ULogTernaryGeneratedMarginLoopResources.final_edges M p x
  have hw := (ULogTernaryGeneratedMarginLoop.final_window M p x).2.2.2
  have hr : (ULogTernaryGeneratedMarginLoop.final M p x).right ≠ [] := by rw [hw]; simp
  have hs : leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x) =
        leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.final M p x) ∧
      rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x) =
        rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.final M p x) := by
    cases h : (ULogTernaryGeneratedMarginLoop.final M p x).right with
    | nil => exact (hr h).elim
    | cons a rest =>
        simp [guard, ULogFiniteTapeGuardedStageComposition.guardConfig,
          ULogFiniteTapeGuardedStageComposition.leftConfig, applyBounded, h, leftEdge, rightEdge]
        omega
  exact ⟨hs.1.trans he.1, hs.2.trans he.2⟩

theorem guard_prefix_growth (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    GrowthRun (program M p) 2 (guardWord M p x) 0 (initial M p x)
      (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x)
      1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program M p) 2 _ 0 _ _ _ (guard_prefix_run M p x)
  have hi := ULogTernaryGeneratedMarginLoopResources.initial_edges nt p x
  have hs : leftEdge 0 (initial M p x) = 0 ∧ rightEdge 0 (initial M p x) =
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source (ULogTernaryGeneratedMarginLoop.depth nt p)
          (ULogTernaryGeneratedMarginLoop.seed nt p) x).length : Nat) := by
    simpa only [initial, ULogFiniteTapeGuardedStageComposition.leftConfig, leftEdge, rightEdge] using hi
  have he := guard_edges M p x
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  rw [hs.1, he.1] at hl
  rw [hs.2, he.2] at hr
  have hlg : lg = 1 := by omega
  have hrg : rg = ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
    push_cast at hr
    omega
  simpa only [hlg, hrg] using hg

theorem accepting_ready_capacity (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (hw : run (program M p) 2 w 0 (initial M p x) = some (hf, out)) (ha : out.state.val = 0)
    (C : Nat) (outer : List ULogProgram.Tape)
    (ready : ActiveReadyRun (program M p) w 0 (initial M p x) C outer) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C := by
  obtain ⟨v, zq, he, _, _, _⟩ := ULogFiniteTapeGuardedStageLeafCounts.accepting_whole_split
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) w hf out hw ha
  have hp := actual_resource_run (guard_prefix_growth M p x) C outer
  have he' : w = guardWord M p x ++ false :: v := by simp [guardWord, he]
  rw [he'] at ready
  have tail := ULogFiniteTapeActiveReadySuffix.suffix_of_resource_run (program M p)
    (guardWord M p x) (false :: v) 0 (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
    (initial M p x) (guard M p x) C
    (C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1)) outer (outer.drop 1) ready hp
  have hc := ULogFiniteTapeGuardedStageComposition.guard_capacity_necessary
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.final M p x)
    (C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1)) (outer.drop 1)
    (ULogFiniteTapeActiveReadySuffix.head_ready tail)
  change states M p - 1 ≤ C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) at hc
  have hstates := states_ge M p
  omega

theorem shortage_no_ready_accept (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (hC : C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1))
    (outer : List ULogProgram.Tape) :
    ¬ ∃ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) ∧
      out.state.val = 0 ∧ ActiveReadyRun (program M p) w 0 (initial M p x) C outer := by
  rintro ⟨w, hf, out, hw, ha, ready⟩
  exact (Nat.not_le_of_gt hC) (accepting_ready_capacity M p x w hf out hw ha C outer ready)

theorem generated_margin_guard_capacity_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    run (program M p) 2 (guardWord M p x) 0 (initial M p x) =
      some (ULogTernaryGeneratedMarginLoop.head nt p x + 1, guard M p x) ∧
    GrowthRun (program M p) 2 (guardWord M p x) 0 (initial M p x)
      (ULogTernaryGeneratedMarginLoop.head nt p x + 1) (guard M p x)
      1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) ∧
    (∀ C outer, resourceRun (program M p) 2 (guardWord M p x) 0 (initial M p x) C outer =
      some (ULogTernaryGeneratedMarginLoop.head nt p x + 1, guard M p x,
        C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1), outer.drop 1)) ∧
    (∀ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) →
      out.state.val = 0 → ∀ C outer,
        ActiveReadyRun (program M p) w 0 (initial M p x) C outer →
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) ∧
    (∀ C, C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) →
      ∀ outer, ¬ ∃ w hf out,
        run (program M p) 2 w 0 (initial M p x) = some (hf, out) ∧ out.state.val = 0 ∧
        ActiveReadyRun (program M p) w 0 (initial M p x) C outer) :=
  ⟨guard_prefix_run M p x, guard_prefix_growth M p x,
    actual_resource_run (guard_prefix_growth M p x),
    accepting_ready_capacity M p x, shortage_no_ready_accept M p x⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginGuardCapacity
