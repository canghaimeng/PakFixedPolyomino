import PakFixedPolyomino.ULogTernaryGeneratedMarginGuardCapacity
import PakFixedPolyomino.ULogSourceObliviousActiveReadiness
import PakFixedPolyomino.ULogFiniteTapeComposedUniformMoves
import PakFixedPolyomino.ULogFiniteTapeFreshAcceptingSplit

/-! The concrete whole compact loader/scanner has sharp ACTIVE frame
capacity on every accepting labelled logical word. The actual loader is
charged LG1/RG R+1, and the scanner adds no growth. This is an internal
resource theorem; arbitrary physical words and microtime remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerResources
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger
open ULogFiniteTapeDeterministicFrameReadiness (ActiveReadyRun)
open ULogFiniteTapeUniformMoveReadiness ULogFiniteTapeComposedUniformMoves
open ULogTernaryGeneratedMarginScanner
open StandardNondeterministicMachine
variable {ns nt : Nat}

theorem whole_same_moves (M : Machine ns nt 2) (p : Polynomial Nat) : SameMoves (program M p) :=
  guarded_same_moves _ _ _ _ .right
    (falseOnly_same_moves _ (ULogTernaryGeneratedMarginLoop.program_falseOnly M p))
    (fresh_same_moves _ _ (ULogSourceObliviousActiveReadiness.scanner_same_moves M))

set_option maxHeartbeats 1000000 in
theorem all_accepting_growth (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (hf : Int)
    (out : BoundedConfig (states M p) 3)
    (hw : run (program M p) 2 w 0 (initial M p x) = some (hf, out)) (ha : out.state.val = 0) :
    GrowthRun (program M p) 2 w 0 (initial M p x) hf out
      1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) := by
  obtain ⟨v, zq, _, hq, hqa, hout⟩ := ULogFiniteTapeGuardedStageLeafCounts.accepting_whole_split
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) w hf out hw ha
  rw [handoff_start] at hq
  change run (ULogFreshEntry.program (ULogSourceObliviousBytecode.boundedProgram M)
    (scannerInitial M p x).state) 2 v (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
    (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x)) = some (hf, zq) at hq
  obtain ⟨rest, old, _, hold, hoa, hconfig⟩ := ULogFiniteTapeFreshAcceptingSplit.accepting_split
    (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x)
    (ULogFreshEntryExteriorBoot.scanner_right_nonempty M p x _ _)
    (ULogTernaryGeneratedMarginLoop.head nt p x) hf v zq hq hqa
  have hlarge := ULogTernaryGeneratedMarginSourceCounts.radius_ge_time nt p x
  have hsource : RunsAtMost M x (ULogTernaryGeneratedMarginSourceCounts.radius nt p x) :=
    fun word z hz => (ht word z hz).trans hlarge
  have hold' := hold
  rw [scannerInitial, ULogTernaryGeneratedMarginSourceCounts.scanner_initial_eq] at hold'
  have growth := ULogSourceObliviousActiveReadiness.accepting_zero_growth_at M x _ hsource
    (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x) rest
    (ULogTernaryGeneratedMarginLoop.head nt p x) hf old hold' hoa
  have led := growth.exact_ledger
  rw [← ULogTernaryGeneratedMarginSourceCounts.scanner_initial_eq] at led
  change leftEdge hf old = leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) - 0 ∧
    rightEdge hf old = rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) + 0 ∧
    _ at led
  have init_edges := ULogTernaryGeneratedMarginLoopResources.initial_edges nt p x
  have final_edges := ULogTernaryGeneratedMarginLoopResources.final_edges M p x
  have window := ULogTernaryGeneratedMarginLoop.final_window M p x
  have same_edges : leftEdge hf out =
      leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.final M p x) ∧
    rightEdge hf out =
      rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.final M p x) := by
    rw [hout, hconfig]
    change leftEdge hf old = _ ∧ rightEdge hf old = _
    constructor
    · rw [led.1, sub_zero]
      simp only [leftEdge, scannerInitial, ULogTernaryGeneratedMarginSourceCounts.scannerInitial, window.2.1]
    · rw [led.2.1, add_zero]
      simp only [rightEdge, scannerInitial, ULogTernaryGeneratedMarginSourceCounts.scannerInitial,
        window.2.2.2, suffix, List.append_assoc, List.cons_append]
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program M p) 2 w 0 hf (initial M p x) out hw
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  have hi : leftEdge 0 (initial M p x) = 0 ∧ rightEdge 0 (initial M p x) =
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (ULogTernaryGuardedPumpSentinel.source (ULogTernaryGeneratedMarginLoop.depth nt p)
        (ULogTernaryGeneratedMarginLoop.seed nt p) x).length : Nat) := by
    simpa only [ULogTernaryGeneratedMarginScanner.initial, ULogFiniteTapeGuardedStageComposition.leftConfig, leftEdge, rightEdge] using init_edges
  rw [same_edges.1, final_edges.1, hi.1] at hl
  rw [same_edges.2, final_edges.2, hi.2] at hr
  have hlg : lg = 1 := by omega
  have hrg : rg = ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
    push_cast at hr
    omega
  simpa only [hlg, hrg] using hg

theorem accepting_capacity_iff (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (hf : Int)
    (out : BoundedConfig (states M p) 3)
    (hw : run (program M p) 2 w 0 (initial M p x) = some (hf, out)) (ha : out.state.val = 0)
    (C : Nat) (tail : List ULogProgram.Tape) :
    ActiveReadyRun (program M p) w 0 (initial M p x) C (MStarConcreteAlphabet.work :: tail) ↔
      ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C := by
  constructor
  · exact ULogTernaryGeneratedMarginGuardCapacity.accepting_ready_capacity M p x w hf out hw ha C _
  · intro hc
    simpa using actual_active_ready (all_accepting_growth M p x ht w hf out hw ha)
      (whole_same_moves M p) C tail hc

theorem scanner_accepting_resource_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    SameMoves (program M p) ∧
    ∀ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) → out.state.val = 0 →
      GrowthRun (program M p) 2 w 0 (initial M p x) hf out
        1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) ∧
      (∀ C tail, ActiveReadyRun (program M p) w 0 (initial M p x) C (MStarConcreteAlphabet.work :: tail) ↔
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) ∧
      (∀ C tail, resourceRun (program M p) 2 w 0 (initial M p x) C (MStarConcreteAlphabet.work :: tail) =
        some (hf, out, C - (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1), tail)) := by
  refine ⟨whole_same_moves M p, ?_⟩
  intro w hf out hw ha
  have hg := all_accepting_growth M p x ht w hf out hw ha
  exact ⟨hg, accepting_capacity_iff M p x ht w hf out hw ha,
    fun C tail => by simpa using actual_resource_run hg C (MStarConcreteAlphabet.work :: tail)⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerResources
