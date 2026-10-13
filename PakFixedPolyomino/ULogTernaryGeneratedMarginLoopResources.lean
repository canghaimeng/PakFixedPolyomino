import PakFixedPolyomino.ULogTernaryGeneratedMarginLoop

/-! The executed compact entry/feedback caller has exactly the entry's
directional growth. Its actual state count is charged in sufficient
readiness. Sharp exclusion of smaller physical capacities is separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginLoopResources
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open StandardNondeterministicMachine (Machine)
open ULogTernaryGeneratedMarginLoop
variable {ns nt : Nat}

set_option maxHeartbeats 1000000 in
theorem initial_edges (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    leftEdge 0 (initial nt p x) = 0 ∧ rightEdge 0 (initial nt p x) =
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source (depth nt p) (seed nt p) x).length : Nat) := by
  have hi := ULogTernaryGuardedPumpDelimiterSpace.initial_edges
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) (depth nt p) (seed nt p) x
  simpa only [initial, ULogFiniteTapeGuardedStageComposition.leftConfig,
    ULogTernaryGeneratedMarginEntry.compactInitial, ULogTernaryGeneratedMarginEntry.initial,
    ULogTernaryGeneratedMarginEntry.sealedInitial, ULogTernaryGeneratedHeadedSourceReturn.initial,
    ULogTernaryGeneratedHeadedSourceExpansion.initial, ULogFiniteTapeStageComposition.leftConfig,
    leftEdge, rightEdge, depth, seed] using hi

theorem final_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    leftEdge (head nt p x) (final M p x) = -1 ∧
    rightEdge (head nt p x) (final M p x) =
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source (depth nt p) (seed nt p) x).length +
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 : Nat) := by
  have he := ULogTernaryGeneratedMarginEntryResources.final_edges (ULogTernaryMarginMarkedLayout.codes M)
    M.blank (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) (depth nt p) (seed nt p)
    (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x
    (ULogTernaryGeneratedMarginEntry.compact_pool_fits nt p x)
  have hg := ULogTernaryBalancedBlankLoop.actual_growth (Nat.zero_lt_of_lt M.blank.isLt) M.blank
    (ULogTernaryGeneratedMarginEntry.correctedBits (ULogTernaryMarginMarkedLayout.codes M) M.blank x)
    (under nt p x) [] (pool nt p x) (head nt p x)
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  rw [← second_start M p x] at hl hr
  have left_same : leftEdge (head nt p x) (final M p x) =
      leftEdge (head nt p x) (ULogTernaryGeneratedMarginEntry.compactFinal
        (ULogTernaryMarginMarkedLayout.codes M) M.blank p x) := by
    simpa only [final, ULogFiniteTapeGuardedStageComposition.rightConfig,
      ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded, leftEdge, Nat.cast_zero, sub_zero,
      pool, residue, ULogTernaryGeneratedMarginSourceCounts.copies,
      ULogTernaryMarginReserveBudget.iterations, ULogTernaryBalancedBlankLoop.K,
      ULogTernaryMarginReserveBudget.pairWidth, ULogTernaryMarginReserveBudget.residue,
      ULogTernaryGeneratedMarginSourceClock.reserve] using hl
  have right_same : rightEdge (head nt p x) (final M p x) =
      rightEdge (head nt p x) (ULogTernaryGeneratedMarginEntry.compactFinal
        (ULogTernaryMarginMarkedLayout.codes M) M.blank p x) := by
    simpa only [final, ULogFiniteTapeGuardedStageComposition.rightConfig,
      ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded, rightEdge, Nat.cast_zero, add_zero,
      pool, residue, ULogTernaryGeneratedMarginSourceCounts.copies,
      ULogTernaryMarginReserveBudget.iterations, ULogTernaryBalancedBlankLoop.K,
      ULogTernaryMarginReserveBudget.pairWidth, ULogTernaryMarginReserveBudget.residue,
      ULogTernaryGeneratedMarginSourceClock.reserve] using hr
  rw [left_same, right_same]
  simpa only [head, ULogTernaryGeneratedMarginEntry.compactFinal,
    ULogTernaryGeneratedMarginSourceClock.reserve, depth, seed] using he

theorem actual_growth (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    GrowthRun (program M p) 2 (List.replicate (deadline M p x) false) 0 (initial nt p x)
      (head nt p x) (final M p x) 1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program M p) 2 _ 0 _ _ _ (actual_run M p x)
  have hi := initial_edges nt p x
  have hf := final_edges M p x
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  rw [hi.1, hf.1] at hl
  rw [hi.2, hf.2] at hr
  have hlg : lg = 1 := by omega
  have hrg : rg = ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
    push_cast at hr
    omega
  simpa only [hlg, hrg] using hg

theorem every_raw_growth (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt p) 3}
    (hw : run (program M p) 2 w 0 (initial nt p x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program M p) 2 w 0 (initial nt p x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
  obtain ⟨hfalse, hlen⟩ := every_raw M p x hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program M p) 2 w 0 hf (initial nt p x) out hw
  have split : List.replicate (deadline M p x) false =
      w ++ List.replicate (deadline M p x - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  have full := actual_growth M p x
  have le := ULogTernaryOneHotBlockWriter.growth_append_le (by simpa [split] using full) hg
  exact ⟨lg, rg, hg, le⟩

theorem every_raw_ready (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt p) 3}
    (hw : run (program M p) 2 w 0 (initial nt p x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program M p) 2 w 0 (initial nt p x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 ∧
      ∀ C tail, ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states nt p - 1) ≤ C →
        ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program M p)
          w 0 (initial nt p x) C (MStarConcreteAlphabet.work :: tail) ∧
        ULogFiniteTapePhysicalResourceLedger.resourceRun (program M p) 2
          w 0 (initial nt p x) C (MStarConcreteAlphabet.work :: tail) =
            some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, growth, hl, hr⟩ := every_raw_growth M p x hw
  refine ⟨lg, rg, growth, hl, hr, ?_⟩
  intro C tail capacity
  refine ⟨?_, ULogFiniteTapePhysicalResourceLedger.actual_resource_run growth C
    (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly M p) C (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly M p) C tail (by omega)

theorem generated_margin_loop_resource_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    GrowthRun (program M p) 2 (List.replicate (deadline M p x) false) 0 (initial nt p x)
      (head nt p x) (final M p x) 1 (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) ∧
    (∀ w hf out, run (program M p) 2 w 0 (initial nt p x) = some (hf, out) →
      ∃ lg rg, GrowthRun (program M p) 2 w 0 (initial nt p x) hf out lg rg ∧
        lg ≤ 1 ∧ rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 ∧
        ∀ C tail, ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states nt p - 1) ≤ C →
          ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program M p)
            w 0 (initial nt p x) C (MStarConcreteAlphabet.work :: tail) ∧
          ULogFiniteTapePhysicalResourceLedger.resourceRun (program M p) 2
            w 0 (initial nt p x) C (MStarConcreteAlphabet.work :: tail) =
              some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg)) :=
  ⟨actual_growth M p x, fun _ _ _ hw => every_raw_ready M p x hw⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginLoopResources
