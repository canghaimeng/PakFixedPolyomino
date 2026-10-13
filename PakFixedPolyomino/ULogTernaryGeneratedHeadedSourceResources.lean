import PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceExpansion

/-! Actual occupied cells and physical growth of every raw compact headed
source run. Child growth is zero; the only extensions are the audited pump.
This does not assert rejection at insufficient physical capacity. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceResources

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger ULogTernaryGeneratedHeadedSourceExpansion

theorem child_initial_count (nt k d c : Nat) (x : List Bool)
    (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    cellCount (ULogTernaryPreparedHeadedSourceExpansion.initial nt x (under k d c x) (buffer nt k x)) =
      cellCount (ULogTernaryGuardedPumpDelimiter.final k d c x) := by
  rw [← second_start nt k d c x hspace]
  simp [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded, cellCount]

theorem every_raw_space {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x := by
  have split := ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernaryPreparedHeadedSourceExpansion.program hnt codes)
    (prefix_states_ge d c) (prepared_states_ge nt) .stay (2 : Fin 3)
    (ULogTernaryGuardedPumpDelimiter.program_falseOnly d c)
    (ULogTernaryGuardedPumpDelimiter.deadline k d c x) 0
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
    (ULogTernaryGuardedPumpDelimiter.initial k d c x)
    (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · exact (ULogTernaryGuardedPumpDelimiterSpace.every_raw_space k d c hc x w hf zp hp).1
  · exact (ULogTernaryGuardedPumpDelimiterSpace.every_raw_space k d c hc x
      (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
      (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (ULogTernaryGuardedPumpDelimiter.final k d c x)
      (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)).1
  · rw [second_start nt k d c x hspace] at hq
    have raw := ULogTernaryPreparedHeadedSourceExpansion.every_raw hnt codes x
      (under k d c x) (buffer nt k x) (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) hq
    change cellCount zq ≤ _
    rw [raw.2.2.1, child_initial_count nt k d c x hspace]
    exact (ULogTernaryGuardedPumpDelimiterSpace.every_raw_space k d c hc x
      (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
      (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (ULogTernaryGuardedPumpDelimiter.final k d c x)
      (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)).1


theorem prefix_raw_extents (k d c : Nat) (hc : 0 < c) (x w : List Bool)
    (hf : Int) (out : BoundedConfig (prefixStates d c) 3)
    (hw : run (ULogTernaryGuardedPumpDelimiter.program d c) 2 w 0
      (ULogTernaryGuardedPumpDelimiter.initial k d c x) = some (hf, out)) :
    -1 ≤ leftEdge hf out ∧ rightEdge hf out ≤
      (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat) := by
  obtain ⟨lg, rg, hg, hl, hr⟩ := ULogTernaryGuardedPumpDelimiterSpace.every_raw_growth k d c hc x w hf out hw
  have edges := ULogTernaryGuardedPumpDelimiterSpace.initial_edges k d c x
  have ledger := hg.exact_ledger
  rw [edges.1, edges.2] at ledger
  exact ⟨by omega, by omega⟩

theorem every_raw_extents {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    -1 ≤ leftEdge hf out ∧ rightEdge hf out ≤
      (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat) := by
  have split := ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernaryPreparedHeadedSourceExpansion.program hnt codes)
    (prefix_states_ge d c) (prepared_states_ge nt) .stay (2 : Fin 3)
    (ULogTernaryGuardedPumpDelimiter.program_falseOnly d c)
    (ULogTernaryGuardedPumpDelimiter.deadline k d c x) 0
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
    (ULogTernaryGuardedPumpDelimiter.initial k d c x)
    (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x) w hf out hw
  have full := prefix_raw_extents k d c hc x
    (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · exact prefix_raw_extents k d c hc x w hf zp hp
  · exact full
  · rw [second_start nt k d c x hspace] at hq
    have raw := ULogTernaryPreparedHeadedSourceExpansion.every_raw hnt codes x
      (under k d c x) (buffer nt k x) (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) hq
    have ledger := raw.2.2.2.exact_ledger
    rw [← second_start nt k d c x hspace] at ledger
    simp only [Nat.cast_zero, sub_zero, add_zero] at ledger
    have hl : leftEdge hf zq = leftEdge (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
        (ULogTernaryGuardedPumpDelimiter.final k d c x) := by
      simpa [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded, leftEdge] using ledger.1
    have hr : rightEdge hf zq = rightEdge (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
        (ULogTernaryGuardedPumpDelimiter.final k d c x) := by
      simpa [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded, rightEdge] using ledger.2.1
    change -1 ≤ leftEdge hf zq ∧ rightEdge hf zq ≤ _
    rw [hl, hr]
    exact full

theorem every_raw_growth {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes d c) 2 w 0 hf _ out hw
  have edges := ULogTernaryGuardedPumpDelimiterSpace.initial_edges k d c x
  change leftEdge 0 (initial nt k d c x) = 0 ∧ rightEdge 0 (initial nt k d c x) =
    (k + (ULogTernaryGuardedPumpSentinel.source d c x).length : Nat) at edges
  have extents := every_raw_extents hnt codes k d c hc x hspace hw
  have ledger := hg.exact_ledger
  rw [edges.1, edges.2] at ledger
  exact ⟨lg, rg, hg, by omega, by omega⟩


theorem every_raw_ready {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
      ∀ C tail, 2 ^ k + (totalStates nt d c - 1) ≤ C →
        ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun
          (program hnt codes d c) w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) ∧
        ULogFiniteTapePhysicalResourceLedger.resourceRun
          (program hnt codes d c) 2 w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) =
            some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, growth, hlg, hrg⟩ := every_raw_growth hnt codes k d c hc x hspace hw
  refine ⟨lg, rg, growth, hlg, hrg, ?_⟩
  intro C tail capacity
  refine ⟨?_, ULogFiniteTapePhysicalResourceLedger.actual_resource_run growth C
    (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes d c) C (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes d c) C tail (by omega)

def guardWord (k d c : Nat) (x : List Bool) : List Bool :=
  List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false ++ [false]

def guard (nt k d c : Nat) (x : List Bool) : BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.guardConfig 2 .stay
    (ULogTernaryGuardedPumpDelimiter.final k d c x)

theorem actual_guard_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    run (program hnt codes d c) 2 (guardWord k d c x) 0 (initial nt k d c x) =
      some (ULogTernaryGuardedPumpDelimiter.finalHead k d c x, guard nt k d c x) := by
  unfold guardWord initial program
  rw [run_append, ULogFiniteTapeGuardedStageComposition.run_left
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernaryPreparedHeadedSourceExpansion.program hnt codes)
    (prefix_states_ge d c) (prepared_states_ge nt) .stay (2 : Fin 3) _ 0
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) _ _
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x), Option.bind_some]
  exact ULogFiniteTapeGuardedStageComposition.first_handoff_run _ _ _ _ .stay (2 : Fin 3) _ _
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x)

theorem actual_guard_state (nt k d c : Nat) (x : List Bool) :
    (guard nt k d c x).state.val = totalStates nt d c - 1 := by
  unfold guard
  rw [ULogFiniteTapeGuardedStageComposition.guard_state]
  simp [totalStates, ULogFiniteTapeGuardedStageComposition.stateCount]

theorem guard_cells (nt k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    cellCount (guard nt k d c x) = ULogTernaryGuardedPumpDelimiterSpace.peak k d c x := by
  change cellCount (ULogTernaryGuardedPumpDelimiter.final k d c x) = _
  change cellCount (ULogTernaryCountedSourceDelimiter.finalConfig x
    (ULogTernaryGuardedPumpDelimiter.under k d c x)
    (ULogTernaryGuardedPumpDelimiter.buffer k)) = _
  rw [ULogTernaryCountedSourceDelimiterSpace.occupied_final,
    ULogTernaryGuardedPumpDelimiterSpace.delimiter_occupied k d c x hc]

theorem actual_guard_growth {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    GrowthRun (program hnt codes d c) 2 (guardWord k d c x) 0 (initial nt k d c x)
      (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (guard nt k d c x) 1 (2 ^ k) := by
  obtain ⟨lg, rg, growth, hl, hr⟩ := every_raw_growth hnt codes k d c hc x hspace
    (actual_guard_run hnt codes k d c hc x)
  have count := growth.exact_ledger.2.2.1
  have initialCount : cellCount (initial nt k d c x) =
      k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 1 :=
    ULogTernaryGuardedPumpDelimiterResources.initial_cells k d c x
  rw [guard_cells nt k d c hc x hspace, initialCount] at count
  unfold ULogTernaryGuardedPumpDelimiterSpace.peak ULogTernaryGuardedPumpSentinelSpace.peak at count
  have hlg : lg = 1 := by omega
  have hrg : rg = 2 ^ k := by omega
  simpa [hlg, hrg] using growth

theorem whole_word_split (nt k d c : Nat) (x : List Bool) :
    List.replicate (deadline nt k d c x) false =
      guardWord k d c x ++ false ::
        List.replicate (ULogTernaryPreparedHeadedSourceExpansion.deadline nt x) false := by
  simp [deadline, guardWord, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

theorem full_active_ready_iff {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : reserveCost nt x ≤ 2 ^ k - 1)
    (C : Nat) (tail : List ULogProgram.Tape) :
    ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program hnt codes d c)
        (List.replicate (deadline nt k d c x) false) 0 (initial nt k d c x) C
        (MStarConcreteAlphabet.work :: tail) ↔ 2 ^ k + (totalStates nt d c - 1) ≤ C := by
  constructor
  · intro active
    rw [whole_word_split] at active
    have resources := ULogFiniteTapePhysicalResourceLedger.actual_resource_run
      (actual_guard_growth hnt codes k d c hc x hspace) C (MStarConcreteAlphabet.work :: tail)
    have suffix := ULogFiniteTapeActiveReadySuffix.suffix_of_resource_run (program hnt codes d c)
      (guardWord k d c x) (false :: List.replicate (ULogTernaryPreparedHeadedSourceExpansion.deadline nt x) false)
      0 (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (initial nt k d c x) (guard nt k d c x)
      C (C - 2 ^ k) (MStarConcreteAlphabet.work :: tail) ((MStarConcreteAlphabet.work :: tail).drop 1)
      active resources
    have capacity := (ULogFiniteTapeActiveReadySuffix.head_ready suffix).state_le_capacity
    change (guard nt k d c x).state.val ≤ C - 2 ^ k at capacity
    rw [actual_guard_state] at capacity
    have positive : 0 < totalStates nt d c - 1 := by
      have h := prefix_states_ge d c
      unfold totalStates ULogFiniteTapeGuardedStageComposition.stateCount
      omega
    omega
  · intro capacity
    obtain ⟨_, _, _, _, _, ready⟩ := every_raw_ready hnt codes k d c hc x hspace
      (actual_run hnt codes k d c hc x hspace)
    exact (ready C tail capacity).1


noncomputable def compactPeak (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpDelimiterSpace.peak (width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x

noncomputable def compactStates (nt : Nat) (p : Polynomial Nat) : Nat :=
  totalStates nt (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p))

theorem compact_every_raw_space {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input hnt codes p x)) w = some out) :
    out.leftRev.length + 1 + out.right.length ≤ compactPeak nt p x := by
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, he⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl
    (compactProgram hnt codes p) hw (head := 0)
  rw [← he]
  have hs := every_raw_space hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
    x (compact_reserve_fits nt p x) hz
  simpa [liftConfig, cellCount, compactPeak] using hs

/-- Actual raw growth and resource ledger, including the new maximum-state
visit. This is exact intermediate readiness, not physical low-capacity
acceptance inversion or the full square-counting theorem. -/
theorem generated_headed_resource_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes p) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input hnt codes p x)) w = some out →
      w = List.replicate w.length false ∧ w.length ≤ 2 ^ clockWidth nt p x ∧
        ULogBootstrapExecution.SemanticTapeSymbolsLtThree out ∧
        out.leftRev.length + 1 + out.right.length ≤ compactPeak nt p x) ∧
    (∀ x w hf out, run (compactProgram hnt codes p) 2 w 0 (compactInitial nt p x) = some (hf, out) →
      ∃ lg rg, GrowthRun (compactProgram hnt codes p) 2 w 0 (compactInitial nt p x) hf out lg rg ∧
        lg ≤ 1 ∧ rg ≤ 2 ^ width nt p x ∧
        ∀ C tail, 2 ^ width nt p x + (compactStates nt p - 1) ≤ C →
          ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (compactProgram hnt codes p)
            w 0 (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) ∧
          ULogFiniteTapePhysicalResourceLedger.resourceRun (compactProgram hnt codes p) 2 w 0
            (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) =
              some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg)) ∧
    (∀ x C tail, ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (compactProgram hnt codes p)
      (List.replicate (compactDeadline nt p x) false) 0 (compactInitial nt p x) C
      (MStarConcreteAlphabet.work :: tail) ↔ 2 ^ width nt p x + (compactStates nt p - 1) ≤ C) ∧
    (∀ x, ULogBootstrapExecution.decodeBinaryClock
      (List.replicate (clockWidth nt p x) (ULogAlphabet.ulogCore ULogAlphabet.clockZero) ++
        ULogAlphabet.ulogCore ULogAlphabet.clockOne :: [ULogAlphabet.ulogCore ULogAlphabet.clockSep]) =
      some (2 ^ clockWidth nt p x)) := by
  refine ⟨input_polyBitTime hnt codes p, ?_, ?_, ?_, ?_⟩
  · intro x w out hw
    have h := compact_every_raw hnt codes p x w out hw
    exact ⟨h.1, h.2.1, h.2.2, compact_every_raw_space hnt codes p x w out hw⟩
  · intro x w hf out hw
    exact every_raw_ready hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
      x (compact_reserve_fits nt p x) hw
  · intro x C tail
    exact full_active_ready_iff hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
      x (compact_reserve_fits nt p x) C tail
  · intro x
    exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth nt p x) []

end PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceResources
