import PakFixedPolyomino.ULogTernaryGuardedPumpDelimiter

/-! ALL raw resource bounds for the actual generator-to-delimiter bytecode.
The last stage and both stay handoffs create no cells; the pump remains
responsible for the exact left/right extension reserves. Physical rejection
below the ready-capacity threshold and full-frame counts remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterSpace
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeDeterministicFrameReadiness
open ULogTernaryGuardedPumpDelimiter

def peak (k d c : Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpSentinelSpace.peak k d c x

theorem delimiter_occupied (k d c : Nat) (x : List Bool) (hc : 0 < c) :
    ULogTernaryCountedSourceDelimiterSpace.occupied x (under k d c x) (buffer k) =
      peak k d c x := by
  have hu := congrArg List.length
    (ULogTernaryParserLeftSentinel.real_left_cell d c x
      (ULogTernaryGuardedPumpSentinel.parserLeft k) hc)
  simp only [List.length_append, List.length_reverse,
    ULogTernaryNestedHeaderParser.cells_length, List.length_cons] at hu
  have hl : (ULogTernaryGuardedPumpSentinel.parserLeft k).length = k + 2 := by
    simp [ULogTernaryGuardedPumpSentinel.parserLeft]
  rw [hl] at hu
  have hs : (ULogTernaryGuardedPumpSentinel.source d c x).length =
      (ULogTernaryNestedHeaderParser.header d c x).length + 2 * x.length + 1 := by
    simp [ULogTernaryGuardedPumpSentinel.source, ULogTernaryNestedHeaderParser.nested_length,
      ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
  have hR : 0 < 2 ^ k := by positivity
  unfold ULogTernaryCountedSourceDelimiterSpace.occupied under buffer peak
    ULogTernaryGuardedPumpSentinelSpace.peak
  simp only [List.length_replicate]
  rw [hs]
  omega

theorem guard_cell_count (z : BoundedConfig (prefixStates d c) 3) :
    cellCount (ULogFiniteTapeGuardedStageComposition.guardConfig (ms := 24) 2 .stay z) =
      cellCount z := rfl

theorem every_raw_space (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    cellCount out ≤ peak k d c x ∧ -1 ≤ hf ∧
      hf ≤ (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat) := by
  have split := ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGuardedPumpSentinel.program d c) ULogTernaryCountedSourceDelimiter.program
    (prefix_states_ge3 d c) (by omega) .stay (2 : Fin 3)
    (ULogTernaryGuardedPumpSentinel.program_falseOnly d c)
    (ULogTernaryGuardedPumpSentinel.deadline k d c x) 0 (prefixHead k d c x)
    (ULogTernaryGuardedPumpSentinel.initial k d c x)
    (ULogTernaryGuardedPumpSentinel.final k d c x)
    (ULogTernaryGuardedPumpSentinel.actual_run k d c hc x)
    (ULogTernaryGuardedPumpSentinel.final_accepts k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · have old := ULogTernaryGuardedPumpSentinelSpace.every_raw_space k d c hc x w hf zp hp
    exact old
  · have old := ULogTernaryGuardedPumpSentinelSpace.every_raw_space k d c hc x
      (List.replicate (ULogTernaryGuardedPumpSentinel.deadline k d c x) false)
      (prefixHead k d c x) (ULogTernaryGuardedPumpSentinel.final k d c x)
      (ULogTernaryGuardedPumpSentinel.actual_run k d c hc x)
    rw [guard_cell_count]
    exact old
  · rw [handoff_start] at hq
    have raw := ULogTernaryCountedSourceDelimiterSpace.every_raw x (under k d c x)
      (buffer k) (prefixHead k d c x) hq
    have cells : cellCount (ULogFiniteTapeGuardedStageComposition.rightConfig
        (ns := prefixStates d c) zq) = peak k d c x :=
      raw.2.2.2.2.trans (delimiter_occupied k d c x hc)
    have hs : (ULogTernaryGuardedPumpSentinel.source d c x).length =
        (ULogTernaryNestedHeaderParser.header d c x).length + 2 * x.length + 1 := by
      simp [ULogTernaryGuardedPumpSentinel.source, ULogTernaryNestedHeaderParser.nested_length,
        ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
    have hR : 0 < 2 ^ k := by positivity
    have hlo := raw.2.2.1
    have hhi := raw.2.2.2.1
    unfold prefixHead at hlo hhi
    exact ⟨cells.le, by omega, by omega⟩

theorem initial_edges (k d c : Nat) (x : List Bool) :
    leftEdge 0 (initial k d c x) = 0 ∧
      rightEdge 0 (initial k d c x) =
        (k + (ULogTernaryGuardedPumpSentinel.source d c x).length : Nat) :=
  ULogTernaryGuardedPumpSentinelSpace.initial_edges k d c x

theorem every_raw_growth (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program d c) 2 w 0 (initial k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k := by
  obtain ⟨lg, rg, growth⟩ := every_actual_run (program d c) 2 w 0 hf _ out hw
  have edges := initial_edges k d c x
  have hp : (0 : Int) ≤ (2 ^ k : Nat) := Nat.cast_nonneg _
  have bounds := every_run_extents (program d c) 2 w 0 hf (-1)
    (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat)
    (initial k d c x) out (by rw [edges.1]; omega) (by rw [edges.2]; omega)
    (fun v h z hz => (every_raw_space k d c hc x v h z hz).2) hw
  have ledger := growth.exact_ledger
  rw [edges.1, edges.2] at ledger
  exact ⟨lg, rg, growth, by omega, by omega⟩

theorem every_raw_ready (k d c : Nat) (hc : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program d c) 2 w 0 (initial k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
      ∀ C tail, 2 ^ k + (totalStates d c - 1) ≤ C →
        ActiveReadyRun (program d c) w 0 (initial k d c x) C
          (MStarConcreteAlphabet.work :: tail) ∧
        resourceRun (program d c) 2 w 0 (initial k d c x) C
          (MStarConcreteAlphabet.work :: tail) =
            some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, growth, hlg, hrg⟩ := every_raw_growth k d c hc x w hf out hw
  refine ⟨lg, rg, growth, hlg, hrg, ?_⟩
  intro C tail capacity
  refine ⟨?_, actual_resource_run growth C (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using actual_active_ready growth (program_falseOnly d c) C
        (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using actual_active_ready growth (program_falseOnly d c) C tail (by omega)

end PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterSpace
