import PakFixedPolyomino.ULogTernaryGuardedPumpSentinel
import PakFixedPolyomino.ULogTernaryRetainedPumpGrowthBounds
import PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness

/-! EVERY raw prefix of the actual pump/parser bytecode has the pump's
same occupied-cell peak and boundary-extension reserves. The proof uses
raw stage inversion and operational parser prefixes, not a final-to-prefix
inference. Active interpreter readiness charges only literal extensions;
physical clock execution/time/minimum capacity remain separate. -/

namespace PakFixedPolyomino.ULogTernaryGuardedPumpSentinelSpace

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeDeterministicFrameReadiness
open ULogTernaryGuardedPumpSentinel

def peak (k d c : Nat) (x : List Bool) : Nat := k + (source d c x).length + 2 ^ k + 2

theorem guard_cell_count (blank : Fin 3) (z : BoundedConfig 10 3) (hr : z.right ≠ []) :
    cellCount (ULogFiniteTapeGuardedStageComposition.guardConfig (ms := parserStates d c)
      blank .right z) = cellCount z := by
  cases he : z.right with
  | nil => exact (hr he).elim
  | cons a rest =>
      simp [ULogFiniteTapeGuardedStageComposition.guardConfig,
        ULogFiniteTapeGuardedStageComposition.leftConfig, applyBounded, he, cellCount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pump_final_right_nonempty (k : Nat) (bs : List Bool) :
    (ULogTernaryRetainedPumpCounts.final k bs).right ≠ [] := by
  intro h
  have he := congrArg List.length h
  simp [ULogTernaryRetainedPumpCounts.final, ULogTernaryRetainedCounterPump.fromCells] at he

theorem every_raw_space (k d c : Nat) (hcseed : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    cellCount out ≤ peak k d c x ∧ -1 ≤ hf ∧ hf ≤ (k + (source d c x).length + 2 ^ k : Nat) := by
  have hsplit := ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
    ULogTernaryRetainedCounterPump.program (ULogTernaryParserLeftSentinel.program d c)
    (by omega) (parserStates_ge3 d c) .right (2 : Fin 3) ULogTernaryRetainedPumpCounts.program_falseOnly
    (ULogTernaryRetainedPumpCounts.deadline k (source d c x)) 0 k
    (ULogTernaryRetainedCounterPump.initial k (source d c x))
    (ULogTernaryRetainedPumpCounts.final k (source d c x))
    (ULogTernaryRetainedPumpCounts.encoded_zipper_run k (source d c x)) rfl w hf out hw
  rcases hsplit with ⟨_, zp, hp, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · have hs := ULogTernaryRetainedPumpSpaceBounds.every_raw_prefix_space
      k (source d c x) 0 w hf zp hp
    simpa [cellCount, ULogFiniteTapeGuardedStageComposition.leftConfig, peak,
      ULogTernaryRetainedPumpSpaceBounds.peak] using hs
  · have hs := ULogTernaryRetainedPumpSpaceBounds.every_raw_prefix_space
      k (source d c x) 0
      (List.replicate (ULogTernaryRetainedPumpCounts.deadline k (source d c x)) false)
      k (ULogTernaryRetainedPumpCounts.final k (source d c x))
      (ULogTernaryRetainedPumpCounts.encoded_zipper_run k (source d c x))
    have hc := guard_cell_count (d := d) (c := c) (2 : Fin 3)
      (ULogTernaryRetainedPumpCounts.final k (source d c x))
      (pump_final_right_nonempty k (source d c x))
    have hR : 0 < 2 ^ k := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      simpa [peak, ULogTernaryRetainedPumpSpaceBounds.peak, cellCount] using hs.1
    · change (-1 : Int) ≤ (k : Int) + 1
      omega
    · change (k : Int) + 1 ≤ (k + (source d c x).length + 2 ^ k : Nat)
      omega
  · rw [handoff_start] at hq
    have hq' : run (ULogTernaryParserLeftSentinel.program d c) 2 v ((k : Int) + 1)
        (parserInitial k d c x) = some (hf, zq) := by
      simpa [FiniteOneTapeSemantics.moveHead] using hq
    have hs := ULogTernaryParserLeftSentinel.every_raw_space d c x
      (parserLeft k) (List.replicate (2 ^ k) 0) hcseed ((k : Int) + 1) v hf zq hq'
    have hsrc : (source d c x).length =
        (ULogTernaryNestedHeaderParser.header d c x).length + 2 * x.length + 1 := by
      simp [source, ULogTernaryNestedHeaderParser.nested_length,
        ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
    have hc : cellCount (ULogFiniteTapeGuardedStageComposition.rightConfig (ns := 10) zq) =
        peak k d c x := by
      simpa [cellCount, ULogFiniteTapeGuardedStageComposition.rightConfig,
        ULogTernaryNestedHeaderParserSpace.cellCount, parserLeft, peak, source,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.2.2
    refine ⟨hc.le, ?_, ?_⟩
    · have hl := hs.1
      omega
    · have hr := hs.2.1
      have hR : (0 : Int) ≤ (2 ^ k : Nat) := Nat.cast_nonneg _
      omega

theorem initial_edges (k d c : Nat) (x : List Bool) :
    leftEdge 0 (initial k d c x) = 0 ∧
      rightEdge 0 (initial k d c x) = (k + (source d c x).length : Nat) := by
  have h := ULogTernaryRetainedPumpGrowthBounds.initial_edges k (source d c x) 0
  simpa [leftEdge, rightEdge, initial, ULogFiniteTapeGuardedStageComposition.leftConfig] using h

theorem every_raw_growth (k d c : Nat) (hcseed : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program d c) 2 w 0 (initial k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program d c) 2 w 0 hf _ out hw
  have he := initial_edges k d c x
  have hp : (0 : Int) ≤ (2 ^ k : Nat) := Nat.cast_nonneg _
  have hb := every_run_extents (program d c) 2 w 0 hf (-1)
    (k + (source d c x).length + 2 ^ k : Nat) (initial k d c x) out
    (by rw [he.1]; omega) (by rw [he.2]; omega)
    (fun v h z hz => (every_raw_space k d c hcseed x v h z hz).2) hw
  have hl := hg.exact_ledger
  rw [he.1] at hl
  rw [he.2] at hl
  exact ⟨lg, rg, hg, by omega, by omega⟩

theorem every_raw_ready (k d c : Nat) (hcseed : 0 < c) (x w : List Bool) (hf : Int)
    (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w 0 (initial k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program d c) 2 w 0 (initial k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
      ∀ C tail, 2 ^ k + (totalStates d c - 1) ≤ C →
        ActiveReadyRun (program d c) w 0 (initial k d c x) C (MStarConcreteAlphabet.work :: tail) ∧
        resourceRun (program d c) 2 w 0 (initial k d c x) C (MStarConcreteAlphabet.work :: tail) =
          some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, hg, hlg, hrg⟩ := every_raw_growth k d c hcseed x w hf out hw
  refine ⟨lg, rg, hg, hlg, hrg, ?_⟩
  intro C tail hc
  refine ⟨?_, actual_resource_run hg C (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using actual_active_ready hg (program_falseOnly d c) C
        (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using actual_active_ready hg (program_falseOnly d c) C tail (by omega)

end PakFixedPolyomino.ULogTernaryGuardedPumpSentinelSpace
