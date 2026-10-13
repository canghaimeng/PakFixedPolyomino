import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
import PakFixedPolyomino.ULogTernaryRetainedPumpSpaceBounds

/-! Sharp numbers of actual boundary extensions for EVERY raw retained
pump prefix. The final internally built run attains one left extension and
2^k right extensions. The table is the actual ternary repair. Physical frame
clock, time and minimum capacity remain separate. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpGrowthBounds

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedPumpCounts

theorem initial_edges (k : Nat) (source : List Bool) (head : Int) :
    leftEdge head (initial k source) = head ∧
      rightEdge head (initial k source) = head + (k + source.length : Nat) := by
  cases k <;>
    simp [initial, ULogTernaryRetainedCounterPump.initial,
      ULogTernaryRetainedCounterPump.fromCells, leftEdge, rightEdge,
      ULogTernaryRetainedCounterPump.cells, List.replicate_succ] <;> omega

theorem final_edges (k : Nat) (source : List Bool) :
    leftEdge k (final k source) = -1 ∧
      rightEdge k (final k source) = (k + source.length + 2 ^ k : Nat) := by
  simp [final, ULogTernaryRetainedCounterPump.fromCells, leftEdge, rightEdge,
    ULogTernaryRetainedCounterPump.cells]
  omega

theorem every_growth_bound (k : Nat) (source : List Bool) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hrun : run ULogTernaryRetainedCounterPump.program 2 w head (initial k source) = some (hf, zf)) :
    ∃ lg rg, GrowthRun ULogTernaryRetainedCounterPump.program 2 w head
      (initial k source) hf zf lg rg ∧ lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
      cellCount zf = cellCount (initial k source) + lg + rg := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run ULogTernaryRetainedCounterPump.program 2
    w head hf (initial k source) zf hrun
  have hp : (0 : Int) ≤ (2 ^ k : Nat) := Nat.cast_nonneg _
  have he := initial_edges k source head
  have hb := every_run_extents ULogTernaryRetainedCounterPump.program 2 w head hf
    (head - 1) (head + (k + source.length + 2 ^ k : Nat))
    (initial k source) zf (by rw [he.1]; omega) (by rw [he.2]; omega)
    (fun v h out hv => (ULogTernaryRetainedPumpSpaceBounds.every_raw_prefix_space
      k source head v h out hv).2) hrun
  have hl := hg.exact_ledger
  rw [he.1] at hl
  rw [he.2] at hl
  refine ⟨lg, rg, hg, ?_, ?_, hl.2.2.1⟩ <;> omega

theorem final_growth (k : Nat) (source : List Bool) :
    GrowthRun ULogTernaryRetainedCounterPump.program 2
      (List.replicate (deadline k source) false) 0 (initial k source)
      k (final k source) 1 (2 ^ k) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run ULogTernaryRetainedCounterPump.program 2
    (List.replicate (deadline k source) false) 0 k (initial k source)
    (final k source) (encoded_zipper_run k source)
  have hl := hg.exact_ledger
  have hi := initial_edges k source 0
  have hf := final_edges k source
  rw [hi.1, hf.1] at hl
  rw [hi.2, hf.2] at hl
  have hlg : lg = 1 := by omega
  have hrg : rg = 2 ^ k := by omega
  simpa only [hlg, hrg] using hg

theorem retained_growth_spec :
    (∀ (k : Nat) (source : List Bool) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      run ULogTernaryRetainedCounterPump.program 2 w head (initial k source) = some (hf, zf) →
      ∃ lg rg, GrowthRun ULogTernaryRetainedCounterPump.program 2 w head
        (initial k source) hf zf lg rg ∧ lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
        cellCount zf = cellCount (initial k source) + lg + rg) ∧
    (∀ (k : Nat) (source : List Bool),
      GrowthRun ULogTernaryRetainedCounterPump.program 2
        (List.replicate (deadline k source) false) 0 (initial k source)
        k (final k source) 1 (2 ^ k)) :=
  ⟨every_growth_bound, final_growth⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpGrowthBounds
