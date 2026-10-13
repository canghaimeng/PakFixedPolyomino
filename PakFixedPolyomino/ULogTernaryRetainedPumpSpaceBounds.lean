import PakFixedPolyomino.ULogTernaryRetainedPumpIterationSpace
import PakFixedPolyomino.ULogTernaryRetainedPumpInitializationSpace
import PakFixedPolyomino.ULogTernaryRetainedPumpCounts

/-! EVERY raw successful prefix from actual retained binary initialization.
The occupied decoded-cell peak is exact because the internally constructed
final run attains it. This is not a physical frame-capacity or interpreter
clock theorem: those resource models must separately be instantiated. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpSpaceBounds

open ULogCompiler ULogFiniteTapeZipperRun
open ULogTernaryRetainedCounterPump (fromCells cells cell)
open ULogTernaryRetainedPumpIteration (cells_replicate)
open ULogTernaryRetainedPumpCounts (initial finalConfig)
open ULogFiniteAlphabetDeterministicRuns

def peak (k : Nat) (source : List Bool) : Nat := k + source.length + 2 ^ k + 2

theorem every_raw_prefix_space (k : Nat) (source : List Bool) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hrun : run ULogTernaryRetainedCounterPump.program 2 w head (initial k source) = some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤ peak k source ∧
      head - 1 ≤ hf ∧ hf ≤ head + (k + source.length + 2 ^ k : Nat) := by
  have hp : 0 < 2 ^ k := by positivity
  by_cases hs : w.length ≤ 2 * k + 2
  · have hb := ULogTernaryRetainedPumpInitializationSpace.every_initial_prefix_space
      k source head w hf zf hs hrun
    dsimp only [peak]
    omega
  · have hw := successful_zipper_is_false (2 : Fin 3) ULogTernaryRetainedCounterPump.program
      ULogTernaryRetainedPumpCounts.program_falseOnly hrun
    rw [hw, ULogTernaryRetainedPumpIterationSpace.replicate_split w.length (2 * k + 2) (by omega),
      run_append, show run ULogTernaryRetainedCounterPump.program 2
        (List.replicate (2 * k + 2) false) head (initial k source) = _ from
          ULogTernaryRetainedPumpInitialization.initialization_run k source head,
      Option.bind_some] at hrun
    have hbody : run ULogTernaryRetainedCounterPump.program 2
        (List.replicate (w.length - (2 * k + 2)) false) head
        (fromCells 5 [2] (ULogTernaryRetainedCounterPump.data (List.replicate k false) source 0)) =
          some (hf, zf) := by
      simpa [ULogTernaryRetainedCounterPump.data, cells_replicate, cell] using hrun
    have hb := ULogTernaryRetainedPumpIterationSpace.every_loop_prefix_space
      (List.replicate k false) source 0 head _ hf zf hbody
    simpa [ULogTernaryRetainedPumpIterationSpace.capacity, ULogBinaryCounterValue.remaining_zero_bits,
      peak] using hb

theorem every_encoded_prefix_space (k : Nat) (source : List Bool)
    (w : List Bool) (out : ULogSemantics.Config)
    (hsem : semanticRun (ULogSemantics.start (ULogTernaryRetainedCounterPump.input k source)) w = some out) :
    out.leftRev.length + 1 + out.right.length ≤ peak k source := by
  rw [← ULogTernaryRetainedPumpCounts.initial_lift k source] at hsem
  obtain ⟨⟨hf, zf⟩, hzip, hlift⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl
    ULogTernaryRetainedCounterPump.program hsem (head := 0)
  have hc := (every_raw_prefix_space k source 0 w hf zf hzip).1
  rw [← hlift]
  simpa [liftConfig] using hc

theorem decoded_capacity_exact (k : Nat) (source : List Bool) (C : Nat) :
    (∀ w out, semanticRun (ULogSemantics.start (ULogTernaryRetainedCounterPump.input k source)) w = some out →
      out.leftRev.length + 1 + out.right.length ≤ C) ↔ peak k source ≤ C := by
  constructor
  · intro h
    have hc := h (List.replicate (ULogTernaryRetainedPumpCounts.deadline k source) false)
      (finalConfig k source) (ULogTernaryRetainedPumpCounts.encoded_semantic_run k source)
    simpa [peak, ULogTernaryRetainedPumpCounts.final_cell_count] using hc
  · intro h w out hw
    exact (every_encoded_prefix_space k source w out hw).trans h

theorem raw_encoded_peak_spec :
    (∀ (k : Nat) (source : List Bool) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      run ULogTernaryRetainedCounterPump.program 2 w head (initial k source) = some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤ peak k source ∧
        head - 1 ≤ hf ∧ hf ≤ head + (k + source.length + 2 ^ k : Nat)) ∧
    (∀ (k : Nat) (source : List Bool) (w : List Bool) (out : ULogSemantics.Config),
      semanticRun (ULogSemantics.start (ULogTernaryRetainedCounterPump.input k source)) w = some out →
      out.leftRev.length + 1 + out.right.length ≤ peak k source) ∧
    (∀ (k : Nat) (source : List Bool) (C : Nat),
      (∀ w out, semanticRun (ULogSemantics.start (ULogTernaryRetainedCounterPump.input k source)) w = some out →
        out.leftRev.length + 1 + out.right.length ≤ C) ↔ peak k source ≤ C) := by
  exact ⟨every_raw_prefix_space, every_encoded_prefix_space, decoded_capacity_exact⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpSpaceBounds
