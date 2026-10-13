import PakFixedPolyomino.ULogFiniteTapeSelectedMicroInverse
import PakFixedPolyomino.ULogTernaryGeneratedMarginSelectedGuardCapacity
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPhysicalCounts
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapShortage

/-! ALL capacity bands of the actual OWN input. Every raw accepting word
internally supplies selected-action readiness, hence crosses the real highest
guard with enough capacity. Below the sharp threshold there are no physical
accepting words; above it the already-proved ALL-word count/time identity
applies. Microtime begins at the already-copied qStart core. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCapacityMicroCounts
open ULogCompiler ULogFiniteTapeZipperRun ULogBootstrapExecution ULogProgram
open ULogFiniteTapeCapacityReadiness ULogConcreteSlotMicroExpansion
open ULogTernaryGeneratedMarginScanner ULogTernaryGeneratedMarginScannerBootstrapFrame
open ULogTernaryGeneratedMarginScannerBootstrapShortage
open ULogTernaryGeneratedMarginScannerAllPhysicalCounts
open ULogTernaryGeneratedMarginScannerPhysicalFuel ULogConcreteMicroTimeCounts
open ULogFiniteTapeNondeterministicMicroCounts (RawAcceptingMicroWords)
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
open MStarParserExecution (Zipper)
variable {ns nt : Nat}

theorem initial_state_two (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (initial M p x).state.val = 2 := by
  rw [initial_bounded]
  cases ULogTernaryRetainedCounterPump.sourceInput
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
      (ULogTernaryGuardedPumpSentinel.source (ULogTernaryGeneratedMarginLoop.depth nt p)
        (ULogTernaryGeneratedMarginLoop.seed nt p) x) <;> rfl

set_option maxHeartbeats 1000000 in
theorem whole_selected_micro_inverse (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (C : Nat) (capacity : 2 ≤ C) (tail : List Tape)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frame M p x C tail).encode labels (.accepted tape)) :
    ∃ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) ∧
      out.state.val = 0 ∧ CapacityReadyRun (program M p) 2 w 0 (initial M p x) C ∧
      SlotMicroExpansion (frame M p x C tail).encode w labels (.accepted tape) := by
  refine ULogFiniteTapeSelectedMicroInverse.every_accepting_micro_path_reflects_selected
    (program M p) (ULogTernaryGeneratedMarginScannerCompiledNonempty.compiled_program_nonempty M p)
    (ULogTernaryGeneratedMarginScannerCounts.budget M p x) 0 (initial M p x) C
    (MStarConcreteAlphabet.work :: tail)
    (ULogFiniteTapeAllCapacityOuterReadiness.whole_all_capacity_outer_ready M p x ht C tail)
    (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht)
    (initial_not_halted M p x) (by rw [initial_state_two]; exact capacity)
    (frame M p x C tail) ?_ rfl rfl clock_separator_passive
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x)
    (frame_clock_decode M p x C tail)
    (ULogTernaryGeneratedMarginScannerClockSlack.budget_lt_clock M p x) labels tape raw
  simpa only [frame] using (start_input M p x)

theorem frame_accepting_sharp_capacity_necessary
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (capacity : 2 ≤ C)
    (tail : List Tape) (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frame M p x C tail).encode labels (.accepted tape)) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C := by
  obtain ⟨w, hf, out, word, accept, ready, _⟩ :=
    whole_selected_micro_inverse M p x ht C capacity tail labels tape raw
  exact ULogTernaryGeneratedMarginSelectedGuardCapacity.accepting_selected_capacity_necessary
    M p x w hf out word accept C ready

theorem bootstrap_accepting_sharp_capacity_necessary
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C := by
  have capacity := bootstrap_accepting_semantic_capacity_ge_two M p x C labels tape raw
  obtain ⟨rest, _, after⟩ :=
    (ULogBootstrapMicroPrefix.accepting_path_split_iff
      (actual_bootstrap_prefix M p x C capacity) rfl labels tape).1 raw
  exact frame_accepting_sharp_capacity_necessary M p x ht C capacity
    (outerTail M p x) rest tape after

theorem bootstrap_shortage_no_accept
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (shortage : C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1))
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) : False :=
  (Nat.not_le_of_gt shortage)
    (bootstrap_accepting_sharp_capacity_necessary M p x ht C labels tape raw)

theorem bootstrap_shortage_raw_card_zero
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (shortage : C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1)) :
    Nat.card (RawAcceptingMicroWords (bootstrapStart M p x C)) = 0 := by
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨?_⟩
  intro word
  obtain ⟨tape, raw⟩ := word.property
  exact bootstrap_shortage_no_accept M p x ht C shortage word.val tape raw

theorem bootstrap_shortage_time_count_zero
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C T : Nat)
    (shortage : C < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1)) :
    acceptingMicroPaths T (bootstrapStart M p x C) = 0 := by
  unfold acceptingMicroPaths
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨?_⟩
  intro word
  obtain ⟨tape, raw⟩ := word.property.2
  exact bootstrap_shortage_no_accept M p x ht C shortage word.val tape raw

theorem all_capacity_bootstrap_raw_length_le
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) :
    labels.length ≤ totalPhysicalFuelBound M p x :=
  all_bootstrap_raw_length_le M p x ht C
    (bootstrap_accepting_sharp_capacity_necessary M p x ht C labels tape raw) labels tape raw

theorem all_capacity_bootstrap_time_count
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C T : Nat)
    (time : totalPhysicalFuelBound M p x ≤ T) :
    acceptingMicroPaths T (bootstrapStart M p x C) =
      if ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C
      then acceptingCount M x (2 ^ p.eval x.length) else 0 := by
  split_ifs with capacity
  · exact (ordinary_bootstrap_time_count M p x ht C capacity T time).symm
  · exact bootstrap_shortage_time_count_zero M p x ht C T (by omega)

theorem all_capacity_physical_count_time_spec
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 ∧
    ∀ C, (∀ labels tape, ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape) →
      labels.length ≤ totalPhysicalFuelBound M p x) ∧
      ∀ T, totalPhysicalFuelBound M p x ≤ T →
        acceptingMicroPaths T (bootstrapStart M p x C) =
          if ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C
          then acceptingCount M x (2 ^ p.eval x.length) else 0 :=
  ⟨input_polyBitTime M p, total_physical_fuel_lt_copied_pow_nine M p x,
    fun C => ⟨all_capacity_bootstrap_raw_length_le M p x ht C,
      all_capacity_bootstrap_time_count M p x ht C⟩⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCapacityMicroCounts
