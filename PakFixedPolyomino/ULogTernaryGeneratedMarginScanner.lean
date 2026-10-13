import PakFixedPolyomino.ULogTernaryGeneratedMarginLoop

/-! The actual compact loader and its real RIGHT highest-state handoff
to the existing fresh LEFT scanner entry. The old scanner start is kept
literally, including its possible terminal code. Counts across the live
handoff and physical capacity/time are separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScanner
open ULogCompiler ULogFiniteTapeZipperRun StandardNondeterministicMachine
variable {ns nt : Nat}

noncomputable def scannerState (M : Machine ns nt 2) :=
  ULogSourceObliviousBytecode.stateEquiv M (.atLeft M.start)

noncomputable def scannerStates (M : Machine ns nt 2) : Nat :=
  3 + Fintype.card (ULogSourceObliviousBytecode.Active M)

noncomputable def scannerProgram (M : Machine ns nt 2) : BoundedProgram (scannerStates M) 3 :=
  ULogFreshEntry.program (ULogSourceObliviousBytecode.boundedProgram M) (scannerState M)

theorem scanner_states_ge (M : Machine ns nt 2) : 3 ≤ scannerStates M := by
  unfold scannerStates; omega

noncomputable def states (M : Machine ns nt 2) (p : Polynomial Nat) : Nat :=
  ULogFiniteTapeGuardedStageComposition.stateCount
    (ULogTernaryGeneratedMarginLoop.states nt p) (scannerStates M)

theorem states_ge (M : Machine ns nt 2) (p : Polynomial Nat) : 3 ≤ states M p := by
  have := ULogTernaryGeneratedMarginLoop.states_ge nt p
  unfold states ULogFiniteTapeGuardedStageComposition.stateCount; omega

noncomputable def program (M : Machine ns nt 2) (p : Polynomial Nat) :
    BoundedProgram (states M p) 3 :=
  ULogFiniteTapeGuardedStageComposition.program
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right

noncomputable def initial (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    BoundedConfig (states M p) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig (ULogTernaryGeneratedMarginLoop.initial nt p x)

noncomputable def suffix (nt : Nat) (p : Polynomial Nat) (x : List Bool) : List (Fin 3) :=
  List.replicate (ULogTernaryGeneratedMarginLoop.residue nt p x) 0 ++ [2]

noncomputable def scannerInitial (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :=
  ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x
    (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x)

theorem handoff_start (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogFiniteTapeGuardedStageComposition.secondStart (scanner_states_ge M) (2 : Fin 3) .right
      (ULogTernaryGeneratedMarginLoop.final M p x) =
      ULogFreshEntryExteriorBoot.initial (scannerInitial M p x) := by
  have hf := ULogTernaryGeneratedMarginLoop.final_window M p x
  simp only [ULogFiniteTapeGuardedStageComposition.secondStart,
    ULogFreshEntryExteriorBoot.initial, scannerInitial,
    ULogTernaryGeneratedMarginSourceCounts.scannerInitial, suffix]
  rw [hf.2.1, hf.2.2.1, hf.2.2.2]
  simp only [List.append_assoc, List.cons_append, ULogFreshEntry.entryState]
  rfl

noncomputable def bootFinal (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    BoundedConfig (states M p) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig (ULogFreshEntry.insertConfig (scannerInitial M p x))

noncomputable def bootDeadline (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedMarginLoop.deadline M p x + 3

theorem load_and_boot (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    run (program M p) 2 (List.replicate (bootDeadline M p x) false) 0 (initial M p x) =
      some (ULogTernaryGeneratedMarginLoop.head nt p x, bootFinal M p x) := by
  have hboot := ULogFreshEntryExteriorBoot.actual_left_tick
    (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x)
    (ULogFreshEntryExteriorBoot.scanner_right_nonempty M p x
      (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x))
    (ULogTernaryGeneratedMarginLoop.head nt p x)
  have h := ULogFiniteTapeGuardedStageComposition.sequential_run
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right (2 : Fin 3)
    (List.replicate (ULogTernaryGeneratedMarginLoop.deadline M p x) false) [false]
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.head nt p x)
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    (ULogFreshEntry.insertConfig (scannerInitial M p x))
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) (by
      rw [handoff_start M p x]
      simpa [scannerProgram, scannerState, scannerStates, scannerInitial,
        ULogTernaryGeneratedMarginSourceCounts.scannerInitial, FiniteOneTapeSemantics.moveHead] using hboot)
  have hw : List.replicate (bootDeadline M p x) false =
      List.replicate (ULogTernaryGeneratedMarginLoop.deadline M p x) false ++ [false, false, false] := by
    simp [bootDeadline, List.replicate_add, -List.replicate_append_replicate]
  rw [hw]
  exact h

noncomputable def input (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap (program M p)
    (StandardBitCountedPolynomialPayload.payload
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x)

theorem input_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input M p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogPayloadClockBitWrapper.wrap_polyBitTime (program M p))

theorem initial_bounded (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    initial M p x = boundedInitial (⟨2, states_ge M p⟩ : Fin (states M p)) (0 : Fin 3) 1 2
      (ULogTernaryRetainedCounterPump.sourceInput
        (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
        (ULogTernaryGuardedPumpSentinel.source
          (ULogTernaryGeneratedMarginLoop.depth nt p) (ULogTernaryGeneratedMarginLoop.seed nt p) x)) := by
  unfold initial
  rw [ULogTernaryGeneratedMarginLoop.initial_bounded]
  cases ULogTernaryRetainedCounterPump.sourceInput
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
      (ULogTernaryGuardedPumpSentinel.source
        (ULogTernaryGeneratedMarginLoop.depth nt p) (ULogTernaryGeneratedMarginLoop.seed nt p) x) <;>
    simp [boundedInitial, ULogFiniteTapeGuardedStageComposition.leftConfig,
      ULogFiniteTapeGuardedStageComposition.leftState] <;> rfl

theorem start_input (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input M p x) = liftConfig (program M p) (initial M p x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitCountedPolynomialPayload.payload_layout,
    initial_bounded]
  exact (liftConfig_boundedInitial (program M p) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _).symm

theorem semantic_load_and_boot (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input M p x)) (List.replicate (bootDeadline M p x) false) =
      some (liftConfig (program M p) (bootFinal M p x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0, load_and_boot]
  rfl

theorem generated_margin_scanner_boot_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    StandardBitTime.PolyBitTime (input M p) ∧
    ULogSemantics.start (input M p x) = liftConfig (program M p) (initial M p x) ∧
    run (program M p) 2 (List.replicate (bootDeadline M p x) false) 0 (initial M p x) =
      some (ULogTernaryGeneratedMarginLoop.head nt p x, bootFinal M p x) ∧
    semanticRun (ULogSemantics.start (input M p x)) (List.replicate (bootDeadline M p x) false) =
      some (liftConfig (program M p) (bootFinal M p x)) ∧
    ULogFiniteTapeGuardedStageComposition.secondStart (scanner_states_ge M) (2 : Fin 3) .right
      (ULogTernaryGeneratedMarginLoop.final M p x) =
        ULogFreshEntryExteriorBoot.initial (scannerInitial M p x) :=
  ⟨input_polyBitTime M p, start_input M p x, load_and_boot M p x,
    semantic_load_and_boot M p x, handoff_start M p x⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScanner
