import PakFixedPolyomino.ULogTernaryBalancedBlankLoop
import PakFixedPolyomino.ULogFreshEntryExteriorBoot
import PakFixedPolyomino.ULogTernaryGeneratedMarginEntryResources

/-! Actual compact sealed entry followed by the actual exhausting margin
loop. Both children are instantiated internally. The local accept is to be
made live by the subsequent scanner guard; it is not the source acceptance. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginLoop
open ULogCompiler ULogFiniteTapeZipperRun
open StandardNondeterministicMachine
open ULogTernaryMarginMarkedLayout (codes)
open ULogTernaryGeneratedMarginSourceCounts (copies)
variable {ns nt : Nat}

noncomputable def depth (nt : Nat) (p : Polynomial Nat) : Nat :=
  ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
noncomputable def seed (nt : Nat) (p : Polynomial Nat) : Nat :=
  ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
noncomputable def entryStates (nt : Nat) (p : Polynomial Nat) : Nat :=
  ULogTernaryGeneratedMarginEntry.states nt (depth nt p) (seed nt p)

theorem entry_states_ge (nt : Nat) (p : Polynomial Nat) : 3 ≤ entryStates nt p := by
  have h := ULogTernaryGeneratedMarginEntry.sealed_states_ge nt (depth nt p) (seed nt p)
  unfold entryStates ULogTernaryGeneratedMarginEntry.states
    ULogFiniteTapeStageComposition.stateCount
  omega

theorem loop_states_ge (nt : Nat) : 3 ≤ ULogTernaryBalancedBlankLoop.loopStates nt := by
  have h := ULogTernaryBalancedBlankLoop.loop_ge nt
  omega

noncomputable def states (nt : Nat) (p : Polynomial Nat) : Nat :=
  ULogFiniteTapeGuardedStageComposition.stateCount (entryStates nt p)
    (ULogTernaryBalancedBlankLoop.loopStates nt)

theorem states_ge (nt : Nat) (p : Polynomial Nat) : 3 ≤ states nt p := by
  have := entry_states_ge nt p
  unfold states ULogFiniteTapeGuardedStageComposition.stateCount
  omega

noncomputable def program (M : Machine ns nt 2) (p : Polynomial Nat) :
    BoundedProgram (states nt p) 3 :=
  ULogFiniteTapeGuardedStageComposition.program
    (ULogTernaryGeneratedMarginEntry.compactProgram (Nat.zero_lt_of_lt M.blank.isLt)
      (codes M) M.blank p)
    (ULogTernaryBalancedBlankLoop.program (Nat.zero_lt_of_lt M.blank.isLt) M.blank)
    (entry_states_ge nt p) (loop_states_ge nt) .stay

noncomputable def initial (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    BoundedConfig (states nt p) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig
    (ULogTernaryGeneratedMarginEntry.compactInitial nt p x)

noncomputable def under (nt : Nat) (p : Polynomial Nat) (x : List Bool) : List (Fin 3) :=
  ULogTernaryGeneratedHeadedSourceReturn.retained
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) (depth nt p) (seed nt p) x

noncomputable def pool (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryMarginReserveBudget.after nt
    (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) x.length
noncomputable def residue (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryMarginReserveBudget.residue nt
    (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) x.length

noncomputable def head (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Int :=
  ULogTernaryGeneratedHeadedSourceReturn.finalHead nt
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) (depth nt p) (seed nt p) x

noncomputable def final (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    BoundedConfig (states nt p) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig
    (ULogTernaryBalancedBlankLoop.final (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x)
      (under nt p x) [] (copies nt p x) (residue nt p x))

noncomputable def deadline (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedMarginEntry.compactDeadline nt p x + 2 +
    ULogTernaryBalancedBlankLoop.deadline nt
      (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x).length
      (copies nt p x) (residue nt p x)

theorem copies_snoc (blank : Fin nt) (m : Nat) :
    ULogTernaryBalancedMarginEncoding.copies blank (m + 1) =
      ULogTernaryBalancedMarginEncoding.copies blank m ++ ULogTernaryBalancedBlankPair.block blank := by
  unfold ULogTernaryBalancedMarginEncoding.copies
  rw [List.replicate_succ']
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem loop_margin_encoding (blank : Fin nt) (source : List Bool) (m : Nat) :
    ULogTernaryBalancedBlankLoop.marginBits blank source m =
      ULogTernaryBalancedMarginEncoding.copies blank m ++ source ++
        ULogTernaryBalancedMarginEncoding.copies blank m := by
  induction m with
  | zero => simp [ULogTernaryBalancedBlankLoop.marginBits, ULogTernaryBalancedMarginEncoding.copies]
  | succ m ih =>
      calc
        ULogTernaryBalancedBlankLoop.marginBits blank source (m + 1) =
            (ULogTernaryBalancedBlankPair.block blank ++ ULogTernaryBalancedMarginEncoding.copies blank m) ++
              source ++ (ULogTernaryBalancedMarginEncoding.copies blank m ++ ULogTernaryBalancedBlankPair.block blank) := by
                simp [ULogTernaryBalancedBlankLoop.marginBits, ih, List.append_assoc]
        _ = _ := by
          rw [← ULogTernaryBalancedMarginEncoding.copies_succ, ← copies_snoc]

theorem second_start (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogFiniteTapeGuardedStageComposition.secondStart (loop_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryGeneratedMarginEntry.compactFinal (codes M) M.blank p x) =
      ULogTernaryBalancedBlankLoop.initial (Nat.zero_lt_of_lt M.blank.isLt)
        (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x) (under nt p x) [] (pool nt p x) := by
  have ht := ULogTernaryGeneratedMarginEntry.final_tape (codes M) M.blank
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) (depth nt p) (seed nt p) x
    (ULogTernaryGeneratedMarginEntry.compact_pool_fits nt p x)
  apply ULogTernaryOneHotBlockWriter.config_ext
  · apply Fin.ext
    simp [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
      ULogTernaryBalancedBlankLoop.initial, ULogFiniteTapeTestBodyLoop.testConfig,
      ULogFiniteTapeTestBodyLoop.testState, ULogTernaryReserveThresholdProbe.initial,
      ULogTernaryReserveThresholdProbe.S]
  · simpa [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
      ULogTernaryBalancedBlankLoop.initial, ULogFiniteTapeTestBodyLoop.testConfig,
      ULogTernaryReserveThresholdProbe.initial, under,
      ULogTernaryGeneratedMarginEntry.compactFinal, depth, seed] using ht.1
  · simpa [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
      ULogTernaryBalancedBlankLoop.initial, ULogFiniteTapeTestBodyLoop.testConfig,
      ULogTernaryReserveThresholdProbe.initial,
      ULogTernaryGeneratedMarginEntry.compactFinal, depth, seed] using ht.2.1
  · simpa [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
      ULogTernaryBalancedBlankLoop.initial, ULogFiniteTapeTestBodyLoop.testConfig,
      ULogTernaryReserveThresholdProbe.initial, ULogTernaryReserveThresholdProbe.srcRight,
      pool, ULogTernaryGeneratedMarginSourceClock.reserve, List.append_assoc,
      ULogTernaryGeneratedMarginEntry.compactFinal, depth, seed] using ht.2.2

theorem actual_run (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    run (program M p) 2 (List.replicate (deadline M p x) false) 0 (initial nt p x) =
      some (head nt p x, final M p x) := by
  have hp := ULogTernaryGeneratedMarginEntry.compact_actual_run
    (Nat.zero_lt_of_lt M.blank.isLt) (codes M) M.blank p x
  have hq := ULogTernaryBalancedBlankLoop.actual_run (Nat.zero_lt_of_lt M.blank.isLt) M.blank
    (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x) (under nt p x) []
    (pool nt p x) (head nt p x)
  change run _ 2 (List.replicate (ULogTernaryBalancedBlankLoop.deadline nt
    (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x).length
      (copies nt p x) (residue nt p x)) false) _ _ = _ at hq
  have h := ULogFiniteTapeGuardedStageComposition.sequential_run
    (ULogTernaryGeneratedMarginEntry.compactProgram (Nat.zero_lt_of_lt M.blank.isLt) (codes M) M.blank p)
    (ULogTernaryBalancedBlankLoop.program (Nat.zero_lt_of_lt M.blank.isLt) M.blank)
    (entry_states_ge nt p) (loop_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryGeneratedMarginEntry.compactDeadline nt p x) false)
    (List.replicate (ULogTernaryBalancedBlankLoop.deadline nt
      (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x).length
      (copies nt p x) (residue nt p x)) false)
    0 (head nt p x) (head nt p x)
    (ULogTernaryGeneratedMarginEntry.compactInitial nt p x)
    (ULogTernaryGeneratedMarginEntry.compactFinal (codes M) M.blank p x)
    (ULogTernaryBalancedBlankLoop.final (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x)
      (under nt p x) [] (copies nt p x) (residue nt p x))
    hp (ULogTernaryGeneratedMarginEntry.final_accepts (codes M) M.blank _ _ _ x) (by
      rw [second_start, FiniteOneTapeSemantics.moveHead]; exact hq)
  have hw : List.replicate (deadline M p x) false =
      List.replicate (ULogTernaryGeneratedMarginEntry.compactDeadline nt p x) false ++
        false :: false :: List.replicate (ULogTernaryBalancedBlankLoop.deadline nt
          (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x).length
          (copies nt p x) (residue nt p x)) false := by
    simp [deadline, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]
  exact h

theorem final_window (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (final M p x).state.val = 0 ∧ (final M p x).leftRev = under nt p x ∧
      (final M p x).focus = 2 ∧ (final M p x).right =
        ULogTernaryRetainedCounterPump.cells
          (ULogTernaryBalancedMarginEncoding.marginBits M x (copies nt p x)) ++
          2 :: List.replicate (residue nt p x) 0 ++ [2] := by
  simp [final, ULogFiniteTapeGuardedStageComposition.rightConfig,
    ULogFiniteTapeGuardedStageComposition.rightState, ULogTernaryBalancedBlankLoop.final,
    ULogTernaryReserveThresholdProbe.srcRight, loop_margin_encoding,
    ULogTernaryBalancedMarginEncoding.marginBits, List.append_assoc]

theorem program_falseOnly (M : Machine ns nt 2) (p : Polynomial Nat) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program M p) :=
  ULogFiniteTapeGuardedStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernaryGeneratedMarginEntry.program_falseOnly
      (Nat.zero_lt_of_lt M.blank.isLt) (codes M) M.blank _ _)
    (ULogTernaryBalancedBlankLoop.program_falseOnly (Nat.zero_lt_of_lt M.blank.isLt) M.blank)

theorem final_accepts (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (final M p x).state.val = 0 := rfl

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

set_option maxHeartbeats 1000000 in
theorem initial_bounded (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    initial nt p x = boundedInitial (⟨2, states_ge nt p⟩ : Fin (states nt p))
      (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput
        (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
        (ULogTernaryGuardedPumpSentinel.source (depth nt p) (seed nt p) x)) := by
  have hb : ULogTernaryRetainedCounterPump.cell = boundedBit (0 : Fin 3) 1 := by
    funext b; cases b <;> rfl
  cases hw : ULogTernaryGeneratedHeadedSourceExpansion.width nt p x <;>
    simp [initial, ULogFiniteTapeGuardedStageComposition.leftConfig,
      ULogFiniteTapeGuardedStageComposition.leftState,
      ULogTernaryGeneratedMarginEntry.compactInitial, ULogTernaryGeneratedMarginEntry.initial,
      ULogTernaryGeneratedMarginEntry.sealedInitial,
      ULogTernaryGeneratedHeadedSourceReturn.initial, ULogTernaryGeneratedHeadedSourceExpansion.initial,
      ULogTernaryGuardedPumpDelimiter.initial, ULogTernaryGuardedPumpSentinel.initial,
      ULogFiniteTapeStageComposition.leftConfig, ULogFiniteTapeStageComposition.leftState,
      ULogTernaryRetainedCounterPump.initial, ULogTernaryRetainedCounterPump.fromCells,
      ULogTernaryRetainedCounterPump.sourceInput, ULogTernaryRetainedCounterPump.cells, hb,
      boundedInitial, boundedBit, List.replicate_succ, depth, seed, hw] <;> rfl

theorem start_input (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input M p x) = liftConfig (program M p) (initial nt p x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitCountedPolynomialPayload.payload_layout]
  rw [initial_bounded]
  exact (liftConfig_boundedInitial (program M p) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _).symm

theorem semantic_run (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input M p x))
      (List.replicate (deadline M p x) false) = some (liftConfig (program M p) (final M p x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0, actual_run]
  rfl

theorem local_cutoff_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x)) =
      if deadline M p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact ULogFiniteAlphabetDeterministicRuns.acceptingPaths_threshold (2 : Fin 3) rfl _
    (program_falseOnly M p) (deadline M p x) 0 (initial nt p x) (final M p x)
    (head nt p x) (actual_run M p x) (final_accepts M p x) T

theorem every_raw (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt p) 3}
    (hw : run (program M p) 2 w 0 (initial nt p x) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline M p x :=
  ⟨ULogFiniteAlphabetDeterministicRuns.successful_zipper_is_false
      (2 : Fin 3) _ (program_falseOnly M p) hw,
    ULogFiniteAlphabetDeterministicRuns.successful_zipper_length_le
      (2 : Fin 3) _ (program_falseOnly M p) (deadline M p x) 0
      (initial nt p x) (final M p x) (head nt p x)
      (actual_run M p x) (final_accepts M p x) hw⟩

theorem accepting_word (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt p) 3}
    (hw : run (program M p) 2 w 0 (initial nt p x) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline M p x) false ∧ hf = head nt p x ∧ out = final M p x :=
  ULogFiniteAlphabetDeterministicRuns.accepting_zipper_word_eq (2 : Fin 3) _
    (program_falseOnly M p) (deadline M p x) 0 (initial nt p x) (final M p x)
    (head nt p x) (actual_run M p x) (final_accepts M p x) hw ha

theorem every_semantic_raw_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {out : ULogSemantics.Config}
    (hw : semanticRun (ULogSemantics.start (input M p x)) w = some out) :
    w.length ≤ deadline M p x := by
  rw [start_input] at hw
  exact ULogFiniteAlphabetDeterministicRuns.successful_semantic_length_le
    (2 : Fin 3) rfl _ (program_falseOnly M p) (deadline M p x) 0
    (initial nt p x) (final M p x) (head nt p x) (actual_run M p x)
    (final_accepts M p x) hw

theorem generated_margin_loop_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    StandardBitTime.PolyBitTime (input M p) ∧
    ULogSemantics.start (input M p x) = liftConfig (program M p) (initial nt p x) ∧
    run (program M p) 2 (List.replicate (deadline M p x) false) 0 (initial nt p x) =
      some (head nt p x, final M p x) ∧
    (final M p x).state.val = 0 ∧ (final M p x).leftRev = under nt p x ∧
    (final M p x).focus = 2 ∧ (final M p x).right =
      ULogTernaryRetainedCounterPump.cells
        (ULogTernaryBalancedMarginEncoding.marginBits M x (copies nt p x)) ++
        2 :: List.replicate (residue nt p x) 0 ++ [2] ∧
    (∀ w hf out, run (program M p) 2 w 0 (initial nt p x) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline M p x) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input M p x)) w = some out →
      w.length ≤ deadline M p x) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x)) =
      if deadline M p x ≤ T then 1 else 0) := by
  have hf := final_window M p x
  exact ⟨input_polyBitTime M p, start_input M p x, actual_run M p x,
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, fun _ _ _ hw => every_raw M p x hw,
    fun _ _ hw => every_semantic_raw_length M p x hw, local_cutoff_count M p x⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginLoop
