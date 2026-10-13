import PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnChecked
import PakFixedPolyomino.ULogTernaryMarginReserveBudget
import PakFixedPolyomino.ULogTernaryReserveEndSeal
import PakFixedPolyomino.ULogTernaryConditionalRightMargin

/-! Actual source return, one-cell reserve seal and counter-dependent extra
right blank. The original unary counter is derived from the loader endpoint;
no original-empty certificate or expanded metric input is supplied. The
repeated balanced loop and its live scanner handoff are separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginEntry
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeStageComposition
open ULogTernaryGeneratedHeadedSourceReturn (sourceBits retained pool)
variable {nt : Nat}

def zeroCount (nt k : Nat) (x : List Bool) := ULogTernaryMarginReserveBudget.before nt (2 ^ k) x.length
def sealBuffer (nt k : Nat) (x : List Bool) : List (Fin 3) :=
  List.replicate (zeroCount nt k x - (nt + 1)) 0 ++ [2]
abbrev sealedStates (nt d c : Nat) := stateCount (ULogTernaryGeneratedHeadedSourceReturn.states nt d c) 7
abbrev states (nt d c : Nat) := stateCount (sealedStates nt d c) (ULogTernaryConditionalRightMargin.states nt)

theorem return_states_ge (nt d c : Nat) : 3 ≤ ULogTernaryGeneratedHeadedSourceReturn.states nt d c := by
  have := ULogTernaryGeneratedHeadedSourceReturn.child_states_ge nt d c
  unfold ULogTernaryGeneratedHeadedSourceReturn.states stateCount; omega
theorem sealed_states_ge (nt d c : Nat) : 3 ≤ sealedStates nt d c := by
  have := return_states_ge nt d c
  unfold sealedStates stateCount; omega
theorem conditional_states_ge (nt : Nat) : 3 ≤ ULogTernaryConditionalRightMargin.states nt := by
  have := ULogTernaryConditionalRightMargin.child_states_ge nt
  unfold ULogTernaryConditionalRightMargin.states stateCount; omega

def sealedProgram (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (d c : Nat) : BoundedProgram (sealedStates nt d c) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernaryGeneratedHeadedSourceReturn.program hnt codes d c)
    ULogTernaryReserveEndSeal.program (return_states_ge nt d c) (by decide) .stay
def program (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (d c : Nat) : BoundedProgram (states nt d c) 3 :=
  ULogFiniteTapeStageComposition.program (sealedProgram hnt codes d c)
    (ULogTernaryConditionalRightMargin.program hnt blank)
    (sealed_states_ge nt d c) (conditional_states_ge nt) .stay
def sealedInitial (nt k d c : Nat) (x : List Bool) : BoundedConfig (sealedStates nt d c) 3 :=
  leftConfig (ULogTernaryGeneratedHeadedSourceReturn.initial nt k d c x)
def sealedFinal (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) : BoundedConfig (sealedStates nt d c) 3 :=
  rightConfig (ULogTernaryReserveEndSeal.final (sourceBits codes x) (retained k d c x) (zeroCount nt k x))
def initial (nt k d c : Nat) (x : List Bool) : BoundedConfig (states nt d c) 3 := leftConfig (sealedInitial nt k d c x)
def final (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat) (x : List Bool) : BoundedConfig (states nt d c) 3 :=
  rightConfig (ULogTernaryConditionalRightMargin.final blank x.length (sourceBits codes x)
    (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x))
def sealedDeadline (nt k d c : Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedHeadedSourceReturn.deadline nt k d c x + 1 +
    ULogTernaryReserveEndSeal.deadline
      (((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1)) (zeroCount nt k x)
def deadline (nt k d c : Nat) (x : List Bool) : Nat := sealedDeadline nt k d c x + 1 +
  ULogTernaryConditionalRightMargin.deadline nt x.length
    (((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1))

theorem pool_eq (nt k : Nat) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) :
    pool nt k x = List.replicate (zeroCount nt k x) 0 := by
  apply List.eq_replicate_iff.2
  refine ⟨ULogTernaryMarginReserveBudget.actual_pool_length nt k x hfit, ?_⟩
  cases x <;> simp [pool, ULogTernaryPreparedHeadedSourceExpansion.remaining,
    ULogTernaryGeneratedHeadedSourceExpansion.buffer]

theorem seal_second_start (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) :
    secondStart (by decide : 3 ≤ 7) (2 : Fin 3) .stay
      (ULogTernaryGeneratedHeadedSourceReturn.final codes k d c x) =
      ULogTernaryReserveEndSeal.initial (sourceBits codes x) (retained k d c x) (zeroCount nt k x) := by
  have ht := ULogTernaryGeneratedHeadedSourceReturn.final_tape codes k d c x
  simp only [secondStart, applyBounded]
  rw [ht.1, ht.2.1, ht.2.2, pool_eq nt k x hfit]
  rfl

theorem sealed_actual_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) :
    run (sealedProgram hnt codes d c) 2 (List.replicate (sealedDeadline nt k d c x) false) 0
      (sealedInitial nt k d c x) =
      some (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x, sealedFinal codes k d c x) := by
  have h := sequential_run (ULogTernaryGeneratedHeadedSourceReturn.program hnt codes d c)
    ULogTernaryReserveEndSeal.program (return_states_ge nt d c) (by decide) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryGeneratedHeadedSourceReturn.deadline nt k d c x) false)
    (List.replicate (ULogTernaryReserveEndSeal.deadline (sourceBits codes x).length (zeroCount nt k x)) false)
    0 (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.initial nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.final codes k d c x)
    (ULogTernaryReserveEndSeal.final (sourceBits codes x) (retained k d c x) (zeroCount nt k x))
    (ULogTernaryGeneratedHeadedSourceReturn.actual_run hnt codes k d c hc x hfit)
    (ULogTernaryGeneratedHeadedSourceReturn.final_accepts codes k d c x) (by
      rw [seal_second_start codes k d c x hfit, FiniteOneTapeSemantics.moveHead]
      exact ULogTernaryReserveEndSeal.actual_run _ _ _ _)
  have hw : List.replicate (sealedDeadline nt k d c x) false =
      List.replicate (ULogTernaryGeneratedHeadedSourceReturn.deadline nt k d c x) false ++ false ::
        List.replicate (ULogTernaryReserveEndSeal.deadline (sourceBits codes x).length (zeroCount nt k x)) false := by
    simp [sealedDeadline, ULogTernaryGeneratedHeadedSourceReturn.source_length,
      List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]; exact h

theorem sealed_accepts (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    (sealedFinal codes k d c x).state.val = 0 :=
  (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2 rfl

theorem conditional_second_start (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool)
    (hpool : nt + 1 ≤ zeroCount nt k x) :
    secondStart (conditional_states_ge nt) (2 : Fin 3) .stay (sealedFinal codes k d c x) =
      ULogTernaryConditionalRightMargin.initial nt x.length (sourceBits codes x)
        (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x) := by
  have hsplit : zeroCount nt k x = (nt + 1) + (zeroCount nt k x - (nt + 1)) := by omega
  have hrep : List.replicate (zeroCount nt k x) (0 : Fin 3) =
      List.replicate (nt + 1) 0 ++ List.replicate (zeroCount nt k x - (nt + 1)) 0 := by
    conv_lhs => rw [hsplit, List.replicate_add]
  simp [secondStart, applyBounded, sealedFinal, rightConfig,
    ULogTernaryReserveEndSeal.final, ULogTernaryReserveEndSeal.sealedRight,
    ULogTernaryConditionalRightMargin.initial, ULogTernaryConditionalRightMargin.counter,
    retained, ULogTernaryCountedSourceDelimiter.ones, sealBuffer,
    hrep, List.append_assoc]
  simp only [List.replicate_add, List.append_assoc]

theorem actual_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x) :
    run (program hnt codes blank d c) 2 (List.replicate (deadline nt k d c x) false) 0
      (initial nt k d c x) = some (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x,
        final codes blank k d c x) := by
  have h := sequential_run (sealedProgram hnt codes d c) (ULogTernaryConditionalRightMargin.program hnt blank)
    (sealed_states_ge nt d c) (conditional_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (sealedDeadline nt k d c x) false)
    (List.replicate (ULogTernaryConditionalRightMargin.deadline nt x.length (sourceBits codes x).length) false)
    0 (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (sealedInitial nt k d c x) (sealedFinal codes k d c x)
    (ULogTernaryConditionalRightMargin.final blank x.length (sourceBits codes x)
      (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x))
    (sealed_actual_run hnt codes k d c hc x hfit) (sealed_accepts codes k d c x) (by
      rw [conditional_second_start codes k d c x hpool, FiniteOneTapeSemantics.moveHead]
      exact ULogTernaryConditionalRightMargin.actual_run hnt blank _ _ _ _ _)
  have hw : List.replicate (deadline nt k d c x) false =
      List.replicate (sealedDeadline nt k d c x) false ++ false ::
        List.replicate (ULogTernaryConditionalRightMargin.deadline nt x.length (sourceBits codes x).length) false := by
    simp [deadline, ULogTernaryGeneratedHeadedSourceReturn.source_length,
      List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]; exact h

theorem compact_pool_fits (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    nt + 1 ≤ zeroCount nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x := by
  have h := (ULogTernaryMarginReserveBudget.compact_reserve_budget nt p x).1
  have hn : ULogTernaryMarginReserveBudget.after nt
      (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x.length ≤
      ULogTernaryMarginReserveBudget.before nt
      (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x.length := Nat.sub_le _ _
  unfold ULogTernaryMarginReserveBudget.pairWidth at h
  unfold zeroCount
  have hp : 1 ≤ ULogTernaryGeneratedWindowBudget.radius p x + 1 := by omega
  have hm := Nat.mul_le_mul_left (2 * (nt + 1)) hp
  omega

theorem compact_actual_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    let k := ULogTernaryGeneratedHeadedSourceExpansion.width nt p x
    let d := ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
    let c := ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
    run (program hnt codes blank d c) 2 (List.replicate (deadline nt k d c x) false) 0
      (initial nt k d c x) = some (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x,
        final codes blank k d c x) := by
  dsimp only
  exact actual_run hnt codes blank _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x
    (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x) (compact_pool_fits nt p x)

def correctedBits (codes : Fin 3 → Fin nt) (blank : Fin nt) (x : List Bool) : List Bool :=
  if x.length = 0 then sourceBits codes x else sourceBits codes x ++ ULogTernaryBalancedBlankPair.block blank

theorem final_accepts (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat) (x : List Bool) :
    (final codes blank k d c x).state.val = 0 :=
  (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryConditionalRightMargin.final_accepts blank _ _ _ _)

theorem final_tape (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat) (x : List Bool)
    (hpool : nt + 1 ≤ zeroCount nt k x) :
    (final codes blank k d c x).leftRev = retained k d c x ∧
    (final codes blank k d c x).focus = 2 ∧
    (final codes blank k d c x).right =
      ULogTernaryRetainedCounterPump.cells (correctedBits codes blank x) ++
        2 :: (List.replicate (ULogTernaryMarginReserveBudget.after nt (2 ^ k) x.length) 0 ++ [2]) := by
  have ht := ULogTernaryConditionalRightMargin.final_tape blank x.length (sourceBits codes x)
    (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x)
  have hrep : List.replicate (zeroCount nt k x) (0 : Fin 3) =
      List.replicate (nt + 1) 0 ++ List.replicate (zeroCount nt k x - (nt + 1)) 0 := by
    have h : zeroCount nt k x = nt + 1 + (zeroCount nt k x - (nt + 1)) := by omega
    conv_lhs => rw [h, List.replicate_add]
  have ha : ULogTernaryMarginReserveBudget.after nt (2 ^ k) x.length =
      if x.length = 0 then zeroCount nt k x else zeroCount nt k x - (nt + 1) := by
    unfold ULogTernaryMarginReserveBudget.after zeroCount
    split_ifs <;> simp_all
  change _ ∧ _ ∧ (ULogTernaryConditionalRightMargin.final blank x.length (sourceBits codes x)
    (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x)).right = _
  rw [ht.2.2, ha]
  refine ⟨ht.1, ht.2.1, ?_⟩
  by_cases hn : x.length = 0
  · simp only [hn, ↓reduceIte, correctedBits, sealBuffer]
    rw [hrep, List.append_assoc]
    simp only [List.cons_append, List.append_assoc]
  · simp [hn, correctedBits, sealBuffer]

theorem program_falseOnly (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (d c : Nat) :
    FalseOnly (program hnt codes blank d c) := by
  apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
  · exact ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
      (ULogTernaryGeneratedHeadedSourceReturn.program_falseOnly hnt codes d c)
      ULogTernaryReserveEndSeal.program_falseOnly
  · exact ULogTernaryConditionalRightMargin.program_falseOnly hnt blank

noncomputable def compactProgram (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) :=
  program hnt codes blank
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
noncomputable def compactInitial (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  initial nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def compactFinal (codes : Fin 3 → Fin nt) (blank : Fin nt) (p : Polynomial Nat) (x : List Bool) :=
  final codes blank (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def compactDeadline (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  deadline nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def input (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap (compactProgram hnt codes blank p)
    (StandardBitCountedPolynomialPayload.payload (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x)

theorem input_polyBitTime (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes blank p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogPayloadClockBitWrapper.wrap_polyBitTime (compactProgram hnt codes blank p))

theorem initial_lift (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat) (x : List Bool) :
    liftConfig (program hnt codes blank d c) (initial nt k d c x) = ULogSemantics.start
      (encodeInstance (program hnt codes blank d c)
        (ULogTernaryRetainedCounterPump.sourceInput k (ULogTernaryGuardedPumpSentinel.source d c x))) := by
  have hb : ULogTernaryRetainedCounterPump.cell = boundedBit (0 : Fin 3) 1 := by funext b; cases b <;> rfl
  have hi : initial nt k d c x = boundedInitial
      (⟨2, by have := sealed_states_ge nt d c; unfold states stateCount; omega⟩ : Fin (states nt d c))
      (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput k (ULogTernaryGuardedPumpSentinel.source d c x)) := by
    cases k <;> simp [initial, sealedInitial, ULogTernaryGeneratedHeadedSourceReturn.initial,
      ULogTernaryGeneratedHeadedSourceExpansion.initial,
      ULogTernaryGuardedPumpDelimiter.initial, ULogTernaryGuardedPumpSentinel.initial,
      ULogFiniteTapeGuardedStageComposition.leftConfig,
      ULogFiniteTapeGuardedStageComposition.leftState, leftConfig, leftState,
      ULogTernaryRetainedCounterPump.initial, ULogTernaryRetainedCounterPump.fromCells,
      ULogTernaryRetainedCounterPump.sourceInput, ULogTernaryRetainedCounterPump.cells, hb,
      boundedInitial, boundedBit, List.replicate_succ]
  rw [hi]
  exact liftConfig_boundedInitial (program hnt codes blank d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _

theorem start_input (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt) (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input hnt codes blank p x) =
      liftConfig (compactProgram hnt codes blank p) (compactInitial nt p x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitCountedPolynomialPayload.payload_layout]
  exact (initial_lift hnt codes blank _ _ _ x).symm

theorem compact_semantic_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input hnt codes blank p x))
      (List.replicate (compactDeadline nt p x) false) =
        some (liftConfig (compactProgram hnt codes blank p) (compactFinal codes blank p x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0]
  simp only [compactProgram, compactInitial, compactDeadline, compactFinal]
  rw [compact_actual_run hnt codes blank p x]
  rfl

theorem compact_cutoff_counts (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes blank p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes blank _ _)
    (compactDeadline nt p x) 0 (compactInitial nt p x) (compactFinal codes blank p x)
    (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
      (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
      (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x)
    (compact_actual_run hnt codes blank p x) (final_accepts codes blank _ _ _ x) T

end PakFixedPolyomino.ULogTernaryGeneratedMarginEntry
