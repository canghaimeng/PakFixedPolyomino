import PakFixedPolyomino.ULogTernaryPreparedHeadedSourceExpansion
import PakFixedPolyomino.ULogTernaryGeneratedWindowBudget

/-! Actual compact guarded generator followed by the prepared headed source
controller. Both empty and nonempty inputs use genuinely generated zeros.
The program depends on source alphabet/codes and polynomial constants only.
Blank margins and the final live scanner handoff are still separate. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceExpansion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)

abbrev prefixStates (d c : Nat) := ULogTernaryGuardedPumpDelimiter.totalStates d c
abbrev totalStates (nt d c : Nat) := ULogFiniteTapeGuardedStageComposition.stateCount
  (prefixStates d c) (ULogTernaryPreparedHeadedSourceExpansion.stateCount nt)

theorem prefix_states_ge (d c : Nat) : 3 ≤ prefixStates d c :=
  ULogTernaryGeneratedSourceExpansion.prefix_states_ge d c

theorem prepared_states_ge (nt : Nat) : 3 ≤ ULogTernaryPreparedHeadedSourceExpansion.stateCount nt := by
  have h := ULogTernaryPreparedHeadedSourceExpansion.prep_states_ge
  unfold ULogTernaryPreparedHeadedSourceExpansion.stateCount ULogFiniteTapeStageComposition.stateCount
  omega

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (d c : Nat) :
    BoundedProgram (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.program (ULogTernaryGuardedPumpDelimiter.program d c)
    (ULogTernaryPreparedHeadedSourceExpansion.program hnt codes)
    (prefix_states_ge d c) (prepared_states_ge nt) .stay

def initial (nt k d c : Nat) (x : List Bool) : BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig (ULogTernaryGuardedPumpDelimiter.initial k d c x)

def reserveCost (nt : Nat) (x : List Bool) :=
  1 + nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1)

def buffer (nt k : Nat) (x : List Bool) : List (Fin 3) :=
  List.replicate (2 ^ k - 1 - reserveCost nt x) 0

def under (k d c : Nat) (x : List Bool) : List (Fin 3) :=
  ULogTernaryGeneratedSourceExpansion.under k d c x

def final {nt : Nat} (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig (ns := prefixStates d c)
    (ULogTernaryPreparedHeadedSourceExpansion.final codes x (under k d c x) (buffer nt k x))

def deadline (nt k d c : Nat) (x : List Bool) :=
  ULogTernaryGuardedPumpDelimiter.deadline k d c x + 2 +
    ULogTernaryPreparedHeadedSourceExpansion.deadline nt x

def finalHead (nt k d c : Nat) (x : List Bool) : Int :=
  ULogTernaryPreparedHeadedSourceExpansion.finalHead nt x
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)

theorem reserve_split (nt k : Nat) (x : List Bool)
    (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    ULogTernaryGuardedPumpDelimiter.buffer k =
      0 :: ULogTernaryPreparedHeadedSourceExpansion.allocated nt x (buffer nt k x) := by
  have hm : 2 ^ k - 1 = reserveCost nt x + (2 ^ k - 1 - reserveCost nt x) := by omega
  unfold ULogTernaryGuardedPumpDelimiter.buffer
  rw [hm, List.replicate_add]
  unfold reserveCost ULogTernaryPreparedHeadedSourceExpansion.allocated buffer
  rw [List.replicate_add]
  simp only [List.replicate_one, List.cons_append, List.nil_append]
  rfl

theorem second_start (nt k d c : Nat) (x : List Bool)
    (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    ULogFiniteTapeGuardedStageComposition.secondStart (prepared_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryGuardedPumpDelimiter.final k d c x) =
      ULogTernaryPreparedHeadedSourceExpansion.initial nt x (under k d c x) (buffer nt k x) := by
  have hs := reserve_split nt k x hspace
  cases x with
  | nil =>
      simp [ULogTernaryGuardedPumpDelimiter.final,
        ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
        ULogFiniteTapeGuardedStageComposition.rightConfig,
        ULogTernaryCountedSourceDelimiter.finalConfig, fromCells, cells,
        ULogTernaryPreparedHeadedSourceExpansion.initial,
        ULogFiniteTapeStageComposition.leftConfig,
        ULogFiniteTapeStageComposition.leftState,
        ULogTernaryEmptyHeadPreparation.initial, under,
        ULogTernaryGeneratedSourceExpansion.under, hs, List.append_assoc]
      rfl
  | cons b xs =>
      simp [ULogTernaryGuardedPumpDelimiter.final,
        ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
        ULogFiniteTapeGuardedStageComposition.rightConfig,
        ULogTernaryCountedSourceDelimiter.finalConfig, fromCells, cells,
        ULogTernaryPreparedHeadedSourceExpansion.initial,
        ULogFiniteTapeStageComposition.leftConfig,
        ULogFiniteTapeStageComposition.leftState,
        ULogTernaryEmptyHeadPreparation.initial, under,
        ULogTernaryGeneratedSourceExpansion.under, hs, List.append_assoc]
      rfl

theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hspace : reserveCost nt x ≤ 2 ^ k - 1) :
    run (program hnt codes d c) 2 (List.replicate (deadline nt k d c x) false) 0
      (initial nt k d c x) = some (finalHead nt k d c x, final codes k d c x) := by
  have hs := ULogFiniteTapeGuardedStageComposition.sequential_run
    (ULogTernaryGuardedPumpDelimiter.program d c)
    (ULogTernaryPreparedHeadedSourceExpansion.program hnt codes)
    (prefix_states_ge d c) (prepared_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
    (List.replicate (ULogTernaryPreparedHeadedSourceExpansion.deadline nt x) false)
    0 (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (finalHead nt k d c x)
    (ULogTernaryGuardedPumpDelimiter.initial k d c x)
    (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernaryPreparedHeadedSourceExpansion.final codes x (under k d c x) (buffer nt k x))
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x)
    (by rw [second_start nt k d c x hspace]
        exact ULogTernaryPreparedHeadedSourceExpansion.actual_run hnt codes x
          (under k d c x) (buffer nt k x) (ULogTernaryGuardedPumpDelimiter.finalHead k d c x))
  have hw : List.replicate (deadline nt k d c x) false =
      List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false ++ false :: false ::
        List.replicate (ULogTernaryPreparedHeadedSourceExpansion.deadline nt x) false := by
    simp [deadline, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]
  exact hs

noncomputable def polynomial (nt : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  ULogTernaryGeneratedSourceExpansion.paddedPolynomial nt (ULogTernaryGeneratedWindowBudget.marginPolynomial p)

noncomputable def width (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedWindowBudget.width nt p x

theorem compact_reserve_fits (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    reserveCost nt x ≤ 2 ^ width nt p x - 1 := by
  have hf := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  have ht : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ x.length + 1 := by
    cases x <;> simp [ULogTernaryPreparedHeadedSourceExpansion.tail]
  have hm := Nat.mul_le_mul_left nt ht
  have hprod : nt * (x.length + 1) ≤
      (x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3) * (nt + 1) := by
    nlinarith
  unfold reserveCost
  change _ ≤ 2 ^ ULogTernaryGeneratedWindowBudget.width nt p x - 1
  omega

noncomputable def compactProgram {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) : BoundedProgram
      (totalStates nt (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p))) 3 :=
  program hnt codes (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p))

noncomputable def input {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat)
    (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap (compactProgram hnt codes p)
    (StandardBitCountedPolynomialPayload.payload (polynomial nt p) x)

theorem input_polyBitTime {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime (polynomial nt p))
    (ULogPayloadClockBitWrapper.wrap_polyBitTime (compactProgram hnt codes p))


theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (d c : Nat) :
    FalseOnly (program hnt codes d c) :=
  ULogFiniteTapeGuardedStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernaryGuardedPumpDelimiter.program_falseOnly d c)
    (ULogTernaryPreparedHeadedSourceExpansion.program_falseOnly hnt codes)

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    (final codes k d c x).state.val = 0 :=
  (ULogFiniteTapeGuardedStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryPreparedHeadedSourceExpansion.final_state codes x (under k d c x) (buffer nt k x))

theorem initial_lift {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (k d c : Nat) (x : List Bool) :
    liftConfig (program hnt codes d c) (initial nt k d c x) = ULogSemantics.start
      (encodeInstance (program hnt codes d c)
        (ULogTernaryRetainedCounterPump.sourceInput k
          (ULogTernaryGuardedPumpSentinel.source d c x))) := by
  have hb : cell = boundedBit (0 : Fin 3) 1 := by funext b; cases b <;> rfl
  have hi : initial nt k d c x =
      boundedInitial (⟨2, by
        have h := prefix_states_ge d c
        unfold totalStates ULogFiniteTapeGuardedStageComposition.stateCount; omega⟩ : Fin (totalStates nt d c))
        (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput k
          (ULogTernaryGuardedPumpSentinel.source d c x)) := by
    cases k <;>
      simp [initial, ULogTernaryGuardedPumpDelimiter.initial,
        ULogTernaryGuardedPumpSentinel.initial,
        ULogFiniteTapeGuardedStageComposition.leftConfig,
        ULogFiniteTapeGuardedStageComposition.leftState,
        ULogTernaryRetainedCounterPump.initial, ULogTernaryRetainedCounterPump.fromCells,
        ULogTernaryRetainedCounterPump.sourceInput, cells, hb,
        boundedInitial, boundedBit, List.replicate_succ]
  rw [hi]
  exact liftConfig_boundedInitial (program hnt codes d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _


noncomputable def compactInitial (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  initial nt (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x

noncomputable def compactFinal {nt : Nat} (codes : Fin 3 → Fin nt) (p : Polynomial Nat) (x : List Bool) :=
  final codes (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x

noncomputable def compactDeadline (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  deadline nt (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x

noncomputable def clockWidth (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpDelimiterInput.clockWidth (polynomial nt p) x

theorem start_input {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input hnt codes p x) =
      liftConfig (compactProgram hnt codes p) (compactInitial nt p x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitCountedPolynomialPayload.payload_layout]
  exact (initial_lift hnt codes _ _ _ x).symm

theorem compact_actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input hnt codes p x))
      (List.replicate (compactDeadline nt p x) false) =
        some (liftConfig (compactProgram hnt codes p) (compactFinal codes p x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0]
  simp only [compactProgram, compactInitial, compactDeadline, compactFinal]
  rw [actual_run hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
    x (compact_reserve_fits nt p x)]
  rfl

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact acceptingPaths_threshold (2 : Fin 3) rfl _
    (program_falseOnly hnt codes _ _) (compactDeadline nt p x) 0 (compactInitial nt p x)
    (compactFinal codes p x) (finalHead nt (width nt p x)
      (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
      (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x)
    (actual_run hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
      x (compact_reserve_fits nt p x))
    (final_state codes _ _ _ x) T

theorem compact_deadline_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 64 * (2 ^ width nt p x) ^ 2 := by
  have hd := ULogTernaryGuardedPumpDelimiterInput.deadline_upper (polynomial nt p) x
  have hw := ULogTernaryGeneratedWindowBudget.width_lower nt p x
  change p.eval x.length + nt + x.length + 8 ≤ width nt p x at hw
  have hnt : nt ≤ 2 ^ width nt p x :=
    (ULogTernaryGeneratedSourceExpansion.self_le_pow_two nt).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega))
  have hlen : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ x.length + 1 := by
    cases x <;> simp [ULogTernaryPreparedHeadedSourceExpansion.tail]
  have hm : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ 2 ^ width nt p x :=
    hlen.trans ((ULogTernaryGeneratedSourceExpansion.self_le_pow_two (x.length + 1)).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)))
  have hc := compact_reserve_fits nt p x
  have hprod : nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) ≤ 2 ^ width nt p x := by
    unfold reserveCost at hc
    omega
  have ha := Nat.mul_le_mul hprod hm
  have hb := Nat.mul_le_mul hnt hprod
  have hr : 1 ≤ 2 ^ width nt p x := by
    have hpos : 0 < 2 ^ width nt p x := by positivity
    omega
  have hr2 : 2 ^ width nt p x ≤ (2 ^ width nt p x) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hp : ULogTernaryEmptyHeadPreparation.deadline x ≤ 4 := by
    cases x <;> simp [ULogTernaryEmptyHeadPreparation.deadline]
  change ULogTernaryGuardedPumpDelimiterInput.deadline (polynomial nt p) x + 2 +
    (ULogTernaryEmptyHeadPreparation.deadline x + 1 +
      ULogTernaryHeadedSourceExpansion.deadline nt (ULogTernaryPreparedHeadedSourceExpansion.tail x).length) ≤ _
  rw [ULogTernaryHeadedSourceExpansion.deadline_eq]
  change _ ≤ 64 * (2 ^ width nt p x) ^ 2
  change _ ≤ 43 * (2 ^ width nt p x) ^ 2 at hd
  rw [pow_two] at hd hr2 ⊢
  have hpoly : (nt * nt + 7 * nt + 5) *
      ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) =
      nt * (nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1)) +
        7 * (nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1)) +
        5 * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) := by ring
  have hmid : (nt * nt + 7 * nt + 5) *
      ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) ≤
      13 * (2 ^ width nt p x * 2 ^ width nt p x) := by
    calc
      _ = nt * (nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1)) +
          7 * (nt * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1)) +
          5 * ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) := hpoly
      _ ≤ (2 ^ width nt p x * 2 ^ width nt p x) +
          7 * 2 ^ width nt p x + 5 * 2 ^ width nt p x := by omega
      _ ≤ 13 * (2 ^ width nt p x * 2 ^ width nt p x) := by omega
  have hrLarge : 2 ≤ 2 ^ width nt p x := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (show 1 ≤ width nt p x by omega)
    exact (show (2 : Nat) ^ 1 = 2 by rfl) ▸ h
  have squareLarge : 2 ≤ 2 ^ width nt p x * 2 ^ width nt p x := hrLarge.trans hr2
  omega

theorem compact_deadline_le_clock (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 2 ^ clockWidth nt p x := by
  have hd := compact_deadline_upper nt p x
  have hs := ULogTernaryGuardedPumpDelimiterInput.source_length_ge (polynomial nt p) x
  have hf : 64 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source (polynomial nt p) x).length + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 6 ≤ _)
  have he : clockWidth nt p x = 2 * width nt p x +
      (2 * (ULogTernaryGuardedPumpDelimiterInput.source (polynomial nt p) x).length + 3) := by
    change 2 * (ULogTernaryGuardedPumpDelimiterInput.width (polynomial nt p) x +
      (ULogTernaryGuardedPumpDelimiterInput.source (polynomial nt p) x).length + 1) + 1 = _
    change 2 * (width nt p x +
      (ULogTernaryGuardedPumpDelimiterInput.source (polynomial nt p) x).length + 1) + 1 = _
    omega
  have hsq : (2 ^ width nt p x) ^ 2 = 2 ^ (2 * width nt p x) := by rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hd
  rw [he, pow_add]
  exact hd.trans (by nlinarith)


theorem compact_every_raw {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input hnt codes p x)) w = some out) :
    w = List.replicate w.length false ∧ w.length ≤ 2 ^ clockWidth nt p x ∧
      ULogBootstrapExecution.SemanticTapeSymbolsLtThree out := by
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, he⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl
    (compactProgram hnt codes p) hw (head := 0)
  have hfals := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes _ _) hz
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes _ _)
    (compactDeadline nt p x) 0 (compactInitial nt p x) (compactFinal codes p x)
    (finalHead nt (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
      (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x)
    (actual_run hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
      x (compact_reserve_fits nt p x))
    (final_state codes _ _ _ x) hz
  refine ⟨hfals, hlen.trans (compact_deadline_le_clock nt p x), ?_⟩
  rw [← he]
  exact ULogTernaryPumpInputSpec.lift_symbols _ _

theorem final_tape {nt : Nat} (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    (final codes k d c x).leftRev =
      (ULogSourceObliviousWindow.encodeWindow
        (ULogTernaryPreparedHeadedSourceExpansion.markedSource codes x)).reverse ++ under k d c x ∧
    (final codes k d c x).focus = 2 ∧
    (final codes k d c x).right =
      ULogTernaryPreparedHeadedSourceExpansion.remaining x (buffer nt k x) := by
  rw [ULogTernaryPreparedHeadedSourceExpansion.markedSource_encoding]
  exact ULogTernaryPreparedHeadedSourceExpansion.final_tape codes x (under k d c x) (buffer nt k x)

/-- All resource fits are derived from the compact polynomial bit input;
no supplied reserve/head/runtime/canonical-image certificate is required. -/
theorem generated_headed_input_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes p) ∧
    (∀ x, reserveCost nt x ≤ 2 ^ width nt p x - 1) ∧
    (∀ x, semanticRun (ULogSemantics.start (input hnt codes p x))
      (List.replicate (compactDeadline nt p x) false) =
        some (liftConfig (compactProgram hnt codes p) (compactFinal codes p x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0) ∧
    (∀ x, compactDeadline nt p x ≤ 2 ^ clockWidth nt p x) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input hnt codes p x)) w = some out →
      w = List.replicate w.length false ∧ w.length ≤ 2 ^ clockWidth nt p x ∧
        ULogBootstrapExecution.SemanticTapeSymbolsLtThree out) ∧
    (∀ x, (compactFinal codes p x).leftRev =
      (ULogSourceObliviousWindow.encodeWindow
        (ULogTernaryPreparedHeadedSourceExpansion.markedSource codes x)).reverse ++
          under (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (polynomial nt p))
            (ULogTernaryGuardedPumpDelimiterInput.seedWidth (polynomial nt p)) x ∧
      (compactFinal codes p x).focus = 2 ∧
      (compactFinal codes p x).right =
        ULogTernaryPreparedHeadedSourceExpansion.remaining x (buffer nt (width nt p x) x)) ∧
    (∀ x, (ULogTernaryPreparedHeadedSourceExpansion.markedSource codes x).map
      ULogSourceObliviousWindow.MarkedCell.head =
        true :: List.replicate (ULogTernaryPreparedHeadedSourceExpansion.tail x).length false) :=
  ⟨input_polyBitTime hnt codes p, compact_reserve_fits nt p, compact_actual_run hnt codes p,
    cutoff_counts hnt codes p, compact_deadline_le_clock nt p, compact_every_raw hnt codes p,
    (fun x => final_tape codes _ _ _ x), ULogTernaryPreparedHeadedSourceExpansion.markedSource_unique codes⟩

end PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceExpansion
