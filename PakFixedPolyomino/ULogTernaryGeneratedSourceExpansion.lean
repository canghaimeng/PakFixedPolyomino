import PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterInput
import PakFixedPolyomino.ULogTernarySourceLoopExecution

/-! Source expansion from the actual compact guarded generator/parser.
The source loop consumes zeros produced by the internal pump. No exponential
reserve is supplied in the metric input. Flags remain uniform in this stage;
actual blank margins, the unique head and scanner handoff are separate. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedSourceExpansion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)

abbrev prefixStates (d c : Nat) := ULogTernaryGuardedPumpDelimiter.totalStates d c
abbrev totalStates (nt d c : Nat) := ULogFiniteTapeGuardedStageComposition.stateCount
  (prefixStates d c) (ULogTernarySourceLoopExecution.stateCount nt)

theorem prefix_states_ge (d c : Nat) : 3 ≤ prefixStates d c := by
  have h := ULogTernaryGuardedPumpDelimiter.prefix_states_ge3 d c
  unfold prefixStates ULogTernaryGuardedPumpDelimiter.totalStates
    ULogFiniteTapeGuardedStageComposition.stateCount
  omega

theorem loop_states_ge (nt : Nat) : 3 ≤ ULogTernarySourceLoopExecution.stateCount nt := by
  unfold ULogTernarySourceLoopExecution.stateCount ULogTernarySourceLoop.stateCount
  omega

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) (d c : Nat) :
    BoundedProgram (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.program (ULogTernaryGuardedPumpDelimiter.program d c)
    (ULogTernarySourceLoopExecution.program hnt codes flag)
    (prefix_states_ge d c) (loop_states_ge nt) .stay

def initial (nt k d c : Nat) (x : List Bool) : BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.leftConfig (ULogTernaryGuardedPumpDelimiter.initial k d c x)

def under (k d c : Nat) (x : List Bool) : List (Fin 3) :=
  2 :: (ULogTernaryCountedSourceDelimiter.ones x.length ++
    2 :: ULogTernaryGuardedPumpDelimiter.under k d c x)

def buffer (nt k : Nat) (x : List Bool) : List (Fin 3) :=
  List.replicate (2 ^ k - 1 - nt * x.length) 0

def final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (k d c : Nat) (x : List Bool) :
    BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.rightConfig (ns := prefixStates d c)
    (ULogTernarySourceLoopExecution.final codes flag x (under k d c x) (buffer nt k x))

def deadline (nt k d c : Nat) (x : List Bool) :=
  ULogTernaryGuardedPumpDelimiter.deadline k d c x + 2 +
    ULogTernarySourceLoopExecution.deadline nt x.length

def finalHead (nt k d c : Nat) (x : List Bool) : Int :=
  ULogTernaryGuardedPumpDelimiter.finalHead k d c x + (((nt + 1) * x.length : Nat) : Int)

theorem reserve_split (nt k : Nat) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1) :
    ULogTernaryGuardedPumpDelimiter.buffer k = List.replicate (nt * x.length) 0 ++ buffer nt k x := by
  have hm : 2 ^ k - 1 = nt * x.length + (2 ^ k - 1 - nt * x.length) := by omega
  unfold ULogTernaryGuardedPumpDelimiter.buffer buffer
  rw [hm, List.replicate_add]
  congr 1
  congr 1
  omega

theorem second_start (nt k d c : Nat) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1) :
    ULogFiniteTapeGuardedStageComposition.secondStart (loop_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryGuardedPumpDelimiter.final k d c x) =
      ULogTernarySourceLoopExecution.initial nt x (under k d c x) (buffer nt k x) := by
  rw [ULogTernaryGuardedPumpDelimiter.final]
  have hn : cells x ++ 2 :: ULogTernaryGuardedPumpDelimiter.buffer k ≠ [] := by simp
  cases hc : cells x ++ 2 :: ULogTernaryGuardedPumpDelimiter.buffer k with
  | nil => exact (hn hc).elim
  | cons a rest =>
      have hs := reserve_split nt k x hspace
      have ht : cells x ++ 2 :: (List.replicate (nt * x.length) 0 ++ buffer nt k x) = a :: rest := by
        simpa only [hs, List.cons_append, List.append_assoc] using hc
      simp [ULogFiniteTapeGuardedStageComposition.secondStart, applyBounded,
        ULogFiniteTapeGuardedStageComposition.rightConfig,
        ULogTernaryCountedSourceDelimiter.finalConfig, fromCells,
        ULogTernarySourceLoopExecution.initial, under, hc, ht, hs,
        List.cons_append, List.append_assoc]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1) :
    run (program hnt codes flag d c) 2 (List.replicate (deadline nt k d c x) false) 0
      (initial nt k d c x) = some (finalHead nt k d c x, final codes flag k d c x) := by
  have hs := ULogFiniteTapeGuardedStageComposition.sequential_run
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernarySourceLoopExecution.program hnt codes flag)
    (prefix_states_ge d c) (loop_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
    (List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false)
    0 (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (finalHead nt k d c x)
    (ULogTernaryGuardedPumpDelimiter.initial k d c x) (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernarySourceLoopExecution.final codes flag x (under k d c x) (buffer nt k x))
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x)
    (by
      rw [second_start nt k d c x hspace]
      exact ULogTernarySourceLoopExecution.actual_run hnt codes flag x (under k d c x)
        (buffer nt k x) (ULogTernaryGuardedPumpDelimiter.finalHead k d c x))
  have hw : List.replicate (deadline nt k d c x) false =
      List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false ++ false :: false ::
        List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false := by
    simp [deadline, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]
  exact hs

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) (d c : Nat) :
    FalseOnly (program hnt codes flag d c) :=
  ULogFiniteTapeGuardedStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernaryGuardedPumpDelimiter.program_falseOnly d c)
    (ULogTernarySourceLoopExecution.program_falseOnly hnt codes flag)

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (k d c : Nat) (x : List Bool) :
    (final codes flag k d c x).state.val = 0 := by
  simp [final, ULogFiniteTapeGuardedStageComposition.rightConfig,
    ULogFiniteTapeGuardedStageComposition.rightState, ULogTernarySourceLoopExecution.final]

theorem every_raw_length {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes flag d c) 2 w 0 (initial nt k d c x) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt k d c x :=
  ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes flag d c) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes flag d c)
      (deadline nt k d c x) 0 (initial nt k d c x) (final codes flag k d c x)
      (finalHead nt k d c x) (actual_run hnt codes flag k d c hc x hspace)
      (final_state codes flag k d c x) hw⟩

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes flag d c) (initial nt k d c x)) =
      if deadline nt k d c x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes flag d c)
    (deadline nt k d c x) 0 (initial nt k d c x) (final codes flag k d c x)
    (finalHead nt k d c x) (actual_run hnt codes flag k d c hc x hspace)
    (final_state codes flag k d c x) T

noncomputable def paddedPolynomial (nt : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  p + Polynomial.X + Polynomial.C (nt + 2)

noncomputable def width (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  ULogTernaryGuardedPumpDelimiterInput.width (paddedPolynomial nt p) x

theorem width_lower (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    nt + x.length + 2 ≤ width nt p x := by
  have h := StandardBitCountedPolynomialPayload.width_dominates (paddedPolynomial nt p) x
  simp only [paddedPolynomial, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h
  exact Nat.le_trans (by omega) h

theorem self_le_pow_two (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < 2 ^ n := by positivity
      rw [pow_succ]; omega

theorem generated_reserve_fits (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    nt * x.length ≤ 2 ^ width nt p x - 1 := by
  have hb := width_lower nt p x
  have hp : nt * x.length ≤ 2 ^ (nt + x.length) := by
    rw [pow_add]
    exact Nat.mul_le_mul (self_le_pow_two nt) (self_le_pow_two x.length)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
    (by omega : nt + x.length + 1 ≤ width nt p x)
  have hpos : 0 < 2 ^ (nt + x.length) := by positivity
  rw [pow_succ] at hpow
  omega

noncomputable def input {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap
    (program hnt codes flag (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
      (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)))
    (StandardBitCountedPolynomialPayload.payload (paddedPolynomial nt p) x)

theorem input_polyBitTime {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) : StandardBitTime.PolyBitTime (input hnt codes flag p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime (paddedPolynomial nt p))
    (ULogPayloadClockBitWrapper.wrap_polyBitTime _)

theorem initial_lift {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (x : List Bool) :
    liftConfig (program hnt codes flag d c) (initial nt k d c x) = ULogSemantics.start
      (encodeInstance (program hnt codes flag d c)
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
  exact liftConfig_boundedInitial (program hnt codes flag d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _

theorem start_input {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input hnt codes flag p x) =
      liftConfig (program hnt codes flag
        (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)))
      (initial nt (width nt p x)
        (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start,
    StandardBitCountedPolynomialPayload.payload_layout]
  exact (initial_lift hnt codes flag _ _ _ x).symm

theorem compact_actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input hnt codes flag p x))
      (List.replicate (deadline nt (width nt p x)
        (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x) false) =
      some (liftConfig (program hnt codes flag
        (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)))
        (final codes flag (width nt p x)
          (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
          (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0]
  rw [actual_run hnt codes flag _ _ _
    (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x)]
  rfl

noncomputable def compactDeadline (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  deadline nt (width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x

noncomputable def clockWidth (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpDelimiterInput.clockWidth (paddedPolynomial nt p) x

theorem compact_deadline_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 60 * (2 ^ width nt p x) ^ 2 := by
  have hD := ULogTernaryGuardedPumpDelimiterInput.deadline_upper (paddedPolynomial nt p) x
  have hb := width_lower nt p x
  have hnt : nt ≤ 2 ^ width nt p x :=
    (self_le_pow_two nt).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega))
  have hn : x.length ≤ 2 ^ width nt p x :=
    (self_le_pow_two x.length).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega))
  have hprod : nt * x.length ≤ 2 ^ width nt p x :=
    (generated_reserve_fits nt p x).trans (Nat.sub_le _ _)
  have hA := Nat.mul_le_mul hprod hn
  have hB := Nat.mul_le_mul hnt hprod
  have hR : 1 ≤ 2 ^ width nt p x := by
    have hpos : 0 < 2 ^ width nt p x := by positivity
    omega
  have hR2 : 2 ^ width nt p x ≤ (2 ^ width nt p x) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  change ULogTernaryGuardedPumpDelimiterInput.deadline (paddedPolynomial nt p) x + 2 +
    ULogTernarySourceLoopExecution.deadline nt x.length ≤ _
  rw [ULogTernarySourceLoopExecution.deadline_eq]
  change _ ≤ 60 * (2 ^ width nt p x) ^ 2
  change _ ≤ 43 * (2 ^ width nt p x) ^ 2 at hD
  rw [pow_two] at hD hR2 ⊢
  nlinarith

theorem compact_deadline_le_clock (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 2 ^ clockWidth nt p x := by
  have hD := compact_deadline_upper nt p x
  have hs := ULogTernaryGuardedPumpDelimiterInput.source_length_ge (paddedPolynomial nt p) x
  have hfactor : 64 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
      (paddedPolynomial nt p) x).length + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 6 ≤ _)
  have hsum : clockWidth nt p x = 2 * width nt p x +
      (2 * (ULogTernaryGuardedPumpDelimiterInput.source (paddedPolynomial nt p) x).length + 3) := by
    unfold clockWidth ULogTernaryGuardedPumpDelimiterInput.clockWidth width
    omega
  have hsq : (2 ^ width nt p x) ^ 2 = 2 ^ (2 * width nt p x) := by
    rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hD
  rw [hsum, pow_add]
  exact hD.trans (by nlinarith)

theorem compact_cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes flag p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact cutoff_counts hnt codes flag _ _ _
    (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x) T

theorem compact_every_raw_clock {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input hnt codes flag p x)) w = some out) :
    w.length ≤ 2 ^ clockWidth nt p x := by
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, _⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl _ hw (head := 0)
  exact (every_raw_length hnt codes flag _ _ _
    (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x) hz).2.trans
      (compact_deadline_le_clock nt p x)

theorem loop_occupied (nt k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hspace : nt * x.length ≤ 2 ^ k - 1) :
    ULogTernarySourceLoopExecution.occupied nt x (under k d c x) (buffer nt k x) =
      ULogTernaryGuardedPumpDelimiterSpace.peak k d c x := by
  have old := ULogTernaryGuardedPumpDelimiterSpace.delimiter_occupied k d c x hc
  unfold ULogTernarySourceLoopExecution.occupied under buffer
    ULogTernaryCountedSourceDelimiterSpace.occupied ULogTernaryGuardedPumpDelimiter.buffer at *
  simp only [List.length_cons, List.length_replicate, List.length_append,
    ULogTernaryCountedSourceDelimiter.ones] at *
  rw [Nat.add_mul, Nat.one_mul]
  have hR : 0 < 2 ^ k := by positivity
  omega

theorem every_raw_space {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes flag d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x ∧ -1 ≤ hf ∧
      hf ≤ (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat) := by
  have split := ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernarySourceLoopExecution.program hnt codes flag)
    (prefix_states_ge d c) (loop_states_ge nt) .stay (2 : Fin 3)
    (ULogTernaryGuardedPumpDelimiter.program_falseOnly d c)
    (ULogTernaryGuardedPumpDelimiter.deadline k d c x) 0
    (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
    (ULogTernaryGuardedPumpDelimiter.initial k d c x)
    (ULogTernaryGuardedPumpDelimiter.final k d c x)
    (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
    (ULogTernaryGuardedPumpDelimiter.final_accepts k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · exact ULogTernaryGuardedPumpDelimiterSpace.every_raw_space k d c hc x w hf zp hp
  · exact ULogTernaryGuardedPumpDelimiterSpace.every_raw_space k d c hc x
      (List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false)
      (ULogTernaryGuardedPumpDelimiter.finalHead k d c x)
      (ULogTernaryGuardedPumpDelimiter.final k d c x)
      (ULogTernaryGuardedPumpDelimiter.actual_run k d c hc x)
  · rw [second_start nt k d c x hspace] at hq
    have raw := ULogTernarySourceLoopExecution.every_raw hnt codes flag x
      (under k d c x) (buffer nt k x) (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) hq
    have hh := raw.2.2.2.1
    have hl := raw.2.2.1
    have hs : (ULogTernaryGuardedPumpSentinel.source d c x).length =
        (ULogTernaryNestedHeaderParser.header d c x).length + 2 * x.length + 1 := by
      simp [ULogTernaryGuardedPumpSentinel.source, ULogTernaryNestedHeaderParser.nested_length,
        ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
    refine ⟨raw.2.2.2.2.1.le.trans (loop_occupied nt k d c hc x hspace).le, ?_, ?_⟩
    · unfold ULogTernaryGuardedPumpDelimiter.finalHead ULogTernaryGuardedPumpDelimiter.prefixHead at hl
      omega
    · have hmax : k + 1 + (ULogTernaryNestedHeaderParser.header d c x).length +
          (x.length + 1) + (nt + 1) * x.length ≤
          k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k := by
        rw [Nat.add_mul]
        have hR : 0 < 2 ^ k := by positivity
        omega
      have hmaxInt : ULogTernaryGuardedPumpDelimiter.finalHead k d c x +
          (((nt + 1) * x.length : Nat) : Int) ≤
          (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat) := by
        unfold ULogTernaryGuardedPumpDelimiter.finalHead ULogTernaryGuardedPumpDelimiter.prefixHead
        exact_mod_cast hmax
      exact hh.trans hmaxInt

theorem initial_edges (nt k d c : Nat) (x : List Bool) :
    leftEdge 0 (initial nt k d c x) = 0 ∧
      rightEdge 0 (initial nt k d c x) =
        (k + (ULogTernaryGuardedPumpSentinel.source d c x).length : Nat) :=
  ULogTernaryGuardedPumpDelimiterSpace.initial_edges k d c x

theorem every_raw_growth {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes flag d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes flag d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k := by
  obtain ⟨lg, rg, growth⟩ := every_actual_run (program hnt codes flag d c) 2 w 0 hf _ out hw
  have edges := initial_edges nt k d c x
  have hp : (0 : Int) ≤ (2 ^ k : Nat) := Nat.cast_nonneg _
  have bounds := every_run_extents (program hnt codes flag d c) 2 w 0 hf (-1)
    (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k : Nat)
    (initial nt k d c x) out (by rw [edges.1]; omega) (by rw [edges.2]; omega)
    (fun v h z hz => (every_raw_space hnt codes flag k d c hc x hspace hz).2) hw
  have ledger := growth.exact_ledger
  rw [edges.1, edges.2] at ledger
  exact ⟨lg, rg, growth, by omega, by omega⟩

theorem every_raw_ready {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (totalStates nt d c) 3}
    (hw : run (program hnt codes flag d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes flag d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k ∧
      ∀ C tail, 2 ^ k + (totalStates nt d c - 1) ≤ C →
        ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun
          (program hnt codes flag d c) w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) ∧
        ULogFiniteTapePhysicalResourceLedger.resourceRun
          (program hnt codes flag d c) 2 w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) =
            some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, growth, hlg, hrg⟩ := every_raw_growth hnt codes flag k d c hc x hspace hw
  refine ⟨lg, rg, growth, hlg, hrg, ?_⟩
  intro C tail capacity
  refine ⟨?_, ULogFiniteTapePhysicalResourceLedger.actual_resource_run growth C
    (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes flag d c) C (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes flag d c) C tail (by omega)

def guardWord (k d c : Nat) (x : List Bool) : List Bool :=
  List.replicate (ULogTernaryGuardedPumpDelimiter.deadline k d c x) false ++ [false]

def guard (nt k d c : Nat) (x : List Bool) : BoundedConfig (totalStates nt d c) 3 :=
  ULogFiniteTapeGuardedStageComposition.guardConfig 2 .stay
    (ULogTernaryGuardedPumpDelimiter.final k d c x)

theorem actual_guard_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    run (program hnt codes flag d c) 2 (guardWord k d c x) 0 (initial nt k d c x) =
      some (ULogTernaryGuardedPumpDelimiter.finalHead k d c x, guard nt k d c x) := by
  unfold guardWord initial program
  rw [run_append, ULogFiniteTapeGuardedStageComposition.run_left
    (ULogTernaryGuardedPumpDelimiter.program d c) (ULogTernarySourceLoopExecution.program hnt codes flag)
    (prefix_states_ge d c) (loop_states_ge nt) .stay (2 : Fin 3) _ 0
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
    (hspace : nt * x.length ≤ 2 ^ k - 1) :
    cellCount (guard nt k d c x) = ULogTernaryGuardedPumpDelimiterSpace.peak k d c x := by
  have count := congrArg cellCount (second_start nt k d c x hspace)
  change cellCount (ULogTernaryGuardedPumpDelimiter.final k d c x) = _ at count
  rw [ULogTernarySourceLoopExecution.occupied_initial, loop_occupied nt k d c hc x hspace] at count
  exact count

theorem actual_guard_growth {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1) :
    GrowthRun (program hnt codes flag d c) 2 (guardWord k d c x) 0 (initial nt k d c x)
      (ULogTernaryGuardedPumpDelimiter.finalHead k d c x) (guard nt k d c x) 1 (2 ^ k) := by
  obtain ⟨lg, rg, growth, hl, hr⟩ := every_raw_growth hnt codes flag k d c hc x hspace
    (actual_guard_run hnt codes flag k d c hc x)
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
        List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false := by
  simp [deadline, guardWord, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

theorem full_active_ready_iff {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (k d c : Nat) (hc : 0 < c) (x : List Bool) (hspace : nt * x.length ≤ 2 ^ k - 1)
    (C : Nat) (tail : List ULogProgram.Tape) :
    ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program hnt codes flag d c)
        (List.replicate (deadline nt k d c x) false) 0 (initial nt k d c x) C
        (MStarConcreteAlphabet.work :: tail) ↔ 2 ^ k + (totalStates nt d c - 1) ≤ C := by
  constructor
  · intro active
    rw [whole_word_split] at active
    have resources := ULogFiniteTapePhysicalResourceLedger.actual_resource_run
      (actual_guard_growth hnt codes flag k d c hc x hspace) C (MStarConcreteAlphabet.work :: tail)
    have suffix := ULogFiniteTapeActiveReadySuffix.suffix_of_resource_run (program hnt codes flag d c)
      (guardWord k d c x) (false :: List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false)
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
    obtain ⟨_, _, _, _, _, ready⟩ := every_raw_ready hnt codes flag k d c hc x hspace
      (actual_run hnt codes flag k d c hc x hspace)
    exact (ready C tail capacity).1

noncomputable def compactStates (nt : Nat) (p : Polynomial Nat) : Nat :=
  totalStates nt (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p))

noncomputable def compactProgram {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (flag : Bool) (p : Polynomial Nat) :
    BoundedProgram (totalStates nt
      (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
      (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p))) 3 :=
  program hnt codes flag (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p))

noncomputable def compactInitial (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  initial nt (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x

noncomputable def compactFinal {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (p : Polynomial Nat) (x : List Bool) :=
  final codes flag (width nt p x) (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x

noncomputable def compactPeak (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  ULogTernaryGuardedPumpDelimiterSpace.peak (width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (paddedPolynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (paddedPolynomial nt p)) x

theorem polynomial_dominates (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    p.eval x.length ≤ width nt p x := by
  have h := StandardBitCountedPolynomialPayload.width_dominates (paddedPolynomial nt p) x
  simp only [paddedPolynomial, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h
  exact Nat.le_trans (by omega) h

theorem compact_every_raw_clock_symbols_space {nt : Nat} (hnt : 0 < nt)
    (codes : Fin 3 → Fin nt) (flag : Bool) (p : Polynomial Nat) (x w : List Bool)
    (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input hnt codes flag p x)) w = some out) :
    w.length ≤ 2 ^ clockWidth nt p x ∧ ULogBootstrapExecution.SemanticTapeSymbolsLtThree out ∧
      out.leftRev.length + 1 + out.right.length ≤ compactPeak nt p x := by
  have ht := compact_every_raw_clock hnt codes flag p x w out hw
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, he⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl _ hw (head := 0)
  rw [← he]
  refine ⟨ht, ULogTernaryPumpInputSpec.lift_symbols _ _, ?_⟩
  have hs := (every_raw_space hnt codes flag _ _ _
    (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x) hz).1
  simpa [compactPeak, liftConfig, cellCount] using hs

/-- The reserve and time certificates in this compact-input statement are
proved internally. Its readiness equivalence is the intermediate logical
resource predicate, not an ALL-physical-path low-capacity rejection theorem. -/
theorem generated_source_input_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (flag : Bool) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes flag p) ∧
    (∀ x, p.eval x.length ≤ width nt p x) ∧
    (∀ x, nt * x.length ≤ 2 ^ width nt p x - 1) ∧
    (∀ x, semanticRun (ULogSemantics.start (input hnt codes flag p x))
      (List.replicate (compactDeadline nt p x) false) =
      some (liftConfig (compactProgram hnt codes flag p) (compactFinal codes flag p x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes flag p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input hnt codes flag p x)) w = some out →
      w.length ≤ 2 ^ clockWidth nt p x ∧ ULogBootstrapExecution.SemanticTapeSymbolsLtThree out ∧
        out.leftRev.length + 1 + out.right.length ≤ compactPeak nt p x) ∧
    (∀ x w hf zf, run (compactProgram hnt codes flag p) 2 w 0 (compactInitial nt p x) = some (hf, zf) →
      ∃ lg rg, GrowthRun (compactProgram hnt codes flag p) 2 w 0 (compactInitial nt p x) hf zf lg rg ∧
        lg ≤ 1 ∧ rg ≤ 2 ^ width nt p x ∧
        ∀ C tail, 2 ^ width nt p x + (compactStates nt p - 1) ≤ C →
          ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun
            (compactProgram hnt codes flag p) w 0 (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) ∧
          ULogFiniteTapePhysicalResourceLedger.resourceRun
            (compactProgram hnt codes flag p) 2 w 0 (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) =
              some (hf, zf, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg)) ∧
    (∀ x, ULogBootstrapExecution.decodeBinaryClock (List.replicate (clockWidth nt p x) (ULogAlphabet.ulogCore ULogAlphabet.clockZero) ++
      ULogAlphabet.ulogCore ULogAlphabet.clockOne :: [ULogAlphabet.ulogCore ULogAlphabet.clockSep]) =
        some (2 ^ clockWidth nt p x)) ∧
    (∀ x C tail, ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun
      (compactProgram hnt codes flag p) (List.replicate (compactDeadline nt p x) false) 0
      (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) ↔
        2 ^ width nt p x + (compactStates nt p - 1) ≤ C) := by
  refine ⟨input_polyBitTime hnt codes flag p, polynomial_dominates nt p,
    generated_reserve_fits nt p, compact_actual_run hnt codes flag p, compact_cutoff_counts hnt codes flag p,
    compact_every_raw_clock_symbols_space hnt codes flag p, ?_, ?_, ?_⟩
  · intro x w hf zf hw
    exact every_raw_ready hnt codes flag _ _ _
      (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x) hw
  · intro x
    exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth nt p x) []
  · intro x C tail
    exact full_active_ready_iff hnt codes flag _ _ _
      (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x (generated_reserve_fits nt p x) C tail

end PakFixedPolyomino.ULogTernaryGeneratedSourceExpansion
