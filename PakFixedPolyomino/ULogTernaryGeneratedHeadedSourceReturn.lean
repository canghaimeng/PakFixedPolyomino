import PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceResources
import PakFixedPolyomino.ULogTernaryDelimitedBinarySweep

/-! The compact headed loader followed by an actual left return. The old
accept state becomes live and one real STAY tick enters the reflected sweep.
The source's retained original unary counter is exposed at the left marker.
Reserve sealing, margins and the final scanner handoff remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceReturn
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger ULogFiniteTapeStageComposition
open ULogTernaryRetainedCounterPump (cell cells)
variable {nt : Nat}

def sourceBits (codes : Fin 3 → Fin nt) (x : List Bool) : List Bool :=
  (ULogTernaryPreparedHeadedSourceExpansion.markedSource codes x).flatMap
    (fun z => z.head :: ULogSourceOneHotBlocks.encodeOneHot z.symbol)
theorem source_encoding (codes : Fin 3 → Fin nt) (x : List Bool) :
    cells (sourceBits codes x) = ULogSourceObliviousWindow.encodeWindow
      (ULogTernaryPreparedHeadedSourceExpansion.markedSource codes x) := by
  simp [sourceBits, cells, ULogSourceObliviousWindow.encodeWindow,
    ULogSourceObliviousWindow.encodeMarkedCell,
    ULogTernaryPreparedHeadedSourceExpansion.cell_tapeOfBit, List.map_flatMap]
  rfl
theorem source_length (codes : Fin 3 → Fin nt) (x : List Bool) :
    (sourceBits codes x).length = ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) := by
  have h := congrArg List.length (source_encoding codes x)
  simpa [cells, ULogTernaryPreparedHeadedSourceExpansion.markedSource] using h

def retained (k d c : Nat) (x : List Bool) : List (Fin 3) :=
  ULogTernaryCountedSourceDelimiter.ones x.length ++
    2 :: ULogTernaryGuardedPumpDelimiter.under k d c x
def pool (nt k : Nat) (x : List Bool) : List (Fin 3) :=
  ULogTernaryPreparedHeadedSourceExpansion.remaining x
    (ULogTernaryGeneratedHeadedSourceExpansion.buffer nt k x)
abbrev childStates (nt d c : Nat) := ULogTernaryGeneratedHeadedSourceExpansion.totalStates nt d c
abbrev states (nt d c : Nat) := stateCount (childStates nt d c) 4

theorem child_states_ge (nt d c : Nat) : 3 ≤ childStates nt d c := by
  have := ULogTernaryGeneratedHeadedSourceExpansion.prefix_states_ge d c
  have := ULogTernaryGeneratedHeadedSourceExpansion.prepared_states_ge nt
  unfold childStates ULogTernaryGeneratedHeadedSourceExpansion.totalStates
    ULogFiniteTapeGuardedStageComposition.stateCount; omega

def program (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (d c : Nat) :
    BoundedProgram (states nt d c) 3 :=
  ULogFiniteTapeStageComposition.program
    (ULogTernaryGeneratedHeadedSourceExpansion.program hnt codes d c)
    ULogTernaryDelimitedBinarySweep.leftProgram (child_states_ge nt d c) (by decide) .stay
def initial (nt k d c : Nat) (x : List Bool) : BoundedConfig (states nt d c) 3 :=
  leftConfig (ULogTernaryGeneratedHeadedSourceExpansion.initial nt k d c x)
def final (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    BoundedConfig (states nt d c) 3 :=
  rightConfig (ULogTernaryDelimitedBinarySweep.leftFinal (sourceBits codes x).reverse
    (pool nt k x) (retained k d c x))
def deadline (nt k d c : Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedHeadedSourceExpansion.deadline nt k d c x + 1 +
    ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) + 2
def finalHead (nt k d c : Nat) (x : List Bool) : Int :=
  ULogTernaryGeneratedHeadedSourceExpansion.finalHead nt k d c x -
    (((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) + 1 : Nat)

theorem second_start (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    secondStart (by decide : 3 ≤ 4) (2 : Fin 3) .stay
      (ULogTernaryGeneratedHeadedSourceExpansion.final codes k d c x) =
      ULogTernaryDelimitedBinarySweep.leftInitial (sourceBits codes x).reverse
        (pool nt k x) (retained k d c x) := by
  have ht := ULogTernaryGeneratedHeadedSourceExpansion.final_tape codes k d c x
  simp only [secondStart, applyBounded]
  rw [ht.1, ht.2.1, ht.2.2]
  rw [← source_encoding codes x]
  simp [ULogTernaryDelimitedBinarySweep.leftInitial,
    ULogFiniteTapeReflection.reflectConfig, ULogTernaryDelimitedBinarySweep.initial,
    cells, List.map_reverse, source_encoding, pool, retained,
    ULogTernaryGeneratedHeadedSourceExpansion.under,
    ULogTernaryGeneratedSourceExpansion.under]

theorem actual_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hspace : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) :
    run (program hnt codes d c) 2 (List.replicate (deadline nt k d c x) false) 0
      (initial nt k d c x) = some (finalHead nt k d c x, final codes k d c x) := by
  have h := sequential_run
    (ULogTernaryGeneratedHeadedSourceExpansion.program hnt codes d c)
    ULogTernaryDelimitedBinarySweep.leftProgram (child_states_ge nt d c) (by decide) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryGeneratedHeadedSourceExpansion.deadline nt k d c x) false)
    (List.replicate (ULogTernaryDelimitedBinarySweep.deadline (sourceBits codes x).reverse) false)
    0 (ULogTernaryGeneratedHeadedSourceExpansion.finalHead nt k d c x) (finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceExpansion.initial nt k d c x)
    (ULogTernaryGeneratedHeadedSourceExpansion.final codes k d c x)
    (ULogTernaryDelimitedBinarySweep.leftFinal (sourceBits codes x).reverse
      (pool nt k x) (retained k d c x))
    (ULogTernaryGeneratedHeadedSourceExpansion.actual_run hnt codes k d c hc x hspace)
    (ULogTernaryGeneratedHeadedSourceExpansion.final_state codes k d c x) (by
      rw [second_start, FiniteOneTapeSemantics.moveHead]
      simpa only [finalHead, List.length_reverse, source_length] using
        ULogTernaryDelimitedBinarySweep.left_run (sourceBits codes x).reverse
          (pool nt k x) (retained k d c x)
          (ULogTernaryGeneratedHeadedSourceExpansion.finalHead nt k d c x))
  have hw : List.replicate (deadline nt k d c x) false =
      List.replicate (ULogTernaryGeneratedHeadedSourceExpansion.deadline nt k d c x) false ++
      false :: List.replicate (ULogTernaryDelimitedBinarySweep.deadline (sourceBits codes x).reverse) false := by
    simp [deadline, ULogTernaryDelimitedBinarySweep.deadline, source_length,
      List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]
  exact h

theorem final_accepts (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    (final codes k d c x).state.val = 0 :=
  (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2 rfl
theorem final_tape (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    (final codes k d c x).leftRev = retained k d c x ∧
    (final codes k d c x).focus = 2 ∧
    (final codes k d c x).right = cells (sourceBits codes x) ++ 2 :: pool nt k x := by
  simp [final, rightConfig, ULogTernaryDelimitedBinarySweep.leftFinal,
    ULogFiniteTapeReflection.reflectConfig, ULogTernaryDelimitedBinarySweep.final,
    cells, List.map_reverse]
theorem program_falseOnly (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (d c : Nat) :
    FalseOnly (program hnt codes d c) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernaryGeneratedHeadedSourceExpansion.program_falseOnly hnt codes d c)
    ULogTernaryDelimitedBinarySweep.left_falseOnly

theorem accepting_word (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hspace : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt k d c x) false ∧ hf = finalHead nt k d c x ∧
      out = final codes k d c x :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt codes d c)
    (deadline nt k d c x) 0 (initial nt k d c x) (final codes k d c x)
    (finalHead nt k d c x) (actual_run hnt codes k d c hc x hspace)
    (final_accepts codes k d c x) hw ha

theorem cutoff_counts (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hspace : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes d c) (initial nt k d c x)) =
        if deadline nt k d c x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes d c)
    (deadline nt k d c x) 0 (initial nt k d c x) (final codes k d c x)
    (finalHead nt k d c x) (actual_run hnt codes k d c hc x hspace)
    (final_accepts codes k d c x) T

set_option maxHeartbeats 1600000 in
theorem every_raw_space (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hspace : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x := by
  have split := ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGeneratedHeadedSourceExpansion.program hnt codes d c)
    ULogTernaryDelimitedBinarySweep.leftProgram (child_states_ge nt d c) (by decide) .stay (2 : Fin 3)
    (ULogTernaryGeneratedHeadedSourceExpansion.program_falseOnly hnt codes d c)
    (ULogTernaryGeneratedHeadedSourceExpansion.deadline nt k d c x) 0
    (ULogTernaryGeneratedHeadedSourceExpansion.finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceExpansion.initial nt k d c x)
    (ULogTernaryGeneratedHeadedSourceExpansion.final codes k d c x)
    (ULogTernaryGeneratedHeadedSourceExpansion.actual_run hnt codes k d c hc x hspace)
    (ULogTernaryGeneratedHeadedSourceExpansion.final_state codes k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · exact ULogTernaryGeneratedHeadedSourceResources.every_raw_space hnt codes k d c hc x hspace hp
  · have count : cellCount (secondStart (by decide : 3 ≤ 4) (2 : Fin 3) .stay
        (ULogTernaryGeneratedHeadedSourceExpansion.final codes k d c x)) =
        cellCount (ULogTernaryGeneratedHeadedSourceExpansion.final codes k d c x) := by
      simp [secondStart, applyBounded, cellCount]
    rw [second_start, FiniteOneTapeSemantics.moveHead] at hq
    have child := ULogTernaryDelimitedBinarySweep.left_every_raw (sourceBits codes x).reverse
      (pool nt k x) (retained k d c x)
      (ULogTernaryGeneratedHeadedSourceExpansion.finalHead nt k d c x) hq
    have hi : cellCount (ULogTernaryDelimitedBinarySweep.leftInitial (sourceBits codes x).reverse
        (pool nt k x) (retained k d c x)) =
        ULogTernaryDelimitedBinarySweep.occupied (sourceBits codes x).reverse
          (pool nt k x) (retained k d c x) := by
      simpa only [ULogTernaryDelimitedBinarySweep.leftInitial,
        ULogFiniteTapeReflection.cellCount_reflect] using
        ULogTernaryDelimitedBinarySweep.initial_cells (sourceBits codes x).reverse
          (pool nt k x) (retained k d c x)
    rw [second_start, hi] at count
    change cellCount zq ≤ _
    rw [child.2.2.1, count]
    exact ULogTernaryGeneratedHeadedSourceResources.every_raw_space hnt codes k d c hc x hspace
      (ULogTernaryGeneratedHeadedSourceExpansion.actual_run hnt codes k d c hc x hspace)

theorem every_raw (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hspace : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt k d c x ∧
      cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x :=
  ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes d c) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes d c)
      (deadline nt k d c x) 0 (initial nt k d c x) (final codes k d c x)
      (finalHead nt k d c x) (actual_run hnt codes k d c hc x hspace)
      (final_accepts codes k d c x) hw, every_raw_space hnt codes k d c hc x hspace hw⟩

noncomputable def compactProgram (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) : BoundedProgram
      (states nt (ULogTernaryGuardedPumpDelimiterInput.depth
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth
          (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))) 3 :=
  program hnt codes (ULogTernaryGuardedPumpDelimiterInput.depth
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
noncomputable def compactInitial (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  initial nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def compactFinal (codes : Fin 3 → Fin nt) (p : Polynomial Nat) (x : List Bool) :=
  final codes (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def compactDeadline (nt : Nat) (p : Polynomial Nat) (x : List Bool) :=
  deadline nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
noncomputable def input (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat)
    (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap (compactProgram hnt codes p)
    (StandardBitCountedPolynomialPayload.payload (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x)

theorem input_polyBitTime (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogPayloadClockBitWrapper.wrap_polyBitTime (compactProgram hnt codes p))

theorem initial_lift (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat) (x : List Bool) :
    liftConfig (program hnt codes d c) (initial nt k d c x) = ULogSemantics.start
      (encodeInstance (program hnt codes d c)
        (ULogTernaryRetainedCounterPump.sourceInput k
          (ULogTernaryGuardedPumpSentinel.source d c x))) := by
  have hb : cell = boundedBit (0 : Fin 3) 1 := by funext b; cases b <;> rfl
  have hi : initial nt k d c x = boundedInitial
      (⟨2, by have := child_states_ge nt d c; unfold states stateCount; omega⟩ : Fin (states nt d c))
      (0 : Fin 3) 1 2 (ULogTernaryRetainedCounterPump.sourceInput k
        (ULogTernaryGuardedPumpSentinel.source d c x)) := by
    cases k <;>
      simp [initial, ULogTernaryGeneratedHeadedSourceExpansion.initial,
        ULogTernaryGuardedPumpDelimiter.initial, ULogTernaryGuardedPumpSentinel.initial,
        ULogFiniteTapeGuardedStageComposition.leftConfig,
        ULogFiniteTapeGuardedStageComposition.leftState,
        leftConfig, leftState, ULogTernaryRetainedCounterPump.initial,
        ULogTernaryRetainedCounterPump.fromCells,
        ULogTernaryRetainedCounterPump.sourceInput, cells, hb,
        boundedInitial, boundedBit, List.replicate_succ]
  rw [hi]
  exact liftConfig_boundedInitial (program hnt codes d c) _ (0 : Fin 3) 1 2 rfl rfl rfl rfl _

theorem start_input (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input hnt codes p x) = liftConfig (compactProgram hnt codes p) (compactInitial nt p x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitCountedPolynomialPayload.payload_layout]
  exact (initial_lift hnt codes _ _ _ x).symm

theorem compact_actual_run (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input hnt codes p x))
      (List.replicate (compactDeadline nt p x) false) =
        some (liftConfig (compactProgram hnt codes p) (compactFinal codes p x)) := by
  rw [start_input, ← run_lift _ (2 : Fin 3) rfl _ 0]
  simp only [compactProgram, compactInitial, compactDeadline, compactFinal]
  rw [actual_run hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
    x (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x)]
  rfl

theorem compact_cutoff_counts (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes p x)) =
      if compactDeadline nt p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact cutoff_counts hnt codes _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _)
    x (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x) T

end PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceReturn
