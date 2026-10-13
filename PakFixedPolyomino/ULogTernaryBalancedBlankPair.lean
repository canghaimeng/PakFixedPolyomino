import PakFixedPolyomino.ULogTernaryBlankBlockInsertion
import PakFixedPolyomino.ULogTernaryBlankBlockAppend
import PakFixedPolyomino.ULogTernaryDelimitedBinarySweep

/-! One actual blank block at each end of an arbitrary binary encoded window.
The controller depends only on the finite alphabet, consumes two allocated
blocks of reserve zeros and returns to the original left delimiter. This
module does not assert a repeated loop or ordinary source-window alignment. -/
namespace PakFixedPolyomino.ULogTernaryBalancedBlankPair
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogFiniteTapeStageComposition

def block {nt : Nat} (blank : Fin nt) : List Bool :=
  false :: ULogSourceOneHotBlocks.encodeOneHot blank

theorem block_length {nt : Nat} (blank : Fin nt) : (block blank).length = nt + 1 := by
  simp [block]

theorem block_cells {nt : Nat} (blank : Fin nt) :
    cells (block blank) = 0 :: ULogTernaryOneHotBlockWriter.bits blank := rfl

abbrev prefixStates (nt : Nat) :=
  ULogFiniteTapeSymbolDispatch.stateCount (ULogTernaryBlankBlockInsertion.stateCount nt)
abbrev sweepStates (nt : Nat) := stateCount (prefixStates nt) 4
abbrev appendStates (nt : Nat) := stateCount (sweepStates nt)
  (ULogTernaryBlankBlockAppend.stateCount nt)
abbrev states (nt : Nat) := stateCount (appendStates nt) 4

theorem prefix_states_ge (nt : Nat) : 3 ≤ prefixStates nt := by
  unfold prefixStates ULogFiniteTapeSymbolDispatch.stateCount stateCount; omega
theorem sweep_states_ge (nt : Nat) : 3 ≤ sweepStates nt := by
  have := prefix_states_ge nt; unfold sweepStates stateCount; omega
theorem append_child_ge (nt : Nat) : 3 ≤ ULogTernaryBlankBlockAppend.stateCount nt := by
  have := ULogTernaryBlankBlockAppend.child_states_ge nt
  unfold ULogTernaryBlankBlockAppend.stateCount stateCount; omega
theorem append_states_ge (nt : Nat) : 3 ≤ appendStates nt := by
  have := sweep_states_ge nt; unfold appendStates stateCount; omega

def prefixEntry (nt : Nat) : Fin (ULogTernaryBlankBlockInsertion.stateCount nt) :=
  (ULogTernaryBlankBlockInsertion.initial nt [] [] []).state

def prefixProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (prefixStates nt) 3 :=
  ULogFiniteTapeSymbolDispatch.program (ULogTernaryBlankBlockInsertion.program hnt blank)
    (fun _ => prefixEntry nt) 2
def sweepProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (sweepStates nt) 3 :=
  program (prefixProgram hnt blank) ULogTernaryDelimitedBinarySweep.program
    (prefix_states_ge nt) (by decide) .stay
def appendProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (appendStates nt) 3 :=
  program (sweepProgram hnt blank) (ULogTernaryBlankBlockAppend.program hnt blank)
    (sweep_states_ge nt) (append_child_ge nt) .stay
def pairProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (states nt) 3 :=
  program (appendProgram hnt blank) ULogTernaryDelimitedBinarySweep.leftProgram
    (append_states_ge nt) (by decide) .stay

def prefixInitial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (prefixStates nt) 3 :=
  ULogFiniteTapeSymbolDispatch.initial 2 under
    (cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer)
def prefixFinal {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (prefixStates nt) 3 :=
  rightConfig (ns := 3) (ULogTernaryBlankBlockInsertion.final blank source under buffer)
def sweepInitial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (sweepStates nt) 3 := leftConfig (prefixInitial nt source under buffer)
def sweepFinal {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (sweepStates nt) 3 :=
  rightConfig (ULogTernaryDelimitedBinarySweep.final (block blank ++ source) under buffer)
def appendInitial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (appendStates nt) 3 := leftConfig
      (sweepInitial nt source under (List.replicate (nt + 1) 0 ++ buffer))
def appendFinal {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (appendStates nt) 3 :=
  rightConfig (ULogTernaryBlankBlockAppend.final blank
    ((cells (block blank ++ source)).reverse ++ 2 :: under) buffer)
def initial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (states nt) 3 := leftConfig (appendInitial nt source under buffer)
def final {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (states nt) 3 :=
  rightConfig (ULogTernaryDelimitedBinarySweep.leftFinal
    (block blank ++ source ++ block blank).reverse buffer under)

def prefixTicks (nt n : Nat) := ULogTernaryBlankBlockInsertion.deadline nt n + 1
def sweepTicks (nt n : Nat) := prefixTicks nt n + 1 + (n + nt + 1 + 2)
def appendTicks (nt n : Nat) := sweepTicks nt n + 1 + ULogTernaryBlankBlockAppend.deadline nt
def deadline (nt n : Nat) := appendTicks nt n + 1 + (n + 2 * (nt + 1) + 2)

theorem replicate_comp (a b : Nat) :
    List.replicate (a + 1 + b) false =
      List.replicate a false ++ false :: List.replicate b false := by
  rw [show a + 1 + b = a + (b + 1) by omega, List.replicate_add, List.replicate_succ]

theorem prefix_dispatched (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeSymbolDispatch.dispatched (fun _ => prefixEntry nt) 2 (2 : Fin 3)
      under (cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer) =
        ULogTernaryBlankBlockInsertion.initial nt source under buffer := rfl

theorem prefix_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (prefixProgram hnt blank) 2 (List.replicate (prefixTicks nt source.length) false)
      H (prefixInitial nt source under buffer) = some (H, prefixFinal blank source under buffer) := by
  unfold prefixProgram prefixInitial prefixTicks
  rw [List.replicate_succ, ULogFiniteTapeSymbolDispatch.run_dispatch_cons,
    prefix_dispatched, ULogTernaryBlankBlockInsertion.actual_run hnt blank source under buffer H]
  rfl

theorem prefix_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (prefixFinal blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryBlankBlockInsertion.final_accepts blank source under buffer)

theorem sweep_second_start {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    secondStart (by decide : 3 ≤ 4) (2 : Fin 3) .stay
      (prefixFinal blank source under buffer) =
        ULogTernaryDelimitedBinarySweep.initial (block blank ++ source) under buffer := by
  simp [secondStart, applyBounded, prefixFinal, rightConfig,
    ULogTernaryBlankBlockInsertion.final, ULogTernaryDelimitedBinarySweep.initial,
    block, ULogTernaryOneHotBlockWriter.bits, cells, cell, List.append_assoc]

theorem sweep_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (sweepProgram hnt blank) 2 (List.replicate (sweepTicks nt source.length) false)
      H (sweepInitial nt source under buffer) =
        some (H + ((source.length + nt + 2 : Nat) : Int), sweepFinal blank source under buffer) := by
  have h := sequential_run (prefixProgram hnt blank) ULogTernaryDelimitedBinarySweep.program
    (prefix_states_ge nt) (by decide) .stay (2 : Fin 3)
    (List.replicate (prefixTicks nt source.length) false)
    (List.replicate (ULogTernaryDelimitedBinarySweep.deadline (block blank ++ source)) false)
    H H (H + ((source.length + nt + 2 : Nat) : Int))
    (prefixInitial nt source under buffer) (prefixFinal blank source under buffer)
    (ULogTernaryDelimitedBinarySweep.final (block blank ++ source) under buffer)
    (prefix_run hnt blank source under buffer H) (prefix_accepts blank source under buffer) (by
      rw [sweep_second_start, FiniteOneTapeSemantics.moveHead]
      simpa only [List.length_append, block_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ULogTernaryDelimitedBinarySweep.actual_run (block blank ++ source) under buffer H)
  have ticks : sweepTicks nt source.length = prefixTicks nt source.length + 1 +
      ULogTernaryDelimitedBinarySweep.deadline (block blank ++ source) := by
    simp [sweepTicks, ULogTernaryDelimitedBinarySweep.deadline, block_length]; omega
  unfold sweepProgram sweepInitial sweepFinal
  rw [ticks, replicate_comp]
  exact h

theorem sweep_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (sweepFinal blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2 rfl

theorem append_second_start {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    secondStart (append_child_ge nt) (2 : Fin 3) .stay
      (sweepFinal blank source under (List.replicate (nt + 1) 0 ++ buffer)) =
        ULogTernaryBlankBlockAppend.initial nt
          ((cells (block blank ++ source)).reverse ++ 2 :: under) buffer := by
  simp [secondStart, applyBounded, sweepFinal, rightConfig,
    ULogTernaryDelimitedBinarySweep.final, ULogTernaryBlankBlockAppend.initial,
    leftConfig, leftState, ULogTernaryEmptyHeadPreparation.initial,
    ULogTernaryCountedSourceDelimiter.fromCells, cells, List.replicate_succ]

theorem append_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (appendProgram hnt blank) 2 (List.replicate (appendTicks nt source.length) false)
      H (appendInitial nt source under buffer) =
        some (H + ((source.length + 2 * (nt + 1) + 1 : Nat) : Int),
          appendFinal blank source under buffer) := by
  have h := sequential_run (sweepProgram hnt blank) (ULogTernaryBlankBlockAppend.program hnt blank)
    (sweep_states_ge nt) (append_child_ge nt) .stay (2 : Fin 3)
    (List.replicate (sweepTicks nt source.length) false)
    (List.replicate (ULogTernaryBlankBlockAppend.deadline nt) false)
    H (H + ((source.length + nt + 2 : Nat) : Int))
    (H + ((source.length + 2 * (nt + 1) + 1 : Nat) : Int))
    (sweepInitial nt source under (List.replicate (nt + 1) 0 ++ buffer))
    (sweepFinal blank source under (List.replicate (nt + 1) 0 ++ buffer))
    (ULogTernaryBlankBlockAppend.final blank
      ((cells (block blank ++ source)).reverse ++ 2 :: under) buffer)
    (sweep_run hnt blank source under (List.replicate (nt + 1) 0 ++ buffer) H)
    (sweep_accepts blank source under _) (by
      rw [append_second_start, FiniteOneTapeSemantics.moveHead]
      convert ULogTernaryBlankBlockAppend.actual_run hnt blank
        ((cells (block blank ++ source)).reverse ++ 2 :: under) buffer
        (H + ((source.length + nt + 2 : Nat) : Int)) using 1 <;> push_cast <;> ring)
  unfold appendProgram appendInitial appendFinal appendTicks
  rw [replicate_comp]
  exact h

theorem append_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (appendFinal blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryBlankBlockAppend.final_accepts blank _ _)

theorem left_second_start {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    secondStart (by decide : 3 ≤ 4) (2 : Fin 3) .stay
      (appendFinal blank source under buffer) =
        ULogTernaryDelimitedBinarySweep.leftInitial
          (block blank ++ source ++ block blank).reverse buffer under := by
  have ht := ULogTernaryBlankBlockAppend.final_tape blank
    ((cells (block blank ++ source)).reverse ++ 2 :: under) buffer
  simp only [secondStart, applyBounded, appendFinal, rightConfig]
  rw [ht.1, ht.2.1, ht.2.2]
  simp [ULogTernaryDelimitedBinarySweep.leftInitial,
    ULogFiniteTapeReflection.reflectConfig, ULogTernaryDelimitedBinarySweep.initial,
    cells, cell, block, ULogTernaryOneHotBlockWriter.bits, List.map_reverse,
    List.reverse_append, List.append_assoc]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (pairProgram hnt blank) 2 (List.replicate (deadline nt source.length) false)
      H (initial nt source under buffer) = some (H, final blank source under buffer) := by
  have h := sequential_run (appendProgram hnt blank) ULogTernaryDelimitedBinarySweep.leftProgram
    (append_states_ge nt) (by decide) .stay (2 : Fin 3)
    (List.replicate (appendTicks nt source.length) false)
    (List.replicate (ULogTernaryDelimitedBinarySweep.deadline
      (block blank ++ source ++ block blank).reverse) false)
    H (H + ((source.length + 2 * (nt + 1) + 1 : Nat) : Int)) H
    (appendInitial nt source under buffer) (appendFinal blank source under buffer)
    (ULogTernaryDelimitedBinarySweep.leftFinal
      (block blank ++ source ++ block blank).reverse buffer under)
    (append_run hnt blank source under buffer H) (append_accepts blank source under buffer) (by
      rw [left_second_start, FiniteOneTapeSemantics.moveHead]
      convert ULogTernaryDelimitedBinarySweep.left_run
        (block blank ++ source ++ block blank).reverse buffer under
        (H + ((source.length + 2 * (nt + 1) + 1 : Nat) : Int)) using 1
      simp only [List.length_reverse, List.length_append, block_length]
      push_cast; ring)
  have ticks : deadline nt source.length = appendTicks nt source.length + 1 +
      ULogTernaryDelimitedBinarySweep.deadline
        (block blank ++ source ++ block blank).reverse := by
    simp [deadline, ULogTernaryDelimitedBinarySweep.deadline, block_length]; omega
  unfold pairProgram initial final
  rw [ticks, replicate_comp]
  exact h

theorem final_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (final blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2 rfl

theorem final_tape {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    (final blank source under buffer).leftRev = under ∧
    (final blank source under buffer).focus = 2 ∧
    (final blank source under buffer).right =
      cells (block blank ++ source ++ block blank) ++ 2 :: buffer := by
  simp [final, rightConfig, ULogTernaryDelimitedBinarySweep.leftFinal,
    ULogFiniteTapeReflection.reflectConfig, ULogTernaryDelimitedBinarySweep.final,
    cells, List.map_reverse]

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (pairProgram hnt blank) := by
  apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
  · apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
    · apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
      · exact ULogFiniteTapeSymbolDispatch.program_falseOnly _ _ _
          (ULogTernaryBlankBlockInsertion.program_falseOnly hnt blank)
      · exact ULogTernaryDelimitedBinarySweep.program_falseOnly
    · exact ULogTernaryBlankBlockAppend.program_falseOnly hnt blank
  · exact ULogTernaryDelimitedBinarySweep.left_falseOnly

def occupied (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :=
  under.length + source.length + 2 * (nt + 1) + 2 + buffer.length

theorem initial_cells (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial nt source under buffer) = occupied nt source under buffer := by
  simp [initial, appendInitial, sweepInitial, prefixInitial, leftConfig,
    ULogFiniteTapeSymbolDispatch.initial, cellCount, cells, occupied]; omega

theorem final_cells {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (final blank source under buffer) = occupied nt source under buffer := by
  have ht := final_tape blank source under buffer
  simp only [cellCount, ht.1, ht.2.2, List.length_append, List.length_cons,
    cells, List.length_map, block_length]
  unfold occupied; omega

theorem every_raw {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt) 3}
    (hw : run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt source.length ∧
      cellCount out = occupied nt source under buffer ∧
      GrowthRun (pairProgram hnt blank) 2 w H (initial nt source under buffer) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt blank) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer)
    (final blank source under buffer) H (actual_run hnt blank source under buffer H)
    (final_accepts blank source under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (pairProgram hnt blank) 2 _ _ _ _ _
    (actual_run hnt blank source under buffer H)
  have ledger := hg.exact_ledger
  have hi := initial_cells nt source under buffer
  have ho := final_cells blank source under buffer
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (pairProgram hnt blank) 2 w H hf _ out hw
  have word : List.replicate (deadline nt source.length) false =
      w ++ List.replicate (deadline nt source.length - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using
      ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [word] at hg
  have le := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger1 := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt) 3}
    (hw : run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt source.length) false ∧ hf = H ∧
      out = final blank source under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer)
    (final blank source under buffer) H (actual_run hnt blank source under buffer H)
    (final_accepts blank source under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (pairProgram hnt blank) (initial nt source under buffer)) =
        if deadline nt source.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer)
    (final blank source under buffer) H (actual_run hnt blank source under buffer H)
    (final_accepts blank source under buffer) T

theorem deadline_eq {nt : Nat} (hnt : 0 < nt) (n : Nat) :
    deadline nt n = 2 * (nt + 2) * n + 2 * nt * nt + 20 * nt + 31 := by
  simp only [deadline, appendTicks, sweepTicks, prefixTicks,
    ULogTernaryBlankBlockInsertion.deadline_eq hnt,
    ULogTernaryBlankBlockAppend.deadline_eq]
  ring

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    ∀ r ∈ compile (pairProgram hnt blank), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (pairProgram hnt blank) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem balanced_blank_pair_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (run (pairProgram hnt blank) 2 (List.replicate (deadline nt source.length) false)
      H (initial nt source under buffer) = some (H, final blank source under buffer)) ∧
    (final blank source under buffer).leftRev = under ∧
    (final blank source under buffer).focus = 2 ∧
    (final blank source under buffer).right =
      cells (block blank ++ source ++ block blank) ++ 2 :: buffer ∧
    (∀ w hf out, run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt source.length ∧
        cellCount out = occupied nt source under buffer ∧
        GrowthRun (pairProgram hnt blank) 2 w H (initial nt source under buffer) hf out 0 0) ∧
    (∀ w hf out, run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      out.state.val = 0 → w = List.replicate (deadline nt source.length) false ∧
        hf = H ∧ out = final blank source under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (pairProgram hnt blank) (initial nt source under buffer)) =
        if deadline nt source.length ≤ T then 1 else 0) ∧
    (∀ r ∈ compile (pairProgram hnt blank), r.read < 3 ∧ r.action.write < 3) ∧
    deadline nt source.length = 2 * (nt + 2) * source.length + 2 * nt * nt + 20 * nt + 31 :=
  ⟨actual_run hnt blank source under buffer H, (final_tape blank source under buffer).1,
    (final_tape blank source under buffer).2.1, (final_tape blank source under buffer).2.2,
    fun _ _ _ => every_raw hnt blank source under buffer H,
    fun _ _ _ => accepting_word hnt blank source under buffer H,
    cutoff_counts hnt blank source under buffer H, compiled_symbols hnt blank,
    deadline_eq hnt source.length⟩

end PakFixedPolyomino.ULogTernaryBalancedBlankPair
