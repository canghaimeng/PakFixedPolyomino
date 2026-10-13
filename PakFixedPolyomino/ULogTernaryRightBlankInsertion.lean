import PakFixedPolyomino.ULogTernaryBalancedBlankPair

/-! One real blank block at the right end of a binary encoded window. This
is the additional right margin required by a nonempty ordinary input. The
caller must still determine original emptiness internally. -/
namespace PakFixedPolyomino.ULogTernaryRightBlankInsertion
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger ULogFiniteTapeStageComposition
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryBalancedBlankPair (block block_length replicate_comp)

abbrev middleStates (nt : Nat) := stateCount 4 (ULogTernaryBlankBlockAppend.stateCount nt)
abbrev states (nt : Nat) := stateCount (middleStates nt) 4
theorem middle_states_ge (nt : Nat) : 3 ≤ middleStates nt := by
  unfold middleStates stateCount; omega

def middleProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (middleStates nt) 3 :=
  program ULogTernaryDelimitedBinarySweep.program (ULogTernaryBlankBlockAppend.program hnt blank)
    (by decide) (ULogTernaryBalancedBlankPair.append_child_ge nt) .stay
def pairProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (states nt) 3 :=
  program (middleProgram hnt blank) ULogTernaryDelimitedBinarySweep.leftProgram
    (middle_states_ge nt) (by decide) .stay

def middleInitial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (middleStates nt) 3 := leftConfig
      (ULogTernaryDelimitedBinarySweep.initial source under (List.replicate (nt + 1) 0 ++ buffer))
def middleFinal {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (middleStates nt) 3 :=
  rightConfig (ULogTernaryBlankBlockAppend.final blank ((cells source).reverse ++ 2 :: under) buffer)
def initial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (states nt) 3 := leftConfig (middleInitial nt source under buffer)
def final {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (states nt) 3 :=
  rightConfig (ULogTernaryDelimitedBinarySweep.leftFinal (source ++ block blank).reverse buffer under)

def middleTicks (nt n : Nat) := n + 2 + 1 + ULogTernaryBlankBlockAppend.deadline nt
def deadline (nt n : Nat) := middleTicks nt n + 1 + (n + nt + 1 + 2)

theorem append_start (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    secondStart (ULogTernaryBalancedBlankPair.append_child_ge nt) (2 : Fin 3) .stay
      (ULogTernaryDelimitedBinarySweep.final source under (List.replicate (nt + 1) 0 ++ buffer)) =
        ULogTernaryBlankBlockAppend.initial nt ((cells source).reverse ++ 2 :: under) buffer := by
  simp [secondStart, applyBounded, ULogTernaryDelimitedBinarySweep.final,
    ULogTernaryBlankBlockAppend.initial, leftConfig, leftState,
    ULogTernaryEmptyHeadPreparation.initial, ULogTernaryCountedSourceDelimiter.fromCells,
    cells, List.replicate_succ]

theorem middle_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (middleProgram hnt blank) 2 (List.replicate (middleTicks nt source.length) false)
      H (middleInitial nt source under buffer) =
        some (H + ((source.length + nt + 2 : Nat) : Int), middleFinal blank source under buffer) := by
  have h := sequential_run ULogTernaryDelimitedBinarySweep.program
    (ULogTernaryBlankBlockAppend.program hnt blank) (by decide)
    (ULogTernaryBalancedBlankPair.append_child_ge nt) .stay (2 : Fin 3)
    (List.replicate (source.length + 2) false)
    (List.replicate (ULogTernaryBlankBlockAppend.deadline nt) false)
    H (H + ((source.length + 1 : Nat) : Int)) (H + ((source.length + nt + 2 : Nat) : Int))
    (ULogTernaryDelimitedBinarySweep.initial source under (List.replicate (nt + 1) 0 ++ buffer))
    (ULogTernaryDelimitedBinarySweep.final source under (List.replicate (nt + 1) 0 ++ buffer))
    (ULogTernaryBlankBlockAppend.final blank ((cells source).reverse ++ 2 :: under) buffer)
    (ULogTernaryDelimitedBinarySweep.actual_run source under _ H) rfl (by
      rw [append_start, FiniteOneTapeSemantics.moveHead]
      convert ULogTernaryBlankBlockAppend.actual_run hnt blank
        ((cells source).reverse ++ 2 :: under) buffer (H + ((source.length + 1 : Nat) : Int)) using 1
      push_cast; ring)
  unfold middleProgram middleInitial middleFinal middleTicks
  rw [replicate_comp]
  exact h

theorem middle_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (middleFinal blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryBlankBlockAppend.final_accepts blank _ _)

theorem left_start {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    secondStart (by decide : 3 ≤ 4) (2 : Fin 3) .stay (middleFinal blank source under buffer) =
      ULogTernaryDelimitedBinarySweep.leftInitial (source ++ block blank).reverse buffer under := by
  have ht := ULogTernaryBlankBlockAppend.final_tape blank ((cells source).reverse ++ 2 :: under) buffer
  simp only [secondStart, applyBounded, middleFinal, rightConfig]
  rw [ht.1, ht.2.1, ht.2.2]
  simp [ULogTernaryDelimitedBinarySweep.leftInitial, ULogFiniteTapeReflection.reflectConfig,
    ULogTernaryDelimitedBinarySweep.initial, cells, cell, block,
    ULogTernaryOneHotBlockWriter.bits, List.map_reverse, List.reverse_append, List.append_assoc]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (pairProgram hnt blank) 2 (List.replicate (deadline nt source.length) false)
      H (initial nt source under buffer) = some (H, final blank source under buffer) := by
  have h := sequential_run (middleProgram hnt blank) ULogTernaryDelimitedBinarySweep.leftProgram
    (middle_states_ge nt) (by decide) .stay (2 : Fin 3)
    (List.replicate (middleTicks nt source.length) false)
    (List.replicate (ULogTernaryDelimitedBinarySweep.deadline (source ++ block blank).reverse) false)
    H (H + ((source.length + nt + 2 : Nat) : Int)) H
    (middleInitial nt source under buffer) (middleFinal blank source under buffer)
    (ULogTernaryDelimitedBinarySweep.leftFinal (source ++ block blank).reverse buffer under)
    (middle_run hnt blank source under buffer H) (middle_accepts blank source under buffer) (by
      rw [left_start, FiniteOneTapeSemantics.moveHead]
      convert ULogTernaryDelimitedBinarySweep.left_run (source ++ block blank).reverse buffer under
        (H + ((source.length + nt + 2 : Nat) : Int)) using 1
      simp only [List.length_reverse, List.length_append, block_length]
      push_cast; ring)
  have ticks : deadline nt source.length = middleTicks nt source.length + 1 +
      ULogTernaryDelimitedBinarySweep.deadline (source ++ block blank).reverse := by
    simp [deadline, ULogTernaryDelimitedBinarySweep.deadline, block_length]; omega
  unfold pairProgram initial final
  rw [ticks, replicate_comp]
  exact h

theorem final_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (final blank source under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2 rfl

theorem final_tape {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    (final blank source under buffer).leftRev = under ∧ (final blank source under buffer).focus = 2 ∧
    (final blank source under buffer).right = cells (source ++ block blank) ++ 2 :: buffer := by
  simp [final, rightConfig, ULogTernaryDelimitedBinarySweep.leftFinal,
    ULogFiniteTapeReflection.reflectConfig, ULogTernaryDelimitedBinarySweep.final,
    cells, List.map_reverse]

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (pairProgram hnt blank) := by
  apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
  · apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
    · exact ULogTernaryDelimitedBinarySweep.program_falseOnly
    · exact ULogTernaryBlankBlockAppend.program_falseOnly hnt blank
  · exact ULogTernaryDelimitedBinarySweep.left_falseOnly

def occupied (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :=
  under.length + source.length + nt + 3 + buffer.length

theorem initial_cells (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial nt source under buffer) = occupied nt source under buffer := by
  simp [initial, middleInitial, leftConfig, ULogTernaryDelimitedBinarySweep.initial,
    cellCount, cells, occupied]; omega
theorem final_cells {nt : Nat} (blank : Fin nt) (source : List Bool) (under buffer : List (Fin 3)) :
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
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) hw
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
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
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
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (pairProgram hnt blank) (initial nt source under buffer)) =
        if deadline nt source.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) T

theorem deadline_eq (nt n : Nat) : deadline nt n = 2 * n + nt * nt + 9 * nt + 16 := by
  simp only [deadline, middleTicks, ULogTernaryBlankBlockAppend.deadline_eq]; ring

theorem right_blank_insertion_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (run (pairProgram hnt blank) 2 (List.replicate (deadline nt source.length) false)
      H (initial nt source under buffer) = some (H, final blank source under buffer)) ∧
    (final blank source under buffer).leftRev = under ∧ (final blank source under buffer).focus = 2 ∧
    (final blank source under buffer).right = cells (source ++ block blank) ++ 2 :: buffer ∧
    (∀ w hf out, run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt source.length ∧
        cellCount out = occupied nt source under buffer ∧
        GrowthRun (pairProgram hnt blank) 2 w H (initial nt source under buffer) hf out 0 0) ∧
    (∀ w hf out, run (pairProgram hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      out.state.val = 0 → w = List.replicate (deadline nt source.length) false ∧ hf = H ∧
        out = final blank source under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (pairProgram hnt blank) (initial nt source under buffer)) =
        if deadline nt source.length ≤ T then 1 else 0) ∧
    deadline nt source.length = 2 * source.length + nt * nt + 9 * nt + 16 :=
  ⟨actual_run hnt blank source under buffer H, (final_tape blank source under buffer).1,
    (final_tape blank source under buffer).2.1, (final_tape blank source under buffer).2.2,
    fun _ _ _ => every_raw hnt blank source under buffer H,
    fun _ _ _ => accepting_word hnt blank source under buffer H,
    cutoff_counts hnt blank source under buffer H, deadline_eq nt source.length⟩

end PakFixedPolyomino.ULogTernaryRightBlankInsertion
