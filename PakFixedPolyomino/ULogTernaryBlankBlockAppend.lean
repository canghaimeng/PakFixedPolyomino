import PakFixedPolyomino.ULogTernaryEmptyHeadPreparation
import PakFixedPolyomino.ULogTernarySourceCellExpansion

/-! A fixed controller appends one unheaded blank block at the actual end2
of a binary encoded window. One reserve zero becomes the new end delimiter;
nt more allocated zeros supply the onehot block. Previous source bits and
head flags survive in the arbitrary left tape. No compact margin loop is
claimed here. -/
namespace PakFixedPolyomino.ULogTernaryBlankBlockAppend
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)

abbrev stateCount (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  ULogTernaryEmptyHeadPreparation.stateCount (ULogTernarySourceCellExpansion.stateCount nt)

theorem child_states_ge (nt : Nat) : 3 ≤ ULogTernarySourceCellExpansion.stateCount nt := by
  unfold ULogTernarySourceCellExpansion.stateCount ULogFiniteTapeSymbolDispatch.stateCount
    ULogFiniteTapeStageComposition.stateCount
  omega

def codes {nt : Nat} (blank : Fin nt) : Fin 3 → Fin nt := fun _ => blank

def program {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.program ULogTernaryEmptyHeadPreparation.program
    (ULogTernarySourceCellExpansion.program hnt (codes blank) false)
    (by decide) (child_states_ge nt) .stay

def initial (nt : Nat) (under buffer : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.leftConfig
    (ULogTernaryEmptyHeadPreparation.initial [] under (List.replicate nt 0 ++ buffer))

def final {nt : Nat} (blank : Fin nt) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig
    (ULogTernarySourceCellExpansion.final (codes blank) false 2 [] under buffer)

def deadline (nt : Nat) := 4 + 1 + ULogTernarySourceCellExpansion.deadline nt 0

theorem deadline_eq (nt : Nat) : deadline nt = nt * nt + 8 * nt + 9 := by
  simp [deadline, ULogTernarySourceCellExpansion.deadline_eq]; omega

theorem second_start (nt : Nat) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (child_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryEmptyHeadPreparation.final [] under (List.replicate nt 0 ++ buffer)) =
        ULogTernarySourceCellExpansion.initial nt 2 [] under buffer := by
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded,
    ULogTernaryEmptyHeadPreparation.final, ULogTernaryEmptyHeadPreparation.prepared,
    ULogTernarySourceCellExpansion.initial, ULogFiniteTapeSymbolDispatch.initial,
    ULogTernaryCountedSourceDelimiter.fromCells, cells]
  rfl

theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt blank) 2 (List.replicate (deadline nt) false) H (initial nt under buffer) =
      some (H + ((nt + 1 : Nat) : Int), final blank under buffer) := by
  have h := ULogFiniteTapeStageComposition.sequential_run
    ULogTernaryEmptyHeadPreparation.program
    (ULogTernarySourceCellExpansion.program hnt (codes blank) false)
    (by decide) (child_states_ge nt) .stay (2 : Fin 3)
    (List.replicate 4 false) (List.replicate (ULogTernarySourceCellExpansion.deadline nt 0) false)
    H H (H + ((nt + 1 : Nat) : Int))
    (ULogTernaryEmptyHeadPreparation.initial [] under (List.replicate nt 0 ++ buffer))
    (ULogTernaryEmptyHeadPreparation.final [] under (List.replicate nt 0 ++ buffer))
    (ULogTernarySourceCellExpansion.final (codes blank) false 2 [] under buffer)
    (ULogTernaryEmptyHeadPreparation.actual_run [] under (List.replicate nt 0 ++ buffer) H)
    (ULogTernaryEmptyHeadPreparation.final_state [] under (List.replicate nt 0 ++ buffer)) (by
      rw [second_start, FiniteOneTapeSemantics.moveHead]
      exact ULogTernarySourceCellExpansion.actual_run hnt (codes blank) false 2 [] under buffer H)
  have word : List.replicate (deadline nt) false =
      List.replicate 4 false ++ false ::
        List.replicate (ULogTernarySourceCellExpansion.deadline nt 0) false := by
    simp [deadline, List.replicate_add, List.append_assoc]
  unfold program initial final
  rw [word]
  exact h

theorem final_accepts {nt : Nat} (blank : Fin nt) (under buffer : List (Fin 3)) :
    (final blank under buffer).state.val = 0 := by
  exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernarySourceCellExpansion.final_state (codes blank) false 2 [] under buffer)

theorem final_tape {nt : Nat} (blank : Fin nt) (under buffer : List (Fin 3)) :
    (final blank under buffer).leftRev = (ULogTernaryOneHotBlockWriter.bits blank).reverse ++ 0 :: under ∧
    (final blank under buffer).focus = 2 ∧ (final blank under buffer).right = buffer := by
  simp [final, ULogTernarySourceCellExpansion.final, ULogTernarySourceCellExpansion.parentFinal,
    ULogTernaryOneHotWriteAdvance.final, ULogTernaryCountedSourceDelimiter.fromCells,
    ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeSymbolBranch.branchConfig,
    codes, cells, cell]

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (program hnt blank) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    ULogTernaryEmptyHeadPreparation.program_falseOnly
    (ULogTernarySourceCellExpansion.program_falseOnly hnt (codes blank) false)

def occupied (nt : Nat) (under buffer : List (Fin 3)) := under.length + nt + 2 + buffer.length

theorem initial_cells (nt : Nat) (under buffer : List (Fin 3)) :
    cellCount (initial nt under buffer) = occupied nt under buffer := by
  simp [initial, ULogFiniteTapeStageComposition.leftConfig,
    ULogTernaryEmptyHeadPreparation.initial, ULogTernaryCountedSourceDelimiter.fromCells,
    cells, cellCount, occupied]; omega

theorem final_cells {nt : Nat} (blank : Fin nt) (under buffer : List (Fin 3)) :
    cellCount (final blank under buffer) = occupied nt under buffer := by
  have h := final_tape blank under buffer
  simp only [cellCount, h.1, h.2.2, List.length_append, List.length_reverse,
    List.length_cons, ULogTernaryOneHotWriteAdvance.bits_length]
  unfold occupied; omega

theorem every_raw {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt ∧
      cellCount out = occupied nt under buffer ∧
      GrowthRun (program hnt blank) 2 w H (initial nt under buffer) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt blank) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt) H (initial nt under buffer) (final blank under buffer) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt blank under buffer H) (final_accepts blank under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt blank) 2 _ _ _ _ _
    (actual_run hnt blank under buffer H)
  have ledger := hg.exact_ledger
  have hi := initial_cells nt under buffer
  have ho := final_cells blank under buffer
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt blank) 2 w H hf _ out hw
  have word : List.replicate (deadline nt) false =
      w ++ List.replicate (deadline nt - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [word] at hg
  have le := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger1 := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt) false ∧ hf = H + ((nt + 1 : Nat) : Int) ∧
      out = final blank under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt) H (initial nt under buffer) (final blank under buffer) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt blank under buffer H) (final_accepts blank under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program hnt blank) (initial nt under buffer)) =
      if deadline nt ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt) H (initial nt under buffer) (final blank under buffer) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt blank under buffer H) (final_accepts blank under buffer) T

theorem blank_block_append_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under buffer : List (Fin 3)) (H : Int) :
    (run (program hnt blank) 2 (List.replicate (deadline nt) false) H (initial nt under buffer) =
      some (H + ((nt + 1 : Nat) : Int), final blank under buffer)) ∧
    (final blank under buffer).leftRev = (ULogTernaryOneHotBlockWriter.bits blank).reverse ++ 0 :: under ∧
    (final blank under buffer).focus = 2 ∧ (final blank under buffer).right = buffer ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt ∧
        cellCount out = occupied nt under buffer ∧
        GrowthRun (program hnt blank) 2 w H (initial nt under buffer) hf out 0 0) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt under buffer) = some (hf, out) →
      out.state.val = 0 → w = List.replicate (deadline nt) false ∧
        hf = H + ((nt + 1 : Nat) : Int) ∧ out = final blank under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig (program hnt blank) (initial nt under buffer)) =
      if deadline nt ≤ T then 1 else 0) ∧ deadline nt = nt * nt + 8 * nt + 9 :=
  ⟨actual_run hnt blank under buffer H, (final_tape blank under buffer).1,
    (final_tape blank under buffer).2.1, (final_tape blank under buffer).2.2,
    fun _ _ _ => every_raw hnt blank under buffer H,
    fun _ _ _ => accepting_word hnt blank under buffer H,
    cutoff_counts hnt blank under buffer H, deadline_eq nt⟩

end PakFixedPolyomino.ULogTernaryBlankBlockAppend
