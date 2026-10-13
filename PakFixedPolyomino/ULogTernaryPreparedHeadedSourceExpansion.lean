import PakFixedPolyomino.ULogTernaryEmptyHeadPreparation
import PakFixedPolyomino.ULogTernaryHeadedSourceExpansion
import PakFixedPolyomino.ULogSourceObliviousWindow

/-! A real prepared source expansion for all binary inputs, including empty.
The original input has one delimiter. Empty preparation allocates its blank
head from one zero; exactly one true flag is then written by the headed stage.
The controller is fixed independently of source length and reserve. -/

namespace PakFixedPolyomino.ULogTernaryPreparedHeadedSourceExpansion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)


def first : List Bool → Fin 3
  | [] => 2
  | b :: _ => cell b

def tail : List Bool → List Bool
  | [] => []
  | _ :: xs => xs

def allocated (nt : Nat) (x : List Bool) (buffer : List (Fin 3)) :=
  List.replicate (nt * ((tail x).length + 1)) 0 ++ buffer

def remaining : List Bool → List (Fin 3) → List (Fin 3)
  | [], buffer => buffer
  | _ :: _, buffer => 0 :: buffer

def stateCount (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  ULogTernaryEmptyHeadPreparation.stateCount (ULogTernaryHeadedSourceExpansion.stateCount nt)

theorem prep_states_ge : 3 ≤ ULogTernaryEmptyHeadPreparation.stateCount := by decide

theorem headed_states_ge (nt : Nat) : 3 ≤ ULogTernaryHeadedSourceExpansion.stateCount nt := by
  have h := ULogTernaryHeadedSourceExpansion.cell_states_ge nt
  unfold ULogTernaryHeadedSourceExpansion.stateCount ULogFiniteTapeStageComposition.stateCount
  omega

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) :
    BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.program ULogTernaryEmptyHeadPreparation.program (ULogTernaryHeadedSourceExpansion.program hnt codes)
    prep_states_ge (headed_states_ge nt) .stay

def initial (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.leftConfig (ULogTernaryEmptyHeadPreparation.initial x under (allocated nt x buffer))

def final {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig (ns := ULogTernaryEmptyHeadPreparation.stateCount)
    (ULogTernaryHeadedSourceExpansion.final codes (first x) (tail x) under (remaining x buffer))

def deadline (nt : Nat) (x : List Bool) :=
  ULogTernaryEmptyHeadPreparation.deadline x + 1 + ULogTernaryHeadedSourceExpansion.deadline nt (tail x).length

def finalHead (nt : Nat) (x : List Bool) (H : Int) :=
  H + (((nt + 1) * ((tail x).length + 1) : Nat) : Int)

theorem second_start (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (headed_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryEmptyHeadPreparation.final x under (allocated nt x buffer)) =
      ULogTernaryHeadedSourceExpansion.initial nt (first x) (tail x) under (remaining x buffer) := by
  have comm (n : Nat) : (0 : Fin 3) :: (List.replicate n 0 ++ buffer) =
      List.replicate n 0 ++ 0 :: buffer := by
    have h : (0 : Fin 3) :: List.replicate n 0 = List.replicate n 0 ++ [0] := by
      calc
        (0 : Fin 3) :: List.replicate n 0 = List.replicate (n + 1) 0 :=
          by simp only [List.replicate_succ]
        _ = List.replicate n 0 ++ [0] := by
          rw [List.replicate_add]; rfl
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using congrArg (fun l => l ++ buffer) h
  cases x with
  | nil =>
      simp [ULogFiniteTapeStageComposition.secondStart, applyBounded, ULogTernaryEmptyHeadPreparation.final,
        ULogTernaryEmptyHeadPreparation.prepared, fromCells, allocated, tail, first, remaining, ULogTernaryHeadedSourceExpansion.initial,
        ULogTernaryHeadedSourceExpansion.reserve, ULogTernarySourceCellExpansion.initial,
        ULogFiniteTapeSymbolDispatch.initial, ULogFiniteTapeStageComposition.leftConfig,
        ULogFiniteTapeStageComposition.leftState, cells, List.append_assoc]
      rfl
  | cons b xs =>
      have hm : nt * (xs.length + 1) = nt + nt * xs.length := by ring
      change (⟨⟨2, _⟩, under, cell b,
        cells xs ++ 2 :: 0 :: (List.replicate (nt * (xs.length + 1)) 0 ++ buffer)⟩ :
        BoundedConfig (ULogTernaryHeadedSourceExpansion.stateCount nt) 3) =
        ⟨⟨2, _⟩, under, cell b,
          (cells xs ++ 2 :: List.replicate nt 0) ++
            (List.replicate (nt * xs.length) 0 ++ 0 :: buffer)⟩
      rw [comm, hm, List.replicate_add]
      simp only [List.append_assoc]
      rfl
theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt codes) 2 (List.replicate (deadline nt x) false) H
      (initial nt x under buffer) = some (finalHead nt x H, final codes x under buffer) := by
  have hs := ULogFiniteTapeStageComposition.sequential_run ULogTernaryEmptyHeadPreparation.program (ULogTernaryHeadedSourceExpansion.program hnt codes)
    prep_states_ge (headed_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryEmptyHeadPreparation.deadline x) false)
    (List.replicate (ULogTernaryHeadedSourceExpansion.deadline nt (tail x).length) false)
    H H (finalHead nt x H) (ULogTernaryEmptyHeadPreparation.initial x under (allocated nt x buffer))
    (ULogTernaryEmptyHeadPreparation.final x under (allocated nt x buffer))
    (ULogTernaryHeadedSourceExpansion.final codes (first x) (tail x) under (remaining x buffer))
    (ULogTernaryEmptyHeadPreparation.actual_run x under (allocated nt x buffer) H)
    (ULogTernaryEmptyHeadPreparation.final_state x under (allocated nt x buffer))
    (by
      rw [second_start]
      exact ULogTernaryHeadedSourceExpansion.actual_run hnt codes (first x) (tail x) under (remaining x buffer) H)
  have hw : List.replicate (deadline nt x) false =
      List.replicate (ULogTernaryEmptyHeadPreparation.deadline x) false ++ false ::
        List.replicate (ULogTernaryHeadedSourceExpansion.deadline nt (tail x).length) false := by
    simp [deadline, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rw [hw]
  exact hs


theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) :
    FalseOnly (program hnt codes) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    ULogTernaryEmptyHeadPreparation.program_falseOnly
    (ULogTernaryHeadedSourceExpansion.program_falseOnly hnt codes)

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool)
    (under buffer : List (Fin 3)) : (final codes x under buffer).state.val = 0 :=
  (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernaryHeadedSourceExpansion.final_state codes (first x) (tail x) under (remaining x buffer))

theorem final_tape {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool)
    (under buffer : List (Fin 3)) :
    (final codes x under buffer).leftRev =
      (ULogTernaryHeadedSourceExpansion.blocks codes (first x) (tail x)).reverse ++ under ∧
    (final codes x under buffer).focus = 2 ∧
    (final codes x under buffer).right = remaining x buffer :=
  ULogTernaryHeadedSourceExpansion.final_tape codes (first x) (tail x) under (remaining x buffer)

theorem occupied_unchanged {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (final codes x under buffer) = cellCount (initial nt x under buffer) := by
  have hf := ULogTernaryHeadedSourceExpansion.occupied_final codes (first x) (tail x)
    under (remaining x buffer)
  change cellCount (ULogTernaryHeadedSourceExpansion.final codes (first x) (tail x)
    under (remaining x buffer)) = _
  rw [hf]
  cases x with
  | nil =>
      simp [ULogTernaryHeadedSourceExpansion.occupied, initial,
        ULogFiniteTapeStageComposition.leftConfig, ULogTernaryEmptyHeadPreparation.initial,
        fromCells, cells, allocated, tail, remaining, cellCount]
      ring
  | cons b xs =>
      simp [ULogTernaryHeadedSourceExpansion.occupied, initial,
        ULogFiniteTapeStageComposition.leftConfig, ULogTernaryEmptyHeadPreparation.initial,
        fromCells, cells, allocated, tail, remaining, cellCount]
      ring

theorem every_raw {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes) 2 w H (initial nt x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt x ∧
      cellCount zf = cellCount (initial nt x under buffer) ∧
      GrowthRun (program hnt codes) 2 w H (initial nt x under buffer) hf zf 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes)
    (deadline nt x) H (initial nt x under buffer) (final codes x under buffer) (finalHead nt x H)
    (actual_run hnt codes x under buffer H) (final_state codes x under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes) 2 _ _ _ _ _
    (actual_run hnt codes x under buffer H)
  have hc := occupied_unchanged codes x under buffer
  have he := hg.exact_ledger
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt codes) 2 w H hf _ zf hw
  have hsplit : List.replicate (deadline nt x) false =
      w ++ List.replicate (deadline nt x - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [hsplit] at hg
  have hle := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes) 2 w H (initial nt x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt x) false ∧ hf = finalHead nt x H ∧
      zf = final codes x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt codes)
    (deadline nt x) H (initial nt x under buffer) (final codes x under buffer) (finalHead nt x H)
    (actual_run hnt codes x under buffer H) (final_state codes x under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program hnt codes) (initial nt x under buffer)) =
      if deadline nt x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes)
    (deadline nt x) H (initial nt x under buffer) (final codes x under buffer) (finalHead nt x H)
    (actual_run hnt codes x under buffer H) (final_state codes x under buffer) T

def markedSource {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool) :
    List (ULogSourceObliviousWindow.MarkedCell nt) :=
  ⟨codes (first x), true⟩ :: (tail x).map (fun b => ⟨codes (cell b), false⟩)

theorem markedSource_unique {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool) :
    (markedSource codes x).map ULogSourceObliviousWindow.MarkedCell.head = true :: List.replicate (tail x).length false := by
  simp [markedSource, List.map_map, Function.comp_def, List.map_const]

theorem cell_tapeOfBit : cell = ULogSourceOneHotReader.tapeOfBit := by
  funext b; cases b <;> rfl

theorem markedSource_encoding {nt : Nat} (codes : Fin 3 → Fin nt) (x : List Bool) :
    ULogSourceObliviousWindow.encodeWindow (markedSource codes x) =
      ULogTernaryHeadedSourceExpansion.blocks codes (first x) (tail x) := by
  simp [markedSource, ULogSourceObliviousWindow.encodeWindow,
    ULogSourceObliviousWindow.encodeMarkedCell,
    ULogTernaryHeadedSourceExpansion.blocks, ULogTernarySourceLoopExecution.blocks,
    ULogTernaryOneHotBlockWriter.bits, cells, cell_tapeOfBit, List.flatMap_map]

theorem prepared_headed_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt codes) 2 (List.replicate (deadline nt x) false) H (initial nt x under buffer) =
      some (finalHead nt x H, final codes x under buffer) ∧
    (final codes x under buffer).leftRev =
      (ULogTernaryHeadedSourceExpansion.blocks codes (first x) (tail x)).reverse ++ under ∧
    (final codes x under buffer).focus = 2 ∧ (final codes x under buffer).right = remaining x buffer ∧
    ULogSourceObliviousWindow.encodeWindow (markedSource codes x) =
      ULogTernaryHeadedSourceExpansion.blocks codes (first x) (tail x) ∧
    (first ([] : List Bool) = (2 : Fin 3)) ∧
    (∀ b xs, first (b :: xs) = cell b ∧ tail (b :: xs) = xs) ∧
    (markedSource codes x).map ULogSourceObliviousWindow.MarkedCell.head = true :: List.replicate (tail x).length false ∧
    (∀ w hf zf, run (program hnt codes) 2 w H (initial nt x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt x ∧
        cellCount zf = cellCount (initial nt x under buffer) ∧
        GrowthRun (program hnt codes) 2 w H (initial nt x under buffer) hf zf 0 0) ∧
    (∀ w hf zf, run (program hnt codes) 2 w H (initial nt x under buffer) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline nt x) false ∧
        hf = finalHead nt x H ∧ zf = final codes x under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig (program hnt codes) (initial nt x under buffer)) =
      if deadline nt x ≤ T then 1 else 0) :=
  ⟨actual_run hnt codes x under buffer H, (final_tape codes x under buffer).1,
    (final_tape codes x under buffer).2.1, (final_tape codes x under buffer).2.2,
    markedSource_encoding codes x, rfl, (fun _ _ => ⟨rfl, rfl⟩), markedSource_unique codes x,
    (fun _ _ _ h => every_raw hnt codes x under buffer H h),
    (fun _ _ _ h ha => accepting_word hnt codes x under buffer H h ha),
    cutoff_counts hnt codes x under buffer H⟩

end PakFixedPolyomino.ULogTernaryPreparedHeadedSourceExpansion
