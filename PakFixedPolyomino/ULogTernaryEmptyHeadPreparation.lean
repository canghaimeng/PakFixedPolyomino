import PakFixedPolyomino.ULogFiniteTapeSymbolBranch
import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter

/-! The actual empty binary source has only one delimiter. A real three-tick
child duplicates it into one allocated zero, providing a blank head symbol
and a following end delimiter. Nonempty original input is restored after
capturing its first symbol. No preexisting extra delimiter is assumed. -/

namespace PakFixedPolyomino.ULogTernaryEmptyHeadPreparation

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter (fromCells)
open ULogTernaryRetainedCounterPump (cell cells)

abbrev stateCount := ULogFiniteTapeSymbolDispatch.stateCount
  (ULogFiniteTapeSymbolBranch.stateCount 5)

def parents (a : Fin 3) : BoundedProgram 5 3 where
  rule q read slot :=
    if slot then none
    else if a = 2 then
      if q = 2 then
        if read = 2 then some ⟨2, 3, .right⟩ else none
      else if q = 3 then
        if read = 0 then some ⟨2, 4, .left⟩ else none
      else if q = 4 then
        if read = 2 then some ⟨2, 0, .stay⟩ else none
      else none
    else if q = 2 then some ⟨a, 0, .stay⟩ else none

def program : BoundedProgram stateCount 3 :=
  ULogFiniteTapeSymbolBranch.dispatch parents (fun _ => 2) 2

def initial (x : List Bool) (under buffer : List (Fin 3)) : BoundedConfig stateCount 3 :=
  fromCells (⟨2, by decide⟩ : Fin stateCount) under (cells x ++ 2 :: 0 :: buffer)

def prepared (x : List Bool) (buffer : List (Fin 3)) : List (Fin 3) :=
  match x with
  | [] => 2 :: 2 :: buffer
  | _ :: _ => cells x ++ 2 :: 0 :: buffer

def final (x : List Bool) (under buffer : List (Fin 3)) : BoundedConfig stateCount 3 :=
  fromCells (⟨0, by decide⟩ : Fin stateCount) under (prepared x buffer)

def deadline : List Bool → Nat
  | [] => 4
  | _ :: _ => 2

theorem parents_falseOnly (a : Fin 3) : FalseOnly (parents a) := by
  intro q read
  simp [parents]

theorem program_falseOnly : FalseOnly program :=
  ULogFiniteTapeSymbolBranch.dispatch_falseOnly parents (fun _ => 2) 2 parents_falseOnly

theorem run_captured (a : Fin 3) (under right : List (Fin 3)) (H : Int) (w : List Bool) :
    run program 2 (false :: w) H (ULogFiniteTapeSymbolDispatch.initial a under right) =
      (run (parents a) 2 w H (⟨2, under, 2, right⟩ : BoundedConfig 5 3)).map
        (fun hz => (hz.1, ULogFiniteTapeStageComposition.rightConfig (ns := 3)
          (ULogFiniteTapeSymbolBranch.branchConfig a hz.2))) := by
  unfold program ULogFiniteTapeSymbolBranch.dispatch
  rw [ULogFiniteTapeSymbolDispatch.run_dispatch_cons]
  change (run (ULogFiniteTapeSymbolBranch.program parents) 2 w H
    (ULogFiniteTapeSymbolBranch.branchConfig a (⟨2, under, 2, right⟩ : BoundedConfig 5 3))).map
      (fun hz => (hz.1, ULogFiniteTapeStageComposition.rightConfig (ns := 3) hz.2)) = _
  rw [ULogFiniteTapeSymbolBranch.run_branch_map]
  rw [Option.map_map]
  rfl

theorem actual_run (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (deadline x) false) H (initial x under buffer) =
      some (H, final x under buffer) := by
  cases x with
  | nil =>
      change run program 2 (false :: [false, false, false]) H
        (ULogFiniteTapeSymbolDispatch.initial 2 under (0 :: buffer)) = _
      rw [run_captured]
      simp [parents, run, boundedHalted, applyBounded, FiniteOneTapeSemantics.moveHead,
        ULogFiniteTapeSymbolBranch.branchConfig, ULogFiniteTapeSymbolBranch.branchState,
        ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
        final, prepared, fromCells, Option.map]
  | cons b x =>
      change run program 2 (false :: [false]) H
        (ULogFiniteTapeSymbolDispatch.initial (cell b) under (cells x ++ 2 :: 0 :: buffer)) = _
      rw [run_captured]
      cases b <;>
        simp [parents, cell, run, boundedHalted, applyBounded, FiniteOneTapeSemantics.moveHead,
          ULogFiniteTapeSymbolBranch.branchConfig, ULogFiniteTapeSymbolBranch.branchState,
          ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
          final, prepared, cells, fromCells, Option.map]

theorem final_state (x : List Bool) (under buffer : List (Fin 3)) :
    (final x under buffer).state.val = 0 := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

theorem occupied_unchanged (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final x under buffer) = cellCount (initial x under buffer) := by
  cases x with
  | nil => simp [initial, final, prepared, cells, fromCells, cellCount]
  | cons b x => cases b <;> rfl

theorem every_raw (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig stateCount 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline x :=
  ⟨successful_zipper_is_false (2 : Fin 3) program program_falseOnly hw,
    successful_zipper_length_le (2 : Fin 3) program program_falseOnly
      (deadline x) H (initial x under buffer) (final x under buffer) H
      (actual_run x under buffer H) (final_state x under buffer) hw⟩

theorem cutoff_counts (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig program (initial x under buffer)) =
      if deadline x ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl program program_falseOnly (deadline x) H
    (initial x under buffer) (final x under buffer) H (actual_run x under buffer H)
    (final_state x under buffer) T

theorem every_raw_resources (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig stateCount 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline x ∧
      cellCount zf = cellCount (initial x under buffer) ∧
      GrowthRun program 2 w H (initial x under buffer) hf zf 0 0 := by
  have raw := every_raw x under buffer H hw
  obtain ⟨lg, rg, growth⟩ := every_actual_run program 2 _ H H _ _ (actual_run x under buffer H)
  have count := occupied_unchanged x under buffer
  have ledger := growth.exact_ledger
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, prefixGrowth⟩ := every_actual_run program 2 w H hf _ zf hw
  have hsplit : List.replicate (deadline x) false =
      w ++ List.replicate (deadline x - w.length) false := by
    rw [raw.1]
    simpa only [List.length_replicate] using
      ULogTernaryOneHotBlockWriter.replicate_split (deadline x) w.length raw.2
  rw [hsplit] at growth
  have hle := ULogTernaryOneHotBlockWriter.growth_append_le growth prefixGrowth
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have hp := prefixGrowth.exact_ledger
  exact ⟨raw.1, raw.2, by omega, by simpa [hl1, hr1] using prefixGrowth⟩

theorem accepting_word (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig stateCount 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline x) false ∧ hf = H ∧ zf = final x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) program program_falseOnly (deadline x) H
    (initial x under buffer) (final x under buffer) H (actual_run x under buffer H)
    (final_state x under buffer) hw ha

theorem preparation_spec (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (deadline x) false) H (initial x under buffer) =
      some (H, final x under buffer) ∧
    cellCount (final x under buffer) = cellCount (initial x under buffer) ∧
    (final [] under buffer).leftRev = under ∧ (final [] under buffer).focus = 2 ∧
      (final [] under buffer).right = 2 :: buffer ∧
    (∀ b rest, (final (b :: rest) under buffer).leftRev = under ∧
      (final (b :: rest) under buffer).focus = cell b ∧
      (final (b :: rest) under buffer).right = cells rest ++ 2 :: 0 :: buffer) ∧
    (∀ w hf zf, run program 2 w H (initial x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline x ∧
        cellCount zf = cellCount (initial x under buffer) ∧
        GrowthRun program 2 w H (initial x under buffer) hf zf 0 0) ∧
    (∀ w hf zf, run program 2 w H (initial x under buffer) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline x) false ∧ hf = H ∧ zf = final x under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig program (initial x under buffer)) =
      if deadline x ≤ T then 1 else 0) := by
  refine ⟨actual_run x under buffer H, occupied_unchanged x under buffer,
    rfl, rfl, rfl, ?_, ?_, ?_, cutoff_counts x under buffer H⟩
  · intro b rest
    cases b <;> exact ⟨rfl, rfl, rfl⟩
  · intro w hf zf hw
    exact every_raw_resources x under buffer H hw
  · intro w hf zf hw ha
    exact accepting_word x under buffer H hw ha

end PakFixedPolyomino.ULogTernaryEmptyHeadPreparation
