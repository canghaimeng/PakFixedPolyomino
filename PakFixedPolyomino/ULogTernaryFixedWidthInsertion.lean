import PakFixedPolyomino.ULogTernaryInsertZeroBeforeSource
import PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns

/-! A fixed finite sequence of genuine insertion sweeps. `K` is a controller
constant, not a binary input or an exponentially expanded program supplied by
the metric map. All K buffer cells are already allocated. Each stage has a
real STAY handoff; the zero-stage entry is immediate acceptance. The local entry
state is explicit and is not asserted to be the global source entry state. -/

namespace PakFixedPolyomino.ULogTernaryFixedWidthInsertion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)

def stateCount : Nat → Nat
  | 0 => 3
  | K + 1 => ULogFiniteTapeStageComposition.stateCount (stateCount K) 8

theorem stateCount_ge (K : Nat) : 3 ≤ stateCount K := by
  induction K with
  | zero => decide
  | succ K ih => unfold stateCount ULogFiniteTapeStageComposition.stateCount; omega

theorem stateCount_eq (K : Nat) : stateCount K = 3 + 9 * K := by
  induction K with
  | zero => rfl
  | succ K ih => simp [stateCount, ULogFiniteTapeStageComposition.stateCount, ih]; omega

def program : (K : Nat) → BoundedProgram (stateCount K) 3
  | 0 => ⟨fun _ _ _ => none⟩
  | K + 1 => ULogFiniteTapeStageComposition.program (program K)
      ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide) .stay

def entry : (K : Nat) → Fin (stateCount K)
  | 0 => ⟨0, by decide⟩
  | K + 1 => ULogFiniteTapeStageComposition.leftState (entry K)

def initial (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount K) 3 :=
  ⟨entry K, under, 2, cells x ++ 2 :: List.replicate K 0 ++ buffer⟩

def final (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount K) 3 :=
  ⟨⟨0, by have := stateCount_ge K; omega⟩, under, 2,
    List.replicate K 0 ++ cells x ++ 2 :: buffer⟩

def ticks : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, n => ticks K n + 1 + ULogTernaryInsertZeroBeforeSource.deadline (n + K)

theorem ticks_eq (K n : Nat) : ticks K n = 2 * K * n + K * K + 5 * K := by
  induction K with
  | zero => simp [ticks]
  | succ K ih => simp [ticks, ih, ULogTernaryInsertZeroBeforeSource.deadline]; ring

theorem cells_zeros (K : Nat) : cells (List.replicate K false) = List.replicate K 0 := by
  simp [cells, cell]

theorem initial_succ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    initial (K + 1) x under buffer =
      ULogFiniteTapeStageComposition.leftConfig (ms := 8)
        (initial K x under (0 :: buffer)) := by
  have hr : List.replicate (K + 1) (0 : Fin 3) ++ buffer =
      List.replicate K 0 ++ 0 :: buffer := by
    rw [List.replicate_succ']; simp [List.append_assoc]
  apply ULogTernaryOneHotBlockWriter.config_ext
  · rfl
  · rfl
  · rfl
  · simpa only [initial, ULogFiniteTapeStageComposition.leftConfig,
      List.append_assoc, List.cons_append] using congrArg (fun xs => cells x ++ 2 :: xs) hr

theorem second_start (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (ms := 8) (by decide) (2 : Fin 3) .stay
      (final K x under (0 :: buffer)) =
      ULogTernaryInsertZeroBeforeSource.initial (List.replicate K false ++ x) under buffer := by
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded, final,
    ULogTernaryInsertZeroBeforeSource.initial, ULogTernaryInsertZeroBeforeSource.srcRight,
    fromCells, cells, cell, List.append_assoc]

theorem final_succ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.rightConfig (ns := stateCount K)
      (ULogTernaryInsertZeroBeforeSource.final (List.replicate K false ++ x) under buffer) =
      final (K + 1) x under buffer := by
  simp [ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
    ULogTernaryInsertZeroBeforeSource.final, ULogTernaryInsertZeroBeforeSource.payload,
    final, fromCells, cells, cell, List.replicate_succ, List.append_assoc]
  rfl

theorem final_state (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    (final K x under buffer).state.val = 0 := rfl

theorem program_falseOnly (K : Nat) : FalseOnly (program K) := by
  induction K with
  | zero => intro q r; rfl
  | succ K ih =>
      exact ULogFiniteTapeStageCompositionRuns.program_falseOnly
        (program K) ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide)
        .stay ih ULogTernaryInsertZeroBeforeSource.program_falseOnly

theorem insertion_run (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program K) 2 (List.replicate (ticks K x.length) false) H
      (initial K x under buffer) = some (H, final K x under buffer) := by
  induction K generalizing buffer with
  | zero => simp [ticks, run, initial, final, entry]
  | succ K ih =>
      have hi := ih (0 :: buffer)
      have hq := ULogTernaryInsertZeroBeforeSource.insert_zero_run
        (List.replicate K false ++ x) under buffer H
      have hs := ULogFiniteTapeStageComposition.sequential_run (program K)
        ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide) .stay
        (2 : Fin 3) (List.replicate (ticks K x.length) false)
        (List.replicate (ULogTernaryInsertZeroBeforeSource.deadline (x.length + K)) false)
        H H H (initial K x under (0 :: buffer)) (final K x under (0 :: buffer))
        (ULogTernaryInsertZeroBeforeSource.final (List.replicate K false ++ x) under buffer)
        hi (final_state K x under (0 :: buffer)) (by
          simpa [second_start, FiniteOneTapeSemantics.moveHead, Nat.add_comm] using hq)
      rw [final_succ, ← initial_succ] at hs
      have hw : List.replicate (ticks (K + 1) x.length) false =
          List.replicate (ticks K x.length) false ++ false ::
            List.replicate (ULogTernaryInsertZeroBeforeSource.deadline (x.length + K)) false := by
        simp [ticks, List.replicate_add, List.append_assoc]
      change run (ULogFiniteTapeStageComposition.program (program K)
        ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide) .stay)
        2 (List.replicate (ticks (K + 1) x.length) false) H
        (initial (K + 1) x under buffer) = some (H, final (K + 1) x under buffer)
      rw [hw]
      exact hs

def occupied (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) : Nat :=
  under.length + x.length + K + 2 + buffer.length

theorem occupied_initial (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial K x under buffer) = occupied K x under buffer := by
  simp [cellCount, initial, occupied, cells]; omega

theorem occupied_final (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final K x under buffer) = occupied K x under buffer := by
  simp [cellCount, final, occupied, cells]; omega

theorem raw_geometry (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount K) 3}
    (hw : run (program K) 2 w H (initial K x under buffer) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + ((x.length + K + 1 : Nat) : Int) ∧
      cellCount zf = occupied K x under buffer := by
  induction K generalizing buffer w hf with
  | zero =>
      cases w with
      | nil =>
          have he : H = hf ∧ initial 0 x under buffer = zf := by simpa [run] using hw
          rcases he with ⟨rfl, rfl⟩
          exact ⟨le_refl _, by omega, occupied_initial 0 x under buffer⟩
      | cons b rest => simp [run, boundedHalted, initial, entry] at hw
  | succ K ih =>
      rw [initial_succ] at hw
      change run (ULogFiniteTapeStageComposition.program (program K)
        ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide) .stay)
        2 w H (ULogFiniteTapeStageComposition.leftConfig (initial K x under (0 :: buffer))) =
          some (hf, zf) at hw
      rcases ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split (program K)
        ULogTernaryInsertZeroBeforeSource.program (stateCount_ge K) (by decide) .stay
        (2 : Fin 3) (program_falseOnly K) (ticks K x.length) H H
        (initial K x under (0 :: buffer)) (final K x under (0 :: buffer))
        (insertion_run K x under (0 :: buffer) H) (final_state K x under (0 :: buffer))
        w hf zf hw with hfirst | hsecond
      · obtain ⟨_, zp, hp, rfl⟩ := hfirst
        have h := ih (0 :: buffer) hp
        change H ≤ hf ∧ hf ≤ H + ((x.length + (K + 1) + 1 : Nat) : Int) ∧
          cellCount zp = occupied (K + 1) x under buffer
        simp only [occupied, List.length_cons] at h ⊢
        exact ⟨h.1, by omega, by omega⟩
      · obtain ⟨v, zq, _, hq, rfl⟩ := hsecond
        rw [second_start] at hq
        simp only [FiniteOneTapeSemantics.moveHead] at hq
        have h := ULogTernaryInsertZeroBeforeSource.every_raw
          (List.replicate K false ++ x) under buffer H hq
        change H ≤ hf ∧ hf ≤ H + ((x.length + (K + 1) + 1 : Nat) : Int) ∧
          cellCount zq = occupied (K + 1) x under buffer
        simp only [ULogTernaryInsertZeroBeforeSource.occupied, occupied,
          List.length_append, List.length_replicate] at h ⊢
        exact ⟨h.2.2.1, by omega, by omega⟩

theorem every_raw (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount K) 3}
    (hw : run (program K) 2 w H (initial K x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ ticks K x.length ∧
      H ≤ hf ∧ hf ≤ H + ((x.length + K + 1 : Nat) : Int) ∧
      cellCount zf = occupied K x under buffer := by
  exact ⟨successful_zipper_is_false (2 : Fin 3) (program K) (program_falseOnly K) hw,
    successful_zipper_length_le (2 : Fin 3) (program K) (program_falseOnly K)
      (ticks K x.length) H (initial K x under buffer) (final K x under buffer) H
      (insertion_run K x under buffer H) (final_state K x under buffer) hw,
    raw_geometry K x under buffer H hw⟩

theorem every_raw_no_growth (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount K) 3}
    (hw : run (program K) 2 w H (initial K x under buffer) = some (hf, zf)) :
    GrowthRun (program K) 2 w H (initial K x under buffer) hf zf 0 0 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program K) 2 w H hf
    (initial K x under buffer) zf hw
  have h := (raw_geometry K x under buffer H hw).2.2
  have hi := occupied_initial K x under buffer
  have he := hg.exact_ledger
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg

theorem accepting_word (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount K) 3}
    (hw : run (program K) 2 w H (initial K x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (ticks K x.length) false ∧ hf = H ∧ zf = final K x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) (program K) (program_falseOnly K)
    (ticks K x.length) H (initial K x under buffer) (final K x under buffer) H
    (insertion_run K x under buffer H) (final_state K x under buffer) hw ha

theorem cutoff_counts (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program K) (initial K x under buffer)) =
      if ticks K x.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl (program K) (program_falseOnly K)
    (ticks K x.length) H (initial K x under buffer) (final K x under buffer) H
    (insertion_run K x under buffer H) (final_state K x under buffer) T

theorem compiled_symbols (K : Nat) :
    ∀ r ∈ compile (program K), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program K) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem fixed_width_insertion_spec :
    (∀ K, stateCount K = 3 + 9 * K) ∧
    (∀ K n, ticks K n = 2 * K * n + K * K + 5 * K) ∧
    (∀ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int),
      run (program K) 2 (List.replicate (ticks K x.length) false) H
        (initial K x under buffer) = some (H, final K x under buffer)) ∧
    (∀ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig (stateCount K) 3),
      run (program K) 2 w H (initial K x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ ticks K x.length ∧
        H ≤ hf ∧ hf ≤ H + ((x.length + K + 1 : Nat) : Int) ∧
        cellCount zf = occupied K x under buffer ∧
        GrowthRun (program K) 2 w H (initial K x under buffer) hf zf 0 0) ∧
    (∀ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig (stateCount K) 3),
      run (program K) 2 w H (initial K x under buffer) = some (hf, zf) →
      zf.state.val = 0 →
      w = List.replicate (ticks K x.length) false ∧ hf = H ∧ zf = final K x under buffer) ∧
    (∀ K, ∀ r ∈ compile (program K), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ (K : Nat) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat),
      ULogSemantics.machine.acceptingPaths T (liftConfig (program K) (initial K x under buffer)) =
        if ticks K x.length ≤ T then 1 else 0) := by
  refine ⟨stateCount_eq, ticks_eq, insertion_run, ?_, ?_, compiled_symbols, cutoff_counts⟩
  · intro K x under buffer H w hf zf hw
    have h := every_raw K x under buffer H hw
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      every_raw_no_growth K x under buffer H hw⟩
  · intro K x under buffer H w hf zf hw ha
    exact accepting_word K x under buffer H hw ha

end PakFixedPolyomino.ULogTernaryFixedWidthInsertion
