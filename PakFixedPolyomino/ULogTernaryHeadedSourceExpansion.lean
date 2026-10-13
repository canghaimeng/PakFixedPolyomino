import PakFixedPolyomino.ULogTernarySourceLoopExecution

/-! A genuine headed first-cell expansion followed by the fixed source loop
with false flags. All work cells are actually allocated. The supplied first
symbol can be a binary input cell or the logical blank code; generation of
blank margins and the compact empty-input layout remains a separate stage. -/

namespace PakFixedPolyomino.ULogTernaryHeadedSourceExpansion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)

def stateCount (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  (ULogTernarySourceCellExpansion.stateCount nt) (ULogTernarySourceLoopExecution.stateCount nt)

theorem cell_states_ge (nt : Nat) : 3 ≤ ULogTernarySourceCellExpansion.stateCount nt := by
  unfold ULogTernarySourceCellExpansion.stateCount ULogFiniteTapeSymbolDispatch.stateCount
    ULogFiniteTapeStageComposition.stateCount
  omega

theorem loop_states_ge (nt : Nat) : 3 ≤ ULogTernarySourceLoopExecution.stateCount nt := by
  unfold ULogTernarySourceLoopExecution.stateCount ULogTernarySourceLoop.stateCount
  omega

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) :
    BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernarySourceCellExpansion.program hnt codes true)
    (ULogTernarySourceLoopExecution.program hnt codes false)
    (cell_states_ge nt) (loop_states_ge nt) .stay

def reserve (nt : Nat) (x : List Bool) (buffer : List (Fin 3)) :=
  List.replicate (nt * x.length) 0 ++ buffer

def initial (nt : Nat) (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.leftConfig
    (ULogTernarySourceCellExpansion.initial nt symbol x under (reserve nt x buffer))

def nextLeft {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3) (under : List (Fin 3)) :=
  (ULogTernaryOneHotBlockWriter.bits (codes symbol)).reverse ++ cell true :: under

def blocks {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3) (x : List Bool) :=
  cell true :: ULogTernaryOneHotBlockWriter.bits (codes symbol) ++
    ULogTernarySourceLoopExecution.blocks codes false x

def final {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig (ns := ULogTernarySourceCellExpansion.stateCount nt)
    (ULogTernarySourceLoopExecution.final codes false x (nextLeft codes symbol under) buffer)

def deadline (nt n : Nat) := ULogTernarySourceLoopExecution.deadline nt (n + 1)

theorem deadline_stages (nt n : Nat) : deadline nt n =
    ULogTernarySourceCellExpansion.deadline nt n + 1 +
      ULogTernarySourceLoopExecution.deadline nt n := by
  simp only [deadline, ULogTernarySourceLoopExecution.deadline,
    ULogTernarySourceCellExpansion.deadline]

theorem deadline_eq (nt n : Nat) : deadline nt n =
    nt * (n + 1) * (n + 1) + (nt * nt + 7 * nt + 5) * (n + 1) + 1 :=
  ULogTernarySourceLoopExecution.deadline_eq nt (n + 1)

theorem initial_tape (nt : Nat) (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    (initial nt symbol x under buffer).leftRev = under ∧
    (initial nt symbol x under buffer).focus = symbol ∧
    (initial nt symbol x under buffer).right =
      cells x ++ 2 :: List.replicate (nt * (x.length + 1)) 0 ++ buffer := by
  have hm : nt * (x.length + 1) = nt + nt * x.length := by ring
  simp [initial, ULogFiniteTapeStageComposition.leftConfig,
    ULogTernarySourceCellExpansion.initial, ULogFiniteTapeSymbolDispatch.initial,
    reserve, hm, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

theorem second_start {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (loop_states_ge nt) (2 : Fin 3) .stay
      (ULogTernarySourceCellExpansion.final codes true symbol x under (reserve nt x buffer)) =
      ULogTernarySourceLoopExecution.initial nt x (nextLeft codes symbol under) buffer := by
  have hn : cells x ++ 2 :: reserve nt x buffer ≠ [] := by simp
  cases hc : cells x ++ 2 :: reserve nt x buffer with
  | nil => exact (hn hc).elim
  | cons a rest =>
      change cells x ++ 2 :: (List.replicate (nt * x.length) 0 ++ buffer) = a :: rest at hc
      simp [ULogFiniteTapeStageComposition.secondStart, applyBounded,
        ULogTernarySourceCellExpansion.final, ULogFiniteTapeStageComposition.rightConfig,
        ULogFiniteTapeSymbolBranch.branchConfig, ULogTernarySourceCellExpansion.parentFinal,
        ULogTernaryOneHotWriteAdvance.final, fromCells,
        ULogTernarySourceLoopExecution.initial, nextLeft, reserve, hc,
        List.append_assoc, List.cons_append]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt codes) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt symbol x under buffer) =
      some (H + (((nt + 1) * (x.length + 1) : Nat) : Int), final codes symbol x under buffer) := by
  have hs := ULogFiniteTapeStageComposition.sequential_run
    (ULogTernarySourceCellExpansion.program hnt codes true)
    (ULogTernarySourceLoopExecution.program hnt codes false)
    (cell_states_ge nt) (loop_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernarySourceCellExpansion.deadline nt x.length) false)
    (List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false)
    H (H + ((nt + 1 : Nat) : Int)) (H + (((nt + 1) * (x.length + 1) : Nat) : Int))
    (ULogTernarySourceCellExpansion.initial nt symbol x under (reserve nt x buffer))
    (ULogTernarySourceCellExpansion.final codes true symbol x under (reserve nt x buffer))
    (ULogTernarySourceLoopExecution.final codes false x (nextLeft codes symbol under) buffer)
    (ULogTernarySourceCellExpansion.actual_run hnt codes true symbol x under (reserve nt x buffer) H)
    (ULogTernarySourceCellExpansion.final_state codes true symbol x under (reserve nt x buffer))
    (by
      rw [second_start]
      have hh : (H + ((nt + 1 : Nat) : Int)) + (((nt + 1) * x.length : Nat) : Int) =
          H + (((nt + 1) * (x.length + 1) : Nat) : Int) := by
        simp only [Nat.mul_add, Nat.mul_one, Int.natCast_add]; ring
      simpa only [FiniteOneTapeSemantics.moveHead, hh] using
        ULogTernarySourceLoopExecution.actual_run hnt codes false x (nextLeft codes symbol under)
          buffer (H + ((nt + 1 : Nat) : Int)))
  have hw : List.replicate (deadline nt x.length) false =
      List.replicate (ULogTernarySourceCellExpansion.deadline nt x.length) false ++ false ::
        List.replicate (ULogTernarySourceLoopExecution.deadline nt x.length) false := by
    rw [deadline_stages]
    simp [List.replicate_add, List.append_assoc]
  rw [hw]
  exact hs

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes symbol x under buffer).state.val = 0 :=
  (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
    (ULogTernarySourceLoopExecution.final_state codes false x (nextLeft codes symbol under) buffer)

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) :
    FalseOnly (program hnt codes) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernarySourceCellExpansion.program_falseOnly hnt codes true)
    (ULogTernarySourceLoopExecution.program_falseOnly hnt codes false)

theorem raw_head {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes) 2 w H (initial nt symbol x under buffer) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + (((nt + 1) * (x.length + 1) : Nat) : Int) := by
  rcases ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernarySourceCellExpansion.program hnt codes true)
    (ULogTernarySourceLoopExecution.program hnt codes false)
    (cell_states_ge nt) (loop_states_ge nt) .stay (2 : Fin 3)
    (ULogTernarySourceCellExpansion.program_falseOnly hnt codes true)
    (ULogTernarySourceCellExpansion.deadline nt x.length) H (H + ((nt + 1 : Nat) : Int))
    (ULogTernarySourceCellExpansion.initial nt symbol x under (reserve nt x buffer))
    (ULogTernarySourceCellExpansion.final codes true symbol x under (reserve nt x buffer))
    (ULogTernarySourceCellExpansion.actual_run hnt codes true symbol x under (reserve nt x buffer) H)
    (ULogTernarySourceCellExpansion.final_state codes true symbol x under (reserve nt x buffer))
    w hf zf hw with hfirst | hsecond
  · obtain ⟨_, zp, hp, _⟩ := hfirst
    have hh := ULogTernarySourceCellExpansion.raw_head hnt codes true symbol x under
      (reserve nt x buffer) H hp
    have hb : x.length + nt + 1 ≤ (nt + 1) * (x.length + 1) := by nlinarith
    exact ⟨hh.1, by have := Int.ofNat_le.mpr hb; omega⟩
  · obtain ⟨_, zq, _, hq, _⟩ := hsecond
    rw [second_start] at hq
    simp only [FiniteOneTapeSemantics.moveHead] at hq
    have hh := ULogTernarySourceLoopExecution.raw_head hnt codes false x
      (nextLeft codes symbol under) buffer (H + ((nt + 1 : Nat) : Int)) hq
    have hsum : ((nt + 1 : Nat) : Int) + (((nt + 1) * x.length : Nat) : Int) =
        (((nt + 1) * (x.length + 1) : Nat) : Int) := by
      simp only [Nat.mul_add, Nat.mul_one, Int.natCast_add]; ring
    exact ⟨by omega, by omega⟩

theorem blocks_length {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3) (x : List Bool) :
    (blocks codes symbol x).length = (nt + 1) * (x.length + 1) := by
  simp [blocks, ULogTernaryOneHotBlockWriter.bits_length,
    ULogTernarySourceLoopExecution.blocks_length]; ring

def occupied (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :=
  under.length + (nt + 1) * (x.length + 1) + 1 + buffer.length

theorem occupied_initial (nt : Nat) (symbol : Fin 3) (x : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (initial nt symbol x under buffer) = occupied nt x under buffer := by
  have h := initial_tape nt symbol x under buffer
  simp [cellCount, h.1, h.2.2, cells, occupied]; ring

theorem final_tape {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes symbol x under buffer).leftRev = (blocks codes symbol x).reverse ++ under ∧
    (final codes symbol x under buffer).focus = 2 ∧
    (final codes symbol x under buffer).right = buffer := by
  simp [final, ULogFiniteTapeStageComposition.rightConfig,
    ULogTernarySourceLoopExecution.final, blocks, nextLeft,
    List.reverse_append, List.append_assoc]

theorem occupied_final {nt : Nat} (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final codes symbol x under buffer) = occupied nt x under buffer := by
  have h := final_tape codes symbol x under buffer
  simp [cellCount, h.1, h.2.2, occupied, blocks_length]; omega

theorem every_raw {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes) 2 w H (initial nt symbol x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
      H ≤ hf ∧ hf ≤ H + (((nt + 1) * (x.length + 1) : Nat) : Int) ∧
      cellCount zf = occupied nt x under buffer ∧
      GrowthRun (program hnt codes) 2 w H (initial nt symbol x under buffer) hf zf 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes symbol x under buffer)
    (H + (((nt + 1) * (x.length + 1) : Nat) : Int))
    (actual_run hnt codes symbol x under buffer H) (final_state codes symbol x under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes) 2 _ _ _ _ _
    (actual_run hnt codes symbol x under buffer H)
  have hfinal := occupied_final codes symbol x under buffer
  have hi := occupied_initial nt symbol x under buffer
  have he := hg.exact_ledger
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt codes) 2 w H hf _ zf hw
  have hsplit : List.replicate (deadline nt x.length) false =
      w ++ List.replicate (deadline nt x.length - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [hsplit] at hg
  have hle := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have hledger := hg1.exact_ledger
  have hc : cellCount zf = occupied nt x under buffer := by omega
  have hh := raw_head hnt codes symbol x under buffer H hw
  exact ⟨hfalse, hlen, hh.1, hh.2, hc, by simpa [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes) 2 w H (initial nt symbol x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt x.length) false ∧
      hf = H + (((nt + 1) * (x.length + 1) : Nat) : Int) ∧ zf = final codes symbol x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt codes)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes symbol x under buffer)
    (H + (((nt + 1) * (x.length + 1) : Nat) : Int))
    (actual_run hnt codes symbol x under buffer H) (final_state codes symbol x under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes) (initial nt symbol x under buffer)) =
      if deadline nt x.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes symbol x under buffer)
    (H + (((nt + 1) * (x.length + 1) : Nat) : Int))
    (actual_run hnt codes symbol x under buffer H) (final_state codes symbol x under buffer) T

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) :
    ∀ r ∈ compile (program hnt codes), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt codes) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem headed_source_expansion_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (deadline nt x.length = nt * (x.length + 1) * (x.length + 1) +
      (nt * nt + 7 * nt + 5) * (x.length + 1) + 1) ∧
    ((initial nt symbol x under buffer).leftRev = under ∧
      (initial nt symbol x under buffer).focus = symbol ∧
      (initial nt symbol x under buffer).right =
        cells x ++ 2 :: List.replicate (nt * (x.length + 1)) 0 ++ buffer) ∧
    (run (program hnt codes) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt symbol x under buffer) =
      some (H + (((nt + 1) * (x.length + 1) : Nat) : Int), final codes symbol x under buffer)) ∧
    ((final codes symbol x under buffer).leftRev = (blocks codes symbol x).reverse ++ under ∧
      (final codes symbol x under buffer).focus = 2 ∧
      (final codes symbol x under buffer).right = buffer) ∧
    (∀ w hf zf, run (program hnt codes) 2 w H (initial nt symbol x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
        H ≤ hf ∧ hf ≤ H + (((nt + 1) * (x.length + 1) : Nat) : Int) ∧
        cellCount zf = occupied nt x under buffer ∧
        GrowthRun (program hnt codes) 2 w H (initial nt symbol x under buffer) hf zf 0 0) ∧
    (∀ w hf zf, run (program hnt codes) 2 w H (initial nt symbol x under buffer) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline nt x.length) false ∧
        hf = H + (((nt + 1) * (x.length + 1) : Nat) : Int) ∧ zf = final codes symbol x under buffer) ∧
    (∀ r ∈ compile (program hnt codes), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes) (initial nt symbol x under buffer)) =
        if deadline nt x.length ≤ T then 1 else 0) :=
  ⟨deadline_eq nt x.length, initial_tape nt symbol x under buffer,
    actual_run hnt codes symbol x under buffer H, final_tape codes symbol x under buffer,
    fun _ _ _ => every_raw hnt codes symbol x under buffer H,
    fun _ _ _ => accepting_word hnt codes symbol x under buffer H,
    compiled_symbols hnt codes, cutoff_counts hnt codes symbol x under buffer H⟩

end PakFixedPolyomino.ULogTernaryHeadedSourceExpansion
