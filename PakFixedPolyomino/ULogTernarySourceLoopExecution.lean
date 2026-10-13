import PakFixedPolyomino.ULogTernarySourceCellExpansion
import PakFixedPolyomino.ULogTernarySourceLoop

/-! A literal fixed source loop instantiated with the actual insertion/writer
body. Its program does not depend on the source length. The explicitly supplied
nt*n zeros are allocated cells, not a runtime oracle; in the final loader they
must come from the internal pump. Blank margins and scanner handoff are separate.
-/

namespace PakFixedPolyomino.ULogTernarySourceLoopExecution

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells)

def bodyStates (nt : Nat) :=
  ULogFiniteTapeSymbolBranch.stateCount (ULogTernarySourceCellExpansion.parentStates nt)

def bodyProgram {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    BoundedProgram (bodyStates nt) 3 :=
  ULogFiniteTapeSymbolBranch.program
    (fun s => ULogTernarySourceCellExpansion.parentProgram hnt (codes s) flag)

def bodyEntry (nt : Nat) (s : Fin 3) : Fin (bodyStates nt) :=
  ULogFiniteTapeSymbolBranch.branchState s (ULogTernarySourceCellExpansion.parentEntry nt)

def stateCount (nt : Nat) := ULogTernarySourceLoop.stateCount (bodyStates nt)

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    BoundedProgram (stateCount nt) 3 :=
  ULogTernarySourceLoop.program (bodyProgram hnt codes flag) (bodyEntry nt)

def blocks {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (x : List Bool) : List (Fin 3) :=
  x.flatMap (fun b => cell flag :: ULogTernaryOneHotBlockWriter.bits (codes (cell b)))

def initial (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  fromCells ⟨2, by unfold stateCount ULogTernarySourceLoop.stateCount; omega⟩ under
    (cells x ++ 2 :: List.replicate (nt * x.length) 0 ++ buffer)

def final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (x : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ⟨⟨0, by unfold stateCount ULogTernarySourceLoop.stateCount; omega⟩,
    (blocks codes flag x).reverse ++ under, 2, buffer⟩

def deadline (nt : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => ULogTernarySourceCellExpansion.parentTicks nt n + 2 + deadline nt n

theorem deadline_eq (nt n : Nat) :
    deadline nt n = nt * n * n + (nt * nt + 7 * nt + 5) * n + 1 := by
  induction n with
  | zero => simp [deadline]
  | succ n ih =>
      simp [deadline, ULogTernarySourceCellExpansion.parentTicks,
        ULogTernaryFixedWidthInsertion.ticks_eq, ULogTernaryOneHotWriteAdvance.deadline, ih]
      ring

theorem initial_cons (nt : Nat) (b : Bool) (x : List Bool) (under buffer : List (Fin 3)) :
    initial nt (b :: x) under buffer =
      ULogTernarySourceLoop.initial (cell b) under
        (cells x ++ 2 :: List.replicate nt 0 ++ (List.replicate (nt * x.length) 0 ++ buffer)) := by
  have hm : nt * (x.length + 1) = nt + nt * x.length := by ring
  simp [initial, cells, fromCells, ULogTernarySourceLoop.initial, hm,
    List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  rfl

theorem selected_eq (nt : Nat) (s : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogTernarySourceLoop.selected (bodyEntry nt) s under
      (cells x ++ 2 :: List.replicate nt 0 ++ buffer) =
      ULogFiniteTapeSymbolBranch.branchConfig s
        (ULogTernarySourceCellExpansion.parentInitial nt x under buffer) := rfl

theorem body_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (s : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (bodyProgram hnt codes flag) 2
      (List.replicate (ULogTernarySourceCellExpansion.parentTicks nt x.length) false) H
      (ULogTernarySourceLoop.selected (bodyEntry nt) s under
        (cells x ++ 2 :: List.replicate nt 0 ++ buffer)) =
      some (H + ((nt + 1 : Nat) : Int), ULogFiniteTapeSymbolBranch.branchConfig s
        (ULogTernarySourceCellExpansion.parentFinal (codes s) flag x under buffer)) := by
  rw [selected_eq]
  change run (ULogFiniteTapeSymbolBranch.program
    (fun s => ULogTernarySourceCellExpansion.parentProgram hnt (codes s) flag)) 2 _ H _ = _
  rw [ULogFiniteTapeSymbolBranch.run_branch_map,
    ULogTernarySourceCellExpansion.parent_run hnt (codes s) flag x under buffer H]
  rfl

theorem body_final_state {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (s : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    (ULogFiniteTapeSymbolBranch.branchConfig s
      (ULogTernarySourceCellExpansion.parentFinal (codes s) flag x under buffer)).state.val = 0 := by
  apply (ULogFiniteTapeSymbolBranch.branch_accepts _ _).2
  apply (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
  exact ULogTernaryOneHotWriteAdvance.final_state _ _ _ _

theorem loop_at_final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (s : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogTernarySourceLoop.loopAt (ULogFiniteTapeSymbolBranch.branchConfig s
      (ULogTernarySourceCellExpansion.parentFinal (codes s) flag x under
        (List.replicate (nt * x.length) 0 ++ buffer))) =
      initial nt x ((ULogTernaryOneHotBlockWriter.bits (codes s)).reverse ++ cell flag :: under) buffer := by
  have hn : cells x ++ 2 :: (List.replicate (nt * x.length) 0 ++ buffer) ≠ [] := by simp
  cases hc : cells x ++ 2 :: (List.replicate (nt * x.length) 0 ++ buffer) with
  | nil => exact (hn hc).elim
  | cons a rest =>
      simp [ULogTernarySourceLoop.loopAt, ULogTernarySourceLoop.initial,
        ULogFiniteTapeSymbolBranch.branchConfig, ULogTernarySourceCellExpansion.parentFinal,
        ULogFiniteTapeStageComposition.rightConfig, ULogTernaryOneHotWriteAdvance.final,
        fromCells, initial, List.append_assoc, List.cons_append, hc]
      rfl

theorem final_cons {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (b : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) :
    final codes flag x ((ULogTernaryOneHotBlockWriter.bits (codes (cell b))).reverse ++ cell flag :: under)
      buffer = final codes flag (b :: x) under buffer := by
  simp [final, blocks, List.reverse_append, List.append_assoc]

theorem cell_ne_sentinel (b : Bool) : (cell b).val ≠ 2 := by cases b <;> decide

theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt codes flag) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt x under buffer) =
      some (H + (((nt + 1) * x.length : Nat) : Int), final codes flag x under buffer) := by
  induction x generalizing under H with
  | nil =>
      change run (ULogTernarySourceLoop.program (bodyProgram hnt codes flag) (bodyEntry nt)) 2
        [false] H (ULogTernarySourceLoop.initial (2 : Fin 3) under buffer) = _
      rw [ULogTernarySourceLoop.run_entry_sentinel _ _ _ _ _ _ [] rfl]
      simp [final, blocks, ULogTernarySourceLoop.sentinelFinal]
      rfl
  | cons b x ih =>
      let nextLeft := (ULogTernaryOneHotBlockWriter.bits (codes (cell b))).reverse ++ cell flag :: under
      let reserve := List.replicate (nt * x.length) 0 ++ buffer
      let z := ULogTernarySourceLoop.selected (bodyEntry nt) (cell b) under
        (cells x ++ 2 :: List.replicate nt 0 ++ reserve)
      let zp := ULogFiniteTapeSymbolBranch.branchConfig (cell b)
        (ULogTernarySourceCellExpansion.parentFinal (codes (cell b)) flag x under reserve)
      have hnext := ih nextLeft (H + ((nt + 1 : Nat) : Int))
      have hloop : ULogTernarySourceLoop.loopAt (ms := bodyStates nt) zp =
          initial nt x nextLeft buffer := loop_at_final codes flag (cell b) x under buffer
      have hseq := ULogTernarySourceLoop.sequential_body (bodyProgram hnt codes flag) (bodyEntry nt)
        (List.replicate (ULogTernarySourceCellExpansion.parentTicks nt x.length) false)
        (List.replicate (deadline nt x.length) false) H (H + ((nt + 1 : Nat) : Int))
        ((H + ((nt + 1 : Nat) : Int)) + (((nt + 1) * x.length : Nat) : Int))
        z zp (final codes flag x nextLeft buffer) (body_run hnt codes flag (cell b) x under reserve H)
        (body_final_state codes flag (cell b) x under reserve) (by rw [hloop]; exact hnext)
      rw [final_cons codes flag b x under buffer] at hseq
      rw [initial_cons]
      change run (ULogTernarySourceLoop.program (bodyProgram hnt codes flag) (bodyEntry nt)) 2
        (List.replicate (deadline nt (b :: x).length) false) H _ = _
      have hw : List.replicate (deadline nt (b :: x).length) false =
          false :: (List.replicate (ULogTernarySourceCellExpansion.parentTicks nt x.length) false ++
            false :: List.replicate (deadline nt x.length) false) := by
        change List.replicate
          (ULogTernarySourceCellExpansion.parentTicks nt x.length + 2 + deadline nt x.length) false = _
        rw [show ULogTernarySourceCellExpansion.parentTicks nt x.length + 2 + deadline nt x.length =
          (ULogTernarySourceCellExpansion.parentTicks nt x.length + (deadline nt x.length + 1)) + 1 by omega,
          List.replicate_succ, List.replicate_add, List.replicate_succ]
      rw [hw, ULogTernarySourceLoop.run_entry_select _ _ _ _ _ _ _ (cell_ne_sentinel b)]
      have hh : H + ((nt + 1 : Nat) : Int) + (((nt + 1) * x.length : Nat) : Int) =
          H + (((nt + 1) * (b :: x).length : Nat) : Int) := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Int.natCast_add]; ring
      rw [← hh]
      exact hseq

theorem body_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    FalseOnly (bodyProgram hnt codes flag) :=
  ULogFiniteTapeSymbolBranch.program_falseOnly _
    (fun s => ULogTernarySourceCellExpansion.parent_falseOnly hnt (codes s) flag)

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    FalseOnly (program hnt codes flag) :=
  ULogTernarySourceLoop.program_falseOnly _ _ (body_falseOnly hnt codes flag)

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes flag x under buffer).state.val = 0 := rfl

theorem raw_head {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt x under buffer) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + (((nt + 1) * x.length : Nat) : Int) := by
  induction x generalizing under H w hf with
  | nil =>
      change run (ULogTernarySourceLoop.program (bodyProgram hnt codes flag) (bodyEntry nt)) 2 w H
        (ULogTernarySourceLoop.initial (ms := bodyStates nt) (2 : Fin 3) under buffer) = some (hf, zf) at hw
      have h := (ULogTernarySourceLoop.every_raw_entry_splits (bodyProgram hnt codes flag) (bodyEntry nt)
        (2 : Fin 3) under buffer w H hf zf).1 hw
      rcases h with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨bad, _⟩
      · simp
      · simp
      · exact (bad rfl).elim
  | cons b x ih =>
      let reserve := List.replicate (nt * x.length) 0 ++ buffer
      rw [initial_cons] at hw
      change run (ULogTernarySourceLoop.program (bodyProgram hnt codes flag) (bodyEntry nt)) 2 w H
        (ULogTernarySourceLoop.initial (ms := bodyStates nt) (cell b) under
          (cells x ++ 2 :: List.replicate nt 0 ++ reserve)) = some (hf, zf) at hw
      have h := (ULogTernarySourceLoop.every_raw_entry_splits (bodyProgram hnt codes flag) (bodyEntry nt)
        (cell b) under (cells x ++ 2 :: List.replicate nt 0 ++ reserve) w H hf zf).1 hw
      rcases h with ⟨_, rfl, _⟩ | ⟨bad, _⟩ | ⟨_, hprefix | hreturn⟩
      · exact ⟨le_refl _, by omega⟩
      · exact (cell_ne_sentinel b bad).elim
      · obtain ⟨v, zp, _, hp, _⟩ := hprefix
        rw [selected_eq] at hp
        change run (ULogFiniteTapeSymbolBranch.program
          (fun s => ULogTernarySourceCellExpansion.parentProgram hnt (codes s) flag)) 2 v H
          (ULogFiniteTapeSymbolBranch.branchConfig (cell b)
            (ULogTernarySourceCellExpansion.parentInitial nt x under reserve)) = some (hf, zp) at hp
        rw [ULogFiniteTapeSymbolBranch.run_branch_map] at hp
        obtain ⟨⟨h, pz⟩, hp', he⟩ := Option.map_eq_some_iff.mp hp
        rcases Prod.mk.inj he with ⟨rfl, _⟩
        have hh := ULogTernarySourceCellExpansion.parent_raw_head hnt (codes (cell b)) flag x under reserve H hp'
        have hb : x.length + nt + 1 ≤ (nt + 1) * (x.length + 1) := by nlinarith
        exact ⟨hh.1, by have hc := Int.ofNat_le.mpr hb; simp only [List.length_cons]; omega⟩
      · obtain ⟨u, v, mid, zp, _, hp, ha, hloop⟩ := hreturn
        have he := accepting_zipper_word_eq (2 : Fin 3) (bodyProgram hnt codes flag)
          (body_falseOnly hnt codes flag) (ULogTernarySourceCellExpansion.parentTicks nt x.length) H
          (ULogTernarySourceLoop.selected (bodyEntry nt) (cell b) under
            (cells x ++ 2 :: List.replicate nt 0 ++ reserve))
          (ULogFiniteTapeSymbolBranch.branchConfig (cell b)
            (ULogTernarySourceCellExpansion.parentFinal (codes (cell b)) flag x under reserve))
          (H + ((nt + 1 : Nat) : Int)) (body_run hnt codes flag (cell b) x under reserve H)
          (body_final_state codes flag (cell b) x under reserve) hp ha
        rcases he with ⟨_, rfl, rfl⟩
        have hl : ULogTernarySourceLoop.loopAt (ms := bodyStates nt)
            (ULogFiniteTapeSymbolBranch.branchConfig (cell b)
              (ULogTernarySourceCellExpansion.parentFinal (codes (cell b)) flag x under reserve)) =
            initial nt x ((ULogTernaryOneHotBlockWriter.bits (codes (cell b))).reverse ++ cell flag :: under)
              buffer := loop_at_final codes flag (cell b) x under buffer
        rw [hl] at hloop
        have hh := ih _ _ hloop
        have hsum : ((nt + 1 : Nat) : Int) + (((nt + 1) * x.length : Nat) : Int) =
            (((nt + 1) * (b :: x).length : Nat) : Int) := by
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Int.natCast_add]; ring
        exact ⟨by omega, by omega⟩

theorem blocks_length {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (x : List Bool) :
    (blocks codes flag x).length = (nt + 1) * x.length := by
  induction x with
  | nil => simp [blocks]
  | cons b x ih =>
      simpa [blocks, ULogTernaryOneHotBlockWriter.bits_length, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg (fun n => nt + 1 + n) ih

def occupied (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :=
  under.length + (nt + 1) * x.length + 1 + buffer.length

theorem occupied_initial (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial nt x under buffer) = occupied nt x under buffer := by
  have hn : cells x ++ 2 :: List.replicate (nt * x.length) 0 ++ buffer ≠ [] := by simp
  rw [initial, ULogTernaryOneHotBlockWriter.cellCount_of_cells _ _ _ hn]
  simp [occupied, cells]; ring

theorem occupied_final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final codes flag x under buffer) = occupied nt x under buffer := by
  simp [final, cellCount, occupied, blocks_length]; omega

theorem final_tape {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes flag x under buffer).leftRev = (blocks codes flag x).reverse ++ under ∧
    (final codes flag x under buffer).focus = 2 ∧
    (final codes flag x under buffer).right = buffer := ⟨rfl, rfl, rfl⟩

theorem every_raw {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
      H ≤ hf ∧ hf ≤ H + (((nt + 1) * x.length : Nat) : Int) ∧
      cellCount zf = occupied nt x under buffer ∧
      GrowthRun (program hnt codes flag) 2 w H (initial nt x under buffer) hf zf 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes flag) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt x under buffer) (final codes flag x under buffer)
    (H + (((nt + 1) * x.length : Nat) : Int))
    (actual_run hnt codes flag x under buffer H) (final_state codes flag x under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes flag) 2 _ _ _ _ _
    (actual_run hnt codes flag x under buffer H)
  have hfinal := occupied_final codes flag x under buffer
  have hi := occupied_initial nt x under buffer
  have he := hg.exact_ledger
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt codes flag) 2 w H hf _ zf hw
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
  have hh := raw_head hnt codes flag x under buffer H hw
  exact ⟨hfalse, hlen, hh.1, hh.2, hc, by simpa [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt x.length) false ∧
      hf = H + (((nt + 1) * x.length : Nat) : Int) ∧ zf = final codes flag x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt x under buffer) (final codes flag x under buffer)
    (H + (((nt + 1) * x.length : Nat) : Int))
    (actual_run hnt codes flag x under buffer H) (final_state codes flag x under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes flag) (initial nt x under buffer)) =
      if deadline nt x.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt x under buffer) (final codes flag x under buffer)
    (H + (((nt + 1) * x.length : Nat) : Int))
    (actual_run hnt codes flag x under buffer H) (final_state codes flag x under buffer) T

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    ∀ r ∈ compile (program hnt codes flag), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt codes flag) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem source_loop_execution_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (deadline nt x.length = nt * x.length * x.length +
      (nt * nt + 7 * nt + 5) * x.length + 1) ∧
    (run (program hnt codes flag) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt x under buffer) =
      some (H + (((nt + 1) * x.length : Nat) : Int), final codes flag x under buffer)) ∧
    ((final codes flag x under buffer).leftRev = (blocks codes flag x).reverse ++ under ∧
      (final codes flag x under buffer).focus = 2 ∧
      (final codes flag x under buffer).right = buffer) ∧
    (∀ w hf zf, run (program hnt codes flag) 2 w H (initial nt x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
        H ≤ hf ∧ hf ≤ H + (((nt + 1) * x.length : Nat) : Int) ∧
        cellCount zf = occupied nt x under buffer ∧
        GrowthRun (program hnt codes flag) 2 w H (initial nt x under buffer) hf zf 0 0) ∧
    (∀ w hf zf, run (program hnt codes flag) 2 w H (initial nt x under buffer) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline nt x.length) false ∧
        hf = H + (((nt + 1) * x.length : Nat) : Int) ∧ zf = final codes flag x under buffer) ∧
    (∀ r ∈ compile (program hnt codes flag), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes flag) (initial nt x under buffer)) =
        if deadline nt x.length ≤ T then 1 else 0) :=
  ⟨deadline_eq nt x.length, actual_run hnt codes flag x under buffer H,
    final_tape codes flag x under buffer,
    fun _ _ _ => every_raw hnt codes flag x under buffer H,
    fun _ _ _ => accepting_word hnt codes flag x under buffer H,
    compiled_symbols hnt codes flag, cutoff_counts hnt codes flag x under buffer H⟩

end PakFixedPolyomino.ULogTernarySourceLoopExecution
