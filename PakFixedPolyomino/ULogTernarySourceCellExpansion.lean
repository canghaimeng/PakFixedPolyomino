import PakFixedPolyomino.ULogTernaryFixedWidthInsertion
import PakFixedPolyomino.ULogTernaryOneHotWriteAdvance
import PakFixedPolyomino.ULogFiniteTapeSymbolBranch

/-! Actual finite source-cell expansion. Read the original ternary cell,
retain it in an indexed parent copy, clear it to the insertion marker, make
room without losing any unread binary cells, write its selected onehot block
and advance to the next unread cell. Width/codes/flag are controller constants.
This is one local cell stage, not the complete compact source loader. -/

namespace PakFixedPolyomino.ULogTernarySourceCellExpansion

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)

def parentStates (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  (ULogTernaryFixedWidthInsertion.stateCount nt) (ULogTernaryOneHotWriteAdvance.stateCount nt)

theorem advance_states_ge (nt : Nat) : 3 ≤ ULogTernaryOneHotWriteAdvance.stateCount nt := by
  unfold ULogTernaryOneHotWriteAdvance.stateCount ULogFiniteTapeMovingSymbolDispatch.stateCount
    ULogFiniteTapeStageComposition.stateCount
  omega

def parentProgram {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool) :
    BoundedProgram (parentStates nt) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernaryFixedWidthInsertion.program nt)
    (ULogTernaryOneHotWriteAdvance.program hnt a flag)
    (ULogTernaryFixedWidthInsertion.stateCount_ge nt) (advance_states_ge nt) .stay

def parentEntry (nt : Nat) : Fin (parentStates nt) :=
  ULogFiniteTapeStageComposition.leftState (ULogTernaryFixedWidthInsertion.entry nt)

def parentInitial (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (parentStates nt) 3 :=
  ULogFiniteTapeStageComposition.leftConfig
    (ULogTernaryFixedWidthInsertion.initial nt x under buffer)

def parentFinal {nt : Nat} (a : Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) : BoundedConfig (parentStates nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig
    (ULogTernaryOneHotWriteAdvance.final a flag under (cells x ++ 2 :: buffer))

def parentTicks (nt n : Nat) := ULogTernaryFixedWidthInsertion.ticks nt n + 1 +
  ULogTernaryOneHotWriteAdvance.deadline nt

theorem suffix_nonempty (x : List Bool) (buffer : List (Fin 3)) :
    cells x ++ 2 :: buffer ≠ [] := by simp

theorem second_start (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (advance_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryFixedWidthInsertion.final nt x under buffer) =
      ULogTernaryOneHotWriteAdvance.initial nt under (cells x ++ 2 :: buffer) := by
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded,
    ULogTernaryFixedWidthInsertion.final, ULogTernaryOneHotWriteAdvance.initial,
    ULogFiniteTapeMovingSymbolDispatch.initial, List.append_assoc]
  rfl

theorem parent_run {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (parentProgram hnt a flag) 2 (List.replicate (parentTicks nt x.length) false) H
      (parentInitial nt x under buffer) =
      some (H + ((nt + 1 : Nat) : Int), parentFinal a flag x under buffer) := by
  have hs := ULogFiniteTapeStageComposition.sequential_run
    (ULogTernaryFixedWidthInsertion.program nt) (ULogTernaryOneHotWriteAdvance.program hnt a flag)
    (ULogTernaryFixedWidthInsertion.stateCount_ge nt) (advance_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryFixedWidthInsertion.ticks nt x.length) false)
    (List.replicate (ULogTernaryOneHotWriteAdvance.deadline nt) false) H H
    (H + ((nt + 1 : Nat) : Int)) (ULogTernaryFixedWidthInsertion.initial nt x under buffer)
    (ULogTernaryFixedWidthInsertion.final nt x under buffer)
    (ULogTernaryOneHotWriteAdvance.final a flag under (cells x ++ 2 :: buffer))
    (ULogTernaryFixedWidthInsertion.insertion_run nt x under buffer H)
    (ULogTernaryFixedWidthInsertion.final_state nt x under buffer)
    (by
      change run (ULogTernaryOneHotWriteAdvance.program hnt a flag) 2 _ H _ = _
      rw [second_start]
      exact ULogTernaryOneHotWriteAdvance.actual_run hnt a flag under
        (cells x ++ 2 :: buffer) (suffix_nonempty x buffer) H)
  have hw : List.replicate (parentTicks nt x.length) false =
      List.replicate (ULogTernaryFixedWidthInsertion.ticks nt x.length) false ++ false ::
        List.replicate (ULogTernaryOneHotWriteAdvance.deadline nt) false := by
    simp [parentTicks, List.replicate_add, List.append_assoc]
  rw [hw]
  exact hs

theorem parent_falseOnly {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool) :
    FalseOnly (parentProgram hnt a flag) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
    (ULogTernaryFixedWidthInsertion.program_falseOnly nt)
    (ULogTernaryOneHotWriteAdvance.program_falseOnly hnt a flag)

theorem parent_raw_head {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (parentStates nt) 3}
    (hw : run (parentProgram hnt a flag) 2 w H (parentInitial nt x under buffer) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + ((x.length + nt + 1 : Nat) : Int) := by
  rcases ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryFixedWidthInsertion.program nt) (ULogTernaryOneHotWriteAdvance.program hnt a flag)
    (ULogTernaryFixedWidthInsertion.stateCount_ge nt) (advance_states_ge nt) .stay (2 : Fin 3)
    (ULogTernaryFixedWidthInsertion.program_falseOnly nt)
    (ULogTernaryFixedWidthInsertion.ticks nt x.length) H H
    (ULogTernaryFixedWidthInsertion.initial nt x under buffer)
    (ULogTernaryFixedWidthInsertion.final nt x under buffer)
    (ULogTernaryFixedWidthInsertion.insertion_run nt x under buffer H)
    (ULogTernaryFixedWidthInsertion.final_state nt x under buffer) w hf zf hw with hfirst | hsecond
  · obtain ⟨_, zp, hp, _⟩ := hfirst
    have h := ULogTernaryFixedWidthInsertion.raw_geometry nt x under buffer H hp
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨v, zq, _, hq, _⟩ := hsecond
    rw [second_start] at hq
    simp only [FiniteOneTapeSemantics.moveHead] at hq
    have h := ULogTernaryOneHotWriteAdvance.raw_head hnt a flag under
      (cells x ++ 2 :: buffer) (suffix_nonempty x buffer) H hq
    exact ⟨h.1, by omega⟩

def stateCount (nt : Nat) :=
  ULogFiniteTapeSymbolDispatch.stateCount (ULogFiniteTapeSymbolBranch.stateCount (parentStates nt))

def program {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeSymbolBranch.dispatch (fun symbol => parentProgram hnt (codes symbol) flag)
    (fun _ => parentEntry nt) 2

def initial (nt : Nat) (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeSymbolDispatch.initial symbol under (cells x ++ 2 :: List.replicate nt 0 ++ buffer)

def final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig (ns := 3)
    (ULogFiniteTapeSymbolBranch.branchConfig symbol (parentFinal (codes symbol) flag x under buffer))

def deadline (nt n : Nat) := parentTicks nt n + 1

theorem deadline_eq (nt n : Nat) : deadline nt n = 2 * nt * n + nt * nt + 8 * nt + 4 := by
  simp [deadline, parentTicks, ULogTernaryFixedWidthInsertion.ticks_eq,
    ULogTernaryOneHotWriteAdvance.deadline]; ring

theorem selected_start (nt : Nat) (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeSymbolDispatch.dispatched
      (fun s => ULogFiniteTapeSymbolBranch.branchState s (parentEntry nt)) 2 symbol under
      (cells x ++ 2 :: List.replicate nt 0 ++ buffer) =
      ULogFiniteTapeSymbolBranch.branchConfig symbol (parentInitial nt x under buffer) := rfl

theorem actual_run {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt codes flag) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt symbol x under buffer) =
      some (H + ((nt + 1 : Nat) : Int), final codes flag symbol x under buffer) := by
  change run (ULogFiniteTapeSymbolDispatch.program
    (ULogFiniteTapeSymbolBranch.program (fun s => parentProgram hnt (codes s) flag))
    (fun s => ULogFiniteTapeSymbolBranch.branchState s (parentEntry nt)) 2)
    2 _ H (ULogFiniteTapeSymbolDispatch.initial symbol under
      (cells x ++ 2 :: List.replicate nt 0 ++ buffer)) = _
  rw [deadline, List.replicate_succ, ULogFiniteTapeSymbolDispatch.run_dispatch_cons,
    selected_start, ULogFiniteTapeSymbolBranch.run_branch_map,
    parent_run hnt (codes symbol) flag x under buffer H]
  rfl

theorem final_state {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes flag symbol x under buffer).state.val = 0 := by
  apply (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
  apply (ULogFiniteTapeSymbolBranch.branch_accepts _ _).2
  apply (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
  exact ULogTernaryOneHotWriteAdvance.final_state _ _ _ _

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    FalseOnly (program hnt codes flag) :=
  ULogFiniteTapeSymbolBranch.dispatch_falseOnly _ _ _
    (fun s => parent_falseOnly hnt (codes s) flag)

theorem raw_head {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt symbol x under buffer) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + ((x.length + nt + 1 : Nat) : Int) := by
  rcases (ULogFiniteTapeSymbolDispatch.every_raw_run_splits
    (ULogFiniteTapeSymbolBranch.program (fun s => parentProgram hnt (codes s) flag))
    (fun s => ULogFiniteTapeSymbolBranch.branchState s (parentEntry nt)) 2 (2 : Fin 3)
    symbol under (cells x ++ 2 :: List.replicate nt 0 ++ buffer) H hf w zf).1 hw with
    ⟨_, rfl, _⟩ | ⟨rest, out, _, hp, _⟩
  · exact ⟨le_refl _, by omega⟩
  · rw [selected_start, ULogFiniteTapeSymbolBranch.run_branch_map] at hp
    obtain ⟨⟨h, zp⟩, hparent, he⟩ := Option.map_eq_some_iff.mp hp
    rcases Prod.mk.inj he with ⟨rfl, _⟩
    exact parent_raw_head hnt (codes symbol) flag x under buffer H hparent

def occupied (nt : Nat) (x : List Bool) (under buffer : List (Fin 3)) :=
  under.length + x.length + nt + 2 + buffer.length

theorem occupied_initial (nt : Nat) (symbol : Fin 3) (x : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (initial nt symbol x under buffer) = occupied nt x under buffer := by
  simp [initial, ULogFiniteTapeSymbolDispatch.initial, cellCount, occupied, cells]; omega

theorem occupied_final {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final codes flag symbol x under buffer) = occupied nt x under buffer := by
  change cellCount (ULogTernaryOneHotWriteAdvance.final (codes symbol) flag under
    (cells x ++ 2 :: buffer)) = occupied nt x under buffer
  rw [ULogTernaryOneHotWriteAdvance.occupied_final _ _ _ _ (suffix_nonempty x buffer)]
  simp [ULogTernaryOneHotWriteAdvance.occupied, occupied, cells]; omega

theorem final_tape {nt : Nat} (codes : Fin 3 → Fin nt) (flag : Bool) (symbol : Fin 3)
    (x : List Bool) (under buffer : List (Fin 3)) :
    (final codes flag symbol x under buffer).leftRev =
      (ULogTernaryOneHotBlockWriter.bits (codes symbol)).reverse ++ cell flag :: under ∧
    (final codes flag symbol x under buffer).focus :: (final codes flag symbol x under buffer).right =
      cells x ++ 2 :: buffer := by
  have hn := suffix_nonempty x buffer
  cases hc : cells x ++ 2 :: buffer with
  | nil => exact (hn hc).elim
  | cons a rest =>
      simp [final, parentFinal, ULogTernaryOneHotWriteAdvance.final,
        ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeSymbolBranch.branchConfig,
        ULogTernaryCountedSourceDelimiter.fromCells, hc]

theorem every_raw {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt symbol x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
      H ≤ hf ∧ hf ≤ H + ((x.length + nt + 1 : Nat) : Int) ∧
      cellCount zf = occupied nt x under buffer ∧
      GrowthRun (program hnt codes flag) 2 w H (initial nt symbol x under buffer) hf zf 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes flag) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes flag symbol x under buffer)
    (H + ((nt + 1 : Nat) : Int)) (actual_run hnt codes flag symbol x under buffer H)
    (final_state codes flag symbol x under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes flag) 2 _ _ _ _ _
    (actual_run hnt codes flag symbol x under buffer H)
  have hfinal := occupied_final codes flag symbol x under buffer
  have hi := occupied_initial nt symbol x under buffer
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
  have hh := raw_head hnt codes flag symbol x under buffer H hw
  exact ⟨hfalse, hlen, hh.1, hh.2, hc, by simpa [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt codes flag) 2 w H (initial nt symbol x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt x.length) false ∧ hf = H + ((nt + 1 : Nat) : Int) ∧
      zf = final codes flag symbol x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes flag symbol x under buffer)
    (H + ((nt + 1 : Nat) : Int)) (actual_run hnt codes flag symbol x under buffer H)
    (final_state codes flag symbol x under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes flag) (initial nt symbol x under buffer)) =
        if deadline nt x.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt codes flag)
    (deadline nt x.length) H (initial nt symbol x under buffer) (final codes flag symbol x under buffer)
    (H + ((nt + 1 : Nat) : Int)) (actual_run hnt codes flag symbol x under buffer H)
    (final_state codes flag symbol x under buffer) T

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool) :
    ∀ r ∈ compile (program hnt codes flag), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt codes flag) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem source_cell_expansion_spec {nt : Nat} (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (flag : Bool)
    (symbol : Fin 3) (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (deadline nt x.length = 2 * nt * x.length + nt * nt + 8 * nt + 4) ∧
    (run (program hnt codes flag) 2 (List.replicate (deadline nt x.length) false) H
      (initial nt symbol x under buffer) =
      some (H + ((nt + 1 : Nat) : Int), final codes flag symbol x under buffer)) ∧
    ((final codes flag symbol x under buffer).leftRev =
      (ULogTernaryOneHotBlockWriter.bits (codes symbol)).reverse ++ cell flag :: under ∧
      (final codes flag symbol x under buffer).focus :: (final codes flag symbol x under buffer).right =
        cells x ++ 2 :: buffer) ∧
    (∀ w hf zf, run (program hnt codes flag) 2 w H (initial nt symbol x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt x.length ∧
        H ≤ hf ∧ hf ≤ H + ((x.length + nt + 1 : Nat) : Int) ∧
        cellCount zf = occupied nt x under buffer ∧
        GrowthRun (program hnt codes flag) 2 w H (initial nt symbol x under buffer) hf zf 0 0) ∧
    (∀ w hf zf, run (program hnt codes flag) 2 w H (initial nt symbol x under buffer) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline nt x.length) false ∧
        hf = H + ((nt + 1 : Nat) : Int) ∧ zf = final codes flag symbol x under buffer) ∧
    (∀ r ∈ compile (program hnt codes flag), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt codes flag) (initial nt symbol x under buffer)) =
        if deadline nt x.length ≤ T then 1 else 0) :=
  ⟨deadline_eq nt x.length, actual_run hnt codes flag symbol x under buffer H,
    final_tape codes flag symbol x under buffer,
    fun _ _ _ => every_raw hnt codes flag symbol x under buffer H,
    fun _ _ _ => accepting_word hnt codes flag symbol x under buffer H,
    compiled_symbols hnt codes flag, cutoff_counts hnt codes flag symbol x under buffer H⟩

end PakFixedPolyomino.ULogTernarySourceCellExpansion
