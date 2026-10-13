import PakFixedPolyomino.ULogTernaryNestedHeaderParserSpace
import PakFixedPolyomino.ULogTernaryLeftSentinel
import PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns

/-! Actual positioning and sentinel placement in one finite ternary
bytecode. A positive seed prefix supplies the existing disposable left
cell. All original counted-source cells and arbitrary exterior suffix
survive. Source-end delimitation and the one-hot loader are separate. -/

namespace PakFixedPolyomino.ULogTernaryParserLeftSentinel

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogTernaryRetainedCounterPump (cells)
open ULogTernaryNestedHeaderParser (counted header nested fromCells)

abbrev parserStates (d c : Nat) := d + c + 4
abbrev totalStates (d c : Nat) := ULogFiniteTapeStageComposition.stateCount (parserStates d c) 5

def program (d c : Nat) : BoundedProgram (totalStates d c) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernaryNestedHeaderParser.parserProgram d c)
    ULogTernaryLeftSentinel.program (by change 3 ≤ d + c + 4; omega) (by omega) .stay

def under (d c : Nat) (x : List Bool) (left : List (Fin 3)) : List (Fin 3) :=
  List.replicate (c - 1) 0 ++
    (cells (ULogTernaryNestedHeaderParser.squareHeaders d c x)).reverse ++ left

def initial (d c : Nat) (x : List Bool) (left suffix : List (Fin 3)) :
    BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeStageComposition.leftConfig
    (fromCells (ULogTernaryNestedHeaderParser.startState d c) left (cells (nested d c x) ++ suffix))

def final (d c : Nat) (x : List Bool) (left suffix : List (Fin 3)) :
    BoundedConfig (totalStates d c) 3 :=
  ULogFiniteTapeStageComposition.rightConfig
    (fromCells (0 : Fin 5) (2 :: under d c x left) (cells (counted x) ++ suffix))

theorem real_left_cell (d c : Nat) (x : List Bool) (left : List (Fin 3)) (hc : 0 < c) :
    (cells (header d c x)).reverse ++ left = 0 :: under d c x left := by
  cases c with
  | zero => omega
  | succ c =>
      rw [ULogTernaryNestedHeaderParser.header_eq_square_seed,
        ULogTernaryNestedHeaderParser.cells_append,
        ULogTernaryNestedHeaderParser.cells_replicate_false,
        List.reverse_append, List.reverse_replicate]
      simp [List.replicate_succ, under, List.append_assoc]

theorem counted_tape_nonempty (x : List Bool) (suffix : List (Fin 3)) :
    cells (counted x) ++ suffix ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp [ULogTernaryNestedHeaderParser.cells_length,
    ULogTernaryNestedHeaderParser.counted_length] at hl

theorem marker_run (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) :
    run ULogTernaryLeftSentinel.program 2 (List.replicate 3 false) H
      (ULogFiniteTapeStageComposition.secondStart (by omega) (2 : Fin 3) .stay
        (fromCells (ULogTernaryNestedHeaderParser.acceptState d c)
          ((cells (header d c x)).reverse ++ left) (cells (counted x) ++ suffix))) =
      some (H, fromCells (0 : Fin 5) (2 :: under d c x left) (cells (counted x) ++ suffix)) := by
  rw [real_left_cell d c x left hc]
  cases hr : cells (counted x) ++ suffix with
  | nil => exact (counted_tape_nonempty x suffix hr).elim
  | cons a rest =>
      simpa [ULogFiniteTapeStageComposition.secondStart, fromCells, applyBounded,
        ULogTernaryLeftSentinel.initial, ULogTernaryLeftSentinel.final] using
        ULogTernaryLeftSentinel.actual_run 0 a (under d c x left) rest H

theorem actual_run (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) :
    run (program d c) 2 (List.replicate ((header d c x).length + 5) false) H
      (initial d c x left suffix) =
      some (H + (header d c x).length, final d c x left suffix) := by
  have hp := ULogTernaryNestedHeaderParser.parser_run d c x H left suffix
  have hq := marker_run d c x left suffix hc (H + (header d c x).length)
  have hseq := ULogFiniteTapeStageComposition.sequential_run
    (ULogTernaryNestedHeaderParser.parserProgram d c) ULogTernaryLeftSentinel.program
    (by omega) (by omega) .stay (2 : Fin 3)
    (List.replicate ((header d c x).length + 1) false) (List.replicate 3 false)
    H (H + (header d c x).length) (H + (header d c x).length)
    (fromCells (ULogTernaryNestedHeaderParser.startState d c) left (cells (nested d c x) ++ suffix))
    (fromCells (ULogTernaryNestedHeaderParser.acceptState d c)
      ((cells (header d c x)).reverse ++ left) (cells (counted x) ++ suffix))
    (fromCells (0 : Fin 5) (2 :: under d c x left) (cells (counted x) ++ suffix))
    hp (by simp [ULogTernaryNestedHeaderParserSpace.fromCells_state,
      ULogTernaryNestedHeaderParser.acceptState]) (by simpa [FiniteOneTapeSemantics.moveHead] using hq)
  have hword : List.replicate ((header d c x).length + 5) false =
      List.replicate ((header d c x).length + 1) false ++ false :: List.replicate 3 false := by
    rw [show (header d c x).length + 5 = ((header d c x).length + 1) + 4 by omega,
      List.replicate_add]
    rfl
  rw [hword]
  simpa only [program, initial, final] using hseq

theorem program_falseOnly (d c : Nat) : FalseOnly (program d c) :=
  ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _
    (by change 3 ≤ d + c + 4; omega) (by omega) .stay
    (ULogTernaryNestedHeaderParserSpace.parser_falseOnly d c) ULogTernaryLeftSentinel.program_falseOnly

theorem final_accepts (d c : Nat) (x : List Bool) (left suffix : List (Fin 3)) :
    (final d c x left suffix).state.val = 0 := by
  simp [final, ULogFiniteTapeStageComposition.rightConfig,
    ULogFiniteTapeStageComposition.rightState, ULogTernaryNestedHeaderParserSpace.fromCells_state]

theorem every_raw_length (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) (w : List Bool) (hf : Int) (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w H (initial d c x left suffix) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ (header d c x).length + 5 :=
  ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly d c) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly d c)
      ((header d c x).length + 5) H _ _ _ (actual_run d c x left suffix hc H)
      (final_accepts d c x left suffix) hw⟩

theorem every_raw_space (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) (w : List Bool) (hf : Int) (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w H (initial d c x left suffix) = some (hf, out)) :
    H ≤ hf ∧ hf ≤ H + (header d c x).length ∧
      ULogFiniteTapeGrowthLedger.cellCount out = left.length + (nested d c x).length + suffix.length := by
  have hsplit := ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryNestedHeaderParser.parserProgram d c) ULogTernaryLeftSentinel.program
    (by omega) (by omega) .stay (2 : Fin 3)
    (ULogTernaryNestedHeaderParserSpace.parser_falseOnly d c)
    ((header d c x).length + 1) H (H + (header d c x).length)
    (fromCells (ULogTernaryNestedHeaderParser.startState d c) left (cells (nested d c x) ++ suffix))
    (fromCells (ULogTernaryNestedHeaderParser.acceptState d c)
      ((cells (header d c x)).reverse ++ left) (cells (counted x) ++ suffix))
    (ULogTernaryNestedHeaderParser.parser_run d c x H left suffix)
    (by simp [ULogTernaryNestedHeaderParserSpace.fromCells_state,
      ULogTernaryNestedHeaderParser.acceptState]) w hf out hw
  rcases hsplit with ⟨_, zp, hp, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · have hs := ULogTernaryNestedHeaderParserSpace.every_raw d c x H left suffix hp
    simpa [ULogFiniteTapeGrowthLedger.cellCount, ULogFiniteTapeStageComposition.leftConfig,
      ULogTernaryNestedHeaderParserSpace.cellCount, ULogTernaryNestedHeaderParserSpace.headerLen] using hs.2.2
  · rw [real_left_cell d c x left hc] at hq
    cases hr : cells (counted x) ++ suffix with
    | nil => exact (counted_tape_nonempty x suffix hr).elim
    | cons a rest =>
        have hq' : run ULogTernaryLeftSentinel.program 2 v (H + (header d c x).length)
            (ULogTernaryLeftSentinel.initial 0 a (under d c x left) rest) = some (hf, zq) := by
          simpa [hr, ULogFiniteTapeStageComposition.secondStart, fromCells, applyBounded,
            FiniteOneTapeSemantics.moveHead, ULogTernaryLeftSentinel.initial] using hq
        have hs := ULogTernaryLeftSentinel.every_raw 0 a (under d c x left) rest
          (H + (header d c x).length) v hf zq hq'
        have hhead : 1 ≤ (header d c x).length := by
          simp [ULogTernaryNestedHeaderParser.header_eq_square_seed]
          omega
        have hlu := congrArg List.length (real_left_cell d c x left hc)
        have hrt := congrArg List.length hr
        have hnl := ULogTernaryNestedHeaderParser.nested_length d c x
        simp only [List.length_append, List.length_reverse,
          ULogTernaryNestedHeaderParser.cells_length, List.length_cons] at hlu hrt
        have hcells := hs.2.2.2.2
        refine ⟨by omega, hs.2.2.2.1, ?_⟩
        change ULogFiniteTapeGrowthLedger.cellCount zq = _
        omega

theorem every_raw_no_growth (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) (w : List Bool) (hf : Int) (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w H (initial d c x left suffix) = some (hf, out)) :
    ULogFiniteTapeGrowthLedger.GrowthRun (program d c) 2 w H
      (initial d c x left suffix) hf out 0 0 := by
  obtain ⟨lg, rg, hg⟩ := ULogFiniteTapeGrowthLedger.every_actual_run (program d c) 2 w H hf _ out hw
  have hcells := (every_raw_space d c x left suffix hc H w hf out hw).2.2
  have hne : cells (nested d c x) ++ suffix ≠ [] := by
    intro hn
    have hl := congrArg List.length hn
    simp [ULogTernaryNestedHeaderParser.cells_length,
      ULogTernaryNestedHeaderParser.nested_length,
      ULogTernaryNestedHeaderParser.counted_length] at hl
  have hi : ULogFiniteTapeGrowthLedger.cellCount (initial d c x left suffix) =
      left.length + (nested d c x).length + suffix.length := by
    have hs := ULogTernaryNestedHeaderParserSpace.cellCount_of_cells
      (ULogTernaryNestedHeaderParser.startState d c) left (cells (nested d c x) ++ suffix) hne
    simpa [initial, ULogFiniteTapeStageComposition.leftConfig,
      ULogFiniteTapeGrowthLedger.cellCount, ULogTernaryNestedHeaderParserSpace.cellCount,
      ULogTernaryNestedHeaderParser.cells_length, Nat.add_assoc] using hs
  have he := hg.exact_ledger.2.2.1
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg

theorem every_accepting_word (d c : Nat) (x : List Bool) (left suffix : List (Fin 3))
    (hc : 0 < c) (H : Int) (w : List Bool) (hf : Int) (out : BoundedConfig (totalStates d c) 3)
    (hw : run (program d c) 2 w H (initial d c x left suffix) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate ((header d c x).length + 5) false ∧
      hf = H + (header d c x).length ∧ out = final d c x left suffix :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly d c)
    ((header d c x).length + 5) H _ _ _ (actual_run d c x left suffix hc H)
    (final_accepts d c x left suffix) hw ha

theorem parser_sentinel_spec (d c : Nat) (hc : 0 < c) :
    (∀ x left suffix H,
      run (program d c) 2 (List.replicate ((header d c x).length + 5) false) H
        (initial d c x left suffix) = some (H + (header d c x).length, final d c x left suffix)) ∧
    (∀ x left suffix H w hf out,
      run (program d c) 2 w H (initial d c x left suffix) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ (header d c x).length + 5 ∧
        H ≤ hf ∧ hf ≤ H + (header d c x).length ∧
        ULogFiniteTapeGrowthLedger.cellCount out = left.length + (nested d c x).length + suffix.length ∧
        ULogFiniteTapeGrowthLedger.GrowthRun (program d c) 2 w H (initial d c x left suffix) hf out 0 0) ∧
    (∀ x left suffix H w hf out,
      run (program d c) 2 w H (initial d c x left suffix) = some (hf, out) → out.state.val = 0 →
      w = List.replicate ((header d c x).length + 5) false ∧
        hf = H + (header d c x).length ∧ out = final d c x left suffix) ∧
    (∀ r ∈ compile (program d c), r.read < 3 ∧ r.action.write < 3) := by
  refine ⟨(fun x left suffix H => actual_run d c x left suffix hc H), ?_,
    (fun x left suffix H w hf out hw ha => every_accepting_word d c x left suffix hc H w hf out hw ha), ?_⟩
  · intro x left suffix H w hf out hw
    have ht := every_raw_length d c x left suffix hc H w hf out hw
    have hs := every_raw_space d c x left suffix hc H w hf out hw
    exact ⟨ht.1, ht.2, hs.1, hs.2.1, hs.2.2,
      every_raw_no_growth d c x left suffix hc H w hf out hw⟩
  · intro r hr
    have hb := compile_rule_bounded (program d c) hr
    exact ⟨hb.2.1, hb.2.2.1⟩

end PakFixedPolyomino.ULogTernaryParserLeftSentinel
