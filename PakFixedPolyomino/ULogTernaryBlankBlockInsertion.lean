import PakFixedPolyomino.ULogTernaryFixedWidthInsertion
import PakFixedPolyomino.ULogTernaryOneHotWriteAdvance
import PakFixedPolyomino.ULogFiniteTapeAllocatedLeftShift

/-! A fixed finite controller inserts one unheaded blank block before an
arbitrary binary encoded window. The actual left delimiter survives and the
controller returns to it. Only nt+1 already allocated reserve zeros are used.
This is a real local margin step; the compact margin loop remains separate. -/
namespace PakFixedPolyomino.ULogTernaryBlankBlockInsertion
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells fromCells_state)

abbrev writerStates (nt : Nat) := ULogTernaryOneHotBlockWriter.stateCount nt
abbrev writeStates (nt : Nat) := ULogFiniteTapeMovingSymbolDispatch.stateCount (writerStates nt)
abbrev shiftStates := ULogFiniteTapeMovingSymbolDispatch.stateCount
  (ULogFiniteTapeAllocatedLeftShift.stateCount 2)
abbrev childStates (nt : Nat) := ULogFiniteTapeStageComposition.stateCount (writeStates nt) shiftStates
abbrev stateCount (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  (ULogTernaryFixedWidthInsertion.stateCount (nt + 1)) (childStates nt)

theorem write_states_ge (nt : Nat) : 3 ≤ writeStates nt := by
  unfold writeStates ULogFiniteTapeMovingSymbolDispatch.stateCount ULogFiniteTapeStageComposition.stateCount
  omega

theorem child_states_ge (nt : Nat) : 3 ≤ childStates nt := by
  have := write_states_ge nt
  unfold childStates ULogFiniteTapeStageComposition.stateCount shiftStates
    ULogFiniteTapeMovingSymbolDispatch.stateCount
    ULogFiniteTapeAllocatedLeftShift.stateCount ULogFiniteTapeAllocatedRightShift.stateCount
  omega

theorem shift_states_ge : 3 ≤ shiftStates := by
  unfold shiftStates ULogFiniteTapeMovingSymbolDispatch.stateCount
    ULogFiniteTapeStageComposition.stateCount ULogFiniteTapeAllocatedLeftShift.stateCount
    ULogFiniteTapeAllocatedRightShift.stateCount
  omega

def writeProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (writeStates nt) 3 :=
  ULogFiniteTapeMovingSymbolDispatch.program (ULogTernaryOneHotBlockWriter.program nt hnt)
    (fun _ => ULogTernaryOneHotBlockWriter.entry hnt blank) 0 .right

def shiftProgram {nt : Nat} (blank : Fin nt) : BoundedProgram shiftStates 3 :=
  ULogFiniteTapeMovingSymbolDispatch.program (ULogFiniteTapeAllocatedLeftShift.program 2)
    (fun _ => ULogFiniteTapeAllocatedRightShift.remaining 2 2 le_rfl)
    (ULogTernaryOneHotWriteAdvance.firstBit blank) .stay

def childProgram {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (childStates nt) 3 :=
  ULogFiniteTapeStageComposition.program (writeProgram hnt blank) (shiftProgram blank)
    (write_states_ge nt) shift_states_ge .stay

def childEntry (nt : Nat) : Fin (childStates nt) :=
  ULogFiniteTapeStageComposition.leftState ⟨2, by have := write_states_ge nt; omega⟩

def program {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernaryFixedWidthInsertion.program (nt + 1))
    (childProgram hnt blank) (ULogTernaryFixedWidthInsertion.stateCount_ge (nt + 1))
    (child_states_ge nt) .right

def initial (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeStageComposition.leftConfig
    (ULogTernaryFixedWidthInsertion.initial (nt + 1) source under buffer)

def final {nt : Nat} (blank : Fin nt) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ⟨⟨0, by have := child_states_ge nt; unfold stateCount ULogFiniteTapeStageComposition.stateCount; omega⟩,
    under, 2, 0 :: (ULogTernaryOneHotBlockWriter.bits blank ++ cells source ++ 2 :: buffer)⟩

def writeTicks (nt : Nat) := 1 + ULogTernaryOneHotBlockWriter.deadline nt
def childTicks (nt : Nat) := writeTicks nt + 1 + 3
def deadline (nt n : Nat) := ULogTernaryFixedWidthInsertion.ticks (nt + 1) n + 1 + childTicks nt

def writeInitial (nt : Nat) (under suffix : List (Fin 3)) : BoundedConfig (writeStates nt) 3 :=
  ULogFiniteTapeMovingSymbolDispatch.initial 0 (2 :: under) (List.replicate nt 0 ++ suffix)

def writeFinal {nt : Nat} (blank : Fin nt) (under suffix : List (Fin 3)) :
    BoundedConfig (writeStates nt) 3 :=
  ULogFiniteTapeStageComposition.rightConfig (ns := 3)
    (ULogTernaryOneHotBlockWriter.final blank (0 :: 2 :: under) suffix)

theorem write_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under suffix : List (Fin 3)) (H : Int) :
    run (writeProgram hnt blank) 2 (List.replicate (writeTicks nt) false) H
      (writeInitial nt under suffix) = some (H + 1, writeFinal blank under suffix) := by
  have hm : ULogFiniteTapeMovingSymbolDispatch.moved
      (fun _ => ULogTernaryOneHotBlockWriter.entry hnt blank) 0 (2 : Fin 3) .right
      0 (2 :: under) (List.replicate nt 0 ++ suffix) =
        ULogTernaryOneHotBlockWriter.initial hnt blank (0 :: 2 :: under) suffix := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnt)
    simp [ULogFiniteTapeMovingSymbolDispatch.moved, applyBounded,
      ULogTernaryOneHotBlockWriter.initial, fromCells, List.replicate_succ]
  unfold writeProgram writeInitial writeTicks
  rw [show 1 + ULogTernaryOneHotBlockWriter.deadline nt =
      ULogTernaryOneHotBlockWriter.deadline nt + 1 by omega,
    List.replicate_succ, ULogFiniteTapeMovingSymbolDispatch.run_dispatch_cons, hm,
    FiniteOneTapeSemantics.moveHead, ULogTernaryOneHotBlockWriter.writer_run hnt blank]
  rfl

theorem write_accepts {nt : Nat} (blank : Fin nt) (under suffix : List (Fin 3)) :
    (writeFinal blank under suffix).state.val = 0 := by
  simp [writeFinal, ULogTernaryOneHotBlockWriter.final, fromCells_state,
    ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState]

def shiftInitial {nt : Nat} (blank : Fin nt) (under suffix : List (Fin 3)) :
    BoundedConfig shiftStates 3 :=
  ULogFiniteTapeMovingSymbolDispatch.initial
    (ULogTernaryOneHotWriteAdvance.firstBit blank) (0 :: 2 :: under)
    ((ULogTernaryOneHotBlockWriter.bits blank).drop 1 ++ suffix)

theorem shift_run {nt : Nat} (blank : Fin nt) (under suffix : List (Fin 3)) (H : Int) :
    run (shiftProgram blank) 2 (List.replicate 3 false) H
      (shiftInitial blank under suffix) =
      some (H - 2, ULogFiniteTapeStageComposition.rightConfig (ns := 3)
        (ULogFiniteTapeAllocatedLeftShift.final 2
          ((ULogTernaryOneHotBlockWriter.bits blank).drop 1 ++ suffix)
          [ULogTernaryOneHotWriteAdvance.firstBit blank, 0] (2 :: under))) := by
  have hm : ULogFiniteTapeMovingSymbolDispatch.moved
      (fun _ => ULogFiniteTapeAllocatedRightShift.remaining 2 2 le_rfl)
      (ULogTernaryOneHotWriteAdvance.firstBit blank) (2 : Fin 3) .stay
      (ULogTernaryOneHotWriteAdvance.firstBit blank) (0 :: 2 :: under)
      ((ULogTernaryOneHotBlockWriter.bits blank).drop 1 ++ suffix) =
        ULogFiniteTapeAllocatedLeftShift.initial 2
          ((ULogTernaryOneHotBlockWriter.bits blank).drop 1 ++ suffix)
          [ULogTernaryOneHotWriteAdvance.firstBit blank, 0] (2 :: under) := rfl
  unfold shiftProgram shiftInitial
  rw [show List.replicate 3 false = false :: List.replicate 2 false by rfl,
    ULogFiniteTapeMovingSymbolDispatch.run_dispatch_cons, hm,
    FiniteOneTapeSemantics.moveHead,
    ULogFiniteTapeAllocatedLeftShift.actual_run 2 _ _ _ (by rfl) (by simp)]
  rfl

theorem write_second_start {nt : Nat} (blank : Fin nt) (under suffix : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (ms := shiftStates)
      shift_states_ge (2 : Fin 3) .stay
      (writeFinal blank under suffix) = shiftInitial blank under suffix := by
  change ULogFiniteTapeStageComposition.secondStart shift_states_ge (2 : Fin 3) .stay
    (ULogFiniteTapeStageComposition.rightConfig (ns := 3)
      (fromCells 0 (0 :: 2 :: under) (ULogTernaryOneHotBlockWriter.bits blank ++ suffix))) = _
  rw [ULogTernaryOneHotWriteAdvance.bits_cons blank]
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded, fromCells,
    ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
    shiftInitial, ULogFiniteTapeMovingSymbolDispatch.initial]

theorem child_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (under suffix : List (Fin 3)) (H : Int) :
    run (childProgram hnt blank) 2 (List.replicate (childTicks nt) false) H
      (ULogFiniteTapeStageComposition.leftConfig (writeInitial nt under suffix)) =
      some (H - 1, ULogFiniteTapeStageComposition.rightConfig
        (ULogFiniteTapeStageComposition.rightConfig (ns := 3)
          (ULogFiniteTapeAllocatedLeftShift.final 2
            ((ULogTernaryOneHotBlockWriter.bits blank).drop 1 ++ suffix)
            [ULogTernaryOneHotWriteAdvance.firstBit blank, 0] (2 :: under)))) := by
  have h := ULogFiniteTapeStageComposition.sequential_run (writeProgram hnt blank)
    (shiftProgram blank) (write_states_ge nt)
    shift_states_ge .stay (2 : Fin 3)
    (List.replicate (writeTicks nt) false) (List.replicate 3 false) H (H + 1) (H - 1)
    (writeInitial nt under suffix) (writeFinal blank under suffix) _
    (write_run hnt blank under suffix H) (write_accepts blank under suffix) (by
      rw [write_second_start, FiniteOneTapeSemantics.moveHead]
      simpa only [show H + 1 - 2 = H - 1 by omega] using
        shift_run blank under suffix (H + 1))
  have word : List.replicate (childTicks nt) false =
      List.replicate (writeTicks nt) false ++ false :: List.replicate 3 false := by
    simp [childTicks, List.replicate_add, List.append_assoc]
  rw [word]
  exact h

theorem insertion_second_start (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (child_states_ge nt) (2 : Fin 3) .right
      (ULogTernaryFixedWidthInsertion.final (nt + 1) source under buffer) =
      ULogFiniteTapeStageComposition.leftConfig
        (writeInitial nt under (cells source ++ 2 :: buffer)) := by
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded,
    ULogTernaryFixedWidthInsertion.final, List.replicate_succ,
    writeInitial, ULogFiniteTapeMovingSymbolDispatch.initial,
    ULogFiniteTapeStageComposition.leftConfig, ULogFiniteTapeStageComposition.leftState]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt blank) 2 (List.replicate (deadline nt source.length) false) H
      (initial nt source under buffer) = some (H, final blank source under buffer) := by
  have hc := child_run hnt blank under (cells source ++ 2 :: buffer) (H + 1)
  have h := ULogFiniteTapeStageComposition.sequential_run
    (ULogTernaryFixedWidthInsertion.program (nt + 1)) (childProgram hnt blank)
    (ULogTernaryFixedWidthInsertion.stateCount_ge (nt + 1)) (child_states_ge nt)
    .right (2 : Fin 3)
    (List.replicate (ULogTernaryFixedWidthInsertion.ticks (nt + 1) source.length) false)
    (List.replicate (childTicks nt) false) H H H _ _ _
    (ULogTernaryFixedWidthInsertion.insertion_run (nt + 1) source under buffer H)
    (ULogTernaryFixedWidthInsertion.final_state (nt + 1) source under buffer) (by
      rw [insertion_second_start, FiniteOneTapeSemantics.moveHead]
      simpa only [show H + 1 - 1 = H by omega] using hc)
  have word : List.replicate (deadline nt source.length) false =
      List.replicate (ULogTernaryFixedWidthInsertion.ticks (nt + 1) source.length) false ++
        false :: List.replicate (childTicks nt) false := by
    simp [deadline, List.replicate_add, List.append_assoc]
  unfold program initial
  rw [word]
  convert h using 1
  simp [ULogFiniteTapeAllocatedLeftShift.final, ULogFiniteTapeReflection.reflectConfig,
    ULogFiniteTapeAllocatedRightShift.final, fromCells,
    ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
    final, List.append_assoc]
  simpa only [List.drop_one, List.cons_append] using
    congrArg (fun xs => xs ++ (cells source ++ 2 :: buffer))
      (ULogTernaryOneHotWriteAdvance.bits_cons blank)


theorem stateCount_eq (nt : Nat) : stateCount nt = nt * nt + 10 * nt + 28 := by
  simp [stateCount, childStates, writeStates, writerStates, shiftStates,
    ULogFiniteTapeMovingSymbolDispatch.stateCount, ULogFiniteTapeStageComposition.stateCount,
    ULogFiniteTapeAllocatedLeftShift.stateCount, ULogFiniteTapeAllocatedRightShift.stateCount,
    ULogTernaryOneHotBlockWriter.stateCount, ULogTernaryFixedWidthInsertion.stateCount_eq]
  ring

theorem deadline_eq {nt : Nat} (hnt : 0 < nt) (n : Nat) :
    deadline nt n = 2 * (nt + 1) * n + nt * nt + 9 * nt + 11 := by
  have hd : ULogTernaryOneHotBlockWriter.deadline nt + 1 = 2 * nt := by
    unfold ULogTernaryOneHotBlockWriter.deadline; omega
  calc
    deadline nt n = ULogTernaryFixedWidthInsertion.ticks (nt + 1) n +
        ULogTernaryOneHotBlockWriter.deadline nt + 6 := by
      unfold deadline childTicks writeTicks; omega
    _ = ULogTernaryFixedWidthInsertion.ticks (nt + 1) n + 2 * nt + 5 := by omega
    _ = _ := by rw [ULogTernaryFixedWidthInsertion.ticks_eq]; ring

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (program hnt blank) := by
  apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
  · exact ULogTernaryFixedWidthInsertion.program_falseOnly (nt + 1)
  · apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
    · exact ULogFiniteTapeMovingSymbolDispatch.program_falseOnly _ _ _ _
        (ULogTernaryOneHotBlockWriter.program_falseOnly hnt)
    · exact ULogFiniteTapeMovingSymbolDispatch.program_falseOnly _ _ _ _
        (ULogFiniteTapeAllocatedLeftShift.program_falseOnly 2)

theorem final_accepts {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) : (final blank source under buffer).state.val = 0 := rfl

def occupied (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :=
  under.length + source.length + nt + 3 + buffer.length

theorem initial_cells (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial nt source under buffer) = occupied nt source under buffer := by
  simp [initial, ULogFiniteTapeStageComposition.leftConfig,
    ULogTernaryFixedWidthInsertion.initial, cellCount, occupied, cells]
  omega

theorem final_cells {nt : Nat} (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (final blank source under buffer) = occupied nt source under buffer := by
  simp [final, cellCount, occupied, cells, ULogTernaryOneHotWriteAdvance.bits_length]
  omega

theorem every_raw {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt source under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt source.length ∧
      cellCount out = occupied nt source under buffer ∧
      GrowthRun (program hnt blank) 2 w H (initial nt source under buffer) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt blank) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt blank) 2 _ _ _ _ _
    (actual_run hnt blank source under buffer H)
  have ledger := hg.exact_ledger
  have hi := initial_cells nt source under buffer
  have ho := final_cells blank source under buffer
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt blank) 2 w H hf _ out hw
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

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt source under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt source.length) false ∧ hf = H ∧
      out = final blank source under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial nt source under buffer)) =
      if deadline nt source.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt source.length) H (initial nt source under buffer) (final blank source under buffer) H
    (actual_run hnt blank source under buffer H) (final_accepts blank source under buffer) T

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    ∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt blank) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem blank_block_insertion_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (run (program hnt blank) 2 (List.replicate (deadline nt source.length) false) H
      (initial nt source under buffer) = some (H, final blank source under buffer)) ∧
    (final blank source under buffer).leftRev = under ∧
    (final blank source under buffer).focus = 2 ∧
    (final blank source under buffer).right =
      0 :: (ULogTernaryOneHotBlockWriter.bits blank ++ cells source ++ 2 :: buffer) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt source.length ∧
        cellCount out = occupied nt source under buffer ∧
        GrowthRun (program hnt blank) 2 w H (initial nt source under buffer) hf out 0 0) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt source under buffer) = some (hf, out) →
      out.state.val = 0 → w = List.replicate (deadline nt source.length) false ∧
        hf = H ∧ out = final blank source under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial nt source under buffer)) =
        if deadline nt source.length ≤ T then 1 else 0) ∧
    (∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3) ∧
    stateCount nt = nt * nt + 10 * nt + 28 ∧
    deadline nt source.length = 2 * (nt + 1) * source.length + nt * nt + 9 * nt + 11 :=
  ⟨actual_run hnt blank source under buffer H, rfl, rfl, rfl,
    fun _ _ _ => every_raw hnt blank source under buffer H,
    fun _ _ _ => accepting_word hnt blank source under buffer H,
    cutoff_counts hnt blank source under buffer H, compiled_symbols hnt blank,
    stateCount_eq nt, deadline_eq hnt source.length⟩

end PakFixedPolyomino.ULogTernaryBlankBlockInsertion
