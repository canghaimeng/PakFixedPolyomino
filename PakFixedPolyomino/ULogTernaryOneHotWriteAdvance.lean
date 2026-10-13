import PakFixedPolyomino.ULogTernaryOneHotBlockWriter
import PakFixedPolyomino.ULogFiniteTapeAllocatedRightShift
import PakFixedPolyomino.ULogFiniteTapeMovingSymbolDispatch

/-! Write one flagged onehot block into actual allocated zeros and advance to
the next source cell. The selected code and flag are finite controller constants.
Both dispatches and the internal handoff are real ticks. The shift entry is
explicitly `remaining nt nt`, not the shift program's different state2. -/

namespace PakFixedPolyomino.ULogTernaryOneHotWriteAdvance

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells fromCells_state)

def firstBit {nt : Nat} (a : Fin nt) : Fin 3 := cell (if a.val = 0 then true else false)

theorem bits_length {nt : Nat} (a : Fin nt) :
    (ULogTernaryOneHotBlockWriter.bits a).length = nt := by
  simp [ULogTernaryOneHotBlockWriter.bits, cells, ULogSourceOneHotBlocks.encodeOneHot_length]

theorem bits_cons {nt : Nat} (a : Fin nt) :
    ULogTernaryOneHotBlockWriter.bits a =
      firstBit a :: (ULogTernaryOneHotBlockWriter.bits a).drop 1 := by
  cases h : a.val with
  | zero => simp [ULogTernaryOneHotBlockWriter.bits, cells,
      ULogSourceOneHotBlocks.encodeOneHot, firstBit, h]
  | succ k => simp [ULogTernaryOneHotBlockWriter.bits, cells,
      ULogSourceOneHotBlocks.encodeOneHot, firstBit, h, List.replicate_succ]

def shiftStates (nt : Nat) :=
  ULogFiniteTapeMovingSymbolDispatch.stateCount (ULogFiniteTapeAllocatedRightShift.stateCount nt)

def shiftProgram {nt : Nat} (a : Fin nt) : BoundedProgram (shiftStates nt) 3 :=
  ULogFiniteTapeMovingSymbolDispatch.program (ULogFiniteTapeAllocatedRightShift.program nt)
    (fun _ => ULogFiniteTapeAllocatedRightShift.remaining nt nt le_rfl) (firstBit a) .stay

def combinedStates (nt : Nat) := ULogFiniteTapeStageComposition.stateCount
  (ULogTernaryOneHotBlockWriter.stateCount nt) (shiftStates nt)

theorem writer_states_ge {nt : Nat} (hnt : 0 < nt) :
    3 ≤ ULogTernaryOneHotBlockWriter.stateCount nt := by
  unfold ULogTernaryOneHotBlockWriter.stateCount; nlinarith

theorem shift_states_ge (nt : Nat) : 3 ≤ shiftStates nt := by
  unfold shiftStates ULogFiniteTapeMovingSymbolDispatch.stateCount
    ULogFiniteTapeStageComposition.stateCount ULogFiniteTapeAllocatedRightShift.stateCount
  omega

def combinedProgram {nt : Nat} (hnt : 0 < nt) (a : Fin nt) :
    BoundedProgram (combinedStates nt) 3 :=
  ULogFiniteTapeStageComposition.program (ULogTernaryOneHotBlockWriter.program nt hnt)
    (shiftProgram a) (writer_states_ge hnt) (shift_states_ge nt) .stay

def combinedEntry {nt : Nat} (hnt : 0 < nt) (a : Fin nt) : Fin (combinedStates nt) :=
  ULogFiniteTapeStageComposition.leftState (ULogTernaryOneHotBlockWriter.entry hnt a)

def stateCount (nt : Nat) := ULogFiniteTapeMovingSymbolDispatch.stateCount (combinedStates nt)

def program {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool) :
    BoundedProgram (stateCount nt) 3 :=
  ULogFiniteTapeMovingSymbolDispatch.program (combinedProgram hnt a)
    (fun _ => combinedEntry hnt a) (cell flag) .right

def initial (nt : Nat) (under suffix : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogFiniteTapeMovingSymbolDispatch.initial 2 under (List.replicate nt 0 ++ suffix)

def final {nt : Nat} (a : Fin nt) (flag : Bool) (under suffix : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  fromCells ⟨0, by
    unfold stateCount ULogFiniteTapeMovingSymbolDispatch.stateCount
      ULogFiniteTapeStageComposition.stateCount
    omega⟩
    ((ULogTernaryOneHotBlockWriter.bits a).reverse ++ cell flag :: under) suffix

def deadline (nt : Nat) := 3 * nt + 2

theorem shift_moved {nt : Nat} (a : Fin nt) (left suffix : List (Fin 3)) :
    ULogFiniteTapeMovingSymbolDispatch.moved
      (fun _ => ULogFiniteTapeAllocatedRightShift.remaining nt nt le_rfl) (firstBit a)
      (2 : Fin 3) .stay (firstBit a) left
      ((ULogTernaryOneHotBlockWriter.bits a).drop 1 ++ suffix) =
      ULogFiniteTapeAllocatedRightShift.initial nt left
        (ULogTernaryOneHotBlockWriter.bits a) suffix := by
  rw [ULogFiniteTapeAllocatedRightShift.initial, bits_cons a]
  simp [ULogFiniteTapeMovingSymbolDispatch.moved, applyBounded, fromCells]

theorem shift_run {nt : Nat} (a : Fin nt) (left suffix : List (Fin 3))
    (hne : suffix ≠ []) (H : Int) :
    run (shiftProgram a) 2 (List.replicate (nt + 1) false) H
      (ULogFiniteTapeMovingSymbolDispatch.initial (firstBit a) left
        ((ULogTernaryOneHotBlockWriter.bits a).drop 1 ++ suffix)) =
      some (H + (nt : Int), ULogFiniteTapeStageComposition.rightConfig (ns := 3)
        (ULogFiniteTapeAllocatedRightShift.final nt left
          (ULogTernaryOneHotBlockWriter.bits a) suffix)) := by
  have hp := ULogFiniteTapeAllocatedRightShift.actual_run nt left
    (ULogTernaryOneHotBlockWriter.bits a) suffix (bits_length a) hne H
  change run (ULogFiniteTapeMovingSymbolDispatch.program
    (ULogFiniteTapeAllocatedRightShift.program nt)
    (fun _ => ULogFiniteTapeAllocatedRightShift.remaining nt nt le_rfl) (firstBit a) .stay)
    2 _ H _ = _
  rw [List.replicate_succ, ULogFiniteTapeMovingSymbolDispatch.run_dispatch_cons,
    shift_moved, FiniteOneTapeSemantics.moveHead, hp]
  rfl

theorem writer_second_start {nt : Nat} (a : Fin nt) (left suffix : List (Fin 3)) :
    ULogFiniteTapeStageComposition.secondStart (shift_states_ge nt) (2 : Fin 3) .stay
      (ULogTernaryOneHotBlockWriter.final a left suffix) =
      ULogFiniteTapeMovingSymbolDispatch.initial (firstBit a) left
        ((ULogTernaryOneHotBlockWriter.bits a).drop 1 ++ suffix) := by
  change ULogFiniteTapeStageComposition.secondStart (shift_states_ge nt) (2 : Fin 3) .stay
    (fromCells 0 left (ULogTernaryOneHotBlockWriter.bits a ++ suffix)) = _
  rw [bits_cons a]
  simp [ULogFiniteTapeStageComposition.secondStart, applyBounded, fromCells,
    ULogFiniteTapeMovingSymbolDispatch.initial]
  rfl

theorem combined_run {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int) :
    run (combinedProgram hnt a) 2 (List.replicate (3 * nt + 1) false) H
      (ULogFiniteTapeStageComposition.leftConfig
        (ULogTernaryOneHotBlockWriter.initial hnt a left suffix)) =
      some (H + (nt : Int), ULogFiniteTapeStageComposition.rightConfig
        (ULogFiniteTapeStageComposition.rightConfig (ns := 3)
          (ULogFiniteTapeAllocatedRightShift.final nt left
            (ULogTernaryOneHotBlockWriter.bits a) suffix))) := by
  have hs := ULogFiniteTapeStageComposition.sequential_run
    (ULogTernaryOneHotBlockWriter.program nt hnt) (shiftProgram a)
    (writer_states_ge hnt) (shift_states_ge nt) .stay (2 : Fin 3)
    (List.replicate (ULogTernaryOneHotBlockWriter.deadline nt) false)
    (List.replicate (nt + 1) false) H H (H + (nt : Int))
    (ULogTernaryOneHotBlockWriter.initial hnt a left suffix)
    (ULogTernaryOneHotBlockWriter.final a left suffix)
    (ULogFiniteTapeStageComposition.rightConfig (ns := 3)
      (ULogFiniteTapeAllocatedRightShift.final nt left
        (ULogTernaryOneHotBlockWriter.bits a) suffix))
    (ULogTernaryOneHotBlockWriter.writer_run hnt a left suffix H)
    (ULogTernaryOneHotBlockWriter.final_state a left suffix)
    (by
      change run (shiftProgram a) 2 _ H _ = _
      rw [writer_second_start]
      exact shift_run a left suffix hne H)
  have ht : 3 * nt + 1 = ULogTernaryOneHotBlockWriter.deadline nt + 1 + (nt + 1) := by
    unfold ULogTernaryOneHotBlockWriter.deadline; omega
  have hw : List.replicate (3 * nt + 1) false =
      List.replicate (ULogTernaryOneHotBlockWriter.deadline nt) false ++ false ::
        List.replicate (nt + 1) false := by rw [ht]; simp [List.replicate_add, List.append_assoc]
  rw [hw]
  exact hs

theorem writer_moved {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) :
    ULogFiniteTapeMovingSymbolDispatch.moved (fun _ => combinedEntry hnt a)
      (cell flag) (2 : Fin 3) .right 2 under (List.replicate nt 0 ++ suffix) =
      ULogFiniteTapeStageComposition.leftConfig
        (ULogTernaryOneHotBlockWriter.initial hnt a (cell flag :: under) suffix) := by
  obtain ⟨k, rfl⟩ : ∃ k, nt = k + 1 := ⟨nt - 1, by omega⟩
  simp [ULogFiniteTapeMovingSymbolDispatch.moved, applyBounded,
    ULogFiniteTapeStageComposition.leftConfig, ULogTernaryOneHotBlockWriter.initial,
    combinedEntry, fromCells, List.replicate_succ]
  rfl

theorem actual_run {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int) :
    run (program hnt a flag) 2 (List.replicate (deadline nt) false) H
      (initial nt under suffix) = some (H + ((nt + 1 : Nat) : Int), final a flag under suffix) := by
  change run (ULogFiniteTapeMovingSymbolDispatch.program (combinedProgram hnt a)
    (fun _ => combinedEntry hnt a) (cell flag) .right) 2 _ H
    (ULogFiniteTapeMovingSymbolDispatch.initial 2 under (List.replicate nt 0 ++ suffix)) = _
  have hw : List.replicate (deadline nt) false = false :: List.replicate (3 * nt + 1) false := by
    unfold deadline; rw [show 3 * nt + 2 = (3 * nt + 1) + 1 by omega, List.replicate_succ]
  rw [hw, ULogFiniteTapeMovingSymbolDispatch.run_dispatch_cons, writer_moved,
    FiniteOneTapeSemantics.moveHead, combined_run hnt a (cell flag :: under) suffix hne (H + 1)]
  cases suffix with
  | nil => contradiction
  | cons s rest =>
      simp [final, ULogFiniteTapeAllocatedRightShift.final, fromCells,
        ULogFiniteTapeStageComposition.rightConfig, ULogFiniteTapeStageComposition.rightState,
        Int.natCast_add, Int.natCast_one, add_assoc, add_comm, add_left_comm]
      rfl

theorem final_state {nt : Nat} (a : Fin nt) (flag : Bool) (under suffix : List (Fin 3)) :
    (final a flag under suffix).state.val = 0 := by simp [final, fromCells_state]

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool) :
    FalseOnly (program hnt a flag) := by
  apply ULogFiniteTapeMovingSymbolDispatch.program_falseOnly
  apply ULogFiniteTapeStageCompositionRuns.program_falseOnly
  · exact ULogTernaryOneHotBlockWriter.program_falseOnly hnt
  · exact ULogFiniteTapeMovingSymbolDispatch.program_falseOnly _ _ _ _
      (ULogFiniteTapeAllocatedRightShift.program_falseOnly nt)

def occupied (nt : Nat) (under suffix : List (Fin 3)) := under.length + nt + 1 + suffix.length

theorem occupied_initial (nt : Nat) (under suffix : List (Fin 3)) :
    cellCount (initial nt under suffix) = occupied nt under suffix := by
  simp [initial, ULogFiniteTapeMovingSymbolDispatch.initial, cellCount, occupied]; omega

theorem occupied_final {nt : Nat} (a : Fin nt) (flag : Bool) (under suffix : List (Fin 3))
    (hne : suffix ≠ []) : cellCount (final a flag under suffix) = occupied nt under suffix := by
  rw [final, ULogTernaryOneHotBlockWriter.cellCount_of_cells _ _ _ hne]
  simp [occupied, bits_length]; omega

theorem combined_raw_head {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (combinedStates nt) 3}
    (hw : run (combinedProgram hnt a) 2 w H
      (ULogFiniteTapeStageComposition.leftConfig
        (ULogTernaryOneHotBlockWriter.initial hnt a left suffix)) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + (nt : Int) := by
  rcases ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryOneHotBlockWriter.program nt hnt) (shiftProgram a)
    (writer_states_ge hnt) (shift_states_ge nt) .stay (2 : Fin 3)
    (ULogTernaryOneHotBlockWriter.program_falseOnly hnt)
    (ULogTernaryOneHotBlockWriter.deadline nt) H H
    (ULogTernaryOneHotBlockWriter.initial hnt a left suffix)
    (ULogTernaryOneHotBlockWriter.final a left suffix)
    (ULogTernaryOneHotBlockWriter.writer_run hnt a left suffix H)
    (ULogTernaryOneHotBlockWriter.final_state a left suffix) w hf zf hw with hfirst | hsecond
  · obtain ⟨_, zp, hp, _⟩ := hfirst
    have h := ULogTernaryOneHotBlockWriter.every_raw hnt a left suffix H hp
    exact ⟨h.2.2.1, by have := h.2.2.2.1; omega⟩
  · obtain ⟨v, zq, _, hq, _⟩ := hsecond
    rw [writer_second_start] at hq
    change run (ULogFiniteTapeMovingSymbolDispatch.program
      (ULogFiniteTapeAllocatedRightShift.program nt)
      (fun _ => ULogFiniteTapeAllocatedRightShift.remaining nt nt le_rfl) (firstBit a) .stay)
      2 v H (ULogFiniteTapeMovingSymbolDispatch.initial (firstBit a) left
        ((ULogTernaryOneHotBlockWriter.bits a).drop 1 ++ suffix)) = some (hf, zq) at hq
    rcases (ULogFiniteTapeMovingSymbolDispatch.every_raw_run_splits
      (ULogFiniteTapeAllocatedRightShift.program nt)
      (fun _ => ULogFiniteTapeAllocatedRightShift.remaining nt nt le_rfl) (firstBit a)
      (2 : Fin 3) .stay (firstBit a) left
      ((ULogTernaryOneHotBlockWriter.bits a).drop 1 ++ suffix) H hf v zq).1 hq with
      ⟨_, rfl, _⟩ | ⟨rest, out, _, hp, _⟩
    · exact ⟨le_refl _, by omega⟩
    · rw [shift_moved] at hp
      simp only [FiniteOneTapeSemantics.moveHead] at hp
      have h := ULogFiniteTapeAllocatedRightShift.every_raw nt left
        (ULogTernaryOneHotBlockWriter.bits a) suffix (bits_length a) hne H hf rest out hp
      exact ⟨by have := h.2.2; omega, by have := h.2.2; have := h.2.1; omega⟩

theorem raw_head {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt a flag) 2 w H (initial nt under suffix) = some (hf, zf)) :
    H ≤ hf ∧ hf ≤ H + ((nt + 1 : Nat) : Int) := by
  rcases (ULogFiniteTapeMovingSymbolDispatch.every_raw_run_splits (combinedProgram hnt a)
    (fun _ => combinedEntry hnt a) (cell flag) (2 : Fin 3) .right 2 under
    (List.replicate nt 0 ++ suffix) H hf w zf).1 hw with
    ⟨_, rfl, _⟩ | ⟨rest, out, _, hp, _⟩
  · exact ⟨le_refl _, by omega⟩
  · rw [writer_moved] at hp
    simp only [FiniteOneTapeSemantics.moveHead] at hp
    have h := combined_raw_head hnt a (cell flag :: under) suffix hne (H + 1) hp
    exact ⟨by omega, by omega⟩

theorem every_raw {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt a flag) 2 w H (initial nt under suffix) = some (hf, zf)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt ∧
      H ≤ hf ∧ hf ≤ H + ((nt + 1 : Nat) : Int) ∧
      cellCount zf = occupied nt under suffix ∧
      GrowthRun (program hnt a flag) 2 w H (initial nt under suffix) hf zf 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt a flag) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt a flag)
    (deadline nt) H (initial nt under suffix) (final a flag under suffix) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt a flag under suffix hne H) (final_state a flag under suffix) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt a flag) 2 _ _ _ _ _
    (actual_run hnt a flag under suffix hne H)
  have hfinal := occupied_final a flag under suffix hne
  have hi := occupied_initial nt under suffix
  have he := hg.exact_ledger
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt a flag) 2 w H hf _ zf hw
  have hsplit : List.replicate (deadline nt) false =
      w ++ List.replicate (deadline nt - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [hsplit] at hg
  have hle := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have hledger := hg1.exact_ledger
  have hc : cellCount zf = occupied nt under suffix := by omega
  have hh := raw_head hnt a flag under suffix hne H hw
  exact ⟨hfalse, hlen, hh.1, hh.2, hc, by simpa [hl1, hr1] using hg1⟩

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program hnt a flag) 2 w H (initial nt under suffix) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt) false ∧ hf = H + ((nt + 1 : Nat) : Int) ∧
      zf = final a flag under suffix :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt a flag)
    (deadline nt) H (initial nt under suffix) (final a flag under suffix) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt a flag under suffix hne H) (final_state a flag under suffix) hw ha

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig (program hnt a flag) (initial nt under suffix)) =
      if deadline nt ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt a flag)
    (deadline nt) H (initial nt under suffix) (final a flag under suffix) (H + ((nt + 1 : Nat) : Int))
    (actual_run hnt a flag under suffix hne H) (final_state a flag under suffix) T

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool) :
    ∀ r ∈ compile (program hnt a flag), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt a flag) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem write_advance_spec {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (flag : Bool)
    (under suffix : List (Fin 3)) (hne : suffix ≠ []) (H : Int) :
    (run (program hnt a flag) 2 (List.replicate (deadline nt) false) H
      (initial nt under suffix) = some (H + ((nt + 1 : Nat) : Int), final a flag under suffix)) ∧
    (∀ w hf zf, run (program hnt a flag) 2 w H (initial nt under suffix) = some (hf, zf) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt ∧
        H ≤ hf ∧ hf ≤ H + ((nt + 1 : Nat) : Int) ∧
        cellCount zf = occupied nt under suffix ∧
        GrowthRun (program hnt a flag) 2 w H (initial nt under suffix) hf zf 0 0) ∧
    (∀ w hf zf, run (program hnt a flag) 2 w H (initial nt under suffix) = some (hf, zf) →
      zf.state.val = 0 → w = List.replicate (deadline nt) false ∧
        hf = H + ((nt + 1 : Nat) : Int) ∧ zf = final a flag under suffix) ∧
    (∀ r ∈ compile (program hnt a flag), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt a flag) (initial nt under suffix)) =
        if deadline nt ≤ T then 1 else 0) :=
  ⟨actual_run hnt a flag under suffix hne H,
    fun _ _ _ => every_raw hnt a flag under suffix hne H,
    fun _ _ _ => accepting_word hnt a flag under suffix hne H,
    compiled_symbols hnt a flag, cutoff_counts hnt a flag under suffix hne H⟩

end PakFixedPolyomino.ULogTernaryOneHotWriteAdvance
