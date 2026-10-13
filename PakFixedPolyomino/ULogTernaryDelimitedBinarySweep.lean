import PakFixedPolyomino.ULogTernaryBlankBlockInsertion

/-! Actual four-state traversal of a binary encoded window between its two
ternary delimiters. The reverse traversal is literal reflection. The end
markers and every bit survive; all raw words and their physical growth are
covered. This traversal has no parameter depending on the window length. -/
namespace PakFixedPolyomino.ULogTernaryDelimitedBinarySweep
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryCountedSourceDelimiter (fromCells fromCells_state)

def program : BoundedProgram 4 3 where
  rule q read slot :=
    if slot then none
    else if q = 2 then
      if read = 2 then some ⟨2, 3, .right⟩ else none
    else if q = 3 then
      if read = 2 then some ⟨2, 0, .stay⟩ else some ⟨read, 3, .right⟩
    else none

def initial (source : List Bool) (under buffer : List (Fin 3)) : BoundedConfig 4 3 :=
  ⟨2, under, 2, cells source ++ 2 :: buffer⟩

def final (source : List Bool) (under buffer : List (Fin 3)) : BoundedConfig 4 3 :=
  ⟨0, (cells source).reverse ++ 2 :: under, 2, buffer⟩

def deadline (source : List Bool) := source.length + 2

theorem sweep (source : List Bool) (left buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (source.length + 1) false) H
      (fromCells (3 : Fin 4) left (cells source ++ 2 :: buffer)) =
      some (H + (source.length : Int),
        (⟨0, (cells source).reverse ++ left, 2, buffer⟩ : BoundedConfig 4 3)) := by
  induction source generalizing left H with
  | nil => simp [cells, fromCells, List.replicate_succ, run, program,
      boundedHalted, applyBounded, FiniteOneTapeSemantics.moveHead]
  | cons b source ih =>
      have hp := ih (cell b :: left) (H + 1)
      change run program 2 (false :: List.replicate (source.length + 1) false) H
        (⟨3, left, cell b, cells source ++ 2 :: buffer⟩ : BoundedConfig 4 3) = _
      have hn : cells source ++ 2 :: buffer ≠ [] := by simp
      cases hc : cells source ++ 2 :: buffer with
      | nil => exact (hn hc).elim
      | cons a rest =>
          rw [hc] at hp
          have hz : boundedHalted
              (⟨3, left, cell b, a :: rest⟩ : BoundedConfig 4 3) = false := rfl
          have hq : program.rule (3 : Fin 4) (cell b) false =
              some (⟨cell b, 3, .right⟩ : BoundedAction 4 3) := by
            cases b <;> rfl
          rw [run, hz, hq]
          change run program 2 (List.replicate (source.length + 1) false) (H + 1)
            (fromCells (3 : Fin 4) (cell b :: left) (a :: rest)) = _
          simpa only [cells, List.map_cons, List.length_cons, List.reverse_cons,
            List.cons_append, List.append_assoc, List.singleton_append, List.nil_append,
            Int.natCast_add, Int.natCast_one, add_assoc, add_comm, add_left_comm] using hp

theorem actual_run (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (deadline source) false) H (initial source under buffer) =
      some (H + ((source.length + 1 : Nat) : Int), final source under buffer) := by
  have step : applyBounded (2 : Fin 3) (initial source under buffer)
      (⟨2, 3, .right⟩ : BoundedAction 4 3) =
      fromCells 3 (2 :: under) (cells source ++ 2 :: buffer) := by
    cases source with
    | nil => simp [initial, cells, applyBounded, fromCells]
    | cons b source => simp [initial, cells, applyBounded, fromCells]
  change run program 2 (false :: List.replicate (source.length + 1) false) H
    (initial source under buffer) = _
  simp only [run, initial, boundedHalted, program, Fin.isValue,
    Bool.false_eq_true, ↓reduceIte, Fin.reduceEq]
  change run program 2 (List.replicate (source.length + 1) false) (H + 1)
    (applyBounded (2 : Fin 3) (initial source under buffer) ⟨2, 3, .right⟩) = _
  rw [step, sweep]
  simp [final, Int.natCast_add, Int.natCast_one, add_assoc, add_comm, add_left_comm]

theorem program_falseOnly : FalseOnly program := by intro q read; simp [program]
theorem final_accepts (source : List Bool) (under buffer : List (Fin 3)) :
    (final source under buffer).state.val = 0 := rfl

def occupied (source : List Bool) (under buffer : List (Fin 3)) :=
  under.length + source.length + 2 + buffer.length

theorem initial_cells (source : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial source under buffer) = occupied source under buffer := by
  simp [cellCount, initial, occupied, cells]; omega

theorem final_cells (source : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final source under buffer) = occupied source under buffer := by
  simp [cellCount, final, occupied, cells]; omega

theorem every_raw (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 4 3}
    (hw : run program 2 w H (initial source under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline source ∧
      cellCount out = occupied source under buffer ∧
      GrowthRun program 2 w H (initial source under buffer) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ program_falseOnly hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ program_falseOnly
    (deadline source) H (initial source under buffer) (final source under buffer)
    (H + ((source.length + 1 : Nat) : Int))
    (actual_run source under buffer H) (final_accepts source under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run program 2 _ _ _ _ _ (actual_run source under buffer H)
  have ledger := hg.exact_ledger
  have hi := initial_cells source under buffer
  have ho := final_cells source under buffer
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run program 2 w H hf _ out hw
  have word : List.replicate (deadline source) false =
      w ++ List.replicate (deadline source - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [word] at hg
  have le := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger1 := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [hl1, hr1] using hg1⟩

theorem accepting_word (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 4 3}
    (hw : run program 2 w H (initial source under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline source) false ∧ hf = H + ((source.length + 1 : Nat) : Int) ∧
      out = final source under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ program_falseOnly (deadline source) H
    (initial source under buffer) (final source under buffer) (H + ((source.length + 1 : Nat) : Int))
    (actual_run source under buffer H) (final_accepts source under buffer) hw ha

theorem cutoff_counts (source : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig program (initial source under buffer)) =
      if deadline source ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ program_falseOnly (deadline source) H
    (initial source under buffer) (final source under buffer) (H + ((source.length + 1 : Nat) : Int))
    (actual_run source under buffer H) (final_accepts source under buffer) T

def leftProgram : BoundedProgram 4 3 := ULogFiniteTapeReflection.program program
def leftInitial (source : List Bool) (under buffer : List (Fin 3)) : BoundedConfig 4 3 :=
  ULogFiniteTapeReflection.reflectConfig (initial source under buffer)
def leftFinal (source : List Bool) (under buffer : List (Fin 3)) : BoundedConfig 4 3 :=
  ULogFiniteTapeReflection.reflectConfig (final source under buffer)

theorem left_run (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run leftProgram 2 (List.replicate (deadline source) false) H (leftInitial source under buffer) =
      some (H - ((source.length + 1 : Nat) : Int), leftFinal source under buffer) := by
  have h := ULogFiniteTapeReflection.run_reflect program (2 : Fin 3)
    (List.replicate (deadline source) false) (-H) (initial source under buffer)
  rw [actual_run source under buffer (-H)] at h
  simpa [leftProgram, leftInitial, leftFinal, sub_eq_add_neg, add_comm] using h

theorem left_falseOnly : FalseOnly leftProgram :=
  ULogFiniteTapeReflection.program_falseOnly _ program_falseOnly

theorem left_final_accepts (source : List Bool) (under buffer : List (Fin 3)) :
    (leftFinal source under buffer).state.val = 0 := rfl

theorem left_every_raw (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 4 3}
    (hw : run leftProgram 2 w H (leftInitial source under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline source ∧
      cellCount out = occupied source under buffer ∧
      GrowthRun leftProgram 2 w H (leftInitial source under buffer) hf out 0 0 := by
  have h := (ULogFiniteTapeReflection.every_raw_inverse program (2 : Fin 3) w H hf
    (leftInitial source under buffer) out).1 hw
  rw [leftInitial, ULogFiniteTapeReflection.config_involutive] at h
  have hr := every_raw source under buffer (-H) h
  have hc : cellCount out = occupied source under buffer := by
    simpa only [ULogFiniteTapeReflection.cellCount_reflect] using hr.2.2.1
  obtain ⟨lg, rg, hg⟩ := every_actual_run leftProgram 2 w H hf _ out hw
  have ledger := hg.exact_ledger
  have hi : cellCount (leftInitial source under buffer) = occupied source under buffer := by
    simpa only [leftInitial, ULogFiniteTapeReflection.cellCount_reflect] using
      initial_cells source under buffer
  have hl : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  exact ⟨hr.1, hr.2.1, hc, by simpa only [hl, hrg] using hg⟩


theorem left_accepting_word (source : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 4 3}
    (hw : run leftProgram 2 w H (leftInitial source under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline source) false ∧ hf = H - ((source.length + 1 : Nat) : Int) ∧
      out = leftFinal source under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ left_falseOnly (deadline source) H
    (leftInitial source under buffer) (leftFinal source under buffer) (H - ((source.length + 1 : Nat) : Int))
    (left_run source under buffer H) (left_final_accepts source under buffer) hw ha

theorem left_cutoff_counts (source : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig leftProgram (leftInitial source under buffer)) =
      if deadline source ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ left_falseOnly (deadline source) H
    (leftInitial source under buffer) (leftFinal source under buffer) (H - ((source.length + 1 : Nat) : Int))
    (left_run source under buffer H) (left_final_accepts source under buffer) T

theorem delimited_binary_sweep_spec (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (run program 2 (List.replicate (deadline source) false) H (initial source under buffer) =
      some (H + ((source.length + 1 : Nat) : Int), final source under buffer)) ∧
    (∀ w hf out, run program 2 w H (initial source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline source ∧
      cellCount out = occupied source under buffer ∧
      GrowthRun program 2 w H (initial source under buffer) hf out 0 0) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig program (initial source under buffer)) =
      if deadline source ≤ T then 1 else 0) ∧
    (run leftProgram 2 (List.replicate (deadline source) false) H (leftInitial source under buffer) =
      some (H - ((source.length + 1 : Nat) : Int), leftFinal source under buffer)) ∧
    (∀ w hf out, run leftProgram 2 w H (leftInitial source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline source ∧
      cellCount out = occupied source under buffer ∧
      GrowthRun leftProgram 2 w H (leftInitial source under buffer) hf out 0 0) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig leftProgram (leftInitial source under buffer)) =
      if deadline source ≤ T then 1 else 0) :=
  ⟨actual_run source under buffer H, fun _ _ _ => every_raw source under buffer H,
    cutoff_counts source under buffer H, left_run source under buffer H,
    fun _ _ _ => left_every_raw source under buffer H, left_cutoff_counts source under buffer H⟩

end PakFixedPolyomino.ULogTernaryDelimitedBinarySweep
