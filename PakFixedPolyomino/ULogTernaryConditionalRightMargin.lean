import PakFixedPolyomino.ULogTernaryRightBlankInsertion

/-! An actual internal branch on the original unary source length. Empty
input keeps its already created head blank; nonempty input gets one extra
right blank. The finite controller does not depend on the length counter. -/
namespace PakFixedPolyomino.ULogTernaryConditionalRightMargin
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger ULogFiniteTapeStageComposition
open ULogTernaryRetainedCounterPump (cell cells)

abbrev states (nt : Nat) := stateCount 6 (ULogTernaryRightBlankInsertion.states nt)
theorem child_states_ge (nt : Nat) : 3 ≤ ULogTernaryRightBlankInsertion.states nt := by
  unfold ULogTernaryRightBlankInsertion.states stateCount; omega

def program {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (states nt) 3 where
  rule q read slot := if slot then none else
    if q.val = 2 ∧ read.val = 2 then some ⟨2, ⟨3, by unfold states stateCount; omega⟩, .left⟩
    else if q.val = 3 ∧ read.val = 1 then some ⟨1, ⟨4, by unfold states stateCount; omega⟩, .right⟩
    else if q.val = 3 ∧ read.val = 2 then some ⟨2, ⟨5, by unfold states stateCount; omega⟩, .right⟩
    else if q.val = 4 ∧ read.val = 2 then some ⟨2, rightState (ns := 6) ⟨2, by have := child_states_ge nt; omega⟩, .stay⟩
    else if q.val = 5 ∧ read.val = 2 then some ⟨2, ⟨0, by unfold states stateCount; omega⟩, .stay⟩
    else if h : 8 ≤ q.val ∧ q.val < 6 + ULogTernaryRightBlankInsertion.states nt then
      ((ULogTernaryRightBlankInsertion.pairProgram hnt blank).rule
        ⟨q.val - 6, by omega⟩ read false).map (rightAction (ns := 6))
    else none

def counter (n : Nat) (under : List (Fin 3)) := List.replicate n (1 : Fin 3) ++ 2 :: under
def initial (nt n : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig (states nt) 3 :=
  ⟨⟨2, by unfold states stateCount; omega⟩, counter n under, 2,
    cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer⟩
def final {nt : Nat} (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) : BoundedConfig (states nt) 3 :=
  if n = 0 then
    ⟨⟨0, by unfold states stateCount; omega⟩, counter n under, 2,
      cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer⟩
  else rightConfig (ns := 6)
    (ULogTernaryRightBlankInsertion.final blank source (counter n under) buffer)
def deadline (nt n s : Nat) := if n = 0 then 3 else 3 + ULogTernaryRightBlankInsertion.deadline nt s

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (program hnt blank) := by intro q read; simp [program]

theorem rule_right {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (z : BoundedConfig (ULogTernaryRightBlankInsertion.states nt) 3) (slot : Bool)
    (live : boundedHalted z = false) :
    (program hnt blank).rule (rightState (ns := 6) z.state) z.focus slot =
      ((ULogTernaryRightBlankInsertion.pairProgram hnt blank).rule z.state z.focus slot).map
        (rightAction (ns := 6)) := by
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using live
    omega
  have hz := z.state.isLt
  cases slot with
  | true =>
      simp only [program, ↓reduceIte]
      rw [ULogTernaryRightBlankInsertion.program_falseOnly hnt blank z.state z.focus]
      rfl
  | false => simp [program, rightState, show ¬ z.state.val < 2 by omega,
      show 6 + z.state.val ≠ 2 by omega, show 6 + z.state.val ≠ 3 by omega,
      show 6 + z.state.val ≠ 4 by omega, show 6 + z.state.val ≠ 5 by omega,
      show 8 ≤ 6 + z.state.val by omega, show 6 + z.state.val < 6 + ULogTernaryRightBlankInsertion.states nt by omega]

theorem run_right_map {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (w : List Bool) (H : Int) (z : BoundedConfig (ULogTernaryRightBlankInsertion.states nt) 3) :
    run (program hnt blank) 2 w H (rightConfig (ns := 6) z) =
      (run (ULogTernaryRightBlankInsertion.pairProgram hnt blank) 2 w H z).map
        (fun hz => (hz.1, rightConfig (ns := 6) hz.2)) := by
  induction w generalizing H z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, ULogFiniteTapeStageCompositionRuns.right_halted, hh]
      | false =>
          cases hr : (ULogTernaryRightBlankInsertion.pairProgram hnt blank).rule z.state z.focus slot with
          | none =>
              simp only [run, ULogFiniteTapeStageCompositionRuns.right_halted, hh,
                Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState (ns := 6) z.state by rfl,
                show (rightConfig (ns := 6) z).focus = z.focus by rfl, rule_right hnt blank z slot hh, hr]
              rfl
          | some a =>
              simp only [run, ULogFiniteTapeStageCompositionRuns.right_halted, hh,
                Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState (ns := 6) z.state by rfl,
                show (rightConfig (ns := 6) z).focus = z.focus by rfl, rule_right hnt blank z slot hh, hr]
              change run (program hnt blank) 2 rest (FiniteOneTapeSemantics.moveHead a.move H)
                (applyBounded (2 : Fin 3) (rightConfig z) (rightAction (ns := 6) a)) = _
              rw [apply_right]
              exact ih _ _

theorem empty_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt blank) 2 (List.replicate 3 false) H (initial nt 0 source under buffer) =
      some (H, final blank 0 source under buffer) := by
  simp [run, program, initial, final, counter, applyBounded, boundedHalted,
    FiniteOneTapeSemantics.moveHead]

theorem nonempty_prefix {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt blank) 2 (List.replicate 3 false) H (initial nt (n + 1) source under buffer) =
      some (H, rightConfig (ns := 6)
        (ULogTernaryRightBlankInsertion.initial nt source (counter (n + 1) under) buffer)) := by
  simp [run, program, initial, counter, applyBounded, boundedHalted,
    FiniteOneTapeSemantics.moveHead, List.replicate_succ, rightConfig, rightState,
    ULogTernaryRightBlankInsertion.initial, ULogTernaryRightBlankInsertion.middleInitial,
    leftConfig, leftState, ULogTernaryDelimitedBinarySweep.initial]

theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run (program hnt blank) 2 (List.replicate (deadline nt n source.length) false)
      H (initial nt n source under buffer) = some (H, final blank n source under buffer) := by
  cases n with
  | zero => exact empty_run hnt blank source under buffer H
  | succ n =>
      simp only [deadline, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        List.replicate_add, run_append, nonempty_prefix hnt blank n source under buffer H,
        Option.bind_some]
      rw [run_right_map, ULogTernaryRightBlankInsertion.actual_run hnt blank source
        (counter (n + 1) under) buffer H]
      simp [final]

theorem final_accepts {nt : Nat} (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) : (final blank n source under buffer).state.val = 0 := by
  by_cases hn : n = 0
  · simp [final, hn]
  · simp only [final, hn, ↓reduceIte]
    exact (ULogFiniteTapeStageCompositionRuns.right_accepts_iff _).2
      (ULogTernaryRightBlankInsertion.final_accepts blank _ _ _)

theorem final_tape {nt : Nat} (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) :
    (final blank n source under buffer).leftRev = counter n under ∧
    (final blank n source under buffer).focus = 2 ∧
    (final blank n source under buffer).right =
      if n = 0 then cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer
      else cells (source ++ ULogTernaryBalancedBlankPair.block blank) ++ 2 :: buffer := by
  by_cases hn : n = 0
  · simp [final, hn]
  · simp only [final, hn, ↓reduceIte, rightConfig]
    exact ULogTernaryRightBlankInsertion.final_tape blank source (counter n under) buffer

theorem cells_unchanged {nt : Nat} (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) :
    cellCount (final blank n source under buffer) = cellCount (initial nt n source under buffer) := by
  by_cases hn : n = 0
  · simp [initial, final, hn, cellCount]
  · have ht := final_tape blank n source under buffer
    simp [cellCount, ht.1, ht.2.2, initial, hn, cells,
      ULogTernaryBalancedBlankPair.block_length]
    omega

theorem every_raw {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt n source under buffer) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline nt n source.length ∧
      cellCount out = cellCount (initial nt n source under buffer) ∧
      GrowthRun (program hnt blank) 2 w H (initial nt n source under buffer) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt blank) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt n source.length) H (initial nt n source under buffer) (final blank n source under buffer) H
    (actual_run hnt blank n source under buffer H) (final_accepts blank n source under buffer) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt blank) 2 _ _ _ _ _
    (actual_run hnt blank n source under buffer H)
  have ledger := hg.exact_ledger
  have hc := cells_unchanged blank n source under buffer
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt blank) 2 w H hf _ out hw
  have split : List.replicate (deadline nt n source.length) false =
      w ++ List.replicate (deadline nt n source.length - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [split] at hg
  have le := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger1 := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [hl1, hr1] using hg1⟩

theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial nt n source under buffer)) =
        if deadline nt n source.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt n source.length) H (initial nt n source under buffer) (final blank n source under buffer) H
    (actual_run hnt blank n source under buffer H) (final_accepts blank n source under buffer) T

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (n : Nat) (source : List Bool)
    (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt) 3}
    (hw : run (program hnt blank) 2 w H (initial nt n source under buffer) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt n source.length) false ∧ hf = H ∧
      out = final blank n source under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt n source.length) H (initial nt n source under buffer) (final blank n source under buffer) H
    (actual_run hnt blank n source under buffer H) (final_accepts blank n source under buffer) hw ha

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    ∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have h := compile_rule_bounded (program hnt blank) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem deadline_eq (nt n s : Nat) :
    deadline nt n s = if n = 0 then 3 else 2 * s + nt * nt + 9 * nt + 19 := by
  by_cases hn : n = 0 <;> simp [deadline, hn, ULogTernaryRightBlankInsertion.deadline_eq]
  omega

theorem conditional_right_margin_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (n : Nat) (source : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    (run (program hnt blank) 2 (List.replicate (deadline nt n source.length) false)
      H (initial nt n source under buffer) = some (H, final blank n source under buffer)) ∧
    (final blank n source under buffer).leftRev = counter n under ∧
    (final blank n source under buffer).focus = 2 ∧
    (final blank n source under buffer).right =
      (if n = 0 then cells source ++ 2 :: List.replicate (nt + 1) 0 ++ buffer
      else cells (source ++ ULogTernaryBalancedBlankPair.block blank) ++ 2 :: buffer) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt n source under buffer) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline nt n source.length ∧
        cellCount out = cellCount (initial nt n source under buffer) ∧
        GrowthRun (program hnt blank) 2 w H (initial nt n source under buffer) hf out 0 0) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial nt n source under buffer) = some (hf, out) →
      out.state.val = 0 → w = List.replicate (deadline nt n source.length) false ∧ hf = H ∧
        out = final blank n source under buffer) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial nt n source under buffer)) =
        if deadline nt n source.length ≤ T then 1 else 0) ∧
    (∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3) ∧
    deadline nt n source.length =
      (if n = 0 then 3 else 2 * source.length + nt * nt + 9 * nt + 19) :=
  ⟨actual_run hnt blank n source under buffer H, (final_tape blank n source under buffer).1,
    (final_tape blank n source under buffer).2.1, (final_tape blank n source under buffer).2.2,
    fun _ _ _ => every_raw hnt blank n source under buffer H,
    fun _ _ _ => accepting_word hnt blank n source under buffer H,
    cutoff_counts hnt blank n source under buffer H, compiled_symbols hnt blank,
    deadline_eq nt n source.length⟩

end PakFixedPolyomino.ULogTernaryConditionalRightMargin
