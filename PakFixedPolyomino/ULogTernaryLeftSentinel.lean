import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Three literal ternary bytecode ticks replace one existing left cell
with the delimiter2 and return to the same source focus. The saved source
focus/right cells and every deeper left cell are unchanged. The caller
must establish that this existing cell belongs to its disposable header;
this lemma does not provide a whole physical loader. -/

namespace PakFixedPolyomino.ULogTernaryLeftSentinel

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger

def program : BoundedProgram 5 3 where
  rule q read slot :=
    if slot then none else
    match q.val with
    | 2 => some ⟨read, 3, .left⟩
    | 3 => some ⟨2, 4, .right⟩
    | 4 => some ⟨read, 0, .stay⟩
    | _ => none

def initial (a focus : Fin 3) (under right : List (Fin 3)) : BoundedConfig 5 3 :=
  ⟨2, a :: under, focus, right⟩

def final (focus : Fin 3) (under right : List (Fin 3)) : BoundedConfig 5 3 :=
  ⟨0, 2 :: under, focus, right⟩

theorem program_falseOnly : FalseOnly program := by
  intro q read
  rfl

theorem actual_run (a focus : Fin 3) (under right : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate 3 false) H (initial a focus under right) =
      some (H, final focus under right) := by
  simp [run, program, initial, final, applyBounded, boundedHalted,
    FiniteOneTapeSemantics.moveHead, List.replicate_succ]

theorem prefix_zero (a focus : Fin 3) (under right : List (Fin 3)) (H : Int) :
    run program 2 [] H (initial a focus under right) =
      some (H, initial a focus under right) := rfl

theorem prefix_one (a focus : Fin 3) (under right : List (Fin 3)) (H : Int) :
    run program 2 [false] H (initial a focus under right) =
      some (H - 1, (⟨3, under, a, focus :: right⟩ : BoundedConfig 5 3)) := by
  simp [run, program, initial, applyBounded, boundedHalted, FiniteOneTapeSemantics.moveHead]

theorem prefix_two (a focus : Fin 3) (under right : List (Fin 3)) (H : Int) :
    run program 2 [false, false] H (initial a focus under right) =
      some (H, (⟨4, 2 :: under, focus, right⟩ : BoundedConfig 5 3)) := by
  simp [run, program, initial, applyBounded, boundedHalted, FiniteOneTapeSemantics.moveHead]

theorem every_raw (a focus : Fin 3) (under right : List (Fin 3)) (H : Int)
    (w : List Bool) (hf : Int) (out : BoundedConfig 5 3)
    (hw : run program 2 w H (initial a focus under right) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ 3 ∧
      H - 1 ≤ hf ∧ hf ≤ H ∧ cellCount out = under.length + right.length + 2 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) program program_falseOnly hw
  have hlen := successful_zipper_length_le (2 : Fin 3) program program_falseOnly
    3 H (initial a focus under right) (final focus under right) H
    (actual_run a focus under right H) rfl hw
  refine ⟨hfalse, hlen, ?_⟩
  rw [hfalse] at hw
  interval_cases h : w.length <;>
    simp [h, run, program, initial, final, applyBounded, boundedHalted,
      FiniteOneTapeSemantics.moveHead, List.replicate_succ] at hw <;>
    rcases hw with ⟨rfl, rfl⟩ <;> simp [cellCount] <;> omega

theorem every_raw_no_growth (a focus : Fin 3) (under right : List (Fin 3)) (H : Int)
    (w : List Bool) (hf : Int) (out : BoundedConfig 5 3)
    (hw : run program 2 w H (initial a focus under right) = some (hf, out)) :
    GrowthRun program 2 w H (initial a focus under right) hf out 0 0 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run program 2 w H hf _ out hw
  have hc := (every_raw a focus under right H w hf out hw).2.2.2.2
  have he := hg.exact_ledger.2.2.1
  have hi : cellCount (initial a focus under right) = under.length + right.length + 2 := by
    simp [cellCount, initial]
    omega
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg

theorem accepting_word (a focus : Fin 3) (under right : List (Fin 3)) (H : Int)
    (w : List Bool) (hf : Int) (out : BoundedConfig 5 3)
    (hw : run program 2 w H (initial a focus under right) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate 3 false ∧ hf = H ∧ out = final focus under right :=
  accepting_zipper_word_eq (2 : Fin 3) program program_falseOnly 3 H
    (initial a focus under right) (final focus under right) H
    (actual_run a focus under right H) rfl hw ha

theorem sentinel_spec (a focus : Fin 3) (under right : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate 3 false) H (initial a focus under right) =
      some (H, final focus under right) ∧
    (∀ w hf out, run program 2 w H (initial a focus under right) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ 3 ∧
      H - 1 ≤ hf ∧ hf ≤ H ∧ cellCount out = under.length + right.length + 2 ∧
      GrowthRun program 2 w H (initial a focus under right) hf out 0 0) ∧
    (∀ w hf out, run program 2 w H (initial a focus under right) = some (hf, out) →
      out.state.val = 0 → w = List.replicate 3 false ∧ hf = H ∧ out = final focus under right) := by
  refine ⟨actual_run a focus under right H, ?_, accepting_word a focus under right H⟩
  intro w hf out hw
  have h := every_raw a focus under right H w hf out hw
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    every_raw_no_growth a focus under right H w hf out hw⟩

end PakFixedPolyomino.ULogTernaryLeftSentinel
