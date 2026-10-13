import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter
import PakFixedPolyomino.ULogFiniteTapeZipperRun
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Literal finite ternary right-end seal. One BoundedProgram 7 3,
independent of source `bits` and reserve `N`. Allocates the first implicit
blank after compact zeros and returns SAMEH. Loader composition remains
separate. -/

namespace PakFixedPolyomino.ULogTernaryReserveEndSeal

open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter (fromCells bind_run)
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryOneHotBlockWriter
  (replicate_split replicate_add_run replicate_concat growth_append_le)
open FiniteOneTapeSemantics (moveHead)

def program : BoundedProgram 7 3 where
  rule q read slot :=
    if slot then none
    else if q.val = 2 then
      if read = 2 then some ⟨2, 3, .right⟩ else none
    else if q.val = 3 then
      if read = 2 then some ⟨2, 4, .right⟩ else some ⟨read, 3, .right⟩
    else if q.val = 4 then
      if read = 0 then some ⟨0, 4, .right⟩
      else if read = 2 then some ⟨2, 5, .left⟩ else none
    else if q.val = 5 then
      if read = 0 then some ⟨0, 5, .left⟩
      else if read = 2 then some ⟨2, 6, .left⟩ else none
    else if q.val = 6 then
      if read = 2 then some ⟨2, 0, .stay⟩ else some ⟨read, 6, .left⟩
    else none

def srcRight (bits : List Bool) (N : Nat) : List (Fin 3) :=
  cells bits ++ 2 :: List.replicate N 0
def sealedRight (bits : List Bool) (N : Nat) : List (Fin 3) :=
  cells bits ++ 2 :: (List.replicate N 0 ++ [2])
def initial (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    BoundedConfig 7 3 := ⟨2, under, 2, srcRight bits N⟩
def final (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    BoundedConfig 7 3 := ⟨0, under, 2, sealedRight bits N⟩
def deadline (n N : Nat) : Nat := 2 * n + 2 * N + 5
def q3Scan (pref rest : List Bool) (under : List (Fin 3)) (N : Nat) :
    BoundedConfig 7 3 :=
  fromCells 3 ((cells pref).reverse ++ 2 :: under) (srcRight rest N)
def q4Scan (bits : List Bool) (under : List (Fin 3)) (done remain : Nat) :
    BoundedConfig 7 3 :=
  fromCells 4 (List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (List.replicate remain 0)
def q5Rev (remain done : Nat) (bits : List Bool) (under : List (Fin 3)) :
    BoundedConfig 7 3 :=
  match remain with
  | 0 => ⟨5, (cells bits).reverse ++ 2 :: under, 2, List.replicate done 0 ++ [2]⟩
  | n + 1 => ⟨5, List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under,
      0, List.replicate done 0 ++ [2]⟩
def q6Rev (near passed : List Bool) (under : List (Fin 3)) (N : Nat) :
    BoundedConfig 7 3 :=
  match near with
  | [] => ⟨6, under, 2, cells passed ++ 2 :: (List.replicate N 0 ++ [2])⟩
  | b :: rest => ⟨6, cells rest ++ 2 :: under, cell b,
      cells passed ++ 2 :: (List.replicate N 0 ++ [2])⟩

theorem program_falseOnly : FalseOnly program := by
  intro q read; simp [program]
theorem rule_q2 : program.rule 2 2 false = some ⟨2, 3, .right⟩ := by
  simp [program]
theorem rule_q3_bit (b : Bool) :
    program.rule 3 (cell b) false = some ⟨cell b, 3, .right⟩ := by
  cases b <;> simp [program, cell]
theorem rule_q3_end : program.rule 3 2 false = some ⟨2, 4, .right⟩ := by
  simp [program]
theorem rule_q4_zero : program.rule 4 0 false = some ⟨0, 4, .right⟩ := by
  simp [program]
theorem rule_q4_end : program.rule 4 2 false = some ⟨2, 5, .left⟩ := by
  simp [program]
theorem rule_q5_zero : program.rule 5 0 false = some ⟨0, 5, .left⟩ := by
  simp [program]
theorem rule_q5_end : program.rule 5 2 false = some ⟨2, 6, .left⟩ := by
  simp [program]
theorem rule_q6_bit (b : Bool) :
    program.rule 6 (cell b) false = some ⟨cell b, 6, .left⟩ := by
  cases b <;> simp [program, cell]
theorem rule_q6_end : program.rule 6 2 false = some ⟨2, 0, .stay⟩ := by
  simp [program]
theorem not_halt {q : Fin 7} (h : 2 ≤ q.val) (left : List (Fin 3))
    (foc : Fin 3) (rest : List (Fin 3)) :
    boundedHalted (⟨q, left, foc, rest⟩ : BoundedConfig 7 3) = false := by
  simp [boundedHalted]; omega
theorem run_one (z : BoundedConfig 7 3) (H : Int) {a : BoundedAction 7 3}
    (hnh : boundedHalted z = false)
    (hr : program.rule z.state z.focus false = some a) :
    run program 2 [false] H z =
      some (moveHead a.move H, applyBounded (2 : Fin 3) z a) := by
  simp [run, hnh, hr]
theorem cons_false (n : Nat) :
    List.replicate (n + 1) false = [false] ++ List.replicate n false := by
  simp [List.replicate_succ]
theorem cells_reverse (bits : List Bool) :
    (cells bits).reverse = cells bits.reverse := by
  simp [cells, List.map_reverse]

theorem step_start (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (initial bits under N) =
      some (H + 1, q3Scan [] bits under N) := by
  have hz : initial bits under N = ⟨2, under, 2, srcRight bits N⟩ := rfl
  have hnh := not_halt (q := (2 : Fin 7)) (by decide) under (2 : Fin 3)
    (srcRight bits N)
  rw [hz, run_one _ H hnh (by simpa using rule_q2)]
  cases hs : srcRight bits N with
  | nil => simp [srcRight, cells] at hs
  | cons a rest => simp [applyBounded, moveHead, q3Scan, fromCells, cells, hs]
theorem q3_step (pref : List Bool) (b : Bool) (rest : List Bool)
    (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (q3Scan pref (b :: rest) under N) =
      some (H + 1, q3Scan (pref ++ [b]) rest under N) := by
  have hz : q3Scan pref (b :: rest) under N =
      ⟨3, (cells pref).reverse ++ 2 :: under, cell b, srcRight rest N⟩ := by
    simp [q3Scan, fromCells, srcRight, cells]
  have hnh := not_halt (q := (3 : Fin 7)) (by decide)
    ((cells pref).reverse ++ 2 :: under) (cell b) (srcRight rest N)
  rw [hz, run_one _ H hnh (by simpa using rule_q3_bit b)]
  cases hs : srcRight rest N with
  | nil => simp [srcRight, cells] at hs
  | cons a tl =>
      simp [applyBounded, moveHead, q3Scan, fromCells, cells, List.reverse_append]
      rw [hs]
theorem q3_scan (pref rest : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    run program 2 (List.replicate rest.length false) H
      (q3Scan pref rest under N) =
      some (H + (rest.length : Int), q3Scan (pref ++ rest) [] under N) := by
  induction rest generalizing pref H with
  | nil => simp [run, List.append_nil]
  | cons b rest ih =>
      simp only [List.length_cons]
      rw [cons_false, run_append, q3_step, bind_run, ih]
      refine congrArg some (Prod.ext ?_ ?_)
      · simp; omega
      · simp [List.append_assoc]
theorem q3_end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (q3Scan bits [] under N) =
      some (H + 1, q4Scan bits under 0 N) := by
  have hz : q3Scan bits [] under N =
      ⟨3, (cells bits).reverse ++ 2 :: under, 2, List.replicate N 0⟩ := by
    simp [q3Scan, fromCells, srcRight, cells]
  have hnh := not_halt (q := (3 : Fin 7)) (by decide)
    ((cells bits).reverse ++ 2 :: under) (2 : Fin 3) (List.replicate N 0)
  rw [hz, run_one _ H hnh (by simpa using rule_q3_end)]
  cases N with
  | zero => simp [applyBounded, moveHead, q4Scan, fromCells]
  | succ n => simp [applyBounded, moveHead, q4Scan, fromCells, List.replicate_succ]
theorem q4_step (bits : List Bool) (under : List (Fin 3)) (done remain : Nat)
    (H : Int) :
    run program 2 [false] H (q4Scan bits under done (remain + 1)) =
      some (H + 1, q4Scan bits under (done + 1) remain) := by
  have hz : q4Scan bits under done (remain + 1) =
      ⟨4, List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under,
        0, List.replicate remain 0⟩ := by
    simp [q4Scan, fromCells, List.replicate_succ]
  have hnh := not_halt (q := (4 : Fin 7)) (by decide)
    (List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (0 : Fin 3) (List.replicate remain 0)
  rw [hz, run_one _ H hnh (by simpa using rule_q4_zero)]
  cases remain with
  | zero => simp [applyBounded, moveHead, q4Scan, fromCells, List.replicate_succ]
  | succ n => simp [applyBounded, moveHead, q4Scan, fromCells, List.replicate_succ]
theorem q4_scan (bits : List Bool) (under : List (Fin 3)) (done remain : Nat)
    (H : Int) :
    run program 2 (List.replicate remain false) H
      (q4Scan bits under done remain) =
      some (H + (remain : Int), q4Scan bits under (done + remain) 0) := by
  induction remain generalizing done H with
  | zero => simp [run]
  | succ remain ih =>
      rw [cons_false, run_append, q4_step, bind_run, ih]
      refine congrArg some (Prod.ext (by omega)
        (congrArg (fun k => q4Scan bits under k 0) (by omega)))
theorem q4_end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (q4Scan bits under N 0) =
      some (H - 1, q5Rev N 0 bits under) := by
  have hz : q4Scan bits under N 0 =
      ⟨4, List.replicate N 0 ++ 2 :: (cells bits).reverse ++ 2 :: under, 2, []⟩ :=
    by simp [q4Scan, fromCells]
  have hnh := not_halt (q := (4 : Fin 7)) (by decide)
    (List.replicate N 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (2 : Fin 3) []
  rw [hz, run_one _ H hnh (by simpa using rule_q4_end)]
  cases N with
  | zero => simp [applyBounded, moveHead, q5Rev]
  | succ n => simp [applyBounded, moveHead, q5Rev, List.replicate_succ]
theorem q5_step (n done : Nat) (bits : List Bool) (under : List (Fin 3))
    (H : Int) :
    run program 2 [false] H (q5Rev (n + 1) done bits under) =
      some (H - 1, q5Rev n (done + 1) bits under) := by
  have hz : q5Rev (n + 1) done bits under =
      ⟨5, List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under,
        0, List.replicate done 0 ++ [2]⟩ := rfl
  have hnh := not_halt (q := (5 : Fin 7)) (by decide)
    (List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (0 : Fin 3) (List.replicate done 0 ++ [2])
  rw [hz, run_one _ H hnh (by simpa using rule_q5_zero)]
  cases n with
  | zero => simp [applyBounded, moveHead, q5Rev, List.replicate_succ]
  | succ n => simp [applyBounded, moveHead, q5Rev, List.replicate_succ]
theorem q5_scan (n done : Nat) (bits : List Bool) (under : List (Fin 3))
    (H : Int) :
    run program 2 (List.replicate n false) H (q5Rev n done bits under) =
      some (H - (n : Int), q5Rev 0 (done + n) bits under) := by
  induction n generalizing done H with
  | zero => simp [run]
  | succ n ih =>
      rw [cons_false, run_append, q5_step, bind_run, ih]
      refine congrArg some (Prod.ext (by omega)
        (congrArg (fun k => q5Rev 0 k bits under) (by omega)))
theorem q5_end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (q5Rev 0 N bits under) =
      some (H - 1, q6Rev bits.reverse [] under N) := by
  have hz : q5Rev 0 N bits under =
      ⟨5, (cells bits).reverse ++ 2 :: under, 2, List.replicate N 0 ++ [2]⟩ :=
    rfl
  have hnh := not_halt (q := (5 : Fin 7)) (by decide)
    ((cells bits).reverse ++ 2 :: under) (2 : Fin 3)
    (List.replicate N 0 ++ [2])
  rw [hz, run_one _ H hnh (by simpa using rule_q5_end)]
  cases hrev : bits.reverse with
  | nil =>
      have hb : bits = [] := List.reverse_eq_nil_iff.mp hrev
      subst hb
      simp [applyBounded, moveHead, q6Rev, cells]
  | cons b rest =>
      have hcells : (cells bits).reverse = cell b :: cells rest := by
        rw [cells_reverse, hrev]; rfl
      rw [hcells]
      simp [applyBounded, moveHead, q6Rev, cells]
theorem q6_step (b : Bool) (rest passed : List Bool) (under : List (Fin 3))
    (N : Nat) (H : Int) :
    run program 2 [false] H (q6Rev (b :: rest) passed under N) =
      some (H - 1, q6Rev rest (b :: passed) under N) := by
  have hz : q6Rev (b :: rest) passed under N =
      ⟨6, cells rest ++ 2 :: under, cell b,
        cells passed ++ 2 :: (List.replicate N 0 ++ [2])⟩ := rfl
  have hnh := not_halt (q := (6 : Fin 7)) (by decide)
    (cells rest ++ 2 :: under) (cell b)
    (cells passed ++ 2 :: (List.replicate N 0 ++ [2]))
  rw [hz, run_one _ H hnh (by simpa using rule_q6_bit b)]
  cases rest with
  | nil => simp [applyBounded, moveHead, q6Rev, cells]
  | cons c rest => simp [applyBounded, moveHead, q6Rev, cells]
theorem q6_scan (near passed : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    run program 2 (List.replicate near.length false) H
      (q6Rev near passed under N) =
      some (H - (near.length : Int),
        q6Rev [] (near.reverse ++ passed) under N) := by
  induction near generalizing passed H with
  | nil => simp [run]
  | cons b rest ih =>
      simp only [List.length_cons]
      rw [cons_false, run_append, q6_step, bind_run, ih]
      refine congrArg some (Prod.ext ?_ ?_)
      · simp; omega
      · simp [List.reverse_cons, List.append_assoc]
theorem q6_stay (passed : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 [false] H (q6Rev [] passed under N) =
      some (H, final passed under N) := by
  have hz : q6Rev [] passed under N =
      ⟨6, under, 2, cells passed ++ 2 :: (List.replicate N 0 ++ [2])⟩ := rfl
  have hnh := not_halt (q := (6 : Fin 7)) (by decide) under (2 : Fin 3)
    (cells passed ++ 2 :: (List.replicate N 0 ++ [2]))
  rw [hz, run_one _ H hnh (by simpa using rule_q6_end)]
  simp [applyBounded, moveHead, final, sealedRight]

theorem to_q3end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 1) false) H
      (initial bits under N) =
      some (H + ((bits.length + 1 : Nat) : Int), q3Scan bits [] under N) := by
  rw [cons_false, run_append, step_start, bind_run, q3_scan]
  exact congrArg some (Prod.ext (by omega) (by simp))
theorem to_q4start (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 2) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int), q4Scan bits under 0 N) := by
  have : bits.length + 2 = bits.length + 1 + 1 := by omega
  rw [this, replicate_concat, run_append, to_q3end, bind_run, q3_end]
  exact congrArg some (Prod.ext (by omega) rfl)
theorem to_q4end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 2 + N) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int) + (N : Int),
        q4Scan bits under N 0) := by
  exact replicate_add_run program 2 (bits.length + 2) N H (initial bits under N)
    (to_q4start bits under N H)
    (by simpa using q4_scan bits under 0 N (H + ((bits.length + 2 : Nat) : Int)))
theorem to_q5start (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 2 + N + 1) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1,
        q5Rev N 0 bits under) := by
  rw [replicate_concat, run_append, to_q4end, bind_run, q4_end]
theorem to_q5end (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 2 + N + 1 + N) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1 - (N : Int),
        q5Rev 0 N bits under) := by
  have h := q5_scan N 0 bits under
    (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1)
  exact replicate_add_run program 2 (bits.length + 2 + N + 1) N H
    (initial bits under N) (to_q5start bits under N H) (by simpa using h)
theorem to_q6start (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2 (List.replicate (bits.length + 2 + N + 1 + N + 1) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1 - (N : Int) - 1,
        q6Rev bits.reverse [] under N) := by
  rw [replicate_concat, run_append, to_q5end, bind_run, q5_end]
theorem to_q6mark (bits : List Bool) (under : List (Fin 3)) (N : Nat) (H : Int) :
    run program 2
      (List.replicate (bits.length + 2 + N + 1 + N + 1 + bits.length) false) H
      (initial bits under N) =
      some (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1 - (N : Int) - 1 -
          (bits.length : Int), q6Rev [] bits under N) := by
  have h := q6_scan bits.reverse [] under N
    (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1 - (N : Int) - 1)
  exact replicate_add_run program 2 (bits.length + 2 + N + 1 + N + 1) bits.length H
    (initial bits under N) (to_q6start bits under N H)
    (by simpa [List.reverse_reverse, List.length_reverse] using h)
theorem actual_run (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    run program 2 (List.replicate (deadline bits.length N) false) H
      (initial bits under N) = some (H, final bits under N) := by
  have hlen : deadline bits.length N =
      bits.length + 2 + N + 1 + N + 1 + bits.length + 1 := by
    simp [deadline]; omega
  have hH : H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1 - (N : Int) - 1 -
      (bits.length : Int) = H := by omega
  rw [hlen, replicate_concat, run_append, to_q6mark, bind_run, hH, q6_stay]

theorem final_accepts (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    (final bits under N).state.val = 0 := rfl
theorem final_tape (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    (final bits under N).leftRev = under ∧
      (final bits under N).focus = 2 ∧
      (final bits under N).right = sealedRight bits N :=
  ⟨rfl, rfl, rfl⟩
theorem initial_cells (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    cellCount (initial bits under N) = under.length + bits.length + N + 2 := by
  simp [initial, cellCount, srcRight, cells]; omega
theorem final_cells (bits : List Bool) (under : List (Fin 3)) (N : Nat) :
    cellCount (final bits under N) = under.length + bits.length + N + 3 := by
  simp [final, cellCount, sealedRight, cells]; omega
theorem initial_left (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    leftEdge H (initial bits under N) = H - under.length := by
  simp [leftEdge, initial]
theorem final_left (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    leftEdge H (final bits under N) = H - under.length := by
  simp [leftEdge, final]
theorem initial_right (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    rightEdge H (initial bits under N) = H + (bits.length + N + 1 : Nat) := by
  simp [rightEdge, initial, srcRight, cells]; omega
theorem final_right (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    rightEdge H (final bits under N) = H + (bits.length + N + 2 : Nat) := by
  simp [rightEdge, final, sealedRight, cells]; omega

theorem actual_growth (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) :
    GrowthRun program 2 (List.replicate (deadline bits.length N) false) H
      (initial bits under N) H (final bits under N) 0 1 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run program 2
    (List.replicate (deadline bits.length N) false) H H
    (initial bits under N) (final bits under N) (actual_run bits under N H)
  have L := hg.exact_ledger
  have hlg : lg = 0 := by
    have := initial_left bits under N H
    have := final_left bits under N H
    omega
  have hrg : rg = 1 := by
    have := initial_right bits under N H
    have := final_right bits under N H
    omega
  simpa [hlg, hrg] using hg

theorem every_raw (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) {w : List Bool} {hf : Int} {out : BoundedConfig 7 3}
    (hw : run program 2 w H (initial bits under N) = some (hf, out)) :
    w = List.replicate w.length false ∧
      w.length ≤ deadline bits.length N ∧
      (∃ rg, rg ≤ 1 ∧
        GrowthRun program 2 w H (initial bits under N) hf out 0 rg) ∧
      cellCount out ≤ cellCount (initial bits under N) + 1 ∧
      leftEdge H (initial bits under N) ≤ leftEdge hf out ∧
      rightEdge hf out ≤ rightEdge H (initial bits under N) + 1 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) program program_falseOnly hw
  have hlen := successful_zipper_length_le (2 : Fin 3) program program_falseOnly
    (deadline bits.length N) H (initial bits under N) (final bits under N) H
    (actual_run bits under N H) (final_accepts bits under N) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run program 2
    (List.replicate (deadline bits.length N) false) H H
    (initial bits under N) (final bits under N) (actual_run bits under N H)
  have ledger := hg.exact_ledger
  have hlg : lg = 0 := by
    have := initial_left bits under N H
    have := final_left bits under N H
    omega
  have hrg : rg = 1 := by
    have := initial_right bits under N H
    have := final_right bits under N H
    omega
  obtain ⟨lg1, rg1, hg1⟩ :=
    every_actual_run program 2 w H hf (initial bits under N) out hw
  have word : List.replicate (deadline bits.length N) false =
      w ++ List.replicate (deadline bits.length N - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using replicate_split _ _ hlen
  rw [word] at hg
  have le := growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 ≤ 1 := by omega
  have ledger1 := hg1.exact_ledger
  refine ⟨hfalse, hlen, ⟨rg1, hr1, by simpa [hl1] using hg1⟩, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem accepting_word (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) {w : List Bool} {hf : Int} {out : BoundedConfig 7 3}
    (hw : run program 2 w H (initial bits under N) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline bits.length N) false ∧ hf = H ∧
      out = final bits under N :=
  accepting_zipper_word_eq (2 : Fin 3) program program_falseOnly
    (deadline bits.length N) H (initial bits under N) (final bits under N) H
    (actual_run bits under N H) (final_accepts bits under N) hw ha

theorem compiled_symbols :
    ∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded program hr
  exact ⟨hb.2.1, hb.2.2.1⟩

theorem cutoff_counts (bits : List Bool) (under : List (Fin 3)) (N : Nat)
    (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig program (initial bits under N)) =
      if deadline bits.length N ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl program program_falseOnly
    (deadline bits.length N) H (initial bits under N) (final bits under N) H
    (actual_run bits under N H) (final_accepts bits under N) T

theorem reserve_end_seal_spec (bits : List Bool) (under : List (Fin 3))
    (N : Nat) (H : Int) :
    (run program 2 (List.replicate (deadline bits.length N) false) H
      (initial bits under N) = some (H, final bits under N)) ∧
    (final bits under N).leftRev = under ∧
      (final bits under N).focus = 2 ∧
      (final bits under N).right = sealedRight bits N ∧
    GrowthRun program 2 (List.replicate (deadline bits.length N) false) H
      (initial bits under N) H (final bits under N) 0 1 ∧
    (∀ w hf out, run program 2 w H (initial bits under N) = some (hf, out) →
      w = List.replicate w.length false ∧
        w.length ≤ deadline bits.length N ∧
        (∃ rg, rg ≤ 1 ∧
          GrowthRun program 2 w H (initial bits under N) hf out 0 rg) ∧
        cellCount out ≤ cellCount (initial bits under N) + 1 ∧
        leftEdge H (initial bits under N) ≤ leftEdge hf out ∧
        rightEdge hf out ≤ rightEdge H (initial bits under N) + 1) ∧
    (∀ w hf out, run program 2 w H (initial bits under N) = some (hf, out) →
      out.state.val = 0 →
      w = List.replicate (deadline bits.length N) false ∧ hf = H ∧
        out = final bits under N) ∧
    (∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig program (initial bits under N)) =
        if deadline bits.length N ≤ T then 1 else 0) :=
  ⟨actual_run bits under N H, (final_tape bits under N).1,
    (final_tape bits under N).2.1, (final_tape bits under N).2.2,
    actual_growth bits under N H, fun _ _ _ => every_raw bits under N H,
    fun _ _ _ => accepting_word bits under N H, compiled_symbols,
    cutoff_counts bits under N H⟩

end PakFixedPolyomino.ULogTernaryReserveEndSeal
