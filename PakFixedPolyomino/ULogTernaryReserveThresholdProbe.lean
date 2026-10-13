import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter
import PakFixedPolyomino.ULogTernaryOriginalEmptyTest
import PakFixedPolyomino.ULogFiniteTapeZipperRun
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
/-! Literal finite ternary reserve threshold probe: BoundedProgram (K+8) 3, K>0. -/
namespace PakFixedPolyomino.ULogTernaryReserveThresholdProbe
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter (fromCells bind_run)
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryOneHotBlockWriter
  (replicate_split replicate_add_run replicate_concat growth_append_le)
open ULogTernaryOriginalEmptyTest (terminal_length_le terminal_word_eq rejecting_paths_zero)
open FiniteOneTapeSemantics (moveHead)
def S (K : Nat) (_hK : 0 < K) (n : Nat) (hn : n < K + 8 := by omega) : Fin (K + 8) := ⟨n, hn⟩
def Ctr (K : Nat) (j : Nat) (hj : j < K) : Fin (K + 8) := ⟨j + 8, by omega⟩
def program (K : Nat) (hK : 0 < K) : BoundedProgram (K + 8) 3 where
  rule q read slot :=
    if slot then none
    else if q.val = 2 then (if read = 2 then some ⟨2, S K hK 3, .right⟩ else none)
    else if q.val = 3 then
      if read = 2 then some ⟨2, Ctr K 0 hK, .right⟩ else some ⟨read, S K hK 3, .right⟩
    else if q.val = 4 then
      if read = 0 then some ⟨0, S K hK 4, .left⟩
      else if read = 2 then some ⟨2, S K hK 6, .left⟩ else none
    else if q.val = 5 then
      if read = 0 then some ⟨0, S K hK 5, .left⟩
      else if read = 2 then some ⟨2, S K hK 7, .left⟩ else none
    else if q.val = 6 then
      if read = 2 then some ⟨2, S K hK 0, .stay⟩ else some ⟨read, S K hK 6, .left⟩
    else if q.val = 7 then
      if read = 2 then some ⟨2, S K hK 1, .stay⟩ else some ⟨read, S K hK 7, .left⟩
    else if h8 : 8 ≤ q.val then
      if read = 0 then
        if hnext : q.val - 8 + 1 < K then some ⟨0, Ctr K (q.val - 8 + 1) hnext, .right⟩
        else some ⟨0, S K hK 4, .left⟩
      else if read = 2 then some ⟨2, S K hK 5, .left⟩ else none
    else none
def srcRight (bits : List Bool) (N : Nat) (buffer : List (Fin 3)) : List (Fin 3) :=
  cells bits ++ 2 :: List.replicate N 0 ++ 2 :: buffer
def initial (K : Nat) (hK : 0 < K) (bits : List Bool) (under buffer : List (Fin 3)) (N : Nat) :
    BoundedConfig (K + 8) 3 := ⟨S K hK 2, under, 2, srcRight bits N buffer⟩
def final (K : Nat) (hK : 0 < K) (bits : List Bool) (under buffer : List (Fin 3)) (N : Nat) :
    BoundedConfig (K + 8) 3 :=
  ⟨if K ≤ N then S K hK 0 else S K hK 1, under, 2, srcRight bits N buffer⟩
def deadline (n K N : Nat) : Nat := if K ≤ N then 2 * n + 2 * K + 3 else 2 * n + 2 * N + 5
def q3Scan (K : Nat) (hK : 0 < K) (pref rest : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) : BoundedConfig (K + 8) 3 :=
  fromCells (S K hK 3) ((cells pref).reverse ++ 2 :: under) (srcRight rest N buffer)
def ctrScan (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < K) (done remain : Nat)
    (bits : List Bool) (under buffer : List (Fin 3)) : BoundedConfig (K + 8) 3 :=
  fromCells (Ctr K j hj)
    (List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (List.replicate remain 0 ++ 2 :: buffer)
def leftRev (K : Nat) (q : Nat) (hq : q < K + 8) (remain done : Nat)
    (bits : List Bool) (under buffer : List (Fin 3)) : BoundedConfig (K + 8) 3 :=
  match remain with
  | 0 => ⟨⟨q, hq⟩, (cells bits).reverse ++ 2 :: under, 2, List.replicate done 0 ++ 2 :: buffer⟩
  | n + 1 => ⟨⟨q, hq⟩, List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under,
      0, List.replicate done 0 ++ 2 :: buffer⟩
def retRev (K : Nat) (q : Nat) (hq : q < K + 8)
    (near passed : List Bool) (under buffer : List (Fin 3)) (N : Nat) :
    BoundedConfig (K + 8) 3 :=
  match near with
  | [] => ⟨⟨q, hq⟩, under, 2, srcRight passed N buffer⟩
  | b :: rest => ⟨⟨q, hq⟩, cells rest ++ 2 :: under, cell b, srcRight passed N buffer⟩
theorem program_falseOnly (K : Nat) (hK : 0 < K) : FalseOnly (program K hK) :=
  fun _ _ => by simp [program]
theorem rule_q2 (K : Nat) (hK : 0 < K) :
    (program K hK).rule (S K hK 2) 2 false = some ⟨2, S K hK 3, .right⟩ := by simp [program, S]
theorem rule_q3_bit (K : Nat) (hK : 0 < K) (b : Bool) :
    (program K hK).rule (S K hK 3) (cell b) false = some ⟨cell b, S K hK 3, .right⟩ := by
  cases b <;> simp [program, S, cell]
theorem rule_q3_end (K : Nat) (hK : 0 < K) :
    (program K hK).rule (S K hK 3) 2 false = some ⟨2, Ctr K 0 hK, .right⟩ := by simp [program, S, Ctr]
theorem rule_ctr_next (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < K) (hjs : j + 1 < K) :
    (program K hK).rule (Ctr K j hj) 0 false = some ⟨0, Ctr K (j + 1) hjs, .right⟩ := by
  simp [program, Ctr, hjs]
theorem rule_ctr_last (K : Nat) (hK : 0 < K) :
    (program K hK).rule (Ctr K (K - 1) (Nat.sub_lt hK (by decide))) 0 false =
      some ⟨0, S K hK 4, .left⟩ := by simp [program, Ctr, S]; omega
theorem rule_ctr_seal (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < K) :
    (program K hK).rule (Ctr K j hj) 2 false = some ⟨2, S K hK 5, .left⟩ := by simp [program, Ctr, S]
theorem not_halt {K : Nat} {q : Fin (K + 8)} (h : 2 ≤ q.val) (left : List (Fin 3))
    (foc : Fin 3) (rest : List (Fin 3)) :
    boundedHalted (⟨q, left, foc, rest⟩ : BoundedConfig (K + 8) 3) = false := by
  simp [boundedHalted]; omega
theorem run_one {K : Nat} (hK : 0 < K) (z : BoundedConfig (K + 8) 3) (H : Int)
    {a : BoundedAction (K + 8) 3} (hnh : boundedHalted z = false)
    (hr : (program K hK).rule z.state z.focus false = some a) :
    run (program K hK) 2 [false] H z = some (moveHead a.move H, applyBounded (2 : Fin 3) z a) := by
  simp [run, hnh, hr]
theorem cons_false (n : Nat) :
    List.replicate (n + 1) false = [false] ++ List.replicate n false := by simp [List.replicate_succ]
theorem cells_reverse (bits : List Bool) :
    (cells bits).reverse = cells bits.reverse := by simp [cells, List.map_reverse]
theorem step_start (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 [false] H (initial K hK bits under buffer N) =
      some (H + 1, q3Scan K hK [] bits under buffer N) := by
  have hz : initial K hK bits under buffer N =
      ⟨S K hK 2, under, 2, srcRight bits N buffer⟩ := rfl
  have hnh := not_halt (q := S K hK 2) (by simp [S]) under (2 : Fin 3) (srcRight bits N buffer)
  rw [hz, run_one hK _ H hnh (by simpa using rule_q2 K hK)]
  cases hs : srcRight bits N buffer with
  | nil => simp [srcRight, cells] at hs
  | cons a rest => simp [applyBounded, moveHead, q3Scan, fromCells, cells, hs]
theorem q3_step (K : Nat) (hK : 0 < K) (pref : List Bool) (b : Bool)
    (rest : List Bool) (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 [false] H (q3Scan K hK pref (b :: rest) under buffer N) =
      some (H + 1, q3Scan K hK (pref ++ [b]) rest under buffer N) := by
  have hz : q3Scan K hK pref (b :: rest) under buffer N =
      ⟨S K hK 3, (cells pref).reverse ++ 2 :: under, cell b, srcRight rest N buffer⟩ := by
    simp [q3Scan, fromCells, srcRight, cells, S]
  have hnh := not_halt (q := S K hK 3) (by simp [S])
    ((cells pref).reverse ++ 2 :: under) (cell b) (srcRight rest N buffer)
  rw [hz, run_one hK _ H hnh (by simpa using rule_q3_bit K hK b)]
  cases hs : srcRight rest N buffer with
  | nil => simp [srcRight, cells] at hs
  | cons a tl =>
      simp [applyBounded, moveHead, q3Scan, fromCells, cells, List.reverse_append]; rw [hs]
theorem q3_scan (K : Nat) (hK : 0 < K) (pref rest : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 (List.replicate rest.length false) H
      (q3Scan K hK pref rest under buffer N) =
      some (H + (rest.length : Int), q3Scan K hK (pref ++ rest) [] under buffer N) := by
  induction rest generalizing pref H with
  | nil => simp [run, List.append_nil]
  | cons b rest ih =>
      simp only [List.length_cons]; rw [cons_false, run_append, q3_step, bind_run, ih]
      exact congrArg some (Prod.ext (by omega) (by simp [List.append_assoc]))
theorem q3_end (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 [false] H (q3Scan K hK bits [] under buffer N) =
      some (H + 1, ctrScan K hK 0 hK 0 N bits under buffer) := by
  have hz : q3Scan K hK bits [] under buffer N =
      ⟨S K hK 3, (cells bits).reverse ++ 2 :: under, 2, List.replicate N 0 ++ 2 :: buffer⟩ := by
    simp [q3Scan, fromCells, srcRight, cells, S]
  have hnh := not_halt (q := S K hK 3) (by simp [S])
    ((cells bits).reverse ++ 2 :: under) (2 : Fin 3) (List.replicate N 0 ++ 2 :: buffer)
  rw [hz, run_one hK _ H hnh (by simpa using rule_q3_end K hK)]
  cases N <;> simp [applyBounded, moveHead, ctrScan, fromCells, Ctr, S, List.replicate_succ]
theorem to_ctr (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 (List.replicate (bits.length + 2) false) H
      (initial K hK bits under buffer N) =
      some (H + ((bits.length + 2 : Nat) : Int), ctrScan K hK 0 hK 0 N bits under buffer) := by
  have : bits.length + 2 = bits.length + 1 + 1 := by omega
  rw [this, replicate_concat, cons_false, List.append_assoc, run_append, step_start,
    bind_run, run_append, q3_scan, bind_run, q3_end]
  exact congrArg some (Prod.ext (by omega) (by simp))
theorem ctr_next (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < K) (hjs : j + 1 < K)
    (done remain : Nat) (bits : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program K hK) 2 [false] H
      (ctrScan K hK j hj done (remain + 1) bits under buffer) =
      some (H + 1, ctrScan K hK (j + 1) hjs (done + 1) remain bits under buffer) := by
  have hz : ctrScan K hK j hj done (remain + 1) bits under buffer =
      ⟨Ctr K j hj, List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under, 0,
        List.replicate remain 0 ++ 2 :: buffer⟩ := by simp [ctrScan, fromCells, List.replicate_succ]
  have hnh := not_halt (q := Ctr K j hj) (by simp [Ctr])
    (List.replicate done 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (0 : Fin 3) (List.replicate remain 0 ++ 2 :: buffer)
  rw [hz, run_one hK _ H hnh (by simpa using rule_ctr_next K hK j hj hjs)]
  cases remain <;>
    simp [applyBounded, moveHead, ctrScan, fromCells, List.replicate_succ, List.cons_append]
theorem ctr_rights (K : Nat) (hK : 0 < K) (N : Nat) (j : Nat) (hj : j < K)
    (hjn : j ≤ N) (bits : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program K hK) 2 (List.replicate j false) H
      (ctrScan K hK 0 hK 0 N bits under buffer) =
      some (H + (j : Int), ctrScan K hK j hj j (N - j) bits under buffer) := by
  induction j with
  | zero => simp [run]
  | succ j ih =>
      have hj' : j < K := Nat.lt_of_succ_lt hj
      have hjn' : j ≤ N := Nat.le_of_succ_le hjn
      have hrem : N - j - 1 + 1 = N - j := by omega
      rw [replicate_concat, run_append, ih hj' hjn', bind_run]
      have hstep := ctr_next K hK j hj' hj j (N - j - 1) bits under buffer (H + (j : Int))
      rw [hrem] at hstep
      rw [hstep]
      exact congrArg some (Prod.ext (by omega) (by
        have : N - j - 1 = N - (j + 1) := by omega
        simp [this]))
theorem ctr_last_enough (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (hKN : K ≤ N) (H : Int) :
    run (program K hK) 2 [false] H
      (ctrScan K hK (K - 1) (Nat.sub_lt hK (by decide)) (K - 1) (N - (K - 1))
        bits under buffer) =
      some (H - 1, leftRev K 4 (by omega) (K - 1) (N - (K - 1)) bits under buffer) := by
  have hrem : N - (K - 1) = (N - (K - 1) - 1) + 1 := by omega
  have hz :
      ctrScan K hK (K - 1) (Nat.sub_lt hK (by decide)) (K - 1) (N - (K - 1))
        bits under buffer =
        ⟨Ctr K (K - 1) (Nat.sub_lt hK (by decide)),
          List.replicate (K - 1) 0 ++ 2 :: (cells bits).reverse ++ 2 :: under, 0,
          List.replicate (N - (K - 1) - 1) 0 ++ 2 :: buffer⟩ := by
    rw [hrem]; simp [ctrScan, fromCells, List.replicate_succ]
  have hnh := not_halt (q := Ctr K (K - 1) (Nat.sub_lt hK (by decide))) (by simp [Ctr])
    (List.replicate (K - 1) 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (0 : Fin 3) (List.replicate (N - (K - 1) - 1) 0 ++ 2 :: buffer)
  rw [hz, run_one hK _ H hnh (by simpa using rule_ctr_last K hK)]
  by_cases h1 : K = 1
  · subst h1
    simp [applyBounded, moveHead, leftRev, S]
    have hN : N = N - 1 + 1 := by omega
    conv_rhs => rw [hN, List.replicate_succ]
    simp [List.cons_append]
  · have hk : K - 1 = Nat.succ (K - 2) := by omega
    have hrep' : List.replicate (K - 1) (0 : Fin 3) =
        (0 : Fin 3) :: List.replicate (K - 2) (0 : Fin 3) := by rw [hk, List.replicate_succ]
    rw [hrep']; simp [List.cons_append, applyBounded, moveHead]; rw [hk]
    simp [leftRev, S, List.append_assoc, List.cons_append]
    have hdone : N - Nat.succ (K - 2) = N - Nat.succ (K - 2) - 1 + 1 := by omega
    conv_rhs => rw [hdone, List.replicate_succ]
    simp [List.cons_append]
theorem ctr_seal (K : Nat) (hK : 0 < K) (j : Nat) (hj : j < K)
    (bits : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run (program K hK) 2 [false] H (ctrScan K hK j hj j 0 bits under buffer) =
      some (H - 1, leftRev K 5 (by omega) j 0 bits under buffer) := by
  have hz : ctrScan K hK j hj j 0 bits under buffer =
      ⟨Ctr K j hj, List.replicate j 0 ++ 2 :: (cells bits).reverse ++ 2 :: under, 2, buffer⟩ := by
    simp [ctrScan, fromCells, Ctr]
  have hnh := not_halt (q := Ctr K j hj) (by simp [Ctr])
    (List.replicate j 0 ++ 2 :: (cells bits).reverse ++ 2 :: under) (2 : Fin 3) buffer
  rw [hz, run_one hK _ H hnh (by simpa using rule_ctr_seal K hK j hj)]
  cases j <;> simp [applyBounded, moveHead, leftRev, S, List.replicate_succ, List.cons_append]
theorem left_zero (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 4 ∨ q = 5)
    (n done : Nat) (bits : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 [false] H (leftRev K q hlt (n + 1) done bits under buffer) =
      some (H - 1, leftRev K q hlt n (done + 1) bits under buffer) := by
  have hz : leftRev K q hlt (n + 1) done bits under buffer =
      ⟨⟨q, hlt⟩, List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under, 0,
        List.replicate done 0 ++ 2 :: buffer⟩ := rfl
  have hnh := not_halt (q := ⟨q, hlt⟩) (by rcases hq with rfl | rfl <;> simp)
    (List.replicate n 0 ++ 2 :: (cells bits).reverse ++ 2 :: under)
    (0 : Fin 3) (List.replicate done 0 ++ 2 :: buffer)
  have hr : (program K hK).rule ⟨q, hlt⟩ 0 false = some ⟨0, ⟨q, hlt⟩, .left⟩ := by
    rcases hq with rfl | rfl <;> simp [program, S]
  rw [hz, run_one hK _ H hnh hr]
  cases n <;> simp [applyBounded, moveHead, leftRev, List.replicate_succ]
theorem left_scan (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 4 ∨ q = 5)
    (n done : Nat) (bits : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 (List.replicate n false) H (leftRev K q hlt n done bits under buffer) =
      some (H - (n : Int), leftRev K q hlt 0 (done + n) bits under buffer) := by
  induction n generalizing done H with
  | zero => simp [run]
  | succ n ih =>
      rw [cons_false, run_append, left_zero K hK q hq n done bits under buffer H, bind_run, ih]
      exact congrArg some (Prod.ext (by omega)
        (congrArg (fun k => leftRev K q hlt 0 k bits under buffer) (by omega)))
theorem left_end (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 4 ∨ q = 5)
    (done : Nat) (bits : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 [false] H (leftRev K q hlt 0 done bits under buffer) =
      some (H - 1, retRev K (q + 2) (by rcases hq with rfl | rfl <;> omega)
        bits.reverse [] under buffer done) := by
  have hz : leftRev K q hlt 0 done bits under buffer =
      ⟨⟨q, hlt⟩, (cells bits).reverse ++ 2 :: under, 2, List.replicate done 0 ++ 2 :: buffer⟩ := rfl
  have hnh := not_halt (q := ⟨q, hlt⟩) (by rcases hq with rfl | rfl <;> simp)
    ((cells bits).reverse ++ 2 :: under) (2 : Fin 3) (List.replicate done 0 ++ 2 :: buffer)
  have hr : (program K hK).rule ⟨q, hlt⟩ 2 false =
      some ⟨2, S K hK (q + 2) (by rcases hq with rfl | rfl <;> omega), .left⟩ := by
    rcases hq with rfl | rfl <;> simp [program, S]
  rw [hz, run_one hK _ H hnh hr]
  cases hrev : bits.reverse with
  | nil =>
      have hb : bits = [] := List.reverse_eq_nil_iff.mp hrev
      subst hb
      simp [applyBounded, moveHead, retRev, cells, srcRight, S]
  | cons b rest =>
      have hcells : (cells bits).reverse = cell b :: cells rest := by
        rw [cells_reverse, hrev]; rfl
      simp [cells] at hcells
      simp [hcells, applyBounded, moveHead, retRev, cells, srcRight, S]
theorem ret_bit (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 6 ∨ q = 7)
    (b : Bool) (rest passed : List Bool) (under buffer : List (Fin 3))
    (N : Nat) (H : Int) (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 [false] H (retRev K q hlt (b :: rest) passed under buffer N) =
      some (H - 1, retRev K q hlt rest (b :: passed) under buffer N) := by
  have hz : retRev K q hlt (b :: rest) passed under buffer N =
      ⟨⟨q, hlt⟩, cells rest ++ 2 :: under, cell b, srcRight passed N buffer⟩ := rfl
  have hnh := not_halt (q := ⟨q, hlt⟩) (by rcases hq with rfl | rfl <;> simp)
    (cells rest ++ 2 :: under) (cell b) (srcRight passed N buffer)
  have hr : (program K hK).rule ⟨q, hlt⟩ (cell b) false = some ⟨cell b, ⟨q, hlt⟩, .left⟩ := by
    rcases hq with rfl | rfl <;> cases b <;> simp [program, S, cell]
  rw [hz, run_one hK _ H hnh hr]
  cases rest <;> simp [applyBounded, moveHead, retRev, cells, srcRight]
theorem ret_scan (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 6 ∨ q = 7)
    (near passed : List Bool) (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 (List.replicate near.length false) H
      (retRev K q hlt near passed under buffer N) =
      some (H - (near.length : Int), retRev K q hlt [] (near.reverse ++ passed) under buffer N) := by
  induction near generalizing passed H with
  | nil => simp [run]
  | cons b rest ih =>
      simp only [List.length_cons]
      rw [cons_false, run_append, ret_bit K hK q hq b rest passed under buffer N H, bind_run, ih]
      exact congrArg some (Prod.ext (by omega) (by simp [List.reverse_cons, List.append_assoc]))
theorem ret_stay (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 6 ∨ q = 7)
    (passed : List Bool) (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 [false] H (retRev K q hlt [] passed under buffer N) =
      some (H, ⟨S K hK (q - 6) (by rcases hq with rfl | rfl <;> omega), under, 2,
        srcRight passed N buffer⟩) := by
  have hz : retRev K q hlt [] passed under buffer N =
      ⟨⟨q, hlt⟩, under, 2, srcRight passed N buffer⟩ := rfl
  have hnh := not_halt (q := ⟨q, hlt⟩) (by rcases hq with rfl | rfl <;> simp)
    under (2 : Fin 3) (srcRight passed N buffer)
  have hr : (program K hK).rule ⟨q, hlt⟩ 2 false =
      some ⟨2, S K hK (q - 6) (by rcases hq with rfl | rfl <;> omega), .stay⟩ := by
    rcases hq with rfl | rfl <;> simp [program, S]
  rw [hz, run_one hK _ H hnh hr]; simp [applyBounded, moveHead, S]
theorem return_home (K : Nat) (hK : 0 < K) (q : Nat) (hq : q = 4 ∨ q = 5)
    (remain done : Nat) (bits : List Bool) (under buffer : List (Fin 3))
    (N : Nat) (hN : done + remain = N) (H : Int) (hlt : q < K + 8 := by omega) :
    run (program K hK) 2 (List.replicate (remain + bits.length + 2) false) H
      (leftRev K q hlt remain done bits under buffer) =
      some (H - (remain : Int) - 1 - (bits.length : Int),
        ⟨S K hK (q - 4) (by rcases hq with rfl | rfl <;> omega),
          under, 2, srcRight bits N buffer⟩) := by
  have hsum : remain + bits.length + 2 = remain + 1 + bits.length + 1 := by omega
  have hq' : q + 2 = 6 ∨ q + 2 = 7 := by rcases hq with rfl | rfl <;> simp
  have t0 := left_scan K hK q hq remain done bits under buffer H
  have p0 := replicate_add_run (program K hK) 2 remain 1 H
    (leftRev K q hlt remain done bits under buffer) (by simpa [hN] using t0)
    (by simpa using left_end K hK q hq N bits under buffer (H - (remain : Int)))
  have t2 := ret_scan K hK (q + 2) hq' bits.reverse [] under buffer N
    (H - (remain : Int) - 1) (by rcases hq with rfl | rfl <;> omega)
  have p2 := replicate_add_run (program K hK) 2 (remain + 1) bits.length H
    (leftRev K q hlt remain done bits under buffer) p0
    (by simpa [List.reverse_reverse, List.length_reverse] using t2)
  have t3 := ret_stay K hK (q + 2) hq' bits under buffer N
    (H - (remain : Int) - 1 - (bits.length : Int))
    (by rcases hq with rfl | rfl <;> omega)
  rw [hsum]
  simpa using replicate_add_run (program K hK) 2 (remain + 1 + bits.length) 1 H
    (leftRev K q hlt remain done bits under buffer) p2 (by simpa using t3)
theorem actual_run (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program K hK) 2 (List.replicate (deadline bits.length K N) false) H
      (initial K hK bits under buffer N) = some (H, final K hK bits under buffer N) := by
  by_cases hKN : K ≤ N
  · simp [deadline, hKN]
    have hK1 : K - 1 < K := Nat.sub_lt hK (by decide)
    have hsum : 2 * bits.length + 2 * K + 3 =
        bits.length + 2 + (K - 1) + 1 + (K - 1 + bits.length + 2) := by omega
    have t0 := to_ctr K hK bits under buffer N H
    have t1 := ctr_rights K hK N (K - 1) hK1 (by omega) bits under buffer
      (H + ((bits.length + 2 : Nat) : Int))
    have p1 := replicate_add_run (program K hK) 2 (bits.length + 2) (K - 1) H
      (initial K hK bits under buffer N) t0 t1
    have t2 := ctr_last_enough K hK bits under buffer N hKN
      (H + ((bits.length + 2 : Nat) : Int) + ((K - 1 : Nat) : Int))
    have p2 := replicate_add_run (program K hK) 2 (bits.length + 2 + (K - 1)) 1 H
      (initial K hK bits under buffer N) p1 (by simpa using t2)
    have t3 := return_home K hK 4 (Or.inl rfl) (K - 1) (N - (K - 1)) bits
      under buffer N (by omega)
      (H + ((bits.length + 2 : Nat) : Int) + ((K - 1 : Nat) : Int) - 1)
    rw [hsum, replicate_add_run (program K hK) 2 (bits.length + 2 + (K - 1) + 1)
      (K - 1 + bits.length + 2) H (initial K hK bits under buffer N) p2 t3]
    refine congrArg some (Prod.ext (by omega) (by simp [final, hKN]))
  · simp [deadline, hKN]
    have hNK : N < K := by omega
    have hsum : 2 * bits.length + 2 * N + 5 =
        bits.length + 2 + N + 1 + (N + bits.length + 2) := by omega
    have t0 := to_ctr K hK bits under buffer N H
    have t1 := ctr_rights K hK N N hNK le_rfl bits under buffer
      (H + ((bits.length + 2 : Nat) : Int))
    have p1 := replicate_add_run (program K hK) 2 (bits.length + 2) N H
      (initial K hK bits under buffer N) t0 t1
    have t2 := ctr_seal K hK N hNK bits under buffer
      (H + ((bits.length + 2 : Nat) : Int) + (N : Int))
    have p2 := replicate_add_run (program K hK) 2 (bits.length + 2 + N) 1 H
      (initial K hK bits under buffer N) p1 (by simpa using t2)
    have t3 := return_home K hK 5 (Or.inr rfl) N 0 bits under buffer N (by omega)
      (H + ((bits.length + 2 : Nat) : Int) + (N : Int) - 1)
    rw [hsum, replicate_add_run (program K hK) 2 (bits.length + 2 + N + 1)
      (N + bits.length + 2) H (initial K hK bits under buffer N) p2 t3]
    refine congrArg some (Prod.ext (by omega) (by simp [final, hKN]))
theorem final_halted (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) :
    boundedHalted (final K hK bits under buffer N) = true := by
  simp [boundedHalted, final]; split_ifs <;> simp [S]
theorem actual_growth (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    GrowthRun (program K hK) 2 (List.replicate (deadline bits.length K N) false) H
      (initial K hK bits under buffer N) H (final K hK bits under buffer N) 0 0 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program K hK) 2
    (List.replicate (deadline bits.length K N) false) H H
    (initial K hK bits under buffer N) (final K hK bits under buffer N)
    (actual_run K hK bits under buffer N H)
  have ⟨hl, hr, hc, _⟩ := hg.exact_ledger
  simp [leftEdge, rightEdge, cellCount, initial, final] at hl hr hc
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by omega
  simpa [hlg, hrg] using hg
theorem every_raw (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (K + 8) 3}
    (hw : run (program K hK) 2 w H (initial K hK bits under buffer N) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ deadline bits.length K N ∧
      cellCount out = cellCount (initial K hK bits under buffer N) ∧
      GrowthRun (program K hK) 2 w H (initial K hK bits under buffer N) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly K hK) hw
  have hlen := terminal_length_le (2 : Fin 3) (program K hK) (program_falseOnly K hK)
    (deadline bits.length K N) H H (initial K hK bits under buffer N)
    (final K hK bits under buffer N) (actual_run K hK bits under buffer N H)
    (final_halted K hK bits under buffer N) hw
  have hg := actual_growth K hK bits under buffer N H
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program K hK) 2 w H hf
    (initial K hK bits under buffer N) out hw
  have split : List.replicate (deadline bits.length K N) false =
      w ++ List.replicate (deadline bits.length K N - w.length) false := by
    rw [hfalse]; simpa only [List.length_replicate] using replicate_split _ _ hlen
  have le := growth_append_le (by simpa [split] using hg) hg1
  have ⟨hl1, hr1, hc1, _⟩ := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [(by omega : lg1 = 0), (by omega : rg1 = 0)] using hg1⟩
theorem every_terminal (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (K + 8) 3}
    (hw : run (program K hK) 2 w H (initial K hK bits under buffer N) = some (hf, out))
    (ho : boundedHalted out = true) :
    w = List.replicate (deadline bits.length K N) false ∧ hf = H ∧
      out = final K hK bits under buffer N :=
  terminal_word_eq (2 : Fin 3) (program K hK) (program_falseOnly K hK)
    (deadline bits.length K N) H H (initial K hK bits under buffer N)
    (final K hK bits under buffer N) (actual_run K hK bits under buffer N H)
    (final_halted K hK bits under buffer N) hw ho
theorem cutoff_counts (K : Nat) (hK : 0 < K) (bits : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program K hK) (initial K hK bits under buffer N)) =
      if K ≤ N ∧ deadline bits.length K N ≤ T then 1 else 0 := by
  by_cases hKN : K ≤ N
  · rw [acceptingPaths_threshold (2 : Fin 3) rfl (program K hK) (program_falseOnly K hK)
      (deadline bits.length K N) H (initial K hK bits under buffer N)
      (final K hK bits under buffer N) H (actual_run K hK bits under buffer N H)
      (by simp [final, hKN, S]) T]; simp [hKN]
  · rw [rejecting_paths_zero (2 : Fin 3) rfl (program K hK) (program_falseOnly K hK)
      (deadline bits.length K N) H H (initial K hK bits under buffer N)
      (final K hK bits under buffer N) (actual_run K hK bits under buffer N H)
      (by simp [final, hKN, S]) T]; simp [hKN]
theorem compiled_symbols (K : Nat) (hK : 0 < K) :
    ∀ r ∈ compile (program K hK), r.read < 3 ∧ r.action.write < 3 := fun r hr =>
  ⟨(compile_rule_bounded (program K hK) hr).2.1, (compile_rule_bounded (program K hK) hr).2.2.1⟩
theorem reserve_threshold_probe_spec (K : Nat) (hK : 0 < K)
    (bits : List Bool) (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    (run (program K hK) 2 (List.replicate (deadline bits.length K N) false) H
      (initial K hK bits under buffer N) = some (H, final K hK bits under buffer N)) ∧
    (final K hK bits under buffer N).state.val = (if K ≤ N then 0 else 1) ∧
    (final K hK bits under buffer N).leftRev = under ∧
    (final K hK bits under buffer N).focus = 2 ∧
    (final K hK bits under buffer N).right = srcRight bits N buffer ∧
    GrowthRun (program K hK) 2 (List.replicate (deadline bits.length K N) false) H
      (initial K hK bits under buffer N) H (final K hK bits under buffer N) 0 0 ∧
    (∀ w hf out, run (program K hK) 2 w H (initial K hK bits under buffer N) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ deadline bits.length K N ∧
      cellCount out = cellCount (initial K hK bits under buffer N) ∧
      GrowthRun (program K hK) 2 w H (initial K hK bits under buffer N) hf out 0 0) ∧
    (∀ w hf out, run (program K hK) 2 w H (initial K hK bits under buffer N) = some (hf, out) →
      boundedHalted out = true → w = List.replicate (deadline bits.length K N) false ∧
        hf = H ∧ out = final K hK bits under buffer N) ∧
    (∀ r ∈ compile (program K hK), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program K hK) (initial K hK bits under buffer N)) =
        if K ≤ N ∧ deadline bits.length K N ≤ T then 1 else 0) :=
  ⟨actual_run K hK bits under buffer N H, by simp [final]; split_ifs <;> simp [S],
    rfl, rfl, rfl, actual_growth K hK bits under buffer N H,
    fun _ _ _ => every_raw K hK bits under buffer N H,
    fun _ _ _ => every_terminal K hK bits under buffer N H,
    compiled_symbols K hK, cutoff_counts K hK bits under buffer N H⟩
end PakFixedPolyomino.ULogTernaryReserveThresholdProbe
