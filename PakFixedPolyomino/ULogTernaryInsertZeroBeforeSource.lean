import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter
import PakFixedPolyomino.ULogFiniteTapeZipperRun
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Literal finite ternary insert-zero primitive. One BoundedProgram 8 3,
independent of source `x` and block width. Compact loader composition remains
separate. -/

namespace PakFixedPolyomino.ULogTernaryInsertZeroBeforeSource

open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter (fromCells bind_run fromCells_state)
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryOneHotBlockWriter
  (cellCount_of_cells replicate_split replicate_add_run growth_append_le
    take_succ_getElem replicate_concat config_ext)
open FiniteOneTapeSemantics (moveHead)

def program : BoundedProgram 8 3 where
  rule q read slot :=
    if slot then none
    else if q.val = 2 then
      if read = 2 then some ⟨2, 3, .right⟩ else none
    else if q.val = 3 then
      if read = 0 then some ⟨0, 4, .right⟩
      else if read = 1 then some ⟨0, 5, .right⟩
      else some ⟨0, 6, .right⟩
    else if q.val = 4 then
      if read = 0 then some ⟨0, 4, .right⟩
      else if read = 1 then some ⟨0, 5, .right⟩
      else some ⟨0, 6, .right⟩
    else if q.val = 5 then
      if read = 0 then some ⟨1, 4, .right⟩
      else if read = 1 then some ⟨1, 5, .right⟩
      else some ⟨1, 6, .right⟩
    else if q.val = 6 then
      if read = 0 then some ⟨2, 7, .left⟩ else none
    else if q.val = 7 then
      if read = 2 then some ⟨2, 0, .stay⟩
      else some ⟨read, 7, .left⟩
    else none

def carryQ (b : Bool) : Fin 8 := if b then 5 else 4
def srcRight (x : List Bool) (buffer : List (Fin 3)) : List (Fin 3) :=
  cells x ++ 2 :: 0 :: buffer
def payload (x : List Bool) : List (Fin 3) := 0 :: cells x
def initial (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 8 3 := fromCells 2 under (2 :: srcRight x buffer)
def final (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 8 3 := fromCells 0 under (2 :: payload x ++ 2 :: buffer)
def deadline (n : Nat) : Nat := 2 * n + 5
def occupied (x : List Bool) (under buffer : List (Fin 3)) : Nat :=
  under.length + x.length + 3 + buffer.length
def q3Cfg (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 8 3 := fromCells 3 (2 :: under) (srcRight x buffer)
def carryCfg (pref rest : List Bool) (c : Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 8 3 :=
  fromCells (carryQ c) ((cells pref).reverse ++ 0 :: 2 :: under)
    (srcRight rest buffer)
def q6Cfg (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 8 3 :=
  fromCells 6 ((cells x).reverse ++ 0 :: 2 :: under) (0 :: buffer)
def returnCfg (x : List Bool) (under buffer : List (Fin 3)) (d : Nat)
    (_hd : d ≤ x.length + 1) : BoundedConfig 8 3 :=
  if h : d = x.length + 1 then ⟨7, under, 2, payload x ++ 2 :: buffer⟩
  else
    ⟨7, ((payload x).take (x.length - d)).reverse ++ 2 :: under,
      (payload x)[x.length - d]'(by simp [payload, cells]),
      (payload x).drop (x.length - d + 1) ++ 2 :: buffer⟩

theorem program_falseOnly : FalseOnly program := by
  intro q read; simp [program]
theorem rule_q2 : program.rule 2 2 false = some ⟨2, 3, .right⟩ := by
  simp [program]
theorem nextQ_cell (b : Bool) :
    (if cell b = 0 then (4 : Fin 8) else if cell b = 1 then 5 else 6) =
      carryQ b := by cases b <;> simp [cell, carryQ]
theorem rule_q3 (r : Fin 3) :
    program.rule 3 r false =
      some ⟨0, if r = 0 then 4 else if r = 1 then 5 else 6, .right⟩ := by
  simp [program]; split_ifs <;> rfl
theorem rule_carry (c : Bool) (r : Fin 3) :
    program.rule (carryQ c) r false =
      some ⟨cell c, if r = 0 then 4 else if r = 1 then 5 else 6, .right⟩ := by
  cases c <;> simp [program, carryQ, cell] <;> split_ifs <;> rfl
theorem rule_q6 : program.rule 6 0 false = some ⟨2, 7, .left⟩ := by
  simp [program]
theorem rule_q7_mark : program.rule 7 2 false = some ⟨2, 0, .stay⟩ := by
  simp [program]
theorem rule_q7_bit (r : Fin 3) (hr : r ≠ 2) :
    program.rule 7 r false = some ⟨r, 7, .left⟩ := by simp [program, hr]
theorem not_halt {q : Fin 8} (h : 2 ≤ q.val) (left : List (Fin 3))
    (foc : Fin 3) (rest : List (Fin 3)) :
    boundedHalted (⟨q, left, foc, rest⟩ : BoundedConfig 8 3) = false := by
  simp [boundedHalted]; omega
theorem not_halt_carry (c : Bool) (left : List (Fin 3)) (foc : Fin 3)
    (rest : List (Fin 3)) :
    boundedHalted (⟨carryQ c, left, foc, rest⟩ : BoundedConfig 8 3) = false := by
  simp [boundedHalted, carryQ]; split_ifs <;> omega
theorem run_one (z : BoundedConfig 8 3) (H : Int) {a : BoundedAction 8 3}
    (hnh : boundedHalted z = false)
    (hr : program.rule z.state z.focus false = some a) :
    run program 2 [false] H z =
      some (moveHead a.move H, applyBounded (2 : Fin 3) z a) := by
  simp [run, hnh, hr]
theorem srcRight_cons (b : Bool) (rest : List Bool) (buffer : List (Fin 3)) :
    srcRight (b :: rest) buffer = cell b :: srcRight rest buffer := rfl
theorem payload_length (x : List Bool) : (payload x).length = x.length + 1 := by
  simp [payload, cells]
theorem cells_snoc (pref : List Bool) (c : Bool) :
    cells (pref ++ [c]) = cells pref ++ [cell c] := by simp [cells]
theorem cell_ne_two (b : Bool) : cell b ≠ 2 := by cases b <;> simp [cell]
theorem payload_ne_two (x : List Bool) (i : Nat) (hi : i < (payload x).length) :
    (payload x)[i] ≠ 2 := by
  cases i with
  | zero => simp [payload]
  | succ i => simp [payload, cells] at hi ⊢; exact cell_ne_two _
theorem q6_leftRev (x : List Bool) (under : List (Fin 3)) :
    (cells x).reverse ++ 0 :: 2 :: under = (payload x).reverse ++ 2 :: under := by
  simp [payload, List.reverse_cons]
theorem reverse_getLast {α} (l : List α) (hne : l ≠ []) :
    l.reverse = l.getLast hne :: l.dropLast.reverse := by
  match l with
  | [] => cases hne rfl
  | a :: as =>
      induction as generalizing a <;> simp [List.getLast, List.dropLast, *]
theorem payload_reverse_cons (x : List Bool) :
    (payload x).reverse =
      (payload x)[x.length]'(by simp [payload_length]) ::
        ((payload x).take x.length).reverse := by
  have hne : payload x ≠ [] := List.cons_ne_nil _ _
  rw [reverse_getLast _ hne, List.getLast_eq_getElem, List.dropLast_eq_take]
  simp [payload_length]
theorem drop_succ_getElem {α} (l : List α) (k : Nat) (hk : k < l.length) :
    l[k] :: l.drop (k + 1) = l.drop k := (List.drop_eq_getElem_cons hk).symm
theorem cons_false (n : Nat) :
    List.replicate (n + 1) false = [false] ++ List.replicate n false := by
  simp [List.replicate_succ]

theorem step_start (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (initial x under buffer) =
      some (H + 1, q3Cfg x under buffer) := by
  have hz : initial x under buffer = ⟨2, under, 2, srcRight x buffer⟩ := rfl
  have hnh := not_halt (q := (2 : Fin 8)) (by decide) under (2 : Fin 3)
    (srcRight x buffer)
  rw [hz, run_one _ H hnh (by simpa using rule_q2)]
  cases hs : srcRight x buffer with
  | nil => simp [srcRight, cells] at hs
  | cons a rest => simp [applyBounded, moveHead, q3Cfg, fromCells, hs]
theorem step_q3_nil (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (q3Cfg [] under buffer) =
      some (H + 1, q6Cfg [] under buffer) := by
  have hz : q3Cfg [] under buffer = ⟨3, 2 :: under, 2, 0 :: buffer⟩ := by
    simp [q3Cfg, fromCells, srcRight, cells]
  have hnh := not_halt (q := (3 : Fin 8)) (by decide) (2 :: under) (2 : Fin 3)
    (0 :: buffer)
  rw [hz, run_one _ H hnh (by simpa using rule_q3 (2 : Fin 3))]
  simp [applyBounded, moveHead, q6Cfg, fromCells, cells]
theorem step_q3_cons (b : Bool) (rest : List Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (q3Cfg (b :: rest) under buffer) =
      some (H + 1, carryCfg [] rest b under buffer) := by
  have hz : q3Cfg (b :: rest) under buffer =
      ⟨3, 2 :: under, cell b, srcRight rest buffer⟩ := by
    simp [q3Cfg, fromCells, srcRight_cons]
  have hnh := not_halt (q := (3 : Fin 8)) (by decide) (2 :: under) (cell b)
    (srcRight rest buffer)
  rw [hz, run_one _ H hnh (by simpa using rule_q3 (cell b))]
  cases hs : srcRight rest buffer with
  | nil => simp [srcRight, cells] at hs
  | cons a tl =>
      simp [applyBounded, moveHead, carryCfg, fromCells, cells, hs]
      exact nextQ_cell b
theorem step_carry_nil (pref : List Bool) (c : Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (carryCfg pref [] c under buffer) =
      some (H + 1, q6Cfg (pref ++ [c]) under buffer) := by
  have hz : carryCfg pref [] c under buffer =
      ⟨carryQ c, (cells pref).reverse ++ 0 :: 2 :: under, 2, 0 :: buffer⟩ := by
    simp [carryCfg, fromCells, srcRight, cells]
  rw [hz, run_one _ H (not_halt_carry _ _ _ _)
    (by simpa using rule_carry c (2 : Fin 3))]
  simp [applyBounded, moveHead, q6Cfg, fromCells, cells_snoc, List.reverse_append]
theorem step_carry_cons (pref : List Bool) (b : Bool) (rest : List Bool)
    (c : Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (carryCfg pref (b :: rest) c under buffer) =
      some (H + 1, carryCfg (pref ++ [c]) rest b under buffer) := by
  have hz : carryCfg pref (b :: rest) c under buffer =
      ⟨carryQ c, (cells pref).reverse ++ 0 :: 2 :: under, cell b,
        srcRight rest buffer⟩ := by
    simp [carryCfg, fromCells, srcRight_cons]
  rw [hz, run_one _ H (not_halt_carry _ _ _ _)
    (by simpa using rule_carry c (cell b))]
  cases hs : srcRight rest buffer with
  | nil => simp [srcRight, cells] at hs
  | cons a tl =>
      simp [applyBounded, moveHead, carryCfg, fromCells, cells_snoc,
        List.reverse_append, hs]
      exact nextQ_cell b

theorem carry_to_q6 (pref rest : List Bool) (c : Bool)
    (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (rest.length + 1) false) H
      (carryCfg pref rest c under buffer) =
      some (H + ((rest.length + 1 : Nat) : Int),
        q6Cfg (pref ++ c :: rest) under buffer) := by
  induction rest generalizing pref c H with
  | nil => simpa [List.replicate, List.append_nil] using
      step_carry_nil pref c under buffer H
  | cons b rest ih =>
      rw [cons_false]; simp only [List.length_cons]
      rw [run_append, step_carry_cons, bind_run, ih]
      refine congrArg some (Prod.ext ?_ ?_)
      · simp [List.length_cons]; omega
      · simp [List.append_assoc]
theorem q3_to_q6 (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (x.length + 1) false) H
      (q3Cfg x under buffer) =
      some (H + ((x.length + 1 : Nat) : Int), q6Cfg x under buffer) := by
  cases x with
  | nil => simpa [List.replicate] using step_q3_nil under buffer H
  | cons b rest =>
      rw [cons_false]; simp only [List.length_cons]
      rw [run_append, step_q3_cons, bind_run, carry_to_q6]
      exact congrArg some (Prod.ext (by simp [List.length_cons]; omega) rfl)
theorem to_q6 (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (x.length + 2) false) H
      (initial x under buffer) =
      some (H + ((x.length + 2 : Nat) : Int), q6Cfg x under buffer) := by
  rw [show x.length + 2 = (x.length + 1) + 1 by omega, cons_false,
    run_append, step_start, bind_run, q3_to_q6]
  exact congrArg some (Prod.ext (by omega) rfl)

theorem returnCfg_zero (x : List Bool) (under buffer : List (Fin 3)) :
    returnCfg x under buffer 0 (Nat.zero_le _) =
      ⟨7, ((payload x).take x.length).reverse ++ 2 :: under,
        (payload x)[x.length]'(by simp [payload_length]),
        (payload x).drop (x.length + 1) ++ 2 :: buffer⟩ := by
  have hne : ¬ 0 = x.length + 1 := by omega
  simp [returnCfg, hne]
theorem step_q6 (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H (q6Cfg x under buffer) =
      some (H - 1, returnCfg x under buffer 0 (Nat.zero_le _)) := by
  have hrev := payload_reverse_cons x
  have hz : q6Cfg x under buffer =
      ⟨6, (payload x)[x.length]'(by simp [payload_length]) ::
          ((payload x).take x.length).reverse ++ 2 :: under, 0, buffer⟩ := by
    simp [q6Cfg, fromCells, q6_leftRev, hrev]
  have hnh := not_halt (q := (6 : Fin 8)) (by decide)
    ((payload x)[x.length]'(by simp [payload_length]) ::
      ((payload x).take x.length).reverse ++ 2 :: under) (0 : Fin 3) buffer
  rw [hz, run_one _ H hnh (by simpa using rule_q6)]
  simp [applyBounded, moveHead, returnCfg_zero, payload_length]
theorem step_return (x : List Bool) (under buffer : List (Fin 3)) (d : Nat)
    (hd : d + 1 ≤ x.length + 1) (H : Int) :
    run program 2 [false] H
      (returnCfg x under buffer d (Nat.le_of_succ_le hd)) =
      some (H - 1, returnCfg x under buffer (d + 1) hd) := by
  have hdlt : d ≠ x.length + 1 := by omega
  have hi : x.length - d < (payload x).length := by
    rw [payload_length]; exact Nat.sub_lt_succ _ _
  have hfoc := payload_ne_two x (x.length - d) hi
  by_cases hlast : d + 1 = x.length + 1
  · have hd0 : x.length - d = 0 := by omega
    have hsrc :
        returnCfg x under buffer d (Nat.le_of_succ_le hd) =
          ⟨7, 2 :: under, (payload x)[0]'(by simp [payload_length]),
            (payload x).drop 1 ++ 2 :: buffer⟩ := by
      simp [returnCfg, hdlt, hd0, List.take_zero]
    have hnh := not_halt (q := (7 : Fin 8)) (by decide) (2 :: under)
      ((payload x)[0]'(by simp [payload_length]))
      ((payload x).drop 1 ++ 2 :: buffer)
    rw [hsrc, run_one _ H hnh (by
      simpa [hd0] using rule_q7_bit
        ((payload x)[0]'(by simp [payload_length]))
        (by simpa [hd0] using hfoc))]
    simp [applyBounded, moveHead, returnCfg, hlast]
    exact congrArg (fun l => l ++ 2 :: buffer)
      (drop_succ_getElem (payload x) 0 (by simp [payload_length]))
  · have hk : x.length - d = x.length - (d + 1) + 1 := by omega
    have hi' : x.length - (d + 1) < (payload x).length := by
      rw [payload_length]; exact Nat.sub_lt_succ _ _
    have hrev :
        ((payload x).take (x.length - d)).reverse =
          (payload x)[x.length - (d + 1)]'hi' ::
            ((payload x).take (x.length - (d + 1))).reverse := by
      rw [hk, take_succ_getElem (payload x) _ hi', List.reverse_append]; simp
    have hsrc :
        returnCfg x under buffer d (Nat.le_of_succ_le hd) =
          ⟨7, (payload x)[x.length - (d + 1)]'hi' ::
              ((payload x).take (x.length - (d + 1))).reverse ++ 2 :: under,
            (payload x)[x.length - d]'hi,
            (payload x).drop (x.length - d + 1) ++ 2 :: buffer⟩ := by
      unfold returnCfg; rw [dif_neg hdlt, hrev]
    have hdst :
        returnCfg x under buffer (d + 1) hd =
          ⟨7, ((payload x).take (x.length - (d + 1))).reverse ++ 2 :: under,
            (payload x)[x.length - (d + 1)]'hi',
            (payload x).drop (x.length - (d + 1) + 1) ++ 2 :: buffer⟩ := by
      unfold returnCfg; rw [dif_neg hlast]
    have hnh := not_halt (q := (7 : Fin 8)) (by decide)
      ((payload x)[x.length - (d + 1)]'hi' ::
        ((payload x).take (x.length - (d + 1))).reverse ++ 2 :: under)
      ((payload x)[x.length - d]'hi)
      ((payload x).drop (x.length - d + 1) ++ 2 :: buffer)
    rw [hsrc, run_one _ H hnh (by simpa using rule_q7_bit _ hfoc)]
    simp [applyBounded, moveHead]
    rw [hdst]
    apply config_ext
    · rfl
    · rfl
    · rfl
    · have hdropidx : x.length - (d + 1) + 1 = x.length - d := by omega
      rw [hdropidx]
      exact congrArg (fun l => l ++ 2 :: buffer)
        (drop_succ_getElem (payload x) (x.length - d) hi)
theorem return_prefix (x : List Bool) (under buffer : List (Fin 3)) (d : Nat)
    (hd : d ≤ x.length + 1) (H : Int) :
    run program 2 (List.replicate d false) H
      (returnCfg x under buffer 0 (Nat.zero_le _)) =
      some (H - d, returnCfg x under buffer d hd) := by
  induction d with
  | zero => simp [run]
  | succ d ih =>
      have hd0 : d ≤ x.length + 1 := by omega
      rw [replicate_concat, run_append, ih hd0, bind_run,
        step_return x under buffer d (by omega)]
      exact congrArg some (Prod.ext (by omega) rfl)
theorem step_accept (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 [false] H
      (returnCfg x under buffer (x.length + 1) (Nat.le_refl _)) =
      some (H, final x under buffer) := by
  have hz : returnCfg x under buffer (x.length + 1) (Nat.le_refl _) =
      ⟨7, under, 2, payload x ++ 2 :: buffer⟩ := by simp [returnCfg]
  have hnh := not_halt (q := (7 : Fin 8)) (by decide) under (2 : Fin 3)
    (payload x ++ 2 :: buffer)
  rw [hz, run_one _ H hnh (by simpa using rule_q7_mark)]
  simp [applyBounded, moveHead, final, fromCells]
theorem to_return0 (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (x.length + 3) false) H
      (initial x under buffer) =
      some (H + ((x.length + 1 : Nat) : Int),
        returnCfg x under buffer 0 (Nat.zero_le _)) := by
  rw [show x.length + 3 = (x.length + 2) + 1 by omega, replicate_concat,
    run_append, to_q6, bind_run, step_q6]
  exact congrArg some (Prod.ext (by omega) rfl)
theorem insert_zero_run (x : List Bool) (under buffer : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate (deadline x.length) false) H
      (initial x under buffer) =
      some (H, final x under buffer) := by
  have h123 := replicate_add_run program 2 (x.length + 3) (x.length + 1) H
    (initial x under buffer) (to_return0 x under buffer H)
    (return_prefix x under buffer (x.length + 1) (Nat.le_refl _)
      (H + ((x.length + 1 : Nat) : Int)))
  have hE2 : H + ((x.length + 1 : Nat) : Int) - ((x.length + 1 : Nat) : Int) =
      H := by omega
  have h123' :
      run program 2 (List.replicate (2 * x.length + 4) false) H
        (initial x under buffer) =
        some (H, returnCfg x under buffer (x.length + 1) (Nat.le_refl _)) := by
    simpa [hE2, show x.length + 3 + (x.length + 1) = 2 * x.length + 4 by omega]
      using h123
  have hfull := replicate_add_run program 2 (2 * x.length + 4) 1 H
    (initial x under buffer) h123' (step_accept x under buffer H)
  simpa [deadline, show 2 * x.length + 4 + 1 = 2 * x.length + 5 by omega] using
    hfull

theorem carry_prefix (pref rest : List Bool) (c : Bool)
    (under buffer : List (Fin 3)) (H : Int) (j : Nat)
    (hj : j ≤ rest.length + 1) :
    ∃ z, run program 2 (List.replicate j false) H
      (carryCfg pref rest c under buffer) = some (H + (j : Int), z) := by
  induction rest generalizing pref c j H with
  | nil =>
      cases j with
      | zero => exact ⟨carryCfg pref [] c under buffer, by simp [run]⟩
      | succ j =>
          have : j = 0 := by
            have hj1 : j.succ ≤ 1 := by simpa [List.length_nil] using hj
            omega
          subst this
          exact ⟨q6Cfg (pref ++ [c]) under buffer,
            by simpa using step_carry_nil pref c under buffer H⟩
  | cons b rest ih =>
      cases j with
      | zero => exact ⟨carryCfg pref (b :: rest) c under buffer, by simp [run]⟩
      | succ j =>
          have hj' : j ≤ rest.length + 1 := by
            simp [List.length_cons] at hj; omega
          obtain ⟨z, hz⟩ := ih (pref ++ [c]) b (H + 1) j hj'
          refine ⟨z, ?_⟩
          rw [cons_false, run_append, step_carry_cons, bind_run, hz]
          exact congrArg some (Prod.ext (by omega) rfl)
theorem q3_prefix (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (j : Nat) (hj : j ≤ x.length + 1) :
    ∃ z, run program 2 (List.replicate j false) H (q3Cfg x under buffer) =
      some (H + (j : Int), z) := by
  cases x with
  | nil =>
      cases j with
      | zero => exact ⟨q3Cfg [] under buffer, by simp [run]⟩
      | succ j =>
          have : j = 0 := by
            have hj1 : j.succ ≤ 1 := by simpa [List.length_nil] using hj
            omega
          subst this
          exact ⟨q6Cfg [] under buffer,
            by simpa using step_q3_nil under buffer H⟩
  | cons b rest =>
      cases j with
      | zero => exact ⟨q3Cfg (b :: rest) under buffer, by simp [run]⟩
      | succ j =>
          have hj' : j ≤ rest.length + 1 := by
            simp [List.length_cons] at hj; omega
          obtain ⟨z, hz⟩ := carry_prefix [] rest b under buffer (H + 1) j hj'
          refine ⟨z, ?_⟩
          rw [cons_false, run_append, step_q3_cons, bind_run, hz]
          exact congrArg some (Prod.ext (by omega) rfl)
theorem right_prefix (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (k : Nat) (hk : k ≤ x.length + 2) :
    ∃ z, run program 2 (List.replicate k false) H (initial x under buffer) =
      some (H + (k : Int), z) := by
  cases k with
  | zero => exact ⟨initial x under buffer, by simp [run]⟩
  | succ k =>
      obtain ⟨z, hz⟩ := q3_prefix x under buffer (H + 1) k (by omega)
      refine ⟨z, ?_⟩
      rw [cons_false, run_append, step_start, bind_run, hz]
      exact congrArg some (Prod.ext (by omega) rfl)

def midHead (n t : Nat) (H : Int) : Int :=
  if t ≤ n + 2 then H + t
  else if t ≤ 2 * n + 4 then
    H + ((n + 1 : Nat) : Int) - ((t - (n + 3) : Nat) : Int)
  else H
theorem prefix_head (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (t : Nat) (ht : t ≤ deadline x.length) :
    ∃ zf,
      run program 2 (List.replicate t false) H (initial x under buffer) =
        some (midHead x.length t H, zf) ∧
      H ≤ midHead x.length t H ∧
      midHead x.length t H ≤ H + ((x.length + 2 : Nat) : Int) := by
  by_cases h1 : t ≤ x.length + 2
  · obtain ⟨zf, hz⟩ := right_prefix x under buffer H t h1
    refine ⟨zf, by simpa [midHead, h1] using hz, by simp [midHead, h1], ?_⟩
    simp [midHead, h1]; exact Int.ofNat_le.mpr h1
  · by_cases h2 : t ≤ 2 * x.length + 4
    · have hd : t - (x.length + 3) ≤ x.length + 1 := by omega
      have hlen : (x.length + 3) + (t - (x.length + 3)) = t := by omega
      have hrun := replicate_add_run program 2 (x.length + 3)
        (t - (x.length + 3)) H (initial x under buffer)
        (to_return0 x under buffer H)
        (return_prefix x under buffer (t - (x.length + 3)) hd
          (H + ((x.length + 1 : Nat) : Int)))
      refine ⟨returnCfg x under buffer (t - (x.length + 3)) hd, ?_, ?_, ?_⟩
      · simpa [midHead, h1, h2, hlen] using hrun
      · simp [midHead, h1, h2]; omega
      · simp [midHead, h1, h2]; omega
    · have ht5 : t = 2 * x.length + 5 := by simp [deadline] at ht; omega
      have hmid : midHead x.length t H = H := by
        subst ht5; simp [midHead, h1, h2]
      refine ⟨final x under buffer, ?_, by simp [hmid], by simp [hmid]; omega⟩
      · rw [hmid, ht5]; simpa [deadline] using insert_zero_run x under buffer H

theorem occupied_initial (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial x under buffer) = occupied x under buffer := by
  have hne : 2 :: srcRight x buffer ≠ [] := List.cons_ne_nil _ _
  rw [initial, cellCount_of_cells _ _ _ hne]
  simp [occupied, srcRight, cells]; omega
theorem occupied_final (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (final x under buffer) = occupied x under buffer := by
  have hne : 2 :: payload x ++ 2 :: buffer ≠ [] := List.cons_ne_nil _ _
  rw [final, cellCount_of_cells _ _ _ hne]
  simp [occupied, payload, cells]; omega
theorem final_state (x : List Bool) (under buffer : List (Fin 3)) :
    (final x under buffer).state.val = 0 := by
  simp [final, fromCells_state]

theorem every_raw (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig 8 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧
      w.length ≤ deadline x.length ∧
      H ≤ hf ∧ hf ≤ H + ((x.length + 2 : Nat) : Int) ∧
      cellCount zf = occupied x under buffer := by
  have hwfalse :=
    successful_zipper_is_false (2 : Fin 3) program program_falseOnly hw
  have hlen :=
    successful_zipper_length_le (2 : Fin 3) program program_falseOnly
      (deadline x.length) H (initial x under buffer) (final x under buffer) H
      (insert_zero_run x under buffer H) (final_state x under buffer) hw
  obtain ⟨zf', hpre, hlo, hhi⟩ := prefix_head x under buffer H w.length hlen
  have hw' : run program 2 (List.replicate w.length false) H
      (initial x under buffer) = some (hf, zf) := by rwa [← hwfalse]
  obtain ⟨hf_eq, zf_eq⟩ := Prod.mk.inj (Option.some.inj (hw'.symm.trans hpre))
  subst zf
  rw [← hf_eq] at hlo hhi
  refine ⟨hwfalse, hlen, hlo, hhi, ?_⟩
  obtain ⟨lg, rg, hG⟩ :=
    every_actual_run program 2 (List.replicate (deadline x.length) false)
      H H (initial x under buffer) (final x under buffer)
      (insert_zero_run x under buffer H)
  have hcnt :
      cellCount (final x under buffer) = cellCount (initial x under buffer) := by
    rw [occupied_final x under buffer, occupied_initial x under buffer]
  have h0 : lg = 0 ∧ rg = 0 := by
    have := hG.exact_ledger; omega
  have hsplit := replicate_split (deadline x.length) w.length hlen
  have hGfull : GrowthRun program 2
      (List.replicate w.length false ++
        List.replicate (deadline x.length - w.length) false)
      H (initial x under buffer) H (final x under buffer) lg rg := by
    simpa [hsplit] using hG
  obtain ⟨lg1, rg1, hG1⟩ :=
    every_actual_run program 2 (List.replicate w.length false) H hf
      (initial x under buffer) zf' hw'
  have ⟨hleL, hleR⟩ := growth_append_le hGfull hG1
  have hP := hG1.exact_ledger
  have hocc := occupied_initial x under buffer
  omega
theorem every_raw_no_growth (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) {w : List Bool} {hf : Int} {zf : BoundedConfig 8 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    GrowthRun program 2 w H (initial x under buffer) hf zf 0 0 := by
  obtain ⟨lg, rg, hg⟩ :=
    every_actual_run program 2 w H hf (initial x under buffer) zf hw
  have hraw := every_raw x under buffer H hw
  have he := hg.exact_ledger
  have h0 := occupied_initial x under buffer
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg
theorem accepting_word (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig 8 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline x.length) false ∧ hf = H ∧
      zf = final x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) program program_falseOnly
    (deadline x.length) H (initial x under buffer) (final x under buffer) H
    (insert_zero_run x under buffer H) (final_state x under buffer) hw ha
theorem compiled_symbols :
    ∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded program hr
  exact ⟨hb.2.1, hb.2.2.1⟩
theorem cutoff_counts (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig program (initial x under buffer)) =
      if deadline x.length ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl program program_falseOnly
    (deadline x.length) H (initial x under buffer) (final x under buffer) H
    (insert_zero_run x under buffer H) (final_state x under buffer) T

theorem insert_zero_spec :
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int),
      run program 2 (List.replicate (deadline x.length) false) H
        (initial x under buffer) =
        some (H, final x under buffer)) ∧
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig 8 3),
      run program 2 w H (initial x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧
        w.length ≤ deadline x.length ∧
        H ≤ hf ∧ hf ≤ H + ((x.length + 2 : Nat) : Int) ∧
        cellCount zf = occupied x under buffer ∧
        GrowthRun program 2 w H (initial x under buffer) hf zf 0 0) ∧
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig 8 3),
      run program 2 w H (initial x under buffer) = some (hf, zf) →
      zf.state.val = 0 →
      w = List.replicate (deadline x.length) false ∧ hf = H ∧
        zf = final x under buffer) ∧
    (∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3) ∧
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int) (T : Nat),
      ULogSemantics.machine.acceptingPaths T
        (liftConfig program (initial x under buffer)) =
        if deadline x.length ≤ T then 1 else 0) := by
  refine ⟨insert_zero_run, ?_, ?_, compiled_symbols, cutoff_counts⟩
  · intro x under buffer H w hf zf hw
    have h := every_raw x under buffer H hw
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      every_raw_no_growth x under buffer H hw⟩
  · intro x under buffer H w hf zf hw ha
    exact accepting_word x under buffer H hw ha

end PakFixedPolyomino.ULogTernaryInsertZeroBeforeSource
