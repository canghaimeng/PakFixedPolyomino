import PakFixedPolyomino.ULogTernaryRetainedCounterPump
import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! Fixed 24-state ternary counted-source delimiter. One program independent
of `x`. Marks the length header into ones, restores every source bit, and
turns the first existing buffer zero into delimiter 2. No tape extension.
Physical loader/headline remain separate. -/

namespace PakFixedPolyomino.ULogTernaryCountedSourceDelimiter

open ULogCompiler ULogFiniteTapeZipperRun
open ULogTernaryRetainedCounterPump (cell cells)
open FiniteOneTapeSemantics (moveHead)

def fromCells {ns : Nat} (q : Fin ns) (left : List (Fin 3)) :
    List (Fin 3) → BoundedConfig ns 3
  | [] => ⟨q, left, 2, []⟩
  | a :: rest => ⟨q, left, a, rest⟩

def mem4 (b : Bool) : Fin 24 := if b then 5 else 4
def mem6 (b : Bool) : Fin 24 := if b then 7 else 6
def mem8 (b : Bool) : Fin 24 := if b then 9 else 8
def mem10 (b : Bool) : Fin 24 := if b then 11 else 10

def program : BoundedProgram 24 3 where
  rule q read slot :=
    if slot then none
    else if q.val = 2 then
      if read = 0 then some ⟨0, 2, .right⟩
      else if read = 1 then some ⟨2, 3, .right⟩
      else none
    else if q.val = 3 then
      if read = 0 then some ⟨2, 4, .left⟩
      else if read = 1 then some ⟨2, 5, .left⟩
      else none
    else if q.val = 4 then
      if read = 2 then some ⟨2, 6, .left⟩
      else some ⟨read, 4, .left⟩
    else if q.val = 5 then
      if read = 2 then some ⟨2, 7, .left⟩
      else some ⟨read, 5, .left⟩
    else if q.val = 6 then
      if read = 1 then some ⟨1, 6, .left⟩
      else if read = 0 then some ⟨1, 8, .right⟩
      else if read = 2 then some ⟨2, 14, .right⟩
      else none
    else if q.val = 7 then
      if read = 1 then some ⟨1, 7, .left⟩
      else if read = 0 then some ⟨1, 9, .right⟩
      else if read = 2 then some ⟨2, 14, .right⟩
      else none
    else if q.val = 8 then
      if read = 1 then some ⟨1, 8, .right⟩
      else if read = 2 then some ⟨2, 10, .right⟩
      else none
    else if q.val = 9 then
      if read = 1 then some ⟨1, 9, .right⟩
      else if read = 2 then some ⟨2, 11, .right⟩
      else none
    else if q.val = 10 then
      if read = 2 then some ⟨0, 3, .right⟩
      else some ⟨read, 10, .right⟩
    else if q.val = 11 then
      if read = 2 then some ⟨1, 3, .right⟩
      else some ⟨read, 11, .right⟩
    else if q.val = 14 then
      if read = 1 then some ⟨1, 14, .right⟩
      else if read = 2 then some ⟨2, 15, .right⟩
      else none
    else if q.val = 15 then
      if read = 2 then some ⟨2, 16, .left⟩
      else some ⟨read, 15, .right⟩
    else if q.val = 16 then
      if read = 2 then some ⟨2, 0, .right⟩
      else some ⟨read, 16, .left⟩
    else none

theorem rule_true (q : Fin 24) (read : Fin 3) :
    program.rule q read true = none := by
  simp [program]

def initial (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 24 3 :=
  fromCells 2 (2 :: under)
    (List.replicate x.length (0 : Fin 3) ++ 1 :: (cells x ++ 0 :: buffer))

def deadline (n : Nat) : Nat := 2 * n * n + 9 * n + 7

def copiesCost (i : Nat) : Nat := 2 * i * i + 3 * i

def roundCost (i : Nat) : Nat := 4 * i + 5

def failCost (n : Nat) : Nat := 5 * n + 6

def ones (i : Nat) : List (Fin 3) := List.replicate i 1

def zeros (i : Nat) : List (Fin 3) := List.replicate i 0

/-- Header as leftRev from the separator: nearest cells are the used ones. -/
def headerL (n i : Nat) : List (Fin 3) := ones i ++ zeros (n - i)

def cursorLeft (x : List Bool) (under : List (Fin 3)) (i : Nat) : List (Fin 3) :=
  (cells (x.take i)).reverse ++ 2 :: headerL x.length i ++ 2 :: under

def cursorTape (x : List Bool) (buffer : List (Fin 3)) (i : Nat) : List (Fin 3) :=
  cells (x.drop i) ++ 0 :: buffer

def atCursor (x : List Bool) (under buffer : List (Fin 3)) (i : Nat) :
    BoundedConfig 24 3 :=
  fromCells 3 (cursorLeft x under i) (cursorTape x buffer i)

def finalConfig (x : List Bool) (under buffer : List (Fin 3)) :
    BoundedConfig 24 3 :=
  fromCells 0 (2 :: (ones x.length ++ 2 :: under)) (cells x ++ 2 :: buffer)

theorem deadline_split (n : Nat) :
    deadline n = n + 1 + copiesCost n + failCost n := by
  simp [deadline, copiesCost, failCost]
  ring

theorem copiesCost_succ (i : Nat) :
    copiesCost (i + 1) = copiesCost i + roundCost i := by
  simp [copiesCost, roundCost]
  ring

theorem copiesCost_zero : copiesCost 0 = 0 := rfl

theorem not_halted {ns : Nat} (q : Fin ns) (left : List (Fin 3))
    (a : Fin 3) (rest : List (Fin 3)) (h : 2 ≤ q.val) :
    boundedHalted (fromCells q left (a :: rest)) = false := by
  simp [boundedHalted, fromCells]; omega

theorem fromCells_eq {ns : Nat} {q q' : Fin ns}
    {left left' right right' : List (Fin 3)}
    (hq : q = q') (hl : left = left') (hr : right = right') :
    fromCells q left right = fromCells q' left' right' := by
  cases hq; cases hl; cases hr; rfl

theorem bind_run {ns nt : Nat} (p : BoundedProgram ns nt) (blank : Fin nt)
    (ys : List Bool) (head : Int) (z : BoundedConfig ns nt) :
    (some (head, z)).bind (fun hz => run p blank ys hz.1 hz.2) =
      run p blank ys head z :=
  rfl

theorem fromCells_state {ns : Nat} (q : Fin ns) (left right : List (Fin 3)) :
    (fromCells q left right).state = q := by
  cases right <;> rfl

theorem cell_false : cell false = 0 := rfl
theorem cell_true : cell true = 1 := rfl

theorem cells_cons (b : Bool) (x : List Bool) :
    cells (b :: x) = cell b :: cells x :=
  rfl

theorem cells_nil : cells [] = [] := rfl

theorem cells_length (x : List Bool) : (cells x).length = x.length := by
  simp [cells]

theorem cells_append (x y : List Bool) :
    cells (x ++ y) = cells x ++ cells y := by
  simp [cells]

theorem cells_take (x : List Bool) (i : Nat) :
    cells (x.take i) = (cells x).take i := by
  simp [cells, List.map_take]

theorem cells_drop (x : List Bool) (i : Nat) :
    cells (x.drop i) = (cells x).drop i := by
  simp [cells, List.map_drop]

theorem zeros_succ (n : Nat) : zeros (n + 1) = 0 :: zeros n := by
  simp [zeros, List.replicate_succ]

theorem ones_succ (n : Nat) : ones (n + 1) = 1 :: ones n := by
  simp [ones, List.replicate_succ]

theorem zeros_append (i j : Nat) :
    zeros i ++ zeros j = zeros (i + j) := by
  simp [zeros]

theorem ones_append (i j : Nat) :
    ones i ++ ones j = ones (i + j) := by
  simp [ones]

theorem replicate_snoc_zero (n : Nat) (rest : List (Fin 3)) :
    zeros n ++ 0 :: rest = 0 :: (zeros n ++ rest) := by
  induction n with
  | zero => simp [zeros]
  | succ n ih => simp [zeros_succ, ih]

theorem replicate_snoc_one (n : Nat) (rest : List (Fin 3)) :
    ones n ++ 1 :: rest = 1 :: (ones n ++ rest) := by
  induction n with
  | zero => simp [ones]
  | succ n ih => simp [ones_succ, ih]

theorem mem4_false : mem4 false = 4 := rfl
theorem mem4_true : mem4 true = 5 := rfl
theorem mem6_false : mem6 false = 6 := rfl
theorem mem6_true : mem6 true = 7 := rfl
theorem mem8_false : mem8 false = 8 := rfl
theorem mem8_true : mem8 true = 9 := rfl
theorem mem10_false : mem10 false = 10 := rfl
theorem mem10_true : mem10 true = 11 := rfl

theorem mem4_val (b : Bool) : (mem4 b).val = 4 + b.toNat := by
  cases b <;> simp [mem4]
theorem mem6_val (b : Bool) : (mem6 b).val = 6 + b.toNat := by
  cases b <;> simp [mem6]
theorem mem8_val (b : Bool) : (mem8 b).val = 8 + b.toNat := by
  cases b <;> simp [mem8]
theorem mem10_val (b : Bool) : (mem10 b).val = 10 + b.toNat := by
  cases b <;> simp [mem10]

theorem rule_2_zero :
    program.rule 2 0 false = some ⟨0, 2, .right⟩ := by
  simp [program]

theorem rule_2_one :
    program.rule 2 1 false = some ⟨2, 3, .right⟩ := by
  simp [program]

theorem rule_3 (b : Bool) :
    program.rule 3 (cell b) false = some ⟨2, mem4 b, .left⟩ := by
  cases b <;> simp [program, cell, mem4]

theorem rule_45_sep (b : Bool) :
    program.rule (mem4 b) 2 false = some ⟨2, mem6 b, .left⟩ := by
  cases b <;> simp [program, mem4, mem6]

theorem rule_45_bit (b : Bool) (a : Fin 3) (ha : a.val < 2) :
    program.rule (mem4 b) a false = some ⟨a, mem4 b, .left⟩ := by
  fin_cases b <;> fin_cases a <;> simp [program, mem4] at ha ⊢ <;> omega

theorem rule_67_one (b : Bool) :
    program.rule (mem6 b) 1 false = some ⟨1, mem6 b, .left⟩ := by
  cases b <;> simp [program, mem6]

theorem rule_67_zero (b : Bool) :
    program.rule (mem6 b) 0 false = some ⟨1, mem8 b, .right⟩ := by
  cases b <;> simp [program, mem6, mem8]

theorem rule_67_two (b : Bool) :
    program.rule (mem6 b) 2 false = some ⟨2, 14, .right⟩ := by
  cases b <;> simp [program, mem6]

theorem rule_89_one (b : Bool) :
    program.rule (mem8 b) 1 false = some ⟨1, mem8 b, .right⟩ := by
  cases b <;> simp [program, mem8]

theorem rule_89_two (b : Bool) :
    program.rule (mem8 b) 2 false = some ⟨2, mem10 b, .right⟩ := by
  cases b <;> simp [program, mem8, mem10]

theorem rule_1011_two (b : Bool) :
    program.rule (mem10 b) 2 false = some ⟨cell b, 3, .right⟩ := by
  cases b <;> simp [program, mem10, cell]

theorem rule_1011_bit (b : Bool) (a : Fin 3) (ha : a.val < 2) :
    program.rule (mem10 b) a false = some ⟨a, mem10 b, .right⟩ := by
  fin_cases b <;> fin_cases a <;> simp [program, mem10] at ha ⊢ <;> omega

theorem rule_14_one : program.rule 14 1 false = some ⟨1, 14, .right⟩ := by
  simp [program]

theorem rule_14_two : program.rule 14 2 false = some ⟨2, 15, .right⟩ := by
  simp [program]

theorem rule_15_two : program.rule 15 2 false = some ⟨2, 16, .left⟩ := by
  simp [program]

theorem rule_15_bit (a : Fin 3) (ha : a.val < 2) :
    program.rule 15 a false = some ⟨a, 15, .right⟩ := by
  fin_cases a <;> simp [program] at ha ⊢ <;> omega

theorem rule_16_two : program.rule 16 2 false = some ⟨2, 0, .right⟩ := by
  simp [program]

theorem rule_16_bit (a : Fin 3) (ha : a.val < 2) :
    program.rule 16 a false = some ⟨a, 16, .left⟩ := by
  fin_cases a <;> simp [program] at ha ⊢ <;> omega

theorem step2_zero (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 2 left (0 :: rest)) =
      some (head + 1, fromCells 2 (0 :: left) rest) := by
  have hh := not_halted (2 : Fin 24) left 0 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_2_zero, fromCells, applyBounded, moveHead]

theorem step2_one (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 2 left (1 :: rest)) =
      some (head + 1, fromCells 3 (2 :: left) rest) := by
  have hh := not_halted (2 : Fin 24) left 1 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_2_one, fromCells, applyBounded, moveHead]

theorem step3 (b : Bool) (head : Int) (a : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 3 (a :: left) (cell b :: rest)) =
      some (head - 1, fromCells (mem4 b) left (a :: 2 :: rest)) := by
  cases b with
  | false =>
      have hh := not_halted (3 : Fin 24) (a :: left) (cell false) rest (by omega)
      simp [fromCells, cell] at hh
      cases rest <;>
        simp [run, hh, program, fromCells, applyBounded, moveHead, cell, mem4]
  | true =>
      have hh := not_halted (3 : Fin 24) (a :: left) (cell true) rest (by omega)
      simp [fromCells, cell] at hh
      cases rest <;>
        simp [run, hh, program, fromCells, applyBounded, moveHead, cell, mem4]

theorem step45_sep (b : Bool) (head : Int) (a : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem4 b) (a :: left) (2 :: rest)) =
      some (head - 1, fromCells (mem6 b) left (a :: 2 :: rest)) := by
  have hv : 2 ≤ (mem4 b).val := by cases b <;> simp [mem4]
  have hh := not_halted (mem4 b) (a :: left) 2 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_45_sep b, fromCells, applyBounded, moveHead]

theorem step45_bit (b : Bool) (a : Fin 3) (ha : a.val < 2)
    (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem4 b) (p :: left) (a :: rest)) =
      some (head - 1, fromCells (mem4 b) left (p :: a :: rest)) := by
  have hv : 2 ≤ (mem4 b).val := by cases b <;> simp [mem4]
  have hh := not_halted (mem4 b) (p :: left) a rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_45_bit b a ha, fromCells, applyBounded, moveHead]

theorem step67_one (b : Bool) (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem6 b) (p :: left) (1 :: rest)) =
      some (head - 1, fromCells (mem6 b) left (p :: 1 :: rest)) := by
  have hv : 2 ≤ (mem6 b).val := by cases b <;> simp [mem6]
  have hh := not_halted (mem6 b) (p :: left) 1 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_67_one b, fromCells, applyBounded, moveHead]

theorem step67_zero (b : Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem6 b) left (0 :: rest)) =
      some (head + 1, fromCells (mem8 b) (1 :: left) rest) := by
  have hv : 2 ≤ (mem6 b).val := by cases b <;> simp [mem6]
  have hh := not_halted (mem6 b) left 0 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_67_zero b, fromCells, applyBounded, moveHead]

theorem step67_two (b : Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem6 b) left (2 :: rest)) =
      some (head + 1, fromCells 14 (2 :: left) rest) := by
  have hv : 2 ≤ (mem6 b).val := by cases b <;> simp [mem6]
  have hh := not_halted (mem6 b) left 2 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_67_two b, fromCells, applyBounded, moveHead]

theorem step89_one (b : Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem8 b) left (1 :: rest)) =
      some (head + 1, fromCells (mem8 b) (1 :: left) rest) := by
  have hv : 2 ≤ (mem8 b).val := by cases b <;> simp [mem8]
  have hh := not_halted (mem8 b) left 1 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_89_one b, fromCells, applyBounded, moveHead]

theorem step89_two (b : Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem8 b) left (2 :: rest)) =
      some (head + 1, fromCells (mem10 b) (2 :: left) rest) := by
  have hv : 2 ≤ (mem8 b).val := by cases b <;> simp [mem8]
  have hh := not_halted (mem8 b) left 2 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_89_two b, fromCells, applyBounded, moveHead]

theorem step1011_two (b : Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem10 b) left (2 :: rest)) =
      some (head + 1, fromCells 3 (cell b :: left) rest) := by
  have hv : 2 ≤ (mem10 b).val := by cases b <;> simp [mem10]
  have hh := not_halted (mem10 b) left 2 rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_1011_two b, fromCells, applyBounded, moveHead, cell]

theorem step1011_bit (b : Bool) (a : Fin 3) (ha : a.val < 2)
    (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells (mem10 b) left (a :: rest)) =
      some (head + 1, fromCells (mem10 b) (a :: left) rest) := by
  have hv : 2 ≤ (mem10 b).val := by cases b <;> simp [mem10]
  have hh := not_halted (mem10 b) left a rest hv
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_1011_bit b a ha, fromCells, applyBounded, moveHead]

theorem step14_one (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 14 left (1 :: rest)) =
      some (head + 1, fromCells 14 (1 :: left) rest) := by
  have hh := not_halted (14 : Fin 24) left 1 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_14_one, fromCells, applyBounded, moveHead]

theorem step14_two (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 14 left (2 :: rest)) =
      some (head + 1, fromCells 15 (2 :: left) rest) := by
  have hh := not_halted (14 : Fin 24) left 2 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_14_two, fromCells, applyBounded, moveHead]

theorem step15_two (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 15 (p :: left) (2 :: rest)) =
      some (head - 1, fromCells 16 left (p :: 2 :: rest)) := by
  have hh := not_halted (15 : Fin 24) (p :: left) 2 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_15_two, fromCells, applyBounded, moveHead]

theorem step15_bit (a : Fin 3) (ha : a.val < 2)
    (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 15 left (a :: rest)) =
      some (head + 1, fromCells 15 (a :: left) rest) := by
  have hh := not_halted (15 : Fin 24) left a rest (by omega)
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_15_bit a ha, fromCells, applyBounded, moveHead]

theorem step16_two (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 16 left (2 :: rest)) =
      some (head + 1, fromCells 0 (2 :: left) rest) := by
  have hh := not_halted (16 : Fin 24) left 2 rest (by omega)
  simp [fromCells] at hh
  cases rest <;> simp [run, hh, rule_16_two, fromCells, applyBounded, moveHead]

theorem step16_bit (a : Fin 3) (ha : a.val < 2)
    (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 16 (p :: left) (a :: rest)) =
      some (head - 1, fromCells 16 left (p :: a :: rest)) := by
  have hh := not_halted (16 : Fin 24) (p :: left) a rest (by omega)
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_16_bit a ha, fromCells, applyBounded, moveHead]

theorem cell_val_lt (b : Bool) : (cell b).val < 2 := by
  cases b <;> simp [cell]

theorem drop_cons_get {α : Type*} (l : List α) (i : Nat) (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons _ _ => rfl
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons _ ls =>
          have ht : i < ls.length := by simp at hi; omega
          simpa [List.drop] using ih ls ht

theorem scan2_zeros (k : Nat) (head : Int) (left rest : List (Fin 3)) :
    run program 2 (List.replicate k false) head
      (fromCells 2 left (zeros k ++ rest)) =
      some (head + k, fromCells 2 (zeros k ++ left) rest) := by
  induction k generalizing head left with
  | zero => simp [run, zeros]
  | succ k ih =>
      have hw : List.replicate (k + 1) false =
          [false] ++ List.replicate k false := by
        simp [List.replicate_succ]
      rw [hw, run_append, zeros_succ, List.cons_append, step2_zero, bind_run]
      exact (ih (head + 1) (0 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [zeros_succ, replicate_snoc_zero]

theorem headerL_zero (n : Nat) : headerL n 0 = zeros n := rfl

theorem headerL_all (n : Nat) : headerL n n = ones n := by
  simp [headerL, zeros]

theorem headerL_succ (n i : Nat) (hi : i < n) :
    headerL n i = ones i ++ 0 :: zeros (n - i - 1) := by
  have hpos : n - i = Nat.succ (n - i - 1) := by omega
  unfold headerL
  rw [hpos, zeros_succ, Nat.succ_sub_one]

theorem ones_length (i : Nat) : (ones i).length = i := by
  simp [ones]

theorem zeros_length (i : Nat) : (zeros i).length = i := by
  simp [zeros]

theorem ones_comm_one (k : Nat) (rest : List (Fin 3)) :
    ones k ++ 1 :: rest = 1 :: ones k ++ rest := by
  induction k with
  | zero => simp [ones]
  | succ k ih => simp [ones_succ, ih]

theorem cells_val_lt (xs : List Bool) : ∀ a ∈ cells xs, a.val < 2 := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact cell_val_lt b

theorem cells_reverse (xs : List Bool) :
    (cells xs).reverse = cells xs.reverse := by
  simp [cells]

theorem take_concat (x : List Bool) (i : Nat) (hi : i < x.length) :
    x.take i ++ [x[i]] = x.take (i + 1) := by
  induction i generalizing x with
  | zero =>
      cases x with
      | nil => simp at hi
      | cons _ _ => rfl
  | succ i ih =>
      cases x with
      | nil => simp at hi
      | cons b bs =>
          have ht : i < bs.length := by simp at hi; omega
          simpa [List.take] using congrArg (List.cons b) (ih bs ht)

theorem cursorLeft_zero (x : List Bool) (under : List (Fin 3)) :
    cursorLeft x under 0 = 2 :: zeros x.length ++ 2 :: under := by
  simp [cursorLeft, headerL_zero, cells, List.take]

theorem cursorTape_get (x : List Bool) (buffer : List (Fin 3)) (i : Nat)
    (hi : i < x.length) :
    cursorTape x buffer i =
      cell x[i] :: (cells (x.drop (i + 1)) ++ 0 :: buffer) := by
  rw [cursorTape, drop_cons_get x i hi, cells_cons, List.cons_append]

theorem init_run (x : List Bool) (under buffer : List (Fin 3)) (head : Int) :
    run program 2 (List.replicate (x.length + 1) false) head
      (initial x under buffer) =
      some (head + x.length + 1, atCursor x under buffer 0) := by
  have hw : List.replicate (x.length + 1) false =
      List.replicate x.length false ++ [false] := by
    simp [List.replicate_add]
  have hscan :=
    scan2_zeros x.length head (2 :: under) (1 :: (cells x ++ 0 :: buffer))
  have hstep :=
    step2_one (head + x.length) (zeros x.length ++ 2 :: under)
      (cells x ++ 0 :: buffer)
  rw [initial, hw, run_append, show List.replicate x.length (0 : Fin 3) = zeros x.length from rfl,
    hscan, bind_run, hstep]
  apply congrArg some
  apply Prod.ext
  · omega
  · simp [atCursor, cursorLeft_zero, cursorTape]

/-- LEFT through `a :: as` (nearest-first), starting ON `a`. -/
theorem scan45_cells (b : Bool) (a : Fin 3) (as : List (Fin 3))
    (ha : a.val < 2) (has : ∀ x ∈ as, x.val < 2)
    (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 (List.replicate (as.length + 1) false) head
      (fromCells (mem4 b) (as ++ p :: left) (a :: rest)) =
      some (head - (as.length + 1 : Int),
        fromCells (mem4 b) left (p :: as.reverse ++ a :: rest)) := by
  induction as generalizing a ha head rest with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, List.replicate_succ,
        List.replicate_zero, List.nil_append, List.reverse_nil]
      exact step45_bit b a ha head p left rest
  | cons c cs ih =>
      have hc : c.val < 2 := has c (by simp)
      have hcs : ∀ x ∈ cs, x.val < 2 := fun x hx => has x (by simp [hx])
      rw [List.length_cons]
      have hw : List.replicate (cs.length + 1 + 1) false =
          [false] ++ List.replicate (cs.length + 1) false := by
        simp [List.replicate_succ]
      rw [hw, run_append, List.cons_append,
        step45_bit b a ha head c (cs ++ p :: left) rest, bind_run]
      exact (ih c hc hcs (head - 1) (a :: rest)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons, List.append_assoc]

theorem scan67_ones (b : Bool) (k : Nat)
    (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 (List.replicate (k + 1) false) head
      (fromCells (mem6 b) (ones k ++ p :: left) (1 :: rest)) =
      some (head - (k + 1 : Int),
        fromCells (mem6 b) left (p :: ones (k + 1) ++ rest)) := by
  induction k generalizing head rest with
  | zero =>
      simp [ones]
      exact step67_one b head p left rest
  | succ k ih =>
      have hw : List.replicate (k + 1 + 1) false =
          [false] ++ List.replicate (k + 1) false := by
        simp [List.replicate_succ]
      rw [hw, run_append, ones_succ, List.cons_append,
        step67_one b head 1 (ones k ++ p :: left) rest, bind_run]
      exact (ih (head - 1) (1 :: rest)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [ones_succ, ones_comm_one]

theorem scan89_ones (b : Bool) (k : Nat) (head : Int)
    (left rest : List (Fin 3)) :
    run program 2 (List.replicate k false) head
      (fromCells (mem8 b) left (ones k ++ rest)) =
      some (head + k, fromCells (mem8 b) (ones k ++ left) rest) := by
  induction k generalizing head left with
  | zero => simp [run, ones]
  | succ k ih =>
      have hw : List.replicate (k + 1) false =
          [false] ++ List.replicate k false := by
        simp [List.replicate_succ]
      rw [hw, run_append, ones_succ, List.cons_append,
        step89_one b head left (ones k ++ rest), bind_run]
      exact (ih (head + 1) (1 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [ones_succ, replicate_snoc_one]

theorem scan1011_bits (b : Bool) (xs : List Bool) (head : Int)
    (left rest : List (Fin 3)) :
    run program 2 (List.replicate xs.length false) head
      (fromCells (mem10 b) left (cells xs ++ rest)) =
      some (head + xs.length,
        fromCells (mem10 b) ((cells xs).reverse ++ left) rest) := by
  induction xs generalizing head left with
  | nil => simp [run, cells]
  | cons y ys ih =>
      have ha : (cell y).val < 2 := cell_val_lt y
      have hw : List.replicate (ys.length + 1) false =
          [false] ++ List.replicate ys.length false := by
        simp [List.replicate_succ]
      rw [List.length_cons, hw, run_append, cells_cons, List.cons_append,
        step1011_bit b (cell y) ha head left (cells ys ++ rest), bind_run]
      exact (ih (head + 1) (cell y :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [cells_cons, List.reverse_cons]

theorem scan14_ones (k : Nat) (head : Int) (left rest : List (Fin 3)) :
    run program 2 (List.replicate k false) head
      (fromCells 14 left (ones k ++ rest)) =
      some (head + k, fromCells 14 (ones k ++ left) rest) := by
  induction k generalizing head left with
  | zero => simp [run, ones]
  | succ k ih =>
      have hw : List.replicate (k + 1) false =
          [false] ++ List.replicate k false := by
        simp [List.replicate_succ]
      rw [hw, run_append, ones_succ, List.cons_append,
        step14_one head left (ones k ++ rest), bind_run]
      exact (ih (head + 1) (1 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [ones_succ, replicate_snoc_one]

theorem scan15_bits (xs : List Bool) (head : Int) (left rest : List (Fin 3)) :
    run program 2 (List.replicate xs.length false) head
      (fromCells 15 left (cells xs ++ rest)) =
      some (head + xs.length,
        fromCells 15 ((cells xs).reverse ++ left) rest) := by
  induction xs generalizing head left with
  | nil => simp [run, cells]
  | cons y ys ih =>
      have ha : (cell y).val < 2 := cell_val_lt y
      have hw : List.replicate (ys.length + 1) false =
          [false] ++ List.replicate ys.length false := by
        simp [List.replicate_succ]
      rw [List.length_cons, hw, run_append, cells_cons, List.cons_append,
        step15_bit (cell y) ha head left (cells ys ++ rest), bind_run]
      exact (ih (head + 1) (cell y :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [cells_cons, List.reverse_cons]

theorem scan16_cells (a : Fin 3) (as : List (Fin 3))
    (ha : a.val < 2) (has : ∀ x ∈ as, x.val < 2)
    (head : Int) (p : Fin 3) (left rest : List (Fin 3)) :
    run program 2 (List.replicate (as.length + 1) false) head
      (fromCells 16 (as ++ p :: left) (a :: rest)) =
      some (head - (as.length + 1 : Int),
        fromCells 16 left (p :: as.reverse ++ a :: rest)) := by
  induction as generalizing a ha head rest with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, List.replicate_succ,
        List.replicate_zero, List.nil_append, List.reverse_nil]
      exact step16_bit a ha head p left rest
  | cons c cs ih =>
      have hc : c.val < 2 := has c (by simp)
      have hcs : ∀ x ∈ cs, x.val < 2 := fun x hx => has x (by simp [hx])
      rw [List.length_cons]
      have hw : List.replicate (cs.length + 1 + 1) false =
          [false] ++ List.replicate (cs.length + 1) false := by
        simp [List.replicate_succ]
      rw [hw, run_append, List.cons_append,
        step16_bit a ha head c (cs ++ p :: left) rest, bind_run]
      exact (ih c hc hcs (head - 1) (a :: rest)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons, List.append_assoc]

theorem reverse_take_succ (x : List Bool) (j : Nat) (hj : j < x.length) :
    (cells (x.take (j + 1))).reverse =
      cell x[j] :: (cells (x.take j)).reverse := by
  rw [← take_concat x j hj, cells_append, cells_cons, cells_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil]
  simp [List.singleton_append]

theorem cells_take_concat (x : List Bool) (j : Nat) (hj : j < x.length) :
    cells (x.take j) ++ [cell x[j]] = cells (x.take (j + 1)) := by
  rw [← take_concat x j hj, cells_append]
  simp [cells]

theorem take_len (x : List Bool) (j : Nat) (hj : j ≤ x.length) :
    (x.take j).length = j :=
  List.length_take_of_le hj

theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by
  simp

theorem fromCells_cons_append {ns : Nat} (q : Fin ns) (a : Fin 3)
    (as bs right : List (Fin 3)) :
    fromCells q (a :: as ++ bs) right = fromCells q (a :: (as ++ bs)) right := by
  refine fromCells_eq rfl ?_ rfl
  simp [List.cons_append]

theorem fromCells_right_cons {ns : Nat} (q : Fin ns) (left : List (Fin 3))
    (a : Fin 3) (as bs : List (Fin 3)) :
    fromCells q left (a :: as ++ bs) = fromCells q left (a :: (as ++ bs)) := by
  refine fromCells_eq rfl rfl (by simp [List.cons_append])

theorem take_all (x : List Bool) : x.take x.length = x :=
  List.take_length

theorem drop_all (x : List Bool) : x.drop x.length = [] :=
  List.drop_length

theorem ones_snoc (i : Nat) : ones i ++ [1] = ones (i + 1) := by
  unfold ones
  have h : List.replicate (i + 1) (1 : Fin 3) =
      List.replicate i 1 ++ List.replicate 1 1 :=
    List.replicate_add i 1 1
  simpa using h.symm

theorem headerL_snoc (n i : Nat) (_hi : i < n) :
    ones i ++ 1 :: zeros (n - i - 1) = headerL n (i + 1) := by
  have hsub : n - (i + 1) = n - i - 1 := by omega
  unfold headerL
  rw [hsub, ← ones_snoc, List.append_assoc]
  rfl

def roundSlots (i : Nat) : List Bool :=
  [false] ++ (List.replicate i false ++ ([false] ++ (List.replicate i false ++
    ([false] ++ (List.replicate i false ++ ([false] ++ (List.replicate i false ++
      [false])))))))

def failSlots (n : Nat) : List Bool :=
  [false] ++ (List.replicate n false ++ ([false] ++ (List.replicate n false ++
    ([false] ++ (List.replicate n false ++ ([false] ++ (List.replicate n false ++
      ([false] ++ (List.replicate n false ++ [false])))))))))

theorem roundSlots_length (i : Nat) : (roundSlots i).length = roundCost i := by
  simp [roundSlots, roundCost]
  omega

theorem failSlots_length (n : Nat) : (failSlots n).length = failCost n := by
  simp [failSlots, failCost]
  omega

theorem roundSlots_false (i : Nat) : ∀ a ∈ roundSlots i, a = false := by
  intro a ha
  simp [roundSlots] at ha
  tauto

theorem failSlots_false (n : Nat) : ∀ a ∈ failSlots n, a = false := by
  intro a ha
  simp [failSlots] at ha
  tauto

theorem roundWord (i : Nat) :
    List.replicate (roundCost i) false = roundSlots i := by
  have hl := roundSlots_length i
  have heq : roundSlots i = List.replicate (roundSlots i).length false :=
    List.eq_replicate_iff.mpr ⟨rfl, roundSlots_false i⟩
  rw [heq, hl]

theorem failWord (n : Nat) :
    List.replicate (failCost n) false = failSlots n := by
  have hl := failSlots_length n
  have heq : failSlots n = List.replicate (failSlots n).length false :=
    List.eq_replicate_iff.mpr ⟨rfl, failSlots_false n⟩
  rw [heq, hl]

theorem atCursor_succ_eq (x : List Bool) (under buffer : List (Fin 3))
    (j : Nat) (hj : j + 1 < x.length) :
    atCursor x under buffer (j + 1) =
      fromCells 3
        ((cells (x.take (j + 1))).reverse ++
          2 :: headerL x.length (j + 1) ++ 2 :: under)
        (cell x[j + 1] :: (cells (x.drop (j + 2)) ++ 0 :: buffer)) := by
  exact fromCells_eq rfl rfl (cursorTape_get x buffer (j + 1) hj)

theorem copy_round_zero (b : Bool) (xs : List Bool)
    (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate (roundCost 0) false) h
      (atCursor (b :: xs) under buffer 0) =
      some (h + 1, atCursor (b :: xs) under buffer 1) := by
  rw [roundWord, roundSlots, List.replicate_zero]
  simp only [List.nil_append]
  have hcfg :
      atCursor (b :: xs) under buffer 0 =
        fromCells 3 (2 :: (zeros (xs.length + 1) ++ 2 :: under))
          (cell b :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ ?_
    · rw [cursorLeft_zero, List.length_cons, List.cons_append]
    · simp [cursorTape, cells_cons]
  rw [hcfg]
  have hmark :=
    step3 b h 2 (zeros (xs.length + 1) ++ 2 :: under)
      (cells xs ++ 0 :: buffer)
  rw [run_append, hmark, bind_run]
  have hz :
      fromCells (mem4 b) (zeros (xs.length + 1) ++ 2 :: under)
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) =
        fromCells (mem4 b) (0 :: (zeros xs.length ++ 2 :: under))
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ rfl
    rw [zeros_succ, List.cons_append]
  rw [hz]
  have hsep :=
    step45_sep b (h - 1) 0 (zeros xs.length ++ 2 :: under)
      (2 :: (cells xs ++ 0 :: buffer))
  rw [run_append, hsep, bind_run]
  have hfresh :=
    step67_zero b (h - 1 - 1) (zeros xs.length ++ 2 :: under)
      (2 :: 2 :: (cells xs ++ 0 :: buffer))
  rw [run_append, hfresh, bind_run]
  have hsepr :=
    step89_two b (h - 1 - 1 + 1) (1 :: zeros xs.length ++ 2 :: under)
      (2 :: (cells xs ++ 0 :: buffer))
  have h8 :
      fromCells (mem8 b) (1 :: (zeros xs.length ++ 2 :: under))
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) =
        fromCells (mem8 b) (1 :: zeros xs.length ++ 2 :: under)
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ rfl
    simp [List.cons_append]
  rw [h8, run_append, hsepr, bind_run]
  have hrest :=
    step1011_two b (h - 1 - 1 + 1 + 1)
      (2 :: 1 :: zeros xs.length ++ 2 :: under)
      (cells xs ++ 0 :: buffer)
  have h10 :
      fromCells (mem10 b) (2 :: (1 :: zeros xs.length ++ 2 :: under))
          (2 :: (cells xs ++ 0 :: buffer)) =
        fromCells (mem10 b) (2 :: 1 :: zeros xs.length ++ 2 :: under)
          (2 :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ rfl
    simp [List.cons_append]
  rw [h10, hrest]
  apply congrArg some
  apply Prod.ext
  · omega
  · refine fromCells_eq rfl ?_ ?_
    · change _ = cursorLeft (b :: xs) under 1
      unfold cursorLeft
      rw [show (b :: xs).take 1 = [b] from rfl, cells_cons, cells_nil]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      have hh : headerL (b :: xs).length 1 = 1 :: zeros xs.length := by
        simp [headerL, ones, List.length_cons]
      rw [hh]
      simp [List.singleton_append, List.cons_append]
    · change _ = cursorTape (b :: xs) buffer 1
      simp [cursorTape, List.drop]

theorem copy_round_succ (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (j : Nat) (hj : j + 1 < x.length) :
    run program 2 (List.replicate (roundCost (j + 1)) false) h
      (atCursor x under buffer (j + 1)) =
      some (h + 1, atCursor x under buffer (j + 2)) := by
  have hi : j < x.length := by omega
  rw [atCursor_succ_eq x under buffer j hj, reverse_take_succ x j hi,
    roundWord, roundSlots]
  have hmark :=
    step3 (x[j + 1]) h (cell x[j])
      ((cells (x.take j)).reverse ++ 2 :: headerL x.length (j + 1) ++ 2 :: under)
      (cells (x.drop (j + 2)) ++ 0 :: buffer)
  have hL :
      cell x[j] :: (cells (x.take j)).reverse ++
          2 :: headerL x.length (j + 1) ++ 2 :: under =
        cell x[j] ::
          ((cells (x.take j)).reverse ++
            2 :: headerL x.length (j + 1) ++ 2 :: under) := by
    simp [List.cons_append, List.append_assoc]
  rw [hL, run_append, hmark, bind_run]
  have has : ∀ a ∈ (cells (x.take j)).reverse, a.val < 2 := by
    intro a ha
    exact cells_val_lt (x.take j) a (List.mem_reverse.mp ha)
  have hsrc :=
    scan45_cells (x[j + 1]) (cell x[j]) (cells (x.take j)).reverse
      (cell_val_lt _) has (h - 1) 2
      (headerL x.length (j + 1) ++ 2 :: under)
      (2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  have hlenas : (cells (x.take j)).reverse.length = j := by
    simp [cells_length, take_len x j (Nat.le_of_lt hi)]
  simp [hlenas, natCast_succ] at hsrc
  rw [show
      (cells (x.take j)).reverse ++ 2 :: headerL x.length (j + 1) ++ 2 :: under =
        (cells (x.take j)).reverse ++ 2 ::
          (headerL x.length (j + 1) ++ 2 :: under)
      from List.append_assoc _ _ _,
    run_append, hsrc, bind_run]
  have hleft :
      headerL x.length (j + 1) ++ 2 :: under =
        1 :: (ones j ++ zeros (x.length - (j + 1)) ++ 2 :: under) := by
    simp [headerL, ones_succ, List.cons_append]
  have hright :
      cells (x.take j) ++ cell x[j] ::
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer) =
        cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer) := by
    rw [← List.singleton_append, ← List.append_assoc, cells_take_concat x j hi]
  have hsepl :=
    step45_sep (x[j + 1]) (h - 1 - ((j : Int) + 1)) 1
      (ones j ++ zeros (x.length - (j + 1)) ++ 2 :: under)
      (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  rw [hleft]
  rw [show
      2 :: (cells (x.take j) ++ cell x[j] ::
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)) =
        2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
      from congrArg (List.cons 2) hright]
  rw [run_append, hsepl, bind_run]
  have hz : zeros (x.length - (j + 1)) =
      0 :: zeros (x.length - (j + 1) - 1) := by
    have : x.length - (j + 1) = Nat.succ (x.length - (j + 1) - 1) := by omega
    rw [this, zeros_succ, Nat.succ_sub_one]
  have hctr :=
    scan67_ones (x[j + 1]) j (h - 1 - ((j : Int) + 1) - 1) 0
      (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      (2 :: (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)))
  have hrest1 :
      1 :: 2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)) =
        1 :: (2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))) := rfl
  rw [hz, show
      ones j ++ 0 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under =
        ones j ++ 0 :: (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      from List.append_assoc _ _ _,
    ← hrest1, run_append, hctr, bind_run]
  have hfresh :=
    step67_zero (x[j + 1])
      (h - 1 - ((j : Int) + 1) - 1 - ((j : Int) + 1))
      (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      (ones (j + 1) ++ 2 :: (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)))
  rw [fromCells_right_cons (mem6 (x[j + 1]))
      (zeros (x.length - (j + 1) - 1) ++ 2 :: under) 0 (ones (j + 1))
      (2 :: (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))),
    run_append, hfresh, bind_run]
  have hfwd :=
    scan89_ones (x[j + 1]) (j + 1)
      (h - 1 - ((j : Int) + 1) - 1 - ((j : Int) + 1) + 1)
      (1 :: (zeros (x.length - (j + 1) - 1) ++ 2 :: under))
      (2 :: (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)))
  simp only [natCast_succ] at hfwd
  rw [run_append, hfwd, bind_run]
  have hsepr :=
    step89_two (x[j + 1])
      (h - 1 - ((j : Int) + 1) - 1 - ((j : Int) + 1) + 1 + ((j : Int) + 1))
      (ones (j + 1) ++ (1 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under))
      (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  have h8R :
      fromCells (mem8 (x[j + 1]))
          (ones (j + 1) ++ 1 :: (zeros (x.length - (j + 1) - 1) ++ 2 :: under))
          (2 :: (cells (x.take (j + 1)) ++
            2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))) =
        fromCells (mem8 (x[j + 1]))
          (ones (j + 1) ++ (1 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under))
          (2 :: (cells (x.take (j + 1)) ++
            2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))) := by
    refine fromCells_eq rfl ?_ rfl
    simp [List.append_assoc, List.cons_append]
  rw [h8R, run_append, hsepr, bind_run]
  have hsrcf :=
    scan1011_bits (x[j + 1]) (x.take (j + 1))
      (h - 1 - ((j : Int) + 1) - 1 - ((j : Int) + 1) + 1 + ((j : Int) + 1) + 1)
      (2 :: (ones (j + 1) ++ (1 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under)))
      (2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  have htk : (x.take (j + 1)).length = j + 1 :=
    take_len x (j + 1) (Nat.le_of_lt hj)
  simp only [htk, natCast_succ] at hsrcf
  rw [run_append, hsrcf, bind_run]
  have hrest :=
    step1011_two (x[j + 1])
      (h - 1 - ((j : Int) + 1) - 1 - ((j : Int) + 1) + 1 + ((j : Int) + 1) + 1 +
        ((j : Int) + 1))
      ((cells (x.take (j + 1))).reverse ++
        2 :: (ones (j + 1) ++ (1 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under)))
      (cells (x.drop (j + 2)) ++ 0 :: buffer)
  rw [hrest]
  apply congrArg some
  apply Prod.ext
  · omega
  · refine fromCells_eq rfl ?_ ?_
    · change _ = cursorLeft x under (j + 2)
      unfold cursorLeft
      rw [reverse_take_succ x (j + 1) hj]
      have hh : headerL x.length (j + 2) =
          ones (j + 1) ++ 1 :: zeros (x.length - (j + 1) - 1) := by
        have hsub : x.length - (j + 2) = x.length - (j + 1) - 1 := by omega
        unfold headerL
        rw [hsub, ← ones_snoc, List.append_assoc]
        simp [List.singleton_append]
      rw [hh]
      simp [List.cons_append, List.append_assoc]
    · change _ = cursorTape x buffer (j + 2)
      simp [cursorTape, List.drop]

theorem copy_round (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (i : Nat) (hi : i < x.length) :
    run program 2 (List.replicate (roundCost i) false) h
      (atCursor x under buffer i) =
      some (h + 1, atCursor x under buffer (i + 1)) := by
  cases i with
  | zero =>
      cases x with
      | nil => simp at hi
      | cons b xs => exact copy_round_zero b xs under buffer h
  | succ j =>
      simpa using copy_round_succ x under buffer h j hi

theorem copies_prefix (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (k : Nat) (hk : k ≤ x.length) :
    run program 2 (List.replicate (copiesCost k) false) h
      (atCursor x under buffer 0) =
      some (h + k, atCursor x under buffer k) := by
  induction k with
  | zero => simp [copiesCost_zero, run]
  | succ k ih =>
      have hk0 : k ≤ x.length := by omega
      have hlt : k < x.length := by omega
      have hw : List.replicate (copiesCost (k + 1)) false =
          List.replicate (copiesCost k) false ++
            List.replicate (roundCost k) false := by
        rw [copiesCost_succ k, List.replicate_add]
      rw [hw, run_append, ih hk0, bind_run,
        copy_round x under buffer (h + k) k hlt]
      apply congrArg some
      apply Prod.ext
      · omega
      · rfl

theorem atCursor_done (x : List Bool) (under buffer : List (Fin 3)) :
    atCursor x under buffer x.length =
      fromCells 3 ((cells x).reverse ++ 2 :: ones x.length ++ 2 :: under)
        (0 :: buffer) := by
  refine fromCells_eq rfl ?_ ?_
  · simp [cursorLeft, headerL_all, take_all]
  · simp [cursorTape, drop_all, cells_nil]

theorem cells_reverse_last (x : List Bool) (hx : 0 < x.length) :
    (cells x).reverse =
      cell x[x.length - 1] :: (cells (x.take (x.length - 1))).reverse := by
  have hj : x.length - 1 < x.length := by omega
  have hadd : x.length - 1 + 1 = x.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
  have h := reverse_take_succ x (x.length - 1) hj
  simpa [hadd, take_all] using h

theorem fail_run_zero (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate (failCost 0) false) h
      (atCursor [] under buffer 0) =
      some (h, finalConfig [] under buffer) := by
  rw [failWord, failSlots]
  simp only [List.replicate_zero, List.nil_append]
  have hcfg : atCursor [] under buffer 0 =
      fromCells 3 (2 :: 2 :: under) (cell false :: buffer) := by
    refine fromCells_eq rfl ?_ ?_
    · simp [cursorLeft, headerL_zero, cells, zeros, List.take]
    · simp [cursorTape, cells, cell]
  rw [hcfg]
  have hm := step3 false h 2 (2 :: under) buffer
  rw [run_append, hm, bind_run]
  have hs := step45_sep false (h - 1) 2 under (2 :: buffer)
  rw [run_append, hs, bind_run]
  have ht := step67_two false (h - 1 - 1) under (2 :: 2 :: buffer)
  rw [run_append, ht, bind_run]
  have h14 := step14_two (h - 1 - 1 + 1) (2 :: under) (2 :: buffer)
  rw [run_append, h14, bind_run]
  have h15 := step15_two (h - 1 - 1 + 1 + 1) 2 (2 :: under) buffer
  rw [run_append, h15, bind_run]
  have h16 := step16_two (h - 1 - 1 + 1 + 1 - 1) (2 :: under) (2 :: buffer)
  rw [h16]
  apply congrArg some
  apply Prod.ext
  · omega
  · simp [finalConfig, ones, cells]

theorem fail_run_pos (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (hx : 0 < x.length) :
    run program 2 (List.replicate (failCost x.length) false) h
      (atCursor x under buffer x.length) =
      some (h - x.length, finalConfig x under buffer) := by
  rw [failWord, failSlots, atCursor_done]
  have hrev := cells_reverse_last x hx
  have hL :
      (cells x).reverse ++ 2 :: ones x.length ++ 2 :: under =
        cell x[x.length - 1] ::
          ((cells (x.take (x.length - 1))).reverse ++
            2 :: ones x.length ++ 2 :: under) := by
    rw [hrev]
    simp [List.cons_append, List.append_assoc]
  rw [hL]
  have htape0 :
      fromCells (3 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              2 :: ones x.length ++ 2 :: under))
          (0 :: buffer) =
        fromCells (3 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              2 :: ones x.length ++ 2 :: under))
          (cell false :: buffer) := by
    refine fromCells_eq rfl rfl ?_
    simp [cell]
  rw [htape0]
  have hm :=
    step3 false h (cell x[x.length - 1])
      ((cells (x.take (x.length - 1))).reverse ++
        2 :: ones x.length ++ 2 :: under) buffer
  rw [run_append, hm, bind_run]
  have has : ∀ a ∈ (cells (x.take (x.length - 1))).reverse, a.val < 2 := by
    intro a ha
    exact cells_val_lt (x.take (x.length - 1)) a (List.mem_reverse.mp ha)
  have hsrc :=
    scan45_cells false (cell x[x.length - 1])
      (cells (x.take (x.length - 1))).reverse (cell_val_lt _) has
      (h - 1) 2 (ones x.length ++ 2 :: under) (2 :: buffer)
  have hlenas : (cells (x.take (x.length - 1))).reverse.length =
      x.length - 1 := by
    simp [cells_length, take_len x (x.length - 1) (Nat.sub_le _ _)]
  have hk1 : (x.length - 1) + 1 = x.length :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
  simp only [hlenas] at hsrc
  rw [← natCast_succ (x.length - 1), hk1] at hsrc
  have hL2 :
      (cells (x.take (x.length - 1))).reverse ++
          2 :: ones x.length ++ 2 :: under =
        (cells (x.take (x.length - 1))).reverse ++
          2 :: (ones x.length ++ 2 :: under) :=
    List.append_assoc _ _ _
  rw [hL2, run_append, hsrc, bind_run]
  have htk :
      cells (x.take (x.length - 1)) ++ [cell x[x.length - 1]] = cells x := by
    have hj : x.length - 1 < x.length := by omega
    have hadd : x.length - 1 + 1 = x.length :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
    simpa [hadd, take_all] using cells_take_concat x (x.length - 1) hj
  have hsepl :=
    step45_sep false (h - 1 - (x.length : Int)) 1
      (ones (x.length - 1) ++ 2 :: under)
      (cells x ++ 2 :: buffer)
  have hones : ones x.length = 1 :: ones (x.length - 1) := by
    rw [← hk1]
    exact ones_succ (x.length - 1)
  rw [hones]
  have hseplCfg :
      fromCells (mem4 false)
          (1 :: ones (x.length - 1) ++ 2 :: under)
          (2 :: (cells (x.take (x.length - 1))).reverse.reverse ++
            cell x[x.length - 1] :: 2 :: buffer) =
        fromCells (mem4 false)
          (1 :: (ones (x.length - 1) ++ 2 :: under))
          (2 :: (cells x ++ 2 :: buffer)) := by
    refine fromCells_eq rfl ?_ ?_
    · simp [List.cons_append]
    · simp [List.reverse_reverse, List.cons_append]
      rw [← List.singleton_append, ← List.append_assoc, htk]
  rw [hseplCfg, run_append, hsepl, bind_run]
  have hctr :=
    scan67_ones false (x.length - 1) (h - 1 - (x.length : Int) - 1) 2
      under (2 :: (cells x ++ 2 :: buffer))
  simp only [hk1] at hctr
  rw [← natCast_succ (x.length - 1), hk1] at hctr
  rw [show
      1 :: 2 :: (cells x ++ 2 :: buffer) =
        1 :: (2 :: (cells x ++ 2 :: buffer)) from rfl,
    run_append, hctr, bind_run]
  have hturn :=
    step67_two false (h - 1 - (x.length : Int) - 1 - (x.length : Int))
      under (ones x.length ++ 2 :: (cells x ++ 2 :: buffer))
  have honesR :
      fromCells (mem6 false) under
          (2 :: ones x.length ++ 2 :: (cells x ++ 2 :: buffer)) =
        fromCells (mem6 false) under
          (2 :: (ones x.length ++ 2 :: (cells x ++ 2 :: buffer))) :=
    fromCells_right_cons (mem6 false) under 2 (ones x.length)
      (2 :: (cells x ++ 2 :: buffer))
  rw [honesR, run_append, hturn, bind_run]
  have hfwd :=
    scan14_ones x.length
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1)
      (2 :: under) (2 :: (cells x ++ 2 :: buffer))
  rw [run_append, hfwd, bind_run]
  have h14 :=
    step14_two
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1 +
        x.length)
      (ones x.length ++ 2 :: under) (cells x ++ 2 :: buffer)
  have h14L :
      fromCells (14 : Fin 24) (ones x.length ++ 2 :: under)
          (2 :: (cells x ++ 2 :: buffer)) =
        fromCells (14 : Fin 24) (ones x.length ++ 2 :: under)
          (2 :: (cells x ++ 2 :: buffer)) := rfl
  rw [run_append, h14, bind_run]
  have hsrcf :=
    scan15_bits x
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1 +
        x.length + 1)
      (2 :: ones x.length ++ 2 :: under) (2 :: buffer)
  have h15L :
      fromCells (15 : Fin 24) (2 :: (ones x.length ++ 2 :: under))
          (cells x ++ 2 :: buffer) =
        fromCells (15 : Fin 24) (2 :: ones x.length ++ 2 :: under)
          (cells x ++ 2 :: buffer) := by
    refine fromCells_eq rfl ?_ rfl
    simp [List.cons_append]
  rw [h15L, run_append, hsrcf, bind_run]
  have h15 :=
    step15_two
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1 +
        x.length + 1 + x.length)
      (cell x[x.length - 1])
      ((cells (x.take (x.length - 1))).reverse ++
        (2 :: ones x.length ++ 2 :: under)) buffer
  have h15R :
      fromCells (15 : Fin 24)
          ((cells x).reverse ++ (2 :: ones x.length ++ 2 :: under))
          (2 :: buffer) =
        fromCells (15 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              (2 :: ones x.length ++ 2 :: under)))
          (2 :: buffer) := by
    refine fromCells_eq rfl ?_ rfl
    rw [hrev]
    simp [List.cons_append]
  rw [h15R, run_append, h15, bind_run]
  have hback :=
    scan16_cells (cell x[x.length - 1])
      (cells (x.take (x.length - 1))).reverse (cell_val_lt _) has
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1 +
        x.length + 1 + x.length - 1)
      2 (ones x.length ++ 2 :: under) (2 :: buffer)
  simp only [hlenas, hk1] at hback
  rw [← natCast_succ (x.length - 1), hk1] at hback
  have hbackL :
      (cells (x.take (x.length - 1))).reverse ++
          (2 :: ones x.length ++ 2 :: under) =
        (cells (x.take (x.length - 1))).reverse ++
          2 :: (ones x.length ++ 2 :: under) := by
    simp [List.cons_append]
  rw [hbackL, run_append, hback, bind_run]
  have h16 :=
    step16_two
      (h - 1 - (x.length : Int) - 1 - (x.length : Int) + 1 +
        x.length + 1 + x.length - 1 - (x.length : Int))
      (ones x.length ++ 2 :: under) (cells x ++ 2 :: buffer)
  have h16R :
      fromCells (16 : Fin 24) (ones x.length ++ 2 :: under)
          (2 :: (cells (x.take (x.length - 1))).reverse.reverse ++
            cell x[x.length - 1] :: 2 :: buffer) =
        fromCells (16 : Fin 24) (ones x.length ++ 2 :: under)
          (2 :: (cells x ++ 2 :: buffer)) := by
    refine fromCells_eq rfl rfl ?_
    simp [List.reverse_reverse, List.cons_append]
    rw [← List.singleton_append, ← List.append_assoc, htk]
  rw [h16R, h16]
  apply congrArg some
  apply Prod.ext
  · omega
  · refine fromCells_eq rfl ?_ rfl
    simp [finalConfig, List.cons_append]

theorem fail_run (x : List Bool) (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate (failCost x.length) false) h
      (atCursor x under buffer x.length) =
      some (h - x.length, finalConfig x under buffer) := by
  cases x with
  | nil => simpa using fail_run_zero under buffer h
  | cons b xs => exact fail_run_pos (b :: xs) under buffer h (Nat.succ_pos _)

theorem delimiter_run (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) :
    run program 2 (List.replicate (deadline x.length) false) H
      (initial x under buffer) =
      some (H + x.length + 1, finalConfig x under buffer) := by
  have hw : List.replicate (deadline x.length) false =
      List.replicate (x.length + 1) false ++
        (List.replicate (copiesCost x.length) false ++
          List.replicate (failCost x.length) false) := by
    rw [deadline_split, List.replicate_add, List.replicate_add, List.append_assoc]
  rw [hw, run_append, init_run, bind_run]
  rw [run_append, copies_prefix x under buffer (H + x.length + 1) x.length le_rfl,
    bind_run, fail_run x under buffer (H + x.length + 1 + x.length)]
  apply congrArg some
  apply Prod.ext
  · omega
  · rfl

theorem compiled_symbols :
    ∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded program hr
  exact ⟨hb.2.1, hb.2.2.1⟩

end PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
