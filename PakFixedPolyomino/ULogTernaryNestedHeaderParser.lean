import PakFixedPolyomino.StandardBitPolynomialPayload
import PakFixedPolyomino.StandardBitRetainedPayload
import PakFixedPolyomino.ULogTernaryRetainedCounterPump
import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! Actual finite ternary nested-header positioning parser. Fixed `d` and
`c` are bytecode parameters of `BoundedProgram (d+c+4) 3`. Positions the
head at the retained original length field. Does not delimit the end of
`x`, decode a physical frame, or prove a complete loader. -/

namespace PakFixedPolyomino.ULogTernaryNestedHeaderParser

open ULogCompiler ULogFiniteTapeZipperRun
open ULogTernaryRetainedCounterPump (cell cells)
open FiniteOneTapeSemantics (moveHead)
open StandardBitSquarePayload (squarePayload)

def counted (x : List Bool) : List Bool :=
  StandardBitRetainedPayload.payload x

def body (c : Nat) (x : List Bool) : List Bool :=
  List.replicate c false ++ counted x

def nested (d c : Nat) (x : List Bool) : List Bool :=
  StandardBitPolynomialPayload.iterateSquare d (body c x)

def header : Nat → Nat → List Bool → List Bool
  | 0, c, _ => List.replicate c false
  | d + 1, c, x =>
      List.replicate ((nested d c x).length ^ 2) false ++ true :: header d c x

def squareHeaders : Nat → Nat → List Bool → List Bool
  | 0, _, _ => []
  | d + 1, c, x =>
      List.replicate ((nested d c x).length ^ 2) false ++
        true :: squareHeaders d c x

def fromCells {ns : Nat} (q : Fin ns) (left : List (Fin 3)) :
    List (Fin 3) → BoundedConfig ns 3
  | [] => ⟨q, left, 2, []⟩
  | a :: rest => ⟨q, left, a, rest⟩

def startState (d c : Nat) : Fin (d + c + 4) :=
  ⟨2, by omega⟩

def seedState (d c : Nat) : Fin (d + c + 4) :=
  ⟨2 + d, by omega⟩

def haltState (d c : Nat) : Fin (d + c + 4) :=
  ⟨2 + d + c, by omega⟩

def acceptState (d c : Nat) : Fin (d + c + 4) :=
  ⟨0, by omega⟩

def parserProgram (d c : Nat) : BoundedProgram (d + c + 4) 3 where
  rule q read slot :=
    if slot then none
    else if hHdr : 2 ≤ q.val ∧ q.val ≤ d + 1 then
      if read = 0 then
        some ⟨0, q, .right⟩
      else if read = 1 then
        some ⟨1, ⟨q.val + 1, by omega⟩, .right⟩
      else none
    else if hSeed : 2 + d ≤ q.val ∧ q.val < 2 + d + c then
      some ⟨read, ⟨q.val + 1, by omega⟩, .right⟩
    else if q.val = 2 + d + c then
      some ⟨read, ⟨0, by omega⟩, .stay⟩
    else none

theorem rule_true (d c : Nat) (q : Fin (d + c + 4)) (read : Fin 3) :
    (parserProgram d c).rule q read true = none := by
  simp [parserProgram]

theorem counted_eq (x : List Bool) :
    counted x = List.replicate x.length false ++ true :: x :=
  StandardBitRetainedPayload.payload_eq_encode x

theorem counted_length (x : List Bool) :
    (counted x).length = 2 * x.length + 1 :=
  StandardBitRetainedPayload.payload_length x

theorem counted_ne_nil (x : List Bool) : counted x ≠ [] := by
  have h : 0 < (counted x).length := by
    simp [counted_length]
  exact List.ne_nil_of_length_pos h

theorem cells_append (as bs : List Bool) :
    cells (as ++ bs) = cells as ++ cells bs := by
  simp [cells]

theorem cells_replicate_false (n : Nat) :
    cells (List.replicate n false) = List.replicate n (0 : Fin 3) := by
  simp [cells, cell]

theorem cells_cons_true (bs : List Bool) :
    cells (true :: bs) = (1 : Fin 3) :: cells bs := by
  simp [cells, cell]

theorem cells_length (bs : List Bool) : (cells bs).length = bs.length := by
  simp [cells]

theorem header_eq_square_seed (d c : Nat) (x : List Bool) :
    header d c x = squareHeaders d c x ++ List.replicate c false := by
  induction d with
  | zero => simp [header, squareHeaders]
  | succ d ih =>
      simp [header, squareHeaders, ih, List.append_assoc]

theorem nested_eq_header_counted (d c : Nat) (x : List Bool) :
    nested d c x = header d c x ++ counted x := by
  induction d with
  | zero =>
      simp [nested, StandardBitPolynomialPayload.iterateSquare, body, header]
  | succ d ih =>
      rw [nested, StandardBitPolynomialPayload.iterateSquare, ← nested,
        squarePayload, header, ih, Nat.pow_two]
      simp [List.cons_append, List.append_assoc]

theorem nested_eq_square_seed_counted (d c : Nat) (x : List Bool) :
    nested d c x =
      squareHeaders d c x ++ List.replicate c false ++ counted x := by
  rw [nested_eq_header_counted, header_eq_square_seed, List.append_assoc]

theorem nested_length (d c : Nat) (x : List Bool) :
    (nested d c x).length =
      (header d c x).length + (counted x).length := by
  simp [nested_eq_header_counted]

theorem cells_nested (d c : Nat) (x : List Bool) :
    cells (nested d c x) = cells (header d c x) ++ cells (counted x) := by
  simp [nested_eq_header_counted, cells_append]

theorem haltState_val (d c : Nat) : (haltState d c).val = 2 + d + c := rfl

theorem startState_val (d c : Nat) : (startState d c).val = 2 := rfl

theorem not_halted_start (d c : Nat) :
    boundedHalted
      (fromCells (startState d c) ([] : List (Fin 3)) [0]) = false := by
  simp [boundedHalted, fromCells, startState]

theorem rule_header_zero (d c : Nat) (q : Fin (d + c + 4))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    (parserProgram d c).rule q 0 false = some ⟨0, q, .right⟩ := by
  dsimp [parserProgram]
  split_ifs <;> first | rfl | omega

theorem rule_header_one (d c : Nat) (q : Fin (d + c + 4))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    (parserProgram d c).rule q 1 false =
      some ⟨1, ⟨q.val + 1, by omega⟩, .right⟩ := by
  dsimp [parserProgram]
  split_ifs <;> first | rfl | omega

theorem rule_seed (d c : Nat) (q : Fin (d + c + 4)) (read : Fin 3)
    (h : 2 + d ≤ q.val ∧ q.val < 2 + d + c) :
    (parserProgram d c).rule q read false =
      some ⟨read, ⟨q.val + 1, by omega⟩, .right⟩ := by
  have hnot : ¬ (2 ≤ q.val ∧ q.val ≤ d + 1) := by omega
  dsimp [parserProgram]
  split_ifs <;> first | rfl | omega

theorem rule_halt (d c : Nat) (q : Fin (d + c + 4)) (read : Fin 3)
    (h : q.val = 2 + d + c) :
    (parserProgram d c).rule q read false =
      some ⟨read, ⟨0, by omega⟩, .stay⟩ := by
  have hnotH : ¬ (2 ≤ q.val ∧ q.val ≤ d + 1) := by omega
  have hnotS : ¬ (2 + d ≤ q.val ∧ q.val < 2 + d + c) := by omega
  dsimp [parserProgram]
  split_ifs <;> first | rfl | omega

theorem not_halted_focus (d c : Nat) (q : Fin (d + c + 4))
    (left : List (Fin 3)) (a : Fin 3) (rest : List (Fin 3))
    (h : 2 ≤ q.val) :
    boundedHalted (fromCells q left (a :: rest)) = false := by
  simp [boundedHalted, fromCells]; omega

theorem step_right_zero (d c : Nat) (q : Fin (d + c + 4))
    (head : Int) (left rest : List (Fin 3))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    run (parserProgram d c) 2 [false] head
      (fromCells q left (0 :: rest)) =
      some (head + 1, fromCells q (0 :: left) rest) := by
  have hh := not_halted_focus d c q left 0 rest h.1
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_header_zero d c q h, fromCells, applyBounded, moveHead]

theorem step_right_one (d c : Nat) (q : Fin (d + c + 4))
    (head : Int) (left rest : List (Fin 3))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    run (parserProgram d c) 2 [false] head
      (fromCells q left (1 :: rest)) =
      some (head + 1, fromCells ⟨q.val + 1, by omega⟩ (1 :: left) rest) := by
  have hh := not_halted_focus d c q left 1 rest h.1
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_header_one d c q h, fromCells, applyBounded, moveHead]

theorem step_seed (d c : Nat) (q : Fin (d + c + 4)) (a : Fin 3)
    (head : Int) (left rest : List (Fin 3))
    (h : 2 + d ≤ q.val ∧ q.val < 2 + d + c) :
    run (parserProgram d c) 2 [false] head
      (fromCells q left (a :: rest)) =
      some (head + 1, fromCells ⟨q.val + 1, by omega⟩ (a :: left) rest) := by
  have hh := not_halted_focus d c q left a rest (by omega)
  simp [fromCells] at hh
  cases rest <;>
    simp [run, hh, rule_seed d c q a h, fromCells, applyBounded, moveHead]

theorem step_halt (d c : Nat) (q : Fin (d + c + 4)) (a : Fin 3)
    (head : Int) (left rest : List (Fin 3))
    (h : q.val = 2 + d + c) :
    run (parserProgram d c) 2 [false] head
      (fromCells q left (a :: rest)) =
      some (head, fromCells (acceptState d c) left (a :: rest)) := by
  have hh := not_halted_focus d c q left a rest (by omega)
  simp [fromCells] at hh
  simp [run, hh, rule_halt d c q a h, fromCells, applyBounded, moveHead,
    acceptState]

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

theorem scan_zeros (d c : Nat) (q : Fin (d + c + 4)) (n : Nat)
    (head : Int) (left rest : List (Fin 3))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    run (parserProgram d c) 2 (List.replicate n false) head
      (fromCells q left (List.replicate n (0 : Fin 3) ++ rest)) =
      some (head + n,
        fromCells q ((List.replicate n (0 : Fin 3)).reverse ++ left) rest) := by
  induction n generalizing head left with
  | zero => simp [run]
  | succ n ih =>
      have hw : List.replicate (n + 1) false =
          [false] ++ List.replicate n false := by
        simp [List.replicate_succ]
      have hz : List.replicate (n + 1) (0 : Fin 3) =
          0 :: List.replicate n 0 := by
        simp [List.replicate_succ]
      rw [hw, hz, run_append, List.cons_append, step_right_zero d c q head left
        (List.replicate n 0 ++ rest) h, bind_run]
      exact (ih (head + 1) (0 :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.replicate_succ, List.reverse_cons]

theorem scan_square_header (d c : Nat) (q : Fin (d + c + 4)) (n : Nat)
    (head : Int) (left rest : List (Fin 3))
    (h : 2 ≤ q.val ∧ q.val ≤ d + 1) :
    run (parserProgram d c) 2
      (List.replicate (n ^ 2 + 1) false) head
      (fromCells q left
        (List.replicate (n ^ 2) (0 : Fin 3) ++ 1 :: rest)) =
      some (head + (n ^ 2 + 1 : Nat),
        fromCells ⟨q.val + 1, by omega⟩
          (1 :: (List.replicate (n ^ 2) (0 : Fin 3)).reverse ++ left) rest) := by
  have hw : List.replicate (n ^ 2 + 1) false =
      List.replicate (n ^ 2) false ++ [false] := by
    simp [List.replicate_add]
  rw [hw, run_append, scan_zeros d c q (n ^ 2) head left (1 :: rest) h, bind_run]
  exact (step_right_one d c q (head + (n ^ 2 : Nat))
      ((List.replicate (n ^ 2) (0 : Fin 3)).reverse ++ left) rest h).trans <| by
    apply congrArg some
    apply Prod.ext
    · omega
    · simp [List.cons_append]

theorem scan_seed (d c : Nat) (q : Fin (d + c + 4)) (j : Nat)
    (h : 2 + d ≤ q.val ∧ q.val + j ≤ 2 + d + c)
    (head : Int) (left rest : List (Fin 3)) :
    run (parserProgram d c) 2 (List.replicate j false) head
      (fromCells q left (List.replicate j (0 : Fin 3) ++ rest)) =
      some (head + j,
        fromCells ⟨q.val + j, by omega⟩
          ((List.replicate j (0 : Fin 3)).reverse ++ left) rest) := by
  induction j generalizing q head left with
  | zero => simp [run]
  | succ j ih =>
      have hst : 2 + d ≤ q.val ∧ q.val < 2 + d + c := by omega
      have hw : List.replicate (j + 1) false =
          [false] ++ List.replicate j false := by
        simp [List.replicate_succ]
      have hz : List.replicate (j + 1) (0 : Fin 3) =
          0 :: List.replicate j 0 := by
        simp [List.replicate_succ]
      have hq1 : q.val + 1 < d + c + 4 := by omega
      rw [hw, hz, run_append, List.cons_append,
        step_seed d c q 0 head left (List.replicate j 0 ++ rest) hst, bind_run]
      refine (ih ⟨q.val + 1, hq1⟩ ?_ (head + 1) (0 :: left)).trans ?_
      · simpa using
          (by omega : 2 + d ≤ q.val + 1 ∧ q.val + 1 + j ≤ 2 + d + c)
      · apply congrArg some
        apply Prod.ext
        · omega
        · refine fromCells_eq (Fin.ext (by ac_rfl)) ?_ rfl
          simp [List.reverse_cons]

theorem scan_squares (d c : Nat) (n : Nat) (q : Fin (d + c + 4))
    (hq : q.val + n = 2 + d) (h2 : 2 ≤ q.val) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) :
    run (parserProgram d c) 2
      (List.replicate (squareHeaders n c x).length false) head
      (fromCells q left
        (cells (squareHeaders n c x ++ List.replicate c false ++ counted x) ++
          suffix)) =
      some (head + (squareHeaders n c x).length,
        fromCells ⟨q.val + n, by omega⟩
          ((cells (squareHeaders n c x)).reverse ++ left)
          (cells (List.replicate c false ++ counted x) ++ suffix)) := by
  induction n generalizing q head left with
  | zero =>
      simp [squareHeaders, run]
      exact fromCells_eq (Fin.ext (by simp)) (by simp [cells]) rfl
  | succ n ih =>
      have hst : 2 ≤ q.val ∧ q.val ≤ d + 1 := by omega
      set L := (nested n c x).length
      have hsq : squareHeaders (n + 1) c x =
          List.replicate (L ^ 2) false ++ true :: squareHeaders n c x := by
        simp [squareHeaders, L]
      have hlen : (squareHeaders (n + 1) c x).length =
          (L ^ 2 + 1) + (squareHeaders n c x).length := by
        simp [hsq]; omega
      have hw : List.replicate (squareHeaders (n + 1) c x).length false =
          List.replicate (L ^ 2 + 1) false ++
            List.replicate (squareHeaders n c x).length false := by
        rw [hlen, List.replicate_add]
      have htape :
          cells (squareHeaders (n + 1) c x ++ List.replicate c false ++
              counted x) ++ suffix =
            List.replicate (L ^ 2) (0 : Fin 3) ++ 1 ::
              (cells (squareHeaders n c x ++ List.replicate c false ++
                counted x) ++ suffix) := by
        simp [hsq, cells_append, cells_replicate_false, cells_cons_true,
          List.append_assoc]
      have hq1 : q.val + 1 < d + c + 4 := by omega
      rw [hw, htape, run_append,
        scan_square_header d c q L head left
          (cells (squareHeaders n c x ++ List.replicate c false ++ counted x) ++
            suffix) hst, bind_run]
      refine (ih ⟨q.val + 1, hq1⟩ ?_ ?_
          (head + (L ^ 2 + 1 : Nat))
          (1 :: (List.replicate (L ^ 2) (0 : Fin 3)).reverse ++ left)).trans ?_
      · simpa using (by omega : q.val + 1 + n = 2 + d)
      · simpa using (by omega : 2 ≤ q.val + 1)
      · apply congrArg some
        apply Prod.ext
        · omega
        · refine fromCells_eq (Fin.ext (by ac_rfl)) ?_ rfl
          simp [hsq, cells_append, cells_replicate_false, cells_cons_true,
            List.reverse_cons, List.reverse_append, List.append_assoc]

theorem scan_header (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) :
    run (parserProgram d c) 2
      (List.replicate (header d c x).length false) head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
      some (head + (header d c x).length,
        fromCells (haltState d c)
          ((cells (header d c x)).reverse ++ left)
          (cells (counted x) ++ suffix)) := by
  have hsq :=
    scan_squares d c d (startState d c) (by simp [startState])
      (by simp [startState]) x head left suffix
  have hseed :=
    scan_seed d c (seedState d c) c (by simp [seedState])
      (head + (squareHeaders d c x).length)
      ((cells (squareHeaders d c x)).reverse ++ left)
      (cells (counted x) ++ suffix)
  have hw : List.replicate (header d c x).length false =
      List.replicate (squareHeaders d c x).length false ++
        List.replicate c false := by
    rw [header_eq_square_seed, List.length_append, List.length_replicate,
      List.replicate_add]
  have hnest :
      cells (nested d c x) ++ suffix =
        cells (squareHeaders d c x ++ List.replicate c false ++ counted x) ++
          suffix := by
    simp [nested_eq_square_seed_counted]
  have htape :
      cells (List.replicate c false ++ counted x) ++ suffix =
        List.replicate c (0 : Fin 3) ++ (cells (counted x) ++ suffix) := by
    simp [cells_append, cells_replicate_false]
  have hlt : (startState d c).val + d < d + c + 4 := by
    simp [startState]; omega
  have hseedq : (⟨(startState d c).val + d, hlt⟩ : Fin (d + c + 4)) =
      seedState d c :=
    Fin.ext (by simp [startState, seedState])
  rw [hw, hnest, run_append, hsq, bind_run, fromCells_eq hseedq rfl htape, hseed]
  congr 1
  apply Prod.ext
  · simp [header_eq_square_seed]; omega
  · refine fromCells_eq ?_ ?_ rfl
    · apply Fin.ext
      simp [seedState, haltState]
    · simp [header_eq_square_seed, cells_append, cells_replicate_false,
        List.reverse_append, List.append_assoc]

theorem parser_run (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) :
    run (parserProgram d c) 2
      (List.replicate ((header d c x).length + 1) false) head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
      some (head + (header d c x).length,
        fromCells (acceptState d c)
          ((cells (header d c x)).reverse ++ left)
          (cells (counted x) ++ suffix)) := by
  have hw : List.replicate ((header d c x).length + 1) false =
      List.replicate (header d c x).length false ++ [false] := by
    simp [List.replicate_add]
  rw [hw, run_append, scan_header, bind_run]
  cases hc : cells (counted x) ++ suffix with
  | nil =>
      have hl := congrArg List.length hc
      simpa [cells_length, counted_length] using hl
  | cons a rest =>
      exact step_halt d c (haltState d c) a
        (head + (header d c x).length)
        ((cells (header d c x)).reverse ++ left) rest (by simp [haltState])

theorem compiled_symbols (d c : Nat) :
    ∀ r ∈ compile (parserProgram d c),
      r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded (parserProgram d c) hr
  exact ⟨hb.2.1, hb.2.2.1⟩

theorem accept_state_zero (d c : Nat) :
    (acceptState d c).val = 0 := rfl

end PakFixedPolyomino.ULogTernaryNestedHeaderParser
