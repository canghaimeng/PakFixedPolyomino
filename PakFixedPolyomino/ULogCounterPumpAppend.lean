import PakFixedPolyomino.ULogCounterPump

/-! Actual ready-to-carry append/return of the fixed nine-state Fin4 pump.
One genuine zero is written at the first right blank, old nonblank cells
and the left sentinel are preserved, and the integer head is restored, in
exactly `2 * cells.length + 3` false-slot transitions. Includes the empty
payload. Exponential generation, compact loading and the original headline
remain open. -/

namespace PakFixedPolyomino.ULogCounterPumpAppend

open ULogCompiler
open ULogFiniteTapeZipperRun
open ULogCounterPump
open FiniteOneTapeSemantics (moveHead)

theorem replicate_append_word (n : Nat) :
    List.replicate (2 * n + 3) false =
      [false] ++ List.replicate n false ++ [false] ++
        List.replicate n false ++ [false] := by
  have : 2 * n + 3 = 1 + n + 1 + n + 1 := by omega
  simp [this, List.replicate_add]

theorem append_scan (cells left : List (Fin 4)) (head : Int)
    (hnb : ∀ a ∈ cells, a ≠ 2) :
    run program 2 (List.replicate cells.length false) head
      (fromCells 6 left cells) =
      some (head + (cells.length : Int),
        fromCells 6 (cells.reverse ++ left) []) := by
  induction cells generalizing left head with
  | nil => simp [run, fromCells]
  | cons a rest ih =>
      have ha : a ≠ 2 := hnb a (by simp)
      have hrest : ∀ x ∈ rest, x ≠ 2 := fun x hx => hnb x (by simp [hx])
      have hword : List.replicate (rest.length + 1) false =
          [false] ++ List.replicate rest.length false := by
        simp [List.replicate_succ]
      rw [List.length_cons, hword, run_append, append_right head left rest a ha]
      exact (ih (a :: left) (head + 1) hrest).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons]

theorem append_write_after_scan (cells : List (Fin 4)) (head : Int) :
    run program 2 [false] head
      (fromCells 6 (cells.reverse ++ [2]) []) =
      some (head - 1,
        match cells.reverse with
        | [] => fromCells 7 [] [(2 : Fin 4), 0]
        | a :: left => fromCells 7 (left ++ [2]) [a, 0]) := by
  cases hrev : cells.reverse with
  | nil =>
      simpa [hrev] using append_write_turn head (2 : Fin 4) []
  | cons a left =>
      simpa [hrev] using append_write_turn head a (left ++ [2])

theorem pump_return_to_sentinel (stack : List (Fin 4)) (a : Fin 4)
    (right : List (Fin 4)) (head : Int)
    (ha : a ≠ 2) (hs : ∀ x ∈ stack, x ≠ 2) :
    run program 2 (List.replicate (stack.length + 1) false) head
      (fromCells 7 (stack ++ [2]) (a :: right)) =
      some (head - (stack.length + 1 : Int),
        fromCells 7 [] (2 :: stack.reverse ++ a :: right)) := by
  induction stack generalizing a right head with
  | nil =>
      simpa [run, List.reverse_nil] using
        pump_return_left head [] right a 2 ha
  | cons b bs ih =>
      have hb : b ≠ 2 := hs b (by simp)
      have hbs : ∀ x ∈ bs, x ≠ 2 := fun x hx => hs x (by simp [hx])
      have hword : List.replicate (bs.length + 1 + 1) false =
          [false] ++ List.replicate (bs.length + 1) false := by
        simp [List.replicate_succ]
      have hlen : (b :: bs).length = bs.length + 1 := by simp
      rw [hlen, hword, run_append, List.cons_append,
        pump_return_left head (bs ++ [2]) right a b ha]
      exact (ih b (a :: right) (head - 1) hb hbs).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons]

theorem pump_return_after_write (cells : List (Fin 4)) (head : Int)
    (hnb : ∀ a ∈ cells, a ≠ 2) :
    run program 2 (List.replicate cells.length false) head
      (match cells.reverse with
        | [] => fromCells 7 [] [(2 : Fin 4), 0]
        | a :: left => fromCells 7 (left ++ [2]) [a, 0]) =
      some (head - (cells.length : Int),
        fromCells 7 [] (2 :: cells ++ [0])) := by
  cases hrev : cells.reverse with
  | nil =>
      have hcells : cells = [] := by
        rw [← List.reverse_reverse cells, hrev, List.reverse_nil]
      subst hcells
      simp [run]
  | cons a left =>
      have hlen : cells.length = left.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      have ha : a ≠ 2 := by
        have : a ∈ cells.reverse := by simp [hrev]
        exact hnb a (List.mem_reverse.mp this)
      have hs : ∀ x ∈ left, x ≠ 2 := fun x hx => by
        have : x ∈ cells.reverse := by simp [hrev, hx]
        exact hnb x (List.mem_reverse.mp this)
      have hcells : cells = left.reverse ++ [a] := by
        rw [← List.reverse_reverse cells, hrev, List.reverse_cons]
      rw [hlen]
      exact (pump_return_to_sentinel left a [0] head ha hs).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [hcells]

/-- Ready5 to carry3: every nonblank payload, including empty, is scanned
right, a physical zero is written at the first blank, and return restores
the original head on `fromCells 3 [2] (cells ++ [0])`. -/
theorem append_return (cells : List (Fin 4)) (head : Int)
    (hnb : ∀ a ∈ cells, a ≠ 2) :
    run program 2 (List.replicate (2 * cells.length + 3) false) head
      (fromCells 5 [2] cells) =
      some (head, fromCells 3 [2] (cells ++ [0])) := by
  have hword := replicate_append_word cells.length
  have hready := start_append head [2] cells
  have hscan :
      run program 2 ([false] ++ List.replicate cells.length false) head
        (fromCells 5 [2] cells) =
        some (head + (cells.length : Int),
          fromCells 6 (cells.reverse ++ [2]) []) := by
    rw [run_append, hready]
    exact append_scan cells [2] head hnb
  have hwrite :
      run program 2
        ([false] ++ List.replicate cells.length false ++ [false]) head
        (fromCells 5 [2] cells) =
        some (head + (cells.length : Int) - 1,
          match cells.reverse with
          | [] => fromCells 7 [] [(2 : Fin 4), 0]
          | a :: left => fromCells 7 (left ++ [2]) [a, 0]) := by
    rw [run_append, hscan]
    exact append_write_after_scan cells (head + (cells.length : Int))
  have hret :
      run program 2
        ([false] ++ List.replicate cells.length false ++ [false] ++
          List.replicate cells.length false) head
        (fromCells 5 [2] cells) =
        some (head - 1, fromCells 7 [] (2 :: cells ++ [0])) := by
    rw [run_append, hwrite]
    exact (pump_return_after_write cells
        (head + (cells.length : Int) - 1) hnb).trans <| by
      apply congrArg some
      apply Prod.ext
      · show (head + (cells.length : Int) - 1) - (cells.length : Int) =
            head - 1
        omega
      · rfl
  rw [hword, run_append, hret]
  have hblank := pump_return_blank (head - 1) (cells ++ [0])
  have hhead : ((head - 1) + 1 : Int) = head := Int.sub_add_cancel head 1
  simpa [hhead] using hblank

def bitCell : Bool → Fin 4
  | false => 0
  | true => 1

theorem bit_cells_nonblank (bits : List Bool) (m : Nat) :
    ∀ a ∈ bits.map bitCell ++ [(3 : Fin 4)] ++ List.replicate m 0, a ≠ 2 := by
  intro a ha
  fin_cases a
  · decide
  · decide
  · simp [List.mem_append, List.mem_map, List.mem_replicate, bitCell] at ha
  · decide

/-- Optional: mapped bits, a delimiter, and `m` zeros append in
`2 * k + 2 * m + 5` false-slot steps into carry3. -/
theorem bits_delimiter_zeros_append (bits : List Bool) (m : Nat) (head : Int) :
    run program 2
      (List.replicate (2 * (bits.length + 1 + m) + 3) false) head
      (fromCells 5 [2]
        (bits.map bitCell ++ [3] ++ List.replicate m 0)) =
      some (head,
        fromCells 3 [2]
          (bits.map bitCell ++ [3] ++ List.replicate m 0 ++ [0])) := by
  have hrun :=
    append_return (bits.map bitCell ++ [(3 : Fin 4)] ++ List.replicate m 0)
      head (bit_cells_nonblank bits m)
  convert hrun using 2
  simp; omega

end PakFixedPolyomino.ULogCounterPumpAppend
