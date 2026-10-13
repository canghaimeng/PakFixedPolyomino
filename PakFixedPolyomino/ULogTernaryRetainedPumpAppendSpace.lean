import PakFixedPolyomino.ULogTernaryRetainedPumpInitializationSpace
import PakFixedPolyomino.ULogTernaryRetainedPumpAppend

/-! Occupied decoded space of EVERY successful raw prefix of the actual
ready5-to-carry3 ternary append macro, with explicit local cutoff
`2 * bs.length + 2 * (source.length + m) + 5`. Scans split at internal
blank 2. Includes empty counter, empty source and m = 0. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpAppendSpace

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open ULogTernaryRetainedPumpAppend
open ULogTernaryRetainedPumpInitializationSpace
  (cellCount pump_falseOnly cells_length every_initial_prefix_space)
open ULogFiniteAlphabetDeterministicRuns

theorem payload_length (source : List Bool) (m : Nat) :
    (cells source ++ List.replicate m (0 : Fin 3)).length =
      source.length + m := by
  simp [cells]

theorem replicate_concat (n m : Nat) :
    List.replicate (n + m) false =
      List.replicate n false ++ List.replicate m false :=
  List.replicate_add n m false

theorem replicate_snoc (n : Nat) :
    List.replicate (n + 1) false = List.replicate n false ++ [false] := by
  simpa using replicate_concat n 1

theorem cellCount_nil (q : Fin 10) (left : List (Fin 3)) :
    cellCount (fromCells q left []) = left.length + 1 := by
  simp [cellCount, fromCells]

theorem cellCount_cons (q : Fin 10) (left : List (Fin 3)) (a : Fin 3)
    (rest : List (Fin 3)) :
    cellCount (fromCells q left (a :: rest)) = left.length + rest.length + 1 := by
  simp [cellCount, fromCells]; omega

theorem cellCount_fromCells_sentinel (q : Fin 10) (cells : List (Fin 3)) :
    cellCount (fromCells q [2] cells) ≤ cells.length + 2 := by
  cases cells with
  | nil => simp [cellCount, fromCells]
  | cons _ rest => simp [cellCount, fromCells]; omega

theorem cellCount_data (q : Fin 10) (bs source : List Bool) (m : Nat) :
    cellCount (fromCells q [2] (data bs source m)) ≤
      bs.length + source.length + m + 2 := by
  cases h : data bs source m with
  | nil =>
      have hl := congrArg List.length h
      simp [data, cells] at hl
  | cons _ rest =>
      have hl := congrArg List.length h
      simp [data, cells, cellCount, fromCells] at hl ⊢
      omega

theorem scan6_prefix (bs : List Bool) (head : Int)
    (left suffix : List (Fin 3)) (j : Nat) (hj : j ≤ bs.length) :
    run program 2 (List.replicate j false) head
      (fromCells 6 left (cells bs ++ 2 :: suffix)) =
      some (head + (j : Int),
        fromCells 6 (List.reverse (cells (bs.take j)) ++ left)
          (cells (bs.drop j) ++ 2 :: suffix)) := by
  induction bs generalizing head left j with
  | nil =>
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      simp [run, cells]
  | cons b rest ih =>
      cases j with
      | zero => simp [run, cells]
      | succ j =>
          have ha := cell_ne_two b
          have hj' : j ≤ rest.length := by
            simp at hj; omega
          have hw : List.replicate (j + 1) false =
              [false] ++ List.replicate j false := by
            simp [List.replicate_succ]
          rw [hw, run_append]
          simp only [cells, List.map_cons, List.cons_append]
          rw [step6_bit head left (List.map cell rest ++ 2 :: suffix) (cell b) ha]
          exact (ih (head + 1) (cell b :: left) j hj').trans <| by
            apply congrArg some
            apply Prod.ext
            · omega
            · simp [cells, List.take_succ_cons, List.drop_succ_cons,
                List.reverse_cons]

theorem scan6_config_space (bs : List Bool) (payload : List (Fin 3)) (j : Nat)
    (hj : j ≤ bs.length) :
    cellCount (fromCells 6 (List.reverse (cells (bs.take j)) ++ [2])
      (cells (bs.drop j) ++ 2 :: payload)) ≤
        bs.length + payload.length + 2 := by
  have htk : (cells (bs.take j)).length = j := by
    simp [cells, List.length_take, Nat.min_eq_left hj]
  cases hdrop : cells (bs.drop j) ++ 2 :: payload with
  | nil =>
      have hl := congrArg List.length hdrop
      simp at hl
  | cons _ rest =>
      have hl := congrArg List.length hdrop
      simp [cells, List.length_drop, List.length_take, Nat.min_eq_left hj] at hl
      simp [cellCount, fromCells, List.length_append, List.length_reverse, htk]
      omega

theorem run_ready_scan6 (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (j : Nat) (hj : j ≤ bs.length) :
    run program 2 (List.replicate (j + 1) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (j : Int),
        fromCells 6 (List.reverse (cells (bs.take j)) ++ [2])
          (cells (bs.drop j) ++ 2 :: payload)) := by
  have hw : List.replicate (j + 1) false =
      [false] ++ List.replicate j false := by
    simp [List.replicate_succ]
  rw [hw, run_append, ready_stay]
  exact scan6_prefix bs head [2] payload j hj

theorem run_ready_sep6 (bs : List Bool) (payload : List (Fin 3)) (head : Int) :
    run program 2 (List.replicate (bs.length + 2) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) + 1,
        fromCells 8 (2 :: (List.reverse (cells bs) ++ [2])) payload) := by
  have hw : List.replicate (bs.length + 2) false =
      List.replicate (bs.length + 1) false ++ [false] := by
    have hlen : bs.length + 2 = bs.length + 1 + 1 := by omega
    rw [hlen, replicate_snoc]
  have hs := run_ready_scan6 bs payload head bs.length (Nat.le_refl _)
  simp [List.take_length, List.drop_length] at hs
  rw [hw, run_append, hs]
  simpa [cells] using
    step6_sep (head + (bs.length : Int)) (List.reverse (cells bs) ++ [2]) payload

theorem scan8_prefix (payload : List (Fin 3)) (head : Int)
    (left : List (Fin 3)) (j : Nat) (hj : j ≤ payload.length)
    (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate j false) head (fromCells 8 left payload) =
      some (head + (j : Int),
        fromCells 8 (List.reverse (payload.take j) ++ left) (payload.drop j)) := by
  induction payload generalizing head left j with
  | nil =>
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      simp [run, fromCells]
  | cons a rest ih =>
      cases j with
      | zero => simp [run]
      | succ j =>
          have ha : a ≠ 2 := hnb a (by simp)
          have hrest : ∀ x ∈ rest, x ≠ 2 := fun x hx => hnb x (by simp [hx])
          have hj' : j ≤ rest.length := by
            simp at hj; omega
          have hw : List.replicate (j + 1) false =
              [false] ++ List.replicate j false := by
            simp [List.replicate_succ]
          rw [hw, run_append, step8_bit head left rest a ha]
          exact (ih (head + 1) (a :: left) j hj' hrest).trans <| by
            apply congrArg some
            apply Prod.ext
            · omega
            · simp [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons]

theorem scan8_config_space (bits payload : List (Fin 3)) (j : Nat)
    (hj : j ≤ payload.length) :
    cellCount (fromCells 8
      (List.reverse (payload.take j) ++ 2 :: (List.reverse bits ++ [2]))
      (payload.drop j)) ≤ bits.length + payload.length + 3 := by
  have htk : (payload.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left hj]
  cases hdrop : payload.drop j with
  | nil =>
      have hn : payload.length ≤ j := by
        have := congrArg List.length hdrop
        simp [List.length_drop] at this
        omega
      simp [cellCount, fromCells, List.length_append, List.length_reverse, htk,
        List.length_drop]
      omega
  | cons _ rest =>
      have hdl := congrArg List.length hdrop
      simp [List.length_drop] at hdl
      simp [cellCount, fromCells, List.length_append, List.length_reverse, htk]
      omega

theorem run_ready_scan8 (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (j : Nat) (hj : j ≤ payload.length) (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate (bs.length + 2 + j) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) + 1 + (j : Int),
        fromCells 8 (List.reverse (payload.take j) ++
          2 :: (List.reverse (cells bs) ++ [2])) (payload.drop j)) := by
  have hw : List.replicate (bs.length + 2 + j) false =
      List.replicate (bs.length + 2) false ++ List.replicate j false :=
    replicate_concat (bs.length + 2) j
  rw [hw, run_append, run_ready_sep6]
  exact scan8_prefix payload (head + (bs.length : Int) + 1)
    (2 :: (List.reverse (cells bs) ++ [2])) j hj hnb

def afterWrite (payload under : List (Fin 3)) : BoundedConfig 10 3 :=
  match payload.reverse with
  | [] => fromCells 9 under [2, 0]
  | a :: rest => fromCells 9 (rest ++ 2 :: under) [a, 0]

theorem run_ready_write (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate (bs.length + payload.length + 3) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1,
        afterWrite payload (List.reverse (cells bs) ++ [2])) := by
  have hlen : bs.length + payload.length + 3 =
      bs.length + 2 + payload.length + 1 := by omega
  have hw : List.replicate (bs.length + payload.length + 3) false =
      List.replicate (bs.length + 2 + payload.length) false ++ [false] := by
    rw [hlen, replicate_snoc]
  have hs := run_ready_scan8 bs payload head payload.length (Nat.le_refl _) hnb
  simp [List.take_length, List.drop_length] at hs
  rw [hw, run_append, hs]
  unfold afterWrite
  exact write_zero_payload payload (List.reverse (cells bs) ++ [2])
    (head + (bs.length : Int) + 1 + (payload.length : Int))

theorem afterWrite_space (bits payload : List (Fin 3)) :
    cellCount (afterWrite payload (List.reverse bits ++ [2])) ≤
      bits.length + payload.length + 3 := by
  cases hrev : payload.reverse with
  | nil =>
      have hp : payload = [] := by
        rw [← List.reverse_reverse payload, hrev, List.reverse_nil]
      subst hp
      simp [afterWrite, cellCount, fromCells, List.length_append,
        List.length_reverse]
  | cons _ rest =>
      have hlen : payload.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      simp [afterWrite, hrev, cellCount, fromCells, List.length_append,
        List.length_reverse]
      omega

theorem return9_prefix (stack : List (Fin 3)) (a : Fin 3)
    (under right : List (Fin 3)) (head : Int) (t : Nat)
    (ht : t ≤ stack.length) (ha : a ≠ 2) (hs : ∀ x ∈ stack, x ≠ 2) :
    run program 2 (List.replicate t false) head
      (fromCells 9 (stack ++ 2 :: under) (a :: right)) =
      some (head - (t : Int),
        fromCells 9 (stack.drop t ++ 2 :: under)
          (List.reverse (stack.take t) ++ a :: right)) := by
  induction stack generalizing a right head t with
  | nil =>
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst ht0
      simp [run]
  | cons b bs ih =>
      cases t with
      | zero => simp [run]
      | succ t =>
          have hb : b ≠ 2 := hs b (by simp)
          have hbs : ∀ x ∈ bs, x ≠ 2 := fun x hx => hs x (by simp [hx])
          have ht' : t ≤ bs.length := by
            simp at ht; omega
          have hw : List.replicate (t + 1) false =
              [false] ++ List.replicate t false := by
            simp [List.replicate_succ]
          rw [hw, run_append, List.cons_append,
            step9_bit head b (bs ++ 2 :: under) right a ha]
          exact (ih b (a :: right) (head - 1) t ht' hb hbs).trans <| by
            apply congrArg some
            apply Prod.ext
            · omega
            · simp [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons]

def afterReturn9 (payload under : List (Fin 3)) (t : Nat) : BoundedConfig 10 3 :=
  match payload.reverse with
  | [] => fromCells 9 under [2, 0]
  | a :: rest =>
      if t ≤ rest.length then
        fromCells 9 (rest.drop t ++ 2 :: under)
          (List.reverse (rest.take t) ++ [a, 0])
      else
        fromCells 9 under (2 :: List.reverse rest ++ [a, 0])

theorem run_afterWrite_prefix (payload under : List (Fin 3)) (head : Int)
    (t : Nat) (ht : t ≤ payload.length) (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate t false) head (afterWrite payload under) =
      some (head - (t : Int), afterReturn9 payload under t) := by
  cases hrev : payload.reverse with
  | nil =>
      have hp : payload = [] := by
        rw [← List.reverse_reverse payload, hrev, List.reverse_nil]
      subst hp
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst ht0
      simp [run, afterWrite, afterReturn9]
  | cons a rest =>
      have hlen : payload.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      have ha : a ≠ 2 := by
        have : a ∈ payload.reverse := by simp [hrev]
        exact hnb a (List.mem_reverse.mp this)
      have hs : ∀ x ∈ rest, x ≠ 2 := fun x hx => by
        have : x ∈ payload.reverse := by simp [hrev, hx]
        exact hnb x (List.mem_reverse.mp this)
      simp [afterWrite, afterReturn9, hrev]
      split_ifs with hle
      · exact return9_prefix rest a under [0] head t hle ha hs
      · have ht1 : t = rest.length + 1 := by omega
        subst ht1
        simpa using return9_to_delim rest a under [0] head ha hs

theorem afterReturn9_space (bits payload : List (Fin 3)) (t : Nat)
    (ht : t ≤ payload.length) :
    cellCount (afterReturn9 payload (List.reverse bits ++ [2]) t) ≤
      bits.length + payload.length + 3 := by
  cases hrev : payload.reverse with
  | nil =>
      simp [afterReturn9, hrev, cellCount_cons, List.length_append,
        List.length_reverse]
  | cons a rest =>
      have hlen : payload.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      simp [afterReturn9, hrev]
      split_ifs with hle
      · have htk : (rest.take t).length = t := by
          simp [List.length_take, Nat.min_eq_left hle]
        cases hcells : List.reverse (rest.take t) ++ [a, 0] with
        | nil =>
            have hl := congrArg List.length hcells
            simp at hl
        | cons _ xs =>
            have hx := congrArg List.length hcells
            simp [List.length_reverse, List.length_append, htk] at hx
            simp [cellCount_cons, List.length_append, List.length_reverse,
              List.length_drop]
            omega
      · simp [cellCount_cons, List.length_append, List.length_reverse]
        omega

theorem run_ready_return9 (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (t : Nat) (ht : t ≤ payload.length) (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2
      (List.replicate (bs.length + payload.length + 3 + t) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 - (t : Int),
        afterReturn9 payload (List.reverse (cells bs) ++ [2]) t) := by
  have hw : List.replicate (bs.length + payload.length + 3 + t) false =
      List.replicate (bs.length + payload.length + 3) false ++
        List.replicate t false :=
    replicate_concat (bs.length + payload.length + 3) t
  rw [hw, run_append, run_ready_write bs payload head hnb]
  exact run_afterWrite_prefix payload (List.reverse (cells bs) ++ [2])
    (head + (bs.length : Int) + 1 + (payload.length : Int) - 1) t ht hnb

theorem run_ready_focus_delim (bs : List Bool) (payload : List (Fin 3))
    (head : Int) (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2
      (List.replicate (bs.length + 2 * payload.length + 3) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) + 1 - 1,
        fromCells 9 (List.reverse (cells bs) ++ [2]) (2 :: payload ++ [0])) := by
  have hr := run_ready_return9 bs payload head payload.length (Nat.le_refl _) hnb
  have hlen : bs.length + payload.length + 3 + payload.length =
      bs.length + 2 * payload.length + 3 := by omega
  have hcfg : afterReturn9 payload (List.reverse (cells bs) ++ [2]) payload.length =
      fromCells 9 (List.reverse (cells bs) ++ [2]) (2 :: payload ++ [0]) := by
    cases hrev : payload.reverse with
    | nil =>
        have hp : payload = [] := by
          rw [← List.reverse_reverse payload, hrev, List.reverse_nil]
        subst hp
        simp [afterReturn9]
    | cons a rest =>
        have hlen' : payload.length = rest.length + 1 := by
          have := congrArg List.length hrev
          simp [List.length_reverse] at this
          omega
        have hpay : payload = List.reverse rest ++ [a] := by
          rw [← List.reverse_reverse payload, hrev, List.reverse_cons]
        unfold afterReturn9
        rw [hrev]
        have hle : ¬ payload.length ≤ rest.length := by omega
        simp [hle, hpay, List.cons_append, List.append_assoc]
  have hhead : head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
      (payload.length : Int) = head + (bs.length : Int) + 1 - 1 := by omega
  simpa [hlen, hcfg, hhead] using hr

def afterSep9 (bits right : List (Fin 3)) : BoundedConfig 10 3 :=
  match bits.reverse with
  | [] => fromCells 7 [] (2 :: 2 :: right)
  | a :: rest => fromCells 7 (rest ++ [2]) (a :: 2 :: right)

theorem run_ready_sep9 (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2
      (List.replicate (bs.length + 2 * payload.length + 4) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) - 1,
        afterSep9 (cells bs) (payload ++ [0])) := by
  have hlen : bs.length + 2 * payload.length + 4 =
      bs.length + 2 * payload.length + 3 + 1 := by omega
  have hw : List.replicate (bs.length + 2 * payload.length + 4) false =
      List.replicate (bs.length + 2 * payload.length + 3) false ++ [false] := by
    rw [hlen, replicate_snoc]
  have hf := run_ready_focus_delim bs payload head hnb
  rw [hw, run_append, hf]
  have hfocus : 2 :: payload ++ [0] = 2 :: (payload ++ [0]) := by
    simp [List.cons_append]
  have hhead0 : head + (bs.length : Int) + 1 - 1 =
      head + (bs.length : Int) := by omega
  rw [hfocus, hhead0]
  unfold afterSep9
  exact step9_sep_bits (cells bs) (payload ++ [0]) (head + (bs.length : Int))

theorem afterSep9_space (bits payload : List (Fin 3)) :
    cellCount (afterSep9 bits (payload ++ [0])) ≤
      bits.length + payload.length + 3 := by
  cases hrev : bits.reverse with
  | nil =>
      simp [afterSep9, hrev, cellCount, fromCells]
      omega
  | cons _ rest =>
      have hlen : bits.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      simp [afterSep9, hrev, cellCount, fromCells, List.length_append]
      omega

theorem return7_prefix (stack : List (Fin 3)) (a : Fin 3)
    (right : List (Fin 3)) (head : Int) (t : Nat)
    (ht : t ≤ stack.length) (ha : a ≠ 2) (hs : ∀ x ∈ stack, x ≠ 2) :
    run program 2 (List.replicate t false) head
      (fromCells 7 (stack ++ [2]) (a :: right)) =
      some (head - (t : Int),
        fromCells 7 (stack.drop t ++ [2])
          (List.reverse (stack.take t) ++ a :: right)) := by
  induction stack generalizing a right head t with
  | nil =>
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst ht0
      simp [run]
  | cons b bs ih =>
      cases t with
      | zero => simp [run]
      | succ t =>
          have hb : b ≠ 2 := hs b (by simp)
          have hbs : ∀ x ∈ bs, x ≠ 2 := fun x hx => hs x (by simp [hx])
          have ht' : t ≤ bs.length := by
            simp at ht; omega
          have hw : List.replicate (t + 1) false =
              [false] ++ List.replicate t false := by
            simp [List.replicate_succ]
          rw [hw, run_append, List.cons_append,
            step7_bit head b (bs ++ [2]) right a ha]
          exact (ih b (a :: right) (head - 1) t ht' hb hbs).trans <| by
            apply congrArg some
            apply Prod.ext
            · omega
            · simp [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons]

def afterReturn7 (bits right : List (Fin 3)) (t : Nat) : BoundedConfig 10 3 :=
  match bits.reverse with
  | [] => fromCells 7 [] (2 :: 2 :: right)
  | a :: rest =>
      if t ≤ rest.length then
        fromCells 7 (rest.drop t ++ [2])
          (List.reverse (rest.take t) ++ a :: 2 :: right)
      else
        fromCells 7 [] (2 :: List.reverse rest ++ a :: 2 :: right)

theorem run_afterSep_prefix (bits right : List (Fin 3)) (head : Int) (t : Nat)
    (ht : t ≤ bits.length) (hnb : ∀ a ∈ bits, a ≠ 2) :
    run program 2 (List.replicate t false) head (afterSep9 bits right) =
      some (head - (t : Int), afterReturn7 bits right t) := by
  cases hrev : bits.reverse with
  | nil =>
      have hb : bits = [] := by
        rw [← List.reverse_reverse bits, hrev, List.reverse_nil]
      subst hb
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst ht0
      simp [run, afterSep9, afterReturn7]
  | cons a rest =>
      have hlen : bits.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      have ha : a ≠ 2 := by
        have : a ∈ bits.reverse := by simp [hrev]
        exact hnb a (List.mem_reverse.mp this)
      have hs : ∀ x ∈ rest, x ≠ 2 := fun x hx => by
        have : x ∈ bits.reverse := by simp [hrev, hx]
        exact hnb x (List.mem_reverse.mp this)
      simp [afterSep9, afterReturn7, hrev]
      split_ifs with hle
      · exact return7_prefix rest a (2 :: right) head t hle ha hs
      · have ht1 : t = rest.length + 1 := by omega
        subst ht1
        simpa using return7_to_blank rest a (2 :: right) head ha hs

theorem afterReturn7_space (bits payload : List (Fin 3)) (t : Nat)
    (ht : t ≤ bits.length) :
    cellCount (afterReturn7 bits (payload ++ [0]) t) ≤
      bits.length + payload.length + 3 := by
  cases hrev : bits.reverse with
  | nil =>
      simp [afterReturn7, hrev, cellCount_cons]
  | cons a rest =>
      have hlen : bits.length = rest.length + 1 := by
        have := congrArg List.length hrev
        simp [List.length_reverse] at this
        omega
      simp [afterReturn7, hrev]
      split_ifs with hle
      · have htk : (rest.take t).length = t := by
          simp [List.length_take, Nat.min_eq_left hle]
        cases hcells : List.reverse (rest.take t) ++ a :: 2 :: (payload ++ [0]) with
        | nil =>
            have hl := congrArg List.length hcells
            simp at hl
        | cons _ xs =>
            have hx := congrArg List.length hcells
            simp [List.length_reverse, List.length_append, htk] at hx
            simp [cellCount_cons, List.length_append, List.length_reverse,
              List.length_drop]
            omega
      · cases hcells : 2 :: List.reverse rest ++ a :: 2 :: (payload ++ [0]) with
        | nil =>
            have hl := congrArg List.length hcells
            simp at hl
        | cons _ xs =>
            have hx := congrArg List.length hcells
            simp [List.length_reverse, List.length_append] at hx
            simp [cellCount_nil, cellCount_cons, List.length_append,
              List.length_reverse]
            omega

theorem run_ready_return7 (bs : List Bool) (payload : List (Fin 3)) (head : Int)
    (t : Nat) (ht : t ≤ bs.length) (hnb_p : ∀ a ∈ payload, a ≠ 2)
    (hnb_bs : ∀ a ∈ cells bs, a ≠ 2) :
    run program 2
      (List.replicate (bs.length + 2 * payload.length + 4 + t) false) head
      (fromCells 5 [2] (cells bs ++ 2 :: payload)) =
      some (head + (bs.length : Int) - 1 - (t : Int),
        afterReturn7 (cells bs) (payload ++ [0]) t) := by
  have hw : List.replicate (bs.length + 2 * payload.length + 4 + t) false =
      List.replicate (bs.length + 2 * payload.length + 4) false ++
        List.replicate t false :=
    replicate_concat (bs.length + 2 * payload.length + 4) t
  rw [hw, run_append, run_ready_sep9 bs payload head hnb_p]
  exact run_afterSep_prefix (cells bs) (payload ++ [0])
    (head + (bs.length : Int) - 1) t (by simpa [cells] using ht) hnb_bs

theorem cellCount_final (bs source : List Bool) (m : Nat) :
    cellCount (fromCells 3 [2] (data bs source (m + 1))) ≤
      bs.length + source.length + m + 3 := by
  have h := cellCount_data 3 bs source (m + 1)
  omega

theorem prefix_run_space (bs source : List Bool) (m : Nat) (head : Int)
    (k : Nat) (hk : k ≤ 2 * bs.length + 2 * (source.length + m) + 5) :
    ∃ hf zf,
      run program 2 (List.replicate k false) head
        (fromCells 5 [2] (data bs source m)) = some (hf, zf) ∧
      cellCount zf ≤ bs.length + source.length + m + 3 ∧
      head - 1 ≤ hf ∧
      hf ≤ head + (bs.length + source.length + m + 1 : Nat) := by
  set payload := cells source ++ List.replicate m (0 : Fin 3)
  have hp : payload.length = source.length + m := by
    simp [payload, cells]
  have hdata : data bs source m = cells bs ++ 2 :: payload := rfl
  have hnb_p : ∀ a ∈ payload, a ≠ 2 := by
    simpa [payload] using payload_ne_two source m
  have hnb_bs := cells_ne_two bs
  rw [hdata]
  if hk0 : k = 0 then
    subst hk0
    refine ⟨head, fromCells 5 [2] (cells bs ++ 2 :: payload), ?_, ?_, ?_⟩
    · simp [run]
    · have h := cellCount_fromCells_sentinel 5 (cells bs ++ 2 :: payload)
      simp [cells] at h ⊢; omega
    · omega
  else if hscan6 : k ≤ bs.length + 1 then
    have hj : k - 1 ≤ bs.length := by omega
    have hrep : k - 1 + 1 = k := by omega
    refine ⟨head + ((k - 1 : Nat) : Int),
      fromCells 6 (List.reverse (cells (bs.take (k - 1))) ++ [2])
        (cells (bs.drop (k - 1)) ++ 2 :: payload), ?_, ?_, ?_⟩
    · simpa [hrep] using run_ready_scan6 bs payload head (k - 1) hj
    · have hs := scan6_config_space bs payload (k - 1) hj
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else if hsep6 : k = bs.length + 2 then
    subst hsep6
    refine ⟨head + (bs.length : Int) + 1,
      fromCells 8 (2 :: (List.reverse (cells bs) ++ [2])) payload, ?_, ?_, ?_⟩
    · exact run_ready_sep6 bs payload head
    · cases hpay : payload with
      | nil =>
          simp [cellCount_nil, List.length_append, List.length_reverse, cells]
          omega
      | cons _ rest =>
          have hpl : payload.length = rest.length + 1 := by
            simp [hpay]
          simp [cellCount_cons, List.length_append, List.length_reverse, cells,
            hp, hpl]
          omega
    · simp [hp]; omega
  else if hscan8 : k ≤ bs.length + 2 + payload.length then
    have hj : k - (bs.length + 2) ≤ payload.length := by omega
    have hrep : bs.length + 2 + (k - (bs.length + 2)) = k := by omega
    refine ⟨head + (bs.length : Int) + 1 +
        ((k - (bs.length + 2) : Nat) : Int),
      fromCells 8 (List.reverse (payload.take (k - (bs.length + 2))) ++
        2 :: (List.reverse (cells bs) ++ [2]))
        (payload.drop (k - (bs.length + 2))), ?_, ?_, ?_⟩
    · simpa [hrep] using
        run_ready_scan8 bs payload head (k - (bs.length + 2)) hj hnb_p
    · have hs := scan8_config_space (cells bs) payload (k - (bs.length + 2)) hj
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else if hwrite : k = bs.length + payload.length + 3 then
    subst hwrite
    refine ⟨head + (bs.length : Int) + 1 + (payload.length : Int) - 1,
      afterWrite payload (List.reverse (cells bs) ++ [2]), ?_, ?_, ?_⟩
    · exact run_ready_write bs payload head hnb_p
    · have hs := afterWrite_space (cells bs) payload
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else if hret9 : k ≤ bs.length + 2 * payload.length + 3 then
    set t := k - (bs.length + payload.length + 3)
    have ht : t ≤ payload.length := by omega
    have hsplit : k = bs.length + payload.length + 3 + t := by omega
    refine ⟨head + (bs.length : Int) + 1 + (payload.length : Int) - 1 - (t : Int),
      afterReturn9 payload (List.reverse (cells bs) ++ [2]) t, ?_, ?_, ?_⟩
    · simpa [hsplit] using run_ready_return9 bs payload head t ht hnb_p
    · have hs := afterReturn9_space (cells bs) payload t ht
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else if hsep9 : k = bs.length + 2 * payload.length + 4 then
    subst hsep9
    refine ⟨head + (bs.length : Int) - 1,
      afterSep9 (cells bs) (payload ++ [0]), ?_, ?_, ?_⟩
    · exact run_ready_sep9 bs payload head hnb_p
    · have hs := afterSep9_space (cells bs) payload
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else if hret7 : k ≤ 2 * bs.length + 2 * payload.length + 4 then
    set t := k - (bs.length + 2 * payload.length + 4)
    have ht : t ≤ bs.length := by omega
    have hsplit : k = bs.length + 2 * payload.length + 4 + t := by omega
    refine ⟨head + (bs.length : Int) - 1 - (t : Int),
      afterReturn7 (cells bs) (payload ++ [0]) t, ?_, ?_, ?_⟩
    · simpa [hsplit] using
        run_ready_return7 bs payload head t ht hnb_p hnb_bs
    · have hs := afterReturn7_space (cells bs) payload t
        (by simpa [cells] using ht)
      simp [cells] at hs ⊢; omega
    · simp [hp]; omega
  else
    have hkf : k = 2 * bs.length + 2 * payload.length + 5 := by
      omega
    subst hkf
    have hlen : 2 * bs.length + 2 * payload.length + 5 =
        2 * bs.length + 2 * (source.length + m) + 5 := by
      simp [hp]
    refine ⟨head, fromCells 3 [2] (data bs source (m + 1)), ?_,
      cellCount_final bs source m, ?_⟩
    · have hr := append_run bs source m head
      rw [hdata] at hr
      simp only [payload] at hr
      simpa [hlen] using hr
    · omega

theorem every_append_prefix_space (bs source : List Bool) (m : Nat) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hlen : w.length ≤ 2 * bs.length + 2 * (source.length + m) + 5)
    (hrun : run program 2 w head (fromCells 5 [2] (data bs source m)) =
      some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤
        bs.length + source.length + m + 3 ∧
      head - 1 ≤ hf ∧
      hf ≤ head + (bs.length + source.length + m + 1 : Nat) := by
  have hw := successful_zipper_is_false (2 : Fin 3) program pump_falseOnly hrun
  rw [hw] at hrun
  obtain ⟨hf', zf', hr, hc, hlo, hhi⟩ :=
    prefix_run_space bs source m head w.length hlen
  rw [hr] at hrun
  have he : (hf', zf') = (hf, zf) := Option.some.inj hrun
  rcases he with ⟨rfl, rfl⟩
  exact ⟨hc, hlo, hhi⟩

theorem ternary_macro_space_spec :
    (∀ (k : Nat) (source : List Bool) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      w.length ≤ 2 * k + 2 →
      run program 2 w head (initial k source) = some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤ k + source.length + 2 ∧
        head - 1 ≤ hf ∧ hf ≤ head + k) ∧
    (∀ (bs source : List Bool) (m : Nat) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      w.length ≤ 2 * bs.length + 2 * (source.length + m) + 5 →
      run program 2 w head (fromCells 5 [2] (data bs source m)) =
        some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤
          bs.length + source.length + m + 3 ∧
        head - 1 ≤ hf ∧
        hf ≤ head + (bs.length + source.length + m + 1 : Nat)) :=
  ⟨every_initial_prefix_space, every_append_prefix_space⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpAppendSpace
