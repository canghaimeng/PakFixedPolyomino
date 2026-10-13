import PakFixedPolyomino.ULogTernaryRetainedPumpInitialization

/-! Actual ready-to-carry append of the ternary retained pump. State 5 STAY 6;
6 scans binary counter cells to delimiter 2 then RIGHT 8; 8 scans source and
existing zeros to the first external blank, writes a genuine 0 and LEFT 9;
9 returns to delimiter 2 then LEFT 7; 7 returns to the left blank then RIGHT 3.
Source is preserved byte-for-byte. Includes empty counter, empty source and m = 0. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpAppend

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open ULogTernaryRetainedPumpInitialization (initialization_run initial_lift)
open FiniteOneTapeSemantics (moveHead)

theorem cell_ne_two (b : Bool) : cell b ≠ 2 := by
  cases b <;> decide

theorem cells_ne_two (bs : List Bool) : ∀ a ∈ cells bs, a ≠ 2 := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨b, _, rfl⟩
  exact cell_ne_two b

theorem zeros_ne_two (m : Nat) : ∀ a ∈ List.replicate m (0 : Fin 3), a ≠ 2 := by
  intro a ha
  have : a = 0 := List.eq_of_mem_replicate ha
  subst a; decide

theorem payload_ne_two (source : List Bool) (m : Nat) :
    ∀ a ∈ cells source ++ List.replicate m (0 : Fin 3), a ≠ 2 := by
  intro a ha
  cases List.mem_append.mp ha with
  | inl h => exact cells_ne_two source a h
  | inr h => exact zeros_ne_two m a h

theorem replicate_succ_zero (m : Nat) :
    List.replicate (m + 1) (0 : Fin 3) = List.replicate m 0 ++ [0] := by
  simp [List.replicate_add]

theorem replicate_append_word (w p : Nat) :
    List.replicate (2 * w + 2 * p + 5) false =
      [false] ++ List.replicate w false ++ [false] ++
        List.replicate p false ++ [false] ++ List.replicate p false ++
          [false] ++ List.replicate w false ++ [false] := by
  have : 2 * w + 2 * p + 5 = 1 + w + 1 + p + 1 + p + 1 + w + 1 := by omega
  simp [this, List.replicate_add]

theorem ready_stay (head : Int) (left cells : List (Fin 3)) :
    run program 2 [false] head (fromCells 5 left cells) =
      some (head, fromCells 6 left cells) := by
  cases cells <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem step6_bit (head : Int) (left rest : List (Fin 3)) (a : Fin 3)
    (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 6 left (a :: rest)) =
      some (head + 1, fromCells 6 (a :: left) rest) := by
  cases rest <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem step6_sep (head : Int) (left rest : List (Fin 3)) :
    run program 2 [false] head (fromCells 6 left (2 :: rest)) =
      some (head + 1, fromCells 8 (2 :: left) rest) := by
  cases rest <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem scan6_run (bs : List Bool) (head : Int) (left suffix : List (Fin 3)) :
    run program 2 (List.replicate bs.length false) head
      (fromCells 6 left (cells bs ++ 2 :: suffix)) =
      some (head + (bs.length : Int),
        fromCells 6 (List.reverse (cells bs) ++ left) (2 :: suffix)) := by
  induction bs generalizing head left with
  | nil => simp [run, cells]
  | cons b rest ih =>
      have ha := cell_ne_two b
      have hw : List.replicate (rest.length + 1) false =
          [false] ++ List.replicate rest.length false := by
        simp [List.replicate_succ]
      rw [List.length_cons, hw, run_append]
      simp only [cells, List.map_cons, List.cons_append]
      rw [step6_bit head left (List.map cell rest ++ 2 :: suffix) (cell b) ha]
      exact (ih (head + 1) (cell b :: left)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [cells, List.reverse_cons]

theorem step8_bit (head : Int) (left rest : List (Fin 3)) (a : Fin 3)
    (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 8 left (a :: rest)) =
      some (head + 1, fromCells 8 (a :: left) rest) := by
  cases rest <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem scan8_run (payload : List (Fin 3)) (head : Int) (left : List (Fin 3))
    (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate payload.length false) head
      (fromCells 8 left payload) =
      some (head + (payload.length : Int),
        fromCells 8 (List.reverse payload ++ left) []) := by
  induction payload generalizing head left with
  | nil => simp [run, fromCells]
  | cons a rest ih =>
      have ha : a ≠ 2 := hnb a (by simp)
      have hrest : ∀ x ∈ rest, x ≠ 2 := fun x hx => hnb x (by simp [hx])
      have hw : List.replicate (rest.length + 1) false =
          [false] ++ List.replicate rest.length false := by
        simp [List.replicate_succ]
      rw [List.length_cons, hw, run_append, step8_bit head left rest a ha]
      exact (ih (head + 1) (a :: left) hrest).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons]

theorem write_zero (head : Int) (a : Fin 3) (left : List (Fin 3)) :
    run program 2 [false] head (fromCells 8 (a :: left) []) =
      some (head - 1, fromCells 9 left [a, 0]) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem write_zero_payload (payload under : List (Fin 3)) (head : Int) :
    run program 2 [false] head
      (fromCells 8 (payload.reverse ++ 2 :: under) []) =
      some (head - 1,
        match payload.reverse with
        | [] => fromCells 9 under [2, 0]
        | a :: rest => fromCells 9 (rest ++ 2 :: under) [a, 0]) := by
  cases hrev : payload.reverse with
  | nil =>
      simpa [hrev] using write_zero head (2 : Fin 3) under
  | cons a rest =>
      simpa [hrev] using write_zero head a (rest ++ 2 :: under)

theorem step9_bit (head : Int) (b : Fin 3) (left right : List (Fin 3))
    (a : Fin 3) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 9 (b :: left) (a :: right)) =
      some (head - 1, fromCells 9 left (b :: a :: right)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead, ha]

/-- Walk left across `stack ++ [a]` onto the delimiter 2 as focus. -/
theorem return9_to_delim (stack : List (Fin 3)) (a : Fin 3)
    (under right : List (Fin 3)) (head : Int)
    (ha : a ≠ 2) (hs : ∀ x ∈ stack, x ≠ 2) :
    run program 2 (List.replicate (stack.length + 1) false) head
      (fromCells 9 (stack ++ 2 :: under) (a :: right)) =
      some (head - (stack.length + 1 : Int),
        fromCells 9 under (2 :: stack.reverse ++ a :: right)) := by
  induction stack generalizing a right head with
  | nil =>
      simpa [List.reverse_nil] using
        step9_bit head (2 : Fin 3) under right a ha
  | cons b bs ih =>
      have hb : b ≠ 2 := hs b (by simp)
      have hbs : ∀ x ∈ bs, x ≠ 2 := fun x hx => hs x (by simp [hx])
      have hw : List.replicate (bs.length + 1 + 1) false =
          [false] ++ List.replicate (bs.length + 1) false := by
        simp [List.replicate_succ]
      have hlen : (b :: bs).length = bs.length + 1 := by simp
      rw [hlen, hw, run_append, List.cons_append,
        step9_bit head b (bs ++ 2 :: under) right a ha]
      exact (ih b (a :: right) (head - 1) hb hbs).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons]

theorem return9_after_write (payload under : List (Fin 3)) (head : Int)
    (hnb : ∀ a ∈ payload, a ≠ 2) :
    run program 2 (List.replicate payload.length false) head
      (match payload.reverse with
        | [] => fromCells 9 under [2, 0]
        | a :: rest => fromCells 9 (rest ++ 2 :: under) [a, 0]) =
      some (head - (payload.length : Int),
        fromCells 9 under (2 :: payload ++ [0])) := by
  cases hrev : payload.reverse with
  | nil =>
      have hp : payload = [] := by
        rw [← List.reverse_reverse payload, hrev, List.reverse_nil]
      subst hp
      simp [run]
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
      have hpay : payload = rest.reverse ++ [a] := by
        rw [← List.reverse_reverse payload, hrev, List.reverse_cons]
      rw [hlen]
      simpa [hrev] using
        (return9_to_delim rest a under [0] head ha hs).trans <| by
          apply congrArg some
          apply Prod.ext
          · omega
          · simp [hpay]

theorem step9_sep (head : Int) (b : Fin 3) (left right : List (Fin 3)) :
    run program 2 [false] head (fromCells 9 (b :: left) (2 :: right)) =
      some (head - 1, fromCells 7 left (b :: 2 :: right)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

theorem step9_sep_bits (bits : List (Fin 3)) (right : List (Fin 3)) (head : Int) :
    run program 2 [false] head
      (fromCells 9 (bits.reverse ++ [2]) (2 :: right)) =
      some (head - 1,
        match bits.reverse with
        | [] => fromCells 7 [] (2 :: 2 :: right)
        | a :: rest => fromCells 7 (rest ++ [2]) (a :: 2 :: right)) := by
  cases hrev : bits.reverse with
  | nil =>
      simpa [hrev] using step9_sep head (2 : Fin 3) [] right
  | cons a rest =>
      simpa [hrev] using step9_sep head a (rest ++ [2]) right

theorem step7_bit (head : Int) (b : Fin 3) (left right : List (Fin 3))
    (a : Fin 3) (ha : a ≠ 2) :
    run program 2 [false] head (fromCells 7 (b :: left) (a :: right)) =
      some (head - 1, fromCells 7 left (b :: a :: right)) := by
  simp [run, program, fromCells, boundedHalted, applyBounded, moveHead, ha]

theorem step7_blank (head : Int) (right : List (Fin 3)) :
    run program 2 [false] head (fromCells 7 [] (2 :: right)) =
      some (head + 1, fromCells 3 [2] right) := by
  cases right <;>
    simp [run, program, fromCells, boundedHalted, applyBounded, moveHead]

/-- Walk left across `stack ++ [a]` onto the left sentinel 2 as focus. -/
theorem return7_to_blank (stack : List (Fin 3)) (a : Fin 3)
    (right : List (Fin 3)) (head : Int)
    (ha : a ≠ 2) (hs : ∀ x ∈ stack, x ≠ 2) :
    run program 2 (List.replicate (stack.length + 1) false) head
      (fromCells 7 (stack ++ [2]) (a :: right)) =
      some (head - (stack.length + 1 : Int),
        fromCells 7 [] (2 :: stack.reverse ++ a :: right)) := by
  induction stack generalizing a right head with
  | nil =>
      simpa [List.reverse_nil] using
        step7_bit head (2 : Fin 3) [] right a ha
  | cons b bs ih =>
      have hb : b ≠ 2 := hs b (by simp)
      have hbs : ∀ x ∈ bs, x ≠ 2 := fun x hx => hs x (by simp [hx])
      have hw : List.replicate (bs.length + 1 + 1) false =
          [false] ++ List.replicate (bs.length + 1) false := by
        simp [List.replicate_succ]
      have hlen : (b :: bs).length = bs.length + 1 := by simp
      rw [hlen, hw, run_append, List.cons_append,
        step7_bit head b (bs ++ [2]) right a ha]
      exact (ih b (a :: right) (head - 1) hb hbs).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · simp [List.reverse_cons]

theorem return7_after_sep (bits : List (Fin 3)) (right : List (Fin 3))
    (head : Int) (hnb : ∀ a ∈ bits, a ≠ 2) :
    run program 2 (List.replicate bits.length false) head
      (match bits.reverse with
        | [] => fromCells 7 [] (2 :: 2 :: right)
        | a :: rest => fromCells 7 (rest ++ [2]) (a :: 2 :: right)) =
      some (head - (bits.length : Int),
        fromCells 7 [] (2 :: bits ++ 2 :: right)) := by
  cases hrev : bits.reverse with
  | nil =>
      have hb : bits = [] := by
        rw [← List.reverse_reverse bits, hrev, List.reverse_nil]
      subst hb
      simp [run]
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
      have hbits : bits = rest.reverse ++ [a] := by
        rw [← List.reverse_reverse bits, hrev, List.reverse_cons]
      rw [hlen]
      simpa [hrev] using
        (return7_to_blank rest a (2 :: right) head ha hs).trans <| by
          apply congrArg some
          apply Prod.ext
          · omega
          · simp [hbits, List.append_assoc]

theorem append_run (bs source : List Bool) (m : Nat) (head : Int) :
    run program 2
      (List.replicate (2 * bs.length + 2 * (source.length + m) + 5) false)
      head (fromCells 5 [2] (data bs source m)) =
      some (head, fromCells 3 [2] (data bs source (m + 1))) := by
  set payload := cells source ++ List.replicate m (0 : Fin 3)
  set bits := cells bs
  have hp : payload.length = source.length + m := by
    simp [payload, cells]
  have hb : bits.length = bs.length := by
    simp [bits, cells]
  have hnb_bs : ∀ a ∈ bits, a ≠ 2 := by
    simpa [bits] using cells_ne_two bs
  have hnb_p : ∀ a ∈ payload, a ≠ 2 := by
    simpa [payload] using payload_ne_two source m
  have hdata0 : data bs source m = bits ++ 2 :: payload := rfl
  have hdata1 : data bs source (m + 1) = bits ++ 2 :: (payload ++ [0]) := by
    simp [data, bits, payload, replicate_succ_zero, List.append_assoc]
  have hword :
      List.replicate (2 * bs.length + 2 * (source.length + m) + 5) false =
        [false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false ++ [false] ++
            List.replicate payload.length false ++ [false] ++
              List.replicate bs.length false ++ [false] := by
    have ht : 2 * bs.length + 2 * (source.length + m) + 5 =
        1 + bs.length + 1 + payload.length + 1 + payload.length + 1 +
          bs.length + 1 := by
      simp [hp]; omega
    simp [ht, List.replicate_add]
  have h0 := ready_stay head [2] (data bs source m)
  have h1 :
      run program 2 ([false] ++ List.replicate bs.length false) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int),
          fromCells 6 (bits.reverse ++ [2]) (2 :: payload)) := by
    rw [run_append, h0]
    simpa [hdata0, bits] using scan6_run bs head [2] payload
  have h2 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false]) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1,
          fromCells 8 (2 :: (bits.reverse ++ [2])) payload) := by
    rw [run_append, h1]
    exact step6_sep (head + (bs.length : Int)) (bits.reverse ++ [2]) payload
  have h3 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1 + (payload.length : Int),
          fromCells 8 (payload.reverse ++ 2 :: (bits.reverse ++ [2])) []) := by
    rw [run_append, h2]
    simpa using scan8_run payload (head + (bs.length : Int) + 1)
      (2 :: (bits.reverse ++ [2])) hnb_p
  have h4 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false ++ [false]) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1,
          match payload.reverse with
          | [] => fromCells 9 (bits.reverse ++ [2]) [2, 0]
          | a :: rest =>
              fromCells 9 (rest ++ 2 :: (bits.reverse ++ [2])) [a, 0]) := by
    rw [run_append, h3]
    exact write_zero_payload payload (bits.reverse ++ [2])
      (head + (bs.length : Int) + 1 + (payload.length : Int))
  have h5 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false ++ [false] ++
            List.replicate payload.length false) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
            (payload.length : Int),
          fromCells 9 (bits.reverse ++ [2]) (2 :: payload ++ [0])) := by
    rw [run_append, h4]
    exact return9_after_write payload (bits.reverse ++ [2])
      (head + (bs.length : Int) + 1 + (payload.length : Int) - 1) hnb_p
  have h6 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false ++ [false] ++
            List.replicate payload.length false ++ [false]) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
            (payload.length : Int) - 1,
          match bits.reverse with
          | [] => fromCells 7 [] (2 :: 2 :: (payload ++ [0]))
          | a :: rest =>
              fromCells 7 (rest ++ [2]) (a :: 2 :: (payload ++ [0]))) := by
    rw [run_append, h5]
    have hs := step9_sep_bits bits (payload ++ [0])
      (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
        (payload.length : Int))
    have hfocus : 2 :: payload ++ [0] = 2 :: (payload ++ [0]) := by
      simp [List.cons_append]
    simpa [hfocus] using hs
  have h7 :
      run program 2
        ([false] ++ List.replicate bs.length false ++ [false] ++
          List.replicate payload.length false ++ [false] ++
            List.replicate payload.length false ++ [false] ++
              List.replicate bs.length false) head
        (fromCells 5 [2] (data bs source m)) =
        some (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
            (payload.length : Int) - 1 - (bs.length : Int),
          fromCells 7 [] (2 :: bits ++ 2 :: (payload ++ [0]))) := by
    rw [run_append, h6]
    have hr := return7_after_sep bits (payload ++ [0])
      (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
        (payload.length : Int) - 1) hnb_bs
    simpa [hb] using hr
  rw [hword, run_append, h7]
  have hblank :=
    step7_blank
      (head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
        (payload.length : Int) - 1 - (bs.length : Int))
      (bits ++ 2 :: (payload ++ [0]))
  have hhead :
      ((head + (bs.length : Int) + 1 + (payload.length : Int) - 1 -
          (payload.length : Int) - 1 - (bs.length : Int)) + 1 : Int) =
        head := by omega
  have hfocus : 2 :: bits ++ 2 :: (payload ++ [0]) =
      2 :: (bits ++ 2 :: (payload ++ [0])) := by
    simp [List.cons_append]
  have htape : bits ++ 2 :: (payload ++ [0]) = data bs source (m + 1) :=
    hdata1.symm
  simpa [hhead, hfocus, htape] using hblank

def ternary_macro_spec : Prop :=
  (∀ (k : Nat) (source : List Bool) (head : Int),
      run program 2 (List.replicate (2 * k + 2) false) head
        (initial k source) =
        some (head, fromCells 5 [2] (data (List.replicate k false) source 0))) ∧
    (∀ (k : Nat) (source : List Bool),
      liftConfig program (initial k source) =
        ULogSemantics.start (input k source)) ∧
    (∀ (bs source : List Bool) (m : Nat) (head : Int),
      run program 2
        (List.replicate (2 * bs.length + 2 * (source.length + m) + 5) false)
        head (fromCells 5 [2] (data bs source m)) =
        some (head, fromCells 3 [2] (data bs source (m + 1))))

theorem ternary_macro_spec_holds : ternary_macro_spec :=
  ⟨initialization_run, initial_lift, append_run⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpAppend
