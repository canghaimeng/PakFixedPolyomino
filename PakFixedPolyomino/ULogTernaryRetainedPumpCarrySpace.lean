import PakFixedPolyomino.ULogTernaryRetainedPumpCarry
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Occupied decoded space of EVERY successful raw prefix of the actual
first-zero carry/return macro (`2 * n + 2`) and of the all-ones overflow
macro (`k + 1`). Bounds come from operational stage identities, not from
the endpoint tape or a runtime certificate. Internal separatorblank2 is now compatible with the physical ternary
alphabet. Suffix cells are arbitrary: they are not visited by the carry
macro. Full-loop peak/loading/physical resources/headline remain open. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpCarrySpace

open ULogCompiler
open ULogFiniteTapeZipperRun
open ULogTernaryRetainedCounterPump
open ULogTernaryRetainedPumpCarry
open ULogFiniteAlphabetDeterministicRuns

def cellCount {ns nt : Nat} (z : BoundedConfig ns nt) : Nat :=
  z.leftRev.length + 1 + z.right.length

theorem pump_falseOnly : FalseOnly program :=
  fun q read => rule_true q read

theorem cellCount_cons (q : Fin 10) (left : List (Fin 3)) (a : Fin 3)
    (rest : List (Fin 3)) :
    cellCount (fromCells q left (a :: rest)) = left.length + 1 + rest.length := by
  simp [cellCount, fromCells]

theorem cellCount_increment_start (n : Nat) (tail : List (Fin 3)) :
    cellCount (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      n + tail.length + 2 := by
  cases n with
  | zero => simp [cellCount_cons]; omega
  | succ n =>
      simp [List.replicate_succ, cellCount_cons, List.length_append,
        List.length_replicate]
      omega

theorem cellCount_increment_carry (n j : Nat) (tail : List (Fin 3))
    (hj : j ≤ n) :
    cellCount (fromCells 3 (List.replicate j 0 ++ [2])
        (List.replicate (n - j) 1 ++ 0 :: tail)) =
      n + tail.length + 2 := by
  by_cases hje : j = n
  · subst hje
    simp [cellCount_cons, List.length_append, List.length_replicate]
    omega
  · have hsplit : n - j = n - j - 1 + 1 := by omega
    rw [hsplit, List.replicate_succ]
    simp [cellCount_cons, List.length_append, List.length_replicate]
    omega

theorem cellCount_returnStart (n : Nat) (rest : List (Fin 3)) :
    cellCount (returnStart n rest) = n + rest.length + 1 := by
  cases n with
  | zero => simp [returnStart, cellCount_cons]; omega
  | succ n =>
      simp [returnStart, cellCount_cons, List.length_append, List.length_replicate]
      omega

theorem cellCount_increment_final (n : Nat) (tail : List (Fin 3)) :
    cellCount (fromCells 5 [2] (List.replicate n 0 ++ 1 :: tail)) =
      n + tail.length + 2 := by
  cases n with
  | zero => simp [cellCount_cons]; omega
  | succ n =>
      simp [List.replicate_succ, cellCount_cons, List.length_append,
        List.length_replicate]
      omega

theorem increment_carry_prefix (n j : Nat) (head : Int) (tail : List (Fin 3))
    (hj : j ≤ n) :
    run program 2 (List.replicate j false) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head + j,
        fromCells 3 (List.replicate j 0 ++ [2])
          (List.replicate (n - j) 1 ++ 0 :: tail)) := by
  have hsplit : List.replicate n (1 : Fin 3) ++ 0 :: tail =
      List.replicate j 1 ++ (List.replicate (n - j) 1 ++ 0 :: tail) := by
    have hn : List.replicate n (1 : Fin 3) =
        List.replicate j 1 ++ List.replicate (n - j) 1 := by
      conv_lhs => rw [show n = j + (n - j) from by omega]
      exact List.replicate_add j (n - j) 1
    rw [hn, List.append_assoc]
  rw [hsplit]
  simpa using carry_ones_run j head [2]
    (List.replicate (n - j) 1 ++ 0 :: tail)

theorem increment_flip_run (n : Nat) (head : Int) (tail : List (Fin 3)) :
    run program 2 (List.replicate (n + 1) false) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head + n - 1, returnStart n (1 :: tail)) := by
  have hword : List.replicate (n + 1) false =
      List.replicate n false ++ [false] := by
    simp [List.replicate_add]
  rw [hword, run_append, increment_carry_prefix n n head tail le_rfl]
  simp
  exact carry_flip_sentinel n (head + n) tail

theorem return_prefix (n t : Nat) (head : Int) (rest : List (Fin 3))
    (ht : t ≤ n) :
    run program 2 (List.replicate t false) head (returnStart n rest) =
      some (head - t,
        returnStart (n - t) (List.replicate t 0 ++ rest)) := by
  induction t generalizing n head rest with
  | zero => simp [run]
  | succ t ih =>
      have hword : List.replicate (t + 1) false =
          [false] ++ List.replicate t false := by
        simp [List.replicate_succ]
      have hs : run program 2 [false] head (returnStart n rest) =
          some (head - 1, returnStart (n - 1) (0 :: rest)) := by
        have hn : n - 1 + 1 = n := by omega
        simpa [hn] using return_zero_step (n - 1) head rest
      rw [hword, run_append, hs]
      exact (ih (n - 1) (head - 1) (0 :: rest) (by omega)).trans <| by
        apply congrArg some
        apply Prod.ext
        · omega
        · have hidx : n - 1 - t = n - (t + 1) := by omega
          have hrest : List.replicate t (0 : Fin 3) ++ 0 :: rest =
              List.replicate (t + 1) 0 ++ rest := by
            simpa [List.replicate_succ] using
              zeros_snoc t rest
          simp [hidx, hrest]

theorem increment_return_prefix (n t : Nat) (head : Int) (tail : List (Fin 3))
    (ht : t ≤ n) :
    run program 2 (List.replicate (n + 1 + t) false) head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
      some (head + n - 1 - t,
        returnStart (n - t) (List.replicate t 0 ++ 1 :: tail)) := by
  have hword : List.replicate (n + 1 + t) false =
      List.replicate (n + 1) false ++ List.replicate t false := by
    simp [List.replicate_add]
  rw [hword, run_append, increment_flip_run]
  exact return_prefix n t (head + n - 1) (1 :: tail) ht

theorem increment_prefix_run (n : Nat) (tail : List (Fin 3)) (head : Int)
    (k : Nat) (hk : k ≤ 2 * n + 2) :
    ∃ hf zf,
      run program 2 (List.replicate k false) head
        (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
          some (hf, zf) ∧
      cellCount zf ≤ n + tail.length + 2 ∧
      head - 1 ≤ hf ∧ hf ≤ head + n := by
  if hk0 : k = 0 then
    subst hk0
    refine ⟨head, fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail),
      by simp [run], by simp [cellCount_increment_start], ?_⟩
    omega
  else if hcarry : k ≤ n then
    refine ⟨head + k,
      fromCells 3 (List.replicate k 0 ++ [2])
        (List.replicate (n - k) 1 ++ 0 :: tail),
      increment_carry_prefix n k head tail hcarry,
      by simp [cellCount_increment_carry n k tail hcarry], ?_⟩
    omega
  else if hflip : k = n + 1 then
    subst hflip
    refine ⟨head + n - 1, returnStart n (1 :: tail),
      increment_flip_run n head tail, ?_, ?_⟩
    · simp [cellCount_returnStart]; omega
    · omega
  else if hret : k ≤ 2 * n + 1 then
    set t := k - (n + 1)
    have ht : t ≤ n := by omega
    have hsplit : k = n + 1 + t := by omega
    refine ⟨head + n - 1 - t,
      returnStart (n - t) (List.replicate t 0 ++ 1 :: tail), ?_, ?_, ?_⟩
    · simpa [hsplit] using increment_return_prefix n t head tail ht
    · simp [cellCount_returnStart, List.length_append, List.length_replicate]
      omega
    · omega
  else
    have hkf : k = 2 * n + 2 := by omega
    subst hkf
    refine ⟨head, fromCells 5 [2] (List.replicate n 0 ++ 1 :: tail),
      increment_return n head tail, by simp [cellCount_increment_final], ?_⟩
    omega

theorem increment_prefix_space (n : Nat) (tail : List (Fin 3)) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hlen : w.length ≤ 2 * n + 2)
    (hrun : run program 2 w head
      (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) = some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤ n + tail.length + 2 ∧
      head - 1 ≤ hf ∧ hf ≤ head + n := by
  have hfalse : w = List.replicate w.length false :=
    successful_zipper_is_false (2 : Fin 3) program pump_falseOnly hrun
  rw [hfalse] at hrun
  obtain ⟨hf', zf', huniq, hcount, hlo, hhi⟩ :=
    increment_prefix_run n tail head w.length hlen
  have heq : (hf', zf') = (hf, zf) := by
    rw [huniq] at hrun
    exact Option.some.inj hrun
  rcases heq with ⟨rfl, rfl⟩
  exact ⟨hcount, hlo, hhi⟩

theorem cellCount_overflow_start (k : Nat) (suffix : List (Fin 3)) :
    cellCount (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
      k + suffix.length + 2 := by
  cases k with
  | zero => simp [cellCount_cons]; omega
  | succ k =>
      simp [List.replicate_succ, cellCount_cons, List.length_append,
        List.length_replicate]
      omega

theorem cellCount_overflow_carry (k j : Nat) (suffix : List (Fin 3))
    (hj : j ≤ k) :
    cellCount (fromCells 3 (List.replicate j 0 ++ [2])
        (List.replicate (k - j) 1 ++ 2 :: suffix)) =
      k + suffix.length + 2 := by
  by_cases hje : j = k
  · subst hje
    simp [cellCount_cons, List.length_append, List.length_replicate]
    omega
  · have hsplit : k - j = k - j - 1 + 1 := by omega
    rw [hsplit, List.replicate_succ]
    simp [cellCount_cons, List.length_append, List.length_replicate]
    omega

theorem cellCount_overflow_accept (k : Nat) (suffix : List (Fin 3)) :
    cellCount (fromCells 0 (List.replicate k 0 ++ [2]) (2 :: suffix)) =
      k + suffix.length + 2 := by
  simp [cellCount_cons, List.length_append, List.length_replicate]
  omega

theorem overflow_carry_prefix (k j : Nat) (head : Int) (suffix : List (Fin 3))
    (hj : j ≤ k) :
    run program 2 (List.replicate j false) head
      (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
      some (head + j,
        fromCells 3 (List.replicate j 0 ++ [2])
          (List.replicate (k - j) 1 ++ 2 :: suffix)) := by
  have hsplit : List.replicate k (1 : Fin 3) ++ 2 :: suffix =
      List.replicate j 1 ++ (List.replicate (k - j) 1 ++ 2 :: suffix) := by
    have hk : List.replicate k (1 : Fin 3) =
        List.replicate j 1 ++ List.replicate (k - j) 1 := by
      conv_lhs => rw [show k = j + (k - j) from by omega]
      exact List.replicate_add j (k - j) 1
    rw [hk, List.append_assoc]
  rw [hsplit]
  simpa using carry_ones_run j head [2]
    (List.replicate (k - j) 1 ++ 2 :: suffix)

theorem overflow_accept_run (k : Nat) (head : Int) (suffix : List (Fin 3)) :
    run program 2 (List.replicate (k + 1) false) head
      (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
      some (head + k,
        fromCells 0 (List.replicate k 0 ++ [2]) (2 :: suffix)) :=
  overflow_accept k head suffix

theorem overflow_prefix_run (k : Nat) (suffix : List (Fin 3)) (head : Int)
    (m : Nat) (hm : m ≤ k + 1) :
    ∃ hf zf,
      run program 2 (List.replicate m false) head
        (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
          some (hf, zf) ∧
      cellCount zf ≤ k + suffix.length + 2 ∧
      head ≤ hf ∧ hf ≤ head + k := by
  if hm0 : m = 0 then
    subst hm0
    refine ⟨head, fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix),
      by simp [run], by simp [cellCount_overflow_start], ?_⟩
    omega
  else if hcarry : m ≤ k then
    refine ⟨head + m,
      fromCells 3 (List.replicate m 0 ++ [2])
        (List.replicate (k - m) 1 ++ 2 :: suffix),
      overflow_carry_prefix k m head suffix hcarry,
      by simp [cellCount_overflow_carry k m suffix hcarry], ?_⟩
    omega
  else
    have hmf : m = k + 1 := by omega
    subst hmf
    refine ⟨head + k,
      fromCells 0 (List.replicate k 0 ++ [2]) (2 :: suffix),
      overflow_accept_run k head suffix, by simp [cellCount_overflow_accept],
      ?_⟩
    omega

theorem overflow_prefix_space (k : Nat) (suffix : List (Fin 3)) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hlen : w.length ≤ k + 1)
    (hrun : run program 2 w head
      (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) = some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤ k + suffix.length + 2 ∧
      head ≤ hf ∧ hf ≤ head + k := by
  have hfalse : w = List.replicate w.length false :=
    successful_zipper_is_false (2 : Fin 3) program pump_falseOnly hrun
  rw [hfalse] at hrun
  obtain ⟨hf', zf', huniq, hcount, hlo, hhi⟩ :=
    overflow_prefix_run k suffix head w.length hlen
  have heq : (hf', zf') = (hf, zf) := by
    rw [huniq] at hrun
    exact Option.some.inj hrun
  rcases heq with ⟨rfl, rfl⟩
  exact ⟨hcount, hlo, hhi⟩

theorem ternary_carry_spec :
    (∀ (n : Nat) (head : Int) (tail : List (Fin 3)),
      run program 2 (List.replicate (2 * n + 2) false) head
        (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
          some (head, fromCells 5 [2] (List.replicate n 0 ++ 1 :: tail))) ∧
    (∀ (k : Nat) (head : Int) (suffix : List (Fin 3)),
      run program 2 (List.replicate (k + 1) false) head
        (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
          some (head + k, fromCells 0 (List.replicate k 0 ++ [2]) (2 :: suffix))) ∧
    (∀ (n : Nat) (tail : List (Fin 3)) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      w.length ≤ 2 * n + 2 →
      run program 2 w head (fromCells 3 [2] (List.replicate n 1 ++ 0 :: tail)) =
        some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤ n + tail.length + 2 ∧
        head - 1 ≤ hf ∧ hf ≤ head + n) ∧
    (∀ (k : Nat) (suffix : List (Fin 3)) (head : Int) (w : List Bool)
      (hf : Int) (zf : BoundedConfig 10 3),
      w.length ≤ k + 1 →
      run program 2 w head (fromCells 3 [2] (List.replicate k 1 ++ 2 :: suffix)) =
        some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤ k + suffix.length + 2 ∧
        head ≤ hf ∧ hf ≤ head + k) ∧
    (∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3) := by
  exact ⟨increment_return, overflow_accept, increment_prefix_space,
    overflow_prefix_space, compiled_symbols_ternary⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpCarrySpace
