import PakFixedPolyomino.ULogTernaryRetainedPumpInitialization
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Every successful raw prefix of ternary retained-source initialization,
with explicit local cutoff `2 * k + 2`. Occupied cells and integer head
come from operational stage identities, including k = 0 and empty source. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpInitializationSpace

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open ULogTernaryRetainedPumpInitialization
open ULogFiniteAlphabetDeterministicRuns

def cellCount {ns nt : Nat} (z : BoundedConfig ns nt) : Nat :=
  z.leftRev.length + 1 + z.right.length

theorem pump_falseOnly : FalseOnly program :=
  fun q read => rule_true q read

theorem cells_length (bs : List Bool) : (cells bs).length = bs.length := by
  simp [cells]

theorem scan_prefix (k j : Nat) (hj : j ≤ k) (source : List Bool) (head : Int) :
    run program 2 (List.replicate j false) head (initial k source) =
      some (head + j, fromCells 2 (List.replicate j 0)
        (List.replicate (k - j) 0 ++ 1 :: cells source)) := by
  have hk : k = j + (k - j) := by omega
  rw [initial, hk, List.replicate_add, List.append_assoc]
  simpa using
    scan_zeros_run j head [] (List.replicate (k - j) 0 ++ 1 :: cells source)

theorem return_prefix (n j : Nat) (hj : j ≤ n) (head : Int) (rest : List (Fin 3)) :
    run program 2 (List.replicate j false) head (returnStart n rest) =
      some (head - j, returnStart (n - j) (List.replicate j 0 ++ rest)) := by
  induction j generalizing n head rest with
  | zero => simp [run]
  | succ j ih =>
      obtain ⟨n, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      have ht : j ≤ n := by omega
      have hw : List.replicate (j + 1) false =
          [false] ++ List.replicate j false := by
        simp [List.replicate_succ]
      rw [hw, run_append, return_zero_step, Option.bind_some,
        ih n ht (head - 1) (0 :: rest)]
      congr 1
      apply Prod.ext
      · omega
      · simp [zeros_snoc, List.replicate_succ]

theorem scan_config_space (k j : Nat) (hj : j ≤ k) (source : List Bool) :
    cellCount (fromCells 2 (List.replicate j 0)
      (List.replicate (k - j) 0 ++ 1 :: cells source)) ≤
        k + source.length + 2 := by
  cases hd : List.replicate (k - j) (0 : Fin 3) ++ 1 :: cells source with
  | nil =>
      have hl := congrArg List.length hd
      simp at hl
  | cons _ rest =>
      have hl := congrArg List.length hd
      simp only [List.length_append, List.length_replicate, List.length_cons,
        cells_length] at hl
      simp [cellCount, fromCells]
      omega

theorem return_config_space (k j : Nat) (hj : j ≤ k) (source : List Bool) :
    cellCount (returnStart (k - j) (List.replicate j 0 ++ 2 :: cells source)) ≤
      k + source.length + 2 := by
  cases hn : k - j with
  | zero => simp [returnStart, cellCount, fromCells, cells_length]; omega
  | succ n => simp [returnStart, cellCount, fromCells, cells_length]; omega

theorem ready_config_space (k : Nat) (source : List Bool) :
    cellCount (fromCells 5 [2] (data (List.replicate k false) source 0)) ≤
      k + source.length + 2 := by
  have hdata : data (List.replicate k false) source 0 =
      List.replicate k 0 ++ 2 :: cells source := by
    simp [data, cells_replicate_false]
  rw [hdata]
  cases hd : List.replicate k (0 : Fin 3) ++ 2 :: cells source with
  | nil =>
      have hl := congrArg List.length hd
      simp at hl
  | cons _ rest =>
      have hl := congrArg List.length hd
      simp only [List.length_append, List.length_replicate, List.length_cons,
        cells_length] at hl
      simp [cellCount, fromCells]
      omega

theorem prefix_run_space (k : Nat) (source : List Bool) (head : Int) (t : Nat)
    (ht : t ≤ 2 * k + 2) :
    ∃ hf zf,
      run program 2 (List.replicate t false) head (initial k source) =
        some (hf, zf) ∧
      cellCount zf ≤ k + source.length + 2 ∧
      head - 1 ≤ hf ∧ hf ≤ head + k := by
  by_cases hs : t ≤ k
  · refine ⟨head + t, _, scan_prefix k t hs source head,
      scan_config_space k t hs source, ?_⟩
    omega
  · by_cases hfinish : t = 2 * k + 2
    · subst t
      refine ⟨head, fromCells 5 [2] (data (List.replicate k false) source 0),
        initialization_run k source head, ready_config_space k source, ?_⟩
      omega
    · let j := t - (k + 1)
      have hj : j ≤ k := by omega
      have hsplit : t = k + 1 + j := by omega
      have hsrun : run program 2 (List.replicate k false) head (initial k source) =
          some (head + k, fromCells 2 (List.replicate k 0) (1 :: cells source)) := by
        simpa [initial] using scan_zeros_run k head [] (1 :: cells source)
      refine ⟨head + k - 1 - j, returnStart (k - j)
        (List.replicate j 0 ++ 2 :: cells source), ?_,
        return_config_space k j hj source, ?_⟩
      · have hw : List.replicate t false =
            List.replicate k false ++ [false] ++ List.replicate j false := by
          rw [hsplit, List.replicate_add, List.replicate_add]; rfl
        rw [hw, run_append, run_append, hsrun, Option.bind_some,
          separator_turn k (head + k) (cells source), Option.bind_some]
        exact return_prefix k j hj (head + k - 1) (2 :: cells source)
      · omega

theorem every_initial_prefix_space (k : Nat) (source : List Bool) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hlen : w.length ≤ 2 * k + 2)
    (hrun : run program 2 w head (initial k source) = some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤ k + source.length + 2 ∧
      head - 1 ≤ hf ∧ hf ≤ head + k := by
  have hw := successful_zipper_is_false (2 : Fin 3) program pump_falseOnly hrun
  rw [hw] at hrun
  obtain ⟨hf', zf', hr, hc, hlo, hhi⟩ := prefix_run_space k source head w.length hlen
  rw [hr] at hrun
  have he : (hf', zf') = (hf, zf) := Option.some.inj hrun
  rcases he with ⟨rfl, rfl⟩
  exact ⟨hc, hlo, hhi⟩

end PakFixedPolyomino.ULogTernaryRetainedPumpInitializationSpace
