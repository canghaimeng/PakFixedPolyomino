import PakFixedPolyomino.ULogTernaryRetainedPumpIteration
import PakFixedPolyomino.ULogTernaryRetainedPumpAppendSpace
import PakFixedPolyomino.ULogTernaryRetainedPumpCarrySpace

/-! Global ternary retained-pump occupied space from actual append/carry prefix
stages. The accepted loop is constructed internally; every raw successful
word is covered. All local macros are actual ternary executions with raw-prefix space proofs. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpIterationSpace

open ULogCompiler ULogFiniteTapeZipperRun
open ULogTernaryRetainedCounterPump (fromCells data cells cell)
open ULogTernaryRetainedPumpIteration (cells_replicate)
open ULogTernaryRetainedPumpIteration
open ULogBinaryCounterValue ULogFiniteAlphabetDeterministicRuns

def capacity (bs source : List Bool) (m : Nat) : Nat :=
  bs.length + source.length + m + remaining bs + 2

theorem replicate_split (n a : Nat) (h : a ≤ n) :
    List.replicate n false = List.replicate a false ++ List.replicate (n - a) false := by
  have hn : n = a + (n - a) := by omega
  conv_lhs => rw [hn]
  exact List.replicate_add _ _ _

theorem every_loop_prefix_space (bs source : List Bool) (m : Nat) (head : Int)
    (w : List Bool) (hf : Int) (zf : BoundedConfig 10 3)
    (hrun : run ULogTernaryRetainedCounterPump.program 2 w head
      (fromCells 5 [2] (data bs source m)) = some (hf, zf)) :
    zf.leftRev.length + 1 + zf.right.length ≤ capacity bs source m ∧
      head - 1 ≤ hf ∧ hf ≤ head + (bs.length + source.length + m + remaining bs : Nat) := by
  have hp : FalseOnly ULogTernaryRetainedCounterPump.program := fun _ _ => rfl
  have all : ∀ r (bs : List Bool), remaining bs = r → ∀ m w hf zf,
      run ULogTernaryRetainedCounterPump.program 2 w head
        (fromCells 5 [2] (data bs source m)) = some (hf, zf) →
      zf.leftRev.length + 1 + zf.right.length ≤ capacity bs source m ∧
        head - 1 ≤ hf ∧ hf ≤ head + (bs.length + source.length + m + remaining bs : Nat) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro bs hr m w hf zf hw
      have hpos := remaining_positive bs
      let A := 2 * bs.length + 2 * (source.length + m) + 5
      have hfalse := successful_zipper_is_false (2 : Fin 3) ULogTernaryRetainedCounterPump.program hp hw
      have hlen := successful_zipper_length_le (2 : Fin 3) ULogTernaryRetainedCounterPump.program hp
        (ULogCounterPumpPotential.fuel bs (source.length + m)) head
        (fromCells 5 [2] (data bs source m))
        (fromCells 0 (List.replicate bs.length 0 ++ [2])
          (2 :: (cells source ++ List.replicate (m + remaining bs) 0)))
        (head + bs.length) (run_to_overflow bs source m head) rfl hw
      by_cases hs : w.length ≤ A
      · have hb := ULogTernaryRetainedPumpAppendSpace.every_append_prefix_space
          bs source m head w hf zf hs hw
        dsimp only [capacity]
        omega
      · rw [hfalse, replicate_split w.length A (by omega), run_append,
          append_data_run, Option.bind_some] at hw
        cases hi : increment bs with
        | none =>
          have hr1 := remaining_overflow hi
          have htail : (List.replicate (w.length - A) false).length ≤ bs.length + 1 := by
            rw [ULogCounterPumpPotential.fuel_overflow hi] at hlen
            simp only [List.length_replicate]
            dsimp [A] at *
            omega
          have hc : cells bs = List.replicate bs.length (1 : Fin 3) := by
            simpa [cells_replicate, cell] using congrArg cells (increment_none_bits hi)
          rw [data, hc] at hw
          have hb := ULogTernaryRetainedPumpCarrySpace.overflow_prefix_space bs.length
            (cells source ++ List.replicate (m + 1) 0) head
            (List.replicate (w.length - A) false) hf zf htail hw
          simp [cells] at hb
          dsimp only [capacity]
          omega
        | some next =>
          obtain ⟨n, tail, hbs, hnext⟩ := increment_first_zero hi
          have hrn := remaining_increment hi
          have hl := increment_length hi
          have hlt : remaining next < r := by omega
          have hbslen : bs.length = n + 1 + tail.length := by simp [hbs]; omega
          by_cases hcarry : w.length - A ≤ 2 * n + 2
          · have hd : data bs source (m + 1) =
                List.replicate n 1 ++ 0 :: data tail source (m + 1) := by
              simp [hbs, data, ULogTernaryRetainedCounterPump.cells, cell, List.append_assoc]
            rw [hd] at hw
            have hb := ULogTernaryRetainedPumpCarrySpace.increment_prefix_space n
              (data tail source (m + 1)) head (List.replicate (w.length - A) false) hf zf
              (by simpa using hcarry) hw
            simp [data, cells] at hb
            dsimp only [capacity]
            omega
          · rw [replicate_split (w.length - A) (2 * n + 2) (by omega),
              run_append, increment_run hbs hnext head source (m + 1), Option.bind_some] at hw
            have hb := ih (remaining next) hlt next rfl (m + 1)
              (List.replicate (w.length - A - (2 * n + 2)) false) hf zf hw
            dsimp only [capacity] at hb ⊢
            omega
  exact all (remaining bs) bs rfl m w hf zf hrun

end PakFixedPolyomino.ULogTernaryRetainedPumpIterationSpace
