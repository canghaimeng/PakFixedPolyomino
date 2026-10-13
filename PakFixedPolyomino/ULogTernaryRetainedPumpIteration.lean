import PakFixedPolyomino.ULogTernaryRetainedPumpAppend
import PakFixedPolyomino.ULogTernaryRetainedPumpCarry
import PakFixedPolyomino.ULogCounterPumpPotential

/-! Full literal ternary append/carry iteration preserving arbitrary source.
Every sweep charges source length. Arithmetic potential is tied to actual
runs by the operational macros, not supplied as a runtime certificate. -/

namespace PakFixedPolyomino.ULogTernaryRetainedPumpIteration

open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryRetainedCounterPump
open ULogBinaryCounterValue

@[simp] theorem cells_replicate (k : Nat) (b : Bool) :
    cells (List.replicate k b) = List.replicate k (cell b) := by
  simp [cells]

theorem append_data_run (bs source : List Bool) (m : Nat) (head : Int) :
    run program 2
      (List.replicate (2 * bs.length + 2 * (source.length + m) + 5) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head, fromCells 3 [2] (data bs source (m + 1))) := by
  exact ULogTernaryRetainedPumpAppend.append_run bs source m head

theorem increment_run {bs next : List Bool} {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail)
    (head : Int) (source : List Bool) (m : Nat) :
    run program 2 (List.replicate (2 * n + 2) false) head
      (fromCells 3 [2] (data bs source m)) =
        some (head, fromCells 5 [2] (data next source m)) := by
  simpa [hb, hn, data, cells, cell, List.append_assoc] using
    ULogTernaryRetainedPumpCarry.increment_return n head (data tail source m)

theorem overflow_run {bs : List Bool} (hi : increment bs = none)
    (head : Int) (source : List Bool) (m : Nat) :
    run program 2 (List.replicate (bs.length + 1) false) head
      (fromCells 3 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (2 :: (cells source ++ List.replicate m 0))) := by
  have hc : cells bs = List.replicate bs.length (1 : Fin 3) := by
    have h := congrArg cells (increment_none_bits hi)
    simpa [cells_replicate, cell] using h
  rw [data, hc]
  exact ULogTernaryRetainedPumpCarry.overflow_accept bs.length head _

theorem increment_cycle {bs next : List Bool} {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail)
    (head : Int) (source : List Bool) (m : Nat) :
    run program 2
      (List.replicate (2 * bs.length + 2 * (source.length + m) + 2 * n + 7) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head, fromCells 5 [2] (data next source (m + 1))) := by
  have ht : 2 * bs.length + 2 * (source.length + m) + 2 * n + 7 =
      (2 * bs.length + 2 * (source.length + m) + 5) + (2 * n + 2) := by omega
  rw [ht, List.replicate_add, run_append, append_data_run, Option.bind_some]
  exact increment_run hb hn head source (m + 1)

theorem overflow_cycle {bs : List Bool} (hi : increment bs = none)
    (head : Int) (source : List Bool) (m : Nat) :
    run program 2
      (List.replicate (3 * bs.length + 2 * (source.length + m) + 6) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (2 :: (cells source ++ List.replicate (m + 1) 0))) := by
  have ht : 3 * bs.length + 2 * (source.length + m) + 6 =
      (2 * bs.length + 2 * (source.length + m) + 5) + (bs.length + 1) := by omega
  rw [ht, List.replicate_add, run_append, append_data_run, Option.bind_some]
  exact overflow_run hi head source (m + 1)

theorem run_to_overflow (bs source : List Bool) (m : Nat) (head : Int) :
    run program 2
      (List.replicate (ULogCounterPumpPotential.fuel bs (source.length + m)) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (2 :: (cells source ++ List.replicate (m + remaining bs) 0))) := by
  have all : ∀ r (bs : List Bool), remaining bs = r → ∀ m,
      run program 2
        (List.replicate (ULogCounterPumpPotential.fuel bs (source.length + m)) false) head
        (fromCells 5 [2] (data bs source m)) =
          some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
            (2 :: (cells source ++ List.replicate (m + remaining bs) 0))) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro bs hr m
      cases hi : increment bs with
      | none =>
        rw [ULogCounterPumpPotential.fuel_overflow hi, remaining_overflow hi]
        exact overflow_cycle hi head source m
      | some next =>
        obtain ⟨n, tail, hb, hn⟩ := increment_first_zero hi
        have hrn := remaining_increment hi
        have hlt : remaining next < r := by omega
        have hnext := ih (remaining next) hlt next rfl (m + 1)
        rw [ULogCounterPumpPotential.fuel_increment hi hb hn,
          List.replicate_add, run_append, increment_cycle hb hn head source m, Option.bind_some]
        have hm : m + 1 + remaining next = m + remaining bs := by omega
        simpa only [increment_length hi, Nat.add_assoc, hm] using hnext
  exact all (remaining bs) bs rfl m

theorem zero_bits_run (k : Nat) (source : List Bool) (head : Int) :
    run program 2
      (List.replicate ((2 ^ k) ^ 2 + (2 * k + 2 * source.length + 8) * 2 ^ k - k - 3)
        false) head
      (fromCells 5 [2] (List.replicate k 0 ++ 2 :: cells source)) =
        some (head + k, fromCells 0 (List.replicate k 0 ++ [2])
          (2 :: (cells source ++ List.replicate (2 ^ k) 0))) := by
  simpa [ULogCounterPumpPotential.fuel_zero_bits, data, cells_replicate, cell,
    remaining_zero_bits] using run_to_overflow (List.replicate k false) source 0 head

end PakFixedPolyomino.ULogTernaryRetainedPumpIteration
