import PakFixedPolyomino.ULogRetainedCounterPump
import PakFixedPolyomino.ULogCounterPumpAppend
import PakFixedPolyomino.ULogCounterPumpBinarySteps

/-! Actual append/increment execution with arbitrary binary source retained
between the counter delimiter and the generated zeros. Every append scans
the source too, so its length contributes to the charged execution. -/

namespace PakFixedPolyomino.ULogRetainedCounterPumpIteration

open ULogCompiler ULogFiniteTapeZipperRun ULogCounterPump
open ULogBinaryCounterValue ULogCounterPumpBinarySteps

def data (bs source : List Bool) (m : Nat) : List (Fin 4) :=
  cells bs ++ 3 :: (cells source ++ List.replicate m 0)

@[simp] theorem data_length (bs source : List Bool) (m : Nat) :
    (data bs source m).length = bs.length + source.length + m + 1 := by
  simp [data]; omega

theorem data_no_blank (bs source : List Bool) (m : Nat) :
    ∀ a ∈ data bs source m, a ≠ (2 : Fin 4) := by
  intro a ha
  simp only [data, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | ha | ha | ha
  · exact cells_no_blank bs a ha
  · subst a; decide
  · exact cells_no_blank source a ha
  · have hz : a = 0 := (List.mem_replicate.mp ha).2
    subst a; decide

theorem data_append_zero (bs source : List Bool) (m : Nat) :
    data bs source m ++ [0] = data bs source (m + 1) := by
  simp [data, List.replicate_add, List.append_assoc]

theorem append_data_run (bs source : List Bool) (m : Nat) (head : Int) :
    run ULogRetainedCounterPump.program 2
      (List.replicate (2 * bs.length + 2 * (source.length + m) + 5) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head, fromCells 3 [2] (data bs source (m + 1))) := by
  rw [ULogRetainedCounterPump.run_off_entry _ _ _ (by simp [fromCells])]
  have ht : 2 * (data bs source m).length + 3 =
      2 * bs.length + 2 * (source.length + m) + 5 := by simp; omega
  simpa only [ht, data_append_zero] using
    ULogCounterPumpAppend.append_return (data bs source m) head (data_no_blank bs source m)

theorem increment_run {bs next : List Bool} {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail)
    (head : Int) (source : List Bool) (m : Nat) :
    run ULogRetainedCounterPump.program 2 (List.replicate (2 * n + 2) false) head
      (fromCells 3 [2] (data bs source m)) =
        some (head, fromCells 5 [2] (data next source m)) := by
  rw [ULogRetainedCounterPump.run_off_entry _ _ _ (by simp [fromCells])]
  simpa [hb, hn, data, cells, cell, List.append_assoc] using
    ULogCounterPumpCounterSteps.increment_return n head (data tail source m)

theorem overflow_run {bs : List Bool} (hi : increment bs = none)
    (head : Int) (source : List Bool) (m : Nat) :
    run ULogRetainedCounterPump.program 2 (List.replicate (bs.length + 1) false) head
      (fromCells 3 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (3 :: (cells source ++ List.replicate m 0))) := by
  rw [ULogRetainedCounterPump.run_off_entry _ _ _ (by simp [fromCells])]
  have hc : cells bs = List.replicate bs.length (1 : Fin 4) := by
    have h := congrArg cells (increment_none_bits hi)
    simpa [cells_replicate, cell] using h
  rw [data, hc]
  exact ULogCounterPumpCounterSteps.overflow_accept bs.length head _

theorem increment_cycle {bs next : List Bool} {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail)
    (head : Int) (source : List Bool) (m : Nat) :
    run ULogRetainedCounterPump.program 2
      (List.replicate (2 * bs.length + 2 * (source.length + m) + 2 * n + 7) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head, fromCells 5 [2] (data next source (m + 1))) := by
  have ht : 2 * bs.length + 2 * (source.length + m) + 2 * n + 7 =
      (2 * bs.length + 2 * (source.length + m) + 5) + (2 * n + 2) := by omega
  rw [ht, List.replicate_add, run_append, append_data_run, Option.bind_some]
  exact increment_run hb hn head source (m + 1)

theorem overflow_cycle {bs : List Bool} (hi : increment bs = none)
    (head : Int) (source : List Bool) (m : Nat) :
    run ULogRetainedCounterPump.program 2
      (List.replicate (3 * bs.length + 2 * (source.length + m) + 6) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (3 :: (cells source ++ List.replicate (m + 1) 0))) := by
  have ht : 3 * bs.length + 2 * (source.length + m) + 6 =
      (2 * bs.length + 2 * (source.length + m) + 5) + (bs.length + 1) := by omega
  rw [ht, List.replicate_add, run_append, append_data_run, Option.bind_some]
  exact overflow_run hi head source (m + 1)

theorem run_to_overflow (bs source : List Bool) (m : Nat) (head : Int) :
    run ULogRetainedCounterPump.program 2
      (List.replicate (ULogCounterPumpPotential.fuel bs (source.length + m)) false) head
      (fromCells 5 [2] (data bs source m)) =
        some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
          (3 :: (cells source ++ List.replicate (m + remaining bs) 0))) := by
  have all : ∀ r (bs : List Bool), remaining bs = r → ∀ m,
      run ULogRetainedCounterPump.program 2
        (List.replicate (ULogCounterPumpPotential.fuel bs (source.length + m)) false) head
        (fromCells 5 [2] (data bs source m)) =
          some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
            (3 :: (cells source ++ List.replicate (m + remaining bs) 0))) := by
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
    run ULogRetainedCounterPump.program 2
      (List.replicate ((2 ^ k) ^ 2 + (2 * k + 2 * source.length + 8) * 2 ^ k - k - 3)
        false) head
      (fromCells 5 [2] (List.replicate k 0 ++ 3 :: cells source)) =
        some (head + k, fromCells 0 (List.replicate k 0 ++ [2])
          (3 :: (cells source ++ List.replicate (2 ^ k) 0))) := by
  simpa [ULogCounterPumpPotential.fuel_zero_bits, data, cells_replicate, cell,
    remaining_zero_bits] using run_to_overflow (List.replicate k false) source 0 head

end PakFixedPolyomino.ULogRetainedCounterPumpIteration
