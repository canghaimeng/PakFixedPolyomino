import PakFixedPolyomino.ULogBinaryCounterValue

/-! A pure potential for the append-before-increment loader. Its arithmetic
recurrence is not an execution or bit-time claim. Operational append/carry
sweeps and their composition must separately identify it with actual fuel. -/

namespace PakFixedPolyomino.ULogCounterPumpPotential

open ULogBinaryCounterValue

def fuel (bs : List Bool) (m : Nat) : Nat :=
  remaining bs ^ 2 + (2 * bs.length + 2 * m + 8) * remaining bs +
    2 * ones bs - bs.length - 3

theorem fuel_balance (bs : List Bool) (m : Nat) :
    fuel bs m + bs.length + 3 =
      remaining bs ^ 2 + (2 * bs.length + 2 * m + 8) * remaining bs + 2 * ones bs := by
  have hb := ULogBinaryCounterValue.fuel_balance bs
  have hm : 5 * remaining bs ≤ (2 * bs.length + 2 * m + 8) * remaining bs :=
    Nat.mul_le_mul_right _ (by omega)
  unfold fuel
  omega

theorem fuel_overflow {bs : List Bool} (h : increment bs = none) (m : Nat) :
    fuel bs m = 3 * bs.length + 2 * m + 6 := by
  have hr := remaining_overflow h
  have ho : ones bs = bs.length := by
    have hh := congrArg ones (increment_none_bits h)
    simpa only [ones_replicate_true] using hh
  have hf := fuel_balance bs m
  simp only [hr, ho, one_pow, Nat.mul_one] at hf
  omega

theorem fuel_increment {bs next : List Bool} (h : increment bs = some next)
    {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail) (m : Nat) :
    fuel bs m = 2 * bs.length + 2 * m + 2 * n + 7 + fuel next (m + 1) := by
  have hr := remaining_increment h
  have hl := increment_length h
  have hob : ones bs = n + ones tail := by
    rw [hb, ones_append, ones_replicate_true]; rfl
  have hon : ones next = 1 + ones tail := by
    rw [hn, ones_append, ones_replicate_false]
    simp [ones, Nat.add_comm]
  have he : remaining bs ^ 2 + (2 * bs.length + 2 * m + 8) * remaining bs + 2 * ones bs =
      remaining next ^ 2 + (2 * next.length + 2 * (m + 1) + 8) * remaining next +
        2 * ones next + (2 * bs.length + 2 * m + 2 * n + 7) := by
    rw [hr, hl]
    nlinarith
  have hfb := fuel_balance bs m
  have hfn := fuel_balance next (m + 1)
  omega

theorem fuel_zero_bits (k m : Nat) :
    fuel (List.replicate k false) m =
      (2 ^ k) ^ 2 + (2 * k + 2 * m + 8) * 2 ^ k - k - 3 := by
  simp [fuel, remaining_zero_bits, ones_replicate_false]

end PakFixedPolyomino.ULogCounterPumpPotential
