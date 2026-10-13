import PakFixedPolyomino.PartitionAccounting
import Mathlib.Tactic

namespace PakFixedPolyomino

/-- The exponent used by the seam amplifier. -/
def amplifierExponent (n : ℕ) : ℕ := 2 * n * (n - 1)

@[simp] theorem amplifierExponent_one : amplifierExponent 1 = 0 := rfl

/-- Exact floor readout: lower-order junk strictly below the base cannot carry. -/
theorem floor_readout {base exponent signal junk total : ℕ}
    (hbase : 0 < base)
    (htotal : total = base ^ exponent * signal + junk)
    (hjunk : junk < base ^ exponent) :
    total / base ^ exponent = signal := by
  rw [htotal, Nat.add_comm, Nat.add_mul_div_left junk signal (pow_pos hbase exponent)]
  simp [Nat.div_eq_of_lt hjunk]

/-- Equivalent remainder formulation of the same readout. -/
theorem floor_readout_mod {base exponent signal junk total : ℕ}
    (hbase : 0 < base)
    (htotal : total = base ^ exponent * signal + junk)
    (hjunk : junk < base ^ exponent) :
    total % base ^ exponent = junk := by
  rw [htotal, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hjunk

/-- A total capped implementation of division by `base^exponent`.
It avoids constructing the divisor on branches where a certified lower bound
already exceeds the dividend. -/
def divCap (base exponent y lowerBound : ℕ) : ℕ :=
  if lowerBound > y then 0 else y / base ^ exponent

theorem divCap_eq_div {base exponent y lowerBound : ℕ}
    (hbase : 0 < base) (hlower : lowerBound ≤ base ^ exponent) :
    divCap base exponent y lowerBound = y / base ^ exponent := by
  unfold divCap
  split_ifs with h
  · have hdiv : y < base ^ exponent := lt_of_lt_of_le h hlower
    exact (Nat.div_eq_of_lt hdiv).symm
  · rfl

/-- The exponent-zero branch is exactly identity division. -/
@[simp] theorem divCap_zero_exponent {base y : ℕ} (hbase : 0 < base) :
    divCap base 0 y 1 = y := by
  unfold divCap
  split_ifs with h
  · have : y = 0 := by omega
    simp [this]
  · simp

/-- A geometric-series estimate in natural-number form. -/
theorem junk_lt_base_of_scaled_bound {base junk : ℕ} {num den : ℕ}
    (hden : 0 < den) (hbound : den * junk < num * base) (hnum : num ≤ den) :
    junk < base := by
  by_contra h
  have hbj : base ≤ junk := Nat.le_of_not_gt h
  have : den * base ≤ den * junk := Nat.mul_le_mul_left den hbj
  have : den * junk < den * base := lt_of_lt_of_le hbound (Nat.mul_le_mul_right base hnum)
  omega

/-- The final accepted floor identity as a pure arithmetic interface. -/
theorem accepted_floor_readout
    {n sAmp geometricCount wangCount junk : ℕ}
    (hs : 0 < sAmp)
    (hcount : geometricCount = sAmp ^ amplifierExponent n * wangCount + junk)
    (hjunk : junk < sAmp ^ amplifierExponent n) :
    geometricCount / sAmp ^ amplifierExponent n = wangCount :=
  floor_readout hs hcount hjunk

end PakFixedPolyomino
