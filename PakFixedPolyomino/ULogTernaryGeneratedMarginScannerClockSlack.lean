import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClock

/-! The literal existing compact clock has STRICT room beyond every
successful whole logical word. This uses its actual source header and
actual exhausting loop, with no clock/payload/program change. Interpreter
microtime and square-time are separate. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClockSlack
open StandardNondeterministicMachine
open ULogTernaryGeneratedMarginScannerCounts
open ULogTernaryGeneratedMarginSourceClock (reserve)
open ULogTernaryGeneratedMarginLoopClock (counted_source_length_ge full_budget_upper)
open ULogTernaryGuardedPumpDelimiterInput (source)
variable {ns nt : Nat}

theorem clock_ge_512_reserve_sq (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    512 * (reserve nt p x) ^ 2 ≤
      2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have hs := counted_source_length_ge
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x
  have factor : 512 ≤ 2 ^ (2 * (source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    have power : (2 : Nat) ^ 9 ≤ 2 ^ (2 * (source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    norm_num only [Nat.reducePow] at power
    exact power
  have width : ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x =
      2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (2 * (source (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    change 2 * (ULogTernaryGuardedPumpDelimiterInput.width
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x +
      (source (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    change 2 * (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (source (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    omega
  have square : (reserve nt p x) ^ 2 =
      2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) := by
    unfold reserve
    rw [Nat.mul_comm 2, pow_mul]
  rw [square, width, pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right
    (2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)) factor

theorem budget_lt_clock (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    budget M p x < 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have upper := full_budget_upper M p x
  change budget M p x ≤ 256 * (reserve nt p x) ^ 2 at upper
  have clock := clock_ge_512_reserve_sq nt p x
  have positive : 0 < (reserve nt p x) ^ 2 := by
    unfold reserve
    positivity
  omega

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClockSlack
