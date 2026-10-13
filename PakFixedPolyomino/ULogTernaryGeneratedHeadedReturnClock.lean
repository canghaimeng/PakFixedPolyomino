import PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceReturn

/-! Actual logical deadline of the compact source return fits its decoded
clock. This is separate from the physical scanner micro-time bound. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnClock
open ULogTernaryGeneratedHeadedSourceReturn
variable {nt : Nat}

theorem source_fits (codes : Fin 3 → Fin nt) (p : Polynomial Nat) (x : List Bool) :
    (sourceBits codes x).length ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by
  have h := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  have ht : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ x.length + 1 := by
    cases x <;> simp [ULogTernaryPreparedHeadedSourceExpansion.tail]
  rw [source_length]
  have hm := Nat.mul_le_mul_right (nt + 1) ht
  have hn : (x.length + 1) * (nt + 1) ≤
      (x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3) * (nt + 1) := by
    exact Nat.mul_le_mul_right _ (by omega)
  change _ ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x at h
  omega

theorem deadline_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 68 * (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
  have h := ULogTernaryGeneratedHeadedSourceExpansion.compact_deadline_upper nt p x
  have hlen : ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) ≤
      2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by
    have ht : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ x.length + 1 := by
      cases x <;> simp [ULogTernaryPreparedHeadedSourceExpansion.tail]
    have hw := ULogTernaryGeneratedWindowBudget.window_fits nt p x
    have hm := Nat.mul_le_mul_right (nt + 1) ht
    have hn := Nat.mul_le_mul_right (nt + 1)
      (show x.length + 1 ≤ x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3 by omega)
    change _ ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x at hw
    omega
  have hp : 0 < 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by positivity
  have hr : 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x ≤
      (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ hp
  change ULogTernaryGeneratedHeadedSourceExpansion.compactDeadline nt p x + 1 +
    ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) + 2 ≤ _
  have hs : 1 ≤ (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
    have hp : 0 < (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by positivity
    omega
  omega

theorem deadline_le_clock (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have hd := deadline_upper nt p x
  have hs := ULogTernaryGuardedPumpDelimiterInput.source_length_ge
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x
  have hf : 68 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    have h : (2 : Nat) ^ 7 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
    norm_num only [Nat.reducePow] at h
    omega
  have he : ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x =
      2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (2 * (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    change 2 * (ULogTernaryGuardedPumpDelimiterInput.width
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x +
      (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    change 2 * (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    omega
  have hsq : (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 =
      2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) := by
    rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hd
  rw [he, pow_add]
  exact hd.trans (by nlinarith)

end PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnClock
