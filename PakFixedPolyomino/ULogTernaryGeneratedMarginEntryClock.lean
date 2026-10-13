import PakFixedPolyomino.ULogTernaryGeneratedMarginEntry

/-! Logical cost of the actual compact return/seal/counter branch. Physical
scanner micro-time and the later repeated margins are separate obligations. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginEntryClock
open ULogTernaryGeneratedMarginEntry

theorem zeroCount_le (nt k : Nat) (x : List Bool) : zeroCount nt k x ≤ 2 ^ k := by
  have hp : 0 < (2 : Nat) ^ k := by positivity
  unfold zeroCount ULogTernaryMarginReserveBudget.before
  split_ifs <;> omega

theorem alphabet_le_reserve (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    nt ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by
  have h := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  have hprod : nt + 1 ≤ (x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3) * (nt + 1) := by
    have hm := Nat.mul_le_mul_right (nt + 1)
      (show 1 ≤ x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3 by omega)
    simpa only [Nat.one_mul] using hm
  change _ ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x at h
  omega

theorem deadline_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 110 * (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
  have hreturn := ULogTernaryGeneratedHeadedReturnClock.deadline_upper nt p x
  have hpool := zeroCount_le nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x
  have hnt := alphabet_le_reserve nt p x
  have hs : ((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1) ≤
      2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by
    have hw := ULogTernaryGeneratedWindowBudget.window_fits nt p x
    have ht : (ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1 ≤ x.length + 1 := by
      cases x <;> simp [ULogTernaryPreparedHeadedSourceExpansion.tail]
    have hm := Nat.mul_le_mul_right (nt + 1) ht
    have hn := Nat.mul_le_mul_right (nt + 1)
      (show x.length + 1 ≤ x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3 by omega)
    change _ ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x at hw
    omega
  have hp : 0 < 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x := by positivity
  have hr : 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x ≤
      (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ hp
  have hnt2 : nt * nt ≤ (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by
    simpa only [pow_two] using Nat.mul_self_le_mul_self hnt
  have hsq : 1 ≤ (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ^ 2 := by omega
  change ULogTernaryGeneratedHeadedSourceReturn.compactDeadline nt p x + 1 +
    ULogTernaryReserveEndSeal.deadline
      (((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1))
      (zeroCount nt (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x) + 1 +
    ULogTernaryConditionalRightMargin.deadline nt x.length
      (((ULogTernaryPreparedHeadedSourceExpansion.tail x).length + 1) * (nt + 1)) ≤ _
  rw [ULogTernaryReserveEndSeal.deadline, ULogTernaryConditionalRightMargin.deadline_eq]
  split_ifs <;> omega

theorem deadline_le_clock (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    compactDeadline nt p x ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have hd := deadline_upper nt p x
  have hs := ULogTernaryGuardedPumpDelimiterInput.source_length_ge
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x
  have hf : 110 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    have h : (2 : Nat) ^ 7 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
    norm_num only [Nat.reducePow] at h; omega
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

end PakFixedPolyomino.ULogTernaryGeneratedMarginEntryClock
