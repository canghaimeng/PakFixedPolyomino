import PakFixedPolyomino.ULogTernaryGeneratedHeadedSourceExpansion

/-! Exact zero-pool arithmetic for the actual headed source and the
nonempty-only extra right blank. Division specifies the number of successful
balanced pairs; execution of that feedback loop is a separate obligation. -/
namespace PakFixedPolyomino.ULogTernaryMarginReserveBudget

def before (nt R n : Nat) : Nat := if n = 0 then R - 2 - nt else R - 1 - nt * n
def after (nt R n : Nat) : Nat := before nt R n - if n = 0 then 0 else nt + 1
def pairWidth (nt : Nat) := 2 * (nt + 1)
def iterations (nt R n : Nat) := after nt R n / pairWidth nt
def residue (nt R n : Nat) := after nt R n % pairWidth nt

theorem actual_pool_length (nt k : Nat) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1) :
    (ULogTernaryPreparedHeadedSourceExpansion.remaining x
      (ULogTernaryGeneratedHeadedSourceExpansion.buffer nt k x)).length =
        before nt (2 ^ k) x.length := by
  cases x with
  | nil => simp [ULogTernaryPreparedHeadedSourceExpansion.remaining,
      ULogTernaryGeneratedHeadedSourceExpansion.buffer,
      ULogTernaryGeneratedHeadedSourceExpansion.reserveCost,
      ULogTernaryPreparedHeadedSourceExpansion.tail, before]; omega
  | cons b xs =>
      simp [ULogTernaryGeneratedHeadedSourceExpansion.reserveCost,
        ULogTernaryPreparedHeadedSourceExpansion.tail] at hfit
      simp [ULogTernaryPreparedHeadedSourceExpansion.remaining,
        ULogTernaryGeneratedHeadedSourceExpansion.buffer,
        ULogTernaryGeneratedHeadedSourceExpansion.reserveCost,
        ULogTernaryPreparedHeadedSourceExpansion.tail, before]; omega

theorem enough_after (nt R n B : Nat)
    (hbudget : (n + 2 * B + 3) * (nt + 1) + 2 ≤ R) :
    pairWidth nt * (B + 1) + 1 ≤ after nt R n := by
  have hprod : (n + 2 * B + 3) * (nt + 1) + 2 =
      nt * n + n + 2 * (nt + 1) * (B + 1) + (nt + 1) + 2 := by ring
  rw [hprod] at hbudget
  by_cases hn : n = 0
  · subst n; simp [after, before, pairWidth] at *; omega
  · simp [after, before, hn, pairWidth]; omega

theorem divide_decomposition (nt R n : Nat) :
    after nt R n = pairWidth nt * iterations nt R n + residue nt R n := by
  exact (Nat.div_add_mod (after nt R n) (pairWidth nt)).symm

theorem residue_lt (nt R n : Nat) : residue nt R n < pairWidth nt := by
  exact Nat.mod_lt _ (by unfold pairWidth; omega)

theorem iterations_large (nt R n B : Nat)
    (hbudget : (n + 2 * B + 3) * (nt + 1) + 2 ≤ R) :
    B + 1 ≤ iterations nt R n := by
  have h := enough_after nt R n B hbudget
  unfold iterations
  apply (Nat.le_div_iff_mul_le (by unfold pairWidth; omega)).2
  simpa only [Nat.mul_comm] using (show pairWidth nt * (B + 1) ≤ after nt R n by omega)

theorem compact_reserve_budget (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    let R := 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x
    let B := ULogTernaryGeneratedWindowBudget.radius p x
    pairWidth nt * (B + 1) + 1 ≤ after nt R x.length ∧
      B + 1 ≤ iterations nt R x.length ∧
      B ≤ iterations nt R x.length - 1 ∧
      residue nt R x.length < pairWidth nt ∧
      after nt R x.length = pairWidth nt * iterations nt R x.length + residue nt R x.length := by
  dsimp
  have h := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  have hm : ULogTernaryGeneratedWindowBudget.radius p x + 1 ≤
      iterations nt (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x.length :=
    iterations_large nt _ x.length _ h
  exact ⟨enough_after nt _ x.length _ h, hm, by omega, residue_lt nt _ x.length,
    divide_decomposition nt _ x.length⟩

end PakFixedPolyomino.ULogTernaryMarginReserveBudget
