import PakFixedPolyomino.ULogTernaryGeneratedMarginSourceCounts
import PakFixedPolyomino.ULogTernaryGeneratedMarginEntryClock

/-! Logical scanner ticks at the reserve-derived radius. These bounds concern
actual successful scanner words, using the ALL-word theorem, and do not
claim physical interpreter micro-time or execution of the margin feedback. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginSourceClock
open ULogTernaryGeneratedMarginSourceCounts

noncomputable def reserve (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x

theorem input_length_le (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    x.length ≤ reserve nt p x := by
  have h := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  have hm := Nat.le_mul_of_pos_right
    (x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3)
    (by omega : 0 < nt + 1)
  change _ ≤ reserve nt p x at h
  omega

theorem pool_le (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryMarginReserveBudget.after nt (reserve nt p x) x.length ≤ reserve nt p x := by
  unfold ULogTernaryMarginReserveBudget.after ULogTernaryMarginReserveBudget.before
  split_ifs <;> omega

theorem copies_le (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    copies nt p x ≤ reserve nt p x :=
  (Nat.div_le_self _ _).trans (pool_le nt p x)

theorem window_bytes_le (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    (x.length + 2 * radius nt p x + 3) * (nt + 1) ≤ 2 * reserve nt p x := by
  have hm := copies_positive nt p x
  have hn := input_length_le nt p x
  have hb := ULogTernaryGeneratedWindowBudget.window_fits nt p x
  change _ ≤ reserve nt p x at hb
  have hd := ULogTernaryMarginReserveBudget.divide_decomposition nt (reserve nt p x) x.length
  change ULogTernaryMarginReserveBudget.after nt (reserve nt p x) x.length =
    2 * (nt + 1) * copies nt p x + _ at hd
  have hshape : (x.length + 2 * radius nt p x + 3) * (nt + 1) =
      nt * x.length + x.length + nt + 1 + 2 * (nt + 1) * copies nt p x := by
    have he : x.length + 2 * radius nt p x + 3 = x.length + 2 * copies nt p x + 1 := by
      unfold radius; omega
    rw [he]; ring
  have hbudget : nt * x.length + nt + 3 ≤ reserve nt p x := by
    have he : (x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x + 3) * (nt + 1) + 2 =
      nt * x.length + x.length + 2 * ULogTernaryGeneratedWindowBudget.radius p x * (nt + 1) + 3 * nt + 5 := by ring
    rw [he] at hb
    omega
  rw [hshape]
  unfold ULogTernaryMarginReserveBudget.after ULogTernaryMarginReserveBudget.before at hd
  split_ifs at hd <;> omega

theorem scanner_budget_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤
      14 * (reserve nt p x) ^ 2 := by
  have hm := copies_positive nt p x
  have hc := copies_le nt p x
  have hb := window_bytes_le nt p x
  have hp : 0 < reserve nt p x := by unfold reserve; positivity
  have hr : radius nt p x + 1 = copies nt p x := by unfold radius; omega
  unfold ULogSourceObliviousSemanticAcceptance.scannerBudget
  rw [hr]
  have he := Nat.mul_le_mul hc (by omega :
    4 * ((x.length + 2 * radius nt p x + 3) * (nt + 1)) + 6 ≤ 8 * reserve nt p x + 6)
  rw [pow_two]
  nlinarith

theorem entry_guard_scanner_budget_upper (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedMarginEntry.compactDeadline nt p x + 2 +
      ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤
        126 * (reserve nt p x) ^ 2 := by
  have he := ULogTernaryGeneratedMarginEntryClock.deadline_upper nt p x
  change _ ≤ 110 * (reserve nt p x) ^ 2 at he
  have hs := scanner_budget_upper nt p x
  have hp : 0 < reserve nt p x := by unfold reserve; positivity
  have hsq : 1 ≤ (reserve nt p x) ^ 2 := by
    have : 0 < (reserve nt p x) ^ 2 := pow_pos hp _
    omega
  omega

theorem entry_guard_scanner_budget_le_clock (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedMarginEntry.compactDeadline nt p x + 2 +
      ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤
        2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have hd := entry_guard_scanner_budget_upper nt p x
  have hs := ULogTernaryGuardedPumpDelimiterInput.source_length_ge
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x
  have hf : 126 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    have h : (2 : Nat) ^ 7 ≤ 2 ^ (2 * (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
    norm_num only [Nat.reducePow] at h; omega
  have he : ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x =
      2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (2 * (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    change 2 * (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (ULogTernaryGuardedPumpDelimiterInput.source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    omega
  have hsq : (reserve nt p x) ^ 2 =
      2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) := by
    unfold reserve; rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hd
  rw [he, pow_add]
  exact hd.trans (by nlinarith)

theorem every_raw_scanner_length {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length))
    (left suffix : List (Fin 3)) (slots : List Bool) (out : ULogSemantics.Config)
    (hrun : ULogFiniteProgramZipperRunBridge.semanticRun
      (ULogCompiler.liftConfig (ULogSourceObliviousBytecode.boundedProgram M)
        (scannerInitial M p x left suffix)) slots = some out) :
    slots.length ≤ 14 * (reserve nt p x) ^ 2 :=
  (all_raw_length M p x htime left suffix slots out hrun).trans (scanner_budget_upper nt p x)

theorem large_cutoff_count {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length))
    (left suffix : List (Fin 3)) (T : Nat) (hT : 14 * (reserve nt p x) ^ 2 ≤ T) :
    StandardNondeterministicMachine.acceptingCount M x (2 ^ p.eval x.length) =
      ULogSemantics.machine.acceptingPaths T
        (ULogCompiler.liftConfig (ULogSourceObliviousBytecode.boundedProgram M)
          (scannerInitial M p x left suffix)) :=
  cutoff_count M p x htime left suffix T ((scanner_budget_upper nt p x).trans hT)

theorem reserve_scanner_clock_spec {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length)) :
    copies nt p x ≤ reserve nt p x ∧
    (x.length + 2 * radius nt p x + 3) * (nt + 1) ≤ 2 * reserve nt p x ∧
    ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤
      14 * (reserve nt p x) ^ 2 ∧
    ULogTernaryGeneratedMarginEntry.compactDeadline nt p x + 2 +
      ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤
        2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ∧
    (∀ left suffix slots out, ULogFiniteProgramZipperRunBridge.semanticRun
      (ULogCompiler.liftConfig (ULogSourceObliviousBytecode.boundedProgram M)
        (scannerInitial M p x left suffix)) slots = some out →
        slots.length ≤ 14 * (reserve nt p x) ^ 2) ∧
    (∀ left suffix T, 14 * (reserve nt p x) ^ 2 ≤ T →
      StandardNondeterministicMachine.acceptingCount M x (2 ^ p.eval x.length) =
        ULogSemantics.machine.acceptingPaths T
          (ULogCompiler.liftConfig (ULogSourceObliviousBytecode.boundedProgram M)
            (scannerInitial M p x left suffix))) :=
  ⟨copies_le nt p x, window_bytes_le nt p x, scanner_budget_upper nt p x,
    entry_guard_scanner_budget_le_clock nt p x,
    fun left suffix slots out => every_raw_scanner_length M p x htime left suffix slots out,
    large_cutoff_count M p x htime⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginSourceClock
