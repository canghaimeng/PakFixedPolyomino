import PakFixedPolyomino.ULogTernaryGeneratedMarginLoop
import PakFixedPolyomino.ULogTernaryGeneratedMarginSourceClock
import PakFixedPolyomino.ULogTernaryNestedHeaderParser
import PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterInput

/-! Logical tick budget of the actual exhausting blank loop inside the
frozen compact Caller, then the full loader+scanner budget against the
existing compact payload clock. Not BIT runtime or physical square-time. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginLoopClock

open ULogCompiler
open StandardNondeterministicMachine
open ULogTernaryGeneratedMarginLoop
open ULogTernaryGeneratedMarginSourceClock
open ULogTernaryGeneratedMarginSourceCounts (copies radius)
open ULogTernaryGeneratedMarginEntry (correctedBits compactDeadline)
open ULogTernaryMarginMarkedLayout (codes)
open ULogFiniteTapeZipperRun (semanticRun)
open ULogTernaryBalancedBlankLoop (K)
open ULogTernaryNestedHeaderParser (header nested_length counted_length)
open ULogTernaryGuardedPumpDelimiterInput (source depth seedWidth)

variable {ns nt : Nat}

theorem pair_deadline_eq {nt : Nat} (hnt : 0 < nt) (n : Nat) :
    ULogTernaryBalancedBlankPair.deadline nt n =
      2 * (nt + 2) * n + 2 * nt * nt + 20 * nt + 31 :=
  ULogTernaryBalancedBlankPair.deadline_eq hnt n

theorem loop_deadline_eq (nt n m r : Nat) (hnt : 0 < nt) :
    ULogTernaryBalancedBlankLoop.deadline nt n m r =
      2 * (nt + 3) * n * m +
        2 * (nt + 3) * (nt + 1) * m * (m - 1) +
        m * (2 * K nt + 2 * nt * nt + 20 * nt + 36) +
        2 * n + 2 * K nt * m + 2 * r + 5 := by
  induction m generalizing n with
  | zero => simp [ULogTernaryBalancedBlankLoop.deadline]
  | succ m ih =>
      rw [ULogTernaryBalancedBlankLoop.deadline, pair_deadline_eq hnt n, ih]
      cases m with
      | zero => ring
      | succ m => simp; ring

theorem loop_term_core (nt n k R : Nat) (hnt : 0 < nt) (hn : n ≤ 2 * R)
    (hKm : 2 * (nt + 1) * (k + 1) ≤ R) :
    2 * (nt + 3) * n * (k + 1) ≤ 4 * R ^ 2 := by
  have hntK : nt + 3 ≤ 2 * (nt + 1) := by omega
  have h1 : 2 * (nt + 3) * n * (k + 1) ≤
      2 * (2 * (nt + 1)) * (2 * R) * (k + 1) :=
    Nat.mul_le_mul_right (k + 1)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hntK) hn)
  have h2 : 2 * (2 * (nt + 1)) * (2 * R) * (k + 1) =
      4 * (2 * (nt + 1) * (k + 1)) * R := by ring
  have h3 : 4 * (2 * (nt + 1) * (k + 1)) * R ≤ 4 * R * R :=
    Nat.mul_le_mul_right R (Nat.mul_le_mul_left 4 hKm)
  have h4 : 4 * R * R = 4 * R ^ 2 := by
    rw [pow_two, mul_assoc]
  calc
    2 * (nt + 3) * n * (k + 1) ≤ 2 * (2 * (nt + 1)) * (2 * R) * (k + 1) := h1
    _ = 4 * (2 * (nt + 1) * (k + 1)) * R := h2
    _ ≤ 4 * R * R := h3
    _ = 4 * R ^ 2 := h4

theorem loop_term_quad (nt k R : Nat) (hnt : 0 < nt)
    (hKm : 2 * (nt + 1) * (k + 1) ≤ R) :
    2 * (nt + 3) * (nt + 1) * (k + 1) * k ≤ R ^ 2 := by
  have hntK : nt + 3 ≤ 2 * (nt + 1) := by omega
  have heq : 2 * (nt + 3) * (nt + 1) * (k + 1) * k =
      (2 * (nt + 1) * (k + 1)) * ((nt + 3) * k) := by ring
  have hk : (nt + 3) * k ≤ R :=
    (Nat.mul_le_mul_left (nt + 3) (Nat.le_succ k)).trans
      ((Nat.mul_le_mul_right (k + 1) hntK).trans hKm)
  exact heq.trans_le <| (pow_two R).symm ▸ Nat.mul_le_mul hKm hk

theorem loop_term_mass (nt k R : Nat) (hnt : 0 < nt)
    (hKm : 2 * (nt + 1) * (k + 1) ≤ R) :
    (k + 1) * (2 * (2 * (nt + 1)) + 2 * nt * nt + 20 * nt + 36) ≤
      R ^ 2 + 48 * R := by
  have hntR : nt ≤ R := by
    have : nt + 1 ≤ 2 * (nt + 1) := by omega
    have : 2 * (nt + 1) ≤ 2 * (nt + 1) * (k + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
    omega
  have h2nt : 2 * nt * (k + 1) ≤ R :=
    (Nat.mul_le_mul_right (k + 1) (by omega : 2 * nt ≤ 2 * (nt + 1))).trans hKm
  have hmR : k + 1 ≤ R := by
    have : 1 * (k + 1) ≤ 2 * (nt + 1) * (k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have ha : (k + 1) * (2 * (2 * (nt + 1))) ≤ 2 * R := by
    have heq : (k + 1) * (2 * (2 * (nt + 1))) =
        2 * (2 * (nt + 1) * (k + 1)) := by ring
    exact heq.trans_le (Nat.mul_le_mul_left 2 hKm)
  have hb : (k + 1) * (2 * nt * nt) ≤ R ^ 2 := by
    have heq : (k + 1) * (2 * nt * nt) = nt * (2 * nt * (k + 1)) := by ring
    exact heq.trans_le <| (pow_two R).symm ▸ Nat.mul_le_mul hntR h2nt
  have hc : (k + 1) * (20 * nt) ≤ 10 * R := by
    have heq : (k + 1) * (20 * nt) = 10 * (2 * nt * (k + 1)) := by ring
    exact heq.trans_le (Nat.mul_le_mul_left 10 h2nt)
  have hd : (k + 1) * 36 ≤ 36 * R := by
    rw [Nat.mul_comm (k + 1)]; exact Nat.mul_le_mul_left 36 hmR
  have hsplit : (k + 1) * (2 * (2 * (nt + 1)) + 2 * nt * nt + 20 * nt + 36) =
      (k + 1) * (2 * (2 * (nt + 1))) + (k + 1) * (2 * nt * nt) +
        (k + 1) * (20 * nt) + (k + 1) * 36 := by ring
  have hsum :
      (k + 1) * (2 * (2 * (nt + 1))) + (k + 1) * (2 * nt * nt) +
        (k + 1) * (20 * nt) + (k + 1) * 36 ≤
      2 * R + R ^ 2 + 10 * R + 36 * R :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha hb) hc) hd
  have hcollect : 2 * R + R ^ 2 + 10 * R + 36 * R = R ^ 2 + 48 * R := by ring
  exact hsplit.trans_le (hsum.trans_eq hcollect)

theorem loop_deadline_upper (nt n m r R : Nat)
    (hnt : 0 < nt) (hR : 1 ≤ R) (hn : n ≤ 2 * R)
    (hN : 2 * (nt + 1) * m + r ≤ R) :
    ULogTernaryBalancedBlankLoop.deadline nt n m r ≤ 64 * R ^ 2 := by
  have heq := loop_deadline_eq nt n m r hnt
  rw [heq]
  simp only [K]
  have hR2 : R ≤ R ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_left R hR
  match m with
  | 0 =>
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      have hlin : 2 * n + 2 * r + 5 ≤ 6 * R + 5 := by omega
      have h11 : 6 * R + 5 ≤ 11 * R := by
        have : 5 ≤ 5 * R := Nat.mul_le_mul_left 5 hR
        omega
      exact (hlin.trans h11).trans
        ((Nat.mul_le_mul_left 11 hR2).trans
          (Nat.mul_le_mul_right (R ^ 2) (by omega : 11 ≤ 64)))
  | k + 1 =>
      have hKm : 2 * (nt + 1) * (k + 1) ≤ R := by omega
      have hT1 := loop_term_core nt n k R hnt hn hKm
      have hT2 := loop_term_quad nt k R hnt hKm
      have hT3 := loop_term_mass nt k R hnt hKm
      have hT4 : 2 * n + 2 * (2 * (nt + 1)) * (k + 1) + 2 * r + 5 ≤ 8 * R + 5 := by
        have hn' : 2 * n ≤ 4 * R := by
          have hmul : 2 * n ≤ 2 * (2 * R) := Nat.mul_le_mul_left 2 hn
          have h4 : 2 * (2 * R) = 4 * R := by ring
          exact h4 ▸ hmul
        have hp : 2 * (2 * (nt + 1)) * (k + 1) ≤ 2 * R := by
          have heq : 2 * (2 * (nt + 1)) * (k + 1) =
              2 * (2 * (nt + 1) * (k + 1)) := by ring
          exact heq.trans_le (Nat.mul_le_mul_left 2 hKm)
        have hr5 : 2 * r + 5 ≤ 2 * R + 5 := by omega
        have hsplit : 2 * n + 2 * (2 * (nt + 1)) * (k + 1) + 2 * r + 5 =
            2 * n + (2 * (2 * (nt + 1)) * (k + 1) + (2 * r + 5)) := by ring
        have hadd := Nat.add_le_add hn' (Nat.add_le_add hp hr5)
        have hcollect : 4 * R + (2 * R + (2 * R + 5)) = 8 * R + 5 := by ring
        exact hsplit.trans_le (hadd.trans_eq hcollect)
      have hR4 : 4 ≤ R := by
        have : 4 ≤ 2 * (nt + 1) := by omega
        have : 2 * (nt + 1) ≤ 2 * (nt + 1) * (k + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        omega
      have hsum :
          2 * (nt + 3) * n * (k + 1) +
            2 * (nt + 3) * (nt + 1) * (k + 1) * k +
            (k + 1) * (2 * (2 * (nt + 1)) + 2 * nt * nt + 20 * nt + 36) +
            2 * n + 2 * (2 * (nt + 1)) * (k + 1) + 2 * r + 5 ≤
          6 * R ^ 2 + 56 * R + 5 := by
        have hsplit :
            2 * (nt + 3) * n * (k + 1) +
              2 * (nt + 3) * (nt + 1) * (k + 1) * k +
              (k + 1) * (2 * (2 * (nt + 1)) + 2 * nt * nt + 20 * nt + 36) +
              2 * n + 2 * (2 * (nt + 1)) * (k + 1) + 2 * r + 5 =
            (2 * (nt + 3) * n * (k + 1) +
              2 * (nt + 3) * (nt + 1) * (k + 1) * k +
              (k + 1) * (2 * (2 * (nt + 1)) + 2 * nt * nt + 20 * nt + 36)) +
              (2 * n + 2 * (2 * (nt + 1)) * (k + 1) + 2 * r + 5) := by ring
        have hleft :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hT1 hT2) hT3) hT4
        have hcollect : 4 * R ^ 2 + R ^ 2 + (R ^ 2 + 48 * R) + (8 * R + 5) =
            6 * R ^ 2 + 56 * R + 5 := by ring
        exact hsplit.trans_le (hleft.trans_eq hcollect)
      have hrest : 56 * R + 5 ≤ 15 * R ^ 2 := by
        have h56 : 56 * R ≤ 14 * R ^ 2 := by
          have : 56 ≤ 14 * R := by omega
          have : 56 * R ≤ 14 * R * R := Nat.mul_le_mul_right R this
          simpa [pow_two, mul_assoc] using this
        have h5 : 5 ≤ R ^ 2 := by
          have : 16 ≤ R * R := Nat.mul_le_mul hR4 hR4
          have : 16 ≤ R ^ 2 := by rwa [pow_two]
          omega
        omega
      have hmid : 6 * R ^ 2 + 56 * R + 5 ≤ 6 * R ^ 2 + 15 * R ^ 2 := by
        have hassoc : 6 * R ^ 2 + 56 * R + 5 = 6 * R ^ 2 + (56 * R + 5) := by ring
        exact hassoc.trans_le (Nat.add_le_add_left hrest (6 * R ^ 2))
      have h64 : 6 * R ^ 2 + 15 * R ^ 2 ≤ 64 * R ^ 2 := by
        have h21 : 6 * R ^ 2 + 15 * R ^ 2 = 21 * R ^ 2 := by ring
        have : 21 * R ^ 2 ≤ 64 * R ^ 2 :=
          Nat.mul_le_mul_right (R ^ 2) (by omega : 21 ≤ 64)
        exact h21.trans_le this
      exact hsum.trans (hmid.trans h64)

theorem header_length_ge (d c : Nat) (x : List Bool) :
    c ≤ (header d c x).length := by
  induction d with
  | zero => simp [header]
  | succ d ih =>
      simp [header, List.length_append, List.length_cons]; omega

theorem counted_source_length_ge (p : Polynomial Nat) (x : List Bool) :
    3 ≤ (source p x).length := by
  have hc : 2 ≤ seedWidth p := by unfold seedWidth; omega
  have hh := header_length_ge (depth p) (seedWidth p) x
  have hct : 1 ≤ (ULogTernaryNestedHeaderParser.counted x).length := by
    simp [counted_length]
  simp [source, ULogTernaryGuardedPumpSentinel.source, nested_length]
  omega

theorem reserve_ge (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    1 ≤ reserve nt p x := by
  unfold reserve; exact Nat.one_le_two_pow

theorem pool_decomp (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    K nt * copies nt p x + residue nt p x = pool nt p x := by
  simp only [copies, residue, pool, K, reserve,
    ULogTernaryMarginReserveBudget.iterations, ULogTernaryMarginReserveBudget.pairWidth]
  exact (ULogTernaryMarginReserveBudget.divide_decomposition nt
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x.length).symm

theorem corrected_length_le (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (correctedBits (codes M) M.blank x).length ≤ 2 * reserve nt p x := by
  have hR := reserve_ge nt p x
  have hntR := ULogTernaryGeneratedMarginEntryClock.alphabet_le_reserve nt p x
  have hw := window_bytes_le nt p x
  have hc := ULogTernaryGeneratedMarginEntryResources.corrected_length (codes M) M.blank x
  rw [hc]
  split_ifs with hx
  · have : nt + 1 ≤ reserve nt p x + 1 := by
      change nt ≤ reserve nt p x at hntR; omega
    omega
  · have : (x.length + 1) * (nt + 1) ≤
        (x.length + 2 * radius nt p x + 3) * (nt + 1) := by
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem loop_bound (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryBalancedBlankLoop.deadline nt
      (correctedBits (codes M) M.blank x).length (copies nt p x) (residue nt p x) ≤
      64 * (reserve nt p x) ^ 2 := by
  have hnt : 0 < nt := Nat.zero_lt_of_lt M.blank.isLt
  have hR := reserve_ge nt p x
  have hn := corrected_length_le M p x
  have hpool := pool_le nt p x
  have hd := pool_decomp nt p x
  have hN : 2 * (nt + 1) * copies nt p x + residue nt p x ≤ reserve nt p x := by
    have hK : 2 * (nt + 1) = K nt := rfl
    rw [hK, hd]; exact hpool
  exact loop_deadline_upper nt _ _ _ _ hnt hR hn hN

theorem caller_deadline_upper (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    deadline M p x ≤ 176 * (reserve nt p x) ^ 2 := by
  have he := ULogTernaryGeneratedMarginEntryClock.deadline_upper nt p x
  change compactDeadline nt p x ≤ 110 * (reserve nt p x) ^ 2 at he
  have hl := loop_bound M p x
  have hR := reserve_ge nt p x
  have hsq : 1 ≤ (reserve nt p x) ^ 2 := by
    have : 0 < (reserve nt p x) ^ 2 := pow_pos (by unfold reserve; positivity) _
    omega
  unfold deadline
  omega

theorem full_budget_upper (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    deadline M p x + 3 + 14 * (reserve nt p x) ^ 2 ≤ 256 * (reserve nt p x) ^ 2 := by
  have hc := caller_deadline_upper M p x
  have hR := reserve_ge nt p x
  have hsq : 1 ≤ (reserve nt p x) ^ 2 := by
    have : 0 < (reserve nt p x) ^ 2 := pow_pos (by unfold reserve; positivity) _
    omega
  omega

theorem full_budget_le_clock (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    deadline M p x + 3 + 14 * (reserve nt p x) ^ 2 ≤
      2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  have hd := full_budget_upper M p x
  have hs := counted_source_length_ge
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x
  have hf : 256 ≤ 2 ^ (2 * (source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    have h : (2 : Nat) ^ 9 ≤ 2 ^ (2 * (source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
    norm_num only [Nat.reducePow] at h; omega
  have he : ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x =
      2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (2 * (source
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    change 2 * (ULogTernaryGuardedPumpDelimiterInput.width
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x +
      (source (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    change 2 * (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
      (source (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 = _
    omega
  have hsq : (reserve nt p x) ^ 2 =
      2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) := by
    unfold reserve; rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hd ⊢
  rw [he, pow_add]
  have hmul :
      256 * 2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) ≤
        2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) *
          2 ^ (2 * (source
            (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 3) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right
      (2 ^ (2 * ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)) hf
  exact hd.trans hmul

theorem every_semantic_le (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {out : ULogSemantics.Config}
    (hw : semanticRun (ULogSemantics.start (input M p x)) w = some out) :
    w.length ≤ 176 * (reserve nt p x) ^ 2 :=
  (every_semantic_raw_length M p x hw).trans (caller_deadline_upper M p x)

def generated_margin_loop_clock_spec (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool) : Prop :=
  let R := reserve nt p x
  ULogTernaryBalancedBlankLoop.deadline nt
      (correctedBits (codes M) M.blank x).length (copies nt p x) (residue nt p x) ≤
      64 * R ^ 2 ∧
    deadline M p x ≤ 176 * R ^ 2 ∧
    deadline M p x + 3 + 14 * R ^ 2 ≤ 256 * R ^ 2 ∧
    deadline M p x + 3 + 14 * R ^ 2 ≤
      2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ∧
    (∀ w out, semanticRun (ULogSemantics.start (input M p x)) w = some out →
      w.length ≤ 176 * R ^ 2)

theorem generated_margin_loop_clock_spec_holds (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool) :
    generated_margin_loop_clock_spec M p x :=
  ⟨loop_bound M p x, caller_deadline_upper M p x, full_budget_upper M p x,
    full_budget_le_clock M p x, fun _ _ hw => every_semantic_le M p x hw⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginLoopClock
