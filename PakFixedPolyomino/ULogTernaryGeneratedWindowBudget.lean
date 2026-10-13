import PakFixedPolyomino.ULogTernaryGeneratedSourceExpansion
import PakFixedPolyomino.StandardMachineWindowInitialLayout

/-! Physically fitting ordinary input windows inside the actual generated
reserve. Extra polynomial padding is part of the compact bit input. This
proves available cells, not execution of the remaining margin/head loader. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedWindowBudget

open ULogTernaryGeneratedSourceExpansion (paddedPolynomial self_le_pow_two)

noncomputable def marginPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  p + Polynomial.C 6

noncomputable def width (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedSourceExpansion.width nt (marginPolynomial p) x

noncomputable def radius (p : Polynomial Nat) (x : List Bool) : Nat :=
  2 ^ p.eval x.length

theorem width_lower (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    p.eval x.length + nt + x.length + 8 ≤ width nt p x := by
  have h := StandardBitCountedPolynomialPayload.width_dominates
    (paddedPolynomial nt (marginPolynomial p)) x
  simp only [paddedPolynomial, marginPolynomial, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] at h
  exact Nat.le_trans (by omega) h

theorem window_fits (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    (x.length + 2 * radius p x + 3) * (nt + 1) + 2 ≤ 2 ^ width nt p x := by
  have hB : 1 ≤ radius p x := by
    have hpos : 0 < radius p x := by unfold radius; positivity
    omega
  have hshape : x.length + 2 * radius p x + 3 ≤ (x.length + 5) * radius p x := by
    nlinarith
  have hcoeff : (nt + 1) * (x.length + 5) ≤ 2 ^ (nt + x.length + 6) := by
    have h := Nat.mul_le_mul (self_le_pow_two (nt + 1)) (self_le_pow_two (x.length + 5))
    rw [← pow_add] at h
    convert h using 1 <;> congr 1 <;> omega
  have hcoeff2 : (nt + 1) * (x.length + 5) + 2 ≤ 2 ^ (nt + x.length + 8) := by
    have hp : 0 < 2 ^ (nt + x.length + 6) := by positivity
    rw [show nt + x.length + 8 = nt + x.length + 6 + 2 by omega, pow_add]
    norm_num only [pow_two] at *
    nlinarith
  have hcost : (x.length + 2 * radius p x + 3) * (nt + 1) + 2 ≤
      ((nt + 1) * (x.length + 5) + 2) * radius p x := by
    have hm := Nat.mul_le_mul_right (nt + 1) hshape
    nlinarith
  have hmul := Nat.mul_le_mul hcoeff2 (Nat.le_refl (radius p x))
  have hpow : 2 ^ (nt + x.length + 8) * radius p x =
      2 ^ (p.eval x.length + nt + x.length + 8) := by
    unfold radius
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hmul
  exact hcost.trans (hmul.trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (width_lower nt p x)))

theorem remaining_reserve_fits_margins (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    (2 * radius p x + 3) * (nt + 1) + 1 ≤
      2 ^ width nt p x - 1 - nt * x.length := by
  have h := window_fits nt p x
  rw [show x.length + 2 * radius p x + 3 = x.length + (2 * radius p x + 3) by omega,
    Nat.add_mul] at h
  have hprod : x.length * (nt + 1) = nt * x.length + x.length := by ring
  rw [hprod] at h
  omega

theorem generated_window_budget_spec {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (StandardMachineWindowBridge.inputWindow M x (radius p x)).cells =
      List.replicate (radius p x + 1) M.blank ++ StandardMachineWindowInitialLayout.sourceSymbols M x ++
        List.replicate (radius p x + 2) M.blank ∧
    (StandardMachineWindowBridge.inputWindow M x (radius p x)).head.val = radius p x + 1 ∧
    ((StandardMachineWindowBridge.inputWindow M x (radius p x)).cells.length * (nt + 1) + 2 ≤
      2 ^ width nt p x) ∧
    ((2 * radius p x + 3) * (nt + 1) + 1 ≤
      (ULogTernaryGeneratedSourceExpansion.buffer nt (width nt p x) x).length) := by
  have layout := StandardMachineWindowInitialLayout.initial_layout_spec M x (radius p x)
  refine ⟨layout.1, layout.2.1, ?_, ?_⟩
  · rw [layout.2.2]
    exact window_fits nt p x
  · simpa [ULogTernaryGeneratedSourceExpansion.buffer] using remaining_reserve_fits_margins nt p x

def alphabet_positive {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) : 0 < nt :=
  lt_of_le_of_lt (Nat.zero_le M.blank.val) M.blank.isLt

def sourceCodes {ns nt : Nat} (M : StandardNondeterministicMachine.Machine ns nt 2)
    (a : Fin 3) : Fin nt :=
  if a.val = 0 then M.zero else if a.val = 1 then M.one else M.blank

noncomputable def input {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) : List Bool → List Bool :=
  ULogTernaryGeneratedSourceExpansion.input (alphabet_positive M) (sourceCodes M) false (marginPolynomial p)

theorem input_polyBitTime {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input M p) :=
  ULogTernaryGeneratedSourceExpansion.input_polyBitTime
    (alphabet_positive M) (sourceCodes M) false (marginPolynomial p)

/-- Actual compact BIT input with provably sufficient remaining reserve for
the ordinary window. Generation of its blank cells and head flag is pending. -/
theorem generated_window_bit_budget_spec {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input M p) ∧
    sourceCodes M 0 = M.zero ∧ sourceCodes M 1 = M.one ∧ sourceCodes M 2 = M.blank ∧
    (∀ x, (StandardMachineWindowBridge.inputWindow M x (radius p x)).cells =
      List.replicate (radius p x + 1) M.blank ++ StandardMachineWindowInitialLayout.sourceSymbols M x ++
        List.replicate (radius p x + 2) M.blank ∧
      (StandardMachineWindowBridge.inputWindow M x (radius p x)).head.val = radius p x + 1 ∧
      ((StandardMachineWindowBridge.inputWindow M x (radius p x)).cells.length * (nt + 1) + 2 ≤
        2 ^ width nt p x) ∧
      ((2 * radius p x + 3) * (nt + 1) + 1 ≤
        (ULogTernaryGeneratedSourceExpansion.buffer nt (width nt p x) x).length)) := by
  exact ⟨input_polyBitTime M p, rfl, rfl, rfl, generated_window_budget_spec M p⟩

end PakFixedPolyomino.ULogTernaryGeneratedWindowBudget
