import PakFixedPolyomino.StandardBitTimeComposition

/-! Numerical bounds on actual polynomial transition costs evaluated at an
exponential physical word length. This proves a bound on those transitions;
it does not replace execution proofs by arithmetic-operation counts. -/
namespace PakFixedPolyomino.StandardPolynomialExponentialBounds
open Polynomial

theorem eval_two_pow_bound (p : Polynomial Nat) :
    ∃ a b : Nat, ∀ n,p.eval (2^n)≤2^(a*n+b) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,b,hp⟩ := hp
    obtain ⟨c,d,hq⟩ := hq
    refine ⟨a+c,b+d+1,?_⟩
    intro n
    have h1 : 2^(a*n+b)≤2^((a+c)*n+(b+d)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    have h2 : 2^(c*n+d)≤2^((a+c)*n+(b+d)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    rw [eval_add]
    calc
      p.eval (2^n)+q.eval (2^n)≤2^((a+c)*n+(b+d))+2^((a+c)*n+(b+d)) :=
        Nat.add_le_add ((hp n).trans h1) ((hq n).trans h2)
      _=2^((a+c)*n+(b+d+1)) := by rw [show (a+c)*n+(b+d+1)=((a+c)*n+(b+d))+1 by omega,pow_succ];omega
  | monomial k c =>
    refine ⟨k,c,?_⟩
    intro n
    rw [eval_monomial]
    calc
      c*(2^n)^k≤2^c*(2^n)^k :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
      _=2^(k*n+c) := by rw [← pow_mul,← pow_add];congr 1;ring

theorem polynomial_bound (p : Polynomial Nat) :
    ∃ q : Polynomial Nat, ∀ n,p.eval n≤2^q.eval n := by
  obtain ⟨a,b,h⟩ := eval_two_pow_bound p
  refine ⟨C a*X+C b,?_⟩
  intro n
  have he := (StandardBitTimeComposition.eval_mono p
    (Nat.le_of_lt Nat.lt_two_pow_self : n≤2^n)).trans (h n)
  simpa only [eval_add,eval_mul,eval_C,eval_X] using he

theorem evaluated_bound (p : Polynomial Nat) (L : Nat → Nat) (q : Polynomial Nat)
    (hL : ∀ n,L n≤2^q.eval n) :
    ∃ r : Polynomial Nat, ∀ n,p.eval (L n)≤2^r.eval n := by
  obtain ⟨a,b,h⟩ := eval_two_pow_bound p
  refine ⟨C a*q+C b,?_⟩
  intro n
  have he := (StandardBitTimeComposition.eval_mono p (hL n)).trans (h (q.eval n))
  simpa only [eval_add,eval_mul,eval_C] using he

end PakFixedPolyomino.StandardPolynomialExponentialBounds
