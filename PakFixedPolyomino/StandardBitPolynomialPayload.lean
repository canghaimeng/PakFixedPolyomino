import PakFixedPolyomino.StandardBitSquarePayload
import PakFixedPolyomino.StandardBitPrepend
import Mathlib.Algebra.Polynomial.Degree.Support

/-! Effective arbitrary-polynomial unary width via a fixed number of real
ordinary square-payload encoders. The original source is retained under
explicit nested headers. This proves the input map's genuine bit-time;
physical parsing/loading of the nested headers remains separate. -/

namespace PakFixedPolyomino.StandardBitPolynomialPayload

open StandardBitTime StandardBitTimeComposition Polynomial

def coefficientTotal (p : Polynomial Nat) : Nat :=
  ∑ i ∈ p.support, p.coeff i

theorem polynomial_envelope (p : Polynomial Nat) (n : Nat) :
    p.eval n ≤ coefficientTotal p * (n + 1) ^ p.natDegree := by
  rw [eval_eq_sum, sum_def]
  calc
    (∑ i ∈ p.support, p.coeff i * n ^ i) ≤
        ∑ i ∈ p.support, p.coeff i * (n + 1) ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
        (Nat.pow_le_pow_right (Nat.succ_pos n) (p.le_natDegree_of_mem_supp i hi))
    _ = coefficientTotal p * (n + 1) ^ p.natDegree := by
      simp only [coefficientTotal, Finset.sum_mul]

def iterateSquare : Nat → List Bool → List Bool
  | 0, x => x
  | d + 1, x => StandardBitSquarePayload.squarePayload (iterateSquare d x)

theorem square_length_lower (x : List Bool) :
    x.length ^ 2 ≤ (StandardBitSquarePayload.squarePayload x).length := by
  rw [StandardBitSquarePayload.squarePayload_length, pow_two]
  omega

theorem iterate_length_lower (d : Nat) (x : List Bool) :
    x.length ^ (2 ^ d) ≤ (iterateSquare d x).length := by
  induction d with
  | zero => simp [iterateSquare]
  | succ d ih =>
      have hh := (Nat.pow_le_pow_left ih 2).trans (square_length_lower (iterateSquare d x))
      simpa only [iterateSquare, pow_succ, pow_mul] using hh

def seed (c : Nat) (x : List Bool) : List Bool := List.replicate (c + 2) false ++ x

theorem iterate_length_ge (d : Nat) (x : List Bool) :
    x.length ≤ (iterateSquare d x).length := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [iterateSquare, StandardBitSquarePayload.squarePayload_length]
      omega

def payload (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitSquarePayload.squarePayload
    (iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x))

def width (p : Polynomial Nat) (x : List Bool) : Nat :=
  (iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x)).length ^ 2

theorem payload_layout (p : Polynomial Nat) (x : List Bool) :
    payload p x = List.replicate (width p x) false ++ true ::
      iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x) := by
  simp [payload, width, StandardBitSquarePayload.squarePayload, pow_two]

theorem width_dominates (p : Polynomial Nat) (x : List Bool) :
    p.eval x.length ≤ width p x := by
  let L := (seed (coefficientTotal p) x).length
  have hlen : L = coefficientTotal p + 2 + x.length := by simp [L, seed]
  have hbase : 1 ≤ L := by omega
  have hn : x.length + 1 ≤ L := by omega
  have hc : coefficientTotal p ≤ L := by omega
  have hd : p.natDegree + 1 ≤ 2 ^ (p.natDegree + 1) :=
    Nat.le_of_lt (Nat.lt_two_pow_self)
  have hpoly : p.eval x.length ≤ L ^ (p.natDegree + 1) := by
    calc p.eval x.length ≤ coefficientTotal p * (x.length + 1) ^ p.natDegree :=
        polynomial_envelope p x.length
      _ ≤ L * L ^ p.natDegree := Nat.mul_le_mul hc (Nat.pow_le_pow_left hn _)
      _ = L ^ (p.natDegree + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _
  have hiter : L ^ (p.natDegree + 1) ≤
      (iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x)).length :=
    (Nat.pow_le_pow_right hbase hd).trans (iterate_length_lower _ _)
  have hlarge : 1 ≤ (iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x)).length :=
    (Nat.one_le_pow _ _ hbase).trans hiter
  unfold width
  exact hpoly.trans (hiter.trans (by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ hlarge))

theorem seed_polyBitTime (c : Nat) : PolyBitTime (seed c) :=
  StandardBitPrepend.fixed_prefix_polyBitTime (List.replicate (c + 2) false)

theorem seeded_iteration_polyBitTime (c d : Nat) :
    PolyBitTime (fun x => iterateSquare d (seed c x)) := by
  induction d with
  | zero => exact seed_polyBitTime c
  | succ d ih =>
      exact polyBitTime_comp ih StandardBitSquarePayload.squarePayload_polyBitTime

theorem payload_polyBitTime (p : Polynomial Nat) : PolyBitTime (payload p) :=
  polyBitTime_comp (seeded_iteration_polyBitTime (coefficientTotal p) (p.natDegree + 1))
    StandardBitSquarePayload.squarePayload_polyBitTime

def dropHeader : List Bool → List Bool
  | [] => []
  | false :: xs => dropHeader xs
  | true :: xs => xs

theorem dropHeader_zero_prefix (k : Nat) (x : List Bool) :
    dropHeader (List.replicate k false ++ true :: x) = x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, dropHeader] using ih

def stripIterations : Nat → List Bool → List Bool
  | 0, x => x
  | d + 1, x => stripIterations d (dropHeader x)

theorem strip_iterations_exact (d : Nat) (x : List Bool) :
    stripIterations d (iterateSquare d x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simpa [iterateSquare, stripIterations, StandardBitSquarePayload.squarePayload,
        dropHeader_zero_prefix] using ih

def recover (p : Polynomial Nat) (y : List Bool) : List Bool :=
  (stripIterations (p.natDegree + 2) y).drop (coefficientTotal p + 2)

theorem recover_payload (p : Polynomial Nat) (x : List Bool) :
    recover p (payload p x) = x := by
  have hp : payload p x = iterateSquare (p.natDegree + 2) (seed (coefficientTotal p) x) := rfl
  rw [recover, hp, strip_iterations_exact]
  simp [seed]

theorem polynomial_payload_spec (p : Polynomial Nat) :
    PolyBitTime (payload p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, payload p x = List.replicate (width p x) false ++ true ::
      iterateSquare (p.natDegree + 1) (seed (coefficientTotal p) x)) ∧
    (∀ x, recover p (payload p x) = x) :=
  ⟨payload_polyBitTime p, width_dominates p, payload_layout p, recover_payload p⟩

end PakFixedPolyomino.StandardBitPolynomialPayload
