import PakFixedPolyomino.StandardBitPolynomialPayload
import PakFixedPolyomino.StandardBitRetainedPayload

/-! Effective polynomial width with an explicit original-source length
field. The field remains before the source when genuine zeros are later
appended. All maps use actual audited ordinary machines. Operational
crossing of the nested headers and loading remain separate. -/

namespace PakFixedPolyomino.StandardBitCountedPolynomialPayload

open StandardBitTime

def payload (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitPolynomialPayload.payload p (StandardBitRetainedPayload.payload x)

def width (p : Polynomial Nat) (x : List Bool) : Nat :=
  StandardBitPolynomialPayload.width p (StandardBitRetainedPayload.payload x)

def source (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitPolynomialPayload.iterateSquare (p.natDegree + 1)
    (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p)
      (StandardBitRetainedPayload.payload x))

theorem eval_monotone (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

theorem width_dominates (p : Polynomial Nat) (x : List Bool) :
    p.eval x.length ≤ width p x := by
  have hn : x.length ≤ (StandardBitRetainedPayload.payload x).length := by
    rw [StandardBitRetainedPayload.payload_length]
    omega
  exact (eval_monotone p hn).trans
    (StandardBitPolynomialPayload.width_dominates p (StandardBitRetainedPayload.payload x))

theorem payload_polyBitTime (p : Polynomial Nat) : PolyBitTime (payload p) :=
  StandardBitTimeComposition.polyBitTime_comp StandardBitRetainedPayload.payload_polyBitTime
    (StandardBitPolynomialPayload.payload_polyBitTime p)

theorem payload_layout (p : Polynomial Nat) (x : List Bool) :
    payload p x = List.replicate (width p x) false ++ true :: source p x :=
  StandardBitPolynomialPayload.payload_layout p (StandardBitRetainedPayload.payload x)

theorem original_length_field (p : Polynomial Nat) (x : List Bool) :
    StandardBitPolynomialPayload.stripIterations (p.natDegree + 1) (source p x) =
      List.replicate (StandardBitPolynomialPayload.coefficientTotal p + 2) false ++
        (List.replicate x.length false ++ true :: x) := by
  rw [source, StandardBitPolynomialPayload.strip_iterations_exact]
  rw [StandardBitPolynomialPayload.seed, StandardBitRetainedPayload.payload_eq_encode]

theorem decode_original_with_buffer (x buffer : List Bool) :
    ULogBytecode.decodePayloadWithPadding (StandardBitRetainedPayload.payload x ++ buffer) =
      some (x, buffer.length) := by
  simpa [StandardBitRetainedPayload.payload, ULogBytecode.encodePayload,
    List.append_assoc] using ULogBytecode.decodePayloadWithPadding_encode x buffer

theorem recover_original (p : Polynomial Nat) (x : List Bool) :
    ULogBytecode.decodePayload (StandardBitPolynomialPayload.recover p (payload p x)) =
      some x := by
  rw [payload, StandardBitPolynomialPayload.recover_payload]
  exact ULogBytecode.decodePayload_encode x []

theorem counted_polynomial_payload_spec (p : Polynomial Nat) :
    PolyBitTime (payload p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, payload p x = List.replicate (width p x) false ++ true :: source p x) ∧
    (∀ x, StandardBitPolynomialPayload.stripIterations (p.natDegree + 1) (source p x) =
      List.replicate (StandardBitPolynomialPayload.coefficientTotal p + 2) false ++
        (List.replicate x.length false ++ true :: x)) ∧
    (∀ x buffer, ULogBytecode.decodePayloadWithPadding
      (StandardBitRetainedPayload.payload x ++ buffer) = some (x, buffer.length)) ∧
    (∀ x, ULogBytecode.decodePayload
      (StandardBitPolynomialPayload.recover p (payload p x)) = some x) :=
  ⟨payload_polyBitTime p, width_dominates p, payload_layout p, original_length_field p,
    decode_original_with_buffer, recover_original p⟩

end PakFixedPolyomino.StandardBitCountedPolynomialPayload
