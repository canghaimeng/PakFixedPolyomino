import PakFixedPolyomino.StandardBitPolynomialPayload
import PakFixedPolyomino.ULogPayloadClockBitWrapper
import PakFixedPolyomino.ULogRetainedPumpClockBitInput
import PakFixedPolyomino.ULogTernaryRetainedPumpResourceBounds

/-! Real polynomial-width and outer-clock input construction for the
decoded retained pump, for every natural-coefficient polynomial. All source
bits survive inside explicitly recoverable headers. Physical source
loading, finite-frame feasibility and actual interpreter time are separate. -/

namespace PakFixedPolyomino.ULogTernaryPolynomialPumpClockInput

set_option maxRecDepth 3000

open StandardBitTime ULogCompiler ULogBytecode
open ULogBootstrapExecution ULogAlphabet ULogProgram

def source (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitPolynomialPayload.iterateSquare (p.natDegree + 1)
    (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p) x)

def width (p : Polynomial Nat) (x : List Bool) : Nat :=
  StandardBitPolynomialPayload.width p x

def input (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap ULogTernaryRetainedCounterPump.program
    (StandardBitPolynomialPayload.payload p x)

def clockWidth (p : Polynomial Nat) (x : List Bool) : Nat :=
  2 * (width p x + (source p x).length + 1) + 1

theorem source_length_ge (p : Polynomial Nat) (x : List Bool) : 2 ≤ (source p x).length := by
  have h := StandardBitPolynomialPayload.iterate_length_ge (p.natDegree + 1)
    (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p) x)
  change 2 ≤ (StandardBitPolynomialPayload.iterateSquare (p.natDegree + 1)
    (StandardBitPolynomialPayload.seed (StandardBitPolynomialPayload.coefficientTotal p) x)).length
  have hs : 2 ≤ (StandardBitPolynomialPayload.seed
      (StandardBitPolynomialPayload.coefficientTotal p) x).length := by
    simp [StandardBitPolynomialPayload.seed]
    omega
  exact hs.trans h

theorem width_eq (p : Polynomial Nat) (x : List Bool) :
    width p x = (source p x).length ^ 2 := rfl

theorem source_fits (p : Polynomial Nat) (x : List Bool) :
    (source p x).length ≤ 2 ^ (width p x) := by
  have hn := source_length_ge p x
  have hk : (source p x).length ≤ width p x := by
    rw [width_eq, pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact (Nat.le_of_lt (Nat.lt_two_pow_self)).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hk)

theorem input_polyBitTime (p : Polynomial Nat) : PolyBitTime (input p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitPolynomialPayload.payload_polyBitTime p)
    (ULogPayloadClockBitWrapper.wrap_polyBitTime ULogTernaryRetainedCounterPump.program)

theorem padding_length (p : Polynomial Nat) (x : List Bool) :
    (ULogPayloadClockBitWrapper.padding (StandardBitPolynomialPayload.payload p x)).length =
      clockWidth p x := by
  rw [StandardBitPolynomialPayload.payload_layout]
  simp [ULogPayloadClockBitWrapper.padding, clockWidth, width, source, Nat.add_assoc]

theorem start_input (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input p x) =
      ULogSemantics.start (ULogTernaryRetainedCounterPump.input (width p x) (source p x)) := by
  rw [input, ULogPayloadClockBitWrapper.same_start, StandardBitPolynomialPayload.payload_layout]
  rfl

theorem deadline_le_clock (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x) ≤ 2 ^ (clockWidth p x) := by
  have hD := ULogTernaryRetainedPumpResourceBounds.deadline_upper
    (width p x) (source p x) (source_fits p x)
  have hs := source_length_ge p x
  have h5 : 5 ≤ 2 * (source p x).length + 3 := by omega
  have hfactor : 32 ≤ 2 ^ (2 * (source p x).length + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h5
  have hsum : clockWidth p x = 2 * width p x + (2 * (source p x).length + 3) := by
    unfold clockWidth; omega
  have hsq : (2 ^ width p x) ^ 2 = 2 ^ (2 * width p x) := by
    rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hD
  rw [hsum, pow_add]
  exact hD.trans (by nlinarith)

theorem every_raw_word_clock_bound (p : Polynomial Nat) (x w : List Bool)
    (out : ULogSemantics.Config)
    (hw : ULogFiniteTapeZipperRun.semanticRun (ULogSemantics.start (input p x)) w = some out) :
    w.length ≤ 2 ^ (clockWidth p x) := by
  rw [start_input] at hw
  exact (ULogTernaryRetainedPumpCounts.every_raw_prefix_length_le
    (width p x) (source p x) w out hw).trans (deadline_le_clock p x)

theorem polynomial_clock_input_spec (p : Polynomial Nat) :
    PolyBitTime (input p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, ULogSemantics.start (input p x) =
      ULogSemantics.start (ULogTernaryRetainedCounterPump.input (width p x) (source p x))) ∧
    (∀ x, decodeBinaryClock (List.replicate (clockWidth p x) (ulogCore clockZero) ++
      ulogCore clockOne :: [ulogCore clockSep]) = some (2 ^ (clockWidth p x))) ∧
    (∀ x, ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x) ≤ 2 ^ (clockWidth p x)) ∧
    (∀ x w out, ULogFiniteTapeZipperRun.semanticRun (ULogSemantics.start (input p x)) w = some out →
      w.length ≤ 2 ^ (clockWidth p x)) ∧
    (∀ x, StandardBitPolynomialPayload.recover p (StandardBitPolynomialPayload.payload p x) = x) := by
  refine ⟨input_polyBitTime p, StandardBitPolynomialPayload.width_dominates p,
    start_input p, ?_, deadline_le_clock p, every_raw_word_clock_bound p,
    StandardBitPolynomialPayload.recover_payload p⟩
  intro x
  exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth p x) []

end PakFixedPolyomino.ULogTernaryPolynomialPumpClockInput
