import PakFixedPolyomino.StandardBitAppendLengthZeros
import PakFixedPolyomino.StandardBitRetainedPayload
import PakFixedPolyomino.StandardBitPrepend
import PakFixedPolyomino.ULogRetainedCounterPumpResourceBounds
import PakFixedPolyomino.ULogFrameReady

/-! Actual ordinary BIT construction of a retained input with a real outer
clock field. Its decoded clock covers the internally constructed pump run.
The Fin4 pump still needs the ternary repair, and physical capacity/trace
instantiation remain separate; no physical resource certificate is assumed. -/

namespace PakFixedPolyomino.ULogRetainedPumpClockBitInput

set_option maxRecDepth 3000

open StandardBitTime ULogCompiler ULogBytecode
open ULogBootstrapExecution ULogAlphabet ULogProgram

def padding (x : List Bool) : List Bool := List.replicate (4 * x.length + 3) false

def inputFor {ns nt : Nat} (p : BoundedProgram ns nt) (x : List Bool) : List Bool :=
  encodeProgram (compile p) ++ encodePayload (StandardBitRetainedPayload.payload x) (padding x)

def input (x : List Bool) : List Bool := inputFor ULogRetainedCounterPump.program x

theorem pipeline_eq_inputFor {ns nt : Nat} (p : BoundedProgram ns nt) (x : List Bool) :
    encodeProgram (compile p) ++ StandardBitAppendLengthZeros.output
      (StandardBitRetainedPayload.payload (StandardBitRetainedPayload.payload x)) = inputFor p x := by
  have hl : (StandardBitRetainedPayload.payload (StandardBitRetainedPayload.payload x)).length =
      4 * x.length + 3 := by simp; omega
  rw [StandardBitAppendLengthZeros.output, hl]
  simp [inputFor, padding, StandardBitRetainedPayload.payload, encodePayload, List.append_assoc]

theorem inputFor_polyBitTime {ns nt : Nat} (p : BoundedProgram ns nt) : PolyBitTime (inputFor p) := by
  have hP := StandardBitTimeComposition.polyBitTime_comp
    StandardBitRetainedPayload.payload_polyBitTime StandardBitRetainedPayload.payload_polyBitTime
  have hQ := StandardBitTimeComposition.polyBitTime_comp hP
    StandardBitAppendLengthZeros.output_polyBitTime
  have h := StandardBitTimeComposition.polyBitTime_comp hQ
    (StandardBitPrepend.fixed_prefix_polyBitTime (encodeProgram (compile p)))
  have he : inputFor p = (fun x => encodeProgram (compile p) ++
      StandardBitAppendLengthZeros.output
        (StandardBitRetainedPayload.payload (StandardBitRetainedPayload.payload x))) := by
    funext x
    exact (pipeline_eq_inputFor p x).symm
  rw [he]
  simpa only [Function.comp_def] using h

theorem input_polyBitTime : PolyBitTime input := inputFor_polyBitTime _

theorem input_length (x : List Bool) :
    (input x).length = (encodeProgram (compile ULogRetainedCounterPump.program)).length +
      8 * x.length + 6 := by
  simp only [input, inputFor, List.length_append, length_encodePayload, padding,
    List.length_replicate, StandardBitRetainedPayload.payload_length]
  omega

theorem start_inputFor {ns nt : Nat} (p : BoundedProgram ns nt) (x : List Bool) :
    ULogSemantics.start (inputFor p x) =
      ULogSemantics.start (encodeInstance p (StandardBitRetainedPayload.payload x)) := by
  simp only [inputFor, encodeInstance, ULogSemantics.start, decodeProgramPrefix_encode_prefix,
    decodePayload_encode]

theorem start_input (x : List Bool) :
    ULogSemantics.start (input x) = ULogSemantics.start (ULogRetainedCounterPump.input x.length x) := by
  rw [input, start_inputFor]
  exact congrArg (fun source => ULogSemantics.start (encodeInstance ULogRetainedCounterPump.program source))
    (StandardBitRetainedPayload.payload_eq_encode x)

/-- Kernel-reduced clock symbols; no inherited native clock computation lemma. -/
theorem power_clock_decode (k : Nat) (tail : List Tape) :
    decodeBinaryClock (List.replicate k (ulogCore clockZero) ++
      ulogCore clockOne :: ulogCore clockSep :: tail) = some (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    change (decodeBinaryClock (List.replicate k (ulogCore clockZero) ++
      ulogCore clockOne :: ulogCore clockSep :: tail)).map (2 * ·) = some (2 ^ (k + 1))
    rw [ih]
    simp [pow_succ, Nat.mul_comm]

theorem deadline_le_clock (x : List Bool) :
    ULogRetainedCounterPumpCounts.deadline x.length x ≤ 2 ^ (4 * x.length + 3) := by
  by_cases hn : x.length = 0
  · have hx : x = [] := by
      cases x with
      | nil => rfl
      | cons b bs => simp at hn
    subst x
    simp [ULogRetainedCounterPumpCounts.deadline, ULogRetainedCounterPumpCounts.bodyFuel]
  · have hlen : x.length ≤ 2 ^ x.length := by have h := x.length.lt_two_pow_self; omega
    have hD := ULogRetainedCounterPumpResourceBounds.deadline_upper x.length x hlen
    have h5 : 5 ≤ 2 * x.length + 3 := by omega
    have hpow : 32 ≤ 2 ^ (2 * x.length + 3) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h5
    have hsq : (2 ^ x.length) ^ 2 = 2 ^ (2 * x.length) := by
      rw [Nat.mul_comm 2 x.length, pow_mul]
    have hsum : 4 * x.length + 3 = 2 * x.length + (2 * x.length + 3) := by omega
    rw [hsq] at hD
    rw [hsum, pow_add]
    exact hD.trans (by nlinarith)

theorem every_raw_word_clock_bound (x w : List Bool) (out : ULogSemantics.Config)
    (hrun : ULogFiniteTapeZipperRun.semanticRun (ULogSemantics.start (input x)) w = some out) :
    w.length ≤ 2 ^ (4 * x.length + 3) := by
  rw [start_input] at hrun
  exact (ULogRetainedCounterPumpCounts.every_raw_prefix_length_le x.length x w out hrun).trans
    (deadline_le_clock x)

theorem clock_input_spec :
    PolyBitTime input ∧
    (∀ x, (input x).length = (encodeProgram (compile ULogRetainedCounterPump.program)).length +
      8 * x.length + 6) ∧
    (∀ x, ULogSemantics.start (input x) = ULogSemantics.start (ULogRetainedCounterPump.input x.length x)) ∧
    (∀ x, decodeBinaryClock (List.replicate (padding x).length (ulogCore clockZero) ++
      ulogCore clockOne :: [ulogCore clockSep]) = some (2 ^ (4 * x.length + 3))) ∧
    (∀ x, ULogRetainedCounterPumpCounts.deadline x.length x ≤ 2 ^ (4 * x.length + 3)) ∧
    (∀ x w out, ULogFiniteTapeZipperRun.semanticRun (ULogSemantics.start (input x)) w = some out →
      w.length ≤ 2 ^ (4 * x.length + 3)) := by
  refine ⟨input_polyBitTime, input_length, start_input, ?_, deadline_le_clock,
    every_raw_word_clock_bound⟩
  intro x
  simpa only [padding, List.length_replicate] using power_clock_decode (4 * x.length + 3) []

end PakFixedPolyomino.ULogRetainedPumpClockBitInput
