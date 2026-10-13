import PakFixedPolyomino.StandardBitCountedPolynomialPayload
import PakFixedPolyomino.ULogTernaryPumpInputSpec

/-! Genuine ordinary input construction for the actual ternary pump,
retaining the original length field under nested headers. Old admitted
maps and tables are preserved. This is a decoded count/clock/format
theorem; the operational parser and physical loader are separate. -/

namespace PakFixedPolyomino.ULogTernaryCountedPumpInput

open ULogFiniteTapeZipperRun ULogBootstrapExecution
open ULogAlphabet MStarParserExecution

def input (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogTernaryPolynomialPumpClockInput.input p (StandardBitRetainedPayload.payload x)

def width (p : Polynomial Nat) (x : List Bool) : Nat :=
  StandardBitCountedPolynomialPayload.width p x

def source (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitCountedPolynomialPayload.source p x

def clockWidth (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryPolynomialPumpClockInput.clockWidth p (StandardBitRetainedPayload.payload x)

theorem input_polyBitTime (p : Polynomial Nat) : StandardBitTime.PolyBitTime (input p) :=
  StandardBitTimeComposition.polyBitTime_comp StandardBitRetainedPayload.payload_polyBitTime
    (ULogTernaryPolynomialPumpClockInput.input_polyBitTime p)

theorem start_input (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input p x) = ULogSemantics.start
      (ULogTernaryRetainedCounterPump.input (width p x) (source p x)) :=
  ULogTernaryPolynomialPumpClockInput.start_input p (StandardBitRetainedPayload.payload x)

theorem counted_pump_input_spec (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, semanticRun (ULogSemantics.start (input p x))
      (List.replicate (ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x)) false) =
      some (ULogTernaryRetainedPumpCounts.finalConfig (width p x) (source p x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x) ≤ T then 1 else 0) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input p x)) w = some out →
      w.length ≤ 2 ^ clockWidth p x ∧ ULogBootstrapExecution.SemanticTapeSymbolsLtThree out) ∧
    (∀ x, decodeBinaryClock
      (List.replicate (clockWidth p x) (ulogCore clockZero) ++
        ulogCore clockOne :: [ulogCore clockSep]) = some (2 ^ clockWidth p x)) ∧
    (∀ x, StandardBitPolynomialPayload.stripIterations (p.natDegree + 1) (source p x) =
      List.replicate (StandardBitPolynomialPayload.coefficientTotal p + 2) false ++
        (List.replicate x.length false ++ true :: x)) ∧
    (∀ x buffer, ULogBytecode.decodePayloadWithPadding
      (StandardBitRetainedPayload.payload x ++ buffer) = some (x, buffer.length)) := by
  refine ⟨input_polyBitTime p, StandardBitCountedPolynomialPayload.width_dominates p,
    ?_, ?_, ?_, ?_, StandardBitCountedPolynomialPayload.original_length_field p,
    StandardBitCountedPolynomialPayload.decode_original_with_buffer⟩
  · intro x
    exact ULogTernaryPumpInputSpec.actual_encoded_run p (StandardBitRetainedPayload.payload x)
  · intro x T
    exact ULogTernaryPumpInputSpec.all_cutoff_counts p (StandardBitRetainedPayload.payload x) T
  · intro x w out hr
    exact ULogTernaryPumpInputSpec.every_raw_clock_symbols p
      (StandardBitRetainedPayload.payload x) w out hr
  · intro x
    exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth p x) []

end PakFixedPolyomino.ULogTernaryCountedPumpInput
