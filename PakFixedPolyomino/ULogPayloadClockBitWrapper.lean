import PakFixedPolyomino.StandardBitAppendLengthZeros
import PakFixedPolyomino.StandardBitRetainedPayload
import PakFixedPolyomino.StandardBitPrepend
import PakFixedPolyomino.ULogCompiler

/-! Ordinary clocked encoding for arbitrary binary payloads. The input
constructor works independently of how a source/counter payload was built;
later polynomial padding can therefore use the same actual tape machines.
No generator run, physical clock sufficiency or frame invariant is assumed. -/

namespace PakFixedPolyomino.ULogPayloadClockBitWrapper

set_option maxRecDepth 3000

open ULogCompiler ULogBytecode StandardBitTime

def padding (y : List Bool) : List Bool := List.replicate (2 * y.length + 1) false

def wrap {ns nt : Nat} (p : BoundedProgram ns nt) (y : List Bool) : List Bool :=
  encodeProgram (compile p) ++ encodePayload y (padding y)

theorem pipeline_eq_wrap {ns nt : Nat} (p : BoundedProgram ns nt) (y : List Bool) :
    encodeProgram (compile p) ++
      StandardBitAppendLengthZeros.output (StandardBitRetainedPayload.payload y) = wrap p y := by
  rw [StandardBitAppendLengthZeros.output, StandardBitRetainedPayload.payload_length]
  simp [wrap, padding, StandardBitRetainedPayload.payload, encodePayload, List.append_assoc]

theorem wrap_polyBitTime {ns nt : Nat} (p : BoundedProgram ns nt) : PolyBitTime (wrap p) := by
  have hQ := StandardBitTimeComposition.polyBitTime_comp
    StandardBitRetainedPayload.payload_polyBitTime StandardBitAppendLengthZeros.output_polyBitTime
  have h := StandardBitTimeComposition.polyBitTime_comp hQ
    (StandardBitPrepend.fixed_prefix_polyBitTime (encodeProgram (compile p)))
  have he : wrap p = (fun y => encodeProgram (compile p) ++
      StandardBitAppendLengthZeros.output (StandardBitRetainedPayload.payload y)) := by
    funext y
    exact (pipeline_eq_wrap p y).symm
  rw [he]
  simpa only [Function.comp_def] using h

theorem length_wrap {ns nt : Nat} (p : BoundedProgram ns nt) (y : List Bool) :
    (wrap p y).length = (encodeProgram (compile p)).length + 4 * y.length + 2 := by
  simp only [wrap, List.length_append, length_encodePayload, padding, List.length_replicate]
  omega

theorem decoded_payload {ns nt : Nat} (p : BoundedProgram ns nt) (y : List Bool) :
    decodeProgramPrefix (wrap p y) = some (compile p, encodePayload y (padding y)) ∧
    decodePayloadWithPadding (encodePayload y (padding y)) = some (y, 2 * y.length + 1) := by
  simp [wrap, padding]

theorem same_start {ns nt : Nat} (p : BoundedProgram ns nt) (y : List Bool) :
    ULogSemantics.start (wrap p y) = ULogSemantics.start (encodeInstance p y) := by
  simp only [wrap, encodeInstance, ULogSemantics.start, decodeProgramPrefix_encode_prefix,
    decodePayload_encode]

theorem actual_clock_wrapper_spec {ns nt : Nat} (p : BoundedProgram ns nt) :
    PolyBitTime (wrap p) ∧
    (∀ y, (wrap p y).length = (encodeProgram (compile p)).length + 4 * y.length + 2) ∧
    (∀ y, decodeProgramPrefix (wrap p y) = some (compile p, encodePayload y (padding y)) ∧
      decodePayloadWithPadding (encodePayload y (padding y)) = some (y, 2 * y.length + 1)) ∧
    (∀ y, ULogSemantics.start (wrap p y) = ULogSemantics.start (encodeInstance p y)) :=
  ⟨wrap_polyBitTime p, length_wrap p, decoded_payload p, same_start p⟩

end PakFixedPolyomino.ULogPayloadClockBitWrapper
