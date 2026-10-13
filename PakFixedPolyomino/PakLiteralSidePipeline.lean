import PakFixedPolyomino.StandardBitAppendThirtySixLengthZeros
import PakFixedPolyomino.StandardBitRetainedPayload
import PakFixedPolyomino.StandardBitAppend
import PakFixedPolyomino.StandardBitPrepend
import PakFixedPolyomino.PakFixedPitchBinaryInstance

/-! Exact decomposition of the unchanged literal side word. The final
36*length padding and leading bit use genuine ordinary tape machines.
The two reversal operations still need their separate operational proof;
no bit-time theorem for the entire pipeline is asserted in this module. -/
namespace PakFixedPolyomino.PakLiteralSidePipeline
open StandardBitTime StandardBitTimeComposition

def reversePayload (x : List Bool) : List Bool :=
  (StandardBitRetainedPayload.payload x.reverse).reverse

theorem reversePayload_eq (x : List Bool) : reversePayload x =
    x ++ [true] ++ List.replicate x.length false := by
  simp [reversePayload,StandardBitRetainedPayload.payload_eq_encode,
    List.reverse_append,List.reverse_cons,List.append_assoc]

def header (x : List Bool) : List Bool := reversePayload x ++ [true]

theorem header_eq (x : List Bool) : header x =
    x ++ [true] ++ List.replicate x.length false ++ [true] := by
  rw [header,reversePayload_eq]

@[simp] theorem header_length (x : List Bool) : (header x).length = 2*x.length+2 := by
  simp [header_eq]
  omega

def assemble (y : List Bool) : List Bool :=
  true :: StandardBitAppendThirtySixLengthZeros.output y

theorem assemble_polyBitTime : PolyBitTime assemble :=
  polyBitTime_comp StandardBitAppendThirtySixLengthZeros.output_polyBitTime
    (StandardBitPrepend.prepend_polyBitTime true)

def pipeline (x : List Bool) : List Bool := assemble (header x)

theorem pipeline_eq_encodedWord (x : List Bool) : pipeline x = ConcretePakSide.encodedWord x := by
  have hpad : 36*(header x).length = ConcretePakSide.paddingLength x.length := by
    rw [header_length]
    unfold ConcretePakSide.paddingLength
    ring
  unfold pipeline assemble StandardBitAppendThirtySixLengthZeros.output
  rw [hpad,header_eq]
  simp [ConcretePakSide.encodedWord,List.cons_append,List.append_assoc]

theorem pipeline_reverse_eq_sideBits (x : List Bool) :
    (pipeline x).reverse = PakFixedPitchBinaryInstance.sideBits x := by
  rw [pipeline_eq_encodedWord]
  rfl

theorem literal_side_pipeline_spec :
    (∀ x,header x = x++[true]++List.replicate x.length false++[true]) ∧
    (∀ x,(header x).length = 2*x.length+2) ∧
    PolyBitTime assemble ∧
    (∀ x,pipeline x = ConcretePakSide.encodedWord x) ∧
    (∀ x,(pipeline x).reverse = PakFixedPitchBinaryInstance.sideBits x) :=
  ⟨header_eq,header_length,assemble_polyBitTime,pipeline_eq_encodedWord,
    pipeline_reverse_eq_sideBits⟩

end PakFixedPolyomino.PakLiteralSidePipeline
