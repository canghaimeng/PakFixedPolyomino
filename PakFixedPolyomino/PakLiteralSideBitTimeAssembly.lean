import PakFixedPolyomino.PakLiteralSidePipeline

/-! Exact composition interface for the unchanged instance map. The explicit
reversal premise is an explicit hypothesis of this intermediate assembly. No closed
instance runtime or original completeness theorem is asserted here. -/
namespace PakFixedPolyomino.PakLiteralSideBitTimeAssembly
open StandardBitTime StandardBitTimeComposition PakLiteralSidePipeline
open PakFixedPitchBinaryInstance
open StandardNondeterministicMachine (Machine)

theorem reversePayload_polyBitTime (hr : PolyBitTime (List.reverse : List Bool → List Bool)) :
    PolyBitTime reversePayload :=
  polyBitTime_comp (polyBitTime_comp hr StandardBitRetainedPayload.payload_polyBitTime) hr

theorem header_polyBitTime (hr : PolyBitTime (List.reverse : List Bool → List Bool)) :
    PolyBitTime header :=
  polyBitTime_comp (reversePayload_polyBitTime hr) (StandardBitAppend.append_polyBitTime true)

theorem pipeline_polyBitTime (hr : PolyBitTime (List.reverse : List Bool → List Bool)) :
    PolyBitTime pipeline :=
  polyBitTime_comp (header_polyBitTime hr) assemble_polyBitTime

theorem sideBits_polyBitTime (hr : PolyBitTime (List.reverse : List Bool → List Bool)) :
    PolyBitTime sideBits := by
  have h : (List.reverse : List Bool → List Bool) ∘ pipeline = sideBits :=
    funext pipeline_reverse_eq_sideBits
  rw [← h]
  exact polyBitTime_comp (pipeline_polyBitTime hr) hr

attribute [local irreducible] ULogTernaryGeneratedMarginScanner.input
  PakFixedPitchBinaryInstance.pitchMap PakFixedPitchBinaryInstance.sideBits

theorem abstract_composition (f g h : List Bool → List Bool) :
    (fun x => f (g (h x))) = (f ∘ g) ∘ h := rfl

theorem instanceBits_eq_composition {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    instanceBits M p = (pitchMap ∘ sideBits) ∘ ULogTernaryGeneratedMarginScanner.input M p := by
  exact abstract_composition pitchMap sideBits (ULogTernaryGeneratedMarginScanner.input M p)

theorem instanceBits_polyBitTime (hr : PolyBitTime (List.reverse : List Bool → List Bool))
    {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (instanceBits M p) := by
  rw [instanceBits_eq_composition]
  exact polyBitTime_comp (f := ULogTernaryGeneratedMarginScanner.input M p)
    (g := pitchMap ∘ sideBits) (ULogTernaryGeneratedMarginScanner.input_polyBitTime M p)
    (polyBitTime_comp (f := sideBits) (g := pitchMap) (sideBits_polyBitTime hr) pitchMap_polyBitTime)

theorem unchanged_instance_bit_spec (hr : PolyBitTime (List.reverse : List Bool → List Bool)) :
    ∀ ns nt (M : Machine ns nt 2) p,
      PolyBitTime (instanceBits M p) ∧
      (∀ x,instanceBits M p x =
        Computability.encodeNat (PakFixedWeightedPhysicalSourceReadout.sourceSide M p x)) :=
  fun _ _ M p => ⟨instanceBits_polyBitTime hr M p,instanceBits_eq_encode M p⟩

end PakFixedPolyomino.PakLiteralSideBitTimeAssembly
