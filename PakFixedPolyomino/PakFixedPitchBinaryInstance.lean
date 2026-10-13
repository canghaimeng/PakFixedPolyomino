import PakFixedPolyomino.StandardBitFixedMultiply

/-! Exact ordinary binary interface of the unchanged physical source side.
The one global pitch has real fixed-multiplication bit time. The remaining
side-word reversal/length-padding tape implementation is a separate obligation.
No bit-time certificate for that whole source map is asserted here. -/
namespace PakFixedPolyomino.PakFixedPitchBinaryInstance
open Computability StandardBitTime StandardBinaryWordNormalization
open PakFixedWeightedStandardBinaryCount (value)
open PakFixedWeightedRegisterInventory (params)
open StandardNondeterministicMachine (Machine)

def sideBits (x : List Bool) : List Bool := (ConcretePakSide.encodedWord x).reverse

theorem value_eq_ofDigits (x : List Bool) : value x = Nat.ofDigits 2 (x.map Bool.toNat) := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [value,List.map_cons,Nat.ofDigits_cons,ih]

theorem sideBits_value (x : List Bool) : value (sideBits x) = ConcretePakSide.sideValue x :=
  value_eq_ofDigits _

theorem normalize_append_true (x : List Bool) : normalizeBits (x++[true]) = x++[true] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [List.cons_append,normalizeBits,ih]

theorem normalize_sideBits (x : List Bool) : normalizeBits (sideBits x) = sideBits x := by
  unfold sideBits ConcretePakSide.encodedWord
  simp only [List.cons_append,List.reverse_cons]
  exact normalize_append_true _

theorem sideBits_eq_encode (x : List Bool) : sideBits x = encodeNat (ConcretePakSide.sideValue x) := by
  have h := normalize_eq_encodeNat (sideBits x)
  rw [normalize_sideBits,sideBits_value] at h
  exact h

theorem sideBits_length (x : List Bool) : (sideBits x).length = 74*x.length+75 := by
  simp [sideBits]

noncomputable def pitchMap (bits : List Bool) : List Bool := encodeNat (params.pitch*value bits)

theorem pitchMap_polyBitTime : PolyBitTime pitchMap :=
  StandardBitFixedMultiply.fixed_multiply_polyBitTime params.pitch

noncomputable def instanceBits {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : List Bool :=
  pitchMap (sideBits (ULogTernaryGeneratedMarginScanner.input M p x))

theorem instanceBits_eq_encode {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : instanceBits M p x =
      encodeNat (PakFixedWeightedPhysicalSourceReadout.sourceSide M p x) := by
  simp only [instanceBits,pitchMap,sideBits_value,PakFixedWeightedPhysicalSourceReadout.sourceSide]

theorem fixed_pitch_binary_instance_spec :
    (∀ x,sideBits x = encodeNat (ConcretePakSide.sideValue x)) ∧
    (∀ x,(sideBits x).length = 74*x.length+75) ∧
    PolyBitTime pitchMap ∧
    (∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) x,
      instanceBits M p x = encodeNat (PakFixedWeightedPhysicalSourceReadout.sourceSide M p x)) :=
  ⟨sideBits_eq_encode,sideBits_length,pitchMap_polyBitTime,fun _ _ M p x=>instanceBits_eq_encode M p x⟩

end PakFixedPolyomino.PakFixedPitchBinaryInstance
