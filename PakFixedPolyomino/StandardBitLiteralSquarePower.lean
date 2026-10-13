import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitPolynomialBoundedPower
import PakFixedPolyomino.StandardBitVariableMultiplyLoop
import PakFixedPolyomino.StandardBitVariableAddClosed

/-! Fixed-base power with squared literal-length exponent on every word.
The exponent uses the actual physical length and variable multiply machines;
the latter's adder premise is supplied by the closed actual64/32 runtime.
No exponent compiler, iteration, width or runtime premise remains. -/
namespace PakFixedPolyomino.StandardBitLiteralSquarePower
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value_encode_nat)

def exponent (raw : List Bool) : Nat := raw.length*raw.length
def powerBits (c : Nat) (raw : List Bool) : List Bool := encodeNat (c^exponent raw)

theorem exponent_polyBitTime : PolyBitTime (fun raw => encodeNat (exponent raw)) := by
  have hp := StandardBitPairMaps.parallel_polyBitTime
    StandardBitLiteralLength.lengthBits StandardBitLiteralLength.lengthBits
    StandardBitLiteralLength.length_polyBitTime StandardBitLiteralLength.length_polyBitTime
  have h := polyBitTime_comp hp (StandardBitVariableMultiplyLoop.multiply_polyBitTime
    StandardBitVariableAddClosed.add_polyBitTime)
  have he : StandardBitVariableMultiplyLoop.multiplyBits ∘
      StandardBitPairMaps.parallel StandardBitLiteralLength.lengthBits StandardBitLiteralLength.lengthBits=
      (fun raw => encodeNat (exponent raw)) := by
    funext raw
    rw [Function.comp_apply,StandardBitPairMaps.parallel_pair,
      StandardBitVariableMultiplyLoop.multiply_pair]
    simp only [StandardBitLiteralLength.lengthBits,value_encode_nat,exponent]
  rwa [he] at h

theorem power_polyBitTime (c : Nat) : PolyBitTime (powerBits c) :=
  StandardBitPolynomialBoundedPower.power_polyBitTime c exponent (Polynomial.X*Polynomial.X)
    exponent_polyBitTime (by intro raw;simp [exponent])

theorem power_spec (c : Nat) : PolyBitTime (powerBits c) ∧
    (∀ raw,powerBits c raw=encodeNat (c^(raw.length^2))) ∧
    (∀ raw,(powerBits c raw).length≤c*(raw.length^2)+1) := by
  refine ⟨power_polyBitTime c,?_,?_⟩
  · intro raw;simp only [powerBits,exponent,pow_two]
  · intro raw;simpa only [powerBits,exponent,pow_two] using
      StandardBitBoundedPower.power_length c (raw.length*raw.length)

end
end PakFixedPolyomino.StandardBitLiteralSquarePower
