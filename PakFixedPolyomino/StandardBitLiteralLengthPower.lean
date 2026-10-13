import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitPolynomialBoundedPower
import PakFixedPolyomino.StandardBitFixedMultiply
import PakFixedPolyomino.StandardBitFixedAdd

/-! Fixed-base powers with a linear literal-length exponent. The constants
are fixed program data. The exponent is computed by actual length, fixed
multiply and fixed add machines; the initialized power loop's exponent,
iteration and tape-width bounds are instantiated internally. -/
namespace PakFixedPolyomino.StandardBitLiteralLengthPower
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)

def exponent (a b : Nat) (raw : List Bool) : Nat := a*raw.length+b
def powerBits (c a b : Nat) (raw : List Bool) : List Bool :=
  encodeNat (c^exponent a b raw)

theorem exponent_polyBitTime (a b : Nat) :
    PolyBitTime (fun raw => encodeNat (exponent a b raw)) := by
  have hmul := polyBitTime_comp StandardBitLiteralLength.length_polyBitTime
    (StandardBitFixedMultiply.fixed_multiply_polyBitTime a)
  have h := polyBitTime_comp hmul (StandardBitFixedAdd.fixed_add_polyBitTime b)
  simpa only [Function.comp_def,StandardBitLiteralLength.lengthBits,value_encode_nat,
    exponent] using h

theorem power_polyBitTime (c a b : Nat) : PolyBitTime (powerBits c a b) := by
  exact StandardBitPolynomialBoundedPower.power_polyBitTime c (exponent a b)
    (Polynomial.C a*Polynomial.X+Polynomial.C b) (exponent_polyBitTime a b)
    (by intro raw;simp [exponent])

theorem power_spec (c a b : Nat) : PolyBitTime (powerBits c a b) ∧
    (∀ raw,powerBits c a b raw=encodeNat (c^(a*raw.length+b))) ∧
    (∀ raw,(powerBits c a b raw).length≤c*(a*raw.length+b)+1) :=
  ⟨power_polyBitTime c a b,fun _ => rfl,
    fun raw => StandardBitBoundedPower.power_length c (a*raw.length+b)⟩

end
end PakFixedPolyomino.StandardBitLiteralLengthPower
