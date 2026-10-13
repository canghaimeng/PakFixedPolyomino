import PakFixedPolyomino.PakLiteralSideBitTimeClosed
import PakFixedPolyomino.PakFixedWeightedOracleLengthGuard

/-! The original macro side has an actual bit-time implementation before
the raw-answer guard. This does not implement the paired guard itself. -/
namespace PakFixedPolyomino.PakMacroSideBitTimeClosed
open StandardBitTime StandardBitTimeComposition PakFixedPitchBinaryInstance
open StandardNondeterministicMachine (Machine)

noncomputable def macroBits {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : List Bool := sideBits (ULogTernaryGeneratedMarginScanner.input M p x)

theorem macroBits_eq_encode {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : macroBits M p x =
      Computability.encodeNat (PakFixedWeightedOracleLengthGuard.macroSide M p x) :=
  sideBits_eq_encode _

attribute [local irreducible] ULogTernaryGeneratedMarginScanner.input
  PakFixedPitchBinaryInstance.sideBits

theorem macroBits_eq_composition {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    macroBits M p = sideBits ∘ ULogTernaryGeneratedMarginScanner.input M p := rfl

theorem macroBits_polyBitTime {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (macroBits M p) := by
  rw [macroBits_eq_composition]
  exact polyBitTime_comp (ULogTernaryGeneratedMarginScanner.input_polyBitTime M p)
    (PakLiteralSideBitTimeAssembly.sideBits_polyBitTime StandardBitReverseClosed.reverse_polyBitTime)

theorem unchanged_macro_side_bit_spec :
    ∀ ns nt (M : Machine ns nt 2) (p : Polynomial Nat),
      PolyBitTime (macroBits M p) ∧
      (∀ x,macroBits M p x =
        Computability.encodeNat (PakFixedWeightedOracleLengthGuard.macroSide M p x)) :=
  fun _ _ M p => ⟨macroBits_polyBitTime M p,macroBits_eq_encode M p⟩

end PakFixedPolyomino.PakMacroSideBitTimeClosed
