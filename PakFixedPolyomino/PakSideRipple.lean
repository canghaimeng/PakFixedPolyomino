import PakFixedPolyomino.PakCanonicalFullTrack
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# The arbitrary-input ripple boundary word

This module records the exact bridge from `sideValue x` to the east colours
of the canonical ripple tiling.  It is the numeric half of the arbitrary
scanner construction: the same little-endian word is used by
`MStarParserExecution.inputCells`.
-/

namespace PakFixedPolyomino.PakSideRipple

open ConcretePakSide

/-- The Boolean interpretation of one (zero-padded) binary digit. -/
def sideDigit (x : Word) (j : ℕ) : Bool :=
  decide ((littleDigits x).getD j 0 = 1)

theorem sideValue_testBit (x : Word) (j : ℕ) :
    (sideValue x).testBit j = sideDigit x j := by
  unfold sideDigit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  rw [← Nat.getD_digits (sideValue x) j (by omega), digits_sideValue]

/-- On the right edge of the `sideValue x` ripple grid, the Wang east colour
is exactly the padded little-endian digit used by the parser input. -/
theorem canonicalRipple_east_sideDigit (x : Word) (hn : 0 < sideValue x)
    (j : Fin (sideValue x)) :
    (rippleTile
      ((PakRippleCanonical.canonicalTiling (sideValue x) (sideValue x)).1
        ⟨sideValue x - 1, by omega⟩ j)).east = sideDigit x j.1 := by
  rw [PakRippleCanonical.canonicalTiling_east (sideValue x) (sideValue x) hn j]
  exact sideValue_testBit x j.1

/-- The parser's concrete source row is the same encoded word in little
endian order, followed by its literal work delimiter. -/
theorem parserInputCells_sideWord (x : Word) :
    MStarParserExecution.inputCells MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work (encodedWord x) =
      List.replicate (paddingLength x.length)
          (.core MStarConcreteAlphabet.zero) ++
        [.core MStarConcreteAlphabet.one] ++
        List.replicate x.length (.core MStarConcreteAlphabet.zero) ++
        [.core MStarConcreteAlphabet.one] ++
        x.reverse.map
          (MStarParserExecution.bitCell MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one) ++
        [.core MStarConcreteAlphabet.one, .core MStarConcreteAlphabet.work] :=
  MStarParserExecution.inputCells_encodedWord
    MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
    MStarConcreteAlphabet.work x

end PakFixedPolyomino.PakSideRipple
