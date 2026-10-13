import PakFixedPolyomino.ULogClocked
import Mathlib.Tactic

/-!
# Physical core-tape layout for `U_log`

This module fixes the literal encoding of semantic bytecode configurations in
the fifty-letter interpreter block.  The finite microcode refinement can now
target one immutable list format rather than changing delimiters while its
transition table is developed.
-/

namespace PakFixedPolyomino.ULogTapeLayout

open ULogAlphabet ULogBytecode

abbrev CoreTape := MStarConcreteAlphabet.CoreTape

def codeBit : Bool → CoreTape
  | false => ulogCore ULogAlphabet.codeZero
  | true => ulogCore ULogAlphabet.codeOne

def encodeCodeBits (bits : List Bool) : List CoreTape := bits.map codeBit

def encodeUnary (zero endMark : CoreTape) (n : ℕ) : List CoreTape :=
  List.replicate n zero ++ [endMark]

def encodeNatList (xs : List ℕ) : List CoreTape :=
  xs.flatMap (encodeUnary (ulogCore dataZero) (ulogCore dataSep)) ++
    [ulogCore dataEnd]

def encodeBase (c : ULogSemantics.Config) : List CoreTape :=
  [ulogCore pcMark] ++
    encodeCodeBits (encodeProgram c.program) ++
    [ulogCore codeEnd] ++
    encodeUnary (ulogCore stateZero) (ulogCore stateOne) c.state ++
    [ulogCore stateSep] ++
    encodeNatList c.leftRev ++
    [ulogCore headLeft] ++
    encodeUnary (ulogCore dataZero) (ulogCore dataSep) c.focus ++
    [ulogCore headHere] ++
    encodeNatList c.right ++
    [ulogCore headRight, ulogCore returnMark]

def encodeClocked (c : ULogClocked.Config) : List CoreTape :=
  encodeBase c.base ++
    encodeUnary (ulogCore clockZero) (ulogCore clockOne) c.remaining ++
    [ulogCore clockSep]

@[simp] theorem length_encodeCodeBits (bits : List Bool) :
    (encodeCodeBits bits).length = bits.length := by
  simp [encodeCodeBits]

@[simp] theorem length_encodeUnary (zero endMark : CoreTape) (n : ℕ) :
    (encodeUnary zero endMark n).length = n + 1 := by
  simp [encodeUnary]

@[simp] theorem length_encodeNatList (xs : List ℕ) :
    (encodeNatList xs).length = xs.sum + xs.length + 1 := by
  induction xs with
  | nil => simp [encodeNatList]
  | cons x xs ih =>
      simp [encodeNatList, ih]
      omega

@[simp] theorem length_encodeBase (c : ULogSemantics.Config) :
    (encodeBase c).length =
      (encodeProgram c.program).length + c.state +
        c.leftRev.sum + c.leftRev.length + c.focus +
          c.right.sum + c.right.length + 11 := by
  simp [encodeBase]
  ring

@[simp] theorem length_encodeClocked (c : ULogClocked.Config) :
    (encodeClocked c).length =
      (encodeProgram c.base.program).length + c.base.state +
        c.base.leftRev.sum + c.base.leftRev.length + c.base.focus +
          c.base.right.sum + c.base.right.length + c.remaining + 13 := by
  simp [encodeClocked]
  ring

theorem codeBit_injective : Function.Injective codeBit := by
  intro a b h
  cases a <;> cases b
  · rfl
  · have hh : ULogAlphabet.codeZero = ULogAlphabet.codeOne :=
      ulogCore_injective (by simpa [codeBit] using h)
    exact ((by native_decide :
      ULogAlphabet.codeZero ≠ ULogAlphabet.codeOne) hh).elim
  · have hh : ULogAlphabet.codeOne = ULogAlphabet.codeZero :=
      ulogCore_injective (by simpa [codeBit] using h)
    exact ((by native_decide :
      ULogAlphabet.codeOne ≠ ULogAlphabet.codeZero) hh).elim
  · rfl

theorem encodeCodeBits_injective : Function.Injective encodeCodeBits := by
  exact codeBit_injective.list_map

@[simp] theorem encodeClocked_ne_nil (c : ULogClocked.Config) :
    encodeClocked c ≠ [] := by
  simp [encodeClocked, encodeBase]

end PakFixedPolyomino.ULogTapeLayout
