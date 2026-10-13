import PakFixedPolyomino.ULogSourceOneHotFullMacro
import Mathlib.Tactic

/-!
# Constant-time padding arithmetic for physical source macros

The currently checked source macro has a move-dependent relocation suffix.
This file records the exact deterministic padding required to equalize that
suffix.  It is arithmetic only: a later finite-control wrapper must still
realize these stay ticks before it may claim common physical time.
-/

namespace PakFixedPolyomino.ULogSourceOneHotPaddingArithmetic

open OneTapeTableau ULogSourceOneHotPhysicalStep

def paddingLength (move : Move) (nt : ℕ) : ℕ :=
  2 * nt - relocationDistance move nt

theorem relocation_add_padding (move : Move) (nt : ℕ) :
    relocationDistance move nt + paddingLength move nt = 2 * nt := by
  cases move <;> simp [paddingLength, relocationDistance] <;> omega

theorem padded_macro_length (move : Move) (nt : ℕ) :
    (3 * nt + relocationDistance move nt + 2) + paddingLength move nt =
      5 * nt + 2 := by
  cases move <;> simp [paddingLength, relocationDistance] <;> omega

@[simp] theorem paddingLength_right (nt : ℕ) :
    paddingLength .right nt = 2 * nt := by
  simp [paddingLength, relocationDistance]

@[simp] theorem paddingLength_stay (nt : ℕ) :
    paddingLength .stay nt = nt := by
  simp [paddingLength, relocationDistance]
  omega

@[simp] theorem paddingLength_left (nt : ℕ) :
    paddingLength .left nt = 0 := by
  simp [paddingLength, relocationDistance]

end PakFixedPolyomino.ULogSourceOneHotPaddingArithmetic
