import PakFixedPolyomino.WangRectangleBoundConcrete
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Canonical ripple grid

The ripple track is the binary increment tableau.  At horizontal coordinate
`i`, row `j` stores bit `j` of `i`; the second component records that the
increment from `i` to `i + 1` carries through all lower positions.
-/

namespace PakFixedPolyomino.PakRippleCanonical

/-- The value carried horizontally by the canonical ripple cell. -/
def rippleBit (i j : ℕ) : Bool := i.testBit j

/-- The carry into bit `j` when incrementing `i`. -/
def rippleCarry (i j : ℕ) : Bool :=
  decide (i % 2 ^ j = 2 ^ j - 1)

private theorem even_carry_false (q p : ℕ) (hp : 0 < p) :
    decide ((2 * q) % (p * 2) = p * 2 - 1) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have heq : (2 * q) % (p * 2) = p * 2 - 1 :=
    decide_eq_true_eq.mp h
  have hdvd : 2 ∣ p * 2 := ⟨p, by omega⟩
  have hmod := congrArg (fun z : ℕ => z % 2) heq
  rw [Nat.mod_mod_of_dvd (2 * q) hdvd] at hmod
  have hleft : (2 * q) % 2 = 0 := by omega
  have hright : (p * 2 - 1) % 2 = 1 := by omega
  omega

private theorem odd_carry_iff (q p : ℕ) (hp : 0 < p) :
    (2 * q + 1) % (p * 2) = p * 2 - 1 ↔ q % p = p - 1 := by
  have hdecomp : q % p + p * (q / p) = q := Nat.mod_add_div q p
  rw [← hdecomp]
  have hsmall : 2 * (q % p) + 1 < p * 2 := by
    have hrem : q % p < p := Nat.mod_lt _ hp
    omega
  rw [show 2 * (q % p + p * (q / p)) + 1 =
      (2 * (q % p) + 1) + (p * 2) * (q / p) by ring]
  have hleft :
      ((2 * (q % p) + 1) + (p * 2) * (q / p)) % (p * 2) =
        2 * (q % p) + 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
  have hright : (q % p + p * (q / p)) % p = q % p := by
    rw [show p * (q / p) = (q / p) * p by ring]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hp)]
  rw [hleft, hright]
  omega

/-- The binary successor law in the form used by the horizontal ripple Wang
colour: incrementing toggles a bit exactly when the lower carry reaches it. -/
theorem rippleBit_succ_xor_carry (i j : ℕ) :
    rippleBit (i + 1) j = xor (rippleBit i j) (rippleCarry i j) := by
  induction j generalizing i with
  | zero =>
      unfold rippleBit rippleCarry
      simp only [pow_zero, Nat.mod_one, Nat.reduceSub, decide_eq_true_eq]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow, h, Nat.add_mod] <;> omega
  | succ j ih =>
      unfold rippleBit rippleCarry at ih ⊢
      cases hparity : i % 2 with
      | zero =>
          have hi : i = 2 * (i / 2) := by
            omega
          rw [hi]
          simp [Nat.testBit_add_one, Nat.shiftRight_eq_div_pow,
            Nat.mul_add_div, pow_succ, ih]
          rw [even_carry_false (i / 2) (2 ^ j) (pow_pos (by decide) _)]
          simp
      | succ h =>
          have hparity' : i % 2 = 1 := by omega
          have hi : i = 2 * (i / 2) + 1 := by
            omega
          rw [hi]
          simp [Nat.testBit_add_one, Nat.shiftRight_eq_div_pow,
            Nat.mul_add_div, pow_succ, ih]
          rw [show decide ((2 * (i / 2) + 1) % (2 ^ j * 2) =
              2 ^ j * 2 - 1) =
              decide ((i / 2) % 2 ^ j = 2 ^ j - 1) by
            exact decide_eq_decide.mpr
              (odd_carry_iff (i / 2) (2 ^ j) (pow_pos (by decide) _))]
          have hdiv : (2 * (i / 2) + 1 + 1) / 2 = i / 2 + 1 := by omega
          rw [hdiv]
          exact ih (i / 2)

/-- Carrying through one more binary position means that the present bit and
all lower carry bits are set. -/
theorem rippleCarry_succ (i j : ℕ) :
    rippleCarry i (j + 1) = (rippleBit i j && rippleCarry i j) := by
  unfold rippleCarry rippleBit
  apply Bool.eq_iff_iff.mpr
  rw [pow_succ]
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_eq]
  let p := 2 ^ j
  let q := i / p
  let r := i % p
  change i % (p * 2) = p * 2 - 1 ↔
    (i.testBit j = true ∧ i % p = p - 1)
  have hp : 0 < p := by
    dsimp [p]
    exact pow_pos (by decide) _
  have hr : r < p := by
    dsimp [r]
    exact Nat.mod_lt _ hp
  have hdecomp : r + 2 ^ j * q = i := by
    change i % p + p * (i / p) = i
    exact Nat.mod_add_div i (2 ^ j)
  change r + p * q = i at hdecomp
  rw [← hdecomp]
  have hlow : (r + p * q) % p = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hdiv : (r + p * q) / p = q := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hhigh : (r + p * q) % (p * 2) = r + p * (q % 2) := by
    have hq : q % 2 < 2 := Nat.mod_lt _ (by omega)
    have hsmall : r + p * (q % 2) < p * 2 := by
      by_cases hz : q % 2 = 0
      · simp [hz]
        omega
      · have ho : q % 2 = 1 := by omega
        simp [ho]
        omega
    calc
      (r + p * q) % (p * 2) =
          (r + p * (q % 2 + 2 * (q / 2))) % (p * 2) := by
            rw [Nat.mod_add_div q 2]
      _ = ((r + p * (q % 2)) + (p * 2) * (q / 2)) % (p * 2) := by
            congr 1
            ring
      _ = (r + p * (q % 2)) % (p * 2) := by
            rw [Nat.add_mul_mod_self_left]
      _ = r + p * (q % 2) := Nat.mod_eq_of_lt hsmall
  have hbit : (r + p * q).testBit j = true ↔ q % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change decide ((r + p * q) / p % 2 = 1) = true ↔ q % 2 = 1
    rw [hdiv]
    simp
  rw [hhigh, hlow, hbit]
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · have hne : r ≠ p * 2 - 1 := by
      intro h
      omega
    simp [hq, hne]
  · simp [hq]
    omega

/-- The canonical ripple tile at binary counter position `(i,j)`. -/
def canonicalCell (i j : ℕ) : RippleTile :=
  (rippleBit i j, rippleCarry i j)

theorem canonicalCell_east (i j : ℕ) :
    (rippleTile (canonicalCell i j)).east = (rippleTile (canonicalCell (i + 1) j)).west := by
  simp [canonicalCell, rippleTile, rippleBit_succ_xor_carry]

theorem canonicalCell_north (i j : ℕ) :
    (rippleTile (canonicalCell i j)).north =
      (rippleTile (canonicalCell i (j + 1))).south := by
  simpa [canonicalCell, rippleTile] using (rippleCarry_succ i j).symm

/-- The finite canonical binary-counter ripple tableau. -/
def canonicalTiling (w h : ℕ) : OpenWangTiling rippleTile w h := by
  refine ⟨fun i j => canonicalCell i.1 j.1, ?_⟩
  constructor
  · intro i j hi
    simpa using canonicalCell_east i.1 j.1
  · intro i j hj
    simpa using canonicalCell_north i.1 j.1

theorem canonicalTiling_west (w h : ℕ) (j : Fin h) (hw : 0 < w) :
    ((canonicalTiling w h).1 ⟨0, hw⟩ j).1 = false := by
  change rippleBit 0 j.1 = false
  simp [rippleBit, Nat.testBit]

theorem canonicalTiling_south (w h : ℕ) (i : Fin w) (hh : 0 < h) :
    ((canonicalTiling w h).1 i ⟨0, hh⟩).2 = true := by
  change rippleCarry i.1 0 = true
  change decide (i.1 % 1 = 0) = true
  simp only [Nat.mod_one, decide_true]

theorem canonicalTiling_east (w h : ℕ) (hw : 0 < w) (j : Fin h) :
    (rippleTile ((canonicalTiling w h).1 ⟨w - 1, by omega⟩ j)).east =
      w.testBit j.1 := by
  have hstep := rippleBit_succ_xor_carry (w - 1) j.1
  have hlast : w - 1 + 1 = w := by omega
  rw [hlast] at hstep
  simpa [canonicalTiling, canonicalCell, rippleTile, rippleBit] using hstep.symm

/-! ## The full-activity amplifier track -/

/-- The unique zero-coloured amplifier cell whose four activity bits are
exactly its four geometric boundary predicates.  Thus no boundary word or
existential amplifier filler is hidden in the construction. -/
def canonicalFullAmpCell (Q w h : ℕ) [NeZero Q]
    (i : Fin w) (j : Fin h) : SharedQAmpTile Q :=
  ⟨{ westActive := decide (i.1 = 0)
     eastActive := decide (i.1 + 1 = w)
     southActive := decide (j.1 = 0)
     northActive := decide (j.1 + 1 = h)
     qWest := ⟨0, NeZero.pos Q⟩
     qEast := ⟨0, NeZero.pos Q⟩
     qSouth := ⟨0, NeZero.pos Q⟩
     qNorth := ⟨0, NeZero.pos Q⟩ }, by
    refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

/-- A literal full-active tiling of the shared-`Q` amplifier, for every
rectangle.  All internal activity bits are false, and the four exterior
chains are carried by the matching colours. -/
def canonicalFullAmpTiling (Q w h : ℕ) [NeZero Q] :
    OpenWangTiling (sharedQAmpWangTile Q) w h := by
  refine ⟨fun i j => canonicalFullAmpCell Q w h i j, ?_⟩
  constructor
  · intro i j hi
    have hne : i.1 + 1 ≠ w := by omega
    apply AmpHorizontalColour.ext <;>
      simp [canonicalFullAmpCell, sharedQAmpWangTile, hne]
  · intro i j hj
    have hne : j.1 + 1 ≠ h := by omega
    apply AmpVerticalColour.ext <;>
      simp [canonicalFullAmpCell, sharedQAmpWangTile, hne]

theorem canonicalFullAmp_west (Q w h : ℕ) [NeZero Q]
    (hw : 0 < w) (j : Fin h) :
    ((canonicalFullAmpTiling Q w h).1 ⟨0, hw⟩ j).1.westActive = true := by
  simp [canonicalFullAmpTiling, canonicalFullAmpCell]

theorem canonicalFullAmp_east (Q w h : ℕ) [NeZero Q]
    (hw : 0 < w) (j : Fin h) :
    ((canonicalFullAmpTiling Q w h).1 ⟨w - 1, by omega⟩ j).1.eastActive = true := by
  have hlast : w - 1 + 1 = w := by omega
  simp [canonicalFullAmpTiling, canonicalFullAmpCell, hlast]

theorem canonicalFullAmp_south (Q w h : ℕ) [NeZero Q]
    (i : Fin w) (hh : 0 < h) :
    ((canonicalFullAmpTiling Q w h).1 i ⟨0, hh⟩).1.southActive = true := by
  simp [canonicalFullAmpTiling, canonicalFullAmpCell]

theorem canonicalFullAmp_north (Q w h : ℕ) [NeZero Q]
    (i : Fin w) (hh : 0 < h) :
    ((canonicalFullAmpTiling Q w h).1 i ⟨h - 1, by omega⟩).1.northActive = true := by
  have hlast : h - 1 + 1 = h := by omega
  simp [canonicalFullAmpTiling, canonicalFullAmpCell, hlast]

end PakFixedPolyomino.PakRippleCanonical
