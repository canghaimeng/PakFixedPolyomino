import PakFixedPolyomino.PakRippleCanonical
import PakFixedPolyomino.PakMStarCouplingCorrectness
import Mathlib.Tactic

/-!
# A literal canonical east scanner

This is the small, completely explicit scanner used at the right boundary of
the first nontrivial full frame.  Its three cells read the initial word
`hash, hash, head-zero, hash, hash`; the ripple counter of horizontal length
four supplies the required scanner bits `0, 0, 1`.
-/

namespace PakFixedPolyomino.PakCanonicalScanner

open ConcretePakScanner
open PakMStarCouplingCorrectness

namespace Fixed

abbrev State := PakMStarCouplingCorrectness.Fixed.State
abbrev Tape := PakMStarCouplingCorrectness.Fixed.Tape
abbrev Arrow := PakMStarCouplingCorrectness.Fixed.Arrow

end Fixed

/-- A reusable extension lemma: a vertically matching marked column, placed
only at the east edge, is a genuine scanner Wang tiling. -/
def eastColumnCell {S : Type*} {w h : ℕ} (column : Fin h → ScannerTile S)
    (i : Fin w) (j : Fin h) : ScannerTile S :=
  if i.1 + 1 = w then column j else none

@[simp] theorem scannerTile_west_false {S : Type*} (u : ScannerTile S) :
    (scannerTile u).west = false := by
  cases u <;> rfl

def eastColumnTiling {S : Type*} [Fintype S] {w h : ℕ} (hw : 0 < w)
    (column : Fin h → ScannerTile S)
    (hvertical : ∀ (j : Fin h) (hj : j.1 + 1 < h),
      (scannerTile (column j)).north =
        (scannerTile (column ⟨j.1 + 1, hj⟩)).south) :
    OpenWangTiling (scannerTile (S := S)) w h := by
  refine ⟨fun i j => eastColumnCell column i j, ?_⟩
  constructor
  · intro i j hi
    have hne : i.1 + 1 ≠ w := by omega
    have hcell : eastColumnCell column i j = none := by
      simp [eastColumnCell, hne]
    change (scannerTile (eastColumnCell column i j)).east =
      (scannerTile (eastColumnCell column ⟨i.1 + 1, hi⟩ j)).west
    rw [hcell]
    change false =
      (scannerTile (eastColumnCell column ⟨i.1 + 1, hi⟩ j)).west
    exact (scannerTile_west_false _).symm
  · intro i j hj
    by_cases he : i.1 + 1 = w
    · simpa only [eastColumnCell, if_pos he] using hvertical j hj
    · have hleft : eastColumnCell column i j = none := by
        simp [eastColumnCell, he]
      have hright : eastColumnCell column i ⟨j.1 + 1, hj⟩ = none := by
        simp [eastColumnCell, he]
      change (scannerTile (eastColumnCell column i j)).north =
        (scannerTile (eastColumnCell column i ⟨j.1 + 1, hj⟩)).south
      rw [hleft, hright]
      rfl

/-- Bottom scanner state for the fixed three-cell initial row. -/
def bottomState : State :=
  PakCouplingGenerated.scannerBottom

/-- The sole ordinary scanner state: it stores the marked initial zero and
remains in high mode so that `preTop` is the next legal clause. -/
def middleState : State :=
  { phase := .mid
    left := .hash
    centre := .headZero
    lookahead := .lh0
    mode := .high }

/-- The terminal scanner state immediately below the cap. -/
def topState : State :=
  { phase := .top
    left := .headZero
    centre := .hash
    lookahead := .lh1
    mode := .high }

def capState : State := ConcretePakScanner.topNorth

theorem bottom_middle_legal : LegalScan bottomState middleState false := by
  refine ⟨.bot, ?_⟩
  native_decide

theorem middle_top_legal : LegalScan middleState topState false := by
  refine ⟨.preTop, ?_⟩
  native_decide

theorem top_cap_legal : LegalScan topState capState true := by
  refine ⟨.top, ?_⟩
  native_decide

/-- The fixed vertical scanner path.  The final `top` edge reads no bit, so
the last ripple bit may be one. -/
def canonicalColumn (j : Fin 3) : ScannerTile State :=
  if j.1 = 0 then some (bottomState, middleState)
  else if j.1 = 1 then some (middleState, topState)
  else some (topState, capState)

theorem canonicalColumn_vertical (j : Fin 3) (hj : j.1 + 1 < 3) :
    (scannerTile (canonicalColumn j)).north =
      (scannerTile (canonicalColumn ⟨j.1 + 1, hj⟩)).south := by
  have hcases : j.1 = 0 ∨ j.1 = 1 := by omega
  rcases hcases with h0 | h1
  · have hj0 : j = ⟨0, by decide⟩ := Fin.ext h0
    subst j
    change some middleState = some middleState
    rfl
  · have hj1 : j = ⟨1, by decide⟩ := Fin.ext h1
    subst j
    change some topState = some topState
    rfl

/-- The actual east-diode scanner tiling on the `4 × 3` canonical frame. -/
def canonicalTiling : OpenWangTiling (scannerTile (S := State)) 4 3 :=
  eastColumnTiling (S := State) (w := 4) (h := 3) (by decide)
    canonicalColumn canonicalColumn_vertical

theorem canonicalTiling_east (j : Fin 3) :
    canonicalTiling.1 (⟨3, by decide⟩ : Fin 4) j = canonicalColumn j := by
  change eastColumnCell canonicalColumn (⟨3, by decide⟩ : Fin 4) j =
    canonicalColumn j
  simp [eastColumnCell]

theorem canonicalTiling_interior (i : Fin 4) (j : Fin 3)
    (hi : i.1 + 1 < 4) : canonicalTiling.1 i j = none := by
  have hne : i.1 + 1 ≠ 4 := by omega
  change eastColumnCell canonicalColumn i j = none
  simp [eastColumnCell, hne]

/-- Every marked scanner edge is legal for the literal ripple east colour of
the width-four canonical counter. -/
theorem canonicalColumn_legal_ripple (j : Fin 3) :
    ∃ s t : State,
      canonicalColumn j = some (s, t) ∧
        LegalScan s t
          ((rippleTile
            ((PakRippleCanonical.canonicalTiling 4 3).1 ⟨3, by decide⟩ j)).east) := by
  rw [PakRippleCanonical.canonicalTiling_east 4 3 (by decide) j]
  have hb0 : Nat.testBit 4 0 = false := by native_decide
  have hb1 : Nat.testBit 4 1 = false := by native_decide
  have hb2 : Nat.testBit 4 2 = true := by native_decide
  fin_cases j
  · exact ⟨bottomState, middleState, by simp [canonicalColumn], by
      simpa [hb0] using bottom_middle_legal⟩
  · exact ⟨middleState, topState, by simp [canonicalColumn], by
      simpa [hb1] using middle_top_legal⟩
  · exact ⟨topState, capState, by simp [canonicalColumn], by
      simpa [hb2] using top_cap_legal⟩

/-- The literal `M_star` initial tape scanned by the three-edge path. -/
def encodedInitialTape (z : Int) : Fixed.Tape :=
  if z = 1 then .core MStarConcreteAlphabet.zero else .hash

def encodedInitialConfig : MStarConfig :=
  { state := .start
    head := 1
    tape := encodedInitialTape }

def encodedInitialCell (z : Int) : TableauCell Fixed.State Fixed.Tape :=
  if z = encodedInitialConfig.head then
    .head encodedInitialConfig.state (encodedInitialConfig.tape z)
  else .plain (encodedInitialConfig.tape z)

def encodedInitialWindow (j : Fin 3) :
    CellTriple (TableauCell Fixed.State Fixed.Tape) :=
  { minus := encodedInitialCell (j.1 - 1)
    center := encodedInitialCell j.1
    plus := encodedInitialCell (j.1 + 1) }

/-- The scanner's three emitted windows are exactly the overlapping windows
of the concrete encoded start configuration. -/
theorem canonicalColumn_emits_initial (j : Fin 3) :
    ∃ s t : State,
      canonicalColumn j = some (s, t) ∧
        PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t =
          encodedInitialWindow j := by
  fin_cases j
  · refine ⟨bottomState, middleState, by simp [canonicalColumn], ?_⟩
    simp [bottomState, middleState, PakCouplingGenerated.emittedWindow,
      PakCouplingGenerated.bufferCell, encodedInitialWindow, encodedInitialCell,
      encodedInitialConfig, encodedInitialTape, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach, PakCouplingGenerated.scannerBottom]
  · refine ⟨middleState, topState, by simp [canonicalColumn], ?_⟩
    simp [middleState, topState, PakCouplingGenerated.emittedWindow,
      PakCouplingGenerated.bufferCell, encodedInitialWindow, encodedInitialCell,
      encodedInitialConfig, encodedInitialTape, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach]
  · refine ⟨topState, capState, by simp [canonicalColumn], ?_⟩
    simp [topState, capState, PakCouplingGenerated.emittedWindow,
      PakCouplingGenerated.bufferCell, encodedInitialWindow, encodedInitialCell,
      encodedInitialConfig, encodedInitialTape, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach, ConcretePakScanner.topNorth]

end PakFixedPolyomino.PakCanonicalScanner
