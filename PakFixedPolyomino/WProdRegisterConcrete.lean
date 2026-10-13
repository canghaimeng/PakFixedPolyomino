import PakFixedPolyomino.HigherBlockTableauConcrete
import Mathlib.Tactic

/-!
# Concrete `W_prod` and its enumerated register

The product construction is independent of names chosen for finite tile and
colour alphabets.  This file proves that enumeration into `Fin` preserves open
rectangle counts, constructs the `RegisterParams` consumed by the geometric
compiler, and exports its `WangRectangleBound`.
-/

namespace PakFixedPolyomino

noncomputable section

def relabelWangTile {W H V W' H' V' : Type*}
    (eW : W ≃ W') (eH : H ≃ H') (eV : V ≃ V')
    (tile : W → WangTile H V) : W' → WangTile H' V' := fun u =>
  { west := eH (tile (eW.symm u)).west
    east := eH (tile (eW.symm u)).east
    south := eV (tile (eW.symm u)).south
    north := eV (tile (eW.symm u)).north }

def openWangRelabelEquiv {W H V W' H' V' : Type*}
    [Fintype W] [Fintype W']
    (eW : W ≃ W') (eH : H ≃ H') (eV : V ≃ V')
    (tile : W → WangTile H V) (w h : ℕ) :
    OpenWangTiling tile w h ≃
      OpenWangTiling (relabelWangTile eW eH eV tile) w h where
  toFun f := by
    refine ⟨fun i j => eW (f.1 i j), ?_⟩
    constructor
    · intro i j hi
      simpa [relabelWangTile] using congrArg eH (f.2.1 i j hi)
    · intro i j hj
      simpa [relabelWangTile] using congrArg eV (f.2.2 i j hj)
  invFun f := by
    refine ⟨fun i j => eW.symm (f.1 i j), ?_⟩
    constructor
    · intro i j hi
      exact eH.injective (f.2.1 i j hi)
    · intro i j hj
      exact eV.injective (f.2.2 i j hj)
  left_inv f := by
    apply Subtype.ext
    funext i j
    simp
  right_inv f := by
    apply Subtype.ext
    funext i j
    simp

theorem openWangCount_relabel {W H V W' H' V' : Type*}
    [Fintype W] [Fintype W']
    [DecidableEq H] [DecidableEq V] [DecidableEq H'] [DecidableEq V']
    (eW : W ≃ W') (eH : H ≃ H') (eV : V ≃ V')
    (tile : W → WangTile H V) (w h : ℕ) :
    openWangCount (relabelWangTile eW eH eV tile) w h =
      openWangCount tile w h := by
  unfold openWangCount
  exact (Fintype.card_congr (openWangRelabelEquiv eW eH eV tile w h)).symm

def WangRectangleBound.relabel {W H V W' H' V' : Type*}
    [Fintype W] [Fintype W']
    [DecidableEq H] [DecidableEq V] [DecidableEq H'] [DecidableEq V']
    (eW : W ≃ W') (eH : H ≃ H') (eV : V ≃ V')
    (tile : W → WangTile H V) {R : ℕ} (C : WangRectangleBound R tile) :
    WangRectangleBound R (relabelWangTile eW eH eV tile) where
  bound w h := by rw [openWangCount_relabel]; exact C.bound w h

/-- Enumerate one finite Wang system into exactly the `Fin` tables expected by
the identity-register compiler. -/
def registerParamsOfWang {W H V : Type*}
    [Fintype W] [Fintype H] [Fintype V]
    [Nonempty W] [Nonempty H] [Nonempty V]
    (tile : W → WangTile H V) (R : ℕ) (hR : 2 ≤ R) : RegisterParams where
  tileCount := Fintype.card W
  horizontalColours := Fintype.card H
  verticalColours := Fintype.card V
  perimeterBase := R
  tileCount_pos := Fintype.card_pos
  horizontalColours_pos := Fintype.card_pos
  verticalColours_pos := Fintype.card_pos
  perimeterBase_ge_two := hR
  west i := Fintype.equivFin H (tile ((Fintype.equivFin W).symm i)).west
  east i := Fintype.equivFin H (tile ((Fintype.equivFin W).symm i)).east
  south i := Fintype.equivFin V (tile ((Fintype.equivFin W).symm i)).south
  north i := Fintype.equivFin V (tile ((Fintype.equivFin W).symm i)).north

theorem registerWangTile_ofWang_eq {W H V : Type*}
    [Fintype W] [Fintype H] [Fintype V]
    [Nonempty W] [Nonempty H] [Nonempty V]
    (tile : W → WangTile H V) (R : ℕ) (hR : 2 ≤ R) :
    registerWangTile (registerParamsOfWang tile R hR) =
      relabelWangTile (Fintype.equivFin W) (Fintype.equivFin H)
        (Fintype.equivFin V) tile := by
  rfl

theorem openWangCount_registerParamsOfWang {W H V : Type*}
    [Fintype W] [Fintype H] [Fintype V]
    [Nonempty W] [Nonempty H] [Nonempty V]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (R : ℕ) (hR : 2 ≤ R) (w h : ℕ) :
    openWangCount (registerWangTile (registerParamsOfWang tile R hR)) w h =
      openWangCount tile w h := by
  rw [registerWangTile_ofWang_eq]
  exact openWangCount_relabel
    (Fintype.equivFin W) (Fintype.equivFin H) (Fintype.equivFin V)
    tile w h

/-- A concrete rectangle certificate survives enumeration into the register
tables without changing the base. -/
def registerParamsOfWang.rectangleBound {W H V : Type*}
    [Fintype W] [Fintype H] [Fintype V]
    [Nonempty W] [Nonempty H] [Nonempty V]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (R : ℕ) (hR : 2 ≤ R)
    (C : WangRectangleBound R tile) :
    WangRectangleBound (registerParamsOfWang tile R hR).perimeterBase
      (registerWangTile (registerParamsOfWang tile R hR)) := by
  rw [registerWangTile_ofWang_eq]
  exact C.relabel (Fintype.equivFin W) (Fintype.equivFin H)
    (Fintype.equivFin V) tile

/-! ## Instantiation with the actual higher-block tile inventory -/

namespace ConcreteWProd

variable {State Tape Arrow ScanState : Type*}
variable [Fintype State] [Fintype Tape] [Fintype Arrow] [Fintype ScanState]
variable [DecidableEq State] [DecidableEq Tape] [DecidableEq Arrow]
variable [DecidableEq ScanState]

variable (M : TableauMachineData State Tape Arrow)
variable (Q : ℕ) [NeZero Q]

abbrev Tab := HigherBlockTableauTile State Tape Arrow M
abbrev HTab := TableauHorizontalColour State Tape
abbrev VTab := TableauVerticalColour State Tape Arrow
abbrev Kcol := Fintype.card (HigherBlockTableau.TableauColumnSummary State Tape Arrow M)

abbrev Tracks (M : TableauMachineData State Tape Arrow) (Q : ℕ) [NeZero Q]
    (ScanState : Type*) := WProdTracks Q (Tab M) ScanState

abbrev Horizontal (Q : ℕ) (State Tape : Type*) :=
  Option (((AmpHorizontalColour Q × Bool) × TableauHorizontalColour State Tape) × Bool)

abbrev Vertical (Q : ℕ) (State Tape Arrow ScanState : Type*) :=
  Option (((AmpVerticalColour Q × Bool) × TableauVerticalColour State Tape Arrow) ×
    Option ScanState)

/-- The five same-cell constraints `(K-W)`, `(K-E)`, `(K-S)`, `(K-N)`, and
`(K-nE)` of the accepted product compiler.  Each is a finite Boolean lookup
table on the already concrete component alphabet. -/
structure FiveCouplingTable
    (M : TableauMachineData State Tape Arrow) (Q : ℕ) [NeZero Q]
    (ScanState : Type*) where
  west : Tracks M Q ScanState → Bool
  east : Tracks M Q ScanState → Bool
  south : Tracks M Q ScanState → Bool
  north : Tracks M Q ScanState → Bool
  nonEast : Tracks M Q ScanState → Bool

def FiveCouplingTable.accepts
    (K : FiveCouplingTable M Q ScanState) (u : Tracks M Q ScanState) : Prop :=
  K.west u = true ∧ K.east u = true ∧ K.south u = true ∧
    K.north u = true ∧ K.nonEast u = true

instance (K : FiveCouplingTable M Q ScanState) : DecidablePred K.accepts :=
  fun u => Classical.propDecidable (FiveCouplingTable.accepts M Q K u)

def wangTile (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :=
  wProdWangTile (ScanState := ScanState) Q (higherBlockTableauWangTile M) Coupled

def perimeterBase : ℕ :=
  wProdRectangleBase Q (HTab (State := State) (Tape := Tape)) ScanState (Kcol M) + 1

theorem perimeterBase_ge_two : 2 ≤ perimeterBase M Q (ScanState := ScanState) := by
  unfold perimeterBase wProdRectangleBase
  have hA : 0 < (Fintype.card (SharedQAmpTile Q) + 1) ^ 2 := by positivity
  have hH : 0 < Fintype.card (HTab (State := State) (Tape := Tape)) + 1 := by omega
  have hK : 0 < Kcol M + 1 := by omega
  have hS : 0 < Fintype.card (ScannerTile ScanState) + 1 := by omega
  have : 0 < (Fintype.card (SharedQAmpTile Q) + 1) ^ 2 * 4 *
      ((Fintype.card (HTab (State := State) (Tape := Tape)) + 1) * (Kcol M + 1)) *
      (Fintype.card (ScannerTile ScanState) + 1) := by positivity
  omega

/-- The accepted arbitrary-rectangle fact for the actual four-track inventory,
uniformly in the five local coupling predicates. -/
def rectangleBound (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :
    WangRectangleBound (perimeterBase M Q (ScanState := ScanState))
      (wangTile M Q Coupled) where
  bound w h := by
    have hb := (wProdRectangleBound (ScanState := ScanState) Q
      (higherBlockTableauWangTile M)
      (HigherBlockTableau.constantEastColumnBound M) Coupled).bound w h
    simpa [perimeterBase, wangTile, Kcol, HTab] using hb

noncomputable instance horizontalNonempty : Nonempty
    (Option (((AmpHorizontalColour Q × Bool) × HTab (State := State) (Tape := Tape)) × Bool)) :=
  ⟨none⟩

noncomputable instance verticalNonempty : Nonempty
    (Option (((AmpVerticalColour Q × Bool) × VTab (State := State) (Tape := Tape)
      (Arrow := Arrow)) × Option ScanState)) := ⟨none⟩

/-- The actual enumerated `RegisterParams`.  The tile type is nonempty because
the private dummy is always present, independently of whether the coupling
predicate admits a computation tile. -/
def registerParams (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] : RegisterParams :=
  registerParamsOfWang (wangTile M Q Coupled)
    (perimeterBase M Q (ScanState := ScanState))
    (perimeterBase_ge_two M Q (ScanState := ScanState))

noncomputable local instance registerTileDecidableEq
    (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :
    DecidableEq (RegisterTile (registerParams M Q Coupled)) := Classical.decEq _

/-- Exact certificate consumed by
`RectangularJunkBounds.ofDissectionAndWang` and hence by the unconditional
physical floor readout. -/
def registerRectangleBound (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :
    WangRectangleBound (registerParams M Q Coupled).perimeterBase
      (registerWangTile (registerParams M Q Coupled)) :=
  registerParamsOfWang.rectangleBound (wangTile M Q Coupled)
    (perimeterBase M Q (ScanState := ScanState))
    (perimeterBase_ge_two M Q (ScanState := ScanState))
    (rectangleBound M Q Coupled)

/-- Specialisation to the literal five coupling tables of `W_prod`. -/
def registerRectangleBoundOfFiveCouplings
    (K : FiveCouplingTable M Q ScanState) :
    WangRectangleBound (registerParams M Q K.accepts).perimeterBase
      (registerWangTile (registerParams M Q K.accepts)) :=
  registerRectangleBound M Q K.accepts

/-- Feed the concrete product/register certificate into the already verified
dissection accounting. -/
def rectangularJunkBounds (Coupled : Tracks M Q ScanState → Prop)
    [DecidablePred Coupled] {n : ℕ} (whole : RectangularPartition n)
    (D : RectangularDissectionFacts n whole) :
    RectangularJunkBounds n (registerParams M Q Coupled).perimeterBase
      (registerWangTile (registerParams M Q Coupled)) whole :=
  RectangularJunkBounds.ofDissectionAndWang n
    (registerParams M Q Coupled).perimeterBase
    (registerWangTile (registerParams M Q Coupled)) whole D
    (registerRectangleBound M Q Coupled)

/-- End-to-end use of the concrete perimeter theorem by the physical floor
readout.  The only remaining argument is the independent rectangular
dissection census/perimeter theorem. -/
theorem physicalFloorReadout (Coupled : Tracks M Q ScanState → Prop)
    [DecidablePred Coupled] {n : ℕ} (hn : 2 ≤ n)
    (D : RectangularDissectionFacts n
      (wholePartition n (lt_of_lt_of_le (by decide) hn))) :
    Fintype.card
        (Tiling (registerTileSupport (registerParams M Q Coupled))
          (square ((registerParams M Q Coupled).pitch * n))) /
          (registerParams M Q Coupled).amp ^ amplifierExponent n =
      openWangCount (registerWangTile (registerParams M Q Coupled)) n n := by
  exact physical_floor_readout_of_rectangular_bounds
    (registerParams M Q Coupled) hn
    (rectangularJunkBounds M Q Coupled
      (wholePartition n (lt_of_lt_of_le (by decide) hn)) D)

end ConcreteWProd

end
end PakFixedPolyomino
