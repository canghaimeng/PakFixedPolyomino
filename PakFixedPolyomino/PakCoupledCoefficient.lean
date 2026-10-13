import PakFixedPolyomino.PakAmpCoefficient
import PakFixedPolyomino.MStarULogAssembly
import PakFixedPolyomino.PakMStarCouplingCorrectness

/-! The shared-`Q` coefficient decomposition lifted to the actual fixed
four-track coupled Wang inventory. -/

namespace PakFixedPolyomino.PakCoupledCoefficient

noncomputable section

abbrev Machine := MStarULogAssembly.tableauData
abbrev ScannerState := ConcretePakScanner.State

abbrev Tracks (Q : ℕ) [NeZero Q] :=
  ConcreteWProd.Tracks Machine Q ScannerState

def Coupled (Q : ℕ) [NeZero Q] : Tracks Q → Prop :=
  ConcreteWProd.FiveCouplingTable.accepts Machine Q
    (MStarULogAssembly.fiveCouplings Q)

instance (Q : ℕ) [NeZero Q] : DecidablePred (Coupled Q) :=
  by
    intro u
    unfold Coupled
    infer_instance

abbrev CoupledTrack (Q : ℕ) [NeZero Q] := {u : Tracks Q // Coupled Q u}

abbrev coupledWangTile (Q : ℕ) [NeZero Q] :=
  wProdComputeTile Q (higherBlockTableauWangTile Machine) (Coupled Q)

abbrev CoupledTiling (Q : ℕ) [NeZero Q] (w h : ℕ) :=
  OpenWangTiling (coupledWangTile Q) w h

def eraseTracks {Q : ℕ} [NeZero Q] (u : Tracks Q) : Tracks 1 :=
  (((PakAmpCoefficient.eraseAmpTile u.1.1.1, u.1.1.2), u.1.2), u.2)

@[simp] theorem eraseTracks_amp {Q : ℕ} [NeZero Q] (u : Tracks Q) :
    PakCouplingGenerated.amp Machine 1 (eraseTracks u) =
      PakAmpCoefficient.eraseAmpTile
        (PakCouplingGenerated.amp Machine Q u) := rfl

@[simp] theorem eraseTracks_ripple {Q : ℕ} [NeZero Q] (u : Tracks Q) :
    PakCouplingGenerated.ripple Machine 1 (eraseTracks u) =
      PakCouplingGenerated.ripple Machine Q u := rfl

@[simp] theorem eraseTracks_tableau {Q : ℕ} [NeZero Q] (u : Tracks Q) :
    PakCouplingGenerated.tableau Machine 1 (eraseTracks u) =
      PakCouplingGenerated.tableau Machine Q u := rfl

@[simp] theorem eraseTracks_scan {Q : ℕ} [NeZero Q] (u : Tracks Q) :
    PakCouplingGenerated.scan Machine 1 (eraseTracks u) =
      PakCouplingGenerated.scan Machine Q u := rfl

theorem coupled_eraseTracks_iff {Q : ℕ} [NeZero Q] (u : Tracks Q) :
    Coupled Q u ↔ Coupled 1 (eraseTracks u) := by
  unfold Coupled MStarULogAssembly.fiveCouplings
  rw [PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Machine Q u,
    PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Machine 1 (eraseTracks u)]
  rfl

def eraseCoupledTrack {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) : CoupledTrack 1 :=
  ⟨eraseTracks u.1, (coupled_eraseTracks_iff u.1).mp u.2⟩

@[simp] theorem eraseCoupledTrack_amp {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) :
    (eraseCoupledTrack u).1.1.1.1 =
      PakAmpCoefficient.eraseAmpTile u.1.1.1.1 := rfl

def eraseAmpHorizontalColour {Q : ℕ}
    (c : AmpHorizontalColour Q) : AmpHorizontalColour 1 where
  westDead := c.westDead
  westCode := 0
  eastDead := c.eastDead
  eastCode := 0
  southChain := c.southChain
  northChain := c.northChain

def eraseAmpVerticalColour {Q : ℕ}
    (c : AmpVerticalColour Q) : AmpVerticalColour 1 where
  westChain := c.westChain
  eastChain := c.eastChain
  southDead := c.southDead
  southCode := 0
  northDead := c.northDead
  northCode := 0

def eraseHorizontalColour {Q : ℕ}
    (c : (((AmpHorizontalColour Q × Bool) ×
      TableauHorizontalColour MStarULogAssembly.State MStarULogAssembly.Tape) ×
        Bool)) :
    (((AmpHorizontalColour 1 × Bool) ×
      TableauHorizontalColour MStarULogAssembly.State MStarULogAssembly.Tape) ×
        Bool) :=
  (((eraseAmpHorizontalColour c.1.1.1, c.1.1.2), c.1.2), c.2)

def eraseVerticalColour {Q : ℕ}
    (c : (((AmpVerticalColour Q × Bool) ×
      TableauVerticalColour MStarULogAssembly.State MStarULogAssembly.Tape
        MStarULogAssembly.Arrow) × Option ScannerState)) :
    (((AmpVerticalColour 1 × Bool) ×
      TableauVerticalColour MStarULogAssembly.State MStarULogAssembly.Tape
        MStarULogAssembly.Arrow) × Option ScannerState) :=
  (((eraseAmpVerticalColour c.1.1.1, c.1.1.2), c.1.2), c.2)

@[simp] theorem eraseCoupledTrack_west {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) :
    (coupledWangTile 1 (eraseCoupledTrack u)).west =
      eraseHorizontalColour (coupledWangTile Q u).west := rfl

@[simp] theorem eraseCoupledTrack_east {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) :
    (coupledWangTile 1 (eraseCoupledTrack u)).east =
      eraseHorizontalColour (coupledWangTile Q u).east := rfl

@[simp] theorem eraseCoupledTrack_south {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) :
    (coupledWangTile 1 (eraseCoupledTrack u)).south =
      eraseVerticalColour (coupledWangTile Q u).south := rfl

@[simp] theorem eraseCoupledTrack_north {Q : ℕ} [NeZero Q]
    (u : CoupledTrack Q) :
    (coupledWangTile 1 (eraseCoupledTrack u)).north =
      eraseVerticalColour (coupledWangTile Q u).north := rfl

def eraseCoupledTiling {Q : ℕ} [NeZero Q] {w h : ℕ}
    (F : CoupledTiling Q w h) : CoupledTiling 1 w h := by
  refine ⟨fun i j => eraseCoupledTrack (F.1 i j), ?_⟩
  constructor
  · intro i j hi
    rw [eraseCoupledTrack_east, eraseCoupledTrack_west]
    exact congrArg eraseHorizontalColour (F.2.1 i j hi)
  · intro i j hj
    rw [eraseCoupledTrack_north, eraseCoupledTrack_south]
    exact congrArg eraseVerticalColour (F.2.2 i j hj)

@[simp] theorem eraseCoupledTiling_cell {Q : ℕ} [NeZero Q]
    {w h : ℕ} (F : CoupledTiling Q w h) (i : Fin w) (j : Fin h) :
    (eraseCoupledTiling F).1 i j = eraseCoupledTrack (F.1 i j) := rfl

def amplifierProjection {Q : ℕ} [NeZero Q] {w h : ℕ}
    (F : CoupledTiling Q w h) : PakAmpCoefficient.AmpTiling (Q := Q) w h := by
  refine ⟨fun i j => (F.1 i j).1.1.1.1, ?_⟩
  constructor
  · intro i j hi
    have hm := F.2.1 i j hi
    exact congrArg (fun c => c.1.1.1) hm
  · intro i j hj
    have hm := F.2.2 i j hj
    exact congrArg (fun c => c.1.1.1) hm

@[simp] theorem amplifierProjection_cell {Q : ℕ} [NeZero Q]
    {w h : ℕ} (F : CoupledTiling Q w h) (i : Fin w) (j : Fin h) :
    (amplifierProjection F).1 i j = (F.1 i j).1.1.1.1 := rfl

theorem amplifierProjection_erase {Q : ℕ} [NeZero Q]
    {w h : ℕ} (F : CoupledTiling Q w h) :
    amplifierProjection (eraseCoupledTiling F) =
      PakAmpCoefficient.eraseAmpTiling (amplifierProjection F) := by
  apply Subtype.ext
  funext i j
  rfl

def liftTracksAt {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) : Tracks Q :=
  (((PakAmpCoefficient.liftAmpTile (amplifierProjection skeleton) hw hh A i j,
      (skeleton.1 i j).1.1.1.2),
    (skeleton.1 i j).1.1.2),
    (skeleton.1 i j).1.2)

theorem erase_liftTracksAt {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) :
    eraseTracks (liftTracksAt skeleton hw hh A i j) = (skeleton.1 i j).1 := by
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact PakAmpCoefficient.erase_liftAmpTile
          (amplifierProjection skeleton) hw hh A i j
      · rfl
    · rfl
  · rfl

def liftCoupledTrackAt {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) : CoupledTrack Q := by
  refine ⟨liftTracksAt skeleton hw hh A i j, ?_⟩
  apply (coupled_eraseTracks_iff _).mpr
  rw [erase_liftTracksAt]
  exact (skeleton.1 i j).2

theorem liftCoupledTrackAt_horizontal_match {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    (coupledWangTile Q (liftCoupledTrackAt skeleton hw hh A i j)).east =
      (coupledWangTile Q
        (liftCoupledTrackAt skeleton hw hh A ⟨i.1 + 1, hi⟩ j)).west := by
  have hm := skeleton.2.1 i j hi
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact PakAmpCoefficient.liftAmpTile_horizontal_match
          (amplifierProjection skeleton) hw hh A i j hi
      · exact congrArg (fun c => c.1.1.2) hm
    · exact congrArg (fun c => c.1.2) hm
  · change (scannerTile (S := ScannerState) (skeleton.1 i j).1.2).east =
      (scannerTile (S := ScannerState)
        (skeleton.1 ⟨i.1 + 1, hi⟩ j).1.2).west
    have hs := congrArg Prod.snd hm
    exact hs

theorem liftCoupledTrackAt_vertical_match {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (coupledWangTile Q (liftCoupledTrackAt skeleton hw hh A i j)).north =
      (coupledWangTile Q
        (liftCoupledTrackAt skeleton hw hh A i ⟨j.1 + 1, hj⟩)).south := by
  have hm := skeleton.2.2 i j hj
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact PakAmpCoefficient.liftAmpTile_vertical_match
          (amplifierProjection skeleton) hw hh A i j hj
      · exact congrArg (fun c => c.1.1.2) hm
    · exact congrArg (fun c => c.1.2) hm
  · change (scannerTile (S := ScannerState) (skeleton.1 i j).1.2).north =
      (scannerTile (S := ScannerState)
        (skeleton.1 i ⟨j.1 + 1, hj⟩).1.2).south
    have hs := congrArg Prod.snd hm
    exact hs

def liftCoupledTiling {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h) : CoupledTiling Q w h := by
  refine ⟨fun i j => liftCoupledTrackAt skeleton hw hh A i j, ?_⟩
  constructor
  · intro i j hi
    exact liftCoupledTrackAt_horizontal_match skeleton hw hh A i j hi
  · intro i j hj
    exact liftCoupledTrackAt_vertical_match skeleton hw hh A i j hj

@[simp] theorem erase_liftCoupledTiling {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h) :
    eraseCoupledTiling (liftCoupledTiling skeleton hw hh A) = skeleton := by
  apply Subtype.ext
  funext i j
  apply Subtype.ext
  exact erase_liftTracksAt skeleton hw hh A i j

abbrev CoupledSkeletonFiber {w h : ℕ}
    (Q : ℕ) [NeZero Q] (skeleton : CoupledTiling 1 w h) :=
  {F : CoupledTiling Q w h // eraseCoupledTiling F = skeleton}

noncomputable instance {w h : ℕ} (Q : ℕ) [NeZero Q]
    (skeleton : CoupledTiling 1 w h) :
    Fintype (CoupledSkeletonFiber Q skeleton) := Fintype.ofFinite _

def amplifierFiberOfCoupledFiber {Q w h : ℕ} [NeZero Q]
    {skeleton : CoupledTiling 1 w h}
    (F : CoupledSkeletonFiber Q skeleton) :
    PakAmpCoefficient.AmpSkeletonFiber Q (amplifierProjection skeleton) := by
  refine ⟨amplifierProjection F.1, ?_⟩
  calc
    PakAmpCoefficient.eraseAmpTiling (amplifierProjection F.1) =
        amplifierProjection (eraseCoupledTiling F.1) :=
      (amplifierProjection_erase F.1).symm
    _ = amplifierProjection skeleton := by rw [F.2]

noncomputable def coupledFiberAssignment {Q w h : ℕ} [NeZero Q]
    {skeleton : CoupledTiling 1 w h}
    (F : CoupledSkeletonFiber Q skeleton) (hw : 2 ≤ w) (hh : 0 < h) :
    PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h :=
  PakAmpCoefficient.fiberAssignment (amplifierFiberOfCoupledFiber F) hw hh

def assignmentCoupledFiber {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h) : CoupledSkeletonFiber Q skeleton :=
  ⟨liftCoupledTiling skeleton hw hh A,
    erase_liftCoupledTiling skeleton hw hh A⟩

theorem amplifierProjection_liftCoupledTiling
    {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h) :
    amplifierProjection (liftCoupledTiling skeleton hw hh A) =
      PakAmpCoefficient.liftAmpTiling
        (amplifierProjection skeleton) hw hh A := by
  apply Subtype.ext
  funext i j
  rfl

theorem coupledFiberAssignment_assignmentCoupledFiber
    {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : PakAmpCoefficient.BoundaryQAssignment
      (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh) Q w h) :
    coupledFiberAssignment (assignmentCoupledFiber skeleton hw hh A) hw hh = A := by
  let F := assignmentCoupledFiber skeleton hw hh A
  have hfiber : amplifierFiberOfCoupledFiber F =
      PakAmpCoefficient.assignmentFiber (amplifierProjection skeleton) hw hh A := by
    apply Subtype.ext
    exact amplifierProjection_liftCoupledTiling skeleton hw hh A
  change PakAmpCoefficient.fiberAssignment
      (amplifierFiberOfCoupledFiber F) hw hh = A
  rw [hfiber]
  exact PakAmpCoefficient.fiberAssignment_assignmentFiber
    (amplifierProjection skeleton) hw hh A

theorem assignmentCoupledFiber_coupledFiberAssignment
    {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h)
    (F : CoupledSkeletonFiber Q skeleton) :
    assignmentCoupledFiber skeleton hw hh (coupledFiberAssignment F hw hh) = F := by
  rcases F with ⟨F, hF⟩
  subst skeleton
  let AF : PakAmpCoefficient.AmpSkeletonFiber Q
      (amplifierProjection (eraseCoupledTiling F)) :=
    amplifierFiberOfCoupledFiber
      (⟨F, rfl⟩ : CoupledSkeletonFiber Q (eraseCoupledTiling F))
  have hampSubtype := PakAmpCoefficient.assignmentFiber_fiberAssignment
    (amplifierProjection (eraseCoupledTiling F)) hw hh AF
  have hamp : PakAmpCoefficient.liftAmpTiling
      (amplifierProjection (eraseCoupledTiling F)) hw hh
        (PakAmpCoefficient.fiberAssignment AF hw hh) =
      amplifierProjection F := congrArg Subtype.val hampSubtype
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · exact congrFun (congrFun (congrArg Subtype.val hamp) i) j
      · rfl
    · rfl
  · rfl

/-- The exact shared-`Q` fibre theorem for the full fixed four-track coupled
Wang inventory.  The other three tracks contribute no multiplicity. -/
noncomputable def coupledSkeletonFiberEquivBoundaryQAssignment
    {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h) :
    CoupledSkeletonFiber Q skeleton ≃
      PakAmpCoefficient.BoundaryQAssignment
        (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
          (by omega) hh) Q w h where
  toFun F := coupledFiberAssignment F hw hh
  invFun A := assignmentCoupledFiber skeleton hw hh A
  left_inv := assignmentCoupledFiber_coupledFiberAssignment skeleton hw hh
  right_inv := coupledFiberAssignment_assignmentCoupledFiber skeleton hw hh

theorem card_coupledSkeletonFiber {Q w h : ℕ} [NeZero Q]
    (skeleton : CoupledTiling 1 w h) (hw : 2 ≤ w) (hh : 0 < h) :
    Fintype.card (CoupledSkeletonFiber Q skeleton) =
      Q ^ (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
        (by omega) hh).qDegree w h := by
  rw [Fintype.card_congr
    (coupledSkeletonFiberEquivBoundaryQAssignment skeleton hw hh)]
  exact PakAmpCoefficient.card_boundaryQAssignment _ Q hw

noncomputable def coupledTilingSigmaFiberEquiv (Q : ℕ) [NeZero Q]
    (w h : ℕ) :
    CoupledTiling Q w h ≃
      Σ skeleton : CoupledTiling 1 w h,
        CoupledSkeletonFiber Q skeleton :=
  (Equiv.sigmaFiberEquiv
    (eraseCoupledTiling (Q := Q) (w := w) (h := h))).symm

theorem card_coupledTiling_eq_sum_skeletonFibers
    (Q : ℕ) [NeZero Q] (w h : ℕ) :
    Fintype.card (CoupledTiling Q w h) =
      ∑ skeleton : CoupledTiling 1 w h,
        Fintype.card (CoupledSkeletonFiber Q skeleton) := by
  rw [Fintype.card_congr (coupledTilingSigmaFiberEquiv Q w h)]
  simp [Fintype.card_sigma]

theorem card_coupledTiling_eq_sum_skeletonPowers
    (Q : ℕ) [NeZero Q] {w h : ℕ} (hw : 2 ≤ w) (hh : 0 < h) :
    Fintype.card (CoupledTiling Q w h) =
      ∑ skeleton : CoupledTiling 1 w h,
        Q ^ (PakAmpCoefficient.boundaryMask (amplifierProjection skeleton)
          (by omega) hh).qDegree w h := by
  rw [card_coupledTiling_eq_sum_skeletonFibers]
  apply Fintype.sum_congr
  intro skeleton
  exact card_coupledSkeletonFiber skeleton hw hh

abbrev FullMaskSkeleton (w h : ℕ) (hw : 0 < w) (hh : 0 < h) :=
  {skeleton : CoupledTiling 1 w h //
    PakAmpCoefficient.boundaryMask (amplifierProjection skeleton) hw hh =
      PakAmpCoefficient.BoundaryMask.full}

def fullMaskSkeletonToFullFrame {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (S : FullMaskSkeleton w h hw hh) :
    PakMStarCouplingCorrectness.FullFrame w h where
  tiling := S.1
  width_pos := hw
  height_pos := hh
  boundary := by
    have hwest : (PakAmpCoefficient.boundaryMask
        (amplifierProjection S.1) hw hh).west = true := by
      rw [S.2]
      rfl
    have heast : (PakAmpCoefficient.boundaryMask
        (amplifierProjection S.1) hw hh).east = true := by
      rw [S.2]
      rfl
    have hsouth : (PakAmpCoefficient.boundaryMask
        (amplifierProjection S.1) hw hh).south = true := by
      rw [S.2]
      rfl
    have hnorth : (PakAmpCoefficient.boundaryMask
        (amplifierProjection S.1) hw hh).north = true := by
      rw [S.2]
      rfl
    constructor
    · intro j
      change ((amplifierProjection S.1).1 ⟨0, hw⟩ j).1.westActive = true
      exact (PakAmpCoefficient.westActive_iff_boundaryMask
        (amplifierProjection S.1) hw hh ⟨0, hw⟩ j).mpr ⟨hwest, rfl⟩
    constructor
    · intro j
      change ((amplifierProjection S.1).1 ⟨w - 1, by omega⟩ j).1.eastActive = true
      apply (PakAmpCoefficient.eastActive_iff_boundaryMask
        (amplifierProjection S.1) hw hh ⟨w - 1, by omega⟩ j).mpr
      exact ⟨heast, by change w - 1 + 1 = w; omega⟩
    constructor
    · intro i
      change ((amplifierProjection S.1).1 i ⟨0, hh⟩).1.southActive = true
      exact (PakAmpCoefficient.southActive_iff_boundaryMask
        (amplifierProjection S.1) hw hh i ⟨0, hh⟩).mpr ⟨hsouth, rfl⟩
    · intro i
      change ((amplifierProjection S.1).1 i ⟨h - 1, by omega⟩).1.northActive = true
      apply (PakAmpCoefficient.northActive_iff_boundaryMask
        (amplifierProjection S.1) hw hh i ⟨h - 1, by omega⟩).mpr
      exact ⟨hnorth, by change h - 1 + 1 = h; omega⟩

def fullFrameToFullMaskSkeleton {w h : ℕ}
    (F : PakMStarCouplingCorrectness.FullFrame w h) :
    FullMaskSkeleton w h F.width_pos F.height_pos := by
  refine ⟨F.tiling, ?_⟩
  apply PakAmpCoefficient.BoundaryMask.ext
  · change (PakMStarCouplingCorrectness.ampAt F.tiling
      ⟨0, F.width_pos⟩ ⟨0, F.height_pos⟩).1.westActive = true
    exact F.boundary.1 ⟨0, F.height_pos⟩
  · change (PakMStarCouplingCorrectness.ampAt F.tiling
      ⟨w - 1, Nat.sub_lt F.width_pos (by decide)⟩
        ⟨0, F.height_pos⟩).1.eastActive = true
    exact F.boundary.2.1 ⟨0, F.height_pos⟩
  · change (PakMStarCouplingCorrectness.ampAt F.tiling
      ⟨0, F.width_pos⟩ ⟨0, F.height_pos⟩).1.southActive = true
    exact F.boundary.2.2.1 ⟨0, F.width_pos⟩
  · change (PakMStarCouplingCorrectness.ampAt F.tiling
      ⟨0, F.width_pos⟩
        ⟨h - 1, Nat.sub_lt F.height_pos (by decide)⟩).1.northActive = true
    exact F.boundary.2.2.2 ⟨0, F.width_pos⟩

noncomputable def fullMaskSkeletonEquivFullFrame
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    FullMaskSkeleton w h hw hh ≃
      PakMStarCouplingCorrectness.FullFrame w h where
  toFun := fullMaskSkeletonToFullFrame hw hh
  invFun F := by
    let S := fullFrameToFullMaskSkeleton F
    exact ⟨S.1, by simpa using S.2⟩
  left_inv S := by
    apply Subtype.ext
    rfl
  right_inv F := by
    apply PakMStarCouplingCorrectness.FullFrame.ext
    rfl

instance fullFrameFinite (w h : ℕ) :
    Finite (PakMStarCouplingCorrectness.FullFrame w h) :=
  Finite.of_injective
    (fun F : PakMStarCouplingCorrectness.FullFrame w h => F.tiling) (by
      intro F G htiling
      apply PakMStarCouplingCorrectness.FullFrame.ext
      exact htiling)

noncomputable instance fullFrameFintype (w h : ℕ) :
    Fintype (PakMStarCouplingCorrectness.FullFrame w h) :=
  Fintype.ofFinite _

def skeletonMask {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (skeleton : CoupledTiling 1 w h) : PakAmpCoefficient.BoundaryMask :=
  PakAmpCoefficient.boundaryMask (amplifierProjection skeleton) hw hh

abbrev CoupledSkeletonsOfMask {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (mask : PakAmpCoefficient.BoundaryMask) :=
  {skeleton : CoupledTiling 1 w h // skeletonMask hw hh skeleton = mask}

def coupledSkeletonCount {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (mask : PakAmpCoefficient.BoundaryMask) : ℕ :=
  Fintype.card (CoupledSkeletonsOfMask hw hh mask)

def fullFrameCount {w h : ℕ} (hw : 0 < w) (hh : 0 < h) : ℕ :=
  Fintype.card (FullMaskSkeleton w h hw hh)

theorem coupledSkeletonCount_full_eq_fullFrameCount
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    coupledSkeletonCount hw hh PakAmpCoefficient.BoundaryMask.full =
      fullFrameCount hw hh := rfl

theorem fullFrameCount_eq_card_fullFrame
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    fullFrameCount hw hh =
      Fintype.card (PakMStarCouplingCorrectness.FullFrame w h) :=
  Fintype.card_congr (fullMaskSkeletonEquivFullFrame hw hh)

theorem sum_skeletonPowers_eq_sum_masks
    (Q : ℕ) {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    (∑ skeleton : CoupledTiling 1 w h,
        Q ^ (skeletonMask hw hh skeleton).qDegree w h) =
      ∑ mask : PakAmpCoefficient.BoundaryMask,
        Q ^ mask.qDegree w h * coupledSkeletonCount hw hh mask := by
  let e := (Equiv.sigmaFiberEquiv (skeletonMask hw hh))
  calc
    (∑ skeleton : CoupledTiling 1 w h,
        Q ^ (skeletonMask hw hh skeleton).qDegree w h) =
        ∑ z : Σ mask : PakAmpCoefficient.BoundaryMask,
          CoupledSkeletonsOfMask hw hh mask,
            Q ^ (skeletonMask hw hh (e z)).qDegree w h := by
      exact (e.sum_comp (fun skeleton =>
        Q ^ (skeletonMask hw hh skeleton).qDegree w h)).symm
    _ = ∑ z : Σ mask : PakAmpCoefficient.BoundaryMask,
          CoupledSkeletonsOfMask hw hh mask,
            Q ^ z.1.qDegree w h := by
      apply Fintype.sum_congr
      intro z
      congr 2
      exact z.2.2
    _ = ∑ mask : PakAmpCoefficient.BoundaryMask,
        ∑ _skeleton : CoupledSkeletonsOfMask hw hh mask,
          Q ^ mask.qDegree w h := by
      exact Fintype.sum_sigma _
    _ = ∑ mask : PakAmpCoefficient.BoundaryMask,
        Q ^ mask.qDegree w h * coupledSkeletonCount hw hh mask := by
      apply Fintype.sum_congr
      intro mask
      simp [coupledSkeletonCount, Nat.mul_comm]

theorem card_coupledTiling_eq_sum_masks
    (Q : ℕ) [NeZero Q] {w h : ℕ} (hw : 2 ≤ w) (hh : 0 < h) :
    Fintype.card (CoupledTiling Q w h) =
      ∑ mask : PakAmpCoefficient.BoundaryMask,
        Q ^ mask.qDegree w h *
          coupledSkeletonCount (Nat.zero_lt_of_lt hw) hh mask := by
  rw [card_coupledTiling_eq_sum_skeletonPowers Q hw hh]
  exact sum_skeletonPowers_eq_sum_masks Q (Nat.zero_lt_of_lt hw) hh

def coefficientPerimeterBase : ℕ :=
  ConcreteWProd.perimeterBase Machine 1 (ScanState := ScannerState)

theorem coupledSkeletonCount_le_perimeter
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (mask : PakAmpCoefficient.BoundaryMask) :
    coupledSkeletonCount hw hh mask ≤ coefficientPerimeterBase ^ (w + h) := by
  have hsub : coupledSkeletonCount hw hh mask ≤
      Fintype.card (CoupledTiling 1 w h) := by
    exact Fintype.card_subtype_le _
  have hequiv := Fintype.card_congr
    (withDummyOpenEquiv (coupledWangTile 1) w h hw hh)
  have hcomp : Fintype.card (CoupledTiling 1 w h) ≤
      Fintype.card
        (OpenWangTiling (withDummyWangTile (coupledWangTile 1)) w h) := by
    rw [hequiv]
    simp
  have hbound := (ConcreteWProd.rectangleBound Machine 1 (Coupled 1)).bound w h
  unfold openWangCount at hbound
  change Fintype.card
      (OpenWangTiling (withDummyWangTile (coupledWangTile 1)) w h) ≤
        coefficientPerimeterBase ^ (w + h) at hbound
  exact hsub.trans (hcomp.trans hbound)

theorem maskSum_eq_full_add_nonFullTail
    (count : PakAmpCoefficient.BoundaryMask → ℕ) (Q n : ℕ) :
    (∑ mask : PakAmpCoefficient.BoundaryMask,
        Q ^ mask.qDegree n n * count mask) =
      Q ^ PakAmpCoefficient.BoundaryMask.full.qDegree n n *
          count PakAmpCoefficient.BoundaryMask.full +
        PakAmpCoefficient.nonFullMaskTail count Q n := by
  have hmem : PakAmpCoefficient.BoundaryMask.full ∈
      (Finset.univ : Finset PakAmpCoefficient.BoundaryMask) := Finset.mem_univ _
  rw [← Finset.sum_erase_add (Finset.univ :
    Finset PakAmpCoefficient.BoundaryMask)
      (fun mask => Q ^ mask.qDegree n n * count mask) hmem]
  simp only [PakAmpCoefficient.nonFullMaskTail,
    PakAmpCoefficient.nonFullMasks]
  ring

theorem card_coupledSquare_eq_full_add_tail
    (Q : ℕ) [NeZero Q] {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (CoupledTiling Q n n) =
      Q ^ PakAmpCoefficient.BoundaryMask.full.qDegree n n *
          fullFrameCount (Nat.zero_lt_of_lt hn) (Nat.zero_lt_of_lt hn) +
        PakAmpCoefficient.nonFullMaskTail
          (coupledSkeletonCount (Nat.zero_lt_of_lt hn)
            (Nat.zero_lt_of_lt hn)) Q n := by
  rw [card_coupledTiling_eq_sum_masks Q hn (Nat.zero_lt_of_lt hn),
    maskSum_eq_full_add_nonFullTail]
  rw [coupledSkeletonCount_full_eq_fullFrameCount]

def extractionQ : ℕ :=
  PakAmpCoefficient.coefficientBase coefficientPerimeterBase

theorem coefficientPerimeterBase_pos : 0 < coefficientPerimeterBase := by
  have h := ConcreteWProd.perimeterBase_ge_two Machine 1
    (ScanState := ScannerState)
  exact h.trans_lt' (by decide)

theorem extractionQ_pos : 0 < extractionQ :=
  PakAmpCoefficient.coefficientBase_pos coefficientPerimeterBase_pos

instance extractionQ_neZero : NeZero extractionQ :=
  ⟨Nat.ne_of_gt extractionQ_pos⟩

theorem coupledNonFullTail_lt_extractionPower {n : ℕ} (hn : 5 ≤ n) :
    PakAmpCoefficient.nonFullMaskTail
        (coupledSkeletonCount (Nat.zero_lt_of_lt (show 2 ≤ n by omega))
          (Nat.zero_lt_of_lt (show 2 ≤ n by omega))) extractionQ n <
      extractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree n n := by
  apply PakAmpCoefficient.nonFullMaskTail_lt_fullPower_fixedBase
    (coupledSkeletonCount (Nat.zero_lt_of_lt (show 2 ≤ n by omega))
      (Nat.zero_lt_of_lt (show 2 ≤ n by omega)))
    coefficientPerimeterBase_pos hn
  intro mask _hmask
  simpa [two_mul] using
    coupledSkeletonCount_le_perimeter (w := n) (h := n)
      (by omega) (by omega) mask

/-- Fixed-base coefficient extraction for the actual coupled square count.
No `Q` depending on `n` occurs in the statement. -/
theorem coupledSquare_div_fullPower_eq_fullFrameCount
    {n : ℕ} (hn : 5 ≤ n) :
    Fintype.card (CoupledTiling extractionQ n n) /
        extractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree n n =
      fullFrameCount
        (lt_of_lt_of_le (by decide : 0 < 5) hn)
        (lt_of_lt_of_le (by decide : 0 < 5) hn) := by
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 5) hn
  let power := extractionQ ^
    PakAmpCoefficient.BoundaryMask.full.qDegree n n
  let full := fullFrameCount hnpos hnpos
  let tail := PakAmpCoefficient.nonFullMaskTail
    (coupledSkeletonCount hnpos hnpos) extractionQ n
  have hcard := card_coupledSquare_eq_full_add_tail
    (Q := extractionQ) (n := n) hn2
  have htail : tail < power := coupledNonFullTail_lt_extractionPower hn
  have hpower : power ≠ 0 := by
    exact ne_of_gt (pow_pos extractionQ_pos _)
  rw [hcard]
  change (power * full + tail) / power = full
  rw [Nat.mul_add_div (Nat.pos_of_ne_zero hpower)]
  rw [Nat.div_eq_of_lt htail]
  omega

end

end PakFixedPolyomino.PakCoupledCoefficient
