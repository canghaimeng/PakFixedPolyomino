import PakFixedPolyomino.PakFullFrameForward
import PakFixedPolyomino.PakSlotOneScannerMultiplicity
import PakFixedPolyomino.PakSlotZeroFullFrameBijection

/-!
# Capacity-indexed east scanner data for a FullFrame

The old forward construction fixed the scanner terminator at the canonical
reserve.  The physical reverse fibre, however, records the actual number of
work cells before `rightEnd`.  This companion isolates the part of the
forward construction which is uniform in that physical capacity.

It deliberately does *not* manufacture an arbitrary-capacity MStar start
window.  `CapacitySquarePaddedRun` states the exact literal contract required
from such a run: the east scanner column must emit its time-zero old strip.
This keeps the later raw-to-FullFrame inverse honest.
-/

namespace PakFixedPolyomino.PakGeneralCapacityFullFrameForward

open FiniteOneTapeSemantics
open PakMStarCouplingCorrectness
open PakFullFrameForward
open PakSlotOneScannerMultiplicity
open PakScannerBaselineAutomaton

/-- The uncast, literal scanner tiling at an actual work-cell capacity.  Its
height is definitionally `sideSquareSize x`, so its terminal column is a
standard terminal scanner column with the capacity-specific terminal index. -/
def rawCapacityScannerTiling (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State))
      (sideSquareSize x) (sideSquareSize x) :=
  (rawCapacityScannerPath x c).toEastTiling

def rawCapacityEastIndex (x : ConcretePakSide.Word) : Fin (sideSquareSize x) :=
  ⟨sideSquareSize x - 1, by
    have h := PakSideScanner.sideScannerBits_pos x
    dsimp [sideSquareSize]
    omega⟩

theorem rawCapacityScannerTiling_east (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (j : Fin (sideSquareSize x)) :
    (rawCapacityScannerTiling x c).1 (rawCapacityEastIndex x) j =
      (rawCapacityScannerPath x c).column j := by
  exact ScannerPath.toEastTiling_east (rawCapacityScannerPath x c) j

theorem rawCapacityScannerTiling_east_explicit (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (j : Fin (sideSquareSize x)) :
    (rawCapacityScannerTiling x c).1 (rawCapacityEastIndex x) j =
      some
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) j.1,
        PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) (j.1 + 1)) := by
  rw [rawCapacityScannerTiling_east]
  rfl

/-- The literal terminal column obeys the east activity/lookahead coupling at
the capacity-specific `rightEnd`.  The displayed bit is the actual encoded
side bit, not a canonical-reserve surrogate. -/
theorem rawCapacityScannerTiling_activityCoupled (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (j : Fin (sideSquareSize x)) :
    ConcretePakScanner.ActivityCoupledStep
      (decide (j.1 = 0)) (decide (j.1 + 1 = sideSquareSize x))
      ((rawCapacityScannerTiling x c).1 (rawCapacityEastIndex x) j)
      ((ConcretePakSide.sideValue x).testBit j.1) := by
  rw [rawCapacityScannerTiling_east]
  have h := PakSlotZeroFullFrameBijection.ScannerPath.activityCoupled
    (rawCapacityScannerPath x c) j
  simpa [sideSquareSize, PakSideScanner.sideScannerHeight] using h

/-- The capacity-indexed scanner after transport to the physical square side.
This is the version which can be placed directly into a `FullTrackRunCertificate`
whose dimensions are `sideValue x` by `sideValue x`. -/
def capacityScannerTiling (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State))
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) :=
  (capacityScannerPath x c).toEastTiling

def capacityEastIndex (x : ConcretePakSide.Word) : Fin (ConcretePakSide.sideValue x) :=
  ⟨ConcretePakSide.sideValue x - 1, by
    have hbits := PakSideScanner.sideScannerBits_pos x
    have hheight := PakSideScanner.sideScannerHeight x
    omega⟩

theorem capacityScannerTiling_east (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (j : Fin (ConcretePakSide.sideValue x)) :
    (capacityScannerTiling x c).1 (capacityEastIndex x) j =
      (capacityScannerPath x c).column j := by
  exact ScannerPath.toEastTiling_east (capacityScannerPath x c) j

theorem capacityScannerTiling_activityCoupled (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (j : Fin (ConcretePakSide.sideValue x)) :
    ConcretePakScanner.ActivityCoupledStep
      (decide (j.1 = 0)) (decide (j.1 + 1 = ConcretePakSide.sideValue x))
      ((capacityScannerTiling x c).1 (capacityEastIndex x) j)
      ((ConcretePakSide.sideValue x).testBit j.1) := by
  rw [capacityScannerTiling_east]
  exact PakSlotZeroFullFrameBijection.ScannerPath.activityCoupled
    (capacityScannerPath x c) j

/-- Exact input contract for a padded MStar track that can be coupled to an
actual-capacity east scanner.  The condition is occurrence-labelled and is
imposed for every physical row of this *same* padded run. -/
structure CapacitySquarePaddedRun (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) where
  padded : PaddedUniformWindowedMStarRun
    (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)
  east_old : ∀ j : Fin (ConcretePakSide.sideValue x),
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
      ((capacityScannerPath x c).states
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      ((capacityScannerPath x c).states ⟨j.1 + 1, by omega⟩) =
      (padded.run.tableauTiling.1 (capacityEastIndex x) j).1.old

theorem CapacitySquarePaddedRun.scanner_emits_tableau_old
    {x : ConcretePakSide.Word} {c : ScannerCapacity x}
    (R : CapacitySquarePaddedRun x c)
    (j : Fin (ConcretePakSide.sideValue x)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
      ((capacityScannerPath x c).states
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      ((capacityScannerPath x c).states ⟨j.1 + 1, by omega⟩) =
      (R.padded.run.tableauTiling.1 (capacityEastIndex x) j).1.old :=
  R.east_old j

theorem capacitySide_pos (x : ConcretePakSide.Word) :
    0 < ConcretePakSide.sideValue x := by
  have hbits := PakSideScanner.sideScannerBits_pos x
  have hheight := PakSideScanner.sideScannerHeight x
  omega

theorem capacitySide_ge_three (x : ConcretePakSide.Word) :
    3 ≤ ConcretePakSide.sideValue x := by
  have hbits := PakSideScanner.sideScannerBits_pos x
  have hheight := PakSideScanner.sideScannerHeight x
  omega

theorem CapacitySquarePaddedRun.tableau_west_new_accepting
    {x : ConcretePakSide.Word} {c : ScannerCapacity x}
    (R : CapacitySquarePaddedRun x c)
    (j : Fin (ConcretePakSide.sideValue x)) :
    PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
      (R.padded.run.tableauTiling.1 ⟨0, capacitySide_pos x⟩ j).1.new := by
  rw [UniformWindowedMStarRun.tableauTiling_cell_new]
  apply WindowedMStarStep.acceptingWindow_newStrip_of_after_accept
  have hn : ConcretePakSide.sideValue x - 1 + 1 = ConcretePakSide.sideValue x :=
    Nat.sub_add_cancel (by
      have h := capacitySide_ge_three x
      omega)
  simpa [UniformWindowedMStarRun.stepWindow,
    UniformWindowedMStarRun.revTime, hn] using R.padded.run.final_accept

private theorem legal_to_top_scannerTopSouth
    (s : ConcretePakScanner.State) (b : Bool) :
    ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth b →
      PakCouplingGenerated.scannerTopSouth s := by
  intro h
  rcases h with ⟨clause, hclause⟩
  cases clause <;> simp_all [ConcretePakScanner.LegalClause,
    ConcretePakScanner.topNorth, PakCouplingGenerated.scannerTopSouth]

/-- A capacity-indexed version of the forward coupled-frame construction.
The only capacity-dependent datum is the scanner column and the `east_old`
contract in `CapacitySquarePaddedRun`; all sentinel and ripple arguments are
the same literal square construction as in the canonical case. -/
noncomputable def capacitySquareFullTrackCertificate
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (R : CapacitySquarePaddedRun x c) : FullTrackRunCertificate R.padded where
  time_pos := capacitySide_pos x
  amplifier := PakRippleCanonical.canonicalFullAmpTiling Fixed.Q
    (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)
  ripple := PakRippleCanonical.canonicalTiling
    (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)
  scanner := capacityScannerTiling x c
  coupled := by
    intro i j
    change ConcreteWProd.FiveCouplingTable.accepts Fixed.Machine Fixed.Q
      (MStarULogAssembly.fiveCouplings Fixed.Q) _
    apply (PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q _).mpr
    have hfinal := R.padded.run.final_accept
    have hleft := R.padded.left_endpoint_hash
    have hright := R.padded.right_endpoint_hash
    have heast_scan := capacityScannerTiling_east x c j
    have heast_old := R.scanner_emits_tableau_old j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hwest
      have hi : i.1 = 0 := by
        simpa [PakCouplingGenerated.amp,
          PakRippleCanonical.canonicalFullAmpTiling,
          PakRippleCanonical.canonicalFullAmpCell] using hwest
      have hi0 : i = ⟨0, capacitySide_pos x⟩ := Fin.ext hi
      subst i
      refine ⟨PakRippleCanonical.canonicalTiling_west
        (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) j
        (capacitySide_pos x),
        R.tableau_west_new_accepting j, ?_⟩
      have hnone := ScannerPath.toEastTiling_nonEast (capacityScannerPath x c)
        ⟨0, capacitySide_pos x⟩ j (by
          have h := capacitySide_ge_three x
          omega)
      simpa [PakCouplingGenerated.scan, capacityScannerTiling] using hnone
    · intro heast
      have hi : i = capacityEastIndex x := by
        apply Fin.ext
        change decide (i.1 + 1 = ConcretePakSide.sideValue x) = true at heast
        have hival : i.1 + 1 = ConcretePakSide.sideValue x :=
          decide_eq_true_eq.mp heast
        dsimp [capacityEastIndex]
        omega
      subst i
      have hripple :
          xor ((PakRippleCanonical.canonicalTiling
            (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)).1
              (capacityEastIndex x) j).1
            ((PakRippleCanonical.canonicalTiling
              (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)).1
                (capacityEastIndex x) j).2 =
            (ConcretePakSide.sideValue x).testBit j.1 := by
        simpa [capacityEastIndex, rippleTile] using
          PakRippleCanonical.canonicalTiling_east (ConcretePakSide.sideValue x)
            (ConcretePakSide.sideValue x) (capacitySide_pos x) j
      refine ⟨?_, ?_⟩
      · have hactivity := capacityScannerTiling_activityCoupled x c j
        rw [← hripple] at hactivity
        simpa [PakCouplingGenerated.amp, PakCouplingGenerated.ripple,
          PakCouplingGenerated.scan, PakRippleCanonical.canonicalFullAmpTiling,
          PakRippleCanonical.canonicalFullAmpCell, capacityScannerTiling,
          PakCanonicalScanner.eastColumnTiling,
          PakCanonicalScanner.eastColumnCell, capacityEastIndex] using hactivity
      · refine ⟨(capacityScannerPath x c).states
            ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
            (capacityScannerPath x c).states ⟨j.1 + 1, by omega⟩,
            ?_, ?_⟩
        · change (capacityScannerTiling x c).1 (capacityEastIndex x) j =
            some ((capacityScannerPath x c).states
              ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
              (capacityScannerPath x c).states ⟨j.1 + 1, by omega⟩)
          rw [capacityScannerTiling_east]
          rfl
        · apply (PakCouplingGenerated.emittedMatches_iff_eq
            MStarULogAssembly.boundaryData _ _ _).mpr
          exact heast_old.symm
    · intro hsouth
      have hj : j = ⟨0, capacitySide_pos x⟩ := by
        apply Fin.ext
        change decide (j.1 = 0) = true at hsouth
        exact decide_eq_true_eq.mp hsouth
      subst j
      refine ⟨PakRippleCanonical.canonicalTiling_south
          (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) i
          (capacitySide_pos x),
        padded_tableau_south_sentinel R.padded i, ?_⟩
      intro heast'
      have hi : i = capacityEastIndex x := by
        apply Fin.ext
        change decide (i.1 + 1 = ConcretePakSide.sideValue x) = true at heast'
        have hival : i.1 + 1 = ConcretePakSide.sideValue x :=
          decide_eq_true_eq.mp heast'
        dsimp [capacityEastIndex]
        omega
      subst i
      refine ⟨(capacityScannerPath x c).states ⟨1, by
        have h := (capacityScannerPath x c).pos
        omega⟩, ?_⟩
      change (capacityScannerTiling x c).1 (capacityEastIndex x)
          ⟨0, capacitySide_pos x⟩ =
        some (PakCouplingGenerated.scannerBottom,
          (capacityScannerPath x c).states ⟨1, by
            have h := (capacityScannerPath x c).pos
            omega⟩)
      rw [capacityScannerTiling_east]
      change some ((capacityScannerPath x c).states _,
        (capacityScannerPath x c).states _) = _
      rw [(capacityScannerPath x c).bottom]
    · intro hnorth
      have hj : j.1 + 1 = ConcretePakSide.sideValue x := by
        change decide (j.1 + 1 = ConcretePakSide.sideValue x) = true at hnorth
        exact decide_eq_true_eq.mp hnorth
      let top : Fin (ConcretePakSide.sideValue x) :=
        ⟨ConcretePakSide.sideValue x - 1, by
          have h := capacitySide_pos x
          omega⟩
      have hjTop : j = top := by
        apply Fin.ext
        dsimp [top]
        omega
      have hsent : PakCouplingGenerated.northSentinel
          MStarULogAssembly.boundaryData Fixed.Machine
          (R.padded.run.tableauTiling.1 i j) := by
        rw [hjTop]
        simpa [top] using padded_tableau_north_sentinel R.padded i
      refine ⟨?_, hsent, ?_⟩
      · simp only [PakCouplingGenerated.ripple]
        have hside : ConcretePakSide.sideValue x - 1 =
            (PakSideScanner.sideScannerBits x).length + 1 := by
          have hheight := PakSideScanner.sideScannerHeight x
          have hbits := PakSideScanner.sideScannerBits_pos x
          omega
        have hpow : i.1 < 2 ^ (ConcretePakSide.sideValue x - 1) := by
          have hi := i.2
          have hbits := PakSideScanner.sideScannerBits_pos x
          have hheight := PakSideScanner.sideScannerHeight x
          have hk : (PakSideScanner.sideScannerBits x).length + 1 <
              2 ^ ((PakSideScanner.sideScannerBits x).length + 1) :=
            Nat.lt_two_pow_self
          calc
            i.1 ≤ ConcretePakSide.sideValue x - 1 := by
              have hp := capacitySide_pos x
              omega
            _ = (PakSideScanner.sideScannerBits x).length + 1 := hside
            _ < 2 ^ ((PakSideScanner.sideScannerBits x).length + 1) := hk
            _ = 2 ^ (ConcretePakSide.sideValue x - 1) := by rw [hside]
        have htest : i.1.testBit (ConcretePakSide.sideValue x - 1) = false :=
          Nat.testBit_eq_false_of_lt hpow
        change (((PakRippleCanonical.canonicalTiling
            (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)).1 i j).1 &&
            ((PakRippleCanonical.canonicalTiling
              (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)).1 i j).2) = false
        simp [Bool.and_eq_false_iff, PakRippleCanonical.canonicalTiling,
          PakRippleCanonical.canonicalCell, PakRippleCanonical.rippleBit,
          PakRippleCanonical.rippleCarry, hjTop, top, htest]
      · intro heast'
        have hi : i = capacityEastIndex x := by
          apply Fin.ext
          change decide (i.1 + 1 = ConcretePakSide.sideValue x) = true at heast'
          have hival : i.1 + 1 = ConcretePakSide.sideValue x :=
            decide_eq_true_eq.mp heast'
          dsimp [capacityEastIndex]
          omega
        subst i
        refine ⟨(capacityScannerPath x c).states
            ⟨ConcretePakSide.sideValue x - 1, by
              have h := capacitySide_pos x
              omega⟩,
            ConcretePakScanner.topNorth, ?_, ?_⟩
        · have hscanTop : (capacityScannerTiling x c).1
              (capacityEastIndex x) top =
              some ((capacityScannerPath x c).states
                ⟨ConcretePakSide.sideValue x - 1, by
                  have h := capacitySide_pos x
                  omega⟩,
                ConcretePakScanner.topNorth) := by
            rw [capacityScannerTiling_east]
            change some ((capacityScannerPath x c).states _,
              (capacityScannerPath x c).states _) = _
            congr 2
            have hnext : (⟨top.1 + 1, by omega⟩ :
                Fin (ConcretePakSide.sideValue x + 1)) =
                ⟨ConcretePakSide.sideValue x, Nat.lt_succ_self _⟩ := by
              apply Fin.ext
              dsimp [top]
              omega
            rw [hnext, (capacityScannerPath x c).top]
          change (capacityScannerTiling x c).1 (capacityEastIndex x) j =
            some ((capacityScannerPath x c).states
              ⟨ConcretePakSide.sideValue x - 1, by
                have h := capacitySide_pos x
                omega⟩,
              ConcretePakScanner.topNorth)
          simpa [hjTop] using hscanTop
        · have hpath := (capacityScannerPath x c).legal top
          have hnext : (⟨top.1 + 1, by omega⟩ :
              Fin (ConcretePakSide.sideValue x + 1)) =
              ⟨ConcretePakSide.sideValue x, Nat.lt_succ_self _⟩ := by
            apply Fin.ext
            dsimp [top]
            omega
          rw [hnext, (capacityScannerPath x c).top] at hpath
          have hlegal : ConcretePakScanner.LegalScan
              ((capacityScannerPath x c).states
                ⟨ConcretePakSide.sideValue x - 1, by
                  have h := capacitySide_pos x
                  omega⟩)
              ConcretePakScanner.topNorth
              ((ConcretePakSide.sideValue x).testBit (ConcretePakSide.sideValue x - 1)) := by
            simpa [top] using hpath
          exact legal_to_top_scannerTopSouth _ _ hlegal
    · intro hnonEast
      change decide (i.1 + 1 = ConcretePakSide.sideValue x) = false at hnonEast
      have hne : ¬ i.1 + 1 = ConcretePakSide.sideValue x :=
        decide_eq_false_iff_not.mp hnonEast
      have hlt : i.1 + 1 < ConcretePakSide.sideValue x := by omega
      have hnone := ScannerPath.toEastTiling_nonEast (capacityScannerPath x c)
        i j hlt
      simpa [PakRippleCanonical.canonicalFullAmpTiling,
        PakRippleCanonical.canonicalFullAmpCell, capacityScannerTiling,
        PakCouplingGenerated.amp, PakCouplingGenerated.ripple,
        PakCouplingGenerated.tableau, PakCouplingGenerated.scan] using hnone
  west_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_west Fixed.Q
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)
      (capacitySide_pos x) j
  east_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_east Fixed.Q
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x)
      (capacitySide_pos x) j
  south_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_south Fixed.Q
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) i
      (by have h := capacitySide_ge_three x; omega)
  north_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_north Fixed.Q
      (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) i
      (by have h := capacitySide_ge_three x; omega)

/-- The literal square full frame obtained from a run satisfying the
capacity-indexed east-emission contract. -/
noncomputable def capacitySquareFullFrame (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (R : CapacitySquarePaddedRun x c) :
    FullFrame (ConcretePakSide.sideValue x) (ConcretePakSide.sideValue x) :=
  (capacitySquareFullTrackCertificate x c R).toFullFrame

end PakFixedPolyomino.PakGeneralCapacityFullFrameForward
