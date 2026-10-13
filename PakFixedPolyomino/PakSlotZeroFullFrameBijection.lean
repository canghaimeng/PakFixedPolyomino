import PakFixedPolyomino.PakScannerBaselineAutomaton
import PakFixedPolyomino.PakFullFrameFirstBranch
import PakFixedPolyomino.PakFullFrameTableauRoundtrip
import PakFixedPolyomino.PakFullFrameForward

/-! # Slot-zero full-frame readback -/

namespace PakFixedPolyomino.PakSlotZeroFullFrameBijection

open PakMStarCouplingCorrectness
open PakScannerBaselineAutomaton
open PakFullFrameTableauReadback

abbrev SlotZeroFullFrame (n : ℕ) :=
  {F : FullFrame n n //
    ((FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 0}

theorem scannerProjection_eq_of_same_path {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G) :
    scannerProjection F.tiling = scannerProjection G.tiling := by
  have hF :=
    (PakScannerBaselineAutomaton.FullFrame.scannerColumnReadback F).tiling_eq_pathTiling
  have hG :=
    (PakScannerBaselineAutomaton.FullFrame.scannerColumnReadback G).tiling_eq_pathTiling
  change scannerProjection F.tiling =
      (FullFrame.toScannerPath F).toEastTiling at hF
  change scannerProjection G.tiling =
      (FullFrame.toScannerPath G).toEastTiling at hG
  rw [hF, hG, hpath]

theorem slotZero_scannerProjection_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1) :
    scannerProjection F.1.tiling = scannerProjection G.1.tiling :=
  scannerProjection_eq_of_same_path F.1 G.1 hpath

/-- A scanner-path equality fixes the emitted east old window row by row.
This is the concrete bridge from the finite scanner automaton to the first
operational configuration of the tableau readback. -/
theorem east_oldStrip_eq_of_same_path {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G)
    (j : Fin n) :
    (tableauAt F.tiling (eastIndex F.width_pos) j).1.old =
      (tableauAt G.tiling (eastIndex G.width_pos) j).1.old := by
  have hscanner := congrFun (congrFun
    (congrArg Subtype.val (scannerProjection_eq_of_same_path F G hpath))
    (eastIndex F.width_pos)) j
  have heast : eastIndex F.width_pos = eastIndex G.width_pos := by
    apply Fin.ext
    simp [eastIndex]
  rw [heast] at hscanner
  change scannerAt F.tiling (eastIndex F.width_pos) j =
    scannerAt G.tiling (eastIndex G.width_pos) j at hscanner
  rcases F.east_emits_tableau_window j with ⟨sF, tF, hsF, holdF⟩
  rcases G.east_emits_tableau_window j with ⟨sG, tG, hsG, holdG⟩
  have hpairs : (sF, tF) = (sG, tG) := by
    apply Option.some.inj
    exact hsF.symm.trans (hscanner.trans hsG)
  calc
    (tableauAt F.tiling (eastIndex F.width_pos) j).1.old =
        PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData sF tF := holdF
    _ = PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData sG tG := by
        cases hpairs
        rfl
    _ = (tableauAt G.tiling (eastIndex G.width_pos) j).1.old := holdG.symm

private theorem mstarConfig_ext (c d : MStarConfig)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp only at hstate hhead htape
  subst_vars
  rfl

private theorem headSourceOf_fst_eq_of_eq
    {x y : TableauCell Fixed.State Fixed.Tape}
    (hx : x.isHead = true) (hy : y.isHead = true) (hxy : x = y) :
    (x.headSourceOf hx).1 = (y.headSourceOf hy).1 := by
  subst y
  rfl

/-- Equal scanner paths determine the complete first readback configuration,
not merely its control state: the east emitted old strips determine the
unique head, every tape letter, and hence the readback `before` record. -/
theorem east_before_eq_of_same_path {n : ℕ}
    (F G : FullFrame n n)
    (hpath : FullFrame.toScannerPath F = FullFrame.toScannerPath G) :
    (FullFrame.toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ n⟩ =
      (FullFrame.toUniformWindowedRun G).config ⟨0, Nat.zero_lt_succ n⟩ := by
  let RF := FullFrame.tableau_column_readback F (eastIndex F.width_pos)
  let RG := FullFrame.tableau_column_readback G (eastIndex G.width_pos)
  have hstrip : ∀ j : Fin n, RF.oldStrip j = RG.oldStrip j := by
    intro j
    simpa [RF, RG] using east_oldStrip_eq_of_same_path F G hpath j
  have hFhead : (RG.oldStrip RF.head).center.isHead = true := by
    rw [← hstrip RF.head]
    exact RF.head_is_head
  have hheads : RF.head = RG.head := RG.head_unique RF.head hFhead
  have htape : RF.oldTape = RG.oldTape := by
    funext z
    by_cases hz : 0 ≤ z ∧ z < (n : Int)
    · let j : Fin n := ⟨z.toNat, by omega⟩
      have hzj : (j.1 : Int) = z := by
        dsimp [j]
        exact Int.toNat_of_nonneg hz.1
      rw [← hzj, RF.oldTape_at j, RG.oldTape_at j, hstrip j]
    · have hz' : z < 0 ∨ (n : Int) ≤ z := by omega
      rw [RF.oldTape_hash_outside z hz', RG.oldTape_hash_outside z hz']
  have hstate : RF.before.state = RG.before.state := by
    change ((RF.oldStrip RF.head).center.headSourceOf RF.head_is_head).1 =
      ((RG.oldStrip RG.head).center.headSourceOf RG.head_is_head).1
    have hcell : (RF.oldStrip RF.head).center =
        (RG.oldStrip RG.head).center := by
      simpa [hheads] using congrArg CellTriple.center (hstrip RF.head)
    exact headSourceOf_fst_eq_of_eq RF.head_is_head RG.head_is_head hcell
  have hhead : RF.before.head = RG.before.head := by
    change (RF.head.1 : Int) = RG.head.1
    rw [hheads]
  have hbefore : RF.before = RG.before :=
    mstarConfig_ext RF.before RG.before hstate hhead htape
  have hF0 := PakFullFrameTableauRoundtrip.reverse_tableau_config_before F
    (⟨0, F.width_pos⟩ : Fin n)
  have hG0 := PakFullFrameTableauRoundtrip.reverse_tableau_config_before G
    (⟨0, G.width_pos⟩ : Fin n)
  change FullFrame.reverse_tableau_config F ⟨0, Nat.zero_lt_succ n⟩ =
    FullFrame.reverse_tableau_config G ⟨0, Nat.zero_lt_succ n⟩
  rw [hF0, hG0]
  simpa [RF, RG, reverseColumn, eastIndex] using hbefore

theorem slotZero_first_arrow_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1) :
    (FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩ =
      (FullFrame.toUniformWindowedRun G.1).arrow ⟨0, G.1.width_pos⟩ := by
  let RF := FullFrame.toUniformWindowedRun F.1
  let RG := FullFrame.toUniformWindowedRun G.1
  let tF : Fin n := ⟨0, F.1.width_pos⟩
  let tG : Fin n := ⟨0, G.1.width_pos⟩
  have hbefore := east_before_eq_of_same_path F.1 G.1 hpath
  have hFstep := RF.step tF
  have hGstep := RG.step tG
  apply PakFullFrameTableauReadback.arrow_eq_of_successful_steps_same_slot
    (RF.config ⟨0, Nat.zero_lt_succ n⟩)
    (RF.config ⟨1, by have := F.1.width_pos; omega⟩)
    (RG.config ⟨1, by have := G.1.width_pos; omega⟩)
  · simpa [RF, tF] using hFstep
  · rw [hbefore]
    simpa [RG, tG] using hGstep
  · exact F.2.trans G.2.symm

theorem slotZero_config_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1)
    (k : Fin (n + 1)) :
    (FullFrame.toUniformWindowedRun F.1).config k =
      (FullFrame.toUniformWindowedRun G.1).config k := by
  let RF := FullFrame.toUniformWindowedRun F.1
  let RG := FullFrame.toUniformWindowedRun G.1
  have hzero := east_before_eq_of_same_path F.1 G.1 hpath
  have harrow := slotZero_first_arrow_eq_of_same_path F G hpath
  have hfirst : RF.config ⟨1, by have := F.1.width_pos; omega⟩ =
      RG.config ⟨1, by have := G.1.width_pos; omega⟩ := by
    have hF := RF.step ⟨0, F.1.width_pos⟩
    have hG := RG.step ⟨0, G.1.width_pos⟩
    apply FiniteOneTapeSemantics.step_label_deterministic
      MStarULogAssembly.program MStarOuterProgram.movable
      (RF.config ⟨0, Nat.zero_lt_succ n⟩) _ _ (RF.arrow ⟨0, F.1.width_pos⟩)
    · simpa using hF
    · rw [hzero, harrow]
      simpa using hG
  by_cases hk0 : k.1 = 0
  · have hk : k = ⟨0, Nat.zero_lt_succ n⟩ := Fin.eq_of_val_eq hk0
    rw [hk]
    exact hzero
  · let m : ℕ := k.1 - 1
    have hm : m + 1 < n + 1 := by
      dsimp [m]
      omega
    have hk : k = ⟨m + 1, hm⟩ := by
      apply Fin.ext
      dsimp [m]
      omega
    rw [hk]
    calc
      RF.config ⟨m + 1, hm⟩ = RF.config ⟨1, by omega⟩ :=
        PakFullFrameTableauReadback.FullFrame.slotZero_config_succ_eq_first_accept F.1 F.2 m hm
      _ = RG.config ⟨1, by omega⟩ := hfirst
      _ = RG.config ⟨m + 1, hm⟩ :=
        (PakFullFrameTableauReadback.FullFrame.slotZero_config_succ_eq_first_accept G.1 G.2 m hm).symm

theorem slotZero_arrow_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1)
    (t : Fin n) :
    (FullFrame.toUniformWindowedRun F.1).arrow t =
      (FullFrame.toUniformWindowedRun G.1).arrow t := by
  let RF := FullFrame.toUniformWindowedRun F.1
  let RG := FullFrame.toUniformWindowedRun G.1
  by_cases ht0 : t.1 = 0
  · have htF : t = ⟨0, F.1.width_pos⟩ := Fin.eq_of_val_eq ht0
    rw [htF]
    exact slotZero_first_arrow_eq_of_same_path F G hpath
  · have hcfg := slotZero_config_eq_of_same_path F G hpath
      ⟨t.1, Nat.lt_succ_of_lt t.2⟩
    have hacceptF : (RF.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩).state =
        MStarOuterProgram.State.accept := by
      have hfirst := PakFullFrameTableauReadback.FullFrame.slotZero_first_target_accept F.1 F.2
      have hconst := PakFullFrameTableauReadback.FullFrame.slotZero_config_succ_eq_first_accept
        F.1 F.2 (t.1 - 1) (by omega)
      have htval : t.1 = (t.1 - 1) + 1 := by omega
      have htFin : (⟨t.1, Nat.lt_succ_of_lt t.2⟩ : Fin (n + 1)) =
          ⟨(t.1 - 1) + 1, by omega⟩ := Fin.ext htval
      rw [htFin, hconst]
      exact hfirst
    have hFstep := RF.step t
    have hGstep := RG.step t
    have hslotF := PakFullFrameTableauReadback.accept_successful_arrow_slot_zero
      (RF.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩)
      (RF.config ⟨t.1 + 1, by omega⟩) (RF.arrow t) hacceptF hFstep
    have hacceptG : (RG.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩).state =
        MStarOuterProgram.State.accept := by rw [← hcfg]; exact hacceptF
    have hslotG := PakFullFrameTableauReadback.accept_successful_arrow_slot_zero
      (RG.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩)
      (RG.config ⟨t.1 + 1, by omega⟩) (RG.arrow t) hacceptG hGstep
    apply PakFullFrameTableauReadback.arrow_eq_of_successful_steps_same_slot
      (RF.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩)
      (RF.config ⟨t.1 + 1, by omega⟩)
      (RG.config ⟨t.1 + 1, by omega⟩)
    · exact hFstep
    · rw [hcfg]
      exact hGstep
    · exact hslotF.trans hslotG.symm

theorem slotZero_headIndex_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1)
    (k : Fin (n + 1)) :
    (FullFrame.toUniformWindowedRun F.1).head_index k =
      (FullFrame.toUniformWindowedRun G.1).head_index k := by
  let RF := FullFrame.toUniformWindowedRun F.1
  let RG := FullFrame.toUniformWindowedRun G.1
  have hcfg := slotZero_config_eq_of_same_path F G hpath k
  have hF := RF.head_eq k
  have hG := RG.head_eq k
  apply Fin.ext
  change (RF.head_index k).1 = (RG.head_index k).1
  rw [hcfg] at hF
  change (RG.config k).head = 0 + (RF.head_index k).1 at hF
  change (RG.config k).head = 0 + (RG.head_index k).1 at hG
  omega

private theorem uniformRun_ext
    (R S : UniformWindowedMStarRun n n)
    (hconfig : R.config = S.config) (harrow : R.arrow = S.arrow)
    (horigin : R.origin = S.origin) (hhead : R.head_index = S.head_index) :
    R = S := by
  cases R
  cases S
  simp only at hconfig harrow horigin hhead ⊢
  subst_vars
  rfl

theorem slotZero_tableauTiling_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1) :
    (FullFrame.toUniformWindowedRun F.1).tableauTiling =
      (FullFrame.toUniformWindowedRun G.1).tableauTiling := by
  let RF := FullFrame.toUniformWindowedRun F.1
  let RG := FullFrame.toUniformWindowedRun G.1
  have hcfg : RF.config = RG.config := by
    funext k
    exact slotZero_config_eq_of_same_path F G hpath k
  have harrow : RF.arrow = RG.arrow := by
    funext k
    exact slotZero_arrow_eq_of_same_path F G hpath k
  have hhead : RF.head_index = RG.head_index := by
    funext k
    exact slotZero_headIndex_eq_of_same_path F G hpath k
  have horigin : RF.origin = RG.origin := rfl
  exact congrArg UniformWindowedMStarRun.tableauTiling
    (uniformRun_ext RF RG hcfg harrow horigin hhead)

/-- For the fixed construction `Q = 1`, the four-side amplifier has no
colour freedom.  Its activity bits are forced by the dead colours and the
literal four-side boundary of a full frame. -/
theorem FullFrame.amplifier_cell_eq_canonical {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    ampAt F.tiling i j =
      PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j := by
  have hwest : (ampAt F.tiling i j).1.westActive = decide (i.1 = 0) := by
    by_cases hi : i.1 = 0
    · have hi' : i = ⟨0, F.width_pos⟩ := Fin.ext hi
      rw [hi']
      simp [F.boundary.1 j]
    · have hf : (ampAt F.tiling i j).1.westActive = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        exact hi (westActive_on_west_boundary F.tiling i j ht)
      simp [hi, hf]
  have heast : (ampAt F.tiling i j).1.eastActive =
      decide (i.1 + 1 = w) := by
    by_cases hi : i.1 + 1 = w
    · have hi' : i = eastIndex F.width_pos := by
        apply Fin.ext
        simp [eastIndex]
        omega
      rw [hi']
      have hlast : (eastIndex F.width_pos).1 + 1 = w := by
        simp [eastIndex]
        omega
      simp [F.boundary.2.1 j, hlast]
    · have hf : (ampAt F.tiling i j).1.eastActive = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        exact hi (eastActive_on_east_boundary F.tiling i j ht)
      simp [hi, hf]
  have hsouth : (ampAt F.tiling i j).1.southActive = decide (j.1 = 0) := by
    by_cases hj : j.1 = 0
    · have hj' : j = ⟨0, F.height_pos⟩ := Fin.ext hj
      rw [hj']
      simp [F.boundary.2.2.1 i]
    · have hf : (ampAt F.tiling i j).1.southActive = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        exact hj (southActive_on_south_boundary F.tiling i j ht)
      simp [hj, hf]
  have hnorth : (ampAt F.tiling i j).1.northActive =
      decide (j.1 + 1 = h) := by
    by_cases hj : j.1 + 1 = h
    · have hj' : j = northIndex F.height_pos := by
        apply Fin.ext
        simp [northIndex]
        omega
      rw [hj']
      have hlast : (northIndex F.height_pos).1 + 1 = h := by
        simp [northIndex]
        omega
      simp [F.boundary.2.2.2 i, hlast]
    · have hf : (ampAt F.tiling i j).1.northActive = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        exact hj (northActive_on_north_boundary F.tiling i j ht)
      simp [hj, hf]
  apply Subtype.ext
  apply AmpRaw.ext
  · exact hwest
  · exact heast
  · exact hsouth
  · exact hnorth
  · apply Fin.ext
    have ha := (ampAt F.tiling i j).1.qWest.2
    have hb := (PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j).1.qWest.2
    change _ < 1 at ha hb
    omega
  · apply Fin.ext
    have ha := (ampAt F.tiling i j).1.qEast.2
    have hb := (PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j).1.qEast.2
    change _ < 1 at ha hb
    omega
  · apply Fin.ext
    have ha := (ampAt F.tiling i j).1.qSouth.2
    have hb := (PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j).1.qSouth.2
    change _ < 1 at ha hb
    omega
  · apply Fin.ext
    have ha := (ampAt F.tiling i j).1.qNorth.2
    have hb := (PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j).1.qNorth.2
    change _ < 1 at ha hb
    omega

theorem FullFrame.amplifierProjection_eq_canonical {w h : ℕ}
    (F : FullFrame w h) :
    amplifierProjection F.tiling =
      PakRippleCanonical.canonicalFullAmpTiling Fixed.Q w h := by
  apply Subtype.ext
  funext i j
  change ampAt F.tiling i j =
    PakRippleCanonical.canonicalFullAmpCell Fixed.Q w h i j
  exact FullFrame.amplifier_cell_eq_canonical F i j

theorem amplifierProjection_eq_of_fullFrames {n : ℕ}
    (F G : FullFrame n n) :
    amplifierProjection F.tiling = amplifierProjection G.tiling :=
  (FullFrame.amplifierProjection_eq_canonical F).trans
    (FullFrame.amplifierProjection_eq_canonical G).symm

theorem rippleProjection_eq_of_fullFrames {n : ℕ}
    (F G : FullFrame n n) :
    rippleProjection F.tiling = rippleProjection G.tiling :=
  (PakFullFrameRippleClassify.FullFrame.rippleProjection_eq_canonical F).trans
    (PakFullFrameRippleClassify.FullFrame.rippleProjection_eq_canonical G).symm

theorem slotZero_fullFrame_eq_of_same_path {n : ℕ}
    (F G : SlotZeroFullFrame n)
    (hpath : FullFrame.toScannerPath F.1 = FullFrame.toScannerPath G.1) :
    F.1 = G.1 := by
  have hrun := slotZero_tableauTiling_eq_of_same_path F G hpath
  have htableau : tableauProjection F.1.tiling = tableauProjection G.1.tiling := by
    calc
      tableauProjection F.1.tiling =
          (FullFrame.toUniformWindowedRun F.1).tableauTiling :=
            PakFullFrameTableauRoundtrip.FullFrame.tableauProjection_eq_roundtrip F.1
      _ = (FullFrame.toUniformWindowedRun G.1).tableauTiling := hrun
      _ = tableauProjection G.1.tiling :=
            (PakFullFrameTableauRoundtrip.FullFrame.tableauProjection_eq_roundtrip G.1).symm
  apply FullFrame.ext
  apply coupledTiling_ext_of_projections
  · exact amplifierProjection_eq_of_fullFrames F.1 G.1
  · exact rippleProjection_eq_of_fullFrames F.1 G.1
  · exact htableau
  · exact slotZero_scannerProjection_eq_of_same_path F G hpath

noncomputable def slotZeroToHeadedScannerPath {n : ℕ}
    (F : SlotZeroFullFrame n) : HeadedScannerPath n :=
  FullFrame.toHeadedScannerPath F.1

theorem slotZeroToHeadedScannerPath_injective {n : ℕ} :
    Function.Injective (slotZeroToHeadedScannerPath (n := n)) := by
  intro F G hFG
  apply Subtype.ext
  apply slotZero_fullFrame_eq_of_same_path F G
  exact congrArg Subtype.val hFG

/-- The literal east tableau window emitted by an abstract scanner path.
Unlike a frame readback this is defined directly from the path states and has
no hidden tableau or full-frame certificate. -/
def HeadedScannerPath.emittedOldStrip {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n) : CellTriple (TableauCell Fixed.State Fixed.Tape) :=
  PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
    (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    (P.1.states ⟨j.1 + 1, by omega⟩)

theorem headedPath_head_exists {n : ℕ} (P : HeadedScannerPath n) :
    ∃ j : Fin n,
      (HeadedScannerPath.emittedOldStrip P j).center.isHead = true := by
  by_contra hnone
  push Not at hnone
  have hzero : P.1.headCount = 0 := by
    unfold ScannerPath.headCount
    apply Finset.sum_eq_zero
    intro j _
    have hbuf : isHeadBuffer
        (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      have hc := (PakScannerBaselineAutomaton.isHeadBuffer_iff_bufferCell_isHead
        (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre).1 htrue
      have hcell : (HeadedScannerPath.emittedOldStrip P j).center.isHead = true := by
        simpa [HeadedScannerPath.emittedOldStrip,
          PakCouplingGenerated.emittedWindow] using hc
      exact hnone j hcell
    simp [hbuf]
  omega

noncomputable def HeadedScannerPath.headIndex {n : ℕ}
    (P : HeadedScannerPath n) : Fin n :=
  Classical.choose (headedPath_head_exists P)

theorem HeadedScannerPath.headIndex_isHead {n : ℕ}
    (P : HeadedScannerPath n) :
    (HeadedScannerPath.emittedOldStrip P (HeadedScannerPath.headIndex P)).center.isHead = true :=
  Classical.choose_spec (headedPath_head_exists P)

/-- The finite tape read directly from emitted centre cells, with literal hash
outside the scanner height. -/
noncomputable def HeadedScannerPath.initialTape {n : ℕ}
    (P : HeadedScannerPath n) (z : Int) : Fixed.Tape :=
  if hz : 0 ≤ z ∧ z < (n : Int) then
    OneTapeTableau.cellLetter
      (HeadedScannerPath.emittedOldStrip P ⟨z.toNat, by omega⟩).center
  else MStarOuterProgram.Tape.hash

noncomputable def HeadedScannerPath.initialConfig {n : ℕ}
    (P : HeadedScannerPath n) : MStarConfig where
  state := MStarOuterProgram.State.start
  head := (HeadedScannerPath.headIndex P).1
  tape := HeadedScannerPath.initialTape P

theorem HeadedScannerPath.initialTape_at {n : ℕ}
    (P : HeadedScannerPath n) (j : Fin n) :
    HeadedScannerPath.initialTape P j.1 =
      OneTapeTableau.cellLetter (HeadedScannerPath.emittedOldStrip P j).center := by
  unfold HeadedScannerPath.initialTape
  have hj : 0 ≤ (j.1 : Int) ∧ (j.1 : Int) < (n : Int) := by omega
  rw [dif_pos hj]
  congr

theorem HeadedScannerPath.initialTape_hash_outside {n : ℕ}
    (P : HeadedScannerPath n) (z : Int) (hz : z < 0 ∨ (n : Int) ≤ z) :
    HeadedScannerPath.initialTape P z = MStarOuterProgram.Tape.hash := by
  unfold HeadedScannerPath.initialTape
  apply dif_neg
  omega

theorem HeadedScannerPath.headIndex_unique {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n)
    (hj : (HeadedScannerPath.emittedOldStrip P j).center.isHead = true) :
    j = HeadedScannerPath.headIndex P := by
  classical
  let f : Fin n → ℕ := fun k =>
    if isHeadBuffer
      (P.1.states ⟨k.1, Nat.lt_succ_of_lt k.2⟩).centre then 1 else 0
  have hh : f (HeadedScannerPath.headIndex P) = 1 := by
    have hh' : isHeadBuffer
        (P.1.states ⟨(HeadedScannerPath.headIndex P).1,
          Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩).centre = true := by
      rw [isHeadBuffer_iff_bufferCell_isHead]
      simpa [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow] using
          HeadedScannerPath.headIndex_isHead P
    simp [f, hh']
  have hj' : f j = 1 := by
    have hjbuf : isHeadBuffer
        (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre = true := by
      rw [isHeadBuffer_iff_bufferCell_isHead]
      simpa [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow] using hj
    simp [f, hjbuf]
  by_contra hne
  have hsum : ∑ k : Fin n, f k = 1 := by
    simpa [ScannerPath.headCount, f] using P.2
  rw [← Finset.add_sum_erase _ _
    (Finset.mem_univ (HeadedScannerPath.headIndex P))] at hsum
  rw [hh] at hsum
  have hzero : ∑ k ∈ (Finset.univ : Finset (Fin n)).erase
      (HeadedScannerPath.headIndex P), f k = 0 := by omega
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase
      (HeadedScannerPath.headIndex P) := by simp [hne]
  have hjzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp hzero j hjmem
  omega

noncomputable def HeadedScannerPath.initialCell {n : ℕ} (P : HeadedScannerPath n)
    (z : Int) : TableauCell Fixed.State Fixed.Tape :=
  if z = (HeadedScannerPath.initialConfig P).head then
    .head (HeadedScannerPath.initialConfig P).state
      ((HeadedScannerPath.initialConfig P).tape z)
  else .plain ((HeadedScannerPath.initialConfig P).tape z)

theorem HeadedScannerPath.initialCell_at {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n) :
    HeadedScannerPath.initialCell P j.1 =
      (HeadedScannerPath.emittedOldStrip P j).center := by
  have htape := HeadedScannerPath.initialTape_at P j
  have hhead := HeadedScannerPath.headIndex_isHead P
  have hstate : (HeadedScannerPath.initialConfig P).state =
      MStarOuterProgram.State.start := rfl
  have hheadpos : (HeadedScannerPath.initialConfig P).head =
      (HeadedScannerPath.headIndex P).1 := rfl
  rw [HeadedScannerPath.initialCell, hstate, hheadpos]
  change (if (j.1 : Int) = (HeadedScannerPath.headIndex P).1 then
      TableauCell.head MStarOuterProgram.State.start
        (HeadedScannerPath.initialTape P j.1)
    else TableauCell.plain (HeadedScannerPath.initialTape P j.1)) = _
  rw [htape]
  by_cases hj : j = HeadedScannerPath.headIndex P
  · have hjval : (j.1 : Int) = (HeadedScannerPath.headIndex P).1 := by
      exact_mod_cast congrArg Fin.val hj
    rw [if_pos hjval]
    cases hc : (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre <;>
      simp_all [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow, PakCouplingGenerated.bufferCell,
        OneTapeTableau.cellLetter, TableauCell.isHead,
        MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]
  · have hjval : (j.1 : Int) ≠ (HeadedScannerPath.headIndex P).1 := by
      intro h
      exact hj (Fin.ext (by exact_mod_cast h))
    rw [if_neg hjval]
    have hnot :
        (HeadedScannerPath.emittedOldStrip P j).center.isHead ≠ true := by
      intro h
      exact hj (HeadedScannerPath.headIndex_unique P j h)
    cases hc : (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre <;>
      simp_all [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow, PakCouplingGenerated.bufferCell,
        OneTapeTableau.cellLetter, TableauCell.isHead,
        MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]

theorem HeadedScannerPath.initialCell_minus {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n) :
    HeadedScannerPath.initialCell P ((j.1 : Int) - 1) =
      (HeadedScannerPath.emittedOldStrip P j).minus := by
  by_cases hj : j.1 = 0
  · have hb := P.1.bottom
    have hs : P.1.states (0 : Fin (n + 1)) =
        PakCouplingGenerated.scannerBottom := by simpa using hb
    have hz : (j.1 : Int) - 1 = -1 := by omega
    rw [hz]
    have hout := HeadedScannerPath.initialTape_hash_outside P (-1) (by left; omega)
    have hhead : (-1 : Int) ≠ (HeadedScannerPath.headIndex P).1 := by omega
    rw [HeadedScannerPath.initialCell]
    change (if (-1 : Int) = (HeadedScannerPath.headIndex P).1 then _ else _) = _
    rw [if_neg hhead]
    change TableauCell.plain (HeadedScannerPath.initialTape P (-1)) = _
    rw [hout]
    change TableauCell.plain MStarOuterProgram.Tape.hash =
      PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData
        (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).left
    rw [show (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (n + 1)) = 0 by
      apply Fin.ext; exact hj, hs]
    rfl
  · let k : Fin n := ⟨j.1 - 1, by omega⟩
    have hkval : (k.1 : Int) = (j.1 : Int) - 1 := by
      dsimp [k]
      omega
    have hcell := HeadedScannerPath.initialCell_at P k
    rw [← hkval]
    rw [hcell]
    have hlegal := P.1.legal k
    have hnext : (⟨k.1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩ := by
      apply Fin.ext
      dsimp [k]
      omega
    have hshift := ConcretePakScanner.legalScan_shift hlegal
    rw [hnext] at hshift
    change PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData
        (P.1.states ⟨k.1, Nat.lt_succ_of_lt k.2⟩).centre =
      PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData
        (P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).left
    unfold ConcretePakScanner.Shift at hshift
    exact congrArg (PakCouplingGenerated.bufferCell
      MStarULogAssembly.boundaryData) hshift.symm

theorem HeadedScannerPath.initialCell_plus {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n) :
    HeadedScannerPath.initialCell P ((j.1 : Int) + 1) =
      (HeadedScannerPath.emittedOldStrip P j).plus := by
  by_cases hj : j.1 + 1 < n
  · let k : Fin n := ⟨j.1 + 1, hj⟩
    have hkval : (k.1 : Int) = (j.1 : Int) + 1 := by rfl
    have hcell := HeadedScannerPath.initialCell_at P k
    rw [← hkval]
    rw [hcell]
    rfl
  · have hlast : j.1 + 1 = n := by omega
    have htop := P.1.top
    have hnext : (⟨j.1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hlast
    have hout := HeadedScannerPath.initialTape_hash_outside P
      ((j.1 : Int) + 1) (by right; exact_mod_cast hlast.ge)
    have hne : (j.1 : Int) + 1 ≠ (HeadedScannerPath.headIndex P).1 := by
      intro heq
      have : j.1 + 1 = (HeadedScannerPath.headIndex P).1 := by exact_mod_cast heq
      have hlt := (HeadedScannerPath.headIndex P).2
      omega
    rw [HeadedScannerPath.initialCell]
    change (if (j.1 : Int) + 1 = (HeadedScannerPath.headIndex P).1 then _ else _) = _
    rw [if_neg hne]
    change TableauCell.plain (HeadedScannerPath.initialTape P ((j.1 : Int) + 1)) = _
    rw [hout]
    simp [HeadedScannerPath.emittedOldStrip, PakCouplingGenerated.emittedWindow,
      hnext, htop, ConcretePakScanner.topNorth,
      PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
theorem HeadedScannerPath.initialConfig_head {n : ℕ}
    (P : HeadedScannerPath n) :
    (HeadedScannerPath.initialConfig P).head = (HeadedScannerPath.headIndex P).1 := rfl

theorem HeadedScannerPath.initialConfig_state {n : ℕ}
    (P : HeadedScannerPath n) :
    (HeadedScannerPath.initialConfig P).state = MStarOuterProgram.State.start := rfl

theorem HeadedScannerPath.headBuffer_is_headZero_or_headOne {n : ℕ}
    (P : HeadedScannerPath n) :
    (P.1.states ⟨(HeadedScannerPath.headIndex P).1,
      Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩).centre =
        .headZero ∨
      (P.1.states ⟨(HeadedScannerPath.headIndex P).1,
        Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩).centre =
        .headOne := by
  have hh := HeadedScannerPath.headIndex_isHead P
  unfold HeadedScannerPath.emittedOldStrip PakCouplingGenerated.emittedWindow at hh
  cases hc : (P.1.states ⟨(HeadedScannerPath.headIndex P).1,
      Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩).centre <;>
    simp [hc, PakCouplingGenerated.bufferCell, TableauCell.isHead] at hh ⊢

theorem HeadedScannerPath.initialTape_head_is_initial {n : ℕ}
    (P : HeadedScannerPath n) :
    MStarOuterProgram.isInitialLetter MStarULogAssembly.data
      (match HeadedScannerPath.initialTape P (HeadedScannerPath.initialConfig P).head with
      | .core a => a
      | _ => MStarULogAssembly.data.zero) = true ∧
    ∃ a, HeadedScannerPath.initialTape P (HeadedScannerPath.initialConfig P).head =
      MStarOuterProgram.Tape.core a := by
  have hbuf := HeadedScannerPath.headBuffer_is_headZero_or_headOne P
  have htape := HeadedScannerPath.initialTape_at P (HeadedScannerPath.headIndex P)
  change MStarOuterProgram.isInitialLetter MStarULogAssembly.data
      (match HeadedScannerPath.initialTape P (HeadedScannerPath.headIndex P).1 with
      | .core a => a
      | _ => MStarULogAssembly.data.zero) = true ∧
    ∃ a, HeadedScannerPath.initialTape P (HeadedScannerPath.headIndex P).1 =
      MStarOuterProgram.Tape.core a
  rcases hbuf with hbuf | hbuf
  · have htape0 : HeadedScannerPath.initialTape P
        (HeadedScannerPath.headIndex P).1 =
        MStarOuterProgram.Tape.core MStarULogAssembly.data.zero := by
      rw [htape]
      simp [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow, hbuf,
        PakCouplingGenerated.bufferCell, OneTapeTableau.cellLetter,
        MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]
    rw [htape0]
    exact ⟨decide_eq_true_eq.mpr (Or.inl rfl),
      ⟨MStarULogAssembly.data.zero, rfl⟩⟩
  · have htape1 : HeadedScannerPath.initialTape P
        (HeadedScannerPath.headIndex P).1 =
        MStarOuterProgram.Tape.core MStarULogAssembly.data.one := by
      rw [htape]
      simp [HeadedScannerPath.emittedOldStrip,
        PakCouplingGenerated.emittedWindow, hbuf,
        PakCouplingGenerated.bufferCell, OneTapeTableau.cellLetter,
        MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]
    rw [htape1]
    exact ⟨decide_eq_true_eq.mpr (Or.inr (Or.inl rfl)),
      ⟨MStarULogAssembly.data.one, rfl⟩⟩

noncomputable def HeadedScannerPath.initialCore {n : ℕ}
    (P : HeadedScannerPath n) : MStarULogAssembly.CoreTape :=
  Classical.choose (HeadedScannerPath.initialTape_head_is_initial P).2

theorem HeadedScannerPath.initialTape_head_eq_core {n : ℕ}
    (P : HeadedScannerPath n) :
    HeadedScannerPath.initialTape P (HeadedScannerPath.initialConfig P).head =
      MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P) :=
  Classical.choose_spec (HeadedScannerPath.initialTape_head_is_initial P).2

theorem HeadedScannerPath.initialCore_isInitial {n : ℕ}
    (P : HeadedScannerPath n) :
    MStarOuterProgram.isInitialLetter MStarULogAssembly.data
      (HeadedScannerPath.initialCore P) = true := by
  have h := (HeadedScannerPath.initialTape_head_is_initial P).1
  simpa [HeadedScannerPath.initialTape_head_eq_core P] using h

noncomputable def HeadedScannerPath.startArrow {n : ℕ}
    (P : HeadedScannerPath n) : Fixed.Arrow := by
  refine ⟨((MStarOuterProgram.State.start,
    MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)), (0 : Fin 2)), ?_⟩
  have hrule := MStarOuterProgram.start_slot_zero MStarULogAssembly.data
    (HeadedScannerPath.initialCore_isInitial P)
  intro hnone
  rw [hrule] at hnone
  contradiction

noncomputable def HeadedScannerPath.acceptConfig {n : ℕ}
    (P : HeadedScannerPath n) : MStarConfig where
  state := MStarOuterProgram.State.accept
  head := (HeadedScannerPath.initialConfig P).head
  tape := (HeadedScannerPath.initialConfig P).tape

theorem HeadedScannerPath.acceptConfig_eq_written {n : ℕ}
    (P : HeadedScannerPath n) :
    HeadedScannerPath.acceptConfig P =
      { state := MStarOuterProgram.State.accept,
        head := (HeadedScannerPath.initialConfig P).head,
        tape := (HeadedScannerPath.initialConfig P).tape } := rfl

private theorem actionOf_eq_of_rule_eq
    {State Tape : Type*} [Fintype State] [Fintype Tape]
    [DecidableEq State] [DecidableEq Tape]
    (Q : FiniteOneTapeProgram.Program State Tape)
    (a : FiniteOneTapeProgram.Arrow Q)
    (act : FiniteOneTapeProgram.Action State Tape)
    (h : Q.rule a.1.1.1 a.1.1.2 a.1.2 = some act) :
    FiniteOneTapeProgram.actionOf Q a = act := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.2 hnone).elim

theorem HeadedScannerPath.startArrow_rule {n : ℕ}
    (P : HeadedScannerPath n) :
    MStarULogAssembly.program.rule MStarOuterProgram.State.start
      (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) 0 =
      some { write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
             target := .accept
             move := .stay } := by
  simpa [MStarULogAssembly.program, MStarOuterProgram.program] using
    MStarOuterProgram.start_slot_zero MStarULogAssembly.data
      (HeadedScannerPath.initialCore_isInitial P)

theorem HeadedScannerPath.startArrow_action {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeProgram.actionOf MStarULogAssembly.program
      (HeadedScannerPath.startArrow P) =
      { write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        target := .accept
        move := .stay } := by
  apply actionOf_eq_of_rule_eq MStarULogAssembly.program
    (HeadedScannerPath.startArrow P)
  simpa [HeadedScannerPath.startArrow] using HeadedScannerPath.startArrow_rule P

theorem HeadedScannerPath.startArrow_transition {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeProgram.transition MStarULogAssembly.program
      (HeadedScannerPath.startArrow P) =
      { sourceState := MStarOuterProgram.State.start
        read := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        targetState := MStarOuterProgram.State.accept
        move := .stay } := by
  unfold FiniteOneTapeProgram.transition
  rw [HeadedScannerPath.startArrow_action]
  rfl

theorem HeadedScannerPath.writtenTape_initial_eq {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeSemantics.writtenTape (HeadedScannerPath.initialConfig P)
      (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) =
      HeadedScannerPath.initialTape P := by
  funext z
  by_cases hz : z = (HeadedScannerPath.initialConfig P).head
  · subst z
    simp [FiniteOneTapeSemantics.writtenTape, Function.update,
      HeadedScannerPath.initialTape_head_eq_core]
  · have hz' : z ≠ ((HeadedScannerPath.headIndex P).1 : Int) := by
      simpa [HeadedScannerPath.initialConfig] using hz
    simp [FiniteOneTapeSemantics.writtenTape, Function.update, hz',
      HeadedScannerPath.initialConfig]

theorem HeadedScannerPath.start_step {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable (HeadedScannerPath.initialConfig P)
      (HeadedScannerPath.startArrow P) =
      some (HeadedScannerPath.acceptConfig P) := by
  unfold FiniteOneTapeSemantics.step
  dsimp only
  rw [show FiniteOneTapeProgram.transition MStarULogAssembly.program
      (HeadedScannerPath.startArrow P) =
      { sourceState := MStarOuterProgram.State.start
        read := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        targetState := MStarOuterProgram.State.accept
        move := .stay } from HeadedScannerPath.startArrow_transition P]
  rw [if_neg (by
    push_neg
    exact ⟨rfl, HeadedScannerPath.initialTape_head_eq_core P⟩)]
  have hwritten := HeadedScannerPath.writtenTape_initial_eq P
  have hmovable : MStarOuterProgram.movable
      (FiniteOneTapeSemantics.writtenTape (HeadedScannerPath.initialConfig P)
        (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P))
        (HeadedScannerPath.initialConfig P).head) = true := by
    rw [hwritten, HeadedScannerPath.initialTape_head_eq_core]
    rfl
  dsimp only [FiniteOneTapeSemantics.moveHead]
  simp only [hmovable, if_true]
  apply congrArg some
  apply mstarConfig_ext
  · rfl
  · rfl
  · exact hwritten

noncomputable def HeadedScannerPath.acceptArrow {n : ℕ}
    (P : HeadedScannerPath n) : Fixed.Arrow := by
  refine ⟨((MStarOuterProgram.State.accept,
    MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)), (0 : Fin 2)), ?_⟩
  have hrule := (MStarOuterProgram.accept_unique_stay MStarULogAssembly.data
    (a := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) (by simp)).1
  intro hnone
  rw [hrule] at hnone
  contradiction

theorem HeadedScannerPath.acceptArrow_rule {n : ℕ}
    (P : HeadedScannerPath n) :
    MStarULogAssembly.program.rule MStarOuterProgram.State.accept
      (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) 0 =
      some { write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
             target := .accept
             move := .stay } := by
  exact (MStarOuterProgram.accept_unique_stay MStarULogAssembly.data
    (a := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) (by simp)).1

theorem HeadedScannerPath.acceptArrow_action {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeProgram.actionOf MStarULogAssembly.program
      (HeadedScannerPath.acceptArrow P) =
      { write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        target := .accept
        move := .stay } := by
  apply actionOf_eq_of_rule_eq MStarULogAssembly.program
    (HeadedScannerPath.acceptArrow P)
  simpa [HeadedScannerPath.acceptArrow] using HeadedScannerPath.acceptArrow_rule P

theorem HeadedScannerPath.acceptArrow_transition {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeProgram.transition MStarULogAssembly.program
      (HeadedScannerPath.acceptArrow P) =
      { sourceState := MStarOuterProgram.State.accept
        read := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        targetState := MStarOuterProgram.State.accept
        move := .stay } := by
  unfold FiniteOneTapeProgram.transition
  rw [HeadedScannerPath.acceptArrow_action]
  rfl

theorem HeadedScannerPath.accept_step_self {n : ℕ}
    (P : HeadedScannerPath n) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable (HeadedScannerPath.acceptConfig P)
      (HeadedScannerPath.acceptArrow P) =
      some (HeadedScannerPath.acceptConfig P) := by
  unfold FiniteOneTapeSemantics.step
  dsimp only
  rw [show FiniteOneTapeProgram.transition MStarULogAssembly.program
      (HeadedScannerPath.acceptArrow P) =
      { sourceState := MStarOuterProgram.State.accept
        read := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        write := MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)
        targetState := MStarOuterProgram.State.accept
        move := .stay } from HeadedScannerPath.acceptArrow_transition P]
  have hread : (HeadedScannerPath.acceptConfig P).tape
      (HeadedScannerPath.acceptConfig P).head =
      MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P) := by
    exact HeadedScannerPath.initialTape_head_eq_core P
  rw [if_neg (by push Not; exact ⟨rfl, hread⟩)]
  have hwritten : FiniteOneTapeSemantics.writtenTape
      (HeadedScannerPath.acceptConfig P)
      (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P)) =
      HeadedScannerPath.initialTape P := by
    funext z
    by_cases hz : z = (HeadedScannerPath.acceptConfig P).head
    · subst z
      simp [FiniteOneTapeSemantics.writtenTape, Function.update]
      exact hread.symm
    · have hz' : z ≠ ((HeadedScannerPath.headIndex P).1 : Int) := by
        simpa [HeadedScannerPath.acceptConfig, HeadedScannerPath.initialConfig] using hz
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, hz',
        HeadedScannerPath.acceptConfig, HeadedScannerPath.initialConfig]
  have hmovable : MStarOuterProgram.movable
      (FiniteOneTapeSemantics.writtenTape (HeadedScannerPath.acceptConfig P)
        (MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P))
        (HeadedScannerPath.acceptConfig P).head) = true := by
    rw [hwritten]
    have hread' : HeadedScannerPath.initialTape P
        (HeadedScannerPath.acceptConfig P).head =
        MStarOuterProgram.Tape.core (HeadedScannerPath.initialCore P) := hread
    rw [hread']
    rfl
  dsimp only [FiniteOneTapeSemantics.moveHead]
  simp only [hmovable, if_true]
  apply congrArg some
  apply mstarConfig_ext
  · rfl
  · rfl
  · exact hwritten

private theorem no_head_source_to_top :
    ∀ (s : ConcretePakScanner.State) (b : Bool),
      (s.centre = .headZero ∨ s.centre = .headOne) →
      ¬ ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth b := by
  native_decide

private theorem legal_to_top_source_hash :
    ∀ (s : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth b →
      s.centre = .hash := by
  native_decide

private theorem no_legal_bottom_to_top :
    ∀ b : Bool, ¬ ConcretePakScanner.LegalScan
      PakCouplingGenerated.scannerBottom ConcretePakScanner.topNorth b := by
  native_decide

theorem ScannerPath.size_ge_three {n : ℕ} (P : ScannerPath n) : 3 ≤ n := by
  by_contra hn
  have hnle : n ≤ 2 := by omega
  interval_cases n
  · exact (Nat.not_lt_zero _ P.pos).elim
  · have h := P.legal ⟨0, by omega⟩
    rw [P.bottom, P.top] at h
    exact (no_legal_bottom_to_top _ h).elim
  · have h0 := P.legal ⟨0, by omega⟩
    have h1 := P.legal ⟨1, by omega⟩
    rw [P.bottom] at h0
    rw [P.top] at h1
    have hbad : ∀ s : ConcretePakScanner.State,
        ¬ (ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom s false ∧
          ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth true) := by
      native_decide
    norm_num at h0 h1
    exact (hbad _ ⟨h0, h1⟩).elim

theorem HeadedScannerPath.headIndex_interior {n : ℕ} (P : HeadedScannerPath n) :
    0 < (HeadedScannerPath.headIndex P).1 ∧
      (HeadedScannerPath.headIndex P).1 + 1 < n := by
  have hbuf := HeadedScannerPath.headBuffer_is_headZero_or_headOne P
  constructor
  · by_contra h
    have hz : (HeadedScannerPath.headIndex P).1 = 0 := by omega
    have hk : (⟨(HeadedScannerPath.headIndex P).1,
        Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩ : Fin (n + 1)) =
        ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hz
    have hb := congrArg ConcretePakScanner.State.centre P.1.bottom
    rw [← hk] at hb
    change (P.1.states ⟨(HeadedScannerPath.headIndex P).1,
      Nat.lt_succ_of_lt (HeadedScannerPath.headIndex P).2⟩).centre = .hash at hb
    rcases hbuf with hbuf | hbuf <;> rw [hb] at hbuf <;> contradiction
  · by_contra h
    have hlast : (HeadedScannerPath.headIndex P).1 + 1 = n := by omega
    have hlegal := P.1.legal (HeadedScannerPath.headIndex P)
    have hk : (⟨(HeadedScannerPath.headIndex P).1 + 1, by omega⟩ : Fin (n + 1)) =
        ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hlast
    rw [hk, P.1.top] at hlegal
    exact (no_head_source_to_top _ _ hbuf hlegal).elim

theorem HeadedScannerPath.initialTape_zero_hash {n : ℕ} (P : HeadedScannerPath n) :
    HeadedScannerPath.initialTape P 0 = MStarOuterProgram.Tape.hash := by
  have hn := P.1.pos
  rw [show (0 : Int) = ((⟨0, hn⟩ : Fin n).1 : Int) by rfl,
    HeadedScannerPath.initialTape_at]
  have hb := P.1.bottom
  change P.1.states ⟨0, Nat.zero_lt_succ n⟩ = _ at hb
  have hs : P.1.states (0 : Fin (n + 1)) =
      PakCouplingGenerated.scannerBottom := by simpa using hb
  simp [HeadedScannerPath.emittedOldStrip, PakCouplingGenerated.emittedWindow,
    hs, PakCouplingGenerated.scannerBottom, PakCouplingGenerated.bufferCell,
    MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
    OneTapeTableau.cellLetter]

theorem HeadedScannerPath.initialTape_last_hash {n : ℕ} (P : HeadedScannerPath n) :
    HeadedScannerPath.initialTape P (n - 1 : ℕ) = MStarOuterProgram.Tape.hash := by
  have hn := P.1.pos
  let last : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt hn)⟩
  rw [show ((n - 1 : ℕ) : Int) = (last.1 : Int) by rfl,
    HeadedScannerPath.initialTape_at]
  have hlegal := P.1.legal last
  have hnext : (⟨last.1 + 1, by omega⟩ : Fin (n + 1)) =
      ⟨n, Nat.lt_succ_self n⟩ := by
    apply Fin.ext
    dsimp [last]
    omega
  rw [hnext, P.1.top] at hlegal
  have hc := legal_to_top_source_hash _ _ hlegal
  simp [HeadedScannerPath.emittedOldStrip, PakCouplingGenerated.emittedWindow,
    hc, PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
    MStarOuterProgram.boundaryData, OneTapeTableau.cellLetter]

noncomputable def HeadedScannerPath.runConfig {n : ℕ} (P : HeadedScannerPath n)
    (k : Fin (n + 1)) : MStarConfig :=
  if k.1 = 0 then HeadedScannerPath.initialConfig P else HeadedScannerPath.acceptConfig P

noncomputable def HeadedScannerPath.runArrow {n : ℕ} (P : HeadedScannerPath n)
    (t : Fin n) : Fixed.Arrow :=
  if t.1 = 0 then HeadedScannerPath.startArrow P else HeadedScannerPath.acceptArrow P

noncomputable def HeadedScannerPath.toUniformRun {n : ℕ} (P : HeadedScannerPath n) :
    UniformWindowedMStarRun n n where
  config := HeadedScannerPath.runConfig P
  arrow := HeadedScannerPath.runArrow P
  step := by
    intro t
    by_cases ht : t.1 = 0
    · have ht' : t = ⟨0, P.1.pos⟩ := Fin.ext ht
      subst t
      simpa [HeadedScannerPath.runConfig, HeadedScannerPath.runArrow] using
        HeadedScannerPath.start_step P
    · have hnext : t.1 + 1 ≠ 0 := by omega
      simpa [HeadedScannerPath.runConfig, HeadedScannerPath.runArrow, ht, hnext] using
        HeadedScannerPath.accept_step_self P
  origin := 0
  width_ge_three := ScannerPath.size_ge_three P.1
  head_index := fun _ => HeadedScannerPath.headIndex P
  head_eq := by
    intro k
    by_cases hk : k.1 = 0 <;>
      simp [HeadedScannerPath.runConfig, hk, HeadedScannerPath.initialConfig,
        HeadedScannerPath.acceptConfig]
  head_interior_left := fun _ => (HeadedScannerPath.headIndex_interior P).1
  head_interior_right := fun _ => (HeadedScannerPath.headIndex_interior P).2
  hash_outside := by
    intro k z hz
    have htape := HeadedScannerPath.initialTape_hash_outside P z (by simpa using hz)
    by_cases hk : k.1 = 0 <;>
      simpa [HeadedScannerPath.runConfig, hk, HeadedScannerPath.initialConfig,
        HeadedScannerPath.acceptConfig] using htape
  final_accept := by
    have hn := P.1.pos
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [HeadedScannerPath.runConfig, hn0, HeadedScannerPath.acceptConfig]

noncomputable def HeadedScannerPath.toPaddedRun {n : ℕ} (P : HeadedScannerPath n) :
    PaddedUniformWindowedMStarRun n n where
  run := HeadedScannerPath.toUniformRun P
  left_endpoint_hash := by
    intro t
    have h := HeadedScannerPath.initialTape_zero_hash P
    by_cases ht : t.1 = 0 <;>
      simpa [HeadedScannerPath.toUniformRun, HeadedScannerPath.runConfig, ht,
        HeadedScannerPath.initialConfig, HeadedScannerPath.acceptConfig] using h
  right_endpoint_hash := by
    intro t
    have h := HeadedScannerPath.initialTape_last_hash P
    by_cases ht : t.1 = 0 <;>
      simpa [HeadedScannerPath.toUniformRun, HeadedScannerPath.runConfig, ht,
        HeadedScannerPath.initialConfig, HeadedScannerPath.acceptConfig] using h

theorem HeadedScannerPath.tableau_east_old {n : ℕ} (P : HeadedScannerPath n)
    (j : Fin n) :
    ((HeadedScannerPath.toPaddedRun P).run.tableauTiling.1
      ⟨n - 1, by have := P.1.pos; omega⟩ j).1.old =
      HeadedScannerPath.emittedOldStrip P j := by
  rw [UniformWindowedMStarRun.tableauTiling_cell_old]
  apply CellTriple.ext
  · simp only [HeadedScannerPath.toPaddedRun, HeadedScannerPath.toUniformRun,
      UniformWindowedMStarRun.stepWindow, UniformWindowedMStarRun.revTime,
      HeadedScannerPath.runConfig, HeadedScannerPath.initialConfig,
      WindowedMStarStep.oldStrip,
      WindowedMStarStep.triple, WindowedMStarStep.cell,
      WindowedMStarStep.position, Nat.sub_self, if_pos, Int.zero_add]
    change HeadedScannerPath.initialCell P ((j.1 : Int) - 1) = _
    exact HeadedScannerPath.initialCell_minus P j
  · simp only [HeadedScannerPath.toPaddedRun, HeadedScannerPath.toUniformRun,
      UniformWindowedMStarRun.stepWindow, UniformWindowedMStarRun.revTime,
      HeadedScannerPath.runConfig, HeadedScannerPath.initialConfig,
      WindowedMStarStep.oldStrip,
      WindowedMStarStep.triple, WindowedMStarStep.cell,
      WindowedMStarStep.position, Nat.sub_self, if_pos, Int.zero_add]
    change HeadedScannerPath.initialCell P (j.1 : Int) = _
    exact HeadedScannerPath.initialCell_at P j
  · simp only [HeadedScannerPath.toPaddedRun, HeadedScannerPath.toUniformRun,
      UniformWindowedMStarRun.stepWindow, UniformWindowedMStarRun.revTime,
      HeadedScannerPath.runConfig, HeadedScannerPath.initialConfig,
      WindowedMStarStep.oldStrip,
      WindowedMStarStep.triple, WindowedMStarStep.cell,
      WindowedMStarStep.position, Nat.sub_self, if_pos, Int.zero_add]
    change HeadedScannerPath.initialCell P ((j.1 : Int) + 1) = _
    exact HeadedScannerPath.initialCell_plus P j

theorem HeadedScannerPath.tableau_west_new_accepting {n : ℕ}
    (P : HeadedScannerPath n) (j : Fin n) :
    PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
      ((HeadedScannerPath.toPaddedRun P).run.tableauTiling.1
        ⟨0, P.1.pos⟩ j).1.new := by
  rw [UniformWindowedMStarRun.tableauTiling_cell_new]
  apply PakFullFrameForward.WindowedMStarStep.acceptingWindow_newStrip_of_after_accept
  simpa [HeadedScannerPath.toPaddedRun, HeadedScannerPath.toUniformRun,
    UniformWindowedMStarRun.stepWindow, UniformWindowedMStarRun.revTime,
    HeadedScannerPath.runConfig, HeadedScannerPath.acceptConfig] using
      (HeadedScannerPath.toUniformRun P).final_accept

private theorem legal_chain_middle_phase :
    ∀ (a s t u : ConcretePakScanner.State) (b₀ b₁ b₂ : Bool),
      ConcretePakScanner.LegalScan a s b₀ →
      ConcretePakScanner.LegalScan s t b₁ →
      ConcretePakScanner.LegalScan t u b₂ →
      s.phase = .mid ∧ s.lookahead = .lh0 := by
  intro a s t u b₀ b₁ b₂ has hst htu
  rcases hst with ⟨c, hc⟩
  cases c with
  | bot =>
      have hnot := ConcretePakScanner.no_clause_to_bot a s b₀ hc.2.1
      exact (hnot has).elim
  | mid => exact ⟨hc.2.1, hc.2.2.2.1⟩
  | terminal => exact ⟨hc.2.1, hc.2.2.2.1⟩
  | tail => exact ⟨hc.2.1, hc.2.2.2.1⟩
  | preTop => exact ⟨hc.2.1, hc.2.2.2.1⟩
  | top =>
      have hnot := ConcretePakScanner.no_clause_from_cap t u b₂ hc.2.2.1
      exact (hnot htu).elim

private theorem legal_to_top_phase :
    ∀ (s : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth b →
      s.phase = .top ∧ s.lookahead = .lh1 := by
  intro s b h
  rcases h with ⟨c, hc⟩
  cases c <;> simp_all [ConcretePakScanner.LegalClause,
    ConcretePakScanner.topNorth]

private theorem legal_to_top_scannerTopSouth :
    ∀ (s : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan s ConcretePakScanner.topNorth b →
      PakCouplingGenerated.scannerTopSouth s := by
  intro s b h
  rcases h with ⟨c, hc⟩
  cases c <;> simp_all [ConcretePakScanner.LegalClause,
    ConcretePakScanner.topNorth, PakCouplingGenerated.scannerTopSouth]

theorem ScannerPath.activityCoupled {n : ℕ} (P : ScannerPath n) (j : Fin n) :
    ConcretePakScanner.ActivityCoupledStep
      (decide (j.1 = 0)) (decide (j.1 + 1 = n))
      (P.column j) (n.testBit j.1) := by
  let s := P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩
  let t := P.states ⟨j.1 + 1, by omega⟩
  by_cases hbot : j.1 = 0
  · have hs : s = PakCouplingGenerated.scannerBottom := by
      dsimp [s]
      rw [show (⟨j.1, Nat.lt_succ_of_lt j.2⟩ : Fin (n + 1)) =
        ⟨0, Nat.zero_lt_succ n⟩ by apply Fin.ext; exact hbot]
      exact P.bottom
    have hnotTop : j.1 + 1 ≠ n := by
      have hsize := ScannerPath.size_ge_three P
      omega
    have hone : 1 ≠ n := by omega
    refine ⟨s, t, rfl, P.legal j, ?_, ?_⟩
    · simp [ConcretePakScanner.PhaseCoupled, hbot, hone, hs,
        PakCouplingGenerated.scannerBottom]
    · simp [ConcretePakScanner.LookaheadCoupled, hnotTop, hs,
        PakCouplingGenerated.scannerBottom]
  · by_cases htop : j.1 + 1 = n
    · have ht : t = ConcretePakScanner.topNorth := by
        dsimp [t]
        rw [show (⟨j.1 + 1, by omega⟩ : Fin (n + 1)) =
          ⟨n, Nat.lt_succ_self n⟩ by apply Fin.ext; exact htop]
        exact P.top
      have hsphase := legal_to_top_phase s (n.testBit j.1) (by
        simpa [s, t, ht] using P.legal j)
      refine ⟨s, t, rfl, P.legal j, ?_, ?_⟩
      · simpa [ConcretePakScanner.PhaseCoupled, hbot, htop] using hsphase.1
      · simpa [ConcretePakScanner.LookaheadCoupled, htop] using hsphase.2
    · have hjprev : j.1 - 1 < n := by omega
      have hjnext : j.1 + 1 < n := by omega
      let jm : Fin n := ⟨j.1 - 1, hjprev⟩
      let jp : Fin n := ⟨j.1 + 1, hjnext⟩
      have hm := P.legal jm
      have hc := P.legal j
      have hp := P.legal jp
      have hmnext : (⟨jm.1 + 1, by omega⟩ : Fin (n + 1)) =
          ⟨j.1, Nat.lt_succ_of_lt j.2⟩ := by
        apply Fin.ext
        dsimp [jm]
        omega
      have hpstart : (⟨jp.1, Nat.lt_succ_of_lt jp.2⟩ : Fin (n + 1)) =
          ⟨j.1 + 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hmnext] at hm
      have hp' : ConcretePakScanner.LegalScan t
          (P.states ⟨jp.1 + 1, Nat.succ_lt_succ jp.2⟩) (n.testBit jp.1) := by
        dsimp [t]
        rw [← hpstart]
        exact hp
      have hsphase := legal_chain_middle_phase
        (P.states ⟨jm.1, Nat.lt_succ_of_lt jm.2⟩) s t
        (P.states ⟨jp.1 + 1, Nat.succ_lt_succ jp.2⟩)
        (n.testBit jm.1) (n.testBit j.1) (n.testBit jp.1)
        (by simpa [s] using hm) (by simpa [s, t] using hc)
        hp'
      refine ⟨s, t, rfl, P.legal j, ?_, ?_⟩
      · simpa [ConcretePakScanner.PhaseCoupled, hbot, htop] using hsphase.1
      · simpa [ConcretePakScanner.LookaheadCoupled, htop] using hsphase.2

noncomputable def HeadedScannerPath.fullTrackCertificate {n : ℕ}
    (P : HeadedScannerPath n) : FullTrackRunCertificate
      (HeadedScannerPath.toPaddedRun P) where
  time_pos := P.1.pos
  amplifier := PakRippleCanonical.canonicalFullAmpTiling Fixed.Q n n
  ripple := PakRippleCanonical.canonicalTiling n n
  scanner := P.1.toEastTiling
  coupled := by
    intro i j
    let east : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt P.1.pos)⟩
    change ConcreteWProd.FiveCouplingTable.accepts Fixed.Machine Fixed.Q
      (MStarULogAssembly.fiveCouplings Fixed.Q) _
    apply (PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q _).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hwest
      have hi : i.1 = 0 := by
        simpa [PakCouplingGenerated.amp,
          PakRippleCanonical.canonicalFullAmpTiling,
          PakRippleCanonical.canonicalFullAmpCell] using hwest
      have hi0 : i = ⟨0, P.1.pos⟩ := Fin.ext hi
      subst i
      refine ⟨PakRippleCanonical.canonicalTiling_west n n j P.1.pos,
        HeadedScannerPath.tableau_west_new_accepting P j, ?_⟩
      apply P.1.toEastTiling_nonEast
      have hsize := ScannerPath.size_ge_three P.1
      omega
    · intro heast
      have hi : i = east := by
        apply Fin.ext
        dsimp [east]
        change decide (i.1 + 1 = n) = true at heast
        have := decide_eq_true_eq.mp heast
        omega
      subst i
      refine ⟨?_, ?_⟩
      · change ConcretePakScanner.ActivityCoupledStep
          (decide (j.1 = 0)) (decide (j.1 + 1 = n))
          (P.1.toEastTiling.1 east j)
          (Bool.xor ((PakRippleCanonical.canonicalTiling n n).1 east j).1
            ((PakRippleCanonical.canonicalTiling n n).1 east j).2)
        rw [P.1.toEastTiling_east]
        change ConcretePakScanner.ActivityCoupledStep _ _ (P.1.column j)
          ((rippleTile ((PakRippleCanonical.canonicalTiling n n).1 east j)).east)
        have hripple :
            (rippleTile ((PakRippleCanonical.canonicalTiling n n).1 east j)).east =
              n.testBit j.1 := by
          simpa [east] using PakRippleCanonical.canonicalTiling_east n n P.1.pos j
        rw [hripple]
        exact ScannerPath.activityCoupled P.1 j
      · refine ⟨P.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
          P.1.states ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, ?_, ?_⟩
        · change P.1.toEastTiling.1 east j = _
          simpa [east, ScannerPath.column] using P.1.toEastTiling_east j
        · apply (PakCouplingGenerated.emittedMatches_iff_eq
            MStarULogAssembly.boundaryData _ _ _).mpr
          change ((HeadedScannerPath.toPaddedRun P).run.tableauTiling.1 east j).1.old = _
          simpa [east, HeadedScannerPath.emittedOldStrip] using
            HeadedScannerPath.tableau_east_old P j
    · intro hsouth
      have hj : j = ⟨0, P.1.pos⟩ := by
        apply Fin.ext
        change decide (j.1 = 0) = true at hsouth
        exact decide_eq_true_eq.mp hsouth
      subst j
      refine ⟨PakRippleCanonical.canonicalTiling_south n n i P.1.pos,
        PakFullFrameForward.padded_tableau_south_sentinel
          (HeadedScannerPath.toPaddedRun P) i, ?_⟩
      intro heast'
      have hi : i = east := by
        apply Fin.ext
        dsimp [east]
        change decide (i.1 + 1 = n) = true at heast'
        have := decide_eq_true_eq.mp heast'
        omega
      subst i
      refine ⟨P.1.states ⟨1, by have := ScannerPath.size_ge_three P.1; omega⟩, ?_⟩
      change P.1.toEastTiling.1 east ⟨0, P.1.pos⟩ = _
      rw [P.1.toEastTiling_east]
      change some (P.1.states ⟨0, Nat.zero_lt_succ n⟩,
        P.1.states ⟨1, Nat.succ_lt_succ P.1.pos⟩) = _
      rw [P.1.bottom]
    · intro hnorth
      have hjval : j.1 + 1 = n := by
        change decide (j.1 + 1 = n) = true at hnorth
        exact decide_eq_true_eq.mp hnorth
      let top : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt P.1.pos)⟩
      have hjTop : j = top := Fin.ext (by dsimp [top]; omega)
      subst j
      have hsent := PakFullFrameForward.padded_tableau_north_sentinel
        (HeadedScannerPath.toPaddedRun P) i
      refine ⟨?_, ?_, ?_⟩
      · simp only [PakCouplingGenerated.ripple]
        have hpow : i.1 < 2 ^ (n - 1) := by
          have hi := i.2
          have hn3 := ScannerPath.size_ge_three P.1
          have hk : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self
          omega
        have htest : i.1.testBit (n - 1) = false :=
          Nat.testBit_eq_false_of_lt hpow
        simp [PakRippleCanonical.canonicalTiling,
          PakRippleCanonical.canonicalCell, PakRippleCanonical.rippleBit,
          PakRippleCanonical.rippleCarry, top, htest]
      · change PakCouplingGenerated.northSentinel
          MStarULogAssembly.boundaryData Fixed.Machine
          ((HeadedScannerPath.toPaddedRun P).run.tableauTiling.1 i top)
        simpa [top] using hsent
      · intro heast'
        have hi : i = east := by
          apply Fin.ext
          dsimp [east]
          change decide (i.1 + 1 = n) = true at heast'
          have := decide_eq_true_eq.mp heast'
          omega
        subst i
        let last : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt P.1.pos)⟩
        have hlegal := P.1.legal last
        have hnext : (⟨last.1 + 1, by omega⟩ : Fin (n + 1)) =
            ⟨n, Nat.lt_succ_self n⟩ := by
          apply Fin.ext
          dsimp [last]
          omega
        rw [hnext, P.1.top] at hlegal
        refine ⟨P.1.states ⟨last.1, Nat.lt_succ_of_lt last.2⟩,
          ConcretePakScanner.topNorth, ?_, ?_⟩
        · change P.1.toEastTiling.1 east top = _
          have he := P.1.toEastTiling_east last
          have ht : P.1.states ⟨last.1 + 1, Nat.succ_lt_succ last.2⟩ =
              ConcretePakScanner.topNorth := by
            rw [hnext, P.1.top]
          simpa [east, top, last, ScannerPath.column, ht] using he
        · exact legal_to_top_scannerTopSouth _ _ hlegal
    · intro hnonEast
      simp_all [PakRippleCanonical.canonicalFullAmpTiling,
        PakRippleCanonical.canonicalFullAmpCell,
        ScannerPath.toEastTiling, PakCanonicalScanner.eastColumnTiling,
        PakCanonicalScanner.eastColumnCell, PakCouplingGenerated.amp,
        PakCouplingGenerated.ripple, PakCouplingGenerated.tableau,
        PakCouplingGenerated.scan]
  west_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_west Fixed.Q n n P.1.pos j
  east_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_east Fixed.Q n n P.1.pos j
  south_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_south Fixed.Q n n i
      (by have := ScannerPath.size_ge_three P.1; omega)
  north_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_north Fixed.Q n n i
      (by have := ScannerPath.size_ge_three P.1; omega)

noncomputable def HeadedScannerPath.toFullFrame {n : ℕ}
    (P : HeadedScannerPath n) : FullFrame n n :=
  (HeadedScannerPath.fullTrackCertificate P).toFullFrame

theorem ScannerPath.toEastTiling_injective {n : ℕ} :
    Function.Injective (ScannerPath.toEastTiling (n := n)) := by
  intro P Q htiling
  have hstates : P.states = Q.states := by
    funext k
    by_cases hk : k.1 < n
    · let j : Fin n := ⟨k.1, hk⟩
      let eastP : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt P.pos)⟩
      let eastQ : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt Q.pos)⟩
      have heast : eastP = eastQ := by apply Fin.ext; rfl
      have hcell := congrFun (congrFun (congrArg Subtype.val htiling) eastP) j
      rw [heast] at hcell
      have hP := P.toEastTiling_east j
      have hQ := Q.toEastTiling_east j
      have hcol : P.column j = Q.column j := hP.symm.trans (hcell.trans hQ)
      have hpairs :
          (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
            P.states ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) =
          (Q.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
            Q.states ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) := by
        exact Option.some.inj (by simpa [ScannerPath.column] using hcol)
      have hfirst := congrArg Prod.fst hpairs
      simpa [j] using hfirst
    · have hkval : k.1 = n := by omega
      have hkTop : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hkval
      subst k
      exact P.top.trans Q.top.symm
  cases P
  cases Q
  cases hstates
  rfl

theorem HeadedScannerPath.toFullFrame_scannerProjection {n : ℕ}
    (P : HeadedScannerPath n) :
    scannerProjection (HeadedScannerPath.toFullFrame P).tiling =
      P.1.toEastTiling := by
  have hread := FullTrackRunCertificate.toFullFrame_readout
    (HeadedScannerPath.fullTrackCertificate P)
  exact congrArg FrameReadout.scanner hread

theorem HeadedScannerPath.toScannerPath_toFullFrame {n : ℕ}
    (P : HeadedScannerPath n) :
    FullFrame.toScannerPath (HeadedScannerPath.toFullFrame P) = P.1 := by
  apply ScannerPath.toEastTiling_injective
  calc
    (FullFrame.toScannerPath (HeadedScannerPath.toFullFrame P)).toEastTiling =
        scannerProjection (HeadedScannerPath.toFullFrame P).tiling :=
      (FullFrame.scannerColumnReadback
        (HeadedScannerPath.toFullFrame P)).tiling_eq_pathTiling.symm
    _ = P.1.toEastTiling := HeadedScannerPath.toFullFrame_scannerProjection P

private theorem readback_head_northToken {w h : ℕ} (F : FullFrame w h)
    (i : Fin w) :
    let R := FullFrame.tableau_column_readback F i
    (tableauAt F.tiling i R.head).1.northToken = some R.arrow := by
  let head : Fin h := Classical.choose (FullFrame.tableau_column_old_head_exists F i)
  have hhead : (tableauAt F.tiling i head).1.old.center.isHead = true :=
    Classical.choose_spec (FullFrame.tableau_column_old_head_exists F i)
  let transition := FullFrame.tableau_column_head_transition F i head hhead
  let a : Fixed.Arrow := Classical.choose transition
  have htransition := Classical.choose_spec transition
  change (tableauAt F.tiling i head).1.northToken = some a
  exact htransition.2.1

theorem HeadedScannerPath.toFullFrame_firstArrow {n : ℕ}
    (P : HeadedScannerPath n) :
    (FullFrame.toUniformWindowedRun (HeadedScannerPath.toFullFrame P)).arrow
      ⟨0, P.1.pos⟩ = HeadedScannerPath.startArrow P := by
  let C := HeadedScannerPath.fullTrackCertificate P
  let F := HeadedScannerPath.toFullFrame P
  let U := HeadedScannerPath.toUniformRun P
  let east : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt P.1.pos)⟩
  let t0 : Fin n := ⟨0, P.1.pos⟩
  let R := FullFrame.tableau_column_readback F east
  have htableau := FullTrackRunCertificate.toFullFrame_tableau C
  have hcell : tableauAt F.tiling east R.head = U.tileAt t0 R.head := by
    have hc := congrFun (congrFun (congrArg Subtype.val htableau) east) R.head
    change tableauAt F.tiling east R.head = U.tableauTiling.1 east R.head at hc
    rw [hc]
    change U.tileAt (UniformWindowedMStarRun.revTime east) R.head =
      U.tileAt t0 R.head
    congr 1
    apply Fin.ext
    simp [UniformWindowedMStarRun.revTime, east, t0]
  have hstrip : R.oldStrip R.head = HeadedScannerPath.emittedOldStrip P R.head := by
    calc
      R.oldStrip R.head = (tableauAt F.tiling east R.head).1.old := by
        simp [R]
      _ = (U.tileAt t0 R.head).1.old := congrArg (fun u => u.1.old) hcell
      _ = (U.stepWindow t0).oldStrip R.head := U.tileAt_old t0 R.head
      _ = HeadedScannerPath.emittedOldStrip P R.head := by
        have heast := HeadedScannerPath.tableau_east_old P R.head
        rw [UniformWindowedMStarRun.tableauTiling_cell_old] at heast
        simpa [U, HeadedScannerPath.toPaddedRun,
          UniformWindowedMStarRun.revTime, east, t0] using heast
  have hRhead : R.head = HeadedScannerPath.headIndex P := by
    apply HeadedScannerPath.headIndex_unique P R.head
    rw [← hstrip]
    exact R.head_is_head
  have htokenR : (tableauAt F.tiling east R.head).1.northToken =
      some R.arrow := by
    simpa [R] using readback_head_northToken F east
  have htokenP : (U.tileAt t0 R.head).1.northToken =
      some (HeadedScannerPath.startArrow P) := by
    rw [U.tileAt_northToken]
    have hidx : R.head = (U.stepWindow t0).head_index := by
      change R.head = HeadedScannerPath.headIndex P
      exact hRhead
    rw [if_pos hidx]
    rfl
  have harrow : R.arrow = HeadedScannerPath.startArrow P := by
    apply Option.some.inj
    rw [← htokenR, hcell]
    exact htokenP
  change FullFrame.reverse_tableau_arrow F t0 = _
  rw [PakFullFrameTableauRoundtrip.reverse_tableau_arrow_column]
  have hrev : reverseColumn t0 = east := by
    apply Fin.ext
    simp [reverseColumn, t0, east]
  rw [hrev]
  exact harrow

noncomputable def HeadedScannerPath.toSlotZeroFullFrame {n : ℕ}
    (P : HeadedScannerPath n) : SlotZeroFullFrame n :=
  ⟨HeadedScannerPath.toFullFrame P, by
    rw [HeadedScannerPath.toFullFrame_firstArrow]
    rfl⟩

theorem HeadedScannerPath.slotZeroToHeadedScannerPath_toSlotZeroFullFrame {n : ℕ}
    (P : HeadedScannerPath n) :
    slotZeroToHeadedScannerPath (HeadedScannerPath.toSlotZeroFullFrame P) = P := by
  apply Subtype.ext
  exact HeadedScannerPath.toScannerPath_toFullFrame P

noncomputable def slotZeroFullFrameEquivHeadedScannerPath (n : ℕ) :
    SlotZeroFullFrame n ≃ HeadedScannerPath n where
  toFun := slotZeroToHeadedScannerPath
  invFun := HeadedScannerPath.toSlotZeroFullFrame
  left_inv := by
    intro F
    apply slotZeroToHeadedScannerPath_injective
    exact HeadedScannerPath.slotZeroToHeadedScannerPath_toSlotZeroFullFrame _
  right_inv := HeadedScannerPath.slotZeroToHeadedScannerPath_toSlotZeroFullFrame

noncomputable instance slotZeroFullFrameFintype (n : ℕ) :
    Fintype (SlotZeroFullFrame n) :=
  Fintype.ofEquiv (HeadedScannerPath n)
    (slotZeroFullFrameEquivHeadedScannerPath n).symm

theorem card_slotZeroFullFrame_eq_baselineCount (n : ℕ) :
    Fintype.card (SlotZeroFullFrame n) = baselineCount n := by
  rw [Fintype.card_congr (slotZeroFullFrameEquivHeadedScannerPath n)]
  rfl

end PakFixedPolyomino.PakSlotZeroFullFrameBijection
