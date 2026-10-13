import PakFixedPolyomino.PakFullFrameTableauStep

namespace PakFixedPolyomino.PakFullFrameTableauReadback

open PakMStarCouplingCorrectness

theorem FullFrame.adjacent_tableau_columns_new_old_tape {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (hi : i.1 + 1 < w) :
    (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
      ⟨i.1 + 1, hi⟩).newTape =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
        i).oldTape := by
  funext z
  by_cases hz : z < 0 ∨ (h : Int) ≤ z
  · rw [TableauColumnStepReadback.newTape_hash_outside _ z hz,
      TableauColumnStepReadback.oldTape_hash_outside _ z hz]
  · push Not at hz
    let j : Fin h := ⟨z.toNat, by omega⟩
    have hzj : (j.1 : Int) = z := by
      dsimp [j]
      exact Int.toNat_of_nonneg hz.1
    rw [← hzj]
    have hadj := PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.adjacent_tableau_columns_old_new F i hi j
    calc
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
        ⟨i.1 + 1, hi⟩).newTape j.1 =
          OneTapeTableau.cellLetter
            ((tableauAt F.tiling ⟨i.1 + 1, hi⟩ j).1.new).center := by
              simpa using TableauColumnStepReadback.newTape_at
                (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
                  ⟨i.1 + 1, hi⟩) j
      _ = OneTapeTableau.cellLetter ((tableauAt F.tiling i j).1.old).center := by
              rw [← hadj]
      _ = (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
        i).oldTape j.1 := by
              simpa using (TableauColumnStepReadback.oldTape_at
                (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i) j).symm

/-- Chronological time runs from the easternmost tableau column to the west. -/
def reverseColumn {w : ℕ} (t : Fin w) : Fin w :=
  ⟨w - 1 - t.1, by omega⟩

theorem reverseColumn_succ {w : ℕ} (t : Fin w) (ht : t.1 + 1 < w) :
    (reverseColumn ⟨t.1 + 1, ht⟩).1 + 1 = (reverseColumn t).1 := by
  change w - 1 - (t.1 + 1) + 1 = w - 1 - t.1
  omega

theorem reverseColumn_zero {w : ℕ} (t : Fin w) (ht : t.1 + 1 = w) :
    reverseColumn t = ⟨0, by omega⟩ := by
  apply Fin.ext
  change w - 1 - t.1 = 0
  omega

theorem TableauColumnStepReadback.new_head_marker {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    ∃ j : Fin h, (j.1 : Int) = R.after.head ∧
      ∃ a, (R.newStrip j).center =
        TableauCell.head R.after.state a := by
  let tr := FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow
  have htheta := R.theta
  change OneTapeTableau.theta MStarOuterProgram.movable tr
    (R.oldStrip R.head) = some (R.newStrip R.head) at htheta
  have hsrc := R.arrow_source
  change (R.arrow.1.1.1, R.arrow.1.1.2) =
    (R.oldStrip R.head).center.headSourceOf R.head_is_head at hsrc
  have hhead := R.head_is_head
  cases hcell : (R.oldStrip R.head).center with
  | plain x =>
      rw [hcell] at hhead
      simp [TableauCell.isHead] at hhead
  | head q x =>
      have hsourceOf : (R.oldStrip R.head).center.headSourceOf R.head_is_head = (q, x) :=
        WindowedMStarStep.headSourceOf_eq_of_eq hcell R.head_is_head
      have hpair : (q, x) = (tr.sourceState, tr.read) := (hsrc.trans hsourceOf).symm
      have hstate : q = tr.sourceState := congrArg Prod.fst hpair
      have hread : x = tr.read := congrArg Prod.snd hpair
      cases hmove : tr.move with
      | left =>
          cases hm : (R.oldStrip R.head).minus with
          | plain m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
              let left : Fin h := ⟨R.head.1 - 1, by have h := R.head_interior; omega⟩
              have hn : left.1 + 1 < h := by change R.head.1 - 1 + 1 < h; have h := R.head_interior; omega
              have heq : (⟨left.1 + 1, hn⟩ : Fin h) = R.head := by apply Fin.ext; change R.head.1 - 1 + 1 = R.head.1; have h := R.head_interior; omega
              have hover := R.new_overlap left hn |>.1
              refine ⟨left, ?_, m, ?_⟩
              · change ((R.head.1 - 1 : ℕ) : Int) = FiniteOneTapeSemantics.moveHead tr.move R.head.1
                simp [hmove, FiniteOneTapeSemantics.moveHead]
                have h := R.head_interior
                omega
              · have hminus := congrArg CellTriple.minus htheta.2
                calc
                  (R.newStrip left).center = (R.newStrip R.head).minus := hover.trans (by rw [heq])
                  _ = TableauCell.head tr.targetState m := hminus.symm
                  _ = TableauCell.head R.after.state m := by rfl
          | head qm m => simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          refine ⟨R.head, by simp [after, before, tr, hmove, FiniteOneTapeSemantics.moveHead], tr.write, ?_⟩
          have hc := congrArg CellTriple.center htheta.2
          exact hc.symm
      | right =>
          cases hp : (R.oldStrip R.head).plus with
          | plain p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta
              let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
              have hn : R.head.1 + 1 < h := (R.head_interior).2
              have hover := R.new_overlap R.head hn |>.2
              refine ⟨right, ?_, p, ?_⟩
              · change ((R.head.1 + 1 : ℕ) : Int) = FiniteOneTapeSemantics.moveHead tr.move R.head.1
                simp [hmove, FiniteOneTapeSemantics.moveHead]
              · have hplus := congrArg CellTriple.plus htheta.2
                calc
                  (R.newStrip right).center = (R.newStrip R.head).plus := hover.symm
                  _ = TableauCell.head tr.targetState p := hplus.symm
                  _ = TableauCell.head R.after.state p := by rfl
          | head qp p => simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta

private theorem config_ext_plain (c d : MStarConfig)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  rcases c with ⟨cs, ch, ct⟩
  rcases d with ⟨ds, dh, dt⟩
  simp only at hstate hhead htape
  subst ds
  subst dh
  subst dt
  rfl

theorem FullFrame.adjacent_tableau_columns_after_before {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (hi : i.1 + 1 < w) :
    (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
      ⟨i.1 + 1, hi⟩).after =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
        i).before := by
  let east := PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F ⟨i.1 + 1, hi⟩
  let west := PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  have htape : east.after.tape = west.before.tape := by
    change east.newTape = west.oldTape
    exact adjacent_tableau_columns_new_old_tape F i hi
  rcases east.new_head_marker with ⟨j, hjpos, a, hjmarker⟩
  have hadj := PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.adjacent_tableau_columns_old_new F i hi j
  have hadjCenter := congrArg CellTriple.center hadj
  have hwestmarker : (west.oldStrip j).center = TableauCell.head east.after.state a := by
    simpa [east, west] using hadjCenter.trans hjmarker
  have hjhead : j = west.head := by
    apply west.head_unique j
    rw [hwestmarker]
    rfl
  have hhead : east.after.head = west.before.head := by
    change east.after.head = (west.head.1 : Int)
    rw [← hjhead]
    exact hjpos.symm
  have hstate : east.after.state = west.before.state := by
    change east.after.state =
      ((west.oldStrip west.head).center.headSourceOf west.head_is_head).1
    rw [hjhead] at hwestmarker
    have hsource := WindowedMStarStep.headSourceOf_eq_of_eq hwestmarker west.head_is_head
    rw [hsource]
  exact config_ext_plain east.after west.before hstate hhead htape

noncomputable def FullFrame.reverse_tableau_config {w h : ℕ} (F : FullFrame w h)
    (t : Fin (w + 1)) : MStarConfig :=
  if ht : t.1 < w then
    (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
      (reverseColumn ⟨t.1, ht⟩)).before
  else
    (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
      ⟨0, F.width_pos⟩).after

noncomputable def FullFrame.reverse_tableau_arrow {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) : Fixed.Arrow :=
  (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
    (reverseColumn t)).arrow

theorem FullFrame.reverse_tableau_config_last {w h : ℕ} (F : FullFrame w h) :
    reverse_tableau_config F ⟨w, Nat.lt_succ_self w⟩ =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
        ⟨0, F.width_pos⟩).after := by
  simp [FullFrame.reverse_tableau_config]

theorem FullFrame.west_new_head_interior {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) {a : Fixed.Tape}
    (hmarker : ((PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
      ⟨0, F.width_pos⟩).newStrip j).center = TableauCell.head
        (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
          ⟨0, F.width_pos⟩).after.state a) :
    0 < j.1 ∧ j.1 + 1 < h := by
  let west := PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F
    ⟨0, F.width_pos⟩
  rcases (F.south_has_sentinel ⟨0, F.width_pos⟩).2 with
    ⟨_, _, _, hsnew, _, _, _⟩
  rcases (F.north_has_sentinel ⟨0, F.width_pos⟩).2 with
    ⟨_, _, hnnew, _, _, _, _⟩
  constructor
  · by_contra hzero
    have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.ext (Nat.eq_zero_of_not_pos hzero)
    rw [hj] at hmarker
    have hs : (west.newStrip ⟨0, F.height_pos⟩).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
      simpa [west] using hsnew
    rw [hs] at hmarker
    cases hmarker
  · by_contra hlast
    have hjval : j.1 = h - 1 := by omega
    have hj : j = northIndex F.height_pos := by
      apply Fin.ext
      simpa [northIndex] using hjval
    rw [hj] at hmarker
    have hn : (west.newStrip (northIndex F.height_pos)).center =
        TableauCell.plain MStarULogAssembly.boundaryData.hash := by
      simpa [west] using hnnew
    rw [hn] at hmarker
    cases hmarker

@[simp] theorem FullFrame.reverse_tableau_config_of_lt {w h : ℕ}
    (F : FullFrame w h) (t : Fin (w + 1)) (ht : t.1 < w) :
    reverse_tableau_config F t =
      (tableau_column_readback F (reverseColumn ⟨t.1, ht⟩)).before := by
  simp [reverse_tableau_config, ht]

theorem FullFrame.reverse_tableau_step {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
      (reverse_tableau_config F ⟨t.1, Nat.lt_succ_of_lt t.2⟩)
      (reverse_tableau_arrow F t) =
        some (reverse_tableau_config F ⟨t.1 + 1, by omega⟩) := by
  have hbefore : t.1 < w := t.2
  rw [reverse_tableau_config_of_lt F _ hbefore]
  unfold reverse_tableau_arrow
  rw [(tableau_column_readback F (reverseColumn t)).step_eq_after]
  by_cases hnext : t.1 + 1 < w
  · rw [reverse_tableau_config_of_lt F _ hnext]
    have hsucc := reverseColumn_succ t hnext
    let west : Fin w := reverseColumn ⟨t.1 + 1, hnext⟩
    have hi : west.1 + 1 < w := by
      dsimp [west, reverseColumn]
      omega
    have heq : (⟨west.1 + 1, hi⟩ : Fin w) = reverseColumn t := by
      apply Fin.ext
      exact hsucc
    have hadj := adjacent_tableau_columns_after_before F west hi
    rw [heq] at hadj
    exact congrArg some hadj
  · have hlast : t.1 + 1 = w := by omega
    have htLast : (⟨t.1 + 1, by omega⟩ : Fin (w + 1)) =
        ⟨w, Nat.lt_succ_self w⟩ := Fin.eq_of_val_eq hlast
    rw [htLast, reverse_tableau_config_last]
    have hzero := reverseColumn_zero t hlast
    rw [hzero]

noncomputable def FullFrame.reverse_tableau_headIndex {w h : ℕ}
    (F : FullFrame w h) (t : Fin (w + 1)) : Fin h :=
  if ht : t.1 < w then
    (tableau_column_readback F (reverseColumn ⟨t.1, ht⟩)).head
  else
    Classical.choose
      ((tableau_column_readback F ⟨0, F.width_pos⟩).new_head_marker)

theorem FullFrame.reverse_tableau_head_eq {w h : ℕ}
    (F : FullFrame w h) (t : Fin (w + 1)) :
    (reverse_tableau_config F t).head =
      (reverse_tableau_headIndex F t).1 := by
  by_cases ht : t.1 < w
  · simp [reverse_tableau_config, reverse_tableau_headIndex, ht,
      TableauColumnStepReadback.before]
  · have htw : t.1 = w := by omega
    have hlast : t = ⟨w, Nat.lt_succ_self w⟩ := Fin.eq_of_val_eq htw
    rw [hlast, reverse_tableau_config_last]
    let west := tableau_column_readback F ⟨0, F.width_pos⟩
    have hspec := Classical.choose_spec west.new_head_marker
    simpa [reverse_tableau_headIndex, htw, west] using hspec.1.symm

theorem FullFrame.reverse_tableau_head_interior {w h : ℕ}
    (F : FullFrame w h) (t : Fin (w + 1)) :
    0 < (reverse_tableau_headIndex F t).1 ∧
      (reverse_tableau_headIndex F t).1 + 1 < h := by
  by_cases ht : t.1 < w
  · simp [reverse_tableau_headIndex, ht,
      (tableau_column_readback F (reverseColumn ⟨t.1, ht⟩)).head_interior]
  · have htw : t.1 = w := by omega
    let west := tableau_column_readback F ⟨0, F.width_pos⟩
    have hspec := Classical.choose_spec west.new_head_marker
    rcases hspec.2 with ⟨a, hmarker⟩
    have hinterior := west_new_head_interior F
      (Classical.choose west.new_head_marker) hmarker
    simpa [reverse_tableau_headIndex, ht, west] using hinterior

theorem FullFrame.reverse_tableau_hash_outside {w h : ℕ}
    (F : FullFrame w h) (t : Fin (w + 1)) (z : Int)
    (hz : z < 0 ∨ (h : Int) ≤ z) :
    (reverse_tableau_config F t).tape z = .hash := by
  by_cases ht : t.1 < w
  · rw [reverse_tableau_config_of_lt F t ht]
    exact (tableau_column_readback F (reverseColumn ⟨t.1, ht⟩)).oldTape_hash_outside z hz
  · have htw : t.1 = w := by omega
    have hlast : t = ⟨w, Nat.lt_succ_self w⟩ := Fin.eq_of_val_eq htw
    rw [hlast, reverse_tableau_config_last]
    exact (tableau_column_readback F ⟨0, F.width_pos⟩).newTape_hash_outside z hz

theorem FullFrame.reverse_tableau_final_accept {w h : ℕ}
    (F : FullFrame w h) :
    (reverse_tableau_config F ⟨w, Nat.lt_succ_self w⟩).state =
      MStarOuterProgram.State.accept := by
  rw [reverse_tableau_config_last]
  let west := tableau_column_readback F ⟨0, F.width_pos⟩
  rcases west.new_head_marker with ⟨j, hjpos, a, hmarker⟩
  have hliteral : (tableauAt F.tiling ⟨0, F.width_pos⟩ j).1.new.center =
      TableauCell.head west.after.state a := by
    simpa [west] using hmarker
  exact west_new_head_is_accept F j hliteral

/-- Every literal FullFrame reads back to an actual chronological accepting
M-star run, with no scanner classification or run certificate supplied. -/
noncomputable def FullFrame.toUniformWindowedRun {w h : ℕ}
    (F : FullFrame w h) : UniformWindowedMStarRun h w where
  config := reverse_tableau_config F
  arrow := reverse_tableau_arrow F
  step := reverse_tableau_step F
  origin := 0
  width_ge_three := by
    have hinterior := (tableau_column_readback F ⟨0, F.width_pos⟩).head_interior
    omega
  head_index := reverse_tableau_headIndex F
  head_eq := by
    intro t
    simpa using reverse_tableau_head_eq F t
  head_interior_left := fun t => (reverse_tableau_head_interior F t).1
  head_interior_right := fun t => (reverse_tableau_head_interior F t).2
  hash_outside := by
    intro t z hz
    apply reverse_tableau_hash_outside F t z
    simpa using hz
  final_accept := reverse_tableau_final_accept F

end PakFixedPolyomino.PakFullFrameTableauReadback
