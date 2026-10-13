import PakFixedPolyomino.PakFullFrameUniformReadback

/-! # Tableau readback roundtrip interfaces -/

namespace PakFixedPolyomino.PakFullFrameTableauRoundtrip

open PakMStarCouplingCorrectness
open PakFullFrameTableauReadback

@[simp] theorem toMStarStep_before {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : R.toMStarStep.before = R.before := rfl

@[simp] theorem toMStarStep_after {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : R.toMStarStep.after = R.after := rfl

@[simp] theorem toMStarStep_arrow {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : R.toMStarStep.arrow = R.arrow := rfl

@[simp] theorem toMStarStep_head {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : R.toMStarStep.head_index = R.head := rfl

theorem reverse_tableau_config_before {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) :
    FullFrame.reverse_tableau_config F ⟨t.1, Nat.lt_succ_of_lt t.2⟩ =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)).before := by
  simp [FullFrame.reverse_tableau_config]

theorem reverse_tableau_arrow_column {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) :
    FullFrame.reverse_tableau_arrow F t =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)).arrow := rfl

theorem reverse_tableau_config_after_of_succ {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) (ht : t.1 + 1 < w) :
    FullFrame.reverse_tableau_config F ⟨t.1 + 1, by omega⟩ =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)).after := by
  rw [FullFrame.reverse_tableau_config]
  simp only [dif_pos (by omega)]
  let west : Fin w := reverseColumn ⟨t.1 + 1, ht⟩
  have hi : west.1 + 1 < w := by
    dsimp [west, reverseColumn]
    omega
  have heq : (⟨west.1 + 1, hi⟩ : Fin w) = reverseColumn t := by
    apply Fin.ext
    exact reverseColumn_succ t ht
  have hadj := FullFrame.adjacent_tableau_columns_after_before F west hi
  rw [heq] at hadj
  exact hadj.symm

/-- The north/south sentinel bits force a visible new head in every literal
tableau column, just as they force an old head.  This is deliberately proved
from the raw higher-block clauses: it is not inferred from the reconstructed
operational step. -/
theorem FullFrame.tableau_column_new_head_exists {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) :
    ∃ j : Fin h, (tableauAt F.tiling i j).1.new.center.isHead = true := by
  by_contra hheads
  push Not at hheads
  rcases (F.south_has_sentinel i).2 with
    ⟨_, _, _, _, _, hbottom, _⟩
  rcases (F.north_has_sentinel i).2 with
    ⟨_, _, _, _, _, htop, _⟩
  have hbits : ∀ j : Fin h,
      (tableauAt F.tiling i j).1.newMinusBit = false ∧
        (tableauAt F.tiling i j).1.newPlusBit = false := by
    intro j
    induction k : j.1 using Nat.strong_induction_on generalizing j with
    | h k ih =>
        have hminus : (tableauAt F.tiling i j).1.newMinusBit = false := by
          by_cases hj0 : j.1 = 0
          · have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
            simpa [hj] using hbottom
          · let jb : Fin h := ⟨j.1 - 1, by omega⟩
            have hjb : jb.1 + 1 < h := by
              dsimp [jb]
              omega
            have hprev := (ih jb.1 (by dsimp [jb]; omega) jb rfl).2
            have hover := tableau_bits_tokens_overlap F.tiling i jb hjb
            have hj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
              apply Fin.ext
              dsimp [jb]
              omega
            rw [← hj]
            exact hover.2.1.symm.trans hprev
        refine ⟨hminus, ?_⟩
        have hcenter : (tableauAt F.tiling i j).1.new.center.isHead = false := by
          cases hz : (tableauAt F.tiling i j).1.new.center.isHead <;>
            simp_all
        have hord := (tableauAt F.tiling i j).2.2.2.2.1
        have heq : (tableauAt F.tiling i j).1.newMinusBit =
            (tableauAt F.tiling i j).1.newPlusBit := by
          simpa [tableauOrdBit, hcenter] using hord
        rw [← heq]
        exact hminus
  let top : Fin h := northIndex F.height_pos
  have htopFalse := (hbits top).2
  rw [htop] at htopFalse
  simp at htopFalse

/-- The new order track has the same one-crossing rigidity as the old track.
This is the missing uniqueness fact needed when the readback is compared with
the generated `orderBit` decoration. -/
theorem FullFrame.tableau_column_new_head_unique {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) {j k : Fin h}
    (hj : (tableauAt F.tiling i j).1.new.center.isHead = true)
    (hk : (tableauAt F.tiling i k).1.new.center.isHead = true) : j = k := by
  apply Fin.eq_of_val_eq
  by_contra hne
  have hjBits : (tableauAt F.tiling i j).1.newMinusBit = false ∧
      (tableauAt F.tiling i j).1.newPlusBit = true := by
    have ho := (tableauAt F.tiling i j).2.2.2.2.1
    unfold tableauOrdBit at ho
    simpa [hj] using ho
  have hkBits : (tableauAt F.tiling i k).1.newMinusBit = false ∧
      (tableauAt F.tiling i k).1.newPlusBit = true := by
    have ho := (tableauAt F.tiling i k).2.2.2.2.1
    unfold tableauOrdBit at ho
    simpa [hk] using ho
  have chain_mono : ∀ (a b : Fin h), a.1 < b.1 →
      (tableauAt F.tiling i a).1.newPlusBit = true →
        (tableauAt F.tiling i b).1.newMinusBit = true := by
    intro a b hab ha
    induction d : b.1 - a.1 using Nat.strong_induction_on generalizing b with
    | h d ih =>
        by_cases hs : a.1 + 1 = b.1
        · have hov := (tableau_bits_tokens_overlap F.tiling i a (by omega)).2.1
          have heq : (⟨a.1 + 1, by omega⟩ : Fin h) = b := Fin.eq_of_val_eq hs
          simpa [heq, ha] using hov.symm
        · let bp : Fin h := ⟨b.1 - 1, by omega⟩
          have hbp : bp.1 + 1 < h := by
            dsimp [bp]
            omega
          have hprev : (tableauAt F.tiling i bp).1.newMinusBit = true := by
            apply ih (bp.1 - a.1)
            · dsimp [bp]
              omega
            · dsimp [bp]
              omega
            · rfl
          have hord := (tableauAt F.tiling i bp).2.2.2.2.1
          have hplus : (tableauAt F.tiling i bp).1.newPlusBit = true := by
            unfold tableauOrdBit at hord
            split at hord <;> simp_all
          have hov := tableau_bits_tokens_overlap F.tiling i bp hbp
          have heq : (⟨bp.1 + 1, hbp⟩ : Fin h) = b := by
            apply Fin.ext
            dsimp [bp]
            omega
          simpa [heq, hplus] using hov.2.1.symm
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have bad := chain_mono j k hjk hjBits.2
    simp [hkBits.1] at bad
  · have bad := chain_mono k j hkj hkBits.2
    simp [hjBits.1] at bad

/-- The old order bits are not additional tableau choices: the lower
sentinel, vertical overlap, and the unique old head force the literal cut at
the readback head. -/
theorem FullFrame.tableau_column_old_bits_forced {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    let R :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
    (tableauAt F.tiling i j).1.oldMinusBit = decide (R.head.1 < j.1) ∧
      (tableauAt F.tiling i j).1.oldPlusBit = decide (R.head.1 < j.1 + 1) := by
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  have hhead := R.head_is_head
  induction k : j.1 using Nat.strong_induction_on generalizing j with
  | h k ih =>
      subst_vars
      have hminus : (tableauAt F.tiling i j).1.oldMinusBit =
          decide (R.head.1 < j.1) := by
        by_cases hj0 : j.1 = 0
        · rcases (F.south_has_sentinel i).2 with
            ⟨_, _, _, _, hbottom, _, _⟩
          have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
          rw [hj]
          simp [hbottom]
        · let jb : Fin h := ⟨j.1 - 1, by omega⟩
          have hjb : jb.1 + 1 < h := by
            dsimp [jb]
            omega
          have hprev := (ih jb.1 (by dsimp [jb]; omega) jb rfl).2
          have hover := tableau_bits_tokens_overlap F.tiling i jb hjb
          have hj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
            apply Fin.ext
            dsimp [jb]
            omega
          calc
            (tableauAt F.tiling i j).1.oldMinusBit =
                (tableauAt F.tiling i jb).1.oldPlusBit := by
                  rw [← hj]
                  exact hover.1.symm
            _ = decide (R.head.1 < jb.1 + 1) := hprev
            _ = decide (R.head.1 < j.1) := by
                  have hv : jb.1 + 1 = j.1 := by
                    dsimp [jb]
                    omega
                  rw [hv]
      refine ⟨hminus, ?_⟩
      have hord := (tableauAt F.tiling i j).2.2.2.1
      by_cases hjhead : j = R.head
      · subst j
        have hc : (tableauAt F.tiling i R.head).1.old.center.isHead = true := by
          simpa [R] using R.head_is_head
        unfold tableauOrdBit at hord
        rw [hc] at hord
        change (tableauAt F.tiling i R.head).1.oldPlusBit =
          decide (R.head.1 < R.head.1 + 1)
        exact hord.2.trans (by simp)
      · have hc : (tableauAt F.tiling i j).1.old.center.isHead = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hc
          exact hjhead (R.head_unique j (by simpa [R] using hc))
        have heqbits : (tableauAt F.tiling i j).1.oldMinusBit =
            (tableauAt F.tiling i j).1.oldPlusBit := by
          simpa [tableauOrdBit, hc] using hord
        have hcut : decide (R.head.1 < j.1) =
            decide (R.head.1 < j.1 + 1) := by
          by_cases hlt : R.head.1 < j.1
          · have hlt' : R.head.1 < j.1 + 1 := by omega
            simp [hlt, hlt']
          · have hlt' : ¬ R.head.1 < j.1 + 1 := by
              intro hlt'
              apply hjhead
              apply Fin.ext
              omega
            simp [hlt, hlt']
        exact heqbits.symm.trans (hminus.trans hcut)

/-- The analogous rigidity statement for the post-step order decoration.
The chosen head is intrinsic because `tableau_column_new_head_unique` was
proved above from the raw column, rather than supplied by a run. -/
theorem FullFrame.tableau_column_new_bits_forced {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    let H := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
    (tableauAt F.tiling i j).1.newMinusBit = decide (H.1 < j.1) ∧
      (tableauAt F.tiling i j).1.newPlusBit = decide (H.1 < j.1 + 1) := by
  let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
  have hhead : (tableauAt F.tiling i H).1.new.center.isHead = true :=
    Classical.choose_spec (FullFrame.tableau_column_new_head_exists F i)
  induction k : j.1 using Nat.strong_induction_on generalizing j with
  | h k ih =>
      subst_vars
      have hminus : (tableauAt F.tiling i j).1.newMinusBit =
          decide (H.1 < j.1) := by
        by_cases hj0 : j.1 = 0
        · rcases (F.south_has_sentinel i).2 with
            ⟨_, _, _, _, _, hbottom, _⟩
          have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
          rw [hj]
          simp [hbottom]
        · let jb : Fin h := ⟨j.1 - 1, by omega⟩
          have hjb : jb.1 + 1 < h := by
            dsimp [jb]
            omega
          have hprev := (ih jb.1 (by dsimp [jb]; omega) jb rfl).2
          have hover := tableau_bits_tokens_overlap F.tiling i jb hjb
          have hj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
            apply Fin.ext
            dsimp [jb]
            omega
          calc
            (tableauAt F.tiling i j).1.newMinusBit =
                (tableauAt F.tiling i jb).1.newPlusBit := by
                  rw [← hj]
                  exact hover.2.1.symm
            _ = decide (H.1 < jb.1 + 1) := hprev
            _ = decide (H.1 < j.1) := by
                  have hv : jb.1 + 1 = j.1 := by
                    dsimp [jb]
                    omega
                  rw [hv]
      refine ⟨hminus, ?_⟩
      have hord := (tableauAt F.tiling i j).2.2.2.2.1
      by_cases hjhead : j = H
      · subst j
        unfold tableauOrdBit at hord
        rw [hhead] at hord
        change (tableauAt F.tiling i H).1.newPlusBit =
          decide (H.1 < H.1 + 1)
        exact hord.2.trans (by simp)
      · have hc : (tableauAt F.tiling i j).1.new.center.isHead = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hc
          exact hjhead (FullFrame.tableau_column_new_head_unique F i hc hhead)
        have heqbits : (tableauAt F.tiling i j).1.newMinusBit =
            (tableauAt F.tiling i j).1.newPlusBit := by
          simpa [tableauOrdBit, hc] using hord
        have hcut : decide (H.1 < j.1) = decide (H.1 < j.1 + 1) := by
          by_cases hlt : H.1 < j.1
          · have hlt' : H.1 < j.1 + 1 := by omega
            simp [hlt, hlt']
          · have hlt' : ¬ H.1 < j.1 + 1 := by
              intro hlt'
              apply hjhead
              apply Fin.ext
              omega
            simp [hlt, hlt']
        exact heqbits.symm.trans (hminus.trans hcut)

/-- At its unique old head, column readback keeps the literal north token as
the chosen labelled arrow.  This matters because two occupied program slots
may carry the same action but are still distinct tableau arrows. -/
theorem FullFrame.tableau_column_readback_head_north_token {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) :
    let R :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
    (tableauAt F.tiling i R.head).1.northToken = some R.arrow := by
  classical
  let head : Fin h := Classical.choose (FullFrame.tableau_column_old_head_exists F i)
  have hhead : (tableauAt F.tiling i head).1.old.center.isHead = true :=
    Classical.choose_spec (FullFrame.tableau_column_old_head_exists F i)
  let transition := FullFrame.tableau_column_head_transition F i head hhead
  let a : Fixed.Arrow := Classical.choose transition
  have htransition := Classical.choose_spec transition
  change (tableauAt F.tiling i head).1.northToken = some a
  exact htransition.2.1

/-- The north token is forced everywhere in a literal tableau column: it is
the one labelled arrow at the old head and `none` elsewhere. -/
theorem FullFrame.tableau_column_north_token_forced {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    let R :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
    (tableauAt F.tiling i j).1.northToken =
      if j = R.head then some R.arrow else none := by
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  change (tableauAt F.tiling i j).1.northToken =
    if j = R.head then some R.arrow else none
  by_cases hj : j = R.head
  · subst j
    simpa [R] using FullFrame.tableau_column_readback_head_north_token F i
  · rw [if_neg hj]
    have hc : (tableauAt F.tiling i j).1.old.center.isHead = false := by
      simpa [R] using R.old_center_not_head_of_ne hj
    exact HigherBlockTableau.northToken_none_of_center_plain Fixed.Machine
      (tableauAt F.tiling i j) hc

/-- The south token is the same labelled arrow one row above the old head.
The bottom sentinel provides the base case; every other case is the literal
vertical north/south token overlap. -/
theorem FullFrame.tableau_column_south_token_forced {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    let R :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
    let right : Fin h := ⟨R.head.1 + 1, R.head_interior.2⟩
    (tableauAt F.tiling i j).1.southToken =
      if j = right then some R.arrow else none := by
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let right : Fin h := ⟨R.head.1 + 1, R.head_interior.2⟩
  have hright : R.head.1 + 1 < h := R.head_interior.2
  change (tableauAt F.tiling i j).1.southToken =
    if j = right then some R.arrow else none
  by_cases hjright : j = right
  · subst j
    rw [if_pos rfl]
    have hover := tableau_bits_tokens_overlap F.tiling i R.head hright
    have hnorth := FullFrame.tableau_column_readback_head_north_token F i
    change (tableauAt F.tiling i right).1.southToken = some R.arrow
    rw [← hover.2.2]
    simpa [R] using hnorth
  · rw [if_neg hjright]
    by_cases hj0 : j.1 = 0
    · rcases (F.south_has_sentinel i).2 with
        ⟨_, _, _, _, _, _, hbottom⟩
      have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
      simpa [hj] using hbottom
    · let jb : Fin h := ⟨j.1 - 1, by omega⟩
      have hjb : jb.1 + 1 < h := by
        dsimp [jb]
        omega
      have heq : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
        apply Fin.ext
        dsimp [jb]
        omega
      have hjbhead : jb ≠ R.head := by
        intro hEq
        apply hjright
        apply Fin.ext
        have hval : jb.1 = R.head.1 := congrArg Fin.val hEq
        have hjval : jb.1 + 1 = j.1 := congrArg Fin.val heq
        change j.1 = R.head.1 + 1
        omega
      have hc : (tableauAt F.tiling i jb).1.old.center.isHead = false := by
        simpa [R] using R.old_center_not_head_of_ne hjbhead
      have hnorth := HigherBlockTableau.northToken_none_of_center_plain Fixed.Machine
        (tableauAt F.tiling i jb) hc
      have hover := tableau_bits_tokens_overlap F.tiling i jb hjb
      rw [← heq]
      exact hover.2.2.symm.trans hnorth

/-- The intrinsically chosen new head is exactly the physical post-step head
of the literal column readback.  Thus the new cut in
`tableau_column_new_bits_forced` already has the coordinate used by the
reconstructed operational configuration. -/
theorem FullFrame.tableau_column_new_head_eq_after_head {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) :
    ((Classical.choose (FullFrame.tableau_column_new_head_exists F i)).1 : Int) =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F i).after.head := by
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
  have hH : (tableauAt F.tiling i H).1.new.center.isHead = true :=
    Classical.choose_spec (FullFrame.tableau_column_new_head_exists F i)
  rcases R.new_head_marker with ⟨j, hjpos, a, hjmarker⟩
  have hjhead : (tableauAt F.tiling i j).1.new.center.isHead = true := by
    rw [← PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback_newStrip
      F i j, hjmarker]
    rfl
  have hHj : H = j := FullFrame.tableau_column_new_head_unique F i hH hjhead
  change (H.1 : Int) = R.after.head
  rw [hHj]
  exact hjpos

/-- Reversing the horizontal time coordinate twice returns the literal
tableau column. -/
theorem reverseColumn_revTime {w : ℕ} (i : Fin w) :
    reverseColumn (UniformWindowedMStarRun.revTime i) = i := by
  apply Fin.ext
  change w - 1 - (w - 1 - i.1) = i.1
  have hi := i.2
  omega

/-- The post-step configuration of every chronological readback column is
also literal at the final time; the final-time branch is separated here so
later component comparisons do not hide a boundary case. -/
theorem reverse_tableau_config_after {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) :
    FullFrame.reverse_tableau_config F ⟨t.1 + 1, by omega⟩ =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)).after := by
  by_cases hnext : t.1 + 1 < w
  · exact reverse_tableau_config_after_of_succ F t hnext
  · have hlast : t.1 + 1 = w := by omega
    have htLast : (⟨t.1 + 1, by omega⟩ : Fin (w + 1)) =
        ⟨w, Nat.lt_succ_self w⟩ := Fin.eq_of_val_eq hlast
    rw [htLast, FullFrame.reverse_tableau_config_last]
    have hzero := reverseColumn_zero t hlast
    rw [hzero]

/-- At a non-final chronological time, the uniform-run head index is exactly
the unique old head selected by literal column readback. -/
theorem reverse_tableau_headIndex_before {w h : ℕ} (F : FullFrame w h)
    (t : Fin w) :
    FullFrame.reverse_tableau_headIndex F ⟨t.1, Nat.lt_succ_of_lt t.2⟩ =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)).head := by
  simp [FullFrame.reverse_tableau_headIndex, t.2]

/-- The operational step window obtained from a full frame has the literal
readback column as its old configuration, new configuration, arrow, and old
head index.  These component identities avoid identifying proof fields of
`WindowedMStarStep`. -/
theorem FullFrame.toUniform_stepWindow_components {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let R :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
        F (reverseColumn t)
    (U.stepWindow t).before = R.before ∧
      (U.stepWindow t).after = R.after ∧
      (U.stepWindow t).arrow = R.arrow ∧
      (U.stepWindow t).head_index = R.head := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
      F (reverseColumn t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change FullFrame.reverse_tableau_config F ⟨t.1, Nat.lt_succ_of_lt t.2⟩ = R.before
    simpa [R] using reverse_tableau_config_before F t
  · change FullFrame.reverse_tableau_config F ⟨t.1 + 1, by omega⟩ = R.after
    simpa [R] using reverse_tableau_config_after F t
  · exact reverse_tableau_arrow_column F t
  · change FullFrame.reverse_tableau_headIndex F ⟨t.1, Nat.lt_succ_of_lt t.2⟩ = R.head
    simpa [R] using reverse_tableau_headIndex_before F t

/-- The four order decorations in an original column are precisely the four
`orderBit` decorations generated by the readback uniform run at the matching
chronological time. -/
theorem FullFrame.tableau_column_bits_eq_toUniform {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    (tableauAt F.tiling i j).1.oldMinusBit = U.oldMinusBit t j ∧
      (tableauAt F.tiling i j).1.oldPlusBit = U.oldPlusBit t j ∧
      (tableauAt F.tiling i j).1.newMinusBit = U.newMinusBit t j ∧
      (tableauAt F.tiling i j).1.newPlusBit = U.newPlusBit t j := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  have hcomp := FullFrame.toUniform_stepWindow_components F t
  have hpos : (U.stepWindow t).position j = (j.1 : Int) := by
    unfold WindowedMStarStep.position
    rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
    change (0 : Int) + (j.1 : Int) = (j.1 : Int)
    simp
  have hold := FullFrame.tableau_column_old_bits_forced F i j
  have hnew := FullFrame.tableau_column_new_bits_forced F i j
  have hnewHead := FullFrame.tableau_column_new_head_eq_after_head F i
  change (tableauAt F.tiling i j).1.oldMinusBit = U.oldMinusBit t j ∧
    (tableauAt F.tiling i j).1.oldPlusBit = U.oldPlusBit t j ∧
    (tableauAt F.tiling i j).1.newMinusBit = U.newMinusBit t j ∧
    (tableauAt F.tiling i j).1.newPlusBit = U.newPlusBit t j
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (tableauAt F.tiling i j).1.oldMinusBit =
      decide ((U.stepWindow t).before.head < (U.stepWindow t).position j)
    rw [hcomp.1, hpos]
    change (tableauAt F.tiling i j).1.oldMinusBit = decide ((R.head.1 : Int) < j.1)
    simpa [R] using hold.1
  · change (tableauAt F.tiling i j).1.oldPlusBit =
      decide ((U.stepWindow t).before.head < (U.stepWindow t).position j + 1)
    rw [hcomp.1, hpos]
    change (tableauAt F.tiling i j).1.oldPlusBit = decide ((R.head.1 : Int) < j.1 + 1)
    simpa [R] using hold.2
  · change (tableauAt F.tiling i j).1.newMinusBit =
      decide ((U.stepWindow t).after.head < (U.stepWindow t).position j)
    rw [hcomp.2.1, hpos]
    change (tableauAt F.tiling i j).1.newMinusBit = decide (R.after.head < j.1)
    rw [← hnewHead]
    simpa [R] using hnew.1
  · change (tableauAt F.tiling i j).1.newPlusBit =
      decide ((U.stepWindow t).after.head < (U.stepWindow t).position j + 1)
    rw [hcomp.2.1, hpos]
    change (tableauAt F.tiling i j).1.newPlusBit = decide (R.after.head < j.1 + 1)
    rw [← hnewHead]
    simpa [R] using hnew.2

/-- Centre cells of the old strip are recovered exactly by the operational
window.  The head case reads the state from `before`; every other cell is the
plain letter stored in `oldTape`. -/
theorem FullFrame.tableau_column_old_center_eq_stepWindow {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    (tableauAt F.tiling i j).1.old.center = ((U.stepWindow t).oldStrip j).center := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let S := U.stepWindow t
  have hcomp := FullFrame.toUniform_stepWindow_components F t
  have hpos : S.position j = (j.1 : Int) := by
    unfold S WindowedMStarStep.position
    rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
    change (0 : Int) + (j.1 : Int) = (j.1 : Int)
    simp
  change (R.oldStrip j).center = (S.oldStrip j).center
  by_cases hj : j = R.head
  · subst j
    have hshead : S.head_index = R.head := hcomp.2.2.2
    have hcenter := S.head_index_old_center
    rw [hshead] at hcenter
    change (R.oldStrip R.head).center = (S.triple S.before R.head).center
    rw [hcenter, hcomp.1]
    cases hcell : (R.oldStrip R.head).center with
    | plain a =>
        have hhead := R.head_is_head
        simp [hcell, TableauCell.isHead] at hhead
    | head q a =>
        have htape : R.before.tape R.before.head = a := by
          change R.oldTape R.head.1 = a
          rw [R.oldTape_at R.head, hcell]
          rfl
        have hstate : R.before.state = q := by
          change ((R.oldStrip R.head).center.headSourceOf R.head_is_head).1 = q
          rw [WindowedMStarStep.headSourceOf_eq_of_eq hcell R.head_is_head]
        exact congrArg₂ TableauCell.head hstate.symm htape.symm
  · have hplain : (R.oldStrip j).center.isHead = false :=
      R.old_center_not_head_of_ne hj
    cases hcell : (R.oldStrip j).center with
    | plain a =>
        have htape : R.before.tape j.1 = a := by
          change R.oldTape j.1 = a
          calc
            R.oldTape j.1 = OneTapeTableau.cellLetter (R.oldStrip j).center :=
              R.oldTape_at j
            _ = a := by simp [hcell, OneTapeTableau.cellLetter]
        have hne : (j.1 : Int) ≠ R.before.head := by
          change (j.1 : Int) ≠ R.head.1
          intro h
          apply hj
          apply Fin.ext
          exact_mod_cast h
        unfold WindowedMStarStep.oldStrip WindowedMStarStep.triple
        change TableauCell.plain a = S.cell S.before (S.position j)
        rw [hcomp.1, hpos]
        unfold WindowedMStarStep.cell
        rw [if_neg hne, htape]
    | head q a =>
        have : False := by simpa [hcell, TableauCell.isHead] using hplain
        exact this.elim

/-- Centre cells of the new strip are recovered in the same way.  Here the
unique literal new head is first identified with the post-step head. -/
theorem FullFrame.tableau_column_new_center_eq_stepWindow {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    (tableauAt F.tiling i j).1.new.center = ((U.stepWindow t).newStrip j).center := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let S := U.stepWindow t
  let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
  have hcomp := FullFrame.toUniform_stepWindow_components F t
  have hHpos : (H.1 : Int) = R.after.head :=
    FullFrame.tableau_column_new_head_eq_after_head F i
  have hpos : S.position j = (j.1 : Int) := by
    unfold S WindowedMStarStep.position
    rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
    change (0 : Int) + (j.1 : Int) = (j.1 : Int)
    simp
  change (R.newStrip j).center = (S.newStrip j).center
  by_cases hj : j = H
  · subst j
    rcases R.new_head_marker with ⟨k, hkpos, a, hkmarker⟩
    have hkhead : (tableauAt F.tiling i k).1.new.center.isHead = true := by
      rw [← PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback_newStrip
        F i k, hkmarker]
      rfl
    have hHhead : (tableauAt F.tiling i H).1.new.center.isHead = true :=
      Classical.choose_spec (FullFrame.tableau_column_new_head_exists F i)
    have hHk : H = k := FullFrame.tableau_column_new_head_unique F i hHhead hkhead
    subst k
    have htape : R.after.tape R.after.head =
        a := by
      calc
        R.after.tape R.after.head = R.newTape R.after.head := rfl
        _ = R.newTape H.1 := by rw [← hHpos]
        _ = OneTapeTableau.cellLetter (R.newStrip H).center := R.newTape_at H
        _ = a := by simp [hkmarker, OneTapeTableau.cellLetter]
    unfold WindowedMStarStep.newStrip WindowedMStarStep.triple
    change (R.newStrip H).center = S.cell S.after (S.position H)
    rw [hcomp.2.1, hpos]
    rw [hkmarker]
    unfold WindowedMStarStep.cell
    rw [if_pos hHpos]
    change TableauCell.head R.after.state a =
      TableauCell.head R.after.state (R.after.tape (H.1 : Int))
    rw [hHpos, htape]
  · have hplain : (R.newStrip j).center.isHead = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hjhead
      have horig : (tableauAt F.tiling i j).1.new.center.isHead = true := by
        simpa [R] using hjhead
      have hHhead : (tableauAt F.tiling i H).1.new.center.isHead = true :=
        Classical.choose_spec (FullFrame.tableau_column_new_head_exists F i)
      exact hj (FullFrame.tableau_column_new_head_unique F i horig hHhead)
    cases hcell : (R.newStrip j).center with
    | plain a =>
        have htape : R.after.tape j.1 = a := by
          change R.newTape j.1 = a
          calc
            R.newTape j.1 = OneTapeTableau.cellLetter (R.newStrip j).center :=
              R.newTape_at j
            _ = a := by simp [hcell, OneTapeTableau.cellLetter]
        have hne : (j.1 : Int) ≠ R.after.head := by
          intro h
          apply hj
          apply Fin.ext
          exact_mod_cast h.trans hHpos.symm
        unfold WindowedMStarStep.newStrip WindowedMStarStep.triple
        change TableauCell.plain a = S.cell S.after (S.position j)
        rw [hcomp.2.1, hpos]
        unfold WindowedMStarStep.cell
        rw [if_neg hne, htape]
    | head q a =>
        have : False := by simpa [hcell, TableauCell.isHead] using hplain
        exact this.elim

/-- Once centre cells are fixed, vertical Wang overlap and the two old-strip
sentinels determine the complete old radius-one strip. -/
theorem FullFrame.tableau_column_oldStrip_eq_stepWindow {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    (tableauAt F.tiling i j).1.old = (U.stepWindow t).oldStrip j := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let S := U.stepWindow t
  change R.oldStrip j = S.oldStrip j
  apply CellTriple.ext
  · by_cases hj0 : j.1 = 0
    · have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
      subst j
      have hleft : (⟨0, F.height_pos⟩ : Fin h) = S.leftIndex := by
        apply Fin.ext
        rfl
      rw [hleft]
      exact R.south_old_hash.1.trans S.left_boundary_old_minus_hash.symm
    · let jb : Fin h := ⟨j.1 - 1, by omega⟩
      have hjb : jb.1 + 1 < h := by
        dsimp [jb]
        omega
      have heq : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
        apply Fin.ext
        dsimp [jb]
        omega
      calc
        (R.oldStrip j).minus = (R.oldStrip jb).center := by
          rw [← heq]
          exact (R.old_overlap jb hjb).1.symm
        _ = (S.oldStrip jb).center := by
          simpa [S, U, i, R] using FullFrame.tableau_column_old_center_eq_stepWindow F t jb
        _ = (S.oldStrip j).minus := by
          rw [← heq]
          exact (S.oldStrip_overlap jb hjb).1
  · simpa [S, U, i, R] using FullFrame.tableau_column_old_center_eq_stepWindow F t j
  · by_cases hjtop : j.1 + 1 = h
    · have hj : j = northIndex F.height_pos := by
        apply Fin.ext
        simp [northIndex]
        omega
      subst j
      have hright : northIndex F.height_pos = S.rightIndex := by
        apply Fin.ext
        simp [northIndex, WindowedMStarStep.rightIndex]
      rw [hright]
      exact R.north_old_hash.2.trans S.right_boundary_old_plus_hash.symm
    · let jr : Fin h := ⟨j.1 + 1, by omega⟩
      have hjr : j.1 + 1 < h := jr.2
      calc
        (R.oldStrip j).plus = (R.oldStrip jr).center := (R.old_overlap j hjr).2
        _ = (S.oldStrip jr).center := by
          simpa [S, U, i, R] using FullFrame.tableau_column_old_center_eq_stepWindow F t jr
        _ = (S.oldStrip j).plus := (S.oldStrip_overlap j hjr).2.symm

/-- The two literal new-strip sentinels force the post-step head strictly
inside the same finite window. -/
theorem FullFrame.tableau_column_new_head_interior {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) :
    let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
    0 < H.1 ∧ H.1 + 1 < h := by
  let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
  have hH : (tableauAt F.tiling i H).1.new.center.isHead = true :=
    Classical.choose_spec (FullFrame.tableau_column_new_head_exists F i)
  constructor
  · by_contra hzero
    have hval : H.1 = 0 := Nat.eq_zero_of_not_pos hzero
    have hbot : H = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hval
    rcases (F.south_has_sentinel i).2 with ⟨_, _, _, hsnew, _, _, _⟩
    rw [hbot, hsnew] at hH
    simp [TableauCell.isHead] at hH
  · by_contra htop
    have hval : H.1 = h - 1 := by omega
    have htop' : H = northIndex F.height_pos := by
      apply Fin.ext
      simpa [northIndex] using hval
    rcases (F.north_has_sentinel i).2 with ⟨_, _, hnnew, _, _, _, _⟩
    rw [htop', hnnew] at hH
    simp [TableauCell.isHead] at hH

/-- Vertical overlap and the new sentinels now determine the complete
post-step strip as well. -/
theorem FullFrame.tableau_column_newStrip_eq_stepWindow {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    (tableauAt F.tiling i j).1.new = (U.stepWindow t).newStrip j := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let S := U.stepWindow t
  let H : Fin h := Classical.choose (FullFrame.tableau_column_new_head_exists F i)
  have hcomp := FullFrame.toUniform_stepWindow_components F t
  have hHpos : (H.1 : Int) = R.after.head :=
    FullFrame.tableau_column_new_head_eq_after_head F i
  have hHint := FullFrame.tableau_column_new_head_interior F i
  change R.newStrip j = S.newStrip j
  apply CellTriple.ext
  · by_cases hj0 : j.1 = 0
    · have hj : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
      subst j
      rcases (F.south_has_sentinel i).2 with ⟨_, _, hsnew, _, _, _, _⟩
      have hR : (R.newStrip ⟨0, F.height_pos⟩).minus =
          TableauCell.plain MStarULogAssembly.boundaryData.hash := by
        simpa [R] using hsnew
      have hpos : S.position (⟨0, F.height_pos⟩ : Fin h) - 1 < S.origin := by
        unfold S WindowedMStarStep.position
        rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
        omega
      have hne : S.position (⟨0, F.height_pos⟩ : Fin h) - 1 ≠ S.after.head := by
        rw [hcomp.2.1]
        intro heq
        have hnorm : S.position (⟨0, F.height_pos⟩ : Fin h) - 1 = (-1 : Int) := by
          unfold S WindowedMStarStep.position
          rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
          change (0 : Int) + 0 - 1 = -1
          norm_num
        have heq' : (-1 : Int) = R.after.head := hnorm.symm.trans heq
        have hbad : (-1 : Int) = (H.1 : Int) := heq'.trans hHpos.symm
        have hpositive := hHint.1
        omega
      have hS : (S.newStrip (⟨0, F.height_pos⟩ : Fin h)).minus =
          TableauCell.plain MStarULogAssembly.boundaryData.hash := by
        unfold WindowedMStarStep.newStrip WindowedMStarStep.triple
        change S.cell S.after (S.position (⟨0, F.height_pos⟩ : Fin h) - 1) = _
        unfold WindowedMStarStep.cell
        rw [if_neg hne]
        exact congrArg TableauCell.plain
          (S.after_hash_outside _ (Or.inl hpos))
      exact hR.trans hS.symm
    · let jb : Fin h := ⟨j.1 - 1, by omega⟩
      have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
      have heq : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
        apply Fin.ext
        dsimp [jb]
        omega
      calc
        (R.newStrip j).minus = (R.newStrip jb).center := by
          rw [← heq]
          exact (R.new_overlap jb hjb).1.symm
        _ = (S.newStrip jb).center := by
          simpa [S, U, i, R] using FullFrame.tableau_column_new_center_eq_stepWindow F t jb
        _ = (S.newStrip j).minus := by
          rw [← heq]
          exact (S.newStrip_overlap jb hjb).1
  · simpa [S, U, i, R] using FullFrame.tableau_column_new_center_eq_stepWindow F t j
  · by_cases hjtop : j.1 + 1 = h
    · have hj : j = northIndex F.height_pos := by
        apply Fin.ext
        simp [northIndex]
        omega
      subst j
      rcases (F.north_has_sentinel i).2 with ⟨_, _, _, hnnew, _, _, _⟩
      have hR : (R.newStrip (northIndex F.height_pos)).plus =
          TableauCell.plain MStarULogAssembly.boundaryData.hash := by
        simpa [R] using hnnew
      have hpos : S.origin + h ≤ S.position (northIndex F.height_pos) + 1 := by
        unfold S WindowedMStarStep.position
        rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
        simp only [northIndex]
        have hh := F.height_pos
        omega
      have hne : S.position (northIndex F.height_pos) + 1 ≠ S.after.head := by
        rw [hcomp.2.1]
        intro heq
        have hnorm : S.position (northIndex F.height_pos) + 1 = (h : Int) := by
          unfold S WindowedMStarStep.position
          rw [UniformWindowedMStarRun.stepWindow_uniform_origin]
          change (0 : Int) + ((northIndex F.height_pos).1 : Int) + 1 = (h : Int)
          simp only [northIndex]
          have hh := F.height_pos
          omega
        have heq' : (h : Int) = R.after.head := hnorm.symm.trans heq
        have hbad : (h : Int) = (H.1 : Int) := heq'.trans hHpos.symm
        have hinterior := hHint.2
        omega
      have hS : (S.newStrip (northIndex F.height_pos)).plus =
          TableauCell.plain MStarULogAssembly.boundaryData.hash := by
        unfold WindowedMStarStep.newStrip WindowedMStarStep.triple
        change S.cell S.after (S.position (northIndex F.height_pos) + 1) = _
        unfold WindowedMStarStep.cell
        rw [if_neg hne]
        exact congrArg TableauCell.plain
          (S.after_hash_outside _ (Or.inr hpos))
      exact hR.trans hS.symm
    · let jr : Fin h := ⟨j.1 + 1, by omega⟩
      have hjr : j.1 + 1 < h := jr.2
      calc
        (R.newStrip j).plus = (R.newStrip jr).center := (R.new_overlap j hjr).2
        _ = (S.newStrip jr).center := by
          simpa [S, U, i, R] using FullFrame.tableau_column_new_center_eq_stepWindow F t jr
        _ = (S.newStrip j).plus := (S.newStrip_overlap j hjr).2.symm

/-- Every raw higher-block field in a literal frame cell agrees with the
cell generated from its operational readback time. -/
theorem FullFrame.tableau_raw_eq_toUniform_tileAt {w h : ℕ}
    (F : FullFrame w h) (t : Fin w) (j : Fin h) :
    let U :=
      PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
    let i := reverseColumn t
    tableauAt F.tiling i j = U.tileAt t j := by
  let U :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F
  let i : Fin w := reverseColumn t
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback F i
  let S := U.stepWindow t
  have hcomp := FullFrame.toUniform_stepWindow_components F t
  have hbits := FullFrame.tableau_column_bits_eq_toUniform F t j
  apply Subtype.ext
  apply TableauRaw.ext
  · calc
      (tableauAt F.tiling i j).1.old = R.oldStrip j := by
        symm
        simpa [R] using
          PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback_oldStrip F i j
      _ = (S.oldStrip j) := by
        simpa [S, U, i, R] using FullFrame.tableau_column_oldStrip_eq_stepWindow F t j
      _ = (U.tileAt t j).1.old := (U.tileAt_old t j).symm
  · calc
      (tableauAt F.tiling i j).1.new = R.newStrip j := by
        symm
        simpa [R] using
          PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback_newStrip F i j
      _ = (S.newStrip j) := by
        simpa [S, U, i, R] using FullFrame.tableau_column_newStrip_eq_stepWindow F t j
      _ = (U.tileAt t j).1.new := (U.tileAt_new t j).symm
  · exact hbits.1.trans (U.tileAt_bits t j).1.symm
  · exact hbits.2.1.trans (U.tileAt_bits t j).2.1.symm
  · exact hbits.2.2.1.trans (U.tileAt_bits t j).2.2.1.symm
  · exact hbits.2.2.2.trans (U.tileAt_bits t j).2.2.2.symm
  · have hsouth := FullFrame.tableau_column_south_token_forced F i j
    rw [hsouth, U.tileAt_southToken]
    have hright : S.headRightIndex =
        (⟨R.head.1 + 1, R.head_interior.2⟩ : Fin h) := by
      apply Fin.ext
      change S.head_index.1 + 1 = R.head.1 + 1
      rw [hcomp.2.2.2]
    change (if j = (⟨R.head.1 + 1, R.head_interior.2⟩ : Fin h) then
      some R.arrow else none) = if j = S.headRightIndex then some S.arrow else none
    rw [hright, hcomp.2.2.1]
  · have hnorth := FullFrame.tableau_column_north_token_forced F i j
    rw [hnorth, U.tileAt_northToken]
    change (if j = R.head then some R.arrow else none) =
      if j = S.head_index then some S.arrow else none
    rw [hcomp.2.2.1, hcomp.2.2.2]

/-- A geometric tableau cell is literally the generated higher-block tile at
its reversed chronological time.  The equality is an equality of the full
admissible tile subtypes, not merely of their horizontal colours. -/
theorem FullFrame.tableau_cell_eq_toUniform_tileAt {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    tableauAt F.tiling i j =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F).tileAt
        (UniformWindowedMStarRun.revTime i) j := by
  have hraw := FullFrame.tableau_raw_eq_toUniform_tileAt F
    (UniformWindowedMStarRun.revTime i) j
  rw [reverseColumn_revTime i] at hraw
  exact hraw

/-- The tableau projection of a literal full frame is recovered exactly by
reading it as a uniform operational run and regenerating its tableau. -/
theorem FullFrame.tableau_eq_toUniformWindowedRun_tableauTiling {w h : ℕ}
    (F : FullFrame w h) :
    F.tableau =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F).tableauTiling := by
  apply Subtype.ext
  funext i j
  change tableauAt F.tiling i j =
    (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F).tileAt
      (UniformWindowedMStarRun.revTime i) j
  exact FullFrame.tableau_cell_eq_toUniform_tileAt F i j

/-- Alias exposing the same final equality under the projection terminology
used by the full-frame coupling interface. -/
theorem FullFrame.tableauProjection_eq_roundtrip {w h : ℕ}
    (F : FullFrame w h) :
    tableauProjection F.tiling =
      (PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F).tableauTiling :=
  FullFrame.tableau_eq_toUniformWindowedRun_tableauTiling F

end PakFixedPolyomino.PakFullFrameTableauRoundtrip
