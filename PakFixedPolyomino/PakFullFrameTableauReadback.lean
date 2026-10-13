import PakFixedPolyomino.PakFullFrameRippleClassify
import PakFixedPolyomino.PakScannerColumnForms
import PakFixedPolyomino.HigherBlockTableauConcrete
import Mathlib.Tactic

/-!
# Tableau-only readback of a full frame

This module deliberately does not classify the scanner column.  The four
literal full-frame sides already force an operational higher-block history:
the south and north sentinels force one old head in every tableau column, and
the head tile carries the actual fixed-machine arrow and local transition.
Horizontal Wang matching then orders those steps from east (old) to west
(new).

The result below is a readback record, rather than a `FrameReadout` alias and
does not accept a run or a certificate as an argument.
-/

namespace PakFixedPolyomino.PakFullFrameTableauReadback

open PakMStarCouplingCorrectness

/-- The order bits at the literal south and north sentinels force a visible
old head in every tableau column. -/
theorem FullFrame.tableau_column_old_head_exists {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) :
    ∃ j : Fin h, (tableauAt F.tiling i j).1.old.center.isHead = true := by
  by_contra hheads
  push Not at hheads
  rcases (F.south_has_sentinel i).2 with
    ⟨_, _, _, _, hbottom, _, _⟩
  rcases (F.north_has_sentinel i).2 with
    ⟨_, _, _, _, htop, _, _⟩
  have hbits : ∀ j : Fin h,
      (tableauAt F.tiling i j).1.oldMinusBit = false ∧
        (tableauAt F.tiling i j).1.oldPlusBit = false := by
    intro j
    induction k : j.1 using Nat.strong_induction_on generalizing j with
    | h k ih =>
        have hminus : (tableauAt F.tiling i j).1.oldMinusBit = false := by
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
            exact hover.1.symm.trans hprev
        refine ⟨hminus, ?_⟩
        have hcenter : (tableauAt F.tiling i j).1.old.center.isHead = false := by
          cases hz : (tableauAt F.tiling i j).1.old.center.isHead <;>
            simp_all
        have hord := (tableauAt F.tiling i j).2.2.2.1
        have heq : (tableauAt F.tiling i j).1.oldMinusBit =
            (tableauAt F.tiling i j).1.oldPlusBit := by
          simpa [tableauOrdBit, hcenter] using hord
        rw [← heq]
        exact hminus
  let top : Fin h := northIndex F.height_pos
  have htopFalse := (hbits top).2
  rw [htop] at htopFalse
  simp at htopFalse

/-- The higher-block order track makes the read-back head unique. -/
theorem FullFrame.tableau_column_old_head_unique {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) {j k : Fin h}
    (hj : (tableauAt F.tiling i j).1.old.center.isHead = true)
    (hk : (tableauAt F.tiling i k).1.old.center.isHead = true) : j = k :=
  tableau_old_head_unique F.tiling i hj hk

/-- At the unique old head, an admissible higher-block tile exposes the
literal fixed-machine arrow, its source pair, and its `theta` transition. -/
theorem FullFrame.tableau_column_head_transition {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h)
    (hj : (tableauAt F.tiling i j).1.old.center.isHead = true) :
    ∃ a : Fixed.Arrow,
      (tableauAt F.tiling i j).1.southToken = none ∧
      (tableauAt F.tiling i j).1.northToken = some a ∧
      Fixed.Machine.source a =
        (tableauAt F.tiling i j).1.old.center.headSourceOf hj ∧
      Fixed.Machine.theta a (tableauAt F.tiling i j).1.old =
        some (tableauAt F.tiling i j).1.new := by
  have hcase := (tableauAt F.tiling i j).2.2.2.2.2
  simpa only [hj, ↓reduceDIte] using hcase

/-- A direct operational readback of one tableau column.  Its strips are the
literal higher-block configurations; the arrow and `theta` proof are read
from the unique head tile, not supplied by a scanner classification. -/
structure TableauColumnStepReadback {w h : ℕ} (F : FullFrame w h) (i : Fin w) where
  oldStrip : Fin h → CellTriple (TableauCell Fixed.State Fixed.Tape)
  newStrip : Fin h → CellTriple (TableauCell Fixed.State Fixed.Tape)
  old_overlap : ∀ (j : Fin h) (hj : j.1 + 1 < h),
    (oldStrip j).center = (oldStrip ⟨j.1 + 1, hj⟩).minus ∧
      (oldStrip j).plus = (oldStrip ⟨j.1 + 1, hj⟩).center
  new_overlap : ∀ (j : Fin h) (hj : j.1 + 1 < h),
    (newStrip j).center = (newStrip ⟨j.1 + 1, hj⟩).minus ∧
      (newStrip j).plus = (newStrip ⟨j.1 + 1, hj⟩).center
  head : Fin h
  head_is_head : (oldStrip head).center.isHead = true
  head_unique : ∀ j : Fin h, (oldStrip j).center.isHead = true → j = head
  arrow : Fixed.Arrow
  arrow_source : Fixed.Machine.source arrow =
    (oldStrip head).center.headSourceOf head_is_head
  theta : Fixed.Machine.theta arrow (oldStrip head) = some (newStrip head)
  passive_center : ∀ (j : Fin h),
    (oldStrip j).minus.isHead = false →
    (oldStrip j).center.isHead = false →
    (oldStrip j).plus.isHead = false →
    (newStrip j).center = (oldStrip j).center
  south_old_hash : (oldStrip ⟨0, F.height_pos⟩).minus = .plain .hash ∧
    (oldStrip ⟨0, F.height_pos⟩).center = .plain .hash
  north_old_hash : (oldStrip (northIndex F.height_pos)).center = .plain .hash ∧
    (oldStrip (northIndex F.height_pos)).plus = .plain .hash

namespace TableauColumnStepReadback

/-- The finite old strip, completed by literal hash outside the frame. -/
def oldTape {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (z : Int) : Fixed.Tape :=
  if hz : 0 ≤ z ∧ z < (h : Int) then
    OneTapeTableau.cellLetter (R.oldStrip ⟨z.toNat, by omega⟩).center
  else .hash

/-- The finite new strip, completed by literal hash outside the frame. -/
def newTape {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (z : Int) : Fixed.Tape :=
  if hz : 0 ≤ z ∧ z < (h : Int) then
    OneTapeTableau.cellLetter (R.newStrip ⟨z.toNat, by omega⟩).center
  else .hash

/-- The global pre-step configuration reconstructed from the old column
centres.  The geometric origin is fixed to zero. -/
def before {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : MStarConfig where
  state := (R.oldStrip R.head).center.headSourceOf R.head_is_head |>.1
  head := R.head.1
  tape := R.oldTape

/-- The candidate post-step configuration read from the new column centres.
The state and head are the literal target of the read arrow. -/
def after {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : MStarConfig where
  state := (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState
  head := FiniteOneTapeSemantics.moveHead
    (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move R.head.1
  tape := R.newTape

theorem oldTape_at {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (j : Fin h) :
    R.oldTape j.1 = OneTapeTableau.cellLetter (R.oldStrip j).center := by
  unfold oldTape
  have hj : 0 ≤ (j.1 : Int) ∧ (j.1 : Int) < (h : Int) := by omega
  rw [dif_pos hj]
  congr 2

theorem newTape_at {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (j : Fin h) :
    R.newTape j.1 = OneTapeTableau.cellLetter (R.newStrip j).center := by
  unfold newTape
  have hj : 0 ≤ (j.1 : Int) ∧ (j.1 : Int) < (h : Int) := by omega
  rw [dif_pos hj]
  congr 2

theorem oldTape_hash_outside {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (z : Int) (hz : z < 0 ∨ (h : Int) ≤ z) :
    R.oldTape z = .hash := by
  unfold oldTape
  apply dif_neg
  omega

theorem newTape_hash_outside {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) (z : Int) (hz : z < 0 ∨ (h : Int) ≤ z) :
    R.newTape z = .hash := by
  unfold newTape
  apply dif_neg
  omega

theorem head_interior {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) :
    0 < R.head.1 ∧ R.head.1 + 1 < h := by
  constructor
  · by_contra hzero
    have hzero' : R.head.1 = 0 := Nat.eq_zero_of_not_pos hzero
    have heq : R.head = (⟨0, F.height_pos⟩ : Fin h) := by
      apply Fin.ext
      exact hzero'
    have hplain := R.south_old_hash.2
    rw [← heq] at hplain
    have hhead := R.head_is_head
    rw [hplain] at hhead
    simp [TableauCell.isHead] at hhead
  · by_contra hlast
    have hval : R.head.1 = h - 1 := by omega
    have heq : R.head = northIndex F.height_pos := by
      apply Fin.ext
      simpa [northIndex] using hval
    have hplain := R.north_old_hash.1
    rw [← heq] at hplain
    have hhead := R.head_is_head
    rw [hplain] at hhead
    simp [TableauCell.isHead] at hhead

theorem before_source {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) :
    R.before.state = (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).sourceState ∧
      R.before.tape R.before.head =
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read := by
  have hsrc := R.arrow_source
  change (R.arrow.1.1.1, R.arrow.1.1.2) =
    (R.oldStrip R.head).center.headSourceOf R.head_is_head at hsrc
  have htape : R.before.tape R.before.head =
      OneTapeTableau.cellLetter (R.oldStrip R.head).center := by
    change R.oldTape R.head.1 = _
    exact R.oldTape_at R.head
  have hhead := R.head_is_head
  cases hcell : (R.oldStrip R.head).center with
  | plain x =>
      rw [hcell] at hhead
      simp [TableauCell.isHead] at hhead
  | head q x =>
      have hsourceOf : (R.oldStrip R.head).center.headSourceOf R.head_is_head =
          (q, x) :=
        PakMStarCouplingCorrectness.WindowedMStarStep.headSourceOf_eq_of_eq
          hcell R.head_is_head
      have hpair : (q, x) =
          ((FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).sourceState,
            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read) := by
        exact (hsrc.trans hsourceOf).symm
      constructor
      · change ((R.oldStrip R.head).center.headSourceOf R.head_is_head).1 = _
        rw [hsourceOf]
        exact congrArg Prod.fst hpair
      · calc
          R.before.tape R.before.head =
              OneTapeTableau.cellLetter (R.oldStrip R.head).center := htape
          _ = x := by simp [hcell, OneTapeTableau.cellLetter]
          _ = (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read :=
            congrArg Prod.snd hpair

theorem old_center_not_head_of_ne {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) {j : Fin h} (hj : j ≠ R.head) :
    (R.oldStrip j).center.isHead = false := by
  cases hbit : (R.oldStrip j).center.isHead with
  | false => rfl
  | true => exact (hj (R.head_unique j hbit)).elim

theorem passive_center_of_away_from_head {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) (j : Fin h)
    (hleft : j.1 = 0 ∨ j.1 - 1 ≠ R.head.1)
    (hcenter : j ≠ R.head)
    (hright : j.1 + 1 = h ∨ j.1 + 1 ≠ R.head.1) :
    (R.newStrip j).center = (R.oldStrip j).center := by
  apply R.passive_center j
  · by_cases hj0 : j.1 = 0
    · have hplain := R.south_old_hash.1
      have heq : j = (⟨0, F.height_pos⟩ : Fin h) := Fin.eq_of_val_eq hj0
      rw [← heq] at hplain
      rw [hplain]
      rfl
    · rcases hleft with hbad | hleft
      · exact (hj0 hbad).elim
      · let jp : Fin h := ⟨j.1 - 1, by omega⟩
        have hleft' : jp ≠ R.head := by
          intro heq
          apply hleft
          exact congrArg Fin.val heq
        have hjp : jp.1 + 1 < h := by
          dsimp [jp]
          omega
        have hover := R.old_overlap jp hjp
        have heq : (⟨jp.1 + 1, hjp⟩ : Fin h) = j := by
          apply Fin.ext
          dsimp [jp]
          omega
        rw [← heq, ← hover.1]
        exact R.old_center_not_head_of_ne hleft'
  · exact R.old_center_not_head_of_ne hcenter
  · by_cases hjtop : j.1 + 1 = h
    · have hplain := R.north_old_hash.2
      have hval : j.1 = h - 1 := by omega
      have heq : j = northIndex F.height_pos := by
        apply Fin.ext
        simpa [northIndex] using hval
      rw [← heq] at hplain
      rw [hplain]
      rfl
    · rcases hright with hbad | hright
      · exact (hjtop hbad).elim
      · let jn : Fin h := ⟨j.1 + 1, by omega⟩
        have hright' : jn ≠ R.head := by
          intro heq
          apply hright
          exact congrArg Fin.val heq
        have hjn : j.1 + 1 < h := jn.2
        have hover := R.old_overlap j hjn
        rw [hover.2]
        exact R.old_center_not_head_of_ne hright'

/- Rebuild the following theta projection lemmas in a separate green batch.
They are retained here as disabled proof notes so the last verified readback
interface remains compilable while the dependent transports are repaired.

theorem theta_head_writes_center {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) :
    OneTapeTableau.cellLetter (R.newStrip R.head).center =
      (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write := by
  have htheta := R.theta
  change OneTapeTableau.theta MStarOuterProgram.movable
    (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow)
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
      have hsourceOf : (R.oldStrip R.head).center.headSourceOf R.head_is_head =
          (q, x) :=
        PakMStarCouplingCorrectness.WindowedMStarStep.headSourceOf_eq_of_eq
          hcell R.head_is_head
      have hpair : (q, x) =
          ((FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).sourceState,
            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read) :=
        (hsrc.trans hsourceOf).symm
      have hstate : q =
          (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).sourceState :=
        congrArg Prod.fst hpair
      have hread : x =
          (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read :=
        congrArg Prod.snd hpair
      cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move with
      | left =>
          cases hm : (R.oldStrip R.head).minus with
          | plain m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
              have hnew := htheta
              have hcenter := congrArg CellTriple.center hnew
              exact (congrArg OneTapeTableau.cellLetter hcenter).symm.trans rfl
          | head qm m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          have hnew := htheta
          have hcenter := congrArg CellTriple.center hnew
          exact (congrArg OneTapeTableau.cellLetter hcenter).symm.trans rfl
      | right =>
          cases hp : (R.oldStrip R.head).plus with
          | plain p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta
              have hnew := htheta
              have hcenter := congrArg CellTriple.center hnew
              exact (congrArg OneTapeTableau.cellLetter hcenter).symm.trans rfl
          | head qp p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta

theorem theta_head_preserves_side_letters {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    OneTapeTableau.cellLetter (R.newStrip R.head).minus =
        OneTapeTableau.cellLetter (R.oldStrip R.head).minus ∧
      OneTapeTableau.cellLetter (R.newStrip R.head).plus =
        OneTapeTableau.cellLetter (R.oldStrip R.head).plus := by
  have htheta := R.theta
  change OneTapeTableau.theta MStarOuterProgram.movable
    (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow)
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
      have hsourceOf : (R.oldStrip R.head).center.headSourceOf R.head_is_head =
          (q, x) :=
        PakMStarCouplingCorrectness.WindowedMStarStep.headSourceOf_eq_of_eq
          hcell R.head_is_head
      have hpair : (q, x) =
          ((FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).sourceState,
            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).read) :=
        (hsrc.trans hsourceOf).symm
      have hstate := congrArg Prod.fst hpair
      have hread := congrArg Prod.snd hpair
      cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move with
      | left =>
          cases hm : (R.oldStrip R.head).minus with
          | plain m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
              rcases htheta with ⟨_, _, hnew⟩
              have hminus := congrArg CellTriple.minus hnew
              have hplus := congrArg CellTriple.plus hnew
              constructor
              · calc
                  OneTapeTableau.cellLetter (R.newStrip R.head).minus =
                      OneTapeTableau.cellLetter
                        ((show CellTriple (TableauCell Fixed.State Fixed.Tape) from
                          { minus := TableauCell.head
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState m
                            center := TableauCell.plain
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write
                            plus := (R.oldStrip R.head).plus }).minus) :=
                    (congrArg OneTapeTableau.cellLetter hminus).symm
                  _ = OneTapeTableau.cellLetter (R.oldStrip R.head).minus := by
                    simp [hm, OneTapeTableau.cellLetter]
              · calc
                  OneTapeTableau.cellLetter (R.newStrip R.head).plus =
                      OneTapeTableau.cellLetter
                        ((show CellTriple (TableauCell Fixed.State Fixed.Tape) from
                          { minus := TableauCell.head
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState m
                            center := TableauCell.plain
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write
                            plus := (R.oldStrip R.head).plus }).plus) :=
                    (congrArg OneTapeTableau.cellLetter hplus).symm
                  _ = OneTapeTableau.cellLetter (R.oldStrip R.head).plus := rfl
          | head qm m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          rcases htheta with ⟨_, hnew⟩
          have hminus := congrArg CellTriple.minus hnew
          have hplus := congrArg CellTriple.plus hnew
          constructor
          · exact (congrArg OneTapeTableau.cellLetter hminus).symm
          · exact (congrArg OneTapeTableau.cellLetter hplus).symm
      | right =>
          cases hp : (R.oldStrip R.head).plus with
          | plain p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta
              rcases htheta with ⟨_, _, hnew⟩
              have hminus := congrArg CellTriple.minus hnew
              have hplus := congrArg CellTriple.plus hnew
              constructor
              · calc
                  OneTapeTableau.cellLetter (R.newStrip R.head).minus =
                      OneTapeTableau.cellLetter
                        ((show CellTriple (TableauCell Fixed.State Fixed.Tape) from
                          { minus := (R.oldStrip R.head).minus
                            center := TableauCell.plain
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write
                            plus := TableauCell.head
                              (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState p }).minus) :=
                    (congrArg OneTapeTableau.cellLetter hminus).symm
                  _ = OneTapeTableau.cellLetter (R.oldStrip R.head).minus := rfl
              · calc
                  OneTapeTableau.cellLetter (R.newStrip R.head).plus =
                      OneTapeTableau.cellLetter
                        ((show CellTriple (TableauCell Fixed.State Fixed.Tape) from
                          { minus := (R.oldStrip R.head).minus
                            center := TableauCell.plain
                            (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write
                            plus := TableauCell.head
                              (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState p }).plus) :=
                    (congrArg OneTapeTableau.cellLetter hplus).symm
                  _ = OneTapeTableau.cellLetter (R.oldStrip R.head).plus := by
                    simp [hp, OneTapeTableau.cellLetter]
          | head qp p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta

-/

/-- The semantic target associated with the recovered old configuration and
arrow.  The following lemma isolates the last remaining identification needed
to show that `after` is this target: equality of the read new tape with the
single written old tape. -/
def writtenAfter {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : MStarConfig where
  state := (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).targetState
  head := FiniteOneTapeSemantics.moveHead
    (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move R.before.head
  tape := FiniteOneTapeSemantics.writtenTape R.before
    (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write

theorem step_eq_writtenAfter_of_movable {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i)
    (hmovable : MStarOuterProgram.movable
      ((FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        (FiniteOneTapeSemantics.moveHead
          (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move
          R.before.head)) = true) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      R.before R.arrow = some R.writtenAfter := by
  unfold FiniteOneTapeSemantics.step
  dsimp only
  have hsource := R.before_source
  simp [hsource.1, hsource.2, hmovable, writtenAfter]

/- The pointwise full-tape reconstruction below depends on the disabled theta
projection batch above and is re-enabled only after that batch is green.

theorem newTape_eq_written_at_head {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    R.newTape R.before.head =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        R.before.head := by
  change R.newTape R.head.1 = _
  calc
    R.newTape R.head.1 = OneTapeTableau.cellLetter (R.newStrip R.head).center :=
      R.newTape_at R.head
    _ = (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write :=
      R.theta_head_writes_center
    _ = (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        R.before.head := by
      simp [FiniteOneTapeSemantics.writtenTape]

theorem newTape_eq_written_at_head_left {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    let left : Fin h := ⟨R.head.1 - 1, by
      have hinterior := R.head_interior
      omega⟩
    R.newTape left.1 =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        left.1 := by
  let left : Fin h := ⟨R.head.1 - 1, by
    have hinterior := R.head_interior
    omega⟩
  have hnext : left.1 + 1 < h := by
    change R.head.1 - 1 + 1 < h
    have hinterior := R.head_interior
    omega
  have heq : (⟨left.1 + 1, hnext⟩ : Fin h) = R.head := by
    apply Fin.ext
    change R.head.1 - 1 + 1 = R.head.1
    have hinterior := R.head_interior
    omega
  have hnew := R.new_overlap left hnext |>.1
  have hold := R.old_overlap left hnext |>.1
  have hne : R.before.head ≠ left.1 := by
    change (R.head.1 : Int) ≠ (R.head.1 - 1 : ℕ)
    have hinterior := R.head_interior
    omega
  calc
    R.newTape left.1 = OneTapeTableau.cellLetter (R.newStrip left).center :=
      R.newTape_at left
    _ = OneTapeTableau.cellLetter (R.newStrip R.head).minus := by
      exact (congrArg OneTapeTableau.cellLetter hnew).trans
        (by rw [heq])
    _ = OneTapeTableau.cellLetter (R.oldStrip R.head).minus :=
      R.theta_head_preserves_side_letters.1
    _ = OneTapeTableau.cellLetter (R.oldStrip left).center := by
      exact ((congrArg OneTapeTableau.cellLetter hold).trans
        (by rw [heq])).symm
    _ = R.oldTape left.1 := (R.oldTape_at left).symm
    _ = (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        left.1 := by
      have hne' : left.1 ≠ R.before.head := Ne.symm hne
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne']

theorem newTape_eq_written_at_head_right {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
    R.newTape right.1 =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        right.1 := by
  let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
  have hnext : R.head.1 + 1 < h := (R.head_interior).2
  have hne : R.before.head ≠ right.1 := by
    change (R.head.1 : Int) ≠ (R.head.1 + 1 : ℕ)
    omega
  have hnew := R.new_overlap R.head hnext |>.2
  have hold := R.old_overlap R.head hnext |>.2
  calc
    R.newTape right.1 = OneTapeTableau.cellLetter (R.newStrip right).center :=
      R.newTape_at right
    _ = OneTapeTableau.cellLetter (R.newStrip R.head).plus := by
      exact (congrArg OneTapeTableau.cellLetter hnew).symm
    _ = OneTapeTableau.cellLetter (R.oldStrip R.head).plus :=
      R.theta_head_preserves_side_letters.2
    _ = OneTapeTableau.cellLetter (R.oldStrip right).center := by
      exact congrArg OneTapeTableau.cellLetter hold
    _ = R.oldTape right.1 := (R.oldTape_at right).symm
    _ = (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        right.1 := by
      have hne' : right.1 ≠ R.before.head := Ne.symm hne
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne']

theorem newTape_eq_written_at_away {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) (j : Fin h)
    (hleft : j.1 = 0 ∨ j.1 - 1 ≠ R.head.1)
    (hcenter : j ≠ R.head)
    (hright : j.1 + 1 = h ∨ j.1 + 1 ≠ R.head.1) :
    R.newTape j.1 =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        j.1 := by
  have hne : R.before.head ≠ j.1 := by
    change (R.head.1 : Int) ≠ (j.1 : ℕ)
    intro heq
    apply hcenter
    apply Fin.ext
    exact_mod_cast heq.symm
  calc
    R.newTape j.1 = OneTapeTableau.cellLetter (R.newStrip j).center :=
      R.newTape_at j
    _ = OneTapeTableau.cellLetter (R.oldStrip j).center :=
      congrArg OneTapeTableau.cellLetter
        (R.passive_center_of_away_from_head j hleft hcenter hright)
    _ = R.oldTape j.1 := (R.oldTape_at j).symm
    _ = (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        j.1 := by
      have hne' : j.1 ≠ R.before.head := Ne.symm hne
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne']

-/

end TableauColumnStepReadback

/-- Read a genuine higher-block operational step from any full-frame column.
No run, scanner-form certificate, or `FrameReadout` is an input. -/
noncomputable def FullFrame.tableau_column_readback {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) : TableauColumnStepReadback F i := by
  let head : Fin h := Classical.choose (tableau_column_old_head_exists F i)
  have hhead : (tableauAt F.tiling i head).1.old.center.isHead = true :=
    Classical.choose_spec (tableau_column_old_head_exists F i)
  let transition := tableau_column_head_transition F i head hhead
  let a : Fixed.Arrow := Classical.choose transition
  have htransition := Classical.choose_spec transition
  exact
    { oldStrip := fun j => (tableauAt F.tiling i j).1.old
      newStrip := fun j => (tableauAt F.tiling i j).1.new
      old_overlap := fun j hj => tableau_old_overlap F.tiling i j hj
      new_overlap := fun j hj => tableau_new_overlap F.tiling i j hj
      head := head
      head_is_head := hhead
      head_unique := by
        intro j hj
        exact tableau_column_old_head_unique F i hj hhead
      arrow := a
      arrow_source := htransition.2.2.1
      theta := htransition.2.2.2
      passive_center := by
        intro j hm hc hp
        exact HigherBlockTableau.new_center_eq_old_of_no_head Fixed.Machine
          (tableauAt F.tiling i j) hm hc hp
      south_old_hash := by
        rcases (F.south_has_sentinel i).2 with
          ⟨hsm, hsc, _, _, _, _, _⟩
        exact ⟨hsm, hsc⟩
      north_old_hash := by
        rcases (F.north_has_sentinel i).2 with
          ⟨hnc, hnp, _, _, _, _, _⟩
        exact ⟨hnc, hnp⟩ }

@[simp] theorem FullFrame.tableau_column_readback_oldStrip {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    (tableau_column_readback F i).oldStrip j =
      (tableauAt F.tiling i j).1.old := by
  simp [tableau_column_readback]

@[simp] theorem FullFrame.tableau_column_readback_newStrip {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (j : Fin h) :
    (tableau_column_readback F i).newStrip j =
      (tableauAt F.tiling i j).1.new := by
  simp [tableau_column_readback]

/-- Adjacent tableau columns compose in the Wang direction: the old strip of
the eastern column is the new strip of its western neighbour.  Thus reading
columns from east to west gives chronological old-to-new composition. -/
theorem FullFrame.adjacent_tableau_columns_old_new {w h : ℕ}
    (F : FullFrame w h) (i : Fin w) (hi : i.1 + 1 < w) (j : Fin h) :
    (tableauAt F.tiling i j).1.old =
      (tableauAt F.tiling ⟨i.1 + 1, hi⟩ j).1.new := by
  have hmatch := (tableauProjection F.tiling).2.1 i j hi
  change (tableauAt F.tiling i j).1.old =
    (tableauAt F.tiling ⟨i.1 + 1, hi⟩ j).1.new at hmatch
  exact hmatch

/-- The literal west accepting boundary gives the terminal-state readback at
every visible new head of its final tableau strip. -/
theorem FullFrame.west_new_head_is_accept {w h : ℕ}
    (F : FullFrame w h) (j : Fin h) {q : Fixed.State} {a : Fixed.Tape}
    (hhead : (tableauAt F.tiling ⟨0, F.width_pos⟩ j).1.new.center = .head q a) :
    q = MStarOuterProgram.State.accept := by
  have haccept := (F.west_accepts j).2.1
  unfold PakCouplingGenerated.acceptingWindow
    PakCouplingGenerated.cellAccepting at haccept
  rw [hhead] at haccept
  exact haccept.2.1

end PakFixedPolyomino.PakFullFrameTableauReadback
