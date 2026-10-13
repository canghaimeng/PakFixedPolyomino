import PakFixedPolyomino.PakFullFrameTableauReadback

namespace PakFixedPolyomino.PakFullFrameTableauReadback

open PakMStarCouplingCorrectness

namespace TableauColumnStepReadback

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
        WindowedMStarStep.headSourceOf_eq_of_eq hcell R.head_is_head
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
              have hnew := htheta.2
              have hcenter := congrArg CellTriple.center hnew
              exact (congrArg OneTapeTableau.cellLetter hcenter).symm.trans rfl
          | head qm m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          have hnew := htheta.2
          have hcenter := congrArg CellTriple.center hnew
          exact (congrArg OneTapeTableau.cellLetter hcenter).symm.trans rfl
      | right =>
          cases hp : (R.oldStrip R.head).plus with
          | plain p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta
              have hnew := htheta.2
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
        WindowedMStarStep.headSourceOf_eq_of_eq hcell R.head_is_head
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
              have hnew := htheta.2
              have hminus := congrArg CellTriple.minus hnew
              have hplus := congrArg CellTriple.plus hnew
              constructor
              · exact (congrArg OneTapeTableau.cellLetter hminus).symm.trans
                  (by simp [OneTapeTableau.cellLetter])
              · exact (congrArg OneTapeTableau.cellLetter hplus).symm
          | head qm m =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hm] at htheta
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          have hnew := htheta.2
          constructor
          · exact (congrArg OneTapeTableau.cellLetter
              (congrArg CellTriple.minus hnew)).symm
          · exact (congrArg OneTapeTableau.cellLetter
              (congrArg CellTriple.plus hnew)).symm
      | right =>
          cases hp : (R.oldStrip R.head).plus with
          | plain p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta
              have hnew := htheta.2
              have hminus := congrArg CellTriple.minus hnew
              have hplus := congrArg CellTriple.plus hnew
              constructor
              · exact (congrArg OneTapeTableau.cellLetter hminus).symm
              · exact (congrArg OneTapeTableau.cellLetter hplus).symm.trans
                  (by simp [OneTapeTableau.cellLetter])
          | head qp p =>
              simp [OneTapeTableau.theta, hcell, hstate, hread, hmove, hp] at htheta

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
  have hne : (left.1 : Int) ≠ (R.head.1 : Int) := by
    change ((R.head.1 - 1 : ℕ) : Int) ≠ R.head.1
    have hinterior := R.head_interior
    omega
  calc
    R.newTape left.1 = OneTapeTableau.cellLetter (R.newStrip left).center :=
      R.newTape_at left
    _ = OneTapeTableau.cellLetter (R.newStrip R.head).minus := by
      exact (congrArg OneTapeTableau.cellLetter hnew).trans (by rw [heq])
    _ = OneTapeTableau.cellLetter (R.oldStrip R.head).minus :=
      R.theta_head_preserves_side_letters.1
    _ = OneTapeTableau.cellLetter (R.oldStrip left).center := by
      exact ((congrArg OneTapeTableau.cellLetter hold).trans (by rw [heq])).symm
    _ = R.oldTape left.1 := (R.oldTape_at left).symm
    _ = (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        left.1 := by
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne]

theorem newTape_eq_written_at_head_right {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
    R.newTape right.1 =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        right.1 := by
  let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
  have hnext : R.head.1 + 1 < h := (R.head_interior).2
  have hne : (right.1 : Int) ≠ (R.head.1 : Int) := by
    change ((R.head.1 + 1 : ℕ) : Int) ≠ R.head.1
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
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne]

theorem newTape_eq_written_at_away {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) (j : Fin h)
    (hleft : j.1 = 0 ∨ j.1 - 1 ≠ R.head.1)
    (hcenter : j ≠ R.head)
    (hright : j.1 + 1 = h ∨ j.1 + 1 ≠ R.head.1) :
    R.newTape j.1 =
      (FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        j.1 := by
  have hne : (j.1 : Int) ≠ (R.head.1 : Int) := by
    intro heq
    apply hcenter
    apply Fin.ext
    exact_mod_cast heq
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
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, before, hne]

theorem newTape_eq_writtenTape {w h : ℕ} {F : FullFrame w h}
    {i : Fin w} (R : TableauColumnStepReadback F i) :
    R.newTape = FiniteOneTapeSemantics.writtenTape R.before
      (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write := by
  funext z
  by_cases hz : z < 0 ∨ (h : Int) ≤ z
  · have hne : z ≠ (R.head.1 : Int) := by
      intro heq
      have hhead : 0 ≤ (R.head.1 : Int) ∧ (R.head.1 : Int) < (h : Int) := by
        omega
      omega
    simp [R.newTape_hash_outside z hz, FiniteOneTapeSemantics.writtenTape,
      Function.update, before, hne, R.oldTape_hash_outside z hz]
  · push Not at hz
    let j : Fin h := ⟨z.toNat, by omega⟩
    have hzj : (j.1 : Int) = z := by
      dsimp [j]
      exact Int.toNat_of_nonneg hz.1
    rw [← hzj]
    by_cases hcenter : j = R.head
    · rw [hcenter]
      exact R.newTape_eq_written_at_head
    by_cases hleft : j.1 + 1 = R.head.1
    · have hj : j = (⟨R.head.1 - 1, by
          have hinterior := R.head_interior
          omega⟩ : Fin h) := by
        apply Fin.ext
        change j.1 = R.head.1 - 1
        omega
      rw [hj]
      exact R.newTape_eq_written_at_head_left
    by_cases hright : R.head.1 + 1 = j.1
    · have hj : j = (⟨R.head.1 + 1, (R.head_interior).2⟩ : Fin h) := by
        apply Fin.ext
        change j.1 = R.head.1 + 1
        omega
      rw [hj]
      exact R.newTape_eq_written_at_head_right
    · have hjleft : j.1 = 0 ∨ j.1 - 1 ≠ R.head.1 := by
        by_cases hjzero : j.1 = 0
        · exact Or.inl hjzero
        · right
          intro heq
          apply hleft
          omega
      have hjright : j.1 + 1 = h ∨ j.1 + 1 ≠ R.head.1 := by
        by_cases hjtop : j.1 + 1 = h
        · exact Or.inl hjtop
        · right
          intro heq
          apply hright
          omega
      exact R.newTape_eq_written_at_away j hjleft hcenter hjright

theorem theta_movable_after {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) :
    MStarOuterProgram.movable
      ((FiniteOneTapeSemantics.writtenTape R.before
        (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).write)
        (FiniteOneTapeSemantics.moveHead
          (FiniteOneTapeProgram.transition MStarULogAssembly.program R.arrow).move
          R.before.head)) = true := by
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
      have hsourceOf : (R.oldStrip R.head).center.headSourceOf R.head_is_head =
          (q, x) :=
        WindowedMStarStep.headSourceOf_eq_of_eq hcell R.head_is_head
      have hpair : (q, x) = (tr.sourceState, tr.read) :=
        (hsrc.trans hsourceOf).symm
      have hstate : q = tr.sourceState := congrArg Prod.fst hpair
      have hread : x = tr.read := congrArg Prod.snd hpair
      cases hmove : tr.move with
      | left =>
          obtain ⟨b, hminus, hmovable⟩ :=
            OneTapeTableau.theta_left_target_movable MStarOuterProgram.movable tr
              (R.oldStrip R.head) (R.newStrip R.head) hmove htheta
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
          have hold := R.old_overlap left hnext |>.1
          have hletter : R.oldTape left.1 = b := by
            calc
              R.oldTape left.1 = OneTapeTableau.cellLetter (R.oldStrip left).center :=
                R.oldTape_at left
              _ = OneTapeTableau.cellLetter (R.oldStrip R.head).minus := by
                exact (congrArg OneTapeTableau.cellLetter hold).trans (by rw [heq])
              _ = b := by simp [hminus, OneTapeTableau.cellLetter]
          have hleftpos : (left.1 : Int) = (R.head.1 : Int) - 1 := by
            dsimp [left]
            have hinterior := R.head_interior
            omega
          have hvalue : R.oldTape ((R.head.1 : Int) - 1) = b := by
            rw [← hleftpos]
            exact hletter
          have hne : ((R.head.1 : Int) - 1) ≠ R.head.1 := by omega
          simpa [tr, FiniteOneTapeSemantics.writtenTape,
            FiniteOneTapeSemantics.moveHead, Function.update, before, left, hne,
            hvalue] using hmovable
      | stay =>
          simp [OneTapeTableau.theta, hcell, hstate, hread, hmove] at htheta
          simpa [tr, FiniteOneTapeSemantics.writtenTape,
            FiniteOneTapeSemantics.moveHead, before] using htheta.1
      | right =>
          obtain ⟨b, hplus, hmovable⟩ :=
            OneTapeTableau.theta_right_target_movable MStarOuterProgram.movable tr
              (R.oldStrip R.head) (R.newStrip R.head) hmove htheta
          let right : Fin h := ⟨R.head.1 + 1, (R.head_interior).2⟩
          have hnext : R.head.1 + 1 < h := (R.head_interior).2
          have hold := R.old_overlap R.head hnext |>.2
          have hletter : R.oldTape right.1 = b := by
            calc
              R.oldTape right.1 = OneTapeTableau.cellLetter (R.oldStrip right).center :=
                R.oldTape_at right
              _ = OneTapeTableau.cellLetter (R.oldStrip R.head).plus := by
                exact (congrArg OneTapeTableau.cellLetter hold).symm
              _ = b := by simp [hplus, OneTapeTableau.cellLetter]
          have hrightpos : (right.1 : Int) = (R.head.1 : Int) + 1 := by
            dsimp [right]
          have hvalue : R.oldTape ((R.head.1 : Int) + 1) = b := by
            rw [← hrightpos]
            exact hletter
          have hne : ((R.head.1 : Int) + 1) ≠ R.head.1 := by omega
          simpa [tr, FiniteOneTapeSemantics.writtenTape,
            FiniteOneTapeSemantics.moveHead, Function.update, before, right, hne,
            hvalue] using hmovable

theorem after_eq_writtenAfter {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : R.after = R.writtenAfter := by
  unfold after writtenAfter
  dsimp [before]
  congr
  exact R.newTape_eq_writtenTape

theorem step_eq_after {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      R.before R.arrow = some R.after := by
  rw [R.after_eq_writtenAfter]
  exact R.step_eq_writtenAfter_of_movable R.theta_movable_after

/-- The literal column readback is a genuine finite operational step on its
full-height tape window. -/
def toMStarStep {w h : ℕ} {F : FullFrame w h} {i : Fin w}
    (R : TableauColumnStepReadback F i) : WindowedMStarStep h where
  before := R.before
  after := R.after
  arrow := R.arrow
  executes := R.step_eq_after
  origin := 0
  width_ge_three := by
    have hinterior := R.head_interior
    omega
  head_index := R.head
  head_eq := by
    change (R.head.1 : Int) = 0 + R.head.1
    omega
  head_interior_left := R.head_interior.1
  head_interior_right := R.head_interior.2
  before_hash_outside := by
    intro z hz
    change R.oldTape z = .hash
    apply R.oldTape_hash_outside z
    simpa using hz
  after_hash_outside := by
    intro z hz
    change R.newTape z = .hash
    apply R.newTape_hash_outside z
    simpa using hz

end TableauColumnStepReadback
end PakFixedPolyomino.PakFullFrameTableauReadback
