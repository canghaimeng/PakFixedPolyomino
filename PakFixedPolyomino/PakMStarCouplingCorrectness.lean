import PakFixedPolyomino.FixedPakPolyomino
import PakFixedPolyomino.FiniteOneTapeSemantics
import Mathlib.Tactic

/-!
# Fixed M-star coupling: full-frame extraction

The register target contains a private dummy mode.  This module isolates the
computation mode and proves the direction already justified by the literal
local tables: a coupled full frame projects to a higher-block tableau for the
fixed M-star machine.  The reverse direction needs a genuinely global
frame-filling theorem and is not assumed here.
-/

namespace PakFixedPolyomino.PakMStarCouplingCorrectness

open PakFixedPolyomino

namespace Fixed

abbrev State := FixedPakPolyomino.State
abbrev Tape := FixedPakPolyomino.Tape
abbrev Arrow := FixedPakPolyomino.Arrow
abbrev Q := FixedPakPolyomino.Q
abbrev Machine := FixedPakPolyomino.Machine
abbrev Tracks := FixedPakPolyomino.Tracks
abbrev Coupled := FixedPakPolyomino.Coupled
noncomputable abbrev wangTile := FixedPakPolyomino.wangTile

end Fixed

noncomputable section

/-- Configurations for the literal fixed outer M-star program. -/
abbrev MStarConfig :=
  FiniteOneTapeSemantics.Config MStarULogAssembly.State MStarULogAssembly.Tape

/-- A genuinely finite accepting branch of the fixed program, from a supplied
configuration.  The source development intentionally has no globally chosen
input configuration at this layer. -/
abbrev MStarAcceptingRun (start : MStarConfig) (n : ℕ) :=
  FiniteOneTapeSemantics.AcceptingBranch MStarULogAssembly.program
    MStarOuterProgram.movable MStarOuterProgram.State.accept start n

/-- The finite execution history obtained by evaluating every prefix of an
accepting branch. Failed prefixes are retained as Option.none; a valid
accepting branch has a successful final prefix, proved below. -/
def MStarAcceptingRun.history {start : MStarConfig} {n : ℕ}
    (run : MStarAcceptingRun start n) : Fin (n + 1) → Option MStarConfig :=
  fun k =>
    FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable
      (List.take k.1 (List.ofFn run.1)) start

theorem MStarAcceptingRun.history_last {start : MStarConfig} {n : ℕ}
    (run : MStarAcceptingRun start n) :
    ∃ out, run.history ⟨n, Nat.lt_succ_self n⟩ = some out ∧
      out.state = MStarOuterProgram.State.accept := by
  rcases run.2 with ⟨out, hout, haccept⟩
  refine ⟨out, ?_, haccept⟩
  have htake : List.take n (List.ofFn run.1) = List.ofFn run.1 := by
    rw [List.take_eq_self_iff]
    simp
  simpa [MStarAcceptingRun.history, FiniteOneTapeSemantics.branchResult, htake]
    using hout

/-- Turn one certified centre-head transition of the fixed M-star program into
an admissible higher-block tableau tile. This is a concrete local
history-to-tableau constructor; the missing global compiler is only the
finite spatial-window selection for an entire run. -/
def fixedCenteredStepTile (a : Fixed.Arrow)
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold : tripleHeadCount old ≤ 1) (hnew : tripleHeadCount new ≤ 1)
    (hcenter : old.center.isHead = true)
    (hsource : Fixed.Machine.source a = old.center.headSourceOf hcenter)
    (htheta : Fixed.Machine.theta a old = some new) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  ⟨{ old := old
     new := new
     oldMinusBit := false
     oldPlusBit := true
     newMinusBit := false
     newPlusBit := new.center.isHead
     southToken := none
     northToken := some a }, by
    refine ⟨hold, hnew, ?_, ?_, ?_⟩
    · simp [tableauOrdBit, hcenter]
    · cases new.center <;> simp [tableauOrdBit, TableauCell.isHead]
    · simp only [hcenter, ↓reduceDIte]
      exact ⟨a, True.intro, rfl, hsource, htheta⟩⟩

theorem fixedCenteredStepTile_old (a : Fixed.Arrow)
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold hnew hcenter hsource htheta) :
    (fixedCenteredStepTile a old new hold hnew hcenter hsource htheta).1.old = old := rfl

theorem fixedCenteredStepTile_new (a : Fixed.Arrow)
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold hnew hcenter hsource htheta) :
    (fixedCenteredStepTile a old new hold hnew hcenter hsource htheta).1.new = new := rfl

/-- Construct the higher-block tile immediately to the right of a fixed
program head. -/
def fixedLeftHeadStepTile (a : Fixed.Arrow)
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold : tripleHeadCount old ≤ 1) (hnew : tripleHeadCount new ≤ 1)
    (hcenter : old.center.isHead = false) (hminus : old.minus.isHead = true)
    (hsource : Fixed.Machine.source a = old.minus.headSourceOf hminus)
    (hupdate : new.center = Fixed.Machine.rightUpdate a old.center) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  ⟨{ old := old
     new := new
     oldMinusBit := false
     oldPlusBit := false
     newMinusBit := false
     newPlusBit := new.center.isHead
     southToken := some a
     northToken := none }, by
    refine ⟨hold, hnew, ?_, ?_, ?_⟩
    · simp [tableauOrdBit, hcenter]
    · cases new.center <;> simp [tableauOrdBit, TableauCell.isHead]
    · simp only [hcenter, Bool.false_eq_true, ↓reduceDIte, hminus]
      exact ⟨a, rfl, True.intro, hsource, hupdate⟩⟩

/-- Construct the higher-block tile immediately to the left of a fixed
program head. -/
def fixedRightHeadStepTile (a : Fixed.Arrow)
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold : tripleHeadCount old ≤ 1) (hnew : tripleHeadCount new ≤ 1)
    (hcenter : old.center.isHead = false) (hminus : old.minus.isHead = false)
    (hplus : old.plus.isHead = true)
    (hsource : Fixed.Machine.source a = old.plus.headSourceOf hplus)
    (hupdate : new.center = Fixed.Machine.leftUpdate a old.center) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  ⟨{ old := old
     new := new
     oldMinusBit := false
     oldPlusBit := false
     newMinusBit := false
     newPlusBit := new.center.isHead
     southToken := none
     northToken := none }, by
    refine ⟨hold, hnew, ?_, ?_, ?_⟩
    · simp [tableauOrdBit, hcenter]
    · cases new.center <;> simp [tableauOrdBit, TableauCell.isHead]
    · simp only [hcenter, Bool.false_eq_true, ↓reduceDIte, hminus,
        Bool.false_eq_true, hplus]
      exact ⟨True.intro, True.intro, ⟨a, hsource, hupdate⟩⟩⟩

/-- Construct a fixed-program higher-block tile whose visible old window is
head-free, so its centre is copied unchanged. -/
def fixedPassiveTile
    (old new : CellTriple (TableauCell Fixed.State Fixed.Tape))
    (hold : tripleHeadCount old ≤ 1) (hnew : tripleHeadCount new ≤ 1)
    (hminus : old.minus.isHead = false) (hcenter : old.center.isHead = false)
    (hplus : old.plus.isHead = false) (hcopy : new.center = old.center) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  ⟨{ old := old
     new := new
     oldMinusBit := false
     oldPlusBit := false
     newMinusBit := false
     newPlusBit := new.center.isHead
     southToken := none
     northToken := none }, by
    refine ⟨hold, hnew, ?_, ?_, ?_⟩
    · simp [tableauOrdBit, hcenter]
    · cases new.center <;> simp [tableauOrdBit, TableauCell.isHead]
    · simp only [hcenter, Bool.false_eq_true, ↓reduceDIte, hminus,
        Bool.false_eq_true, hplus]
      exact ⟨True.intro, True.intro, hcopy⟩⟩

/-- A finite spatial window around one genuine operational step of the fixed
program. The window is not a tableau assumption: it consists of concrete
configurations, one labelled semantic step, an explicit integer origin, and
the assertion that the tape is hash outside the finite interval. -/
structure WindowedMStarStep (width : ℕ) where
  before : MStarConfig
  after : MStarConfig
  arrow : Fixed.Arrow
  executes :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      before arrow = some after
  origin : Int
  width_ge_three : 3 ≤ width
  head_index : Fin width
  head_eq : before.head = origin + head_index.1
  head_interior_left : 0 < head_index.1
  head_interior_right : head_index.1 + 1 < width
  before_hash_outside :
    ∀ z : Int, z < origin ∨ origin + width ≤ z → before.tape z = .hash
  after_hash_outside :
    ∀ z : Int, z < origin ∨ origin + width ≤ z → after.tape z = .hash

namespace WindowedMStarStep

def position {width : ℕ} (S : WindowedMStarStep width) (j : Fin width) : Int :=
  S.origin + j.1

def cell {width : ℕ} (S : WindowedMStarStep width) (c : MStarConfig)
    (z : Int) : TableauCell Fixed.State Fixed.Tape :=
  if z = c.head then .head c.state (c.tape z) else .plain (c.tape z)

def triple {width : ℕ} (S : WindowedMStarStep width) (c : MStarConfig)
    (j : Fin width) : CellTriple (TableauCell Fixed.State Fixed.Tape) :=
  { minus := S.cell c (S.position j - 1)
    center := S.cell c (S.position j)
    plus := S.cell c (S.position j + 1) }

/-- The old and new finite radius-one window strips of a single operational
step. They are the concrete spatial input to the four local tile
constructors. -/
def oldStrip {width : ℕ} (S : WindowedMStarStep width) :
    Fin width → CellTriple (TableauCell Fixed.State Fixed.Tape) :=
  S.triple S.before

def newStrip {width : ℕ} (S : WindowedMStarStep width) :
    Fin width → CellTriple (TableauCell Fixed.State Fixed.Tape) :=
  S.triple S.after

theorem cell_isHead_iff {width : ℕ} (S : WindowedMStarStep width)
    (c : MStarConfig) (z : Int) :
    (S.cell c z).isHead = true ↔ z = c.head := by
  unfold cell
  split <;> simp_all [TableauCell.isHead]

/-- The three cells in a window see at most the one physical head of a
configuration. -/
theorem triple_head_count_le_one {width : ℕ} (S : WindowedMStarStep width)
    (c : MStarConfig) (j : Fin width) :
    tripleHeadCount (S.triple c j) ≤ 1 := by
  by_cases hm : S.position j - 1 = c.head
  · have hc : S.position j ≠ c.head := by omega
    have hp : S.position j + 1 ≠ c.head := by omega
    simp [tripleHeadCount, triple, cell, TableauCell.isHead, hm, hc, hp]
  · by_cases hc : S.position j = c.head
    · have hp : S.position j + 1 ≠ c.head := by omega
      simp [tripleHeadCount, triple, cell, TableauCell.isHead, hm, hc, hp]
    · have hp : S.position j + 1 = c.head ∨ S.position j + 1 ≠ c.head :=
        em (S.position j + 1 = c.head)
      cases hp with
      | inl hp =>
          simp [tripleHeadCount, triple, cell, TableauCell.isHead, hm, hc, hp]
      | inr hp =>
          simp [tripleHeadCount, triple, cell, TableauCell.isHead, hm, hc, hp]

theorem triple_old_overlap {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hj : j.1 + 1 < width) :
    (S.triple S.before j).center =
        (S.triple S.before ⟨j.1 + 1, hj⟩).minus ∧
      (S.triple S.before j).plus =
        (S.triple S.before ⟨j.1 + 1, hj⟩).center := by
  constructor
  · change S.cell S.before (S.origin + (j.1 : Int)) =
      S.cell S.before (S.origin + ((j.1 + 1 : ℕ) : Int) - 1)
    congr 1
    push_cast
    ring
  · change S.cell S.before (S.origin + (j.1 : Int) + 1) =
      S.cell S.before (S.origin + ((j.1 + 1 : ℕ) : Int))
    congr 1
    push_cast
    ring

theorem triple_new_overlap {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hj : j.1 + 1 < width) :
    (S.triple S.after j).center =
        (S.triple S.after ⟨j.1 + 1, hj⟩).minus ∧
      (S.triple S.after j).plus =
        (S.triple S.after ⟨j.1 + 1, hj⟩).center := by
  constructor
  · change S.cell S.after (S.origin + (j.1 : Int)) =
      S.cell S.after (S.origin + ((j.1 + 1 : ℕ) : Int) - 1)
    congr 1
    push_cast
    ring
  · change S.cell S.after (S.origin + (j.1 : Int) + 1) =
      S.cell S.after (S.origin + ((j.1 + 1 : ℕ) : Int))
    congr 1
    push_cast
    ring

theorem oldStrip_overlap {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hj : j.1 + 1 < width) :
    (S.oldStrip j).center = (S.oldStrip ⟨j.1 + 1, hj⟩).minus ∧
      (S.oldStrip j).plus = (S.oldStrip ⟨j.1 + 1, hj⟩).center :=
  S.triple_old_overlap j hj

theorem newStrip_overlap {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hj : j.1 + 1 < width) :
    (S.newStrip j).center = (S.newStrip ⟨j.1 + 1, hj⟩).minus ∧
      (S.newStrip j).plus = (S.newStrip ⟨j.1 + 1, hj⟩).center :=
  S.triple_new_overlap j hj

theorem left_exterior_before_hash {width : ℕ} (S : WindowedMStarStep width) :
    S.before.tape (S.origin - 1) = .hash := by
  apply S.before_hash_outside
  left
  omega

theorem right_exterior_before_hash {width : ℕ} (S : WindowedMStarStep width) :
    S.before.tape (S.origin + width) = .hash := by
  apply S.before_hash_outside
  right
  omega

/-- The leftmost finite index, available because a window has width at least
three. -/
def leftIndex {width : ℕ} (S : WindowedMStarStep width) : Fin width :=
  ⟨0, Nat.lt_of_lt_of_le (by decide) S.width_ge_three⟩

/-- The rightmost finite index of a nonempty window. -/
def rightIndex {width : ℕ} (S : WindowedMStarStep width) : Fin width :=
  ⟨width - 1, by
    have hw := S.width_ge_three
    omega⟩

theorem left_boundary_old_minus_hash {width : ℕ} (S : WindowedMStarStep width) :
    (S.triple S.before S.leftIndex).minus = .plain .hash := by
  have hnothead : S.origin - 1 ≠ S.before.head := by
    rw [S.head_eq]
    dsimp [leftIndex]
    omega
  simp [triple, leftIndex, position, cell, hnothead,
    left_exterior_before_hash]

theorem right_boundary_old_plus_hash {width : ℕ} (S : WindowedMStarStep width) :
    (S.triple S.before S.rightIndex).plus = .plain .hash := by
  have hposition : S.position S.rightIndex + 1 = S.origin + width := by
    unfold position rightIndex
    have hw := S.width_ge_three
    push_cast
    omega
  have hnothead : S.position S.rightIndex + 1 ≠ S.before.head := by
    rw [S.head_eq]
    have hhead := S.head_interior_right
    dsimp [position, rightIndex] at hhead ⊢
    push_cast
    omega
  have hrightNot : S.origin + width ≠ S.before.head := by
    intro heq
    exact hnothead (hposition.trans heq)
  rw [show (S.triple S.before S.rightIndex).plus =
    S.cell S.before (S.position S.rightIndex + 1) by rfl]
  rw [hposition]
  simp [cell, hrightNot, right_exterior_before_hash]

theorem execution_source {width : ℕ} (S : WindowedMStarStep width) :
    S.before.state = (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).sourceState ∧
      S.before.tape S.before.head =
        (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).read :=
  FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable S.before S.after S.arrow
    S.executes

theorem execution_target_state {width : ℕ} (S : WindowedMStarStep width) :
    S.after.state =
      (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).targetState :=
  FiniteOneTapeSemantics.step_some_state
    MStarULogAssembly.program MStarOuterProgram.movable S.before S.after S.arrow
    S.executes

theorem execution_after_description {width : ℕ} (S : WindowedMStarStep width) :
    S.after =
      { state := (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).targetState
        head := FiniteOneTapeSemantics.moveHead
          (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move
          S.before.head
        tape := FiniteOneTapeSemantics.writtenTape S.before
          (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).write } ∧
      MStarOuterProgram.movable
        ((FiniteOneTapeSemantics.writtenTape S.before
          (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).write)
          (FiniteOneTapeSemantics.moveHead
            (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move
            S.before.head)) = true := by
  have hexec := S.executes
  unfold FiniteOneTapeSemantics.step at hexec
  dsimp only at hexec
  split at hexec
  · simp at hexec
  · rename_i hsource
    split at hexec
    · rename_i hmovable
      exact ⟨(Option.some.inj hexec).symm, by simpa using hmovable⟩
    · simp at hexec

theorem head_index_old_center {width : ℕ} (S : WindowedMStarStep width) :
    (S.triple S.before S.head_index).center =
      .head S.before.state (S.before.tape S.before.head) := by
  unfold triple cell position
  rw [S.head_eq]
  simp

theorem head_index_old_minus_plain {width : ℕ} (S : WindowedMStarStep width) :
    (S.triple S.before S.head_index).minus =
      .plain (S.before.tape (S.before.head - 1)) := by
  have hposition : S.position S.head_index - 1 = S.before.head - 1 := by
    unfold position
    rw [← S.head_eq]
  have hnothead : S.before.head - 1 ≠ S.before.head := by omega
  rw [show (S.triple S.before S.head_index).minus =
    S.cell S.before (S.position S.head_index - 1) by rfl, hposition]
  simp [cell, hnothead]

theorem head_index_old_plus_plain {width : ℕ} (S : WindowedMStarStep width) :
    (S.triple S.before S.head_index).plus =
      .plain (S.before.tape (S.before.head + 1)) := by
  have hposition : S.position S.head_index + 1 = S.before.head + 1 := by
    unfold position
    rw [← S.head_eq]
  have hnothead : S.before.head + 1 ≠ S.before.head := by omega
  rw [show (S.triple S.before S.head_index).plus =
    S.cell S.before (S.position S.head_index + 1) by rfl, hposition]
  simp [cell, hnothead]

def headLeftIndex {width : ℕ} (S : WindowedMStarStep width) : Fin width :=
  ⟨S.head_index.1 - 1, by
    have hleft := S.head_interior_left
    omega⟩

def headRightIndex {width : ℕ} (S : WindowedMStarStep width) : Fin width :=
  ⟨S.head_index.1 + 1, S.head_interior_right⟩

theorem head_right_new_center {width : ℕ} (S : WindowedMStarStep width) :
    (S.newStrip S.headRightIndex).center =
      Fixed.Machine.rightUpdate S.arrow (S.oldStrip S.headRightIndex).center := by
  change (S.triple S.after S.headRightIndex).center =
    Fixed.Machine.rightUpdate S.arrow (S.triple S.before S.headRightIndex).center
  unfold triple cell position
  rcases S.execution_after_description with ⟨hafter, hmovable⟩
  rw [hafter]
  cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move <;>
    simp [newStrip, oldStrip, triple, cell, position, headRightIndex,
      MStarULogAssembly.tableauData, MStarOuterProgram.tableauData,
      FiniteOneTapeProgram.tableauData, OneTapeTableau.tableauMachineData,
      OneTapeTableau.updateFromLeft, hmove,
      FiniteOneTapeSemantics.moveHead, FiniteOneTapeSemantics.writtenTape,
      Function.update_self, Function.update_of_ne, S.head_eq] <;>
    try omega

theorem head_left_new_center {width : ℕ} (S : WindowedMStarStep width) :
    (S.newStrip S.headLeftIndex).center =
      Fixed.Machine.leftUpdate S.arrow (S.oldStrip S.headLeftIndex).center := by
  change (S.triple S.after S.headLeftIndex).center =
    Fixed.Machine.leftUpdate S.arrow (S.triple S.before S.headLeftIndex).center
  unfold triple cell position
  have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
      (S.head_index.1 : Int) - 1 := by
    push_cast
    have hleft := S.head_interior_left
    omega
  rcases S.execution_after_description with ⟨hafter, hmovable⟩
  rw [hafter]
  cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move <;>
    simp [newStrip, oldStrip, triple, cell, position, headLeftIndex,
      MStarULogAssembly.tableauData, MStarOuterProgram.tableauData,
      FiniteOneTapeProgram.tableauData, OneTapeTableau.tableauMachineData,
      OneTapeTableau.updateFromRight, hmove,
      FiniteOneTapeSemantics.moveHead, FiniteOneTapeSemantics.writtenTape,
      Function.update_self, Function.update_of_ne, S.head_eq, hpred] <;>
    try omega

theorem head_right_old_minus {width : ℕ} (S : WindowedMStarStep width) :
    (S.oldStrip S.headRightIndex).minus =
      .head S.before.state (S.before.tape S.before.head) := by
  have hposition : S.position S.headRightIndex - 1 = S.before.head := by
    unfold position headRightIndex
    calc
      S.origin + ((S.head_index.1 : Int) + 1) - 1 =
          S.origin + (S.head_index.1 : Int) := by ring
      _ = S.before.head := S.head_eq.symm
  rw [show (S.oldStrip S.headRightIndex).minus =
    S.cell S.before (S.position S.headRightIndex - 1) by rfl, hposition]
  simp [cell]

theorem head_right_old_center_plain {width : ℕ} (S : WindowedMStarStep width) :
    (S.oldStrip S.headRightIndex).center =
      .plain (S.before.tape (S.before.head + 1)) := by
  have hposition : S.position S.headRightIndex = S.before.head + 1 := by
    unfold position headRightIndex
    calc
      S.origin + ((S.head_index.1 : Int) + 1) =
          (S.origin + (S.head_index.1 : Int)) + 1 := by ring
      _ = S.before.head + 1 := by rw [S.head_eq]
  have hnothead : S.before.head + 1 ≠ S.before.head := by omega
  rw [show (S.oldStrip S.headRightIndex).center =
    S.cell S.before (S.position S.headRightIndex) by rfl, hposition]
  simp [cell, hnothead]

theorem head_left_old_plus {width : ℕ} (S : WindowedMStarStep width) :
    (S.oldStrip S.headLeftIndex).plus =
      .head S.before.state (S.before.tape S.before.head) := by
  have hposition : S.position S.headLeftIndex + 1 = S.before.head := by
    unfold position headLeftIndex
    have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
        (S.head_index.1 : Int) - 1 := by
      push_cast
      have hleft := S.head_interior_left
      omega
    rw [hpred]
    calc
      S.origin + ((S.head_index.1 : Int) - 1) + 1 =
          S.origin + (S.head_index.1 : Int) := by ring
      _ = S.before.head := S.head_eq.symm
  rw [show (S.oldStrip S.headLeftIndex).plus =
    S.cell S.before (S.position S.headLeftIndex + 1) by rfl, hposition]
  simp [cell]

theorem head_left_old_center_plain {width : ℕ} (S : WindowedMStarStep width) :
    (S.oldStrip S.headLeftIndex).center =
      .plain (S.before.tape (S.before.head - 1)) := by
  have hposition : S.position S.headLeftIndex = S.before.head - 1 := by
    unfold position headLeftIndex
    have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
        (S.head_index.1 : Int) - 1 := by
      push_cast
      have hleft := S.head_interior_left
      omega
    rw [hpred]
    calc
      S.origin + ((S.head_index.1 : Int) - 1) =
          (S.origin + (S.head_index.1 : Int)) - 1 := by ring
      _ = S.before.head - 1 := by rw [S.head_eq]
  have hnothead : S.before.head - 1 ≠ S.before.head := by omega
  rw [show (S.oldStrip S.headLeftIndex).center =
    S.cell S.before (S.position S.headLeftIndex) by rfl, hposition]
  simp [cell, hnothead]

theorem tableau_source_at_head {width : ℕ} (S : WindowedMStarStep width) :
    Fixed.Machine.source S.arrow =
      (S.before.state, S.before.tape S.before.head) := by
  rcases S.execution_source with ⟨hs, hr⟩
  change
    (FiniteOneTapeProgram.tableauData MStarULogAssembly.program
      MStarOuterProgram.movable).source S.arrow =
        (S.before.state, S.before.tape S.before.head)
  rw [FiniteOneTapeProgram.tableauData_source]
  apply Prod.ext
  · exact hs.symm
  · exact hr.symm

theorem headSourceOf_eq_of_eq {State Tape : Type*}
    {z : TableauCell State Tape} {q : State} {a : Tape}
    (hz : z = .head q a) (h : z.isHead = true) :
    z.headSourceOf h = (q, a) := by
  subst z
  rfl

theorem theta_old_new {width : ℕ} (S : WindowedMStarStep width) :
    Fixed.Machine.theta S.arrow (S.oldStrip S.head_index) =
      some (S.newStrip S.head_index) := by
  change OneTapeTableau.theta MStarOuterProgram.movable
      (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow)
      (S.triple S.before S.head_index) =
        some (S.triple S.after S.head_index)
  rcases S.execution_source with ⟨hstate, hread⟩
  rcases S.execution_after_description with ⟨hafter, hmovable⟩
  have hread' :
      S.before.tape (S.origin + (S.head_index.1 : Int)) =
        (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).read := by
    rw [← S.head_eq]
    exact hread
  rw [hafter]
  cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move with
  | left =>
      have hne : S.before.head ≠ S.before.head - 1 := by omega
      have hmovable' :
          MStarOuterProgram.movable (S.before.tape
            (S.origin + (S.head_index.1 : Int) - 1)) = true := by
        simpa [hmove, FiniteOneTapeSemantics.moveHead,
          FiniteOneTapeSemantics.writtenTape, Function.update_of_ne, hne,
          S.head_eq] using hmovable
      simp [OneTapeTableau.theta, hstate, hmove, hread', hmovable',
        FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead,
        Function.update_self, Function.update_of_ne, triple, cell, position,
        S.head_eq]
      all_goals omega
  | stay =>
      have hmovable' : MStarOuterProgram.movable
          (FiniteOneTapeProgram.transition MStarULogAssembly.program
            S.arrow).write = true := by
        simpa [hmove, FiniteOneTapeSemantics.moveHead,
          FiniteOneTapeSemantics.writtenTape, Function.update_self] using hmovable
      simp [OneTapeTableau.theta, hstate, hmove, hread', hmovable',
        FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead,
        Function.update_self, Function.update_of_ne, triple, cell, position,
        S.head_eq]
  | right =>
      have hne : S.before.head ≠ S.before.head + 1 := by omega
      have hmovable' :
          MStarOuterProgram.movable (S.before.tape
            (S.origin + (S.head_index.1 : Int) + 1)) = true := by
        simpa [hmove, FiniteOneTapeSemantics.moveHead,
          FiniteOneTapeSemantics.writtenTape, Function.update_of_ne, hne,
          S.head_eq] using hmovable
      simp [OneTapeTableau.theta, hstate, hmove, hread', hmovable',
        FiniteOneTapeSemantics.writtenTape, FiniteOneTapeSemantics.moveHead,
        Function.update_self, Function.update_of_ne, triple, cell, position,
        S.head_eq]
      all_goals omega

/-- The centre tile of one bounded operational step. -/
def centeredTile {width : ℕ} (S : WindowedMStarStep width) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  fixedCenteredStepTile S.arrow (S.oldStrip S.head_index) (S.newStrip S.head_index)
    (S.triple_head_count_le_one S.before S.head_index)
    (S.triple_head_count_le_one S.after S.head_index)
    (by
      change (S.triple S.before S.head_index).center.isHead = true
      rw [S.head_index_old_center]
      rfl)
    (by
      rw [S.tableau_source_at_head]
      exact (headSourceOf_eq_of_eq S.head_index_old_center
        (by
          change (S.triple S.before S.head_index).center.isHead = true
          rw [S.head_index_old_center]
          rfl)).symm)
    S.theta_old_new

theorem centeredTile_old {width : ℕ} (S : WindowedMStarStep width) :
    S.centeredTile.1.old = S.oldStrip S.head_index := rfl

theorem centeredTile_new {width : ℕ} (S : WindowedMStarStep width) :
    S.centeredTile.1.new = S.newStrip S.head_index := rfl

def leftNeighborTile {width : ℕ} (S : WindowedMStarStep width) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  fixedLeftHeadStepTile S.arrow (S.oldStrip S.headRightIndex)
    (S.newStrip S.headRightIndex)
    (S.triple_head_count_le_one S.before S.headRightIndex)
    (S.triple_head_count_le_one S.after S.headRightIndex)
    (by
      change (S.oldStrip S.headRightIndex).center.isHead = false
      rw [S.head_right_old_center_plain]
      rfl)
    (by
      change (S.oldStrip S.headRightIndex).minus.isHead = true
      rw [S.head_right_old_minus]
      rfl)
    (by
      rw [S.tableau_source_at_head]
      change (S.before.state, S.before.tape S.before.head) =
        (S.oldStrip S.headRightIndex).minus.headSourceOf _
      exact (headSourceOf_eq_of_eq S.head_right_old_minus
        (by
          change (S.oldStrip S.headRightIndex).minus.isHead = true
          rw [S.head_right_old_minus]
          rfl)).symm)
    S.head_right_new_center

theorem leftNeighborTile_old {width : ℕ} (S : WindowedMStarStep width) :
    S.leftNeighborTile.1.old = S.oldStrip S.headRightIndex := rfl

theorem leftNeighborTile_new {width : ℕ} (S : WindowedMStarStep width) :
    S.leftNeighborTile.1.new = S.newStrip S.headRightIndex := rfl

def rightNeighborTile {width : ℕ} (S : WindowedMStarStep width) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  fixedRightHeadStepTile S.arrow (S.oldStrip S.headLeftIndex)
    (S.newStrip S.headLeftIndex)
    (S.triple_head_count_le_one S.before S.headLeftIndex)
    (S.triple_head_count_le_one S.after S.headLeftIndex)
    (by
      change (S.oldStrip S.headLeftIndex).center.isHead = false
      rw [S.head_left_old_center_plain]
      rfl)
    (by
      change (S.oldStrip S.headLeftIndex).minus.isHead = false
      have hposition : S.position S.headLeftIndex - 1 ≠ S.before.head := by
        unfold position headLeftIndex
        intro heq
        have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
            (S.head_index.1 : Int) - 1 := by
          push_cast
          have hleft := S.head_interior_left
          omega
        rw [hpred] at heq
        have hh := S.head_eq
        omega
      simp [oldStrip, triple, cell, TableauCell.isHead, hposition])
    (by
      change (S.oldStrip S.headLeftIndex).plus.isHead = true
      rw [S.head_left_old_plus]
      rfl)
    (by
      rw [S.tableau_source_at_head]
      change (S.before.state, S.before.tape S.before.head) =
        (S.oldStrip S.headLeftIndex).plus.headSourceOf _
      exact (headSourceOf_eq_of_eq S.head_left_old_plus
        (by
          change (S.oldStrip S.headLeftIndex).plus.isHead = true
          rw [S.head_left_old_plus]
          rfl)).symm)
    S.head_left_new_center

theorem rightNeighborTile_old {width : ℕ} (S : WindowedMStarStep width) :
    S.rightNeighborTile.1.old = S.oldStrip S.headLeftIndex := rfl

theorem rightNeighborTile_new {width : ℕ} (S : WindowedMStarStep width) :
    S.rightNeighborTile.1.new = S.newStrip S.headLeftIndex := rfl

theorem passive_new_center {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft : j ≠ S.headLeftIndex)
    (hcenter : j ≠ S.head_index) (hright : j ≠ S.headRightIndex) :
    (S.newStrip j).center = (S.oldStrip j).center := by
  have hne : j.1 ≠ S.head_index.1 := by
    intro h
    apply hcenter
    apply Fin.ext
    exact h
  have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
      (S.head_index.1 : Int) - 1 := by
    push_cast
    have hh := S.head_interior_left
    omega
  have hpos : S.position j ≠ S.before.head := by
    intro h
    rw [S.head_eq] at h
    unfold position at h
    apply hne
    exact_mod_cast Int.add_left_cancel h
  have hleftPos : S.position j ≠
      S.origin + (S.head_index.1 : Int) - 1 := by
    intro h
    apply hleft
    apply Fin.ext
    unfold position at h
    have hval : (j.1 : Int) = (S.head_index.1 : Int) - 1 := by
      omega
    rw [← hpred] at hval
    exact_mod_cast hval
  have hrightPos : S.position j ≠
      S.origin + (S.head_index.1 : Int) + 1 := by
    intro h
    apply hright
    apply Fin.ext
    unfold position at h
    have hval : (j.1 : Int) = (S.head_index.1 : Int) + 1 := by
      omega
    exact_mod_cast hval
  have hwritePos : S.origin + (j.1 : Int) ≠
      S.origin + (S.head_index.1 : Int) := by
    intro h
    apply hpos
    unfold position
    rw [S.head_eq]
    exact h
  have hleftPos' : S.origin + (j.1 : Int) ≠
      S.origin + (S.head_index.1 : Int) - 1 := by
    simpa [position] using hleftPos
  have hrightPos' : S.origin + (j.1 : Int) ≠
      S.origin + (S.head_index.1 : Int) + 1 := by
    simpa [position] using hrightPos
  rcases S.execution_after_description with ⟨hafter, hmovable⟩
  change (S.triple S.after j).center = (S.triple S.before j).center
  unfold triple cell position
  rw [hafter]
  cases hmove : (FiniteOneTapeProgram.transition MStarULogAssembly.program S.arrow).move <;>
    simp [hmove, FiniteOneTapeSemantics.moveHead,
      FiniteOneTapeSemantics.writtenTape, Function.update_self,
      Function.update_of_ne, hne, hwritePos, hpos, hleftPos, hrightPos,
      hleftPos', hrightPos',
      S.head_eq] <;>
    try omega

def passiveTileAt {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft : j ≠ S.headLeftIndex)
    (hcenter : j ≠ S.head_index) (hright : j ≠ S.headRightIndex) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  fixedPassiveTile (S.oldStrip j) (S.newStrip j)
    (S.triple_head_count_le_one S.before j)
    (S.triple_head_count_le_one S.after j)
    (by
      change (S.oldStrip j).minus.isHead = false
      unfold oldStrip triple cell position
      have h : S.position j - 1 ≠ S.before.head := by
        intro heq
        apply hright
        apply Fin.ext
        change j.1 = S.head_index.1 + 1
        unfold position at heq
        have hh := S.head_eq
        have heq' : (j.1 : Int) = (S.head_index.1 : Int) + 1 := by
          omega
        exact_mod_cast heq'
      unfold position at h
      simp [TableauCell.isHead, h])
    (by
      change (S.oldStrip j).center.isHead = false
      unfold oldStrip triple cell position
      have h : S.position j ≠ S.before.head := by
        intro heq
        apply hcenter
        apply Fin.ext
        change j.1 = S.head_index.1
        unfold position at heq
        have hh := S.head_eq
        have heq' : (j.1 : Int) = (S.head_index.1 : Int) := by omega
        exact_mod_cast heq'
      unfold position at h
      simp [TableauCell.isHead, h])
    (by
      change (S.oldStrip j).plus.isHead = false
      unfold oldStrip triple cell position
      have h : S.position j + 1 ≠ S.before.head := by
        intro heq
        apply hleft
        apply Fin.ext
        change j.1 = S.head_index.1 - 1
        unfold position at heq
        have hpred : ((S.head_index.1 - 1 : ℕ) : Int) =
            (S.head_index.1 : Int) - 1 := by
          push_cast
          have hpos := S.head_interior_left
          omega
        have hh := S.head_eq
        have heq' : (j.1 : Int) = (S.head_index.1 : Int) - 1 := by
          omega
        rw [← hpred] at heq'
        exact_mod_cast heq'
      unfold position at h
      simp [TableauCell.isHead, h])
    (S.passive_new_center j hleft hcenter hright)

theorem passiveTileAt_old {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft hcenter hright) :
    (S.passiveTileAt j hleft hcenter hright).1.old = S.oldStrip j := rfl

theorem passiveTileAt_new {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft hcenter hright) :
    (S.passiveTileAt j hleft hcenter hright).1.new = S.newStrip j := rfl

@[simp] theorem centeredTile_northToken {width : ℕ} (S : WindowedMStarStep width) :
    S.centeredTile.1.northToken = some S.arrow := rfl

@[simp] theorem centeredTile_southToken {width : ℕ} (S : WindowedMStarStep width) :
    S.centeredTile.1.southToken = none := rfl

@[simp] theorem leftNeighborTile_northToken {width : ℕ} (S : WindowedMStarStep width) :
    S.leftNeighborTile.1.northToken = none := rfl

@[simp] theorem leftNeighborTile_southToken {width : ℕ} (S : WindowedMStarStep width) :
    S.leftNeighborTile.1.southToken = some S.arrow := rfl

@[simp] theorem rightNeighborTile_northToken {width : ℕ} (S : WindowedMStarStep width) :
    S.rightNeighborTile.1.northToken = none := rfl

@[simp] theorem rightNeighborTile_southToken {width : ℕ} (S : WindowedMStarStep width) :
    S.rightNeighborTile.1.southToken = none := rfl

@[simp] theorem passiveTileAt_northToken {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft hcenter hright) :
    (S.passiveTileAt j hleft hcenter hright).1.northToken = none := rfl

@[simp] theorem passiveTileAt_southToken {width : ℕ} (S : WindowedMStarStep width)
    (j : Fin width) (hleft hcenter hright) :
    (S.passiveTileAt j hleft hcenter hright).1.southToken = none := rfl

end WindowedMStarStep

/-- A whole finite accepting M-star computation carried in one fixed spatial
window. Every field is operational or a boundary fact about concrete tapes;
there is no tableau or frame-filling field. -/
structure UniformWindowedMStarRun (width n : ℕ) where
  config : Fin (n + 1) → MStarConfig
  arrow : Fin n → Fixed.Arrow
  step :
    ∀ t : Fin n,
      FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
        (config ⟨t.1, Nat.lt_succ_of_lt t.2⟩) (arrow t) =
          some (config ⟨t.1 + 1, by omega⟩)
  origin : Int
  width_ge_three : 3 ≤ width
  head_index : Fin (n + 1) → Fin width
  head_eq :
    ∀ t : Fin (n + 1),
      (config t).head = origin + (head_index t).1
  head_interior_left : ∀ t : Fin (n + 1), 0 < (head_index t).1
  head_interior_right :
    ∀ t : Fin (n + 1), (head_index t).1 + 1 < width
  hash_outside :
    ∀ (t : Fin (n + 1)) (z : Int),
      z < origin ∨ origin + width ≤ z → (config t).tape z = .hash
  final_accept : (config ⟨n, Nat.lt_succ_self n⟩).state = MStarOuterProgram.State.accept

namespace UniformWindowedMStarRun

/-- Replace only the two propagated order-bit pairs of a locally admissible
tile.  The machine-case witness and its tokens are unaffected. -/
def retagBits
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool)
    (hold : tableauOrdBit oldMinusBit oldPlusBit u.1.old.center)
    (hnew : tableauOrdBit newMinusBit newPlusBit u.1.new.center) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine := by
  refine ⟨{ old := u.1.old
            new := u.1.new
            oldMinusBit := oldMinusBit
            oldPlusBit := oldPlusBit
            newMinusBit := newMinusBit
            newPlusBit := newPlusBit
            southToken := u.1.southToken
            northToken := u.1.northToken }, ?_⟩
  rcases u.2 with ⟨holdCount, hnewCount, _, _, hstep⟩
  exact ⟨holdCount, hnewCount, hold, hnew, hstep⟩

@[simp] theorem retagBits_old
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.old = u.1.old := rfl

@[simp] theorem retagBits_new
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.new = u.1.new := rfl

@[simp] theorem retagBits_oldMinusBit
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.oldMinusBit =
      oldMinusBit := rfl

@[simp] theorem retagBits_oldPlusBit
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.oldPlusBit =
      oldPlusBit := rfl

@[simp] theorem retagBits_newMinusBit
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.newMinusBit =
      newMinusBit := rfl

@[simp] theorem retagBits_newPlusBit
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.newPlusBit =
      newPlusBit := rfl

@[simp] theorem retagBits_southToken
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.southToken =
      u.1.southToken := rfl

@[simp] theorem retagBits_northToken
    (u : HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine)
    (oldMinusBit oldPlusBit newMinusBit newPlusBit : Bool) (hold hnew) :
    (retagBits u oldMinusBit oldPlusBit newMinusBit newPlusBit hold hnew).1.northToken =
      u.1.northToken := rfl

/-- The concrete one-step window at a finite time index, obtained without any
additional certificate from the uniform run. -/
def stepWindow {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) : WindowedMStarStep width where
  before := R.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  after := R.config ⟨t.1 + 1, by omega⟩
  arrow := R.arrow t
  executes := R.step t
  origin := R.origin
  width_ge_three := R.width_ge_three
  head_index := R.head_index ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  head_eq := R.head_eq ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  head_interior_left := R.head_interior_left ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  head_interior_right := R.head_interior_right ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  before_hash_outside := R.hash_outside ⟨t.1, Nat.lt_succ_of_lt t.2⟩
  after_hash_outside := R.hash_outside ⟨t.1 + 1, by omega⟩

/-- The monotone order bit placed on a spatial edge of a concrete
configuration. -/
def orderBit (c : MStarConfig) (edge : Int) : Bool :=
  decide (c.head < edge)

def oldMinusBit {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) : Bool :=
  orderBit (R.stepWindow t).before ((R.stepWindow t).position j)

def oldPlusBit {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) : Bool :=
  orderBit (R.stepWindow t).before ((R.stepWindow t).position j + 1)

def newMinusBit {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) : Bool :=
  orderBit (R.stepWindow t).after ((R.stepWindow t).position j)

def newPlusBit {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) : Bool :=
  orderBit (R.stepWindow t).after ((R.stepWindow t).position j + 1)

theorem order_bits_admissible {width : ℕ} (S : WindowedMStarStep width)
    (c : MStarConfig) (j : Fin width) :
    tableauOrdBit (orderBit c (S.position j))
      (orderBit c (S.position j + 1)) (S.triple c j).center := by
  have hhead : (S.triple c j).center.isHead = true ↔ S.position j = c.head := by
    change (S.cell c (S.position j)).isHead = true ↔ _
    exact S.cell_isHead_iff c (S.position j)
  unfold tableauOrdBit
  split
  · have hp : S.position j = c.head := hhead.mp (by assumption)
    simp [orderBit, hp]
  · have hp : S.position j ≠ c.head := by
      intro h
      have hhead' : (S.triple c j).center.isHead = true := hhead.mpr h
      simp_all
    by_cases hlt : c.head < S.position j
    · have hlt' : c.head < S.position j + 1 := by omega
      simp [orderBit, hlt, hlt']
    · have hlt' : ¬c.head < S.position j + 1 := by
        intro h
        apply hp
        omega
      simp [orderBit, hlt, hlt']

theorem old_bits_admissible {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    tableauOrdBit (R.oldMinusBit t j) (R.oldPlusBit t j)
      ((R.stepWindow t).oldStrip j).center :=
  order_bits_admissible (R.stepWindow t) (R.stepWindow t).before j

theorem new_bits_admissible {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    tableauOrdBit (R.newMinusBit t j) (R.newPlusBit t j)
      ((R.stepWindow t).newStrip j).center :=
  order_bits_admissible (R.stepWindow t) (R.stepWindow t).after j

def tileAt {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  let S := R.stepWindow t
  if hc : j = S.head_index then
    retagBits S.centeredTile (R.oldMinusBit t S.head_index)
      (R.oldPlusBit t S.head_index) (R.newMinusBit t S.head_index)
      (R.newPlusBit t S.head_index) (R.old_bits_admissible t S.head_index)
      (R.new_bits_admissible t S.head_index)
  else if hr : j = S.headRightIndex then
    retagBits S.leftNeighborTile (R.oldMinusBit t S.headRightIndex)
      (R.oldPlusBit t S.headRightIndex) (R.newMinusBit t S.headRightIndex)
      (R.newPlusBit t S.headRightIndex) (R.old_bits_admissible t S.headRightIndex)
      (R.new_bits_admissible t S.headRightIndex)
  else if hl : j = S.headLeftIndex then
    retagBits S.rightNeighborTile (R.oldMinusBit t S.headLeftIndex)
      (R.oldPlusBit t S.headLeftIndex) (R.newMinusBit t S.headLeftIndex)
      (R.newPlusBit t S.headLeftIndex) (R.old_bits_admissible t S.headLeftIndex)
      (R.new_bits_admissible t S.headLeftIndex)
  else
    retagBits (S.passiveTileAt j hl hc hr)
      (R.oldMinusBit t j) (R.oldPlusBit t j) (R.newMinusBit t j) (R.newPlusBit t j)
      (R.old_bits_admissible t j) (R.new_bits_admissible t j)

theorem tileAt_old {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    (R.tileAt t j).1.old = (R.stepWindow t).oldStrip j := by
  unfold tileAt
  dsimp
  split <;> rename_i h
  · subst j
    exact (R.stepWindow t).centeredTile_old
  · split <;> rename_i h'
    · subst j
      exact (R.stepWindow t).leftNeighborTile_old
    · split <;> rename_i h''
      · subst j
        exact (R.stepWindow t).rightNeighborTile_old
      · exact (R.stepWindow t).passiveTileAt_old j h'' h h'

theorem tileAt_new {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    (R.tileAt t j).1.new = (R.stepWindow t).newStrip j := by
  unfold tileAt
  dsimp
  split <;> rename_i h
  · subst j
    exact (R.stepWindow t).centeredTile_new
  · split <;> rename_i h'
    · subst j
      exact (R.stepWindow t).leftNeighborTile_new
    · split <;> rename_i h''
      · subst j
        exact (R.stepWindow t).rightNeighborTile_new
      · exact (R.stepWindow t).passiveTileAt_new j h'' h h'

theorem tileAt_bits {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    (R.tileAt t j).1.oldMinusBit = R.oldMinusBit t j ∧
      (R.tileAt t j).1.oldPlusBit = R.oldPlusBit t j ∧
      (R.tileAt t j).1.newMinusBit = R.newMinusBit t j ∧
      (R.tileAt t j).1.newPlusBit = R.newPlusBit t j := by
  by_cases hc : j = (R.stepWindow t).head_index
  · simp only [tileAt, dif_pos hc]
    rw [hc]
    unfold retagBits
    exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases hr : j = (R.stepWindow t).headRightIndex
  · simp only [tileAt, dif_neg hc, dif_pos hr]
    rw [hr]
    unfold retagBits
    exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases hl : j = (R.stepWindow t).headLeftIndex
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_pos hl]
    rw [hl]
    unfold retagBits
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_neg hl]
    unfold retagBits
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem tileAt_northToken {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    (R.tileAt t j).1.northToken =
      if j = (R.stepWindow t).head_index then some (R.stepWindow t).arrow else none := by
  by_cases hc : j = (R.stepWindow t).head_index
  · simp only [tileAt, dif_pos hc]
    rw [if_pos hc]
    unfold retagBits
    exact (R.stepWindow t).centeredTile_northToken
  by_cases hr : j = (R.stepWindow t).headRightIndex
  · simp only [tileAt, dif_neg hc, dif_pos hr]
    rw [if_neg hc]
    unfold retagBits
    exact (R.stepWindow t).leftNeighborTile_northToken
  by_cases hl : j = (R.stepWindow t).headLeftIndex
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_pos hl]
    rw [if_neg hc]
    unfold retagBits
    exact (R.stepWindow t).rightNeighborTile_northToken
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_neg hl]
    rw [if_neg hc]
    unfold retagBits
    exact (R.stepWindow t).passiveTileAt_northToken j hl hc hr

theorem tileAt_southToken {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) :
    (R.tileAt t j).1.southToken =
      if j = (R.stepWindow t).headRightIndex then some (R.stepWindow t).arrow else none := by
  have hright_ne_head : (R.stepWindow t).headRightIndex ≠
      (R.stepWindow t).head_index := by
    intro h
    have hval := congrArg Fin.val h
    change (R.stepWindow t).head_index.1 + 1 = (R.stepWindow t).head_index.1 at hval
    omega
  have hhead_ne_right : (R.stepWindow t).head_index ≠
      (R.stepWindow t).headRightIndex := fun h => hright_ne_head h.symm
  by_cases hc : j = (R.stepWindow t).head_index
  · simp only [tileAt, dif_pos hc]
    rw [hc, if_neg hhead_ne_right]
    unfold retagBits
    exact (R.stepWindow t).centeredTile_southToken
  by_cases hr : j = (R.stepWindow t).headRightIndex
  · simp only [tileAt, dif_neg hc, dif_pos hr]
    rw [if_pos hr]
    unfold retagBits
    exact (R.stepWindow t).leftNeighborTile_southToken
  by_cases hl : j = (R.stepWindow t).headLeftIndex
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_pos hl]
    rw [if_neg hr]
    unfold retagBits
    exact (R.stepWindow t).rightNeighborTile_southToken
  · simp only [tileAt, dif_neg hc, dif_neg hr, dif_neg hl]
    rw [if_neg hr]
    unfold retagBits
    exact (R.stepWindow t).passiveTileAt_southToken j hl hc hr

theorem tileAt_token_match {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) (hj : j.1 + 1 < width) :
    (R.tileAt t j).1.northToken =
      (R.tileAt t ⟨j.1 + 1, hj⟩).1.southToken := by
  let S := R.stepWindow t
  let k : Fin width := ⟨j.1 + 1, hj⟩
  have hnext : j = S.head_index ↔ k = S.headRightIndex := by
    constructor
    · intro h
      subst j
      apply Fin.ext
      change S.head_index.1 + 1 = S.head_index.1 + 1
      rfl
    · intro h
      have hval := congrArg Fin.val h
      change j.1 + 1 = S.head_index.1 + 1 at hval
      apply Fin.ext
      omega
  rw [R.tileAt_northToken, R.tileAt_southToken]
  by_cases h : j = S.head_index
  · rw [if_pos h, if_pos (hnext.mp h)]
  · rw [if_neg h, if_neg ((not_congr hnext).mp h)]

theorem vertical_match_tileAt {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (j : Fin width) (hj : j.1 + 1 < width) :
    (higherBlockTableauWangTile Fixed.Machine (R.tileAt t j)).north =
      (higherBlockTableauWangTile Fixed.Machine
        (R.tileAt t ⟨j.1 + 1, hj⟩)).south := by
  let k : Fin width := ⟨j.1 + 1, hj⟩
  rcases (R.stepWindow t).oldStrip_overlap j hj with ⟨holdCenter, holdPlus⟩
  rcases (R.stepWindow t).newStrip_overlap j hj with ⟨hnewCenter, hnewPlus⟩
  have holdCenter' : (R.tileAt t j).1.old.center =
      (R.tileAt t k).1.old.minus := by
    rw [R.tileAt_old, R.tileAt_old]
    exact holdCenter
  have holdPlus' : (R.tileAt t j).1.old.plus =
      (R.tileAt t k).1.old.center := by
    rw [R.tileAt_old, R.tileAt_old]
    exact holdPlus
  have hnewCenter' : (R.tileAt t j).1.new.center =
      (R.tileAt t k).1.new.minus := by
    rw [R.tileAt_new, R.tileAt_new]
    exact hnewCenter
  have hnewPlus' : (R.tileAt t j).1.new.plus =
      (R.tileAt t k).1.new.center := by
    rw [R.tileAt_new, R.tileAt_new]
    exact hnewPlus
  have holdBit : (R.tileAt t j).1.oldPlusBit =
      (R.tileAt t k).1.oldMinusBit := by
    rw [(R.tileAt_bits t j).2.1, (R.tileAt_bits t k).1]
    unfold oldPlusBit oldMinusBit
    congr 1
    unfold k WindowedMStarStep.position
    push_cast
    ring
  have hnewBit : (R.tileAt t j).1.newPlusBit =
      (R.tileAt t k).1.newMinusBit := by
    rw [(R.tileAt_bits t j).2.2.2, (R.tileAt_bits t k).2.2.1]
    unfold newPlusBit newMinusBit
    congr 1
    unfold k WindowedMStarStep.position
    push_cast
    ring
  have htoken : (R.tileAt t j).1.northToken =
      (R.tileAt t k).1.southToken := by
    simpa [k] using R.tileAt_token_match t j hj
  simp only [higherBlockTableauWangTile]
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext <;> assumption
    · apply Prod.ext <;> assumption
  · apply Prod.ext
    · apply Prod.ext <;> assumption
    · exact htoken

theorem stepWindow_before {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) :
    (R.stepWindow t).before = R.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩ := rfl

theorem stepWindow_after {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) :
    (R.stepWindow t).after = R.config ⟨t.1 + 1, by omega⟩ := rfl

theorem stepWindow_uniform_origin {width n : ℕ}
    (R : UniformWindowedMStarRun width n) (t : Fin n) :
    (R.stepWindow t).origin = R.origin := rfl

theorem stepWindow_old_strip_overlap {width n : ℕ}
    (R : UniformWindowedMStarRun width n) (t : Fin n)
    (j : Fin width) (hj : j.1 + 1 < width) :
    ((R.stepWindow t).oldStrip j).center =
        ((R.stepWindow t).oldStrip ⟨j.1 + 1, hj⟩).minus ∧
      ((R.stepWindow t).oldStrip j).plus =
        ((R.stepWindow t).oldStrip ⟨j.1 + 1, hj⟩).center :=
  (R.stepWindow t).oldStrip_overlap j hj

theorem final_state_accept {width n : ℕ} (R : UniformWindowedMStarRun width n) :
    (R.config ⟨n, Nat.lt_succ_self n⟩).state = MStarOuterProgram.State.accept :=
  R.final_accept

/-- Reverse chronological horizontal coordinate for the higher-block Wang
orientation (east is old, west is new). -/
def revTime {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.1, by omega⟩

theorem revTime_succ {n : ℕ} (i : Fin n) (hi : i.1 + 1 < n) :
    (revTime ⟨i.1 + 1, hi⟩).1 + 1 = (revTime i).1 := by
  change n - 1 - (i.1 + 1) + 1 = n - 1 - i.1
  omega

theorem consecutive_strip {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin n) (ht : t.1 + 1 < n) (j : Fin width) :
    (R.stepWindow t).newStrip j =
      (R.stepWindow ⟨t.1 + 1, ht⟩).oldStrip j := rfl

/-- The full finite higher-block tableau associated with a uniform run.  Time
is reversed horizontally because tableau east colours are old strips and west
colours are new strips. -/
def tableauTiling {width n : ℕ} (R : UniformWindowedMStarRun width n) :
    OpenWangTiling (higherBlockTableauWangTile Fixed.Machine) n width := by
  refine ⟨fun i j => R.tileAt (revTime i) j, ?_⟩
  constructor
  · intro i j hi
    let t : Fin n := revTime ⟨i.1 + 1, hi⟩
    have ht : t.1 + 1 < n := by
      dsimp [t]
      rw [revTime_succ i hi]
      exact (revTime i).2
    have htime : (⟨t.1 + 1, ht⟩ : Fin n) = revTime i := by
      apply Fin.ext
      dsimp [t]
      exact revTime_succ i hi
    change (R.tileAt (revTime i) j).1.old = (R.tileAt t j).1.new
    rw [R.tileAt_old, R.tileAt_new]
    have hstrip := R.consecutive_strip t ht j
    rw [htime] at hstrip
    exact hstrip.symm
  · intro i j hj
    exact R.vertical_match_tileAt (revTime i) j hj

theorem tableauTiling_cell_old {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (i : Fin n) (j : Fin width) :
    (R.tableauTiling.1 i j).1.old =
      (R.stepWindow (revTime i)).oldStrip j :=
  R.tileAt_old (revTime i) j

theorem tableauTiling_cell_new {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (i : Fin n) (j : Fin width) :
    (R.tableauTiling.1 i j).1.new =
      (R.stepWindow (revTime i)).newStrip j :=
  R.tileAt_new (revTime i) j

end UniformWindowedMStarRun

/-- The live, non-dummy tiles of the fixed four-track Wang system. -/
abbrev CoupledTrack := {u : Fixed.Tracks // Fixed.Coupled u}

/-- The live subsystem before the register construction adjoins its private
dummy tile. -/
abbrev coupledWangTile :=
  wProdComputeTile Fixed.Q
    (higherBlockTableauWangTile Fixed.Machine) Fixed.Coupled

abbrev CoupledWangTiling (w h : ℕ) :=
  OpenWangTiling coupledWangTile w h

/-- The fixed register-facing Wang system, including the private dummy tile. -/
abbrev FixedWangTiling (w h : ℕ) :=
  OpenWangTiling Fixed.wangTile w h

/-- A register-facing tiling is in computation mode exactly when no cell uses
the private dummy tile. -/
def ComputationMode {w h : ℕ} (f : FixedWangTiling w h) : Prop :=
  ∀ i j, (f.1 i j).isSome = true

/-- Remove the private dummy layer from a computation-mode fixed tiling. -/
def stripDummy {w h : ℕ} (f : FixedWangTiling w h)
    (hcompute : ComputationMode f) : CoupledWangTiling w h :=
  stripDummyTiling
    (wProdComputeTile Fixed.Q
      (higherBlockTableauWangTile Fixed.Machine) Fixed.Coupled)
    f hcompute

/-- The underlying four-track tile at one live cell. -/
def trackAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) : Fixed.Tracks :=
  (f.1 i j).1

theorem coupledAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) : Fixed.Coupled (trackAt f i j) :=
  (f.1 i j).2

/-- The three computation tracks read at one live cell. -/
def ampAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) : SharedQAmpTile Fixed.Q :=
  (trackAt f i j).1.1.1

def rippleAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) : RippleTile :=
  (trackAt f i j).1.1.2

def tableauAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    HigherBlockTableauTile Fixed.State Fixed.Tape Fixed.Arrow Fixed.Machine :=
  (trackAt f i j).1.2

def scannerAt {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) : ConcretePakScanner.Tile :=
  (trackAt f i j).2

/-- Forget the same-cell coupling proof, retaining the ordinary product
tiling.  This is the gateway to the verified component projections. -/
def productProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling
      (wProdTracksTile (ScanState := ConcretePakScanner.State)
        Fixed.Q (higherBlockTableauWangTile Fixed.Machine)) w h :=
  (coupledOpenEmbedding
    (wProdTracksTile (ScanState := ConcretePakScanner.State)
      Fixed.Q (higherBlockTableauWangTile Fixed.Machine))
    Fixed.Coupled w h) f

def firstThreeProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling
      (wangProductTile
        (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
        (higherBlockTableauWangTile Fixed.Machine)) w h :=
  openWangProductFst
    (wangProductTile
      (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
      (higherBlockTableauWangTile Fixed.Machine))
    (scannerTile (S := ConcretePakScanner.State))
    (productProjection f)

def ampRippleProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling
      (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile) w h :=
  openWangProductFst
    (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
    (higherBlockTableauWangTile Fixed.Machine)
    (firstThreeProjection f)

/-- The fixed tableau encoded by a live coupled Wang tiling. -/
abbrev MStarComputationTableau (w h : ℕ) :=
  OpenWangTiling (higherBlockTableauWangTile Fixed.Machine) w h

def tableauProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    MStarComputationTableau w h :=
  openWangProductSnd
    (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
    (higherBlockTableauWangTile Fixed.Machine)
    (firstThreeProjection f)

def amplifierProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling (sharedQAmpWangTile Fixed.Q) w h :=
  openWangProductFst (sharedQAmpWangTile Fixed.Q) rippleTile
    (ampRippleProjection f)

def rippleProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling rippleTile w h :=
  openWangProductSnd (sharedQAmpWangTile Fixed.Q) rippleTile
    (ampRippleProjection f)

def scannerProjection {w h : ℕ} (f : CoupledWangTiling w h) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State)) w h :=
  openWangProductSnd
    (wangProductTile
      (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
      (higherBlockTableauWangTile Fixed.Machine))
    (scannerTile (S := ConcretePakScanner.State))
    (productProjection f)

theorem tableauProjection_cell {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    (tableauProjection f).1 i j = tableauAt f i j := rfl

theorem amplifierProjection_cell {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    (amplifierProjection f).1 i j = ampAt f i j := rfl

theorem rippleProjection_cell {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    (rippleProjection f).1 i j = rippleAt f i j := rfl

theorem scannerProjection_cell {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    (scannerProjection f).1 i j = scannerAt f i j := rfl

/-- The diode scanner is globally confined to the east column.  This is a
genuine whole-frame consequence of horizontal Wang matching, rather than a
same-cell coupling clause. -/
theorem scannerAt_interior_idle {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    scannerAt f i j = none := by
  have hmatch : (scannerTile (scannerAt f i j)).east =
      (scannerTile (scannerAt f ⟨i.1 + 1, hi⟩ j)).west := by
    simpa only [scannerProjection_cell] using
      (scannerProjection f).2.1 i j hi
  cases hscan : scannerAt f i j with
  | none => rfl
  | some st =>
      cases hnext : scannerAt f ⟨i.1 + 1, hi⟩ j with
      | none => simp [scannerTile, hscan, hnext] at hmatch
      | some st' => simp [scannerTile, hscan, hnext] at hmatch

/-- Reusable uniqueness principle for live coupled tilings.  In particular,
all four component projections together determine the original coupled tiling. -/
theorem coupledTiling_ext {w h : ℕ} (f g : CoupledWangTiling w h)
    (hfg : ∀ i j, trackAt f i j = trackAt g i j) : f = g := by
  apply Subtype.ext
  funext i j
  apply Subtype.ext
  exact hfg i j

/-- Complete readback data of the four fixed tracks. -/
@[ext] structure FrameReadout (w h : ℕ) where
  amplifier : OpenWangTiling (sharedQAmpWangTile Fixed.Q) w h
  ripple : OpenWangTiling rippleTile w h
  tableau : MStarComputationTableau w h
  scanner : OpenWangTiling (scannerTile (S := ConcretePakScanner.State)) w h

def readout {w h : ℕ} (f : CoupledWangTiling w h) : FrameReadout w h where
  amplifier := amplifierProjection f
  ripple := rippleProjection f
  tableau := tableauProjection f
  scanner := scannerProjection f

/-- The four projected tracks determine every live coupled cell, hence the
entire finite frame. -/
theorem coupledTiling_ext_of_projections {w h : ℕ}
    (f g : CoupledWangTiling w h)
    (ha : amplifierProjection f = amplifierProjection g)
    (hr : rippleProjection f = rippleProjection g)
    (ht : tableauProjection f = tableauProjection g)
    (hs : scannerProjection f = scannerProjection g) : f = g := by
  apply coupledTiling_ext f g
  intro i j
  have haij : ampAt f i j = ampAt g i j := by
    have h := congrFun (congrFun (congrArg Subtype.val ha) i) j
    simpa only [amplifierProjection_cell] using h
  have hrij : rippleAt f i j = rippleAt g i j := by
    have h := congrFun (congrFun (congrArg Subtype.val hr) i) j
    simpa only [rippleProjection_cell] using h
  have htij : tableauAt f i j = tableauAt g i j := by
    have h := congrFun (congrFun (congrArg Subtype.val ht) i) j
    simpa only [tableauProjection_cell] using h
  have hsij : scannerAt f i j = scannerAt g i j := by
    have h := congrFun (congrFun (congrArg Subtype.val hs) i) j
    simpa only [scannerProjection_cell] using h
  change
    (((ampAt f i j, rippleAt f i j), tableauAt f i j), scannerAt f i j) =
      (((ampAt g i j, rippleAt g i j), tableauAt g i j), scannerAt g i j)
  rw [haij, hrij, htij, hsij]

theorem readout_injective {w h : ℕ} : Function.Injective (readout (w := w) (h := h)) := by
  intro f g hfg
  apply coupledTiling_ext_of_projections f g
  · exact congrArg (fun r : FrameReadout w h => r.amplifier) hfg
  · exact congrArg (fun r : FrameReadout w h => r.ripple) hfg
  · exact congrArg (fun r : FrameReadout w h => r.tableau) hfg
  · exact congrArg (fun r : FrameReadout w h => r.scanner) hfg

/-- The fixed local five-coupling specification at an arbitrary live cell. -/
theorem coupledAt_iff {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) :
    PakCouplingGenerated.West MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
        (trackAt f i j) ∧
      PakCouplingGenerated.East MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
        (trackAt f i j) ∧
      PakCouplingGenerated.South MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
        (trackAt f i j) ∧
      PakCouplingGenerated.North MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
        (trackAt f i j) ∧
      PakCouplingGenerated.NonEast Fixed.Machine Fixed.Q (trackAt f i j) := by
  exact
    (PakCouplingGenerated.fiveCouplings_accepts_iff
      MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q (trackAt f i j)).mp
      (coupledAt f i j)

theorem nonEast_idle {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h)
    (he : (ampAt f i j).1.eastActive = false) : scannerAt f i j = none := by
  exact (coupledAt_iff f i j).2.2.2.2 he

theorem coupledEastEmitsTableauWindow {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h)
    (he : (ampAt f i j).1.eastActive = true) :
    ∃ s t : ConcretePakScanner.State,
      scannerAt f i j = some (s, t) ∧
      (tableauAt f i j).1.old =
        PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t := by
  exact PakCouplingGenerated.coupled_east_marked
    MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
    (coupledAt f i j) he

/-- Combining the east coupling with the global diode strip shows that east
amplifier activity cannot occur away from the east frame. -/
theorem eastActive_eq_false_of_interior {w h : ℕ}
    (f : CoupledWangTiling w h) (i : Fin w) (j : Fin h)
    (hi : i.1 + 1 < w) : (ampAt f i j).1.eastActive = false := by
  apply Bool.eq_false_of_not_eq_true
  intro he
  rcases coupledEastEmitsTableauWindow f i j he with ⟨s, t, hscan, _⟩
  have hidle := scannerAt_interior_idle f i j hi
  simp [hidle] at hscan

/-- The amplifier's dead horizontal colour confines west activity to the west
edge of every coupled frame. -/
theorem westActive_on_west_boundary {w h : ℕ}
    (f : CoupledWangTiling w h) (i : Fin w) (j : Fin h)
    (ha : (ampAt f i j).1.westActive = true) : i.1 = 0 := by
  by_contra hi
  let il : Fin w := ⟨i.1 - 1, by omega⟩
  have hmatch := (amplifierProjection f).2.1 il j (by dsimp [il]; omega)
  have hil : (⟨il.1 + 1, by dsimp [il]; omega⟩ : Fin w) = i := by
    apply Fin.ext
    dsimp [il]
    omega
  rw [hil, amplifierProjection_cell, amplifierProjection_cell] at hmatch
  have hdead := congrArg AmpHorizontalColour.westDead hmatch
  simp [sharedQAmpWangTile, ha] at hdead

/-- The amplifier's dead horizontal colour confines east activity to the east
edge of every coupled frame. -/
theorem eastActive_on_east_boundary {w h : ℕ}
    (f : CoupledWangTiling w h) (i : Fin w) (j : Fin h)
    (ha : (ampAt f i j).1.eastActive = true) : i.1 + 1 = w := by
  by_contra hi
  have hinext : i.1 + 1 < w := by omega
  have hmatch := (amplifierProjection f).2.1 i j hinext
  rw [amplifierProjection_cell, amplifierProjection_cell] at hmatch
  have hdead := congrArg AmpHorizontalColour.eastDead hmatch
  simp [sharedQAmpWangTile, ha] at hdead

/-- The amplifier's dead vertical colour confines south activity to the south
edge of every coupled frame. -/
theorem southActive_on_south_boundary {w h : ℕ}
    (f : CoupledWangTiling w h) (i : Fin w) (j : Fin h)
    (ha : (ampAt f i j).1.southActive = true) : j.1 = 0 := by
  by_contra hj
  let jb : Fin h := ⟨j.1 - 1, by omega⟩
  have hmatch := (amplifierProjection f).2.2 i jb (by dsimp [jb]; omega)
  have hjb : (⟨jb.1 + 1, by dsimp [jb]; omega⟩ : Fin h) = j := by
    apply Fin.ext
    dsimp [jb]
    omega
  rw [hjb, amplifierProjection_cell, amplifierProjection_cell] at hmatch
  have hdead := congrArg AmpVerticalColour.southDead hmatch
  simp [sharedQAmpWangTile, ha] at hdead

/-- The amplifier's dead vertical colour confines north activity to the north
edge of every coupled frame. -/
theorem northActive_on_north_boundary {w h : ℕ}
    (f : CoupledWangTiling w h) (i : Fin w) (j : Fin h)
    (ha : (ampAt f i j).1.northActive = true) : j.1 + 1 = h := by
  by_contra hj
  have hjnext : j.1 + 1 < h := by omega
  have hmatch := (amplifierProjection f).2.2 i j hjnext
  rw [amplifierProjection_cell, amplifierProjection_cell] at hmatch
  have hdead := congrArg AmpVerticalColour.northDead hmatch
  simp [sharedQAmpWangTile, ha] at hdead

theorem coupledWestAccepts {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h)
    (hw : (ampAt f i j).1.westActive = true) :
    (rippleAt f i j).1 = false ∧
      PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
        (tableauAt f i j).1.new ∧
      scannerAt f i j = none := by
  exact (coupledAt_iff f i j).1 hw

theorem coupledSouthHasSentinel {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h)
    (hs : (ampAt f i j).1.southActive = true) :
    (rippleAt f i j).2 = true ∧
      PakCouplingGenerated.southSentinel MStarULogAssembly.boundaryData Fixed.Machine
        (tableauAt f i j) := by
  have hlocal := (coupledAt_iff f i j).2.2.1 hs
  exact ⟨hlocal.1, hlocal.2.1⟩

theorem coupledNorthHasSentinel {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h)
    (hn : (ampAt f i j).1.northActive = true) :
    ((rippleAt f i j).1 && (rippleAt f i j).2) = false ∧
      PakCouplingGenerated.northSentinel MStarULogAssembly.boundaryData Fixed.Machine
        (tableauAt f i j) := by
  have hlocal := (coupledAt_iff f i j).2.2.2.1 hn
  exact ⟨hlocal.1, hlocal.2.1⟩

def eastIndex {w : ℕ} (hw : 0 < w) : Fin w := ⟨w - 1, by omega⟩

def northIndex {h : ℕ} (hh : 0 < h) : Fin h := ⟨h - 1, by omega⟩

/-- The literal four-side condition for a full computation frame.  It makes
no reachability or filling claim: it only identifies the amplifier activity
bits exposed at the geometric boundary. -/
def FourSideBoundary {w h : ℕ} (f : CoupledWangTiling w h)
    (hw : 0 < w) (hh : 0 < h) : Prop :=
  (∀ j : Fin h, (ampAt f ⟨0, hw⟩ j).1.westActive = true) ∧
  (∀ j : Fin h, (ampAt f (eastIndex hw) j).1.eastActive = true) ∧
  (∀ i : Fin w, (ampAt f i ⟨0, hh⟩).1.southActive = true) ∧
  (∀ i : Fin w, (ampAt f i (northIndex hh)).1.northActive = true)

/-- A nondegenerate coupled tiling equipped with the literal four-side
activity boundary. -/
@[ext] structure FullFrame (w h : ℕ) where
  tiling : CoupledWangTiling w h
  width_pos : 0 < w
  height_pos : 0 < h
  boundary : FourSideBoundary tiling width_pos height_pos

def FullFrame.tableau {w h : ℕ} (F : FullFrame w h) :
    MStarComputationTableau w h :=
  tableauProjection F.tiling

/-- Read every fixed component track of a full frame.  This is a concrete
readback map on the full-frame subtype, with no global simulation theorem
stored in its definition. -/
def FullFrame.readout {w h : ℕ} (F : FullFrame w h) : FrameReadout w h :=
  PakFixedPolyomino.PakMStarCouplingCorrectness.readout F.tiling

theorem FullFrame.readout_injective {w h : ℕ} :
    Function.Injective (FullFrame.readout (w := w) (h := h)) := by
  intro F G hreadout
  cases F with
  | mk f fw fh fb =>
      cases G with
      | mk g gw gh gb =>
          dsimp [FullFrame.readout] at hreadout
          have htiling : f = g :=
            PakFixedPolyomino.PakMStarCouplingCorrectness.readout_injective hreadout
          subst g
          rfl

theorem FullFrame.west_accepts {w h : ℕ} (F : FullFrame w h) (j : Fin h) :
    (rippleAt F.tiling ⟨0, F.width_pos⟩ j).1 = false ∧
      PakCouplingGenerated.acceptingWindow MStarULogAssembly.boundaryData
        (tableauAt F.tiling ⟨0, F.width_pos⟩ j).1.new ∧
      scannerAt F.tiling ⟨0, F.width_pos⟩ j = none := by
  exact coupledWestAccepts F.tiling ⟨0, F.width_pos⟩ j (F.boundary.1 j)

theorem FullFrame.east_emits_tableau_window {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) :
    ∃ s t : ConcretePakScanner.State,
      scannerAt F.tiling (eastIndex F.width_pos) j = some (s, t) ∧
      (tableauAt F.tiling (eastIndex F.width_pos) j).1.old =
        PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t := by
  exact coupledEastEmitsTableauWindow F.tiling (eastIndex F.width_pos) j
    (F.boundary.2.1 j)

theorem FullFrame.south_has_sentinel {w h : ℕ} (F : FullFrame w h)
    (i : Fin w) :
    (rippleAt F.tiling i ⟨0, F.height_pos⟩).2 = true ∧
      PakCouplingGenerated.southSentinel MStarULogAssembly.boundaryData Fixed.Machine
        (tableauAt F.tiling i ⟨0, F.height_pos⟩) := by
  exact coupledSouthHasSentinel F.tiling i ⟨0, F.height_pos⟩
    (F.boundary.2.2.1 i)

theorem FullFrame.north_has_sentinel {w h : ℕ} (F : FullFrame w h)
    (i : Fin w) :
    ((rippleAt F.tiling i (northIndex F.height_pos)).1 &&
        (rippleAt F.tiling i (northIndex F.height_pos)).2) = false ∧
      PakCouplingGenerated.northSentinel MStarULogAssembly.boundaryData Fixed.Machine
        (tableauAt F.tiling i (northIndex F.height_pos)) := by
  exact coupledNorthHasSentinel F.tiling i (northIndex F.height_pos)
    (F.boundary.2.2.2 i)

/-- At the south-east corner the full-frame boundary is read back as the
literal scanner bottom state. -/
theorem FullFrame.east_bottom_scanner {w h : ℕ} (F : FullFrame w h) :
    ∃ t : ConcretePakScanner.State,
      scannerAt F.tiling (eastIndex F.width_pos) ⟨0, F.height_pos⟩ =
        some (PakCouplingGenerated.scannerBottom, t) := by
  have hlocal := (coupledAt_iff F.tiling (eastIndex F.width_pos)
    ⟨0, F.height_pos⟩).2.2.1
    (F.boundary.2.2.1 (eastIndex F.width_pos))
  exact hlocal.2.2 (F.boundary.2.1 ⟨0, F.height_pos⟩)

/-- At the north-east corner the full-frame boundary is read back as the
literal top scanner state and high-mode hash condition. -/
theorem FullFrame.east_top_scanner {w h : ℕ} (F : FullFrame w h) :
    ∃ s t : ConcretePakScanner.State,
      scannerAt F.tiling (eastIndex F.width_pos) (northIndex F.height_pos) =
        some (s, t) ∧ PakCouplingGenerated.scannerTopSouth s := by
  have hlocal := (coupledAt_iff F.tiling (eastIndex F.width_pos)
    (northIndex F.height_pos)).2.2.2.1
    (F.boundary.2.2.2 (eastIndex F.width_pos))
  exact hlocal.2.2 (F.boundary.2.1 (northIndex F.height_pos))

/-- Every strict interior point of the east scanner column has the repaired
middle phase and zero lookahead.  The proof uses vertical amplifier matching
to rule out both endpoint activities, then the generated K-E phase clause. -/
theorem FullFrame.east_internal_phase {w h : ℕ} (F : FullFrame w h)
    (j : Fin h) (hj0 : 0 < j.1) (hjtop : j.1 + 1 < h) :
    ∃ s t : ConcretePakScanner.State,
      scannerAt F.tiling (eastIndex F.width_pos) j = some (s, t) ∧
      s.phase = .mid ∧ s.lookahead = .lh0 := by
  have heast := F.boundary.2.1 j
  rcases coupledEastEmitsTableauWindow F.tiling (eastIndex F.width_pos) j heast with
    ⟨s, t, hscan, _⟩
  have hsouth : (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hs
    have hbottom := southActive_on_south_boundary F.tiling
      (eastIndex F.width_pos) j hs
    omega
  have hnorth : (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hn
    have htop := northActive_on_north_boundary F.tiling
      (eastIndex F.width_pos) j hn
    omega
  have hactivity := ((coupledAt_iff F.tiling (eastIndex F.width_pos) j).2.1 heast).1
  have hmiddle : ConcretePakScanner.ActivityCoupledStep false false
      (scannerAt F.tiling (eastIndex F.width_pos) j)
      (xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
        (rippleAt F.tiling (eastIndex F.width_pos) j).2) := by
    change ConcretePakScanner.ActivityCoupledStep
      (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive
      (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive
      (scannerAt F.tiling (eastIndex F.width_pos) j)
      (xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
        (rippleAt F.tiling (eastIndex F.width_pos) j).2) at hactivity
    rw [hsouth, hnorth] at hactivity
    exact hactivity
  rcases ConcretePakScanner.activityCoupled_middle_phase
      (scannerAt F.tiling (eastIndex F.width_pos) j)
      (xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
        (rippleAt F.tiling (eastIndex F.width_pos) j).2)
      s t hscan hmiddle with ⟨hphase, hlookahead⟩
  exact ⟨s, t, hscan, hphase, hlookahead⟩

/-- A full frame cannot collapse its south and north boundaries into one row:
the east scanner coupling forbids simultaneous vertical endpoint activity. -/
theorem FullFrame.height_ge_two {w h : ℕ} (F : FullFrame w h) : 2 ≤ h := by
  by_contra hlt
  have hpos := F.height_pos
  have hone : h = 1 := by omega
  subst h
  let i : Fin w := eastIndex F.width_pos
  let j : Fin 1 := ⟨0, by omega⟩
  have heast : (ampAt F.tiling i j).1.eastActive = true := by
    simpa [i, j] using F.boundary.2.1 j
  have hsouth : (ampAt F.tiling i j).1.southActive = true := by
    simpa [i, j] using F.boundary.2.2.1 i
  have hnorth : (ampAt F.tiling i j).1.northActive = true := by
    simpa [i, j, northIndex] using F.boundary.2.2.2 i
  exact PakCouplingGenerated.coupled_no_double_vertical_activity
    MStarULogAssembly.boundaryData Fixed.Machine Fixed.Q
    (coupledAt F.tiling i j) heast ⟨hsouth, hnorth⟩

/-- The tableau readback of a coupled frame, viewed as one vertically matched
Wang column. -/
def tableauColumn {w h : ℕ} (f : CoupledWangTiling w h) (i : Fin w) :
    WangColumn (higherBlockTableauWangTile Fixed.Machine) h :=
  tilingColumn (higherBlockTableauWangTile Fixed.Machine)
    (tableauProjection f) i

/-- Adjacent rows of every extracted tableau column share their old radius-one
windows. -/
theorem tableau_old_overlap {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (tableauAt f i j).1.old.center =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.old.minus ∧
      (tableauAt f i j).1.old.plus =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.old.center := by
  exact HigherBlockTableau.vertical_old_overlap Fixed.Machine
    (tableauColumn f i) j hj

/-- Adjacent rows of every extracted tableau column share their new radius-one
windows. -/
theorem tableau_new_overlap {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (tableauAt f i j).1.new.center =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.new.minus ∧
      (tableauAt f i j).1.new.plus =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.new.center := by
  exact HigherBlockTableau.vertical_new_overlap Fixed.Machine
    (tableauColumn f i) j hj

/-- The order bits and transition token also propagate exactly up a tableau
column. -/
theorem tableau_bits_tokens_overlap {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (tableauAt f i j).1.oldPlusBit =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.oldMinusBit ∧
      (tableauAt f i j).1.newPlusBit =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.newMinusBit ∧
      (tableauAt f i j).1.northToken =
        (tableauAt f i ⟨j.1 + 1, hj⟩).1.southToken := by
  exact HigherBlockTableau.vertical_bits_tokens Fixed.Machine
    (tableauColumn f i) j hj

/-- The full coupled frame inherits the higher-block global no-double-head
property in each of its tableau columns. -/
theorem tableau_old_head_unique {w h : ℕ} (f : CoupledWangTiling w h)
    (i : Fin w) {j k : Fin h}
    (hj : (tableauAt f i j).1.old.center.isHead = true)
    (hk : (tableauAt f i k).1.old.center.isHead = true) : j = k := by
  exact HigherBlockTableau.old_visible_head_unique Fixed.Machine
    (tableauColumn f i) hj hk

/-- Reassemble the first two product tracks of a readout. -/
def FrameReadout.ampRippleAssembly {w h : ℕ} (r : FrameReadout w h) :
    OpenWangTiling
      (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile) w h :=
  (openWangProductEquiv (sharedQAmpWangTile Fixed.Q) rippleTile w h).symm
    (r.amplifier, r.ripple)

/-- Reassemble the amplifier/ripple/tableau part of a readout. -/
def FrameReadout.firstThreeAssembly {w h : ℕ} (r : FrameReadout w h) :
    OpenWangTiling
      (wangProductTile
        (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
        (higherBlockTableauWangTile Fixed.Machine)) w h :=
  (openWangProductEquiv
    (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
    (higherBlockTableauWangTile Fixed.Machine) w h).symm
      (r.ampRippleAssembly, r.tableau)

/-- Reassemble all four uncoupled product tracks from their Wang readouts. -/
def FrameReadout.productAssembly {w h : ℕ} (r : FrameReadout w h) :
    OpenWangTiling
      (wProdTracksTile (ScanState := ConcretePakScanner.State)
        Fixed.Q (higherBlockTableauWangTile Fixed.Machine)) w h :=
  (openWangProductEquiv
    (wangProductTile
      (wangProductTile (sharedQAmpWangTile Fixed.Q) rippleTile)
      (higherBlockTableauWangTile Fixed.Machine))
    (scannerTile (S := ConcretePakScanner.State)) w h).symm
      (r.firstThreeAssembly, r.scanner)

/-- Compatibility is the concrete global condition left after the four tracks
have independently been reconstructed: their tile at every cell must pass the
fixed generated five-coupling table. -/
def ReadoutCompatible {w h : ℕ} (r : FrameReadout w h) : Prop :=
  ∀ i j, Fixed.Coupled (r.productAssembly.1 i j)

abbrev CompatibleFrameReadout (w h : ℕ) :=
  {r : FrameReadout w h // ReadoutCompatible r}

/-- Assemble a live coupled tiling from compatible component readouts. -/
def assembleCoupledReadout {w h : ℕ}
    (r : CompatibleFrameReadout w h) : CoupledWangTiling w h := by
  refine ⟨fun i j => ⟨r.1.productAssembly.1 i j, r.2 i j⟩, ?_⟩
  exact r.1.productAssembly.2

theorem productAssembly_readout {w h : ℕ} (f : CoupledWangTiling w h) :
    (readout f).productAssembly = productProjection f := by
  apply Subtype.ext
  funext i j
  rfl

theorem readout_compatible {w h : ℕ} (f : CoupledWangTiling w h) :
    ReadoutCompatible (readout f) := by
  intro i j
  rw [productAssembly_readout]
  exact coupledAt f i j

theorem readout_assembleCoupledReadout {w h : ℕ}
    (r : CompatibleFrameReadout w h) :
    readout (assembleCoupledReadout r) = r.1 := by
  apply FrameReadout.ext <;> apply Subtype.ext <;> funext i j <;> rfl

/-- At the track level, coupling is exactly the compatibility condition on the
four independently tiled readout tracks. -/
def coupledReadoutEquiv (w h : ℕ) :
    CoupledWangTiling w h ≃ CompatibleFrameReadout w h where
  toFun f := ⟨readout f, readout_compatible f⟩
  invFun := assembleCoupledReadout
  left_inv f := by
    apply readout_injective
    simpa using readout_assembleCoupledReadout
      (⟨readout f, readout_compatible f⟩ : CompatibleFrameReadout w h)
  right_inv r := by
    apply Subtype.ext
    exact readout_assembleCoupledReadout r

/-- Compatible readouts with the literal four-side activity boundary. -/
@[ext] structure FullFrameReadout (w h : ℕ) where
  readout : CompatibleFrameReadout w h
  width_pos : 0 < w
  height_pos : 0 < h
  boundary : FourSideBoundary (assembleCoupledReadout readout) width_pos height_pos

def fullFrameReadoutEquiv (w h : ℕ) : FullFrame w h ≃ FullFrameReadout w h where
  toFun F :=
    { readout := coupledReadoutEquiv w h F.tiling
      width_pos := F.width_pos
      height_pos := F.height_pos
      boundary := by
        change FourSideBoundary
          ((coupledReadoutEquiv w h).symm
            ((coupledReadoutEquiv w h) F.tiling)) _ _
        simpa only [Equiv.symm_apply_apply] using F.boundary }
  invFun R :=
    { tiling := assembleCoupledReadout R.readout
      width_pos := R.width_pos
      height_pos := R.height_pos
      boundary := R.boundary }
  left_inv F := by
    apply FullFrame.ext
    exact (coupledReadoutEquiv w h).left_inv F.tiling
  right_inv R := by
    apply FullFrameReadout.ext
    exact (coupledReadoutEquiv w h).right_inv R.readout

/-- A finite fixed M-star tableau history is exactly the four reconstructed
tracks, their pointwise generated coupling proofs, and the literal full-frame
boundary. This is intentionally a concrete data type, not a semantic
correctness assumption. -/
abbrev FixedMStarTableauHistory (w h : ℕ) := FullFrameReadout w h

def FullFrame.toFixedMStarTableauHistory {w h : ℕ} (F : FullFrame w h) :
    FixedMStarTableauHistory w h :=
  fullFrameReadoutEquiv w h F

def FixedMStarTableauHistory.toFullFrame {w h : ℕ}
    (H : FixedMStarTableauHistory w h) : FullFrame w h :=
  (fullFrameReadoutEquiv w h).symm H

theorem FullFrame.history_readback {w h : ℕ} (F : FullFrame w h) :
    F.toFixedMStarTableauHistory.toFullFrame = F :=
  (fullFrameReadoutEquiv w h).symm_apply_apply F

theorem FixedMStarTableauHistory.frame_roundtrip {w h : ℕ}
    (H : FixedMStarTableauHistory w h) :
    H.toFullFrame.toFixedMStarTableauHistory = H :=
  (fullFrameReadoutEquiv w h).apply_symm_apply H

/-- A uniform operational run whose two visible window endpoints are genuine
hash cells at every time.  This is the minimum extra tableau-side padding
needed by the literal south/north sentinel clauses. -/
structure PaddedUniformWindowedMStarRun (width n : ℕ) where
  run : UniformWindowedMStarRun width n
  left_endpoint_hash : ∀ t : Fin (n + 1),
    (run.config t).tape run.origin = .hash
  right_endpoint_hash : ∀ t : Fin (n + 1),
    (run.config t).tape (run.origin + (width - 1 : ℕ)) = .hash

/-- The non-tableau tracks needed to fill a literal coupled frame around a
padded uniform run.  They are supplied independently as Wang tilings, rather
than smuggling a `FullFrame` into the certificate; the tableau track is always
the one constructed from `run.tableauTiling`. -/
@[ext] structure FullTrackRunCertificate {width n : ℕ}
    (P : PaddedUniformWindowedMStarRun width n) where
  time_pos : 0 < n
  amplifier : OpenWangTiling (sharedQAmpWangTile Fixed.Q) n width
  ripple : OpenWangTiling rippleTile n width
  scanner : OpenWangTiling (scannerTile (S := ConcretePakScanner.State)) n width
  coupled : ∀ i j,
    Fixed.Coupled (((amplifier.1 i j, ripple.1 i j),
      P.run.tableauTiling.1 i j), scanner.1 i j)
  west_boundary : ∀ j : Fin width,
    (amplifier.1 ⟨0, time_pos⟩ j).1.westActive = true
  east_boundary : ∀ j : Fin width,
    (amplifier.1 ⟨n - 1, by omega⟩ j).1.eastActive = true
  south_boundary : ∀ i : Fin n,
    (amplifier.1 i ⟨0, Nat.lt_of_lt_of_le (by decide) P.run.width_ge_three⟩).1.southActive = true
  north_boundary : ∀ i : Fin n,
    (amplifier.1 i ⟨width - 1, by
      have hw := P.run.width_ge_three
      omega⟩).1.northActive = true

namespace FullTrackRunCertificate

def readout {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) : FrameReadout n width where
  amplifier := C.amplifier
  ripple := C.ripple
  tableau := P.run.tableauTiling
  scanner := C.scanner

theorem readout_compatible {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) : ReadoutCompatible C.readout := by
  intro i j
  change Fixed.Coupled (((C.amplifier.1 i j, C.ripple.1 i j),
    P.run.tableauTiling.1 i j), C.scanner.1 i j)
  exact C.coupled i j

def compatibleReadout {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) : CompatibleFrameReadout n width :=
  ⟨C.readout, C.readout_compatible⟩

def coupledTiling {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) : CoupledWangTiling n width :=
  assembleCoupledReadout C.compatibleReadout

theorem amplifier_cell {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) (i : Fin n) (j : Fin width) :
    ampAt C.coupledTiling i j = C.amplifier.1 i j := rfl

/-- Assemble the supplied non-tableau tracks and the run-generated tableau
into an actual live coupled full frame. -/
def toFullFrame {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) : FullFrame n width where
  tiling := C.coupledTiling
  width_pos := C.time_pos
  height_pos := Nat.lt_of_lt_of_le (by decide) P.run.width_ge_three
  boundary := by
    constructor
    · intro j
      rw [C.amplifier_cell]
      exact C.west_boundary j
    constructor
    · intro j
      rw [C.amplifier_cell]
      exact C.east_boundary j
    constructor
    · intro i
      rw [C.amplifier_cell]
      exact C.south_boundary i
    · intro i
      rw [C.amplifier_cell]
      exact C.north_boundary i

theorem toFullFrame_tableau {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) :
    C.toFullFrame.tableau = P.run.tableauTiling := by
  apply Subtype.ext
  funext i j
  rfl

/-- The four-track readback of the assembled frame is exactly the certified
track data; this is the converse at the track level. -/
theorem toFullFrame_readout {width n : ℕ} {P : PaddedUniformWindowedMStarRun width n}
    (C : FullTrackRunCertificate P) :
    C.toFullFrame.readout = C.readout := by
  change PakFixedPolyomino.PakMStarCouplingCorrectness.readout
      (assembleCoupledReadout C.compatibleReadout) = C.readout
  exact readout_assembleCoupledReadout C.compatibleReadout

end FullTrackRunCertificate

/-
The next irreducible theorem is a global frame-filling result: from a finite
accepting run of the fixed MStarULogAssembly.program, together with the chosen
encoded input and a sufficiently large rectangular time/space budget, construct
a FullFrame whose tableau is that run's higher-block tableau.  Its converse
must also read the west/east/south/north frame into the intended initial and
accepting configurations.  The generated five couplings prove the cellwise
facts used above, but do not prove this global existence/readback statement.
-/

end

end PakFixedPolyomino.PakMStarCouplingCorrectness
