import PakFixedPolyomino.ULogSourceLogicalBlockReader
import PakFixedPolyomino.ULogSourceOneHotWriter
import Mathlib.Tactic

/-!
# Physical representation relation for source blocks

An initialized logical tape cell is stored as its fixed-width one-hot block.
An untouched logical blank may still be a full block of the third physical
letter.  Keeping this as a relation (rather than prematurely canonicalizing
the whole infinite tape) is essential when a simulated head first enters an
unvisited cell.
-/

namespace PakFixedPolyomino.ULogSourceOneHotRepresentation

open ULogSourceOneHotBlocks

abbrev Tape := Fin 3
abbrev physicalBlank : Tape := ULogSourceOneHotReader.blank

variable {nt : ℕ}

def IsPhysicalBlankAt (tape : Int → Tape) (head : Int) (nt : ℕ) : Prop :=
  ∀ i : ℕ, i < nt → tape (head + i) = physicalBlank

/-- Operational focus representation used by repeated source simulation. -/
def RepresentsAt (logicalBlank logical : Fin nt) (tape : Int → Tape)
    (head : Int) : Prop :=
  ULogSourceLogicalBlockReader.IsOneHotAt logical tape head ∨
    (logical = logicalBlank ∧ IsPhysicalBlankAt tape head nt)

theorem representsAt_oneHot (logicalBlank logical : Fin nt)
    (tape : Int → Tape) (head : Int)
    (h : ULogSourceLogicalBlockReader.IsOneHotAt logical tape head) :
    RepresentsAt logicalBlank logical tape head := Or.inl h

theorem representsAt_blank (logicalBlank : Fin nt) (tape : Int → Tape)
    (head : Int) (h : IsPhysicalBlankAt tape head nt) :
    RepresentsAt logicalBlank logicalBlank tape head := Or.inr ⟨rfl, h⟩

/-- The `nt` physical letters beginning at `head`. -/
def blockAt (tape : Int → Tape) (head : Int) (nt : ℕ) : List Tape :=
  List.ofFn fun i : Fin nt => tape (head + i.1)

/-- An initialized one-hot block, or the untouched physical realization of
the distinguished logical blank. -/
def RepresentsBlock (logicalBlank logical : Fin nt) (cells : List Tape) : Prop :=
  cells = ULogSourceOneHotReader.oneHotCells logical ∨
    (logical = logicalBlank ∧ cells = List.replicate nt physicalBlank)

theorem represents_oneHot (logicalBlank logical : Fin nt) :
    RepresentsBlock logicalBlank logical
      (ULogSourceOneHotReader.oneHotCells logical) := by
  exact Or.inl rfl

theorem represents_physicalBlank (logicalBlank : Fin nt) :
    RepresentsBlock logicalBlank logicalBlank
      (List.replicate nt physicalBlank) := by
  exact Or.inr ⟨rfl, rfl⟩

/-- Every represented block is decoded to its logical symbol by the literal
blank-aware reader. -/
theorem decode_of_represents {logicalBlank logical : Fin nt} {cells : List Tape}
    (h : RepresentsBlock logicalBlank logical cells) :
    ULogSourceLogicalBlockReader.decodeLogicalBlock logicalBlank cells =
      some logical := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact ULogSourceLogicalBlockReader.decodeLogicalBlock_oneHot _ _
  · exact ULogSourceLogicalBlockReader.decodeLogicalBlock_blank _

@[simp] theorem represents_length {logicalBlank logical : Fin nt}
    {cells : List Tape} (h : RepresentsBlock logicalBlank logical cells) :
    cells.length = nt := by
  rcases h with rfl | ⟨-, rfl⟩ <;> simp

/-- The writer canonicalizes a represented or unrepresented focus block to
the initialized one-hot representation of its target. -/
theorem writer_expected_represents (logicalBlank target : Fin nt)
    (head : Int) (tape : Int → Tape) :
    RepresentsBlock logicalBlank target
      (blockAt (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape
        head nt) := by
  left
  exact ULogSourceOneHotWriter.exact_block_cells target head tape

theorem writer_expected_isOneHotAt (logicalBlank target : Fin nt)
    (head : Int) (tape : Int → Tape) :
    ULogSourceLogicalBlockReader.IsOneHotAt target
      (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape head := by
  intro i hi
  rw [ULogSourceOneHotWriter.exact_block_cell target head tape ⟨i, hi⟩,
    ULogSourceOneHotWriter.targetCell_of_lt target i hi,
    encodeOneHot_getElem target i hi]
  by_cases h : i = target.val <;> simp [h, ULogSourceOneHotWriter.tapeOfBit,
    ULogSourceOneHotReader.tapeOfBit, ULogSourceLogicalBlockReader.one,
    ULogSourceLogicalBlockReader.zero]

theorem writer_expected_representsAt (logicalBlank target : Fin nt)
    (head : Int) (tape : Int → Tape) :
    RepresentsAt logicalBlank target
      (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape head :=
  Or.inl (writer_expected_isOneHotAt logicalBlank target head tape)

theorem writer_preserves_representsAt_shifted (hnt : 0 < nt)
    (logicalBlank target logical : Fin nt) (head : Int) (tape : Int → Tape)
    (offset : Int) (hoffset : offset ≠ 0)
    (hrep : RepresentsAt logicalBlank logical tape
      (head + offset * (nt : Int))) :
    RepresentsAt logicalBlank logical
      (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape
      (head + offset * (nt : Int)) := by
  have hout (i : ℕ) (hi : i < nt) :
      (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape
          (head + offset * (nt : Int) + i) =
        tape (head + offset * (nt : Int) + i) := by
    apply ULogSourceOneHotWriter.exact_block_outside
    rcases lt_or_gt_of_ne hoffset with hneg | hpos
    · left
      have hntInt : (0 : Int) < nt := by exact_mod_cast hnt
      have hiInt : (i : Int) < nt := by exact_mod_cast hi
      nlinarith
    · right
      have hntInt : (0 : Int) < nt := by exact_mod_cast hnt
      nlinarith
  rcases hrep with hone | ⟨rfl, hblank⟩
  · left
    intro i hi
    rw [hout i hi]
    exact hone i hi
  · right
    refine ⟨rfl, ?_⟩
    intro i hi
    rw [hout i hi]
    exact hblank i hi

/-- A block not touched by a writer pass remains represented. -/
theorem writer_preserves_disjoint_block
    (logicalBlank target logical : Fin nt) (head other : Int)
    (tape : Int → Tape)
    (hdisjoint : other + (nt : Int) ≤ head ∨ head + (nt : Int) ≤ other)
    (hrep : RepresentsBlock logicalBlank logical (blockAt tape other nt)) :
    RepresentsBlock logicalBlank logical
      (blockAt (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape
        other nt) := by
  have hcells :
      blockAt (ULogSourceOneHotWriter.expectedConfig target head tape nt).tape
          other nt = blockAt tape other nt := by
    apply List.ext_get
    · simp [blockAt]
    · intro i hi h'i
      simp only [blockAt, List.get_ofFn]
      apply ULogSourceOneHotWriter.exact_block_outside
      rcases hdisjoint with hleft | hright
      · left
        have hin : i < nt := by simpa [blockAt] using hi
        have hil : (i : Int) < nt := by exact_mod_cast hin
        omega
      · right
        omega
  rw [hcells]
  exact hrep

end PakFixedPolyomino.ULogSourceOneHotRepresentation
