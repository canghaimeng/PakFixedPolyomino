import PakFixedPolyomino.Wang
import PakFixedPolyomino.FloorReadout
import Mathlib.Tactic

namespace PakFixedPolyomino

noncomputable section

/-- A cell of the `n × n` macro grid. -/
abbrev MacroCell (n : ℕ) := Fin n × Fin n

/-- A nonempty axis-parallel rectangle contained in the `n × n` macro
grid.  Width and height are stored in `Fin (n+1)` so that the collection of
rectangles is manifestly finite. -/
@[ext] structure GridRectangle (n : ℕ) where
  x₀ : Fin n
  y₀ : Fin n
  width : Fin (n + 1)
  height : Fin (n + 1)
  width_pos : 0 < width.1
  height_pos : 0 < height.1
  x_bound : x₀.1 + width.1 ≤ n
  y_bound : y₀.1 + height.1 ≤ n
  deriving DecidableEq

instance (n : ℕ) : Fintype (GridRectangle n) := by
  let encode : GridRectangle n →
      Fin n × Fin n × Fin (n + 1) × Fin (n + 1) :=
    fun B => (B.x₀, B.y₀, B.width, B.height)
  apply Fintype.ofInjective encode
  intro B C h
  cases B
  cases C
  simp only [encode, Prod.mk.injEq] at h
  simp_all

def GridRectangle.Contains {n : ℕ} (B : GridRectangle n) (p : MacroCell n) : Prop :=
  B.x₀.1 ≤ p.1.1 ∧ p.1.1 < B.x₀.1 + B.width.1 ∧
  B.y₀.1 ≤ p.2.1 ∧ p.2.1 < B.y₀.1 + B.height.1

instance {n : ℕ} (B : GridRectangle n) (p : MacroCell n) :
    Decidable (B.Contains p) := by
  unfold GridRectangle.Contains
  infer_instance

/-- A literal rectangular partition.  `unique_block` simultaneously records
coverage and pairwise disjointness, so later decoding never chooses between
two overlapping physical blocks. -/
@[ext] structure RectangularPartition (n : ℕ) where
  blocks : Finset (GridRectangle n)
  unique_block : ∀ p : MacroCell n, ∃! B : GridRectangle n,
    B ∈ blocks ∧ B.Contains p

instance (n : ℕ) : Fintype (RectangularPartition n) := by
  apply Fintype.ofInjective RectangularPartition.blocks
  intro D E h
  cases D
  cases E
  simp_all
instance (n : ℕ) : DecidableEq (RectangularPartition n) := Classical.decEq _

/-- The distinguished one-block partition of a positive square. -/
def wholeRectangle (n : ℕ) (hn : 0 < n) : GridRectangle n where
  x₀ := ⟨0, hn⟩
  y₀ := ⟨0, hn⟩
  width := ⟨n, Nat.lt_succ_self n⟩
  height := ⟨n, Nat.lt_succ_self n⟩
  width_pos := hn
  height_pos := hn
  x_bound := by simp
  y_bound := by simp

@[simp] theorem wholeRectangle_contains (n : ℕ) (hn : 0 < n)
    (p : MacroCell n) : (wholeRectangle n hn).Contains p := by
  unfold wholeRectangle GridRectangle.Contains
  simp

def wholePartition (n : ℕ) (hn : 0 < n) : RectangularPartition n where
  blocks := {wholeRectangle n hn}
  unique_block p := by
    refine ⟨wholeRectangle n hn, ⟨by simp, wholeRectangle_contains n hn p⟩, ?_⟩
    intro B hB
    simpa using hB.1

@[simp] theorem wholePartition_blocks (n : ℕ) (hn : 0 < n) :
    (wholePartition n hn).blocks = {wholeRectangle n hn} := rfl

theorem gridRectangle_one_eq (B : GridRectangle 1) :
    B = wholeRectangle 1 (by decide) := by
  apply GridRectangle.ext <;> apply Fin.ext <;> dsimp [wholeRectangle] <;>
    have hw := B.width_pos <;> have hh := B.height_pos <;> omega

theorem rectangularPartition_one_eq (D : RectangularPartition 1) :
    D = wholePartition 1 (by decide) := by
  apply RectangularPartition.ext
  ext B
  constructor
  · intro _
    simp [gridRectangle_one_eq B]
  · intro hB
    have hBeq : B = wholeRectangle 1 (by decide) := by simpa using hB
    rw [hBeq]
    obtain ⟨C, ⟨hC, -⟩, -⟩ := D.unique_block (⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩)
    simpa [gridRectangle_one_eq C] using hC

/-- Horizontal or vertical unit edges in the macro grid. -/
abbrev MacroEdge (n : ℕ) :=
  (Fin (n - 1) × Fin n) ⊕ (Fin n × Fin (n - 1))

def MacroEdge.lo {n : ℕ} : MacroEdge n → MacroCell n
  | .inl e => (⟨e.1.1, lt_of_lt_of_le e.1.2 (Nat.sub_le n 1)⟩, e.2)
  | .inr e => (e.1, ⟨e.2.1, lt_of_lt_of_le e.2.2 (Nat.sub_le n 1)⟩)

def MacroEdge.hi {n : ℕ} : MacroEdge n → MacroCell n
  | .inl e => (⟨e.1.1 + 1, by omega⟩, e.2)
  | .inr e => (e.1, ⟨e.2.1 + 1, by omega⟩)

@[simp] theorem card_macroEdge (n : ℕ) :
    Fintype.card (MacroEdge n) = 2 * n * (n - 1) := by
  simp [MacroEdge]
  ring

def RectangularPartition.SameBlock {n : ℕ} (D : RectangularPartition n)
    (p q : MacroCell n) : Prop :=
  ∃ B ∈ D.blocks, B.Contains p ∧ B.Contains q

instance {n : ℕ} (D : RectangularPartition n) (p q : MacroCell n) :
    Decidable (D.SameBlock p q) := by
  unfold RectangularPartition.SameBlock
  infer_instance

@[simp] theorem wholePartition_sameBlock (n : ℕ) (hn : 0 < n)
    (p q : MacroCell n) : (wholePartition n hn).SameBlock p q := by
  exact ⟨wholeRectangle n hn, by simp,
    wholeRectangle_contains n hn p, wholeRectangle_contains n hn q⟩

theorem RectangularPartition.sameBlock_refl {n : ℕ}
    (D : RectangularPartition n) (p : MacroCell n) : D.SameBlock p p := by
  obtain ⟨B, ⟨hB, hp⟩, -⟩ := D.unique_block p
  exact ⟨B, hB, hp, hp⟩

theorem RectangularPartition.sameBlock_symm {n : ℕ}
    (D : RectangularPartition n) {p q : MacroCell n} :
    D.SameBlock p q → D.SameBlock q p := by
  rintro ⟨B, hB, hp, hq⟩
  exact ⟨B, hB, hq, hp⟩

theorem RectangularPartition.sameBlock_trans {n : ℕ}
    (D : RectangularPartition n) {p q r : MacroCell n} :
    D.SameBlock p q → D.SameBlock q r → D.SameBlock p r := by
  rintro ⟨B, hB, hp, hq⟩ ⟨C, hC, hqC, hr⟩
  have hBC : B = C := (D.unique_block q).unique ⟨hB, hq⟩ ⟨hC, hqC⟩
  subst C
  exact ⟨B, hB, hp, hr⟩

/-- The four corners of a unit square of the macro grid. -/
def macroSW {n : ℕ} (i j : Fin (n - 1)) : MacroCell n :=
  (⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩,
   ⟨j.1, lt_of_lt_of_le j.2 (Nat.sub_le n 1)⟩)

def macroSE {n : ℕ} (i j : Fin (n - 1)) : MacroCell n :=
  (⟨i.1 + 1, by omega⟩, ⟨j.1, lt_of_lt_of_le j.2 (Nat.sub_le n 1)⟩)

def macroNW {n : ℕ} (i j : Fin (n - 1)) : MacroCell n :=
  (⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩, ⟨j.1 + 1, by omega⟩)

def macroNE {n : ℕ} (i j : Fin (n - 1)) : MacroCell n :=
  (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)

private theorem rectangle_fourth_corner {n : ℕ} (B : GridRectangle n)
    (i j : Fin (n - 1))
    (hSW : B.Contains (macroSW i j))
    (hSE : B.Contains (macroSE i j))
    (hNW : B.Contains (macroNW i j)) :
    B.Contains (macroNE i j) := by
  unfold GridRectangle.Contains macroSW macroSE macroNW macroNE at *
  simp only at *
  omega

private theorem rectangle_other_corner {n : ℕ} (B : GridRectangle n)
    (i j : Fin (n - 1))
    (hSW : B.Contains (macroSW i j))
    (hSE : B.Contains (macroSE i j))
    (hNE : B.Contains (macroNE i j)) :
    B.Contains (macroNW i j) := by
  unfold GridRectangle.Contains macroSW macroSE macroNE macroNW at *
  simp only at *
  omega

private theorem rectangle_lower_corner {n : ℕ} (B : GridRectangle n)
    (i j : Fin (n - 1))
    (hSW : B.Contains (macroSW i j))
    (hNW : B.Contains (macroNW i j))
    (hNE : B.Contains (macroNE i j)) :
    B.Contains (macroSE i j) := by
  unfold GridRectangle.Contains macroSW macroNW macroNE macroSE at *
  simp only at *
  omega

private theorem rectangle_southwest_corner {n : ℕ} (B : GridRectangle n)
    (i j : Fin (n - 1))
    (hSE : B.Contains (macroSE i j))
    (hNW : B.Contains (macroNW i j))
    (_hNE : B.Contains (macroNE i j)) :
    B.Contains (macroSW i j) := by
  unfold GridRectangle.Contains macroSE macroNW macroNE macroSW at *
  simp only at *
  omega

/-- Rectangular partitions satisfy the local SAT rule: any two consecutive
open sides of a unit macro-square force all four sides open.  The four
conjuncts list the possible consecutive pairs. -/
theorem RectangularPartition.square_saturated {n : ℕ}
    (D : RectangularPartition n) (i j : Fin (n - 1)) :
    ((D.SameBlock (macroSW i j) (macroSE i j) ∧
        D.SameBlock (macroSE i j) (macroNE i j)) →
      D.SameBlock (macroSW i j) (macroNW i j) ∧
        D.SameBlock (macroNW i j) (macroNE i j)) ∧
    ((D.SameBlock (macroSE i j) (macroNE i j) ∧
        D.SameBlock (macroNE i j) (macroNW i j)) →
      D.SameBlock (macroSE i j) (macroSW i j) ∧
        D.SameBlock (macroSW i j) (macroNW i j)) ∧
    ((D.SameBlock (macroNE i j) (macroNW i j) ∧
        D.SameBlock (macroNW i j) (macroSW i j)) →
      D.SameBlock (macroNE i j) (macroSE i j) ∧
        D.SameBlock (macroSE i j) (macroSW i j)) ∧
    ((D.SameBlock (macroNW i j) (macroSW i j) ∧
        D.SameBlock (macroSW i j) (macroSE i j)) →
      D.SameBlock (macroNW i j) (macroNE i j) ∧
        D.SameBlock (macroNE i j) (macroSE i j)) := by
  constructor
  · rintro ⟨⟨B, hB, hSW, hSE⟩, ⟨C, hC, hSEC, hNE⟩⟩
    have hBC : B = C := (D.unique_block (macroSE i j)).unique ⟨hB, hSE⟩ ⟨hC, hSEC⟩
    subst C
    have hNW := rectangle_other_corner B i j hSW hSE hNE
    exact ⟨⟨B, hB, hSW, hNW⟩, ⟨B, hB, hNW, hNE⟩⟩
  · constructor
    · rintro ⟨⟨B, hB, hSE, hNE⟩, ⟨C, hC, hNEC, hNW⟩⟩
      have hBC : B = C := (D.unique_block (macroNE i j)).unique ⟨hB, hNE⟩ ⟨hC, hNEC⟩
      subst C
      have hSW := rectangle_southwest_corner B i j hSE hNW hNE
      exact ⟨⟨B, hB, hSE, hSW⟩, ⟨B, hB, hSW, hNW⟩⟩
    · constructor
      · rintro ⟨⟨B, hB, hNE, hNW⟩, ⟨C, hC, hNWC, hSW⟩⟩
        have hBC : B = C := (D.unique_block (macroNW i j)).unique ⟨hB, hNW⟩ ⟨hC, hNWC⟩
        subst C
        have hSE := rectangle_lower_corner B i j hSW hNW hNE
        exact ⟨⟨B, hB, hNE, hSE⟩, ⟨B, hB, hSE, hSW⟩⟩
      · rintro ⟨⟨B, hB, hNW, hSW⟩, ⟨C, hC, hSWC, hSE⟩⟩
        have hBC : B = C := (D.unique_block (macroSW i j)).unique ⟨hB, hSW⟩ ⟨hC, hSWC⟩
        subst C
        have hNE := rectangle_fourth_corner B i j hSW hSE hNW
        exact ⟨⟨B, hB, hNW, hNE⟩, ⟨B, hB, hNE, hSE⟩⟩

def RectangularPartition.IsOpen {n : ℕ} (D : RectangularPartition n)
    (e : MacroEdge n) : Prop := D.SameBlock e.lo e.hi

instance {n : ℕ} (D : RectangularPartition n) (e : MacroEdge n) :
    Decidable (D.IsOpen e) := by
  unfold RectangularPartition.IsOpen
  infer_instance

/-- The physical open macro-edges of a rectangular partition. -/
abbrev OpenMacroEdge {n : ℕ} (D : RectangularPartition n) :=
  {e : MacroEdge n // D.IsOpen e}

def RectangularPartition.openEdgeCount {n : ℕ} (D : RectangularPartition n) : ℕ :=
  Fintype.card (OpenMacroEdge D)

def RectangularPartition.seamCount {n : ℕ} (D : RectangularPartition n) : ℕ :=
  Fintype.card (MacroEdge n) - D.openEdgeCount

theorem RectangularPartition.openEdgeCount_le {n : ℕ}
    (D : RectangularPartition n) :
    D.openEdgeCount ≤ Fintype.card (MacroEdge n) :=
  Fintype.card_subtype_le _

theorem RectangularPartition.openEdgeCount_eq_grid_sub_seams {n : ℕ}
    (D : RectangularPartition n) :
    D.openEdgeCount = amplifierExponent n - D.seamCount := by
  rw [amplifierExponent]
  rw [← card_macroEdge]
  exact (Nat.sub_sub_self D.openEdgeCount_le).symm

@[simp] theorem wholePartition_seamCount (n : ℕ) (hn : 0 < n) :
    (wholePartition n hn).seamCount = 0 := by
  have hcard : Fintype.card (OpenMacroEdge (wholePartition n hn)) =
      Fintype.card (MacroEdge n) := by
    let e : OpenMacroEdge (wholePartition n hn) ≃ MacroEdge n :=
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, wholePartition_sameBlock n hn x.lo x.hi⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  unfold RectangularPartition.seamCount RectangularPartition.openEdgeCount
  rw [hcard]
  simp

/-- Wang decorations on every block of a rectangular partition. -/
abbrev BlockWangData {n : ℕ} (D : RectangularPartition n)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) :=
  (B : ↑D.blocks) → OpenWangTiling tile B.1.width.1 B.1.height.1

/-- The full data read from an anchored geometric tiling: one open Wang
tiling per rectangular block and one independent amplifier label on every
open macro-edge. -/
abbrev MacroDecoration {n : ℕ} (D : RectangularPartition n)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ) :=
  ((e : OpenMacroEdge D) → Fin amp) × BlockWangData D tile

abbrev MacroData (n : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ) :=
  Σ D : RectangularPartition n, MacroDecoration D tile amp

def macroBlockCount {n : ℕ} {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (D : RectangularPartition n) : ℕ :=
  ∏ B : ↑D.blocks, openWangCount tile B.1.width.1 B.1.height.1

@[simp] theorem macroBlockCount_whole (n : ℕ) (hn : 0 < n)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) :
    macroBlockCount tile (wholePartition n hn) = openWangCount tile n n := by
  classical
  let B₀ : ↑(wholePartition n hn).blocks :=
    ⟨wholeRectangle n hn, by simp⟩
  have huniv : (Finset.univ : Finset ↑(wholePartition n hn).blocks) = {B₀} := by
    ext B
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    simpa [B₀] using B.property
  unfold macroBlockCount
  rw [huniv]
  rw [Finset.prod_singleton]
  rfl

def macroWeight {n : ℕ} {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (D : RectangularPartition n) : ℕ :=
  amp ^ D.openEdgeCount * macroBlockCount tile D

@[simp] theorem card_macroDecoration {n : ℕ} {W H V : Type*}
    [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ) (D : RectangularPartition n) :
    Fintype.card (MacroDecoration D tile amp) = macroWeight tile amp D := by
  classical
  simp [MacroDecoration, macroWeight, macroBlockCount, openWangCount,
    RectangularPartition.openEdgeCount,
    Fintype.card_prod, Fintype.card_pi]

@[simp] theorem card_macroData (n : ℕ) {W H V : Type*}
    [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ) :
    Fintype.card (MacroData n tile amp) =
      ∑ D : RectangularPartition n, macroWeight tile amp D := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro D _
  exact card_macroDecoration tile amp D

/-- A relation-level anchoring certificate.  This is the precise assumption
the unfinished geometric anchoring theorem must eventually produce: every
geometric tiling has exactly one macro readout, and every macro readout has
exactly one geometric realization.  It remains an explicit theorem parameter. -/
structure LatticeAnchored (Tilings Data : Type*) where
  realizes : Tilings → Data → Prop
  unique_readout : ∀ T, ∃! d, realizes T d
  unique_realization : ∀ d, ∃! T, realizes T d

/-- Package explicit forward and reverse geometric constructions into the
relation-level certificate consumed below. -/
def LatticeAnchored.ofMutualInverse {Tilings Data : Type*}
    (readout : Tilings → Data) (realization : Data → Tilings)
    (hleft : Function.LeftInverse realization readout)
    (hright : Function.RightInverse realization readout) :
    LatticeAnchored Tilings Data where
  realizes T d := readout T = d
  unique_readout T := by
    refine ⟨readout T, rfl, ?_⟩
    intro d hd
    exact hd.symm
  unique_realization d := by
    refine ⟨realization d, hright d, ?_⟩
    intro T hT
    calc
      T = realization (readout T) := (hleft T).symm
      _ = realization d := congrArg realization hT

def LatticeAnchored.ofEquiv {Tilings Data : Type*} (e : Tilings ≃ Data) :
    LatticeAnchored Tilings Data :=
  .ofMutualInverse e e.symm e.left_inv e.right_inv

def LatticeAnchored.readout {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (T : Tilings) : Data :=
  Classical.choose (h.unique_readout T)

def LatticeAnchored.realization {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (d : Data) : Tilings :=
  Classical.choose (h.unique_realization d)

theorem LatticeAnchored.readout_realizes {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (T : Tilings) :
    h.realizes T (h.readout T) :=
  Classical.choose_spec (h.unique_readout T) |>.1

theorem LatticeAnchored.realization_realizes {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (d : Data) :
    h.realizes (h.realization d) d :=
  Classical.choose_spec (h.unique_realization d) |>.1

theorem LatticeAnchored.readout_realization {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (d : Data) :
    h.readout (h.realization d) = d := by
  exact (h.unique_readout (h.realization d)).unique
    (h.readout_realizes (h.realization d)) (h.realization_realizes d)

theorem LatticeAnchored.realization_readout {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) (T : Tilings) :
    h.realization (h.readout T) = T := by
  exact (h.unique_realization (h.readout T)).unique
    (h.realization_realizes (h.readout T)) (h.readout_realizes T)

/-- The forward and reverse geometric constructions are mutually inverse as
soon as the future anchoring theorem supplies the occurrence-level uniqueness
certificate.  It is supplied transparently as a theorem parameter. -/
def LatticeAnchored.equiv {Tilings Data : Type*}
    (h : LatticeAnchored Tilings Data) : Tilings ≃ Data where
  toFun := h.readout
  invFun := h.realization
  left_inv := h.realization_readout
  right_inv := h.readout_realization

/-- Exact partition count below the anchoring seam. -/
theorem exact_macro_partition_count {Tilings : Type*} [Fintype Tilings]
    (n : ℕ) {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ)
    (h : LatticeAnchored Tilings (MacroData n tile amp)) :
    Fintype.card Tilings =
      ∑ D : RectangularPartition n, macroWeight tile amp D := by
  rw [Fintype.card_congr h.equiv, card_macroData]

/-- The same count in the exponent form used by the identity register. -/
theorem exact_macro_partition_count_register_form
    {Tilings : Type*} [Fintype Tilings]
    (n : ℕ) {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (amp : ℕ)
    (h : LatticeAnchored Tilings (MacroData n tile amp)) :
    Fintype.card Tilings =
      ∑ D : RectangularPartition n,
        amp ^ (amplifierExponent n - D.seamCount) * macroBlockCount tile D := by
  rw [exact_macro_partition_count n tile amp h]
  apply Finset.sum_congr rfl
  intro D _
  simp only [macroWeight]
  rw [D.openEdgeCount_eq_grid_sub_seams]

end
end PakFixedPolyomino
