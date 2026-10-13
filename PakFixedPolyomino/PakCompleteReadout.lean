import PakFixedPolyomino.RectangularDissectionCensus
import PakFixedPolyomino.WProdRegisterConcrete
import PakFixedPolyomino.UnconditionalReadout
import Mathlib.Tactic

/-!
# Complete physical floor readout

This is the final narrow assembly module for the geometric/counting part of
the Pak construction.  Besides composing the independently checked census
and Wang rectangle bound, it supplies the literal block-side double count
needed for the perimeter identity of a rectangular partition.
-/

namespace PakFixedPolyomino

noncomputable section

/-- Two vertical sides and two horizontal sides for every literal block. -/
abbrev BlockSideIncidence {n : ℕ} (D : RectangularPartition n) :=
  Σ B : ↑D.blocks,
    (Bool × Fin B.1.height.1) ⊕ (Bool × Fin B.1.width.1)

/-- Four outer sides, plus the two block incidences of every seam. -/
abbrev SideTarget {n : ℕ} (D : RectangularPartition n) :=
  (Fin 4 × Fin n) ⊕ (Bool × ↑D.seamEdges)

private theorem seam_of_separated_block {n : ℕ}
    (D : RectangularPartition n) (B : ↑D.blocks) (e : MacroEdge n)
    (hsep : (B.1.Contains e.lo ∧ ¬ B.1.Contains e.hi) ∨
      (B.1.Contains e.hi ∧ ¬ B.1.Contains e.lo)) :
    e ∈ D.seamEdges := by
  rw [RectangularPartition.mem_seamEdges]
  intro hopen
  rcases hopen with ⟨C, hC, hlo, hhi⟩
  rcases hsep with ⟨hBlo, hBnhi⟩ | ⟨hBhi, hBnlo⟩
  · have hBC := (D.unique_block e.lo).unique ⟨B.2, hBlo⟩ ⟨hC, hlo⟩
    subst C
    exact hBnhi hhi
  · have hBC := (D.unique_block e.hi).unique ⟨B.2, hBhi⟩ ⟨hC, hhi⟩
    subst C
    exact hBnlo hlo

def blockSideTarget {n : ℕ} (hn : 0 < n) (D : RectangularPartition n) :
    BlockSideIncidence D → SideTarget D
  | ⟨B, .inl (false, k)⟩ =>
      if hx : B.1.x₀.1 = 0 then
        .inl (0, ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      else
        let e : MacroEdge n := .inl
          (⟨B.1.x₀.1 - 1, by omega⟩,
           ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
        .inr (false, ⟨e, by
          apply seam_of_separated_block D B
          right
          constructor
          · unfold GridRectangle.Contains e MacroEdge.hi
            simp only [Prod.fst, Prod.snd]
            have := B.1.width_pos
            omega
          · unfold GridRectangle.Contains e MacroEdge.lo
            simp only [Prod.fst, Prod.snd]
            omega⟩)
  | ⟨B, .inl (true, k)⟩ =>
      if hx : B.1.x₀.1 + B.1.width.1 = n then
        .inl (1, ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      else
        let e : MacroEdge n := .inl
          (⟨B.1.x₀.1 + B.1.width.1 - 1, by
              have := B.1.x_bound; have := B.1.width_pos; omega⟩,
           ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
        .inr (true, ⟨e, by
          apply seam_of_separated_block D B
          left
          constructor
          · unfold GridRectangle.Contains e MacroEdge.lo
            simp only [Prod.fst, Prod.snd]
            have := B.1.width_pos
            omega
          · unfold GridRectangle.Contains e MacroEdge.hi
            simp only [Prod.fst, Prod.snd]
            omega⟩)

  | ⟨B, .inr (false, k)⟩ =>
      if hy : B.1.y₀.1 = 0 then
        .inl (2, ⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩)
      else
        let e : MacroEdge n := .inr
          (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩,
           ⟨B.1.y₀.1 - 1, by omega⟩)
        .inr (false, ⟨e, by
          apply seam_of_separated_block D B
          right
          constructor
          · unfold GridRectangle.Contains e MacroEdge.hi
            simp only [Prod.fst, Prod.snd]
            have := B.1.height_pos
            omega
          · unfold GridRectangle.Contains e MacroEdge.lo
            simp only [Prod.fst, Prod.snd]
            omega⟩)
  | ⟨B, .inr (true, k)⟩ =>
      if hy : B.1.y₀.1 + B.1.height.1 = n then
        .inl (3, ⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩)
      else
        let e : MacroEdge n := .inr
          (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩,
           ⟨B.1.y₀.1 + B.1.height.1 - 1, by
              have := B.1.y_bound; have := B.1.height_pos; omega⟩)
        .inr (true, ⟨e, by
          apply seam_of_separated_block D B
          left
          constructor
          · unfold GridRectangle.Contains e MacroEdge.lo
            simp only [Prod.fst, Prod.snd]
            have := B.1.height_pos
            omega
          · unfold GridRectangle.Contains e MacroEdge.hi
            simp only [Prod.fst, Prod.snd]
            omega⟩)

def sideTargetBlockSide {n : ℕ} (hn : 0 < n) (D : RectangularPartition n) :
    SideTarget D → BlockSideIncidence D
  | .inl (⟨0, _⟩, k) =>
      let p : MacroCell n := (⟨0, hn⟩, k)
      ⟨D.blockAt p, .inl (false, D.localY p)⟩
  | .inl (⟨1, _⟩, k) =>
      let p : MacroCell n := (⟨n - 1, by omega⟩, k)
      ⟨D.blockAt p, .inl (true, D.localY p)⟩
  | .inl (⟨2, _⟩, k) =>
      let p : MacroCell n := (k, ⟨0, hn⟩)
      ⟨D.blockAt p, .inr (false, D.localX p)⟩
  | .inl (⟨3, _⟩, k) =>
      let p : MacroCell n := (k, ⟨n - 1, by omega⟩)
      ⟨D.blockAt p, .inr (true, D.localX p)⟩
  | .inr (false, ⟨.inl e, _⟩) =>
      let p := MacroEdge.hi (Sum.inl e : MacroEdge n)
      ⟨D.blockAt p, .inl (false, D.localY p)⟩
  | .inr (true, ⟨.inl e, _⟩) =>
      let p := MacroEdge.lo (Sum.inl e : MacroEdge n)
      ⟨D.blockAt p, .inl (true, D.localY p)⟩
  | .inr (false, ⟨.inr e, _⟩) =>
      let p := MacroEdge.hi (Sum.inr e : MacroEdge n)
      ⟨D.blockAt p, .inr (false, D.localX p)⟩
  | .inr (true, ⟨.inr e, _⟩) =>
      let p := MacroEdge.lo (Sum.inr e : MacroEdge n)
      ⟨D.blockAt p, .inr (true, D.localX p)⟩

private theorem localY_heq_of_blockAt_eq {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) (B : ↑D.blocks) (hB : D.blockAt p = B)
    (k : Fin B.1.height.1) (hcoord : p.2.1 = B.1.y₀.1 + k.1) :
    D.localY p ≍ k := by
  subst B
  apply (heq_iff_eq).2
  apply Fin.ext
  dsimp [RectangularPartition.localY]
  omega

private theorem localX_heq_of_blockAt_eq {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) (B : ↑D.blocks) (hB : D.blockAt p = B)
    (k : Fin B.1.width.1) (hcoord : p.1.1 = B.1.x₀.1 + k.1) :
    D.localX p ≍ k := by
  subst B
  apply (heq_iff_eq).2
  apply Fin.ext
  dsimp [RectangularPartition.localX]
  omega

private theorem blockSide_inl_heq {n : ℕ} {D : RectangularPartition n}
    {C B : ↑D.blocks} (hCB : C = B) (b : Bool)
    {a : Fin C.1.height.1} {k : Fin B.1.height.1} (hak : a ≍ k) :
    (Sum.inl (b, a) : (Bool × Fin C.1.height.1) ⊕
      (Bool × Fin C.1.width.1)) ≍
    (Sum.inl (b, k) : (Bool × Fin B.1.height.1) ⊕
      (Bool × Fin B.1.width.1)) := by
  subst B
  exact (heq_iff_eq).2 (congrArg (fun z => Sum.inl (b, z)) (heq_iff_eq.mp hak))

private theorem blockSide_inr_heq {n : ℕ} {D : RectangularPartition n}
    {C B : ↑D.blocks} (hCB : C = B) (b : Bool)
    {a : Fin C.1.width.1} {k : Fin B.1.width.1} (hak : a ≍ k) :
    (Sum.inr (b, a) : (Bool × Fin C.1.height.1) ⊕
      (Bool × Fin C.1.width.1)) ≍
    (Sum.inr (b, k) : (Bool × Fin B.1.height.1) ⊕
      (Bool × Fin B.1.width.1)) := by
  subst B
  exact (heq_iff_eq).2 (congrArg (fun z => Sum.inr (b, z)) (heq_iff_eq.mp hak))

theorem blockSideTarget_left_inv {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (x : BlockSideIncidence D) :
    sideTargetBlockSide hn D (blockSideTarget hn D x) = x := by
  rcases x with ⟨B, x⟩
  rcases x with ⟨b, k⟩ | ⟨b, k⟩ <;> cases b
  · by_cases hx : B.1.x₀.1 = 0
    · simp [blockSideTarget, hx, sideTargetBlockSide]
      let p : MacroCell n := (⟨0, hn⟩,
        ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.width_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inl_heq hB false
          (localY_heq_of_blockAt_eq D p B hB k (by rfl))
    · simp [blockSideTarget, hx, sideTargetBlockSide]
      let e : MacroEdge n := .inl
        (⟨B.1.x₀.1 - 1, by omega⟩,
         ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      let p : MacroCell n := MacroEdge.hi e
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        dsimp [e, MacroEdge.hi]
        have := B.1.width_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inl_heq hB false
          (localY_heq_of_blockAt_eq D p B hB k (by rfl))
  · by_cases hx : B.1.x₀.1 + B.1.width.1 = n
    · simp [blockSideTarget, hx, sideTargetBlockSide]
      let p : MacroCell n := (⟨n - 1, by omega⟩,
        ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.width_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inl_heq hB true
          (localY_heq_of_blockAt_eq D p B hB k (by rfl))
    · simp [blockSideTarget, hx, sideTargetBlockSide]
      let p : MacroCell n :=
        (⟨B.1.x₀.1 + B.1.width.1 - 1, by
          have hxB := B.1.x_bound
          have hw := B.1.width_pos
          omega⟩,
         ⟨B.1.y₀.1 + k.1, by have := B.1.y_bound; omega⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.width_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inl_heq hB true
          (localY_heq_of_blockAt_eq D p B hB k (by rfl))
  · by_cases hy : B.1.y₀.1 = 0
    · simp [blockSideTarget, hy, sideTargetBlockSide]
      let p : MacroCell n :=
        (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩, ⟨0, hn⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.height_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inr_heq hB false
          (localX_heq_of_blockAt_eq D p B hB k (by rfl))
    · simp [blockSideTarget, hy, sideTargetBlockSide]
      let e : MacroEdge n := .inr
        (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩,
         ⟨B.1.y₀.1 - 1, by omega⟩)
      let p : MacroCell n := MacroEdge.hi e
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        dsimp [e, MacroEdge.hi]
        have := B.1.height_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inr_heq hB false
          (localX_heq_of_blockAt_eq D p B hB k (by rfl))
  · by_cases hy : B.1.y₀.1 + B.1.height.1 = n
    · simp [blockSideTarget, hy, sideTargetBlockSide]
      let p : MacroCell n :=
        (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩,
         ⟨n - 1, by omega⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.height_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inr_heq hB true
          (localX_heq_of_blockAt_eq D p B hB k (by rfl))
    · simp [blockSideTarget, hy, sideTargetBlockSide]
      let p : MacroCell n :=
        (⟨B.1.x₀.1 + k.1, by have := B.1.x_bound; omega⟩,
         ⟨B.1.y₀.1 + B.1.height.1 - 1, by
           have hyB := B.1.y_bound
           have hh := B.1.height_pos
           omega⟩)
      have hp : B.1.Contains p := by
        unfold GridRectangle.Contains p
        simp only [Prod.fst, Prod.snd]
        have := B.1.height_pos
        omega
      have hB : D.blockAt p = B := D.blockAt_eq_of_contains p B hp
      constructor
      · change D.blockAt p = B
        exact hB
      · exact blockSide_inr_heq hB true
          (localX_heq_of_blockAt_eq D p B hB k (by rfl))

theorem blockSideTarget_right_inv {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) (y : SideTarget D) :
    blockSideTarget hn D (sideTargetBlockSide hn D y) = y := by
  rcases y with ⟨s, k⟩ | ⟨b, e, he⟩
  · fin_cases s
    · let p : MacroCell n := (⟨0, hn⟩, k)
      have hp := D.blockAt_contains p
      have hx : (D.blockAt p).1.x₀.1 = 0 := by
        dsimp [p]
        dsimp [p] at hp
        unfold GridRectangle.Contains at hp
        simp only [Prod.fst, Prod.snd, Fin.val_zero] at hp
        omega
      simp [sideTargetBlockSide, blockSideTarget, p, hx]
      apply Fin.ext
      dsimp [RectangularPartition.localY, p]
      dsimp [p] at hp
      unfold GridRectangle.Contains at hp
      simp only [Prod.fst, Prod.snd, Fin.val_zero] at hp ⊢
      omega
    · let p : MacroCell n := (⟨n - 1, by omega⟩, k)
      have hp := D.blockAt_contains p
      have hx : (D.blockAt p).1.x₀.1 + (D.blockAt p).1.width.1 = n := by
        dsimp [p]
        dsimp [p] at hp
        unfold GridRectangle.Contains at hp
        simp only [Prod.fst, Prod.snd] at hp
        have hb := (D.blockAt p).1.x_bound
        dsimp [p] at hb
        omega
      simp [sideTargetBlockSide, blockSideTarget, p, hx]
      apply Fin.ext
      dsimp [RectangularPartition.localY, p]
      dsimp [p] at hp
      unfold GridRectangle.Contains at hp
      simp only [Prod.fst, Prod.snd] at hp ⊢
      omega
    · let p : MacroCell n := (k, ⟨0, hn⟩)
      have hp := D.blockAt_contains p
      have hy : (D.blockAt p).1.y₀.1 = 0 := by
        dsimp [p]
        dsimp [p] at hp
        unfold GridRectangle.Contains at hp
        simp only [Prod.fst, Prod.snd, Fin.val_zero] at hp
        omega
      simp [sideTargetBlockSide, blockSideTarget, p, hy]
      apply Fin.ext
      dsimp [RectangularPartition.localX, p]
      dsimp [p] at hp
      unfold GridRectangle.Contains at hp
      simp only [Prod.fst, Prod.snd, Fin.val_zero] at hp ⊢
      omega
    · let p : MacroCell n := (k, ⟨n - 1, by omega⟩)
      have hp := D.blockAt_contains p
      have hy : (D.blockAt p).1.y₀.1 + (D.blockAt p).1.height.1 = n := by
        dsimp [p]
        dsimp [p] at hp
        unfold GridRectangle.Contains at hp
        simp only [Prod.fst, Prod.snd] at hp
        have hb := (D.blockAt p).1.y_bound
        dsimp [p] at hb
        omega
      simp [sideTargetBlockSide, blockSideTarget, p, hy]
      apply Fin.ext
      dsimp [RectangularPartition.localX, p]
      dsimp [p] at hp
      unfold GridRectangle.Contains at hp
      simp only [Prod.fst, Prod.snd] at hp ⊢
      omega
  · rcases e with e | e <;> cases b
    · let edge : MacroEdge n := .inl e
      let p : MacroCell n := MacroEdge.hi edge
      let B : ↑D.blocks := D.blockAt p
      have hhi : B.1.Contains p := D.blockAt_contains p
      have hnotopen : ¬ D.SameBlock edge.lo edge.hi := by
        change ¬ D.IsOpen edge
        simpa [edge] using he
      have hnlo : ¬ B.1.Contains edge.lo := by
        intro hlo
        exact hnotopen ⟨B.1, B.2, hlo, hhi⟩
      have hx : B.1.x₀.1 = e.1.1 + 1 := by
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [p, edge, MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega
      have hx0 : B.1.x₀.1 ≠ 0 := by omega
      dsimp [B, p, edge] at hx hhi hx0
      simp [sideTargetBlockSide, blockSideTarget, edge, p, B, hx0]
      apply Prod.ext <;> apply Fin.ext
      · simp only [Prod.fst]
        omega
      · dsimp [RectangularPartition.localY]
        unfold GridRectangle.Contains at hhi
        dsimp [MacroEdge.hi] at hhi ⊢
        omega
    · let edge : MacroEdge n := .inl e
      let p : MacroCell n := MacroEdge.lo edge
      let B : ↑D.blocks := D.blockAt p
      have hlo : B.1.Contains p := D.blockAt_contains p
      have hnotopen : ¬ D.SameBlock edge.lo edge.hi := by
        change ¬ D.IsOpen edge
        simpa [edge] using he
      have hnhi : ¬ B.1.Contains edge.hi := by
        intro hhi
        exact hnotopen ⟨B.1, B.2, hlo, hhi⟩
      have hx : B.1.x₀.1 + B.1.width.1 = e.1.1 + 1 := by
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [p, edge, MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
      have hxn : B.1.x₀.1 + B.1.width.1 ≠ n := by
        have := e.1.2
        omega
      dsimp [B, p, edge] at hx hlo hxn
      simp [sideTargetBlockSide, blockSideTarget, edge, p, B, hxn]
      apply Prod.ext <;> apply Fin.ext
      · simp only [Prod.fst]
        omega
      · dsimp [RectangularPartition.localY]
        unfold GridRectangle.Contains at hlo
        dsimp [MacroEdge.lo] at hlo ⊢
        omega
    · let edge : MacroEdge n := .inr e
      let p : MacroCell n := MacroEdge.hi edge
      let B : ↑D.blocks := D.blockAt p
      have hhi : B.1.Contains p := D.blockAt_contains p
      have hnotopen : ¬ D.SameBlock edge.lo edge.hi := by
        change ¬ D.IsOpen edge
        simpa [edge] using he
      have hnlo : ¬ B.1.Contains edge.lo := by
        intro hlo
        exact hnotopen ⟨B.1, B.2, hlo, hhi⟩
      have hy : B.1.y₀.1 = e.2.1 + 1 := by
        unfold GridRectangle.Contains at hhi hnlo
        dsimp [p, edge, MacroEdge.lo, MacroEdge.hi] at hhi hnlo
        omega
      have hy0 : B.1.y₀.1 ≠ 0 := by omega
      dsimp [B, p, edge] at hy hhi hy0
      simp [sideTargetBlockSide, blockSideTarget, edge, p, B, hy0]
      apply Prod.ext <;> apply Fin.ext
      · dsimp [RectangularPartition.localX]
        unfold GridRectangle.Contains at hhi
        dsimp [MacroEdge.hi] at hhi ⊢
        omega
      · simp only [Prod.snd]
        omega
    · let edge : MacroEdge n := .inr e
      let p : MacroCell n := MacroEdge.lo edge
      let B : ↑D.blocks := D.blockAt p
      have hlo : B.1.Contains p := D.blockAt_contains p
      have hnotopen : ¬ D.SameBlock edge.lo edge.hi := by
        change ¬ D.IsOpen edge
        simpa [edge] using he
      have hnhi : ¬ B.1.Contains edge.hi := by
        intro hhi
        exact hnotopen ⟨B.1, B.2, hlo, hhi⟩
      have hy : B.1.y₀.1 + B.1.height.1 = e.2.1 + 1 := by
        unfold GridRectangle.Contains at hlo hnhi
        dsimp [p, edge, MacroEdge.lo, MacroEdge.hi] at hlo hnhi
        omega
      have hyn : B.1.y₀.1 + B.1.height.1 ≠ n := by
        have := e.2.2
        omega
      dsimp [B, p, edge] at hy hlo hyn
      simp [sideTargetBlockSide, blockSideTarget, edge, p, B, hyn]
      apply Prod.ext <;> apply Fin.ext
      · dsimp [RectangularPartition.localX]
        unfold GridRectangle.Contains at hlo
        dsimp [MacroEdge.lo] at hlo ⊢
        omega
      · simp only [Prod.snd]
        omega

/-- Literal block-side incidences are exactly the outer unit sides together
with the two incidences of every internal seam. -/
def blockSideEquiv {n : ℕ} (hn : 0 < n) (D : RectangularPartition n) :
    BlockSideIncidence D ≃ SideTarget D where
  toFun := blockSideTarget hn D
  invFun := sideTargetBlockSide hn D
  left_inv := blockSideTarget_left_inv hn D
  right_inv := blockSideTarget_right_inv hn D

theorem blockSide_double_count {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) :
    2 * (∑ B : ↑D.blocks, (B.1.width.1 + B.1.height.1)) =
      4 * n + 2 * D.seamCount := by
  have hcard := Fintype.card_congr (blockSideEquiv hn D)
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_coe, D.card_seamEdges] at hcard
  calc
    2 * (∑ B : ↑D.blocks, (B.1.width.1 + B.1.height.1)) =
        ∑ B : ↑D.blocks, (2 * B.1.height.1 + 2 * B.1.width.1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          omega
    _ = 4 * n + 2 * D.seamCount := hcard

theorem rectangularPartition_perimeter {n : ℕ} (hn : 0 < n)
    (D : RectangularPartition n) :
    ∑ B : ↑D.blocks, (B.1.width.1 + B.1.height.1) =
      2 * n + D.seamCount := by
  apply perimeter_identity_of_double_count
  simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    blockSide_double_count hn D

/-- The accepted rectangular-dissection estimates with every field now
instantiated by literal finite objects. -/
def concreteRectangularDissectionFacts (n : ℕ) (hn : 0 < n) :
    RectangularDissectionFacts n (wholePartition n hn) :=
  rectangularDissectionFactsOfPerimeter n hn
    (fun D => rectangularPartition_perimeter hn D)

namespace ConcreteWProd

variable {State Tape Arrow ScanState : Type*}
variable [Fintype State] [Fintype Tape] [Fintype Arrow] [Fintype ScanState]
variable [DecidableEq State] [DecidableEq Tape] [DecidableEq Arrow]
variable [DecidableEq ScanState]

variable (M : TableauMachineData State Tape Arrow)
variable (Q : ℕ) [NeZero Q]

noncomputable local instance completeReadoutRegisterTileDecidableEq
    (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :
    DecidableEq (RegisterTile (registerParams M Q Coupled)) := Classical.decEq _

/-- Exact physical macro-count identity for the fully enumerated register. -/
theorem physicalExactMacroCount
    (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled]
    (n : ℕ) :
    Fintype.card
        (Tiling (registerTileSupport (registerParams M Q Coupled))
          (square ((registerParams M Q Coupled).pitch * n))) =
      ∑ D : RectangularPartition n,
        macroWeight (registerWangTile (registerParams M Q Coupled))
          (registerParams M Q Coupled).amp D :=
  physical_exact_macro_count (registerParams M Q Coupled) n

/-- Unconditional amplified floor readout for every positive nontrivial
square size.  The rectangular census and perimeter identity are no longer
premises. -/
theorem physicalFloorReadoutUnconditional
    (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled]
    {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card
        (Tiling (registerTileSupport (registerParams M Q Coupled))
          (square ((registerParams M Q Coupled).pitch * n))) /
          (registerParams M Q Coupled).amp ^ amplifierExponent n =
      openWangCount (registerWangTile (registerParams M Q Coupled)) n n := by
  exact physicalFloorReadout M Q Coupled hn
    (concreteRectangularDissectionFacts n (lt_of_lt_of_le (by decide) hn))

/-- The exponent-zero (`n = 1`) endpoint of the same concrete readout. -/
theorem physicalFloorReadoutOneUnconditional
    (Coupled : Tracks M Q ScanState → Prop) [DecidablePred Coupled] :
    Fintype.card
        (Tiling (registerTileSupport (registerParams M Q Coupled))
          (square ((registerParams M Q Coupled).pitch * 1))) /
          (registerParams M Q Coupled).amp ^ amplifierExponent 1 =
      openWangCount (registerWangTile (registerParams M Q Coupled)) 1 1 :=
  physical_floor_readout_one_unconditional (registerParams M Q Coupled)

end ConcreteWProd

end

end PakFixedPolyomino
