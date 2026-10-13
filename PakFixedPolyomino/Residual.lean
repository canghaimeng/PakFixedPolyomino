import PakFixedPolyomino.Connectivity

namespace PakFixedPolyomino

noncomputable section

def macroOrigin (P : RegisterParams) (i j : ℕ) : Cell :=
  ((i * P.pitch : ℕ), (j * P.pitch : ℕ))

def macroCavityOrigin (P : RegisterParams) (i j : ℕ) (u : Fin P.tileCount) : Cell :=
  (((i * P.pitch + 16 + 4 * (u : ℕ) : ℕ) : ℤ),
   ((j * P.pitch + 16 : ℕ) : ℤ))

def macroCavity (P : RegisterParams) (i j : ℕ) (u : Fin P.tileCount) : Polyomino :=
  cavity (macroCavityOrigin P i j u)

@[simp] theorem card_macroCavity (P : RegisterParams) (i j : ℕ)
    (u : Fin P.tileCount) : (macroCavity P i j u).card = 3 := by
  simp [macroCavity]

theorem macroCavity_fourConnected (P : RegisterParams) (i j : ℕ)
    (u : Fin P.tileCount) : FourConnected (macroCavity P i j u) := by
  exact cavity_fourConnected _

theorem macroCavity_bounds {P : RegisterParams} {i j : ℕ}
    {u : Fin P.tileCount} {z : Cell} (hz : z ∈ macroCavity P i j u) :
    (i * P.pitch + 16 : ℕ) ≤ z.1 ∧
    z.1 ≤ (i * P.pitch + 17 + 4 * (u : ℕ) : ℕ) ∧
    (z.2 = (j * P.pitch + 16 : ℕ) ∨ z.2 = (j * P.pitch + 17 : ℕ)) := by
  rw [macroCavity, cavity] at hz
  simp only [translate, Finset.mem_image] at hz
  rcases hz with ⟨p, hp, rfl⟩
  simp only [mem_plugL] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num [macroCavityOrigin] <;> omega

theorem macroCavities_disjoint_of_col_lt
    (P : RegisterParams) {i i' j j' : ℕ} (hii : i < i')
    (u v : Fin P.tileCount) :
    Disjoint (macroCavity P i j u) (macroCavity P i' j' v) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have h := macroCavity_bounds hz
  have h' := macroCavity_bounds hz'
  have hu := u.isLt
  have hm := P.pitch_ge_tile_margin
  have hlocal : 17 + 4 * (u : ℕ) < P.pitch := by omega
  have hiEnd : i * P.pitch + 17 + 4 * (u : ℕ) < (i + 1) * P.pitch := by
    rw [Nat.add_mul]
    omega
  have hstep : (i + 1) * P.pitch ≤ i' * P.pitch :=
    Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr hii)
  have hiEndZ : ((i * P.pitch + 17 + 4 * (u : ℕ) : ℕ) : ℤ) <
      (((i + 1) * P.pitch : ℕ) : ℤ) := by exact_mod_cast hiEnd
  have hstepZ : (((i + 1) * P.pitch : ℕ) : ℤ) ≤
      ((i' * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep
  omega

theorem macroCavities_disjoint_of_row_lt
    (P : RegisterParams) {i i' j j' : ℕ} (hjj : j < j')
    (u v : Fin P.tileCount) :
    Disjoint (macroCavity P i j u) (macroCavity P i' j' v) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have h := macroCavity_bounds hz
  have h' := macroCavity_bounds hz'
  rcases h.2.2 with hy | hy <;> rcases h'.2.2 with hy' | hy'
  all_goals
    have hp := P.pitch_ge_sixty_eight
    have hjEnd : j * P.pitch + 17 < (j + 1) * P.pitch := by
      rw [Nat.add_mul]
      omega
    have hjEndZ : ((j * P.pitch + 17 : ℕ) : ℤ) <
        (((j + 1) * P.pitch : ℕ) : ℤ) := by exact_mod_cast hjEnd
    have hstep : (j + 1) * P.pitch ≤ j' * P.pitch :=
      Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr hjj)
    have hstepZ : (((j + 1) * P.pitch : ℕ) : ℤ) ≤
        ((j' * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep
    omega

theorem macroCavities_pairwise_disjoint
    (P : RegisterParams) {i i' j j' : ℕ} (hne : (i, j) ≠ (i', j'))
    (u v : Fin P.tileCount) :
    Disjoint (macroCavity P i j u) (macroCavity P i' j' v) := by
  rcases lt_trichotomy i i' with h | h | h
  · exact macroCavities_disjoint_of_col_lt P h u v
  · subst i'
    rcases lt_trichotomy j j' with h | h | h
    · exact macroCavities_disjoint_of_row_lt P h u v
    · exact (hne (by simp [h])).elim
    · exact (macroCavities_disjoint_of_row_lt P h v u).symm
  · exact (macroCavities_disjoint_of_col_lt P h v u).symm

/-- A cavity determines the unique translation of the common PlugL. -/
theorem plug_translation_unique
    (P : RegisterParams) (i j : ℕ) (u : Fin P.tileCount) {t : Cell}
    (h : translate plugL t = macroCavity P i j u) :
    t = macroCavityOrigin P i j u := by
  apply cavity_injective
  simpa [cavity, macroCavity] using h

theorem carrier_disjoint_tileCavity
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) :
    Disjoint (carrier P η u l) (tileCavity u) := by
  rw [Finset.disjoint_left]
  intro z hz hzc
  rcases Finset.mem_union.mp hz with hb | hbump
  · exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_union.mpr (Or.inr hzc))
  · exact Finset.disjoint_left.mp (bumps_disjoint_body P η u l) hbump
      (tileCavity_subset_body P u hzc)

theorem macroCavity_subset_square
    (P : RegisterParams) {n : ℕ} (i j : Fin n) (u : Fin P.tileCount) :
    macroCavity P i.1 j.1 u ⊆ square (P.pitch * n) := by
  intro z hz
  have hm := P.pitch_ge_tile_margin
  have hu := u.isLt
  rw [macroCavity, cavity, translate] at hz
  rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
  simp only [mem_plugL] at hq
  rcases hq with rfl | rfl | rfl <;>
    apply ofNat_pair_mem_square.mpr <;>
    constructor <;>
    simp only [macroCavityOrigin] <;>
    have hi := i.isLt <;> have hj := j.isLt <;>
    push_cast <;> nlinarith

/-- If an explicitly listed cavity family is the residual region, then its
cardinality is exactly three times the number of macro-cells. -/
theorem card_residual_cavities {α : Type*} [DecidableEq α]
    (S : Finset α) (C : α → Polyomino)
    (hcard : ∀ a ∈ S, (C a).card = 3)
    (hdis : Set.Pairwise (↑S : Set α) fun a b => Disjoint (C a) (C b)) :
    (S.biUnion C).card = 3 * S.card := by
  rw [Finset.card_biUnion]
  · calc
      ∑ a ∈ S, (C a).card = ∑ _a ∈ S, 3 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hcard a ha
      _ = 3 * S.card := by simp; omega
  · intro a ha b hb hab
    exact hdis ha hb hab

end
end PakFixedPolyomino
