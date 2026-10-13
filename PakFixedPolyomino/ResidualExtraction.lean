import PakFixedPolyomino.GlobalExtractionAlt

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 2400000

local instance residualDecidableEqRegisterTile (P : RegisterParams) :
    DecidableEq (RegisterTile P) :=
  Classical.decEq _

def residualPlacements (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :=
  T.placements \ selectedCarrierPlacements P T

theorem residualPlacement_cells_subset_cavities
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {p : Placement (RegisterTile P)}
    (hp : p ∈ residualPlacements P T) :
    Placement.cells (registerTileSupport P) p ⊆ extractedCavityUnion P T := by
  have hpT : p ∈ T.placements := Finset.mem_sdiff.mp hp |>.1
  have hpNot : p ∉ selectedCarrierPlacements P T := Finset.mem_sdiff.mp hp |>.2
  intro z hzp
  have hzsq := T.placement_subset hpT hzp
  have hznot : z ∉ extractedCarrierUnion P T := by
    intro hzcar
    rcases Finset.mem_biUnion.mp hzcar with ⟨q, _, hzq⟩
    let pq := cornerPlacement P T q.1 q.2
    have hpqT : pq ∈ T.placements := cornerPlacement_mem P T q.1 q.2
    have hpqSel : pq ∈ selectedCarrierPlacements P T :=
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    have hpne : p ≠ pq := fun h => hpNot (h ▸ hpqSel)
    have hzq' : z ∈ Placement.cells (registerTileSupport P) pq := by
      dsimp [pq]
      change z ∈ translate
        (registerTileSupport P (cornerPlacement P T q.1 q.2).tile)
        (cornerPlacement P T q.1 q.2).shift
      rw [(extractedDatum_spec P T q.1 q.2).1,
        (extractedDatum_spec P T q.1 q.2).2]
      exact hzq
    exact Finset.disjoint_left.mp (T.disjoint hpT hpqT hpne) hzp hzq'
  rw [← square_sdiff_extractedCarrierUnion_eq_cavities P T]
  exact Finset.mem_sdiff.mpr ⟨hzsq, hznot⟩

/-- Distinct registered cavities are separated by more than one lattice
edge.  This strengthens pairwise disjointness exactly enough for connected
residual tiles. -/
theorem macroCavities_not_adjacent
    (P : RegisterParams) {n : ℕ} (a b : Fin n × Fin n) (hab : a ≠ b)
    (u v : Fin P.tileCount) {x y : Cell}
    (hx : x ∈ macroCavity P a.1.1 a.2.1 u)
    (hy : y ∈ macroCavity P b.1.1 b.2.1 v) : ¬ Adj4 x y := by
  intro hadj
  have hxb := macroCavity_bounds hx
  have hyb := macroCavity_bounds hy
  have hm := P.pitch_ge_tile_margin
  have hu := u.isLt
  have hv := v.isLt
  rcases hadj with h | h | h | h <;> subst y
  all_goals
    by_cases hi : a.1.1 = b.1.1
    · have hj : a.2.1 ≠ b.2.1 := by
        intro hj
        apply hab
        exact Prod.ext (Fin.ext hi) (Fin.ext hj)
      rcases lt_or_gt_of_ne hj with hjlt | hjgt
      · have hstep := Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr hjlt)
        have hstep' : a.2.1 * P.pitch + P.pitch ≤ b.2.1 * P.pitch := by
          simpa [Nat.add_mul] using hstep
        have hstepZ : ((a.2.1 * P.pitch : ℕ) : ℤ) + (P.pitch : ℤ) ≤
            ((b.2.1 * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep'
        push_cast at hxb hyb
        rcases hxb.2.2 with hx2 | hx2 <;>
          rcases hyb.2.2 with hy2 | hy2 <;> omega
      · have hstep := Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr hjgt)
        have hstep' : b.2.1 * P.pitch + P.pitch ≤ a.2.1 * P.pitch := by
          simpa [Nat.add_mul] using hstep
        have hstepZ : ((b.2.1 * P.pitch : ℕ) : ℤ) + (P.pitch : ℤ) ≤
            ((a.2.1 * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep'
        push_cast at hxb hyb
        rcases hxb.2.2 with hx2 | hx2 <;>
          rcases hyb.2.2 with hy2 | hy2 <;> omega
    · rcases lt_or_gt_of_ne hi with hilt | higt
      · have hstep := Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr hilt)
        have hstep' : a.1.1 * P.pitch + P.pitch ≤ b.1.1 * P.pitch := by
          simpa [Nat.add_mul] using hstep
        have hstepZ : ((a.1.1 * P.pitch : ℕ) : ℤ) + (P.pitch : ℤ) ≤
            ((b.1.1 * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep'
        push_cast at hxb hyb
        omega
      · have hstep := Nat.mul_le_mul_right P.pitch (Nat.succ_le_iff.mpr higt)
        have hstep' : b.1.1 * P.pitch + P.pitch ≤ a.1.1 * P.pitch := by
          simpa [Nat.add_mul] using hstep
        have hstepZ : ((b.1.1 * P.pitch : ℕ) : ℤ) + (P.pitch : ℤ) ≤
            ((a.1.1 * P.pitch : ℕ) : ℤ) := by exact_mod_cast hstep'
        push_cast at hxb hyb
        omega

theorem Walk4In.stays_in_cavity
    (P : RegisterParams) {n : ℕ}
    (U : Fin n × Fin n → Fin P.tileCount)
    {a : Fin n × Fin n} {x y : Cell}
    (w : Walk4In
      (Finset.univ.biUnion fun q : Fin n × Fin n =>
        macroCavity P q.1.1 q.2.1 (U q)) x y)
    (hx : x ∈ macroCavity P a.1.1 a.2.1 (U a)) :
    y ∈ macroCavity P a.1.1 a.2.1 (U a) := by
  induction w with
  | nil _ => exact hx
  | @cons x z y hxU hxz w ih =>
      have hzU : z ∈ Finset.univ.biUnion fun q : Fin n × Fin n =>
          macroCavity P q.1.1 q.2.1 (U q) := by
        cases w with
        | nil hz => exact hz
        | cons hz _ _ => exact hz
      rcases Finset.mem_biUnion.mp hzU with ⟨b, _, hzb⟩
      have hza : z ∈ macroCavity P a.1.1 a.2.1 (U a) := by
        by_cases hab : a = b
        · simpa [hab] using hzb
        · exact (macroCavities_not_adjacent P a b hab (U a) (U b) hx hzb hxz).elim
      exact ih hza

/-- Every residual placement is the unique PlugL occupying one registered
macro-cavity, with its physical translation recovered exactly. -/
theorem residualPlacement_unique_plug
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {p : Placement (RegisterTile P)}
    (hp : p ∈ residualPlacements P T) :
    ∃! q : Fin n × Fin n,
      p.tile = none ∧
      p.shift = macroCavityOrigin P q.1.1 q.2.1
        (extractedDatum P T q.1 q.2).tile := by
  let U : Fin n × Fin n → Fin P.tileCount := fun q =>
    (extractedDatum P T q.1 q.2).tile
  have hsub := residualPlacement_cells_subset_cavities P T hp
  have hpne := registerTileSupport_nonempty P p.tile
  obtain ⟨x, hx⟩ := hpne
  have hxp : (x.1 + p.shift.1, x.2 + p.shift.2) ∈
      Placement.cells (registerTileSupport P) p :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hxU := hsub hxp
  rcases Finset.mem_biUnion.mp hxU with ⟨q, _, hxq⟩
  have hpconn : FourConnected (Placement.cells (registerTileSupport P) p) :=
    (registerTileSupport_fourConnected P p.tile).translate p.shift
  have hpInQ : Placement.cells (registerTileSupport P) p ⊆
      macroCavity P q.1.1 q.2.1 (U q) := by
    intro y hyp
    have w := hpconn.2 hxp hyp
    have wU := w.mono hsub
    exact wU.stays_in_cavity P U hxq
  have htile : p.tile = none := by
    cases ht : p.tile with
    | none => rfl
    | some idx =>
        rcases idx with ⟨η, u, l⟩
        have hc := Finset.card_le_card hpInQ
        have hpitch := P.pitch_ge_sixty_eight
        simp [Placement.cells, ht, registerTileSupport, carrier_area,
          card_macroCavity] at hc
        nlinarith
  have hcells : Placement.cells (registerTileSupport P) p =
      macroCavity P q.1.1 q.2.1 (U q) := by
    apply Finset.eq_of_subset_of_card_le hpInQ
    simp [Placement.cells, htile, registerTileSupport, card_macroCavity]
  have hshift : p.shift = macroCavityOrigin P q.1.1 q.2.1 (U q) := by
    apply plug_translation_unique P q.1.1 q.2.1 (U q)
    simpa [Placement.cells, htile, registerTileSupport] using hcells
  refine ⟨q, ⟨htile, hshift⟩, ?_⟩
  intro r hr
  by_contra hqr
  have hEq : macroCavity P q.1.1 q.2.1 (U q) =
      macroCavity P r.1.1 r.2.1 (U r) := by
    calc
      macroCavity P q.1.1 q.2.1 (U q) =
          Placement.cells (registerTileSupport P) p := hcells.symm
      _ = translate plugL p.shift := by
        simp [Placement.cells, htile, registerTileSupport]
      _ = translate plugL
          (macroCavityOrigin P r.1.1 r.2.1
            (extractedDatum P T r.1 r.2).tile) := by rw [hr.2]
      _ = macroCavity P r.1.1 r.2.1 (U r) := by
        rfl
  have hnon : (macroCavity P q.1.1 q.2.1 (U q)).Nonempty := by
    exact ⟨macroCavityOrigin P q.1.1 q.2.1 (U q) + (0, 1), by
      apply Finset.mem_image.mpr
      refine ⟨(0, 1), by simp [plugL], ?_⟩
      apply Prod.ext <;> dsimp <;> ring⟩
  obtain ⟨z, hz⟩ := hnon
  have hz' : z ∈ macroCavity P r.1.1 r.2.1 (U r) := hEq ▸ hz
  exact Finset.disjoint_left.mp
    (macroCavities_pairwise_disjoint P (by
      intro hpair
      apply hqr
      exact Prod.ext (Fin.ext (congrArg Prod.fst hpair).symm)
        (Fin.ext (congrArg Prod.snd hpair).symm)) (U q) (U r)) hz hz'

/-- In an exact tiling, being a carrier occurrence is equivalent to belonging
to the `n²` selected row-major placements. -/
theorem placement_is_carrier_iff_selected
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {p : Placement (RegisterTile P)} (hp : p ∈ T.placements) :
    p.tile ≠ none ↔ p ∈ selectedCarrierPlacements P T := by
  constructor
  · intro hcar
    by_contra hsel
    have hres : p ∈ residualPlacements P T := Finset.mem_sdiff.mpr ⟨hp, hsel⟩
    obtain ⟨_, hq, _⟩ := residualPlacement_unique_plug P T hres
    exact hcar hq.1
  · exact selectedCarrierPlacement_is_carrier P T

def cavityPlugPlacement (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (q : Fin n × Fin n) : Placement (RegisterTile P) :=
  ⟨none, macroCavityOrigin P q.1.1 q.2.1
    (extractedDatum P T q.1 q.2).tile⟩

theorem cavityPlugPlacement_mem
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (q : Fin n × Fin n) : cavityPlugPlacement P T q ∈ T.placements := by
  let u := (extractedDatum P T q.1 q.2).tile
  let z : Cell := macroCavityOrigin P q.1.1 q.2.1 u + (0, 1)
  have hzC : z ∈ macroCavity P q.1.1 q.2.1 u := by
    apply Finset.mem_image.mpr
    refine ⟨(0, 1), by simp [plugL], ?_⟩
    apply Prod.ext <;> dsimp [z] <;> ring
  have hzSq := macroCavity_subset_square P q.1 q.2 u hzC
  obtain ⟨p, hpT, hzp⟩ := T.every_cell_covered hzSq
  have hpNot : p ∉ selectedCarrierPlacements P T := by
    intro hpSel
    rcases Finset.mem_image.mp hpSel with ⟨r, _, hpr⟩
    subst p
    have hzCarrier : z ∈ translate
        (CarrierDatum.support P (extractedDatum P T r.1 r.2))
        (macroCorner P r.1.1 r.2.1) := by
      simpa [Placement.cells, (extractedDatum_spec P T r.1 r.2).1,
        (extractedDatum_spec P T r.1 r.2).2, CarrierDatum.support,
        registerTileSupport] using hzp
    exact Finset.disjoint_left.mp
      (macroCavity_disjoint_extractedCarrier P T q r) hzC hzCarrier
  have hpRes : p ∈ residualPlacements P T := Finset.mem_sdiff.mpr ⟨hpT, hpNot⟩
  obtain ⟨r, hr, huniq⟩ := residualPlacement_unique_plug P T hpRes
  have hpCells : Placement.cells (registerTileSupport P) p =
      macroCavity P r.1.1 r.2.1 (extractedDatum P T r.1 r.2).tile := by
    simp [Placement.cells, hr.1, registerTileSupport, hr.2, macroCavity, cavity]
  have hzR : z ∈ macroCavity P r.1.1 r.2.1
      (extractedDatum P T r.1 r.2).tile := hpCells ▸ hzp
  have hqr : q = r := by
    by_contra hne
    exact Finset.disjoint_left.mp
      (macroCavities_pairwise_disjoint P (by
        intro hpair
        apply hne
        exact Prod.ext (Fin.ext (congrArg Prod.fst hpair))
          (Fin.ext (congrArg Prod.snd hpair))) u
        (extractedDatum P T r.1 r.2).tile) hzC hzR
  subst r
  have hpEq : p = cavityPlugPlacement P T q := by
    cases p
    simp only [cavityPlugPlacement, Placement.mk.injEq]
    exact ⟨hr.1, hr.2⟩
  simpa [hpEq] using hpT

/-- Occurrence-level residual decomposition: there is exactly one PlugL
placement per macro-cell and no other placements. -/
theorem residualPlacements_eq_plugs
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    residualPlacements P T =
      Finset.univ.image (cavityPlugPlacement P T) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, _⟩ := residualPlacement_unique_plug P T hp
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    cases p
    simp only [cavityPlugPlacement, Placement.mk.injEq]
    exact ⟨hq.1.symm, hq.2.symm⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
    exact Finset.mem_sdiff.mpr
      ⟨cavityPlugPlacement_mem P T q, by
        intro hsel
        exact selectedCarrierPlacement_is_carrier P T hsel rfl⟩

end
end PakFixedPolyomino
