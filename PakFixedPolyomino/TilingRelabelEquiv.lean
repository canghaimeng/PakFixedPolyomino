import PakFixedPolyomino.TilingFinite

/-! Reindexing prototypes with the same physical supports preserves every
exact translation-only tiling and its multiplicity. -/
namespace PakFixedPolyomino.TilingRelabelEquiv
noncomputable section
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

def placementEquiv (e : I ≃ J) : Placement I ≃ Placement J where
  toFun p := ⟨e p.tile, p.shift⟩
  invFun p := ⟨e.symm p.tile, p.shift⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

theorem placement_cells (e : I ≃ J) (tilesI : I → Polyomino) (tilesJ : J → Polyomino)
    (same : ∀ i, tilesJ (e i) = tilesI i) (p : Placement I) :
    Placement.cells tilesJ (placementEquiv e p) = Placement.cells tilesI p := by
  exact congrArg (fun P => translate P p.shift) (same p.tile)

def mapTiling (e : I ≃ J) (tilesI : I → Polyomino) (tilesJ : J → Polyomino)
    (same : ∀ i, tilesJ (e i) = tilesI i) {region : Polyomino}
    (T : Tiling tilesI region) : Tiling tilesJ region where
  placements := T.placements.map (placementEquiv e).toEmbedding
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    have neq : p' ≠ q' := fun eq => hpq (congrArg (placementEquiv e) eq)
    change Disjoint (Placement.cells tilesJ (placementEquiv e p'))
      (Placement.cells tilesJ (placementEquiv e q'))
    rw [placement_cells e tilesI tilesJ same, placement_cells e tilesI tilesJ same]
    exact T.disjoint hp' hq' neq
  covers := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
      change z ∈ Placement.cells tilesJ (placementEquiv e p') at hz
      rw [placement_cells e tilesI tilesJ same] at hz
      rw [← T.covers]
      exact Finset.mem_biUnion.mpr ⟨p', hp', hz⟩
    · intro hz
      rw [← T.covers] at hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      refine Finset.mem_biUnion.mpr ⟨placementEquiv e p, Finset.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
      rw [placement_cells e tilesI tilesJ same]
      exact hz

theorem tiling_eq_of_placements {tiles : I → Polyomino} {region : Polyomino}
    (T U : Tiling tiles region) (same : T.placements = U.placements) : T = U := by
  cases T
  cases U
  simp_all

def equiv (e : I ≃ J) (tilesI : I → Polyomino) (tilesJ : J → Polyomino)
    (same : ∀ i, tilesJ (e i) = tilesI i) (region : Polyomino) :
    Tiling tilesI region ≃ Tiling tilesJ region where
  toFun := mapTiling e tilesI tilesJ same
  invFun := mapTiling e.symm tilesJ tilesI (fun j => by simpa using (same (e.symm j)).symm)
  left_inv T := by
    apply tiling_eq_of_placements
    change (placementEquiv e).finsetCongr.symm
      ((placementEquiv e).finsetCongr T.placements) = T.placements
    exact (placementEquiv e).finsetCongr.symm_apply_apply T.placements
  right_inv T := by
    apply tiling_eq_of_placements
    change (placementEquiv e).finsetCongr
      ((placementEquiv e).finsetCongr.symm T.placements) = T.placements
    exact (placementEquiv e).finsetCongr.apply_symm_apply T.placements

end
end PakFixedPolyomino.TilingRelabelEquiv
