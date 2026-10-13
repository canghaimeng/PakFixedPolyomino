import PakFixedPolyomino.Lattice

namespace PakFixedPolyomino

/-- A placement remembers a prototype and its translation vector. -/
structure Placement (ι : Type*) where
  tile : ι
  shift : Cell
  deriving DecidableEq

def Placement.cells {ι : Type*} (tiles : ι → Polyomino) (p : Placement ι) : Polyomino :=
  translate (tiles p.tile) p.shift

/-- Exact finite tiling: placed supports are pairwise disjoint and cover the region. -/
structure Tiling {ι : Type*} [DecidableEq ι]
    (tiles : ι → Polyomino) (region : Polyomino) where
  placements : Finset (Placement ι)
  disjoint : Set.Pairwise (↑placements : Set (Placement ι))
    fun p q => Disjoint (Placement.cells tiles p) (Placement.cells tiles q)
  covers : placements.biUnion (Placement.cells tiles) = region

theorem Tiling.every_cell_covered {ι : Type*} [DecidableEq ι]
    {tiles : ι → Polyomino} {region : Polyomino} (T : Tiling tiles region)
    {x : Cell} (hx : x ∈ region) :
    ∃ p ∈ T.placements, x ∈ Placement.cells tiles p := by
  have : x ∈ T.placements.biUnion (Placement.cells tiles) := by simpa [T.covers] using hx
  simpa using this

theorem Tiling.placement_subset {ι : Type*} [DecidableEq ι]
    {tiles : ι → Polyomino} {region : Polyomino} (T : Tiling tiles region)
    {p : Placement ι} (hp : p ∈ T.placements) : Placement.cells tiles p ⊆ region := by
  intro x hx
  rw [← T.covers]
  exact Finset.mem_biUnion.mpr ⟨p, hp, hx⟩

theorem Tiling.cover_unique {ι : Type*} [DecidableEq ι]
    {tiles : ι → Polyomino} {region : Polyomino} (T : Tiling tiles region)
    {p q : Placement ι} (hp : p ∈ T.placements) (hq : q ∈ T.placements)
    {x : Cell} (hxp : x ∈ Placement.cells tiles p) (hxq : x ∈ Placement.cells tiles q) :
    p = q := by
  by_contra hpq
  have hd := T.disjoint hp hq hpq
  exact Finset.disjoint_left.mp hd hxp hxq

end PakFixedPolyomino
