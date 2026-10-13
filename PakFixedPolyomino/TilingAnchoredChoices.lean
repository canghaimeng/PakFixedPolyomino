import PakFixedPolyomino.Tiling

/-! Literal fixed finite choices at an uncovered cell. These are geometric
choices for the membership machine, not a tape-time or membership certificate. -/
namespace PakFixedPolyomino.TilingAnchoredChoices
variable {ι : Type*} [DecidableEq ι]
variable {tiles : ι → Polyomino} {region : Polyomino} {done : Finset (Placement ι)}

abbrev Anchor (tiles : ι → Polyomino) := (i : ι) × {a : Cell // a ∈ tiles i}

def placeAt (c : Cell) (a : Anchor tiles) : Placement ι :=
  ⟨a.1,(c.1-a.2.val.1,c.2-a.2.val.2)⟩

theorem placeAt_contains (tiles : ι → Polyomino) (c : Cell) (a : Anchor tiles) :
    c ∈ Placement.cells tiles (placeAt c a) := by
  apply mem_translate.mpr
  simpa [placeAt] using a.2.property

def anchorOf (tiles : ι → Polyomino) (c : Cell) (p : Placement ι)
    (hp : c ∈ Placement.cells tiles p) : Anchor tiles :=
  ⟨p.tile,⟨(c.1-p.shift.1,c.2-p.shift.2),mem_translate.mp hp⟩⟩

theorem placeAt_anchorOf (tiles : ι → Polyomino) (c : Cell) (p : Placement ι)
    (hp : c ∈ Placement.cells tiles p) : placeAt c (anchorOf tiles c p hp) = p := by
  cases p with
  | mk tile shift =>
    cases shift
    simp [placeAt,anchorOf]

theorem anchorOf_placeAt (tiles : ι → Polyomino) (c : Cell) (a : Anchor tiles) :
    anchorOf tiles c (placeAt c a) (placeAt_contains tiles c a) = a := by
  rcases a with ⟨i,a⟩
  dsimp only [anchorOf,placeAt]
  apply congrArg (Sigma.mk i)
  apply Subtype.ext
  ext <;> simp

def anchorEquiv (tiles : ι → Polyomino) (c : Cell) :
    Anchor tiles ≃ {p : Placement ι // c ∈ Placement.cells tiles p} where
  toFun a := ⟨placeAt c a,placeAt_contains tiles c a⟩
  invFun p := anchorOf tiles c p.val p.property
  left_inv := anchorOf_placeAt tiles c
  right_inv p := Subtype.ext (placeAt_anchorOf tiles c p.val p.property)

theorem placeAt_injective (tiles : ι → Polyomino) (c : Cell) :
    Function.Injective (placeAt c : Anchor tiles → Placement ι) := by
  intro a b h
  apply (anchorEquiv tiles c).injective
  exact Subtype.ext h

instance anchorFintype [Fintype ι] (tiles : ι → Polyomino) : Fintype (Anchor tiles) :=
  inferInstance

instance coveringPlacementsFintype [Fintype ι] (tiles : ι → Polyomino) (c : Cell) :
    Fintype {p : Placement ι // c ∈ Placement.cells tiles p} :=
  Fintype.ofEquiv (Anchor tiles) (anchorEquiv tiles c)

theorem covering_choices_card [Fintype ι] (tiles : ι → Polyomino) (c : Cell) :
    Fintype.card {p : Placement ι // c ∈ Placement.cells tiles p} =
      ∑ i : ι,(tiles i).card := by
  rw [← Fintype.card_congr (anchorEquiv tiles c)]
  simp [Anchor,Fintype.card_sigma]

theorem tiling_choice_unique (tiles : ι → Polyomino) (T : Tiling tiles region)
    (c : Cell) (hc : c ∈ region) :
    ∃! a : Anchor tiles, placeAt c a ∈ T.placements := by
  obtain ⟨p,hp,hcp⟩ := T.every_cell_covered hc
  refine ⟨anchorOf tiles c p hcp,by simpa [placeAt_anchorOf] using hp,?_⟩
  intro a ha
  apply placeAt_injective tiles c
  rw [placeAt_anchorOf]
  exact T.cover_unique ha hp (placeAt_contains tiles c a) hcp

def covered (tiles : ι → Polyomino) (done : Finset (Placement ι)) : Polyomino :=
  done.biUnion (Placement.cells tiles)

def uncovered (tiles : ι → Polyomino) (region : Polyomino)
    (done : Finset (Placement ι)) : Polyomino := region \ covered tiles done

theorem chosen_not_done (tiles : ι → Polyomino) (c : Cell)
    (hc : c ∈ uncovered tiles region done) (a : Anchor tiles) : placeAt c a ∉ done := by
  intro ha
  exact (Finset.mem_sdiff.mp hc).2
    (Finset.mem_biUnion.mpr ⟨placeAt c a,ha,placeAt_contains tiles c a⟩)

theorem uncovered_choice_unique (tiles : ι → Polyomino) (T : Tiling tiles region)
    (done : Finset (Placement ι)) (c : Cell) (hc : c ∈ uncovered tiles region done) :
    ∃! a : Anchor tiles, placeAt c a ∈ T.placements ∧ placeAt c a ∉ done := by
  obtain ⟨a,ha,hu⟩ := tiling_choice_unique tiles T c (Finset.mem_sdiff.mp hc).1
  refine ⟨a,⟨ha,chosen_not_done tiles c hc a⟩,?_⟩
  exact fun b hb => hu b hb.1

theorem insert_choice_card (tiles : ι → Polyomino) (c : Cell)
    (hc : c ∈ uncovered tiles region done) (a : Anchor tiles) :
    (insert (placeAt c a) done).card = done.card+1 :=
  Finset.card_insert_of_notMem (chosen_not_done tiles c hc a)

theorem uncovered_insert (tiles : ι → Polyomino) (region : Polyomino)
    (done : Finset (Placement ι)) (p : Placement ι) :
    uncovered tiles region (insert p done) = uncovered tiles region done \ Placement.cells tiles p := by
  ext c
  simp [uncovered,covered,Finset.mem_biUnion]
  tauto

theorem uncovered_strictly_decreases (tiles : ι → Polyomino) (c : Cell)
    (hc : c ∈ uncovered tiles region done) (a : Anchor tiles) :
    (uncovered tiles region (insert (placeAt c a) done)).card <
      (uncovered tiles region done).card := by
  rw [uncovered_insert]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.sdiff_subset,?_⟩
  intro heq
  have hmem : c ∈ uncovered tiles region done \ Placement.cells tiles (placeAt c a) := by
    rw [heq]
    exact hc
  exact (Finset.mem_sdiff.mp hmem).2 (placeAt_contains tiles c a)

end PakFixedPolyomino.TilingAnchoredChoices
