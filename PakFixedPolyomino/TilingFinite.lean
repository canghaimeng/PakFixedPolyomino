import PakFixedPolyomino.Tiling

namespace PakFixedPolyomino

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def tileAnchor (tiles : I → Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) (i : I) : Cell :=
  Classical.choose (hnonempty i)

theorem tileAnchor_mem (tiles : I → Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) (i : I) :
    tileAnchor tiles hnonempty i ∈ tiles i :=
  Classical.choose_spec (hnonempty i)

def placementAnchor (tiles : I → Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) (p : Placement I) : Cell :=
  tileAnchor tiles hnonempty p.tile + p.shift

theorem placementAnchor_mem_cells (tiles : I → Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) (p : Placement I) :
    placementAnchor tiles hnonempty p ∈ Placement.cells tiles p := by
  apply Finset.mem_image.mpr
  exact ⟨tileAnchor tiles hnonempty p.tile,
    tileAnchor_mem tiles hnonempty p.tile, rfl⟩

theorem placement_key_injective (tiles : I → Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) : Function.Injective
    (fun p : Placement I => (p.tile, placementAnchor tiles hnonempty p)) := by
  intro p q h
  have ht : p.tile = q.tile := congrArg Prod.fst h
  have ha : placementAnchor tiles hnonempty p =
      placementAnchor tiles hnonempty q := congrArg Prod.snd h
  cases p with
  | mk pt ps =>
      cases q with
      | mk qt qs =>
          dsimp at ht ha ⊢
          subst qt
          have hs : ps = qs := by
            unfold placementAnchor at ha
            exact add_left_cancel ha
          subst qs
          rfl

def tilingCode (tiles : I → Polyomino) (region : Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty)
    (T : Tiling tiles region) : Finset (I × ↑region) :=
  T.placements.attach.image fun p =>
    (p.1.tile, ⟨placementAnchor tiles hnonempty p.1,
      T.placement_subset p.2 (placementAnchor_mem_cells tiles hnonempty p.1)⟩)

theorem mem_tilingCode_iff (tiles : I → Polyomino) (region : Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty)
    (T : Tiling tiles region) (i : I) (z : ↑region) :
    (i, z) ∈ tilingCode tiles region hnonempty T ↔
    ∃ p ∈ T.placements, p.tile = i ∧
      placementAnchor tiles hnonempty p = z.1 := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨p, _, hp⟩
    refine ⟨p.1, p.2, ?_, ?_⟩
    · exact congrArg Prod.fst hp
    · exact congrArg (fun q : I × ↑region => q.2.1) hp
  · rintro ⟨p, hp, rfl, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact hz

/-- For a fixed finite family of nonempty finite tiles and a fixed finite
region, the type of exact translation-only tilings is finite.  The injection
records, for every placement, its prototype and the image of one canonical
tile cell in the region; this pair uniquely determines the translation. -/
theorem tilingCode_injective (tiles : I → Polyomino) (region : Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) :
    Function.Injective (tilingCode tiles region hnonempty) := by
  intro T U hcode
  have hplacements : T.placements = U.placements := by
    ext p
    constructor
    · intro hp
      let z : ↑region :=
        ⟨placementAnchor tiles hnonempty p,
          T.placement_subset hp (placementAnchor_mem_cells tiles hnonempty p)⟩
      have hmT : (p.tile, z) ∈ tilingCode tiles region hnonempty T :=
        (mem_tilingCode_iff tiles region hnonempty T p.tile z).2
          ⟨p, hp, rfl, rfl⟩
      have hmU : (p.tile, z) ∈ tilingCode tiles region hnonempty U := by
        rw [← hcode]
        exact hmT
      rcases (mem_tilingCode_iff tiles region hnonempty U p.tile z).1 hmU with
        ⟨q, hq, hqtile, hqanchor⟩
      have hkey : (q.tile, placementAnchor tiles hnonempty q) =
          (p.tile, placementAnchor tiles hnonempty p) := by
        apply Prod.ext
        · exact hqtile
        · exact hqanchor
      have hqp := placement_key_injective tiles hnonempty hkey
      simpa [hqp] using hq
    · intro hp
      let z : ↑region :=
        ⟨placementAnchor tiles hnonempty p,
          U.placement_subset hp (placementAnchor_mem_cells tiles hnonempty p)⟩
      have hmU : (p.tile, z) ∈ tilingCode tiles region hnonempty U :=
        (mem_tilingCode_iff tiles region hnonempty U p.tile z).2
          ⟨p, hp, rfl, rfl⟩
      have hmT : (p.tile, z) ∈ tilingCode tiles region hnonempty T := by
        rw [hcode]
        exact hmU
      rcases (mem_tilingCode_iff tiles region hnonempty T p.tile z).1 hmT with
        ⟨q, hq, hqtile, hqanchor⟩
      have hkey : (q.tile, placementAnchor tiles hnonempty q) =
          (p.tile, placementAnchor tiles hnonempty p) := by
        apply Prod.ext
        · exact hqtile
        · exact hqanchor
      have hqp := placement_key_injective tiles hnonempty hkey
      simpa [hqp] using hq
  cases T
  cases U
  simp_all

def tilingFintype (tiles : I → Polyomino) (region : Polyomino)
    (hnonempty : ∀ i, (tiles i).Nonempty) : Fintype (Tiling tiles region) :=
  Fintype.ofInjective (tilingCode tiles region hnonempty)
    (tilingCode_injective tiles region hnonempty)

end
end PakFixedPolyomino
