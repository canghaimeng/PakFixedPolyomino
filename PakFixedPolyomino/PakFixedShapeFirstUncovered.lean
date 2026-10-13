import PakFixedPolyomino.PakFixedShapeAnchoredChoices

/-! Deterministic row-major first-uncovered selection for the original shape
set. This finite-list algorithm has no ordinary tape runtime certificate yet. -/
namespace PakFixedPolyomino.PakFixedShapeFirstUncovered
noncomputable section
open TilingAnchoredChoices PakFixedWeightedShapeFamily PakFixedShapeAnchoredChoices
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def scanCells (n : Nat) : List Cell :=
  (List.range n).flatMap (fun (y : Nat) =>
    (List.range n).map (fun (x : Nat) => ((x : Int),(y : Int))))

theorem mem_scanCells (n : Nat) (c : Cell) : c ∈ scanCells n ↔ c ∈ square n := by
  constructor
  · intro hc
    obtain ⟨y,hy,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    exact ofNat_pair_mem_square.mpr ⟨List.mem_range.mp hx,List.mem_range.mp hy⟩
  · intro hc
    obtain ⟨x,hx,hxeq⟩ := mem_natInterval.mp (Finset.mem_product.mp hc).1
    obtain ⟨y,hy,hyeq⟩ := mem_natInterval.mp (Finset.mem_product.mp hc).2
    exact List.mem_flatMap.mpr ⟨y,List.mem_range.mpr hy,
      List.mem_map.mpr ⟨x,List.mem_range.mpr hx,Prod.ext hxeq hyeq⟩⟩

def firstUncovered (n : Nat) (done : Finset (Placement Shape)) : Option Cell :=
  (scanCells n).find? (fun c => decide (c ∈ uncovered shapeSupport (square n) done))

theorem first_some_mem (n : Nat) (done : Finset (Placement Shape)) (c : Cell)
    (h : firstUncovered n done = some c) : c ∈ uncovered shapeSupport (square n) done :=
  of_decide_eq_true (List.find?_some
    (p := fun a : Cell => decide (a ∈ uncovered shapeSupport (square n) done)) h)

theorem first_some_prefix (n : Nat) (done : Finset (Placement Shape)) (c : Cell)
    (h : firstUncovered n done = some c) :
    ∃ pre post,scanCells n = pre ++ c :: post ∧
      ∀ a ∈ pre,a ∉ uncovered shapeSupport (square n) done := by
  obtain ⟨_,pre,post,heq,hpre⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨pre,post,heq,fun a ha => by simpa using hpre a ha⟩

theorem first_none_iff (n : Nat) (done : Finset (Placement Shape)) :
    firstUncovered n done = none ↔ uncovered shapeSupport (square n) done = ∅ := by
  unfold firstUncovered
  rw [List.find?_eq_none]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hlist := (mem_scanCells n c).mpr (Finset.mem_sdiff.mp hc).1
    have hbad := h c hlist
    simpa [hc] using hbad
  · intro h c _
    simp [h]

theorem first_tiling_choice_unique (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Finset (Placement Shape)) (c : Cell) (h : firstUncovered n done = some c) :
    ∃! p : Placement Shape,p ∈ candidates c ∧ p ∈ T.placements ∧ p ∉ done :=
  tiling_next_unique n T done c (first_some_mem n done c h)

theorem uncovered_empty_iff_done (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Finset (Placement Shape)) (hsub : done ⊆ T.placements) :
    uncovered shapeSupport (square n) done = ∅ ↔ done = T.placements := by
  constructor
  · intro h
    apply Finset.Subset.antisymm hsub
    intro p hp
    by_contra hnot
    obtain ⟨a,ha⟩ := shape_nonempty p.tile
    let c : Cell := (a.1+p.shift.1,a.2+p.shift.2)
    have hcp : c ∈ Placement.cells shapeSupport p := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hcr := T.placement_subset hp hcp
    have hcovered : square n ⊆ covered shapeSupport done := Finset.sdiff_eq_empty_iff_subset.mp h
    obtain ⟨q,hq,hcq⟩ := Finset.mem_biUnion.mp (hcovered hcr)
    have heq := T.cover_unique hp (hsub hq) hcp hcq
    exact hnot (heq ▸ hq)
  · intro h
    rw [h]
    change square n \ T.placements.biUnion (Placement.cells shapeSupport) = ∅
    rw [T.covers]
    simp

theorem first_none_iff_done (n : Nat) (T : Tiling shapeSupport (square n))
    (done : Finset (Placement Shape)) (hsub : done ⊆ T.placements) :
    firstUncovered n done = none ↔ done = T.placements :=
  (first_none_iff n done).trans (uncovered_empty_iff_done n T done hsub)

theorem zero_first_none (done : Finset (Placement Shape)) : firstUncovered 0 done = none := rfl

theorem first_uncovered_spec :
    (∀ n c,c ∈ scanCells n ↔ c ∈ square n) ∧
    (∀ n done c,firstUncovered n done = some c →
      c ∈ uncovered shapeSupport (square n) done) ∧
    (∀ n done c,firstUncovered n done = some c →
      ∃ pre post,scanCells n = pre ++ c :: post ∧
        ∀ a ∈ pre,a ∉ uncovered shapeSupport (square n) done) ∧
    (∀ n done,firstUncovered n done = none ↔ uncovered shapeSupport (square n) done = ∅) ∧
    (∀ n (T : Tiling shapeSupport (square n)) done c,firstUncovered n done = some c →
      ∃! p : Placement Shape,p ∈ candidates c ∧ p ∈ T.placements ∧ p ∉ done) ∧
    (∀ n (T : Tiling shapeSupport (square n)) done,done ⊆ T.placements →
      (firstUncovered n done = none ↔ done = T.placements)) ∧
    (∀ done,firstUncovered 0 done = none) :=
  ⟨mem_scanCells,first_some_mem,first_some_prefix,first_none_iff,first_tiling_choice_unique,
    first_none_iff_done,zero_first_none⟩

end
end PakFixedPolyomino.PakFixedShapeFirstUncovered
