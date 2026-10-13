import PakFixedPolyomino.PakFixedShapeStencilCellAlignment
import PakFixedPolyomino.PakFixedShapeChoiceWords

/-! The ORIGINAL finite shape-anchor inventory supplies the stencil, not a
new parameterized tile family. Each original anchor's ordinary tape checker
tests exactly Fits for its translated placement on the unmodified square.
All offsets are fixed program data from the same physical shape support. -/
namespace PakFixedPolyomino.PakFixedShapeStencilFitsAlignment
noncomputable section
open StandardBitTime StandardBitWordVector
open PakFixedWeightedStandardBinaryCount (value)
open PakFixedWeightedShapeFamily TilingAnchoredChoices PakFixedShapeChoiceWords
open PakFixedShapeStencilCellAlignment (frame point free_frame)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def offsets (a : Label) : List Cell :=
  (shapeSupport a.1).toList.map (fun b => (b.1-a.2.val.1,b.2-a.2.val.2))
def fitsBits (a : Label) (raw : List Bool) : List Bool :=
  [StandardBitGridStencil.fits (offsets a) raw]

theorem mem_offsets (a : Label) (d : Cell) : d∈offsets a ↔
    ∃ b∈shapeSupport a.1,(b.1-a.2.val.1,b.2-a.2.val.2)=d := by
  simp only [offsets,List.mem_map,Finset.mem_toList]

theorem cells_offsets (a : Label) (x y : Nat) (c : Cell) :
    c∈Placement.cells shapeSupport (placeAt ((x : Int),(y : Int)) a) ↔
      ∃ d∈offsets a,point x y d=c := by
  constructor
  · intro hc
    change c∈translate (shapeSupport a.1) ((x : Int)-a.2.val.1,(y : Int)-a.2.val.2) at hc
    let b : Cell := (c.1-((x : Int)-a.2.val.1),c.2-((y : Int)-a.2.val.2))
    have hb : b∈shapeSupport a.1 := mem_translate.mp hc
    refine ⟨(b.1-a.2.val.1,b.2-a.2.val.2),(mem_offsets a _).mpr ⟨b,hb,rfl⟩,?_⟩
    ext <;> dsimp [point,b] <;> ring
  · rintro ⟨d,hd,hc⟩
    obtain ⟨b,hb,he⟩ := (mem_offsets a d).mp hd
    subst d
    subst c
    change point x y (b.1-a.2.val.1,b.2-a.2.val.2)∈
      translate (shapeSupport a.1) ((x : Int)-a.2.val.1,(y : Int)-a.2.val.2)
    refine Finset.mem_image.mpr ⟨b,hb,?_⟩
    ext <;> dsimp [point] <;> ring

theorem fits_iff_uncovered (n : Nat) (done : Done) (p : Placement Shape) :
    Fits n done p ↔ Placement.cells shapeSupport p⊆uncovered shapeSupport (square n) done := by
  constructor
  · rintro ⟨hs,hd⟩ c hc
    refine Finset.mem_sdiff.mpr ⟨hs hc,?_⟩
    intro hcov
    obtain ⟨q,hq,hcq⟩ := Finset.mem_biUnion.mp hcov
    exact Finset.disjoint_left.mp (hd q hq) hc hcq
  · intro h
    refine ⟨fun c hc => (Finset.mem_sdiff.mp (h hc)).1,?_⟩
    intro q hq
    apply Finset.disjoint_left.mpr
    intro c hc hcq
    exact (Finset.mem_sdiff.mp (h hc)).2 (Finset.mem_biUnion.mpr ⟨q,hq,hcq⟩)

theorem fitsBits_polyBitTime (a : Label) : PolyBitTime (fitsBits a) :=
  StandardBitGridStencil.fits_polyBitTime (offsets a)

theorem fits_frame (side : List Bool) (done : Done) (x y : Nat) (a : Label) :
    StandardBitGridStencil.fits (offsets a) (frame side done x y)=true ↔
      Fits (value side) done (placeAt ((x : Int),(y : Int)) a) := by
  simp only [StandardBitGridStencil.fits,List.all_eq_true,free_frame]
  rw [fits_iff_uncovered]
  constructor
  · intro h c hc
    obtain ⟨d,hd,he⟩ := (cells_offsets a x y c).mp hc
    exact he ▸ h d hd
  · intro h d hd
    exact h ((cells_offsets a x y (point x y d)).mpr ⟨d,hd,rfl⟩)

theorem fixed_shape_stencil_fits_spec :
    (∀ a : Label,PolyBitTime (fitsBits a)) ∧
    (∀ side done x y a,StandardBitGridStencil.fits (offsets a) (frame side done x y)=true ↔
      Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) :=
  ⟨fitsBits_polyBitTime,fits_frame⟩

end
end PakFixedPolyomino.PakFixedShapeStencilFitsAlignment
