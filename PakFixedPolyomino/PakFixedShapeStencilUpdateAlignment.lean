import PakFixedPolyomino.PakFixedShapeStencilFitsAlignment

/-! Actual stencil marking agrees with insertion of the SAME original
translated shape placement. Validation supplies geometric Fits, and every
literal mask cell then matches the original covered/uncovered definition.
No runtime/count/bijection certificate is assumed; the ordinary physical
compiler was proved for every raw frame in StandardBitGridStencil. -/
namespace PakFixedPolyomino.PakFixedShapeStencilUpdateAlignment
noncomputable section
open StandardBitTime StandardBitWordVector
open PakFixedWeightedStandardBinaryCount (value)
open PakFixedWeightedShapeFamily TilingAnchoredChoices PakFixedShapeChoiceWords
open PakFixedShapeOccupancyScan (mask mask_length)
open PakFixedShapeStencilCellAlignment (frame field_frame point rowIndex rowIndex_cell mask_rowIndex index_frame)
open PakFixedShapeStencilFitsAlignment (offsets cells_offsets)
open StandardBitGridStencil (maskMap update)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def cellAt (n k : Nat) : Cell := (((k%n : Nat) : Int),((k/n : Nat) : Int))

theorem cellAt_square (n k : Nat) (hk : k<n^2) : cellAt n k∈square n := by
  have hn : 0<n := by
    by_contra h
    have hz : n=0 := by omega
    subst n
    simp at hk
  have hx := Nat.mod_lt k hn
  have hy := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [pow_two] using hk)
  exact ofNat_pair_mem_square.mpr ⟨hx,hy⟩

theorem rowIndex_cellAt (n k : Nat) : rowIndex n (cellAt n k)=k := by
  simp only [rowIndex,cellAt,Int.toNat_natCast]
  rw [Nat.mul_comm,Nat.add_comm]
  exact Nat.mod_add_div k n

theorem maskMap_get (ds : List Cell) (raw : List Bool) (k : Nat)
    (hk : k<(field 1 raw).length) : (maskMap ds raw)[k]?=
      if ds.any (fun d => decide (value (StandardBitGridCell.indexBits d.1 d.2 raw)=k))
      then some true else (field 1 raw)[k]? := by
  induction ds with
  | nil => simp only [maskMap,List.any_nil,Bool.false_eq_true,if_false]
  | cons d ds ih =>
    by_cases he : value (StandardBitGridCell.indexBits d.1 d.2 raw)=k
    · rw [maskMap,he,List.getElem?_set_self (by rw [StandardBitGridStencil.maskMap_length];exact hk)]
      simp only [List.any_cons,he,decide_true,Bool.true_or,if_true]
    · rw [maskMap,List.getElem?_set_ne he,ih]
      simp only [List.any_cons,he,decide_false,Bool.false_or]

theorem indices_iff_cells (side : List Bool) (done : Done) (x y k : Nat) (a : Label)
    (hf : Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) (hk : k<(value side)^2) :
    (offsets a).any (fun d => decide (value (StandardBitGridCell.indexBits d.1 d.2 (frame side done x y))=k))=true ↔
      cellAt (value side) k∈Placement.cells shapeSupport (placeAt ((x : Int),(y : Int)) a) := by
  simp only [List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨d,hd,he⟩
    have hp : point x y d∈Placement.cells shapeSupport (placeAt ((x : Int),(y : Int)) a) :=
      (cells_offsets a x y (point x y d)).mpr ⟨d,hd,rfl⟩
    have hs := rowIndex_cell (value side) (point x y d) (hf.1 hp)
    rw [index_frame] at he
    rw [he] at hs
    have hc := PakFixedShapeGridCoordinates.scan_cell (value side) k hk
    have hpEq : point x y d=cellAt (value side) k := Option.some.inj (hs.symm.trans hc)
    exact hpEq ▸ hp
  · intro hc
    obtain ⟨d,hd,he⟩ := (cells_offsets a x y (cellAt (value side) k)).mp hc
    refine ⟨d,hd,?_⟩
    rw [index_frame,he,rowIndex_cellAt]

theorem covered_insert (done : Done) (p : Placement Shape) :
    covered shapeSupport (insert p done)=Placement.cells shapeSupport p∪covered shapeSupport done := by
  simp only [covered,Finset.biUnion_insert]

theorem maskMap_original (side : List Bool) (done : Done) (x y : Nat) (a : Label)
    (hf : Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) :
    maskMap (offsets a) (frame side done x y)=
      mask (value side) (insert (placeAt ((x : Int),(y : Int)) a) done) := by
  have hfield : field 1 (frame side done x y)=mask (value side) done := by
    simp only [field_frame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  have hlen : (maskMap (offsets a) (frame side done x y)).length=(value side)^2 := by
    rw [StandardBitGridStencil.maskMap_length,hfield,mask_length]
  apply List.ext_getElem?
  intro k
  by_cases hk : k<(value side)^2
  · have hc := cellAt_square (value side) k hk
    have hOld := mask_rowIndex (value side) done (cellAt (value side) k) hc
    have hNew := mask_rowIndex (value side) (insert (placeAt ((x : Int),(y : Int)) a) done) (cellAt (value side) k) hc
    rw [rowIndex_cellAt] at hOld hNew
    have hget := maskMap_get (offsets a) (frame side done x y) k (by rw [hfield,mask_length];exact hk)
    rw [hfield] at hget
    rw [hget,hOld,hNew]
    by_cases hp : cellAt (value side) k∈Placement.cells shapeSupport (placeAt ((x : Int),(y : Int)) a)
    · have ha := (indices_iff_cells side done x y k a hf hk).mpr hp
      have hn : cellAt (value side) k∈covered shapeSupport (insert (placeAt ((x : Int),(y : Int)) a) done) := by
        rw [covered_insert];exact Finset.mem_union.mpr (Or.inl hp)
      simp only [ha,if_true,hn,decide_true]
    · have ha : (offsets a).any (fun d => decide (value (StandardBitGridCell.indexBits d.1 d.2 (frame side done x y))=k))=false :=
        Bool.eq_false_iff.mpr (fun h => hp ((indices_iff_cells side done x y k a hf hk).mp h))
      have hn : (cellAt (value side) k∈covered shapeSupport (insert (placeAt ((x : Int),(y : Int)) a) done)) ↔
          cellAt (value side) k∈covered shapeSupport done := by
        rw [covered_insert,Finset.mem_union];exact or_iff_right hp
      simp only [ha,Bool.false_eq_true,if_false]
      by_cases ho : cellAt (value side) k∈covered shapeSupport done
      · simp only [ho,hn.mpr ho,decide_true]
      · have hno : cellAt (value side) k∉covered shapeSupport (insert (placeAt ((x : Int),(y : Int)) a) done) :=
          fun h => ho (hn.mp h)
        simp only [ho,hno,decide_false]
  · rw [List.getElem?_eq_none (by rw [hlen];omega),List.getElem?_eq_none (by rw [mask_length];omega)]

theorem update_frame (side : List Bool) (done : Done) (x y : Nat) (a : Label)
    (hf : Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) :
    update (offsets a) (frame side done x y)=frame side (insert (placeAt ((x : Int),(y : Int)) a) done) x y := by
  rw [StandardBitGridStencil.output_frame,maskMap_original side done x y a hf]
  simp only [field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl

theorem fixed_shape_stencil_update_spec :
    (∀ a : Label,PolyBitTime (update (offsets a))) ∧
    (∀ (side : List Bool) (done : Done) (x y : Nat) (a : Label),
      Fits (value side) done (placeAt ((x : Int),(y : Int)) a) →
      update (offsets a) (frame side done x y)=frame side (insert (placeAt ((x : Int),(y : Int)) a) done) x y) :=
  ⟨fun a => StandardBitGridStencil.update_polyBitTime (offsets a),update_frame⟩

end
end PakFixedPolyomino.PakFixedShapeStencilUpdateAlignment
