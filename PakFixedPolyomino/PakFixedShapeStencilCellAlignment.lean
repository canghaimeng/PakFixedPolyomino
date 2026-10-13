import PakFixedPolyomino.StandardBitGridStencil
import PakFixedPolyomino.PakFixedShapeGridCoordinates

/-! Exact alignment of the actual signed cell checker with the ORIGINAL
uncovered set for the SAME fixed physical shape family. Raw side words retain
all literal high zeros. Signed offsets below zero and outside the unmodified
square fail the checker. Physical tape-time is already proved in GridCell;
these are the geometric/index equalities needed to instantiate its stencil. -/
namespace PakFixedPolyomino.PakFixedShapeStencilCellAlignment
noncomputable section
open Computability StandardBitMetric StandardBitWordVector
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakFixedWeightedShapeFamily TilingAnchoredChoices
open PakFixedShapeOccupancyScan (mask)
open PakFixedShapeFirstUncovered (scanCells)

def frame (side : List Bool) (done : Finset (Placement Shape)) (x y : Nat) : List Bool :=
  encode [side,mask (value side) done,encodeNat x,encodeNat y]
def point (x y : Nat) (d : Cell) : Cell := ((x : Int)+d.1,(y : Int)+d.2)
def rowIndex (n : Nat) (c : Cell) : Nat := c.2.toNat*n+c.1.toNat

theorem field_frame (k : Nat) (side : List Bool) (done : Finset (Placement Shape)) (x y : Nat) :
    field k (frame side done x y)=([side,mask (value side) done,encodeNat x,encodeNat y][k]?).getD [] :=
  field_encode _ _

theorem square_iff (n : Nat) (c : Cell) : c∈square n ↔
    0≤c.1 ∧ 0≤c.2 ∧ c.1<(n : Int) ∧ c.2<(n : Int) := by
  constructor
  · intro h
    have hb := mem_square_coord_bounds h
    exact ⟨hb.1,hb.2.2.1,hb.2.1,hb.2.2.2⟩
  · rintro ⟨hx,hy,hxl,hyl⟩
    have hx' : c.1.toNat<n := by omega
    have hy' : c.2.toNat<n := by omega
    have h := (ofNat_pair_mem_square).mpr ⟨hx',hy'⟩
    simpa only [Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy] using h

theorem rowIndex_lt (n : Nat) (c : Cell) (hc : c∈square n) : rowIndex n c<n^2 := by
  have hb := mem_square_coord_bounds hc
  have hx : c.1.toNat<n := by omega
  have hy : c.2.toNat+1≤n := by omega
  have hm := Nat.mul_le_mul_right n hy
  simp only [Nat.add_mul,Nat.one_mul] at hm
  simp only [rowIndex,pow_two]
  omega

theorem rowIndex_cell (n : Nat) (c : Cell) (hc : c∈square n) :
    (scanCells n)[rowIndex n c]?=some c := by
  have hb := mem_square_coord_bounds hc
  have hx : c.1.toNat<n := by omega
  have hn : 0<n := by omega
  have hm : rowIndex n c%n=c.1.toNat := by
    simp [rowIndex,Nat.add_mod,Nat.mod_eq_of_lt hx]
  have hd : rowIndex n c/n=c.2.toNat := by
    rw [rowIndex,Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hx]
    omega
  rw [PakFixedShapeGridCoordinates.scan_cell n _ (rowIndex_lt n c hc),hm,hd]
  simp only [Int.toNat_of_nonneg hb.1,Int.toNat_of_nonneg hb.2.2.1]

theorem mask_rowIndex (n : Nat) (done : Finset (Placement Shape)) (c : Cell) (hc : c∈square n) :
    (mask n done)[rowIndex n c]?=some (decide (c∈covered shapeSupport done)) := by
  rw [PakFixedShapeOccupancyScan.mask_covered,List.getElem?_map,rowIndex_cell n c hc]
  rfl

theorem index_frame (side : List Bool) (done : Finset (Placement Shape)) (x y : Nat) (d : Cell) :
    value (StandardBitGridCell.indexBits d.1 d.2 (frame side done x y))=
      rowIndex (value side) (point x y d) := by
  rw [StandardBitGridCell.index_value]
  simp only [field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_encode_nat,rowIndex,point]

theorem inside_frame (side : List Bool) (done : Finset (Placement Shape)) (x y : Nat) (d : Cell) :
    StandardBitGridCell.inside d.1 d.2 (frame side done x y)=true ↔ point x y d∈square (value side) := by
  rw [StandardBitGridCell.inside_iff,square_iff]
  simp only [field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_encode_nat,point]

theorem free_frame (side : List Bool) (done : Finset (Placement Shape)) (x y : Nat) (d : Cell) :
    StandardBitGridCell.free d.1 d.2 (frame side done x y)=true ↔
      point x y d∈uncovered shapeSupport (square (value side)) done := by
  by_cases hc : point x y d∈square (value side)
  · have hi := (inside_frame side done x y d).mpr hc
    simp only [StandardBitGridCell.free,hi,Bool.true_and,decide_eq_true_eq,index_frame,
      field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    rw [mask_rowIndex (value side) done (point x y d) hc]
    simp only [Option.some.injEq,decide_eq_false_iff_not,uncovered,Finset.mem_sdiff]
    tauto
  · have hi : StandardBitGridCell.inside d.1 d.2 (frame side done x y)=false :=
      Bool.eq_false_iff.mpr (fun h => hc ((inside_frame side done x y d).mp h))
    have hu : point x y d∉uncovered shapeSupport (square (value side)) done := by
      intro h;exact hc (Finset.mem_sdiff.mp h).1
    simp only [StandardBitGridCell.free,hi,Bool.false_and,Bool.false_eq_true,hu]

theorem stencil_cell_alignment_spec :
    (∀ n c,c∈square n → (scanCells n)[rowIndex n c]?=some c) ∧
    (∀ side done x y d,StandardBitGridCell.free d.1 d.2 (frame side done x y)=true ↔
      point x y d∈uncovered shapeSupport (square (value side)) done) :=
  ⟨rowIndex_cell,free_frame⟩

end
end PakFixedPolyomino.PakFixedShapeStencilCellAlignment
