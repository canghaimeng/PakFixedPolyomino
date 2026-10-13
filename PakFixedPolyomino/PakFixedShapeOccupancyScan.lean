import PakFixedPolyomino.StandardBitFirstZero
import PakFixedPolyomino.PakFixedShapeFirstUncovered

/-! Exact alignment of the physical first-zero occupancy scan with the
ORIGINAL row-major firstUncovered algorithm for the fixed shape family.
The mask records covered cells by true and uncovered cells by false. Its
index identifies the same first cell and exhaustion the same empty uncovered
set. Constructing/updating the mask and coordinate conversion are separate. -/
namespace PakFixedPolyomino.PakFixedShapeOccupancyScan
noncomputable section
open StandardBitTime TilingAnchoredChoices PakFixedWeightedShapeFamily
open PakFixedShapeFirstUncovered
open StandardBitFirstZero (index firstZeroBits)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def mask (n : Nat) (done : Finset (Placement Shape)) : List Bool :=
  (scanCells n).map (fun c => !decide (c ∈ uncovered shapeSupport (square n) done))

theorem mask_index_findIdx {α : Type} (xs : List α) (p : α → Bool) :
    index (xs.map (fun a => !p a))=xs.findIdx p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p a <;> simp [List.findIdx_cons,index,h,ih]

theorem mask_index_find {α : Type} (xs : List α) (p : α → Bool) :
    xs[index (xs.map (fun a => !p a))]?=xs.find? p := by
  rw [mask_index_findIdx]
  exact List.find?_eq_getElem?_findIdx.symm

theorem scan_length (n : Nat) : (scanCells n).length=n^2 := by
  simp [scanCells,List.length_flatMap,pow_two]

theorem mask_length (n : Nat) (done : Finset (Placement Shape)) :
    (mask n done).length=n^2 := by simp only [mask,List.length_map,scan_length]

theorem mask_covered (n : Nat) (done : Finset (Placement Shape)) :
    mask n done=(scanCells n).map (fun c => decide (c ∈ covered shapeSupport done)) := by
  apply List.map_congr_left
  intro c hc
  have hi := (mem_scanCells n c).mp hc
  simp [uncovered,Finset.mem_sdiff,hi]

theorem first_index_cell (n : Nat) (done : Finset (Placement Shape)) :
    (scanCells n)[index (mask n done)]?=firstUncovered n done :=
  mask_index_find (scanCells n) (fun c => decide (c ∈ uncovered shapeSupport (square n) done))

theorem exhausted_iff (n : Nat) (done : Finset (Placement Shape)) :
    index (mask n done)=(mask n done).length ↔
      uncovered shapeSupport (square n) done=∅ := by
  rw [← first_none_iff,← first_index_cell,List.getElem?_eq_none_iff]
  have hi := StandardBitFirstZero.index_le (mask n done)
  have hl : (mask n done).length=(scanCells n).length := by simp only [mask,List.length_map]
  omega

theorem physical_scan_polyBitTime : PolyBitTime firstZeroBits :=
  StandardBitFirstZero.firstZero_polyBitTime

theorem occupancy_scan_spec :
    PolyBitTime firstZeroBits ∧
    (∀ n done,(mask n done).length=n^2) ∧
    (∀ n done,mask n done=(scanCells n).map (fun c => decide (c ∈ covered shapeSupport done))) ∧
    (∀ n done,(scanCells n)[index (mask n done)]?=firstUncovered n done) ∧
    (∀ n done,index (mask n done)=(mask n done).length ↔
      uncovered shapeSupport (square n) done=∅) :=
  ⟨physical_scan_polyBitTime,mask_length,mask_covered,first_index_cell,exhausted_iff⟩

end
end PakFixedPolyomino.PakFixedShapeOccupancyScan
