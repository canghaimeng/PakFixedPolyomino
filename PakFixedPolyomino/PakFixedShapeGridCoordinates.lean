import PakFixedPolyomino.PakFixedShapeOccupancyScan

/-! Exact zero-based row-major coordinate decoding of the original square
scan. Position k maps to (k%n,k/n), with empty-square cases explicit through
the bound k<n^2. These are geometric/index equalities; physical variable
division is supplied separately by the ordinary div/mod transducer. -/
namespace PakFixedPolyomino.PakFixedShapeGridCoordinates
open PakFixedShapeFirstUncovered
open PakFixedShapeOccupancyScan (mask)
open StandardBitFirstZero (index)

def rows (n : Nat) (ys : List Nat) : List Cell :=
  ys.flatMap (fun (y : Nat) => (List.range n).map (fun (x : Nat) => ((x : Int),(y : Int))))

theorem rows_length (n : Nat) (ys : List Nat) : (rows n ys).length=ys.length*n := by
  simp [rows,List.length_flatMap]

theorem row_get (n y k : Nat) (hk : k<n) :
    ((List.range n).map (fun (x : Nat) => ((x : Int),(y : Int))))[k]?=some ((k : Int),(y : Int)) := by
  rw [List.getElem?_map,List.getElem?_range hk]
  rfl

theorem rows_get (n : Nat) (ys : List Nat) (k : Nat) (hn : 0<n) (hk : k<ys.length*n) :
    (rows n ys)[k]?=(ys[k/n]?).map (fun (y : Nat) => (((k%n : Nat) : Int),(y : Int))) := by
  induction ys generalizing k with
  | nil => simp only [List.length_nil,Nat.zero_mul] at hk;omega
  | cons y ys ih =>
    simp only [rows,List.flatMap_cons]
    by_cases h : k<n
    · rw [List.getElem?_append_left (by simpa using h),row_get n y k h]
      simp only [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h,List.getElem?_cons_zero,Option.map_some]
    · have hkn : n≤k := by omega
      have hb : k-n<ys.length*n := by
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hk
        omega
      have he : k=n+(k-n) := by omega
      have hd : k/n=(k-n)/n+1 := by
        calc
          k/n=(n+(k-n))/n := by rw [← he]
          _=(k-n)/n+1 := by rw [Nat.add_div_left _ hn]
      have hm : k%n=(k-n)%n := by rw [he,Nat.add_mod];simp
      rw [List.getElem?_append_right (by simpa using hkn)]
      simp only [List.length_map,List.length_range]
      change (rows n ys)[k-n]?=(y::ys)[k/n]?.map (fun (y : Nat) => (((k%n : Nat) : Int),(y : Int)))
      rw [ih (k-n) hb,hd,List.getElem?_cons_succ,hm]

theorem scan_cell (n k : Nat) (hk : k<n^2) :
    (scanCells n)[k]?=some (((k%n : Nat) : Int),((k/n : Nat) : Int)) := by
  have hn : 0<n := by
    by_contra h
    have hz : n=0 := by omega
    subst n
    simp at hk
  have hd : k/n<n := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [pow_two] using hk)
  change (rows n (List.range n))[k]?=some _
  rw [rows_get n (List.range n) k hn (by simpa only [List.length_range,pow_two] using hk),
    List.getElem?_range hd]
  rfl

theorem first_uncovered_coordinate (n : Nat)
    (done : Finset (Placement PakFixedWeightedShapeFamily.Shape))
    (h : index (mask n done)<n^2) :
    firstUncovered n done=some
      (((index (mask n done)%n : Nat) : Int),((index (mask n done)/n : Nat) : Int)) := by
  rw [← PakFixedShapeOccupancyScan.first_index_cell]
  exact scan_cell n _ h

theorem grid_coordinates_spec :
    (∀ n k,k<n^2 → (scanCells n)[k]?=some (((k%n : Nat) : Int),((k/n : Nat) : Int))) ∧
    (∀ n done,index (mask n done)<n^2 → firstUncovered n done=some
      (((index (mask n done)%n : Nat) : Int),((index (mask n done)/n : Nat) : Int))) :=
  ⟨scan_cell,first_uncovered_coordinate⟩

end PakFixedPolyomino.PakFixedShapeGridCoordinates
