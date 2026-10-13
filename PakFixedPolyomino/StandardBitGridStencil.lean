import PakFixedPolyomino.StandardBitGridCell

/-! A fixed finite stencil of integer offsets is actual finite program data.
All cells are validated against the ORIGINAL literal mask before any mark is
applied. The actual marking compiler retains the side and anchor fields, keeps
the mask length exactly, and emits a complete clean four-field frame. This
generic primitive does not instantiate the original shape-anchor inventory. -/
namespace PakFixedPolyomino.StandardBitGridStencil
noncomputable section
open StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value)
open StandardBitWordVector (field field_polyBitTime encode field_encode)
open StandardBitBooleanMaps StandardBitGridCell

def fits (offsets : List (Int×Int)) (raw : List Bool) : Bool :=
  offsets.all (fun d => free d.1 d.2 raw)
def normalizeFrame (raw : List Bool) : List Bool := encode [field 0 raw,field 1 raw,field 2 raw,field 3 raw]
def update : List (Int×Int) → List Bool → List Bool
  | [],raw => normalizeFrame raw
  | d::ds,raw => updatedFrame d.1 d.2 (update ds raw)
def maskMap : List (Int×Int) → List Bool → List Bool
  | [],raw => field 1 raw
  | d::ds,raw => (maskMap ds raw).set (value (indexBits d.1 d.2 raw)) true

theorem normalizeFrame_polyBitTime : PolyBitTime normalizeFrame :=
  StandardBitWordVector.assemble_polyBitTime [field 0,field 1,field 2,field 3]
    (by intro f hf; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl|rfl|rfl
        · exact field_polyBitTime 0
        · exact field_polyBitTime 1
        · exact field_polyBitTime 2
        · exact field_polyBitTime 3)

theorem fits_polyBitTime (offsets : List (Int×Int)) : PolyBitTime (fun raw => [fits offsets raw]) := by
  induction offsets with
  | nil => exact constant_bool_polyBitTime true
  | cons d ds ih =>
    exact and_polyBitTime _ _ (free_polyBitTime d.1 d.2) ih

theorem update_polyBitTime (offsets : List (Int×Int)) : PolyBitTime (update offsets) := by
  induction offsets with
  | nil => exact normalizeFrame_polyBitTime
  | cons d ds ih => exact polyBitTime_comp ih (updatedFrame_polyBitTime d.1 d.2)

theorem field_normalizeFrame (k : Nat) (raw : List Bool) : field k (normalizeFrame raw)=
    ([field 0 raw,field 1 raw,field 2 raw,field 3 raw][k]?).getD [] := field_encode _ _

theorem field_updatedFrame (k : Nat) (dx dy : Int) (raw : List Bool) : field k (updatedFrame dx dy raw)=
    ([field 0 raw,markedMask dx dy raw,field 2 raw,field 3 raw][k]?).getD [] := field_encode _ _

theorem side_retained (offsets : List (Int×Int)) (raw : List Bool) : field 0 (update offsets raw)=field 0 raw := by
  induction offsets with
  | nil => simp only [update,field_normalizeFrame,List.getElem?_cons_zero,Option.getD_some]
  | cons d ds ih => simp only [update,field_updatedFrame,List.getElem?_cons_zero,Option.getD_some,ih]

theorem x_retained (offsets : List (Int×Int)) (raw : List Bool) : field 2 (update offsets raw)=field 2 raw := by
  induction offsets with
  | nil => simp only [update,field_normalizeFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  | cons d ds ih => simp only [update,field_updatedFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,ih]

theorem y_retained (offsets : List (Int×Int)) (raw : List Bool) : field 3 (update offsets raw)=field 3 raw := by
  induction offsets with
  | nil => simp only [update,field_normalizeFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  | cons d ds ih => simp only [update,field_updatedFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,ih]

theorem index_retained (offsets : List (Int×Int)) (dx dy : Int) (raw : List Bool) :
    indexBits dx dy (update offsets raw)=indexBits dx dy raw := by
  simp only [indexBits,rowProduct,shifted,side_retained,x_retained,y_retained]

theorem maskMap_length (offsets : List (Int×Int)) (raw : List Bool) :
    (maskMap offsets raw).length=(field 1 raw).length := by
  induction offsets with
  | nil => rfl
  | cons d ds ih => simp only [maskMap,List.length_set,ih]

theorem mask_updated (offsets : List (Int×Int)) (raw : List Bool) :
    field 1 (update offsets raw)=maskMap offsets raw := by
  induction offsets with
  | nil => simp only [update,field_normalizeFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,maskMap]
  | cons d ds ih =>
    simp only [update,field_updatedFrame,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
      markedMask,ih,index_retained,maskMap]

theorem output_frame (offsets : List (Int×Int)) (raw : List Bool) :
    update offsets raw=encode [field 0 raw,maskMap offsets raw,field 2 raw,field 3 raw] := by
  cases offsets with
  | nil => rfl
  | cons d ds =>
    simp only [update,updatedFrame,side_retained,x_retained,y_retained,markedMask,mask_updated,index_retained,maskMap]

theorem fits_iff (offsets : List (Int×Int)) (raw : List Bool) : fits offsets raw=true ↔
    ∀ d∈offsets,inside d.1 d.2 raw=true ∧
      (field 1 raw)[value (indexBits d.1 d.2 raw)]?=some false := by
  simp only [fits,List.all_eq_true,free,Bool.and_eq_true,decide_eq_true_eq]

theorem update_length (offsets : List (Int×Int)) (raw : List Bool) :
    (update offsets raw).length=(normalizeFrame raw).length := by
  rw [output_frame]
  simp only [normalizeFrame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,maskMap_length]

theorem grid_stencil_spec (offsets : List (Int×Int)) :
    PolyBitTime (fun raw => [fits offsets raw]) ∧ PolyBitTime (update offsets) ∧
    (∀ raw,update offsets raw=encode [field 0 raw,maskMap offsets raw,field 2 raw,field 3 raw]) ∧
    (∀ raw,(maskMap offsets raw).length=(field 1 raw).length) ∧
    (∀ raw,(update offsets raw).length=(normalizeFrame raw).length) ∧
    (∀ raw,fits offsets raw=true ↔ ∀ d∈offsets,inside d.1 d.2 raw=true ∧
      (field 1 raw)[value (indexBits d.1 d.2 raw)]?=some false) :=
  ⟨fits_polyBitTime offsets,update_polyBitTime offsets,output_frame offsets,maskMap_length offsets,
    update_length offsets,fits_iff offsets⟩

end
end PakFixedPolyomino.StandardBitGridStencil
