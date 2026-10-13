import PakFixedPolyomino.PakFixedShapeStencilUpdateAlignment
import PakFixedPolyomino.StandardBitFiniteChoicePrefix

/-! ONE fixed original shape-anchor inventory is selected by its literal
unary-prefix label code. Actual ordinary tape-time tag decoding, comparisons,
finite conditional control, stencil validation/marking and state projection
are supplied internally. Invalid placements/indices emit false for rejection;
valid placements emit true and the exact original [side,updated mask] state.
This is the deterministic continuation; the ND feedback loop is separate. -/
namespace PakFixedPolyomino.PakFixedShapeFiniteLabelRound
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (encode field field_polyBitTime)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open PakFixedWeightedShapeFamily TilingAnchoredChoices PakFixedShapeChoiceWords
open PakFixedShapeStencilCellAlignment (frame field_frame)
open PakFixedShapeStencilFitsAlignment (offsets)
open StandardBitFiniteChoicePrefix (labelCode)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def L : Nat := Fintype.card Label
def labelAt (i : Fin L) : Label := (Fintype.equivFin Label).symm i
def labels : List Label := List.ofFn labelAt
def tagValue (raw : List Bool) : Nat := StandardBitFirstZero.index (firstBits raw)
def tagBits (raw : List Bool) : List Bool := encodeNat (tagValue raw)
def returnState (raw : List Bool) : List Bool := encode [field 0 raw,field 1 raw]
def checkedRound (a : Label) (raw : List Bool) : List Bool :=
  if StandardBitGridStencil.fits (offsets a) raw then
    true::returnState (StandardBitGridStencil.update (offsets a) raw) else [false]
def select : List Label → Nat → List Bool → List Bool
  | [],_,_ => [false]
  | a::as,k,raw => if tagValue raw=k then checkedRound a (secondBits raw) else select as (k+1) raw
def round (raw : List Bool) : List Bool := select labels 0 raw

theorem labels_length : labels.length=L := List.length_ofFn
theorem labelAt_bijective : Function.Bijective labelAt := (Fintype.equivFin Label).symm.bijective
theorem labels_get (i : Fin L) : labels[i.val]?=some (labelAt i) := by
  simp [labels,List.getElem?_ofFn,i.isLt]

theorem firstZero_eq_firstFalse (w : List Bool) :
    StandardBitFirstZero.index w=StandardBitFiniteChoicePrefix.firstFalseIndex w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [StandardBitFirstZero.index,StandardBitFiniteChoicePrefix.firstFalseIndex,ih]

theorem tagValue_code (K : Nat) (i : Fin K) (raw : List Bool) :
    tagValue (pairBits (labelCode K i) raw)=i.val := by
  rw [tagValue,firstBits_pair,firstZero_eq_firstFalse,StandardBitFiniteChoicePrefix.firstFalseIndex_labelCode]

theorem tagBits_polyBitTime : PolyBitTime tagBits := by
  have h := polyBitTime_comp (polyBitTime_comp first_polyBitTime StandardBitFirstZero.firstZero_polyBitTime) first_polyBitTime
  have he : firstBits ∘ (StandardBitFirstZero.firstZeroBits ∘ firstBits)=tagBits := by
    funext raw;simp only [Function.comp_apply,StandardBitFirstZero.firstZeroBits,firstBits_pair,tagBits,tagValue]
  rwa [he] at h

theorem tagEq_polyBitTime (k : Nat) : PolyBitTime (fun raw => [decide (tagValue raw=k)]) := by
  have hl : PolyBitTime (fun raw => [decide (tagValue raw<k+1)]) := by
    simpa only [Function.comp_def,tagBits,value_encode_nat] using
      polyBitTime_comp tagBits_polyBitTime (StandardBitSignedOffset.fixed_lt_polyBitTime (k+1))
  have hg : PolyBitTime (fun raw => [decide (k≤tagValue raw)]) := by
    simpa only [Function.comp_def,tagBits,value_encode_nat] using
      polyBitTime_comp tagBits_polyBitTime (StandardBitSignedOffset.fixed_le_polyBitTime k)
  have h := StandardBitBooleanMaps.and_polyBitTime _ _ hl hg
  have he : (fun raw => [decide (tagValue raw<k+1) && decide (k≤tagValue raw)])=
      (fun raw => [decide (tagValue raw=k)]) := by
    funext raw
    by_cases hEq : tagValue raw=k
    · simp [hEq]
    · by_cases hlt : tagValue raw<k+1
      · have hn : ¬k≤tagValue raw := by omega
        simp [hEq,hlt,hn]
      · simp [hEq,hlt]
  rwa [he] at h

theorem returnState_polyBitTime : PolyBitTime returnState :=
  StandardBitWordVector.assemble_polyBitTime [field 0,field 1]
    (by intro f hf;simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl
        · exact field_polyBitTime 0
        · exact field_polyBitTime 1)

theorem checkedRound_polyBitTime (a : Label) : PolyBitTime (checkedRound a) := by
  have hc := polyBitTime_comp (StandardBitGridStencil.update_polyBitTime (offsets a)) returnState_polyBitTime
  have ht := polyBitTime_comp hc (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitGridStencil.fits (offsets a) raw) _ _
    (StandardBitGridStencil.fits_polyBitTime (offsets a))
    (StandardBitBooleanMaps.constant_bool_polyBitTime false) ht

theorem select_polyBitTime (as : List Label) (k : Nat) : PolyBitTime (select as k) := by
  induction as generalizing k with
  | nil => exact StandardBitBooleanMaps.constant_bool_polyBitTime false
  | cons a as ih =>
    have hf := polyBitTime_comp secondBits_polyBitTime (checkedRound_polyBitTime a)
    have h := StandardBitConditionalBitTime.conditional_polyBitTime
      (fun raw => decide (tagValue raw=k)) (select as (k+1)) (checkedRound a ∘ secondBits)
      (tagEq_polyBitTime k) (ih (k+1)) hf
    have he : StandardBitProtectedConditional.conditional (fun raw => decide (tagValue raw=k))
        (select as (k+1)) (checkedRound a ∘ secondBits)=select (a::as) k := by
      funext raw;simp only [StandardBitProtectedConditional.conditional,select,decide_eq_true_eq,Function.comp_apply]
    rwa [he] at h

theorem round_polyBitTime : PolyBitTime round := select_polyBitTime labels 0

theorem select_lookup (as : List Label) (k : Nat) (raw : List Bool) (i : Nat) (a : Label)
    (ha : as[i]?=some a) (hi : tagValue raw=k+i) :
    select as k raw=checkedRound a (secondBits raw) := by
  induction as generalizing k i with
  | nil => simp only [List.getElem?_nil] at ha;contradiction
  | cons b as ih =>
    cases i with
    | zero =>
      have he : b=a := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using ha
      subst b
      simp only [select,hi,Nat.add_zero,if_true]
    | succ i =>
      have ha' : as[i]?=some a := by simpa only [List.getElem?_cons_succ] using ha
      have hn : tagValue raw≠k := by omega
      rw [select,if_neg hn]
      exact ih (k+1) i ha' (by omega)

theorem round_code (i : Fin L) (raw : List Bool) :
    round (pairBits (labelCode L i) raw)=checkedRound (labelAt i) raw := by
  rw [round,select_lookup labels 0 _ i.val (labelAt i) (labels_get i)
    (by rw [tagValue_code];omega),secondBits_pair]

theorem checked_frame_valid (side : List Bool) (done : Done) (x y : Nat) (a : Label)
    (hf : Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) :
    checkedRound a (frame side done x y)=true::encode
      [side,PakFixedShapeOccupancyScan.mask (value side) (insert (placeAt ((x : Int),(y : Int)) a) done)] := by
  rw [checkedRound,(PakFixedShapeStencilFitsAlignment.fits_frame side done x y a).mpr hf,if_pos rfl,
    PakFixedShapeStencilUpdateAlignment.update_frame side done x y a hf]
  simp only [returnState,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem checked_frame_invalid (side : List Bool) (done : Done) (x y : Nat) (a : Label)
    (hf : ¬Fits (value side) done (placeAt ((x : Int),(y : Int)) a)) :
    checkedRound a (frame side done x y)=[false] := by
  have hb : StandardBitGridStencil.fits (offsets a) (frame side done x y)=false :=
    Bool.eq_false_iff.mpr (fun h => hf ((PakFixedShapeStencilFitsAlignment.fits_frame side done x y a).mp h))
  simp only [checkedRound,hb,Bool.false_eq_true,if_false]

theorem fixed_shape_finite_label_round_spec : PolyBitTime round ∧ Function.Bijective labelAt ∧
    (∀ (i : Fin L) raw,round (pairBits (labelCode L i) raw)=checkedRound (labelAt i) raw) ∧
    (∀ (side : List Bool) (done : Done) (x y : Nat) (i : Fin L),
      Fits (value side) done (placeAt ((x : Int),(y : Int)) (labelAt i)) →
      round (pairBits (labelCode L i) (frame side done x y))=true::encode
        [side,PakFixedShapeOccupancyScan.mask (value side)
          (insert (placeAt ((x : Int),(y : Int)) (labelAt i)) done)]) := by
  refine ⟨round_polyBitTime,labelAt_bijective,round_code,?_⟩
  intro side done x y i hf
  rw [round_code]
  exact checked_frame_valid side done x y (labelAt i) hf

end
end PakFixedPolyomino.PakFixedShapeFiniteLabelRound
