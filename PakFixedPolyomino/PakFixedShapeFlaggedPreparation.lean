import PakFixedPolyomino.PakFixedShapeFiniteLabelRound
import PakFixedPolyomino.PakFixedShapeOccupancyAnchorSetup

/-! Ordinary physical preparation for the ORIGINAL occupancy algorithm.
The first literal output bit is true exactly when another uncovered cell
exists; its tail is [ORIGINALside,ORIGINALmask,canonical x,canonical y].
An exhausted/empty square emits false before any nondeterministic choice.
Every raw helper input has a polynomial actual tape-time implementation. -/
set_option maxHeartbeats 800000
namespace PakFixedPolyomino.PakFixedShapeFlaggedPreparation
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (encode field field_polyBitTime field_encode)
open StandardBitPairFirstCompaction (firstBits firstBits_pair)
open StandardBitPairProjection (secondBits secondBits_pair)
open PakFixedWeightedShapeFamily TilingAnchoredChoices PakFixedShapeChoiceWords
open PakFixedShapeOccupancyScan (mask mask_length)
open StandardBitFirstZero (index)
open PakFixedShapeOccupancyAnchorSetup (presence anchorFrame)

def state (side : List Bool) (done : Done) : List Bool := encode [side,mask (value side) done]
def prepare (raw : List Bool) : List Bool := (presence raw).headD false::anchorFrame raw

theorem prepare_polyBitTime : PolyBitTime prepare := by
  have hb := polyBitTime_comp PakFixedShapeOccupancyAnchorSetup.presence_polyBitTime StandardBitHead.head_polyBitTime
  have hf := polyBitTime_comp PakFixedShapeOccupancyAnchorSetup.anchorFrame_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  have ht := polyBitTime_comp PakFixedShapeOccupancyAnchorSetup.anchorFrame_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have h := StandardBitConditionalBitTime.conditional_polyBitTime (fun raw => (presence raw).headD false) _ _ hb hf ht
  have he : StandardBitProtectedConditional.conditional (fun raw => (presence raw).headD false)
      (List.cons false ∘ anchorFrame) (List.cons true ∘ anchorFrame)=prepare := by
    funext raw
    change (if (presence raw).headD false then true::anchorFrame raw else false::anchorFrame raw)=
      (presence raw).headD false::anchorFrame raw
    cases (presence raw).headD false <;> rfl
  rwa [he] at h

theorem prepare_original (side : List Bool) (done : Done) :
    prepare (state side done)=decide (index (mask (value side) done)<(value side)^2)::
      PakFixedShapeStencilCellAlignment.frame side done
        (index (mask (value side) done)%value side) (index (mask (value side) done)/value side) := by
  simp only [prepare,presence,PakFixedShapeOccupancyAnchorSetup.scan,
    StandardBitFirstZero.firstZeroBits,secondBits_pair,List.headD_cons,anchorFrame,
    PakFixedShapeOccupancyAnchorSetup.xBits,PakFixedShapeOccupancyAnchorSetup.yBits,
    PakFixedShapeOccupancyAnchorSetup.quotientInput,PakFixedShapeOccupancyAnchorSetup.indexBits,
    StandardBitVariableDivideLoop.moduloBits,StandardBitVariableDivideLoop.divideBits,
    firstBits_pair,secondBits_pair,value_encode_nat,state,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,mask_length,PakFixedShapeStencilCellAlignment.frame]

theorem stops_iff (side : List Bool) (done : Done) :
    (prepare (state side done)).headD false=false ↔
      PakFixedShapeFirstUncovered.firstUncovered (value side) done=none := by
  rw [prepare_original,List.headD_cons,PakFixedShapeFirstUncovered.first_none_iff]
  have hle := StandardBitFirstZero.index_le (mask (value side) done)
  rw [mask_length] at hle
  have he : decide (index (mask (value side) done)<(value side)^2)=false ↔
      index (mask (value side) done)=(mask (value side) done).length := by
    simp only [decide_eq_false_iff_not,mask_length]
    omega
  rw [he,PakFixedShapeOccupancyScan.exhausted_iff]

theorem original_coordinate (side : List Bool) (done : Done)
    (h : (prepare (state side done)).headD false=true) :
    PakFixedShapeFirstUncovered.firstUncovered (value side) done=some
      (((index (mask (value side) done)%value side : Nat) : Int),
       ((index (mask (value side) done)/value side : Nat) : Int)) := by
  rw [prepare_original,List.headD_cons,decide_eq_true_eq] at h
  exact PakFixedShapeGridCoordinates.first_uncovered_coordinate (value side) done h

theorem zero_stops (side : List Bool) (h : value side=0) (done : Done) :
    (prepare (state side done)).headD false=false :=
  (stops_iff side done).mpr (by rw [h];exact PakFixedShapeFirstUncovered.zero_first_none done)

theorem flagged_preparation_spec : PolyBitTime prepare ∧
    (∀ side done,(prepare (state side done)).headD false=false ↔
      PakFixedShapeFirstUncovered.firstUncovered (value side) done=none) ∧
    (∀ side done,(prepare (state side done)).headD false=true →
      PakFixedShapeFirstUncovered.firstUncovered (value side) done=some
        (((index (mask (value side) done)%value side : Nat) : Int),
         ((index (mask (value side) done)/value side : Nat) : Int))) :=
  ⟨prepare_polyBitTime,stops_iff,original_coordinate⟩

end
end PakFixedPolyomino.PakFixedShapeFlaggedPreparation
