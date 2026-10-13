import PakFixedPolyomino.StandardBitGridCell
import PakFixedPolyomino.StandardBitVariableDivideLoop
import PakFixedPolyomino.PakFixedShapeGridCoordinates

/-! Actual polynomial tape-time inspector of [literal side,literal mask].
It preserves both fields, physically finds the first uncovered bit, computes
its x/y by ordinary variable division, and emits a presence flag plus the
four-field anchor frame. Exact alignment uses the ORIGINAL row-major scan.
Empty squares stop with false before a later nondeterministic choice. -/
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace PakFixedPolyomino.PakFixedShapeOccupancyAnchorSetup
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (encode field field_polyBitTime field_encode)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open StandardBitFirstZero (firstZeroBits index)
open PakFixedShapeOccupancyScan (mask)

def scan (raw : List Bool) : List Bool := firstZeroBits (field 1 raw)
def presence (raw : List Bool) : List Bool := secondBits (scan raw)
def indexBits (raw : List Bool) : List Bool := firstBits (scan raw)
def quotientInput (raw : List Bool) : List Bool := pairBits (indexBits raw) (field 0 raw)
def xBits (raw : List Bool) : List Bool := StandardBitVariableDivideLoop.moduloBits (quotientInput raw)
def yBits (raw : List Bool) : List Bool := StandardBitVariableDivideLoop.divideBits (quotientInput raw)
def anchorFrame (raw : List Bool) : List Bool := encode [field 0 raw,field 1 raw,xBits raw,yBits raw]
def prepare (raw : List Bool) : List Bool := pairBits (presence raw) (anchorFrame raw)

theorem scan_polyBitTime : PolyBitTime scan :=
  polyBitTime_comp (field_polyBitTime 1) StandardBitFirstZero.firstZero_polyBitTime
theorem presence_polyBitTime : PolyBitTime presence :=
  polyBitTime_comp scan_polyBitTime secondBits_polyBitTime
theorem index_polyBitTime : PolyBitTime indexBits :=
  polyBitTime_comp scan_polyBitTime first_polyBitTime
theorem quotientInput_polyBitTime : PolyBitTime quotientInput :=
  StandardBitGridCell.pair_polyBitTime _ _ index_polyBitTime (field_polyBitTime 0)
theorem x_polyBitTime : PolyBitTime xBits := by
  have h := polyBitTime_comp (f:=quotientInput) (g:=StandardBitVariableDivideLoop.moduloBits)
    quotientInput_polyBitTime StandardBitVariableDivideLoop.modulo_polyBitTime
  have he : StandardBitVariableDivideLoop.moduloBits ∘ quotientInput=xBits := by funext raw;rfl
  rwa [he] at h
theorem y_polyBitTime : PolyBitTime yBits := by
  have h := polyBitTime_comp (f:=quotientInput) (g:=StandardBitVariableDivideLoop.divideBits)
    quotientInput_polyBitTime StandardBitVariableDivideLoop.divide_polyBitTime
  have he : StandardBitVariableDivideLoop.divideBits ∘ quotientInput=yBits := by funext raw;rfl
  rwa [he] at h

theorem anchorFrame_polyBitTime : PolyBitTime anchorFrame :=
  StandardBitWordVector.assemble_polyBitTime [field 0,field 1,xBits,yBits]
    (by intro f hf; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl|rfl|rfl
        · exact field_polyBitTime 0
        · exact field_polyBitTime 1
        · exact x_polyBitTime
        · exact y_polyBitTime)
theorem prepare_polyBitTime : PolyBitTime prepare :=
  StandardBitGridCell.pair_polyBitTime _ _ presence_polyBitTime anchorFrame_polyBitTime

theorem prepare_eq (raw : List Bool) : prepare raw=
    pairBits [decide (index (field 1 raw)<(field 1 raw).length)]
      (encode [field 0 raw,field 1 raw,
        encodeNat (index (field 1 raw)%value (field 0 raw)),
        encodeNat (index (field 1 raw)/value (field 0 raw))]) := by
  simp only [prepare,presence,indexBits,scan,firstZeroBits,StandardBitFirstZero.firstZeroBits,
    firstBits_pair,secondBits_pair,anchorFrame,xBits,yBits,quotientInput,
    StandardBitVariableDivideLoop.moduloBits,StandardBitVariableDivideLoop.divideBits,
    value_encode_nat]

theorem original_frame (side : List Bool)
    (done : Finset (Placement PakFixedWeightedShapeFamily.Shape)) :
    prepare (encode [side,mask (value side) done])=
      pairBits [decide (index (mask (value side) done)<(value side)^2)]
        (encode [side,mask (value side) done,
          encodeNat (index (mask (value side) done)%value side),
          encodeNat (index (mask (value side) done)/value side)]) := by
  rw [prepare_eq]
  simp only [field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    PakFixedShapeOccupancyScan.mask_length]

theorem occupancy_anchor_setup_spec : PolyBitTime prepare ∧
    (∀ raw,prepare raw=pairBits [decide (index (field 1 raw)<(field 1 raw).length)]
      (encode [field 0 raw,field 1 raw,
        encodeNat (index (field 1 raw)%value (field 0 raw)),
        encodeNat (index (field 1 raw)/value (field 0 raw))])) ∧
    (∀ side done,index (mask (value side) done)<(value side)^2 →
      PakFixedShapeFirstUncovered.firstUncovered (value side) done=some
        (((index (mask (value side) done)%value side : Nat) : Int),
         ((index (mask (value side) done)/value side : Nat) : Int))) :=
  ⟨prepare_polyBitTime,prepare_eq,fun side done h =>
    PakFixedShapeGridCoordinates.first_uncovered_coordinate (value side) done h⟩

end
end PakFixedPolyomino.PakFixedShapeOccupancyAnchorSetup
