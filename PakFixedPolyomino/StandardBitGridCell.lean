import PakFixedPolyomino.StandardBitSignedOffset
import PakFixedPolyomino.StandardBitIndexedWordMark
import PakFixedPolyomino.PakGuardedArithmeticBitTimeClosed

/-! Actual tape-time access to one fixed offset from an anchor in a square
occupancy grid. The frame is [literal side, literal mask, unsigned x, unsigned y].
Both signed underflow and square-bound checks precede the cell validity flag;
an undersized mask is explicitly rejected. Binary row multiplication/addition,
indexed access, marking and all Boolean/pairing/control costs are internal.
This is a cell primitive; the finite shape stencil and ND program are separate. -/
namespace PakFixedPolyomino.StandardBitGridCell
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (field field_polyBitTime)
open StandardBitBooleanMaps
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)

def shifted (d : Int) (k : Nat) (raw : List Bool) : List Bool :=
  StandardBitSignedOffset.numeric d (field k raw)
def shiftValid (d : Int) (k : Nat) (raw : List Bool) : Bool :=
  StandardBitSignedOffset.valid d (field k raw)
def rowProduct (dy : Int) (raw : List Bool) : List Bool :=
  encodeNat (value (shifted dy 3 raw)*value (field 0 raw))
def indexBits (dx dy : Int) (raw : List Bool) : List Bool :=
  encodeNat (value (rowProduct dy raw)+value (shifted dx 2 raw))
def belowSide (d : Int) (k : Nat) (raw : List Bool) : Bool :=
  decide (value (shifted d k raw)<value (field 0 raw))
def inside (dx dy : Int) (raw : List Bool) : Bool :=
  (shiftValid dx 2 raw && shiftValid dy 3 raw) && (belowSide dx 2 raw && belowSide dy 3 raw)
def inputPair (dx dy : Int) (raw : List Bool) : List Bool := pairBits (indexBits dx dy raw) (field 1 raw)
def readCell (dx dy : Int) (raw : List Bool) : List Bool := StandardBitIndexedWordRead.readBits (inputPair dx dy raw)
def free (dx dy : Int) (raw : List Bool) : Bool :=
  inside dx dy raw && decide ((field 1 raw)[value (indexBits dx dy raw)]?=some false)
def markedMask (dx dy : Int) (raw : List Bool) : List Bool :=
  (field 1 raw).set (value (indexBits dx dy raw)) true
def updatedFrame (dx dy : Int) (raw : List Bool) : List Bool :=
  StandardBitWordVector.encode [field 0 raw,markedMask dx dy raw,field 2 raw,field 3 raw]

theorem pair_polyBitTime (f g : List Bool → List Bool) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (fun raw => pairBits (f raw) (g raw)) := by
  have h := StandardBitPairMaps.parallel_polyBitTime f g hf hg
  have he : StandardBitPairMaps.parallel f g=(fun raw => pairBits (f raw) (g raw)) := by
    funext raw;rw [StandardBitPairMaps.parallel_pair]
  rwa [he] at h

theorem shifted_polyBitTime (d : Int) (k : Nat) : PolyBitTime (shifted d k) :=
  polyBitTime_comp (field_polyBitTime k) (StandardBitSignedOffset.numeric_polyBitTime d)
theorem shiftValid_polyBitTime (d : Int) (k : Nat) : PolyBitTime (fun raw => [shiftValid d k raw]) :=
  polyBitTime_comp (field_polyBitTime k) (StandardBitSignedOffset.valid_polyBitTime d)

theorem rowProduct_polyBitTime (dy : Int) : PolyBitTime (rowProduct dy) := by
  have h := polyBitTime_comp
    (pair_polyBitTime (shifted dy 3) (field 0) (shifted_polyBitTime dy 3) (field_polyBitTime 0))
    PakGuardedArithmeticBitTimeClosed.multiply_polyBitTime
  have he : StandardBitVariableMultiplyLoop.multiplyBits ∘
      (fun raw => pairBits (shifted dy 3 raw) (field 0 raw))=rowProduct dy := by
    funext raw
    simp only [Function.comp_apply,StandardBitVariableMultiplyLoop.multiplyBits,firstBits_pair,secondBits_pair,rowProduct]
  rwa [he] at h

theorem index_polyBitTime (dx dy : Int) : PolyBitTime (indexBits dx dy) := by
  have h := polyBitTime_comp
    (pair_polyBitTime (rowProduct dy) (shifted dx 2) (rowProduct_polyBitTime dy) (shifted_polyBitTime dx 2))
    StandardBitVariableAddClosed.add_polyBitTime
  have he : StandardBitVariableAdd.addBits ∘
      (fun raw => pairBits (rowProduct dy raw) (shifted dx 2 raw))=indexBits dx dy := by
    funext raw
    simp only [Function.comp_apply,StandardBitVariableAdd.add_pair,indexBits]
  rwa [he] at h

theorem belowSide_polyBitTime (d : Int) (k : Nat) : PolyBitTime (fun raw => [belowSide d k raw]) := by
  have h := polyBitTime_comp
    (pair_polyBitTime (shifted d k) (field 0) (shifted_polyBitTime d k) (field_polyBitTime 0))
    StandardBitVariableSubtractClosed.lt_polyBitTime
  have he : StandardBitVariableSubtractLoop.ltBits ∘
      (fun raw => pairBits (shifted d k raw) (field 0 raw))=(fun raw => [belowSide d k raw]) := by
    funext raw
    simp only [Function.comp_apply,StandardBitVariableSubtractLoop.ltBits,firstBits_pair,secondBits_pair,belowSide]
  rwa [he] at h

theorem inside_polyBitTime (dx dy : Int) : PolyBitTime (fun raw => [inside dx dy raw]) :=
  and_polyBitTime _ _
    (and_polyBitTime _ _ (shiftValid_polyBitTime dx 2) (shiftValid_polyBitTime dy 3))
    (and_polyBitTime _ _ (belowSide_polyBitTime dx 2) (belowSide_polyBitTime dy 3))

theorem inputPair_polyBitTime (dx dy : Int) : PolyBitTime (inputPair dx dy) :=
  pair_polyBitTime _ _ (index_polyBitTime dx dy) (field_polyBitTime 1)
theorem readCell_polyBitTime (dx dy : Int) : PolyBitTime (readCell dx dy) :=
  polyBitTime_comp (inputPair_polyBitTime dx dy) StandardBitIndexedWordRead.read_polyBitTime

theorem literal_free_flag (w : List Bool) (i : Nat) :
    (decide (i<w.length) && (!((w[i]?).getD false)))=decide (w[i]?=some false) := by
  cases he : w[i]? with
  | none =>
    have hn : ¬i<w.length := by have h := List.getElem?_eq_none_iff.mp he;omega
    simp [he,hn]
  | some b =>
    have hi : i<w.length := by
      by_contra hn
      have hnone : w[i]?=none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [he] at hnone
      contradiction
    cases b <;> simp [he,hi]

theorem free_polyBitTime (dx dy : Int) : PolyBitTime (fun raw => [free dx dy raw]) := by
  have hr := readCell_polyBitTime dx dy
  have hb := polyBitTime_comp (polyBitTime_comp hr first_polyBitTime) StandardBitHead.head_polyBitTime
  have hv := polyBitTime_comp (polyBitTime_comp hr secondBits_polyBitTime) StandardBitHead.head_polyBitTime
  have hf := and_polyBitTime (fun raw => (secondBits (readCell dx dy raw)).headD false)
    (fun raw => !(firstBits (readCell dx dy raw)).headD false) hv
    (not_polyBitTime (fun raw => (firstBits (readCell dx dy raw)).headD false) hb)
  have he : (fun raw => [(secondBits (readCell dx dy raw)).headD false &&
        !(firstBits (readCell dx dy raw)).headD false])=
      (fun raw => [decide ((field 1 raw)[value (indexBits dx dy raw)]?=some false)]) := by
    funext raw
    simp only [readCell,inputPair,StandardBitIndexedWordRead.readBits,firstBits_pair,secondBits_pair,
      List.headD_cons,literal_free_flag]
  rw [he] at hf
  exact and_polyBitTime _ _ (inside_polyBitTime dx dy) hf

theorem markedMask_polyBitTime (dx dy : Int) : PolyBitTime (markedMask dx dy) := by
  have h := polyBitTime_comp (inputPair_polyBitTime dx dy) StandardBitIndexedWordMark.mark_polyBitTime
  have he : StandardBitIndexedWordMark.markBits ∘ inputPair dx dy=markedMask dx dy := by
    funext raw;rw [Function.comp_apply,inputPair,StandardBitIndexedWordMark.mark_pair];rfl
  rwa [he] at h

theorem updatedFrame_polyBitTime (dx dy : Int) : PolyBitTime (updatedFrame dx dy) := by
  exact StandardBitWordVector.assemble_polyBitTime
    [field 0,markedMask dx dy,field 2,field 3]
    (by intro f hf; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl|rfl|rfl
        · exact field_polyBitTime 0
        · exact markedMask_polyBitTime dx dy
        · exact field_polyBitTime 2
        · exact field_polyBitTime 3)

theorem index_value (dx dy : Int) (raw : List Bool) :
    value (indexBits dx dy raw)=
      ((value (field 3 raw) : Int)+dy).toNat*value (field 0 raw)+
        ((value (field 2 raw) : Int)+dx).toNat := by
  simp only [indexBits,rowProduct,value_encode_nat,shifted,StandardBitSignedOffset.numeric_value]

theorem inside_iff (dx dy : Int) (raw : List Bool) : inside dx dy raw=true ↔
    0≤(value (field 2 raw) : Int)+dx ∧ 0≤(value (field 3 raw) : Int)+dy ∧
    (value (field 2 raw) : Int)+dx<(value (field 0 raw) : Int) ∧
    (value (field 3 raw) : Int)+dy<(value (field 0 raw) : Int) := by
  simp only [inside,Bool.and_eq_true,shiftValid,StandardBitSignedOffset.valid_nonnegative,
    decide_eq_true_eq,belowSide,shifted,StandardBitSignedOffset.numeric_value]
  constructor
  · rintro ⟨⟨hx,hy⟩,hxl,hyl⟩
    refine ⟨hx,hy,?_,?_⟩ <;> omega
  · rintro ⟨hx,hy,hxl,hyl⟩
    refine ⟨⟨hx,hy⟩,?_,?_⟩ <;> omega

theorem markedMask_length (dx dy : Int) (raw : List Bool) :
    (markedMask dx dy raw).length=(field 1 raw).length := List.length_set

theorem grid_cell_spec (dx dy : Int) : PolyBitTime (fun raw => [free dx dy raw]) ∧
    PolyBitTime (readCell dx dy) ∧ PolyBitTime (markedMask dx dy) ∧ PolyBitTime (updatedFrame dx dy) ∧
    (∀ raw,value (indexBits dx dy raw)=
      ((value (field 3 raw) : Int)+dy).toNat*value (field 0 raw)+
        ((value (field 2 raw) : Int)+dx).toNat) ∧
    (∀ raw,(markedMask dx dy raw).length=(field 1 raw).length) :=
  ⟨free_polyBitTime dx dy,readCell_polyBitTime dx dy,markedMask_polyBitTime dx dy,
    updatedFrame_polyBitTime dx dy,index_value dx dy,markedMask_length dx dy⟩

end
end PakFixedPolyomino.StandardBitGridCell
