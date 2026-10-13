import PakFixedPolyomino.StandardBitBooleanMaps
import PakFixedPolyomino.StandardBitFixedAdd
import PakFixedPolyomino.StandardBitVariableSubtractClosed

/-! An actual ordinary tape transducer applies a fixed integer offset to an
unsigned binary coordinate, returning its saturated coordinate and an explicit
nonnegative flag. The offset is finite program data, not a unit-cost input
integer. EVERY raw coordinate, including empty and high zeros, is covered.
Fixed addition, actual ordinary subtraction/comparison, conditional Boolean
control, literal constants and physical pairing costs are all supplied. -/
namespace PakFixedPolyomino.StandardBitSignedOffset
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitBooleanMaps

def numeric : Int → List Bool → List Bool
  | .ofNat k,raw => encodeNat (value raw+k)
  | .negSucc k,raw => encodeNat (value raw-(k+1))
def valid : Int → List Bool → Bool
  | .ofNat _,_ => true
  | .negSucc k,raw => decide (k+1≤value raw)
def offsetBits (d : Int) (raw : List Bool) : List Bool :=
  pairBits (numeric d raw) [valid d raw]
def pairConstant (k : Nat) (raw : List Bool) : List Bool := pairBits raw (encodeNat k)

theorem pairConstant_polyBitTime (k : Nat) : PolyBitTime (pairConstant k) := by
  have h := StandardBitPairMaps.parallel_polyBitTime id (fun _ => encodeNat k)
    identity_polyBitTime (constant_word_polyBitTime (encodeNat k))
  have he : StandardBitPairMaps.parallel id (fun _ => encodeNat k)=pairConstant k := by
    funext raw;rw [StandardBitPairMaps.parallel_pair];rfl
  rwa [he] at h

theorem fixed_sub_polyBitTime (k : Nat) :
    PolyBitTime (fun raw => encodeNat (value raw-k)) := by
  have h := polyBitTime_comp (pairConstant_polyBitTime k)
    StandardBitVariableSubtractClosed.subtract_polyBitTime
  have he : StandardBitVariableSubtractLoop.subtractBits ∘ pairConstant k=
      (fun raw => encodeNat (value raw-k)) := by
    funext raw
    simp only [Function.comp_apply,pairConstant,StandardBitVariableSubtractLoop.subtractBits,
      StandardBitPairFirstCompaction.firstBits_pair,StandardBitPairProjection.secondBits_pair,value_encode_nat]
  rwa [he] at h

theorem fixed_lt_polyBitTime (k : Nat) :
    PolyBitTime (fun raw => [decide (value raw<k)]) := by
  have h := polyBitTime_comp (pairConstant_polyBitTime k)
    StandardBitVariableSubtractClosed.lt_polyBitTime
  have he : StandardBitVariableSubtractLoop.ltBits ∘ pairConstant k=
      (fun raw => [decide (value raw<k)]) := by
    funext raw
    simp only [Function.comp_apply,pairConstant,StandardBitVariableSubtractLoop.ltBits,
      StandardBitPairFirstCompaction.firstBits_pair,StandardBitPairProjection.secondBits_pair,value_encode_nat]
  rwa [he] at h

theorem fixed_le_polyBitTime (k : Nat) :
    PolyBitTime (fun raw => [decide (k≤value raw)]) := by
  have h := not_polyBitTime (fun raw => decide (value raw<k)) (fixed_lt_polyBitTime k)
  have he : (fun raw => [!decide (value raw<k)])=(fun raw => [decide (k≤value raw)]) := by
    funext raw
    by_cases hk : k≤value raw
    · simp [hk,Nat.not_lt.mpr hk]
    · simp [hk,Nat.lt_of_not_ge hk]
  rwa [he] at h

theorem numeric_polyBitTime (d : Int) : PolyBitTime (numeric d) := by
  cases d with
  | ofNat k => exact StandardBitFixedAdd.fixed_add_polyBitTime k
  | negSucc k => exact fixed_sub_polyBitTime (k+1)

theorem valid_polyBitTime (d : Int) : PolyBitTime (fun raw => [valid d raw]) := by
  cases d with
  | ofNat k => exact constant_bool_polyBitTime true
  | negSucc k => exact fixed_le_polyBitTime (k+1)

theorem offset_polyBitTime (d : Int) : PolyBitTime (offsetBits d) := by
  have h := StandardBitPairMaps.parallel_polyBitTime (numeric d) (fun raw => [valid d raw])
    (numeric_polyBitTime d) (valid_polyBitTime d)
  have he : StandardBitPairMaps.parallel (numeric d) (fun raw => [valid d raw])=offsetBits d := by
    funext raw;rw [StandardBitPairMaps.parallel_pair];rfl
  rwa [he] at h

theorem numeric_value (d : Int) (raw : List Bool) :
    value (numeric d raw)=((value raw : Int)+d).toNat := by
  cases d with
  | ofNat k => simp only [numeric,value_encode_nat,Int.ofNat_eq_natCast,← Int.natCast_add,Int.toNat_natCast]
  | negSucc k =>
    have he : (value raw : Int)+Int.negSucc k=(value raw : Int)-((k+1 : Nat) : Int) := by
      simp only [Int.negSucc_eq,Int.natCast_add,Int.natCast_one,sub_eq_add_neg]
    rw [numeric,value_encode_nat,he,Int.toNat_sub]

theorem valid_nonnegative (d : Int) (raw : List Bool) :
    valid d raw=decide (0≤(value raw : Int)+d) := by
  cases d with
  | ofNat k =>
    have hz : 0≤(value raw : Int)+Int.ofNat k := by
      change 0≤(value raw : Int)+(k : Int)
      omega
    simp only [valid,hz,decide_true]
  | negSucc k =>
    simp only [valid,Int.negSucc_eq]
    congr 1
    apply propext
    omega

theorem offset_spec (d : Int) : PolyBitTime (offsetBits d) ∧
    (∀ raw,value (numeric d raw)=((value raw : Int)+d).toNat) ∧
    (∀ raw,valid d raw=decide (0≤(value raw : Int)+d)) :=
  ⟨offset_polyBitTime d,numeric_value d,valid_nonnegative d⟩

end
end PakFixedPolyomino.StandardBitSignedOffset
