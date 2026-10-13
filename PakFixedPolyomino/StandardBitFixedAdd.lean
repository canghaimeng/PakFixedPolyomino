import PakFixedPolyomino.StandardBinaryWordNormalization
import PakFixedPolyomino.StandardBitNormalize
import PakFixedPolyomino.StandardBitTimeComposition

/-! Addition of a fixed constant by a finite sequence of actual increment
machines. The number of compiled stages is fixed independently of the input;
every stage and every compiler handoff has an internal ordinary bit-time proof. -/
namespace PakFixedPolyomino.StandardBitFixedAdd
open Computability StandardBitTime StandardBitTimeComposition StandardBinaryWordNormalization
open PakFixedWeightedStandardBinaryCount (value)

def addBits : Nat → List Bool → List Bool
  | 0, w => w
  | k+1, w => StandardBitIncrement.incrementBits (addBits k w)

theorem addBits_value (k : Nat) (w : List Bool) : value (addBits k w) = value w+k := by
  induction k with
  | zero => simp [addBits]
  | succ k ih => rw [addBits,increment_value,ih]; omega

theorem addBits_length (k : Nat) (w : List Bool) : (addBits k w).length ≤ w.length+k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h := StandardBitIncrement.increment_length (addBits k w)
      change (StandardBitIncrement.incrementBits (addBits k w)).length ≤ w.length+(k+1)
      omega

theorem addBits_polyBitTime (k : Nat) : PolyBitTime (addBits k) := by
  induction k with
  | zero => exact identity_polyBitTime
  | succ k ih => exact polyBitTime_comp ih StandardBitIncrement.increment_polyBitTime

theorem fixed_add_polyBitTime (k : Nat) : PolyBitTime (fun w => encodeNat (value w+k)) := by
  have h := polyBitTime_comp (addBits_polyBitTime k) StandardBitNormalize.normalize_polyBitTime
  have he : normalizeBits ∘ addBits k = (fun w => encodeNat (value w+k)) := by
    funext w
    rw [Function.comp_apply,normalize_eq_encodeNat,addBits_value]
  rwa [he] at h

theorem fixed_add_bit_spec (k : Nat) :
    PolyBitTime (fun w => encodeNat (value w+k)) ∧
    (∀ w, normalizeBits (addBits k w) = encodeNat (value w+k)) ∧
    (∀ w, (encodeNat (value w+k)).length ≤ w.length+k) := by
  refine ⟨fixed_add_polyBitTime k,?_,?_⟩
  · intro w; rw [normalize_eq_encodeNat,addBits_value]
  · intro w
    rw [← addBits_value k w,← normalize_eq_encodeNat]
    exact (normalize_length _).trans (addBits_length k w)

end PakFixedPolyomino.StandardBitFixedAdd
