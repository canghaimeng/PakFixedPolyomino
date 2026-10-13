import PakFixedPolyomino.StandardBitMealy
import PakFixedPolyomino.StandardBinaryFixedMultiplyWord
import PakFixedPolyomino.StandardBitAppend
import PakFixedPolyomino.StandardBitNormalize

/-! Fixed natural multiplication on every ordinary little-endian binary word.
Append a fixed zero suffix, scan using bounded finite carry control, then
normalize by the actual tape machine. All three stages have internally proved
standard tape-time bounds; no unit-cost arithmetic operation is assumed. -/
namespace PakFixedPolyomino.StandardBitFixedMultiply
open Computability StandardBitTime StandardBitTimeComposition
open StandardBinaryFixedMultiplyWord StandardBinaryWordNormalization
open PakFixedWeightedStandardBinaryCount (value value_append)

def delta (c : Nat) (carry : Fin (c+1)) (b : Bool) : Fin (c+1) × Bool :=
  ⟨nextCarry c carry b,lowBit (c*b.toNat+carry.val)⟩

def zeroCarry (c : Nat) : Fin (c+1) := ⟨0,by omega⟩

def padded (c : Nat) (x : List Bool) : List Bool := x++List.replicate c false

def scanBits (c : Nat) (x : List Bool) : List Bool :=
  StandardBitMealy.transform (delta c) (zeroCarry c) (padded c x)

theorem finish_append {S : Nat} (d : Fin S → Bool → Fin S × Bool)
    (q : Fin S) (x y : List Bool) :
    StandardBitMealy.finishState d q (x++y) =
      StandardBitMealy.finishState d (StandardBitMealy.finishState d q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => simpa only [List.cons_append,StandardBitMealy.finishState] using ih (d q b).1

theorem finish_zero_div (c k : Nat) (carry : Fin (c+1)) :
    (StandardBitMealy.finishState (delta c) carry (List.replicate k false)).val =
      carry.val/2^k := by
  induction k generalizing carry with
  | zero => simp [StandardBitMealy.finishState]
  | succ k ih =>
      simp only [List.replicate_succ,StandardBitMealy.finishState,delta]
      rw [ih]
      simp [nextCarry,Nat.pow_succ',Nat.div_div_eq_div_mul]

theorem finish_zero (c : Nat) (carry : Fin (c+1)) :
    (StandardBitMealy.finishState (delta c) carry (List.replicate c false)).val = 0 := by
  rw [finish_zero_div]
  exact Nat.div_eq_of_lt (lt_of_le_of_lt (by omega : carry.val ≤ c) (Nat.lt_two_pow_self))

theorem finish_padded_zero (c : Nat) (x : List Bool) :
    (StandardBitMealy.finishState (delta c) (zeroCarry c) (padded c x)).val = 0 := by
  rw [padded,finish_append]
  exact finish_zero c _

theorem carryMultiply_scan_tail (c : Nat) (carry : Fin (c+1)) (x : List Bool) :
    carryMultiply c carry.val x =
      StandardBitMealy.transform (delta c) carry x ++
        encodeNat (StandardBitMealy.finishState (delta c) carry x).val := by
  induction x generalizing carry with
  | nil => rfl
  | cons b x ih =>
      simpa only [carryMultiply,StandardBitMealy.transform,StandardBitMealy.finishState,
        delta,nextCarry,List.cons_append] using congrArg
          (List.cons (lowBit (c*b.toNat+carry.val))) (ih (nextCarry c carry b))

theorem scanBits_eq_carryMultiply (c : Nat) (x : List Bool) :
    scanBits c x = carryMultiply c 0 (padded c x) := by
  change scanBits c x = carryMultiply c (zeroCarry c).val (padded c x)
  rw [carryMultiply_scan_tail,finish_padded_zero]
  simp only [scanBits,show encodeNat 0 = [] from rfl,List.append_nil]

theorem value_zero_suffix (k : Nat) : value (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,value,ih]

theorem padded_value (c : Nat) (x : List Bool) : value (padded c x) = value x := by
  simp [padded,value_append,value_zero_suffix]

theorem scanBits_value (c : Nat) (x : List Bool) : value (scanBits c x) = c*value x := by
  rw [scanBits_eq_carryMultiply,carryMultiply_value,padded_value,Nat.add_zero]

theorem scanBits_length (c : Nat) (x : List Bool) : (scanBits c x).length = x.length+c := by
  simp [scanBits,padded]

theorem normalized_scanBits (c : Nat) (x : List Bool) :
    normalizeBits (scanBits c x) = encodeNat (c*value x) := by
  rw [normalize_eq_encodeNat,scanBits_value]

theorem scanBits_polyBitTime (c : Nat) : PolyBitTime (scanBits c) := by
  exact polyBitTime_comp (StandardBitAppend.fixed_suffix_polyBitTime (List.replicate c false))
    (StandardBitMealy.transducer_polyBitTime (delta c) (zeroCarry c))

theorem fixed_multiply_polyBitTime (c : Nat) :
    PolyBitTime (fun x=>encodeNat (c*value x)) := by
  have h := polyBitTime_comp (scanBits_polyBitTime c) StandardBitNormalize.normalize_polyBitTime
  have he : normalizeBits ∘ scanBits c = (fun x=>encodeNat (c*value x)) := by
    funext x
    exact normalized_scanBits c x
  rwa [he] at h

theorem word_multiply_polyBitTime (c : Nat) : PolyBitTime (multiply c) := by
  have he : multiply c = (fun x=>encodeNat (c*value x)) := by
    funext x
    exact multiply_eq_encode c x
  rw [he]
  exact fixed_multiply_polyBitTime c

theorem fixed_multiply_bit_spec :
    (∀ c x,normalizeBits (scanBits c x) = encodeNat (c*value x)) ∧
    (∀ c x,(scanBits c x).length = x.length+c) ∧
    (∀ c,PolyBitTime (fun x=>encodeNat (c*value x))) :=
  ⟨normalized_scanBits,scanBits_length,fixed_multiply_polyBitTime⟩

end PakFixedPolyomino.StandardBitFixedMultiply
