import PakFixedPolyomino.PakFixedWeightedStandardBinaryCount
import PakFixedPolyomino.StandardBitIncrement

/-! Ordinary positional binary semantics on every word. Normalization removes
only high zero digits and is proved equal to canonical pinned encodeNat.
These word identities alone do not claim a tape-time bound. -/
namespace PakFixedPolyomino.StandardBinaryWordNormalization
open Computability
open PakFixedWeightedStandardBinaryCount (value)

def rawNum : List Bool → Num
  | [] => .zero
  | b :: rest => if b then (rawNum rest).bit1 else (rawNum rest).bit0

def normalizeBits : List Bool → List Bool
  | [] => []
  | b :: rest =>
      let tail := normalizeBits rest
      if tail = [] then (if b then [true] else []) else b :: tail

theorem rawNum_value (x : List Bool) : (rawNum x : Nat) = value x := by
  induction x with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simp only [rawNum, Bool.false_eq_true, if_false, if_true,
      Num.cast_bit0, Num.cast_bit1, value, Bool.toNat_false, Bool.toNat_true, ih]
    all_goals omega

theorem normalize_eq_encodeNum (x : List Bool) :
    normalizeBits x = encodeNum (rawNum x) := by
  induction x with
  | nil => rfl
  | cons b rest ih =>
    cases hn : rawNum rest with
    | zero =>
      cases b <;> simp [normalizeBits, rawNum, ih, hn, encodeNum, Num.bit0, Num.bit1,
        encodePosNum]
    | pos n =>
      have hne := encodePosNum_nonempty n
      cases b <;> simp [normalizeBits, rawNum, ih, hn, encodeNum, Num.bit0, Num.bit1,
        encodePosNum, hne]

theorem normalize_eq_encodeNat (x : List Bool) :
    normalizeBits x = encodeNat (value x) := by
  rw [normalize_eq_encodeNum]
  unfold encodeNat
  rw [← rawNum_value, Num.of_to_nat]

theorem value_normalize (x : List Bool) : value (normalizeBits x) = value x := by
  rw [normalize_eq_encodeNat, PakFixedWeightedStandardBinaryCount.value_encode_nat]

theorem decode_normalize (x : List Bool) : decodeNat (normalizeBits x) = value x := by
  rw [normalize_eq_encodeNat, decode_encodeNat]

theorem normalize_encodeNat (n : Nat) : normalizeBits (encodeNat n) = encodeNat n := by
  rw [normalize_eq_encodeNat, PakFixedWeightedStandardBinaryCount.value_encode_nat]

theorem normalize_idempotent (x : List Bool) :
    normalizeBits (normalizeBits x) = normalizeBits x := by
  rw [normalize_eq_encodeNat, value_normalize]
  exact (normalize_eq_encodeNat x).symm

theorem normalize_length (x : List Bool) : (normalizeBits x).length ≤ x.length := by
  induction x with
  | nil => rfl
  | cons b rest ih =>
    simp only [normalizeBits]
    split
    · cases b <;> simp <;> omega
    · simp only [List.length_cons] at *
      omega

theorem normalize_zero_suffix (x : List Bool) :
    ∃ k, x = normalizeBits x ++ List.replicate k false := by
  induction x with
  | nil => exact ⟨0, rfl⟩
  | cons b rest ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases he : normalizeBits rest = []
    · have hr : rest = List.replicate k false := by simpa [he] using hk
      cases b with
      | false =>
        refine ⟨k+1, ?_⟩
        simp only [normalizeBits, he, if_pos rfl, Bool.false_eq_true, if_false, List.nil_append]
        rw [hr, List.replicate_succ]
        rfl
      | true =>
        refine ⟨k, ?_⟩
        simp only [normalizeBits, he, if_pos rfl, if_true, List.cons_append, List.nil_append]
        rw [hr]
    · refine ⟨k, ?_⟩
      simp only [normalizeBits, if_neg he]
      exact congrArg (List.cons b) hk

theorem normalize_empty_iff (x : List Bool) : normalizeBits x = [] ↔ value x = 0 := by
  rw [normalize_eq_encodeNat]
  constructor
  · intro h
    have hv := congrArg value h
    simpa [value, PakFixedWeightedStandardBinaryCount.value_encode_nat] using hv
  · intro h
    rw [h]
    rfl

theorem increment_value (x : List Bool) :
    value (StandardBitIncrement.incrementBits x) = value x + 1 := by
  induction x with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simp only [StandardBitIncrement.incrementBits, value,
      Bool.toNat_false, Bool.toNat_true, ih]
    all_goals omega

theorem increment_normalize (x : List Bool) :
    normalizeBits (StandardBitIncrement.incrementBits x) = encodeNat (value x + 1) := by
  rw [normalize_eq_encodeNat, increment_value]

theorem normalization_spec :
    (∀ x, normalizeBits x = encodeNat (value x)) ∧
    (∀ x, value (normalizeBits x) = value x) ∧
    (∀ x, (normalizeBits x).length ≤ x.length) ∧
    (∀ x, ∃ k, x = normalizeBits x ++ List.replicate k false) ∧
    (∀ x, value (StandardBitIncrement.incrementBits x) = value x + 1) :=
  ⟨normalize_eq_encodeNat, value_normalize, normalize_length,
    normalize_zero_suffix, increment_value⟩

end PakFixedPolyomino.StandardBinaryWordNormalization
