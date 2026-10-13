import PakFixedPolyomino.StandardBinaryWordNormalization

/-! Exact little-endian carry specification for multiplication by a fixed
natural. Carry values fit one fixed finite control set; output lengths are
bounded on every raw word. This module asserts no standard tape-time bound. -/
namespace PakFixedPolyomino.StandardBinaryFixedMultiplyWord
open Computability StandardBinaryWordNormalization
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)

def lowBit (n : Nat) : Bool := n % 2 == 1

theorem lowBit_value (n : Nat) : (lowBit n).toNat = n % 2 := by
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by
    have h := Nat.mod_lt n (by decide : 0 < 2)
    omega
  rcases hm with hm | hm <;> simp [lowBit,hm]

def carryMultiply (c carry : Nat) : List Bool → List Bool
  | [] => encodeNat carry
  | b :: rest =>
      lowBit (c*b.toNat+carry) :: carryMultiply c ((c*b.toNat+carry)/2) rest

theorem carryMultiply_value (c carry : Nat) (x : List Bool) :
    value (carryMultiply c carry x) = c * value x + carry := by
  induction x generalizing carry with
  | nil => simp [carryMultiply,value_encode_nat,value]
  | cons b x ih =>
      simp only [carryMultiply,value,lowBit_value,ih]
      have h := Nat.mod_add_div (c*b.toNat+carry) 2
      nlinarith

theorem nextCarry_le (c carry : Nat) (b : Bool) (hcarry : carry ≤ c) :
    (c*b.toNat+carry)/2 ≤ c := by
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,mul_zero,mul_one,zero_add] <;> omega

def nextCarry (c : Nat) (carry : Fin (c+1)) (b : Bool) : Fin (c+1) :=
  ⟨(c*b.toNat+carry.val)/2,by have h := nextCarry_le c carry.val b (by omega); omega⟩

theorem nextCarry_value (c : Nat) (carry : Fin (c+1)) (b : Bool) :
    (nextCarry c carry b).val = (c*b.toNat+carry.val)/2 := rfl

theorem encode_pos_length_le (n : PosNum) : (encodePosNum n).length ≤ (n : Nat) := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp only [encodePosNum,List.length_cons,PosNum.cast_bit0]
      have hp := PosNum.to_nat_pos n
      omega
  | bit1 n ih =>
      simp only [encodePosNum,List.length_cons,PosNum.cast_bit1]
      omega

theorem encode_num_length_le (n : Num) : (encodeNum n).length ≤ (n : Nat) := by
  cases n with
  | zero => rfl
  | pos n => exact encode_pos_length_le n

theorem encode_nat_length_le (n : Nat) : (encodeNat n).length ≤ n := by
  change (encodeNum (n : Num)).length ≤ n
  simpa only [Num.to_of_nat] using encode_num_length_le (n : Num)

theorem carryMultiply_length_le (c carry : Nat) (x : List Bool) (hcarry : carry ≤ c) :
    (carryMultiply c carry x).length ≤ x.length+c := by
  induction x generalizing carry with
  | nil => exact (encode_nat_length_le carry).trans (by simpa using hcarry)
  | cons b x ih =>
      simp only [carryMultiply,List.length_cons]
      have h := ih _ (nextCarry_le c carry b hcarry)
      omega

def multiply (c : Nat) (x : List Bool) : List Bool :=
  normalizeBits (carryMultiply c 0 x)

theorem multiply_eq_encode (c : Nat) (x : List Bool) :
    multiply c x = encodeNat (c*value x) := by
  rw [multiply,normalize_eq_encodeNat,carryMultiply_value]
  simp

theorem multiply_length_le (c : Nat) (x : List Bool) :
    (multiply c x).length ≤ x.length+c :=
  (normalize_length _).trans (carryMultiply_length_le c 0 x (Nat.zero_le c))

theorem fixed_multiply_word_spec :
    (∀ c carry x, value (carryMultiply c carry x) = c*value x+carry) ∧
    (∀ c carry x, carry ≤ c → (carryMultiply c carry x).length ≤ x.length+c) ∧
    (∀ c x, multiply c x = encodeNat (c*value x)) ∧
    (∀ c x, (multiply c x).length ≤ x.length+c) :=
  ⟨carryMultiply_value,carryMultiply_length_le,multiply_eq_encode,multiply_length_le⟩

end PakFixedPolyomino.StandardBinaryFixedMultiplyWord
