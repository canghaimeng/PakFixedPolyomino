import PakFixedPolyomino.PakFixedWeightedBinarySquareCount

/-! Final input convention: usual little-endian positional binary on EVERY
word, including leading zero digits. Pinned encodeNat is retained for
canonical instance/answer encodings; its noncanonical decoder is unused here.
These are arithmetic/model facts, not BIT or membership certificates. -/
namespace PakFixedPolyomino.PakFixedWeightedStandardBinaryCount
noncomputable section
open PakFixedWeightedShapeFamily
open PakFixedWeightedPhysicalSourceReadout (sourceSide sourceAnswer)
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)

def value : List Bool → Nat
  | [] => 0
  | b :: rest => b.toNat + 2 * value rest

theorem pinned_decoder_zero_digit :
    Computability.decodeNat [false] = 2 ∧ value [false] = 0 := ⟨rfl, rfl⟩

theorem value_encode_pos_num (n : PosNum) : value (Computability.encodePosNum n) = (n : Nat) := by
  induction n with
  | one => rfl
  | bit0 n ih =>
    simp only [Computability.encodePosNum, value, Bool.toNat_false, zero_add, ih, PosNum.cast_bit0]
    omega
  | bit1 n ih =>
    simp only [Computability.encodePosNum, value, Bool.toNat_true, ih, PosNum.cast_bit1]
    omega

theorem value_encode_num (n : Num) : value (Computability.encodeNum n) = (n : Nat) := by
  cases n with
  | zero => rfl
  | pos n => exact value_encode_pos_num n

theorem value_encode_nat (n : Nat) : value (Computability.encodeNat n) = n := by
  change value (Computability.encodeNum (n : Num)) = n
  rw [value_encode_num, Num.to_of_nat]

theorem value_append (bits rest : List Bool) :
    value (bits ++ rest) = value bits + 2 ^ bits.length * value rest := by
  induction bits with
  | nil => simp [value]
  | cons b bits ih =>
    simp only [List.cons_append, value, ih, List.length_cons, pow_succ]
    ring

theorem value_append_zero (bits : List Bool) : value (bits ++ [false]) = value bits := by
  rw [value_append]
  simp [value]

theorem value_lt_pow_length (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons b bits ih =>
    cases b <;> simp [value, pow_succ] at * <;> omega

def binarySquareCount (bits : List Bool) : Nat := squareCount (value bits)

theorem binary_square_count_encode (n : Nat) :
    binarySquareCount (Computability.encodeNat n) = squareCount n := by
  rw [binarySquareCount, value_encode_nat]

theorem binary_square_count_nil : binarySquareCount [] = 1 :=
  PakFixedWeightedBinarySquareCount.square_count_zero

theorem binary_square_count_append_zero (bits : List Bool) :
    binarySquareCount (bits ++ [false]) = binarySquareCount bits := by
  rw [binarySquareCount, value_append_zero]
  rfl

theorem binary_source_readout {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    sourceAnswer M p x (binarySquareCount (Computability.encodeNat (sourceSide M p x))) =
      acceptingCount M x (2 ^ p.eval x.length) := by
  rw [binary_square_count_encode]
  exact physical_source_readout M p x ht

theorem standard_sharp_exp_binary_source_readout (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x
        (binarySquareCount (Computability.encodeNat (sourceSide M p x))) = f x := by
  obtain ⟨ns, nt, M, p, h⟩ := standard_sharp_exp_physical_source_readout f hf
  refine ⟨ns, nt, M, p, ?_⟩
  intro x
  rw [binary_square_count_encode]
  exact h x

def fixed_standard_binary_source_spec : Prop :=
  binarySquareCount [] = 1 ∧
  (∀ bits, value bits < 2 ^ bits.length ∧
    binarySquareCount (bits ++ [false]) = binarySquareCount bits) ∧
  (∀ n, binarySquareCount (Computability.encodeNat n) = squareCount n) ∧
  (∀ f : List Bool → Nat, SharpEXP f →
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x
        (binarySquareCount (Computability.encodeNat (sourceSide M p x))) = f x)

theorem fixed_standard_binary_source_spec_holds : fixed_standard_binary_source_spec :=
  ⟨binary_square_count_nil, fun bits => ⟨value_lt_pow_length bits, binary_square_count_append_zero bits⟩,
    binary_square_count_encode, standard_sharp_exp_binary_source_readout⟩

end
end PakFixedPolyomino.PakFixedWeightedStandardBinaryCount
