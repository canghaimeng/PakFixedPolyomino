import PakFixedPolyomino.ConcretePakScanner
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# The executable side-word layer

This module formalizes the self-delimiting word

`1 x 1 0^|x| 1 0^(72|x|+72)`

before it is compiled into the source machine.  Keeping the word layer
separate makes its injectivity and the two omitted-high-bit facts independent
of the still-missing universal-machine transition table.
-/

namespace PakFixedPolyomino.ConcretePakSide

abbrev Word := List Bool

def paddingLength (m : ℕ) : ℕ := 72 * m + 72

def encodedWord (x : Word) : Word :=
  true :: x ++ [true] ++ List.replicate x.length false ++ [true] ++
    List.replicate (paddingLength x.length) false

def payloadAt (m : ℕ) (w : Word) : Word := (w.drop 1).take m

def littleDigits (x : Word) : List ℕ :=
  (encodedWord x).reverse.map Bool.toNat

def sideValue (x : Word) : ℕ := Nat.ofDigits 2 (littleDigits x)

/-- Executable decoder for the self-delimiting language.  The physical
one-tape parser implements the same test by run counting; this word-level
function is its machine-independent specification. -/
def decodeWord (w : Word) : Option Word :=
  let m := (w.length - 75) / 74
  let x := payloadAt m w
  if encodedWord x = w then some x else none

@[simp] theorem encodedWord_length (x : Word) :
    (encodedWord x).length = 74 * x.length + 75 := by
  simp [encodedWord, paddingLength]
  omega

@[simp] theorem payloadAt_encodedWord (x : Word) :
    payloadAt x.length (encodedWord x) = x := by
  simp [payloadAt, encodedWord]

theorem encodedWord_injective : Function.Injective encodedWord := by
  intro x y h
  have hlen := congrArg List.length h
  simp only [encodedWord_length] at hlen
  have hxy : x.length = y.length := by omega
  have hread := congrArg (payloadAt x.length) h
  calc
    x = payloadAt x.length (encodedWord x) := (payloadAt_encodedWord x).symm
    _ = payloadAt x.length (encodedWord y) := hread
    _ = y := by rw [hxy]; exact payloadAt_encodedWord y

private theorem boolToNat_injective : Function.Injective Bool.toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all

theorem digits_sideValue (x : Word) : Nat.digits 2 (sideValue x) = littleDigits x := by
  apply Nat.digits_ofDigits 2 (by decide)
  · intro d hd
    rcases List.mem_map.mp hd with ⟨b, -, rfl⟩
    cases b <;> decide
  · intro hne
    simp [littleDigits, encodedWord]

theorem sideValue_injective : Function.Injective sideValue := by
  intro x y h
  have hd := congrArg (Nat.digits 2) h
  rw [digits_sideValue x, digits_sideValue y] at hd
  have hr : (encodedWord x).reverse = (encodedWord y).reverse :=
    (List.map_injective_iff.mpr boolToNat_injective) hd
  exact encodedWord_injective (List.reverse_injective hr)

@[simp] theorem decodeWord_encodedWord (x : Word) :
    decodeWord (encodedWord x) = some x := by
  have hm : ((encodedWord x).length - 75) / 74 = x.length := by
    rw [encodedWord_length]
    omega
  simp [decodeWord, hm]

theorem decodeWord_sound {w x : Word} (h : decodeWord w = some x) :
    encodedWord x = w := by
  unfold decodeWord at h
  dsimp only at h
  split at h
  · rename_i heq
    have hx : payloadAt ((w.length - 75) / 74) w = x := Option.some.inj h
    simpa [hx] using heq
  · simp at h

theorem decodeWord_eq_some_iff {w x : Word} :
    decodeWord w = some x ↔ encodedWord x = w := by
  constructor
  · exact decodeWord_sound
  · intro h
    subst w
    exact decodeWord_encodedWord x

theorem decodeWord_unique {w x y : Word}
    (hx : decodeWord w = some x) (hy : decodeWord w = some y) : x = y := by
  rw [hx] at hy
  exact Option.some.inj hy

@[simp] theorem encodedWord_head (x : Word) : (encodedWord x).head? = some true := by
  simp [encodedWord]

theorem encodedWord_has_long_zero_suffix (x : Word) :
    ∃ pre, encodedWord x = pre ++
      List.replicate (paddingLength x.length) false := by
  exact ⟨true :: x ++ [true] ++ List.replicate x.length false ++ [true], by
    simp [encodedWord, List.append_assoc]⟩

theorem paddingLength_ge_seventy_two (m : ℕ) : 72 ≤ paddingLength m := by
  simp [paddingLength]

/-- The elementary inequality behind the two omitted high-zero bits. -/
theorem lt_two_pow_sub_two {n : ℕ} (hn : 5 ≤ n) : n < 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        n + 1 ≤ 2 * n := by omega
        _ < 2 * 2 ^ (n - 2) := Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ = 2 ^ (n + 1 - 2) := by
          rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ]
          ring

theorem omitted_bit_sub_two {n : ℕ} (hn : 5 ≤ n) :
    n.testBit (n - 2) = false :=
  Nat.testBit_eq_false_of_lt (lt_two_pow_sub_two hn)

theorem omitted_bit_sub_one {n : ℕ} (hn : 5 ≤ n) :
    n.testBit (n - 1) = false := by
  apply Nat.testBit_eq_false_of_lt
  exact (lt_two_pow_sub_two hn).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))

end PakFixedPolyomino.ConcretePakSide
