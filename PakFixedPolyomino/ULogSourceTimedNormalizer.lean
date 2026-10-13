import PakFixedPolyomino.ULogProgram
import Mathlib.Tactic

/-!
# Executable timed source-input normal form

This file fixes a concrete input language for the eventual `U_log` source
normalizer.  Its payload is self-delimiting: a payload bit is escaped as
`true :: b`, and the first unescaped `false` is the delimiter.  The remaining
`false` cells are a unary timer, whose end is supplied by the enclosing finite
tape frame.  Thus this is a genuine executable code over the existing
`zero`/`one` part of the three-symbol physical tape, not a contract-only
encoding.
-/

namespace PakFixedPolyomino.ULogSourceTimedNormalizer

open ULogProgram

/-- Escape one payload bit.  The leading `true` makes the terminal `false`
delimiter unambiguous even when the payload itself contains false bits. -/
def escapeBit (b : Bool) : List Bool := [true, b]

/-- Escaped payload portion, without its delimiter or unary timer. -/
def encodeEscapedPayload : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: encodeEscapedPayload bs

/-- A self-delimiting payload with a unary, all-zero timer suffix. -/
def encodeTimedInput (payload : List Bool) (timerWidth : ℕ) : List Bool :=
  encodeEscapedPayload payload ++ false :: List.replicate timerWidth false

/-- Parse the escaped payload and leave the cells after the delimiter intact. -/
def decodeEscapedPayload : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: suffix => some ([], suffix)
  | true :: [] => none
  | true :: b :: rest =>
      (decodeEscapedPayload rest).map fun (payload, suffix) =>
        (b :: payload, suffix)

/-- Decode an all-zero unary timer. -/
def decodeZeroTimer : List Bool → Option ℕ
  | [] => some 0
  | false :: rest => (decodeZeroTimer rest).map (· + 1)
  | true :: _ => none

/-- Complete decoder: payload together with the timer width. -/
def decodeTimedInput (code : List Bool) : Option (List Bool × ℕ) := do
  let (payload, suffix) ← decodeEscapedPayload code
  let timerWidth ← decodeZeroTimer suffix
  pure (payload, timerWidth)

/-- The physical realization on the `zero`/`one` cells of `Gamma_Ulog`. -/
def encodeTimedInputTape (payload : List Bool) (timerWidth : ℕ) :
    List ULogProgram.Tape :=
  (encodeTimedInput payload timerWidth).map ULogProgram.bitTape

@[simp] theorem encodeEscapedPayload_length (payload : List Bool) :
    (encodeEscapedPayload payload).length = 2 * payload.length := by
  induction payload with
  | nil => simp [encodeEscapedPayload]
  | cons b bs ih => simp [encodeEscapedPayload, ih, Nat.mul_succ, Nat.succ_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem encodeTimedInput_length (payload : List Bool) (timerWidth : ℕ) :
    (encodeTimedInput payload timerWidth).length =
      2 * payload.length + 1 + timerWidth := by
  simp [encodeTimedInput, encodeEscapedPayload_length, Nat.add_assoc,
    Nat.add_comm]

@[simp] theorem encodeTimedInputTape_length (payload : List Bool)
    (timerWidth : ℕ) :
    (encodeTimedInputTape payload timerWidth).length =
      2 * payload.length + 1 + timerWidth := by
  simp [encodeTimedInputTape, encodeTimedInput_length]

theorem decodeEscapedPayload_encode_prefix (payload suffix : List Bool) :
    decodeEscapedPayload
        (encodeEscapedPayload payload ++ false :: suffix) =
      some (payload, suffix) := by
  induction payload with
  | nil => simp [encodeEscapedPayload, decodeEscapedPayload]
  | cons b bs ih =>
      simp [encodeEscapedPayload, decodeEscapedPayload, ih]

@[simp] theorem decodeZeroTimer_replicate (timerWidth : ℕ) :
    decodeZeroTimer (List.replicate timerWidth false) = some timerWidth := by
  induction timerWidth with
  | zero => simp [decodeZeroTimer]
  | succ n ih => simp [List.replicate_succ, decodeZeroTimer, ih]

theorem decodeTimedInput_encode (payload : List Bool) (timerWidth : ℕ) :
    decodeTimedInput (encodeTimedInput payload timerWidth) =
      some (payload, timerWidth) := by
  simp [decodeTimedInput, encodeTimedInput,
    decodeEscapedPayload_encode_prefix, decodeZeroTimer_replicate]

@[simp] theorem decodeEscapedPayload_encodeTimedInput
    (payload : List Bool) (timerWidth : ℕ) :
    decodeEscapedPayload (encodeTimedInput payload timerWidth) =
      some (payload, List.replicate timerWidth false) := by
  exact decodeEscapedPayload_encode_prefix payload
    (List.replicate timerWidth false)

theorem encodeTimedInput_injective : Function.Injective
    (fun p : List Bool × ℕ => encodeTimedInput p.1 p.2) := by
  intro p q hpq
  have hdecoded := congrArg decodeTimedInput hpq
  simpa [decodeTimedInput_encode] using hdecoded

theorem encodeTimedInput_eq_iff (x y : List Bool) (m n : ℕ) :
    encodeTimedInput x m = encodeTimedInput y n ↔ x = y ∧ m = n := by
  constructor
  · intro h
    have hp : (x, m) = (y, n) := encodeTimedInput_injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The pair-valued encoder has no collisions.  (Its timer is delimited by
the surrounding finite source frame rather than by a second in-band marker.) -/
theorem encodeTimedInput_pair_injective : Function.Injective
    (fun p : List Bool × ℕ => encodeTimedInput p.1 p.2) :=
  encodeTimedInput_injective

/-- The source code only uses the `zero` and `one` symbols, hence it is
directly readable by the existing three-symbol tape program. -/
theorem encodeTimedInputTape_symbols (payload : List Bool) (timerWidth : ℕ)
    (cell : ULogProgram.Tape)
    (hcell : cell ∈ encodeTimedInputTape payload timerWidth) :
    cell = MStarConcreteAlphabet.zero ∨ cell = MStarConcreteAlphabet.one := by
  simp only [encodeTimedInputTape, List.mem_map] at hcell
  obtain ⟨b, -, rfl⟩ := hcell
  cases b <;> simp [ULogProgram.bitTape]

theorem bitTape_injective : Function.Injective ULogProgram.bitTape := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact False.elim (MStarConcreteAlphabet.zero_ne_one hab)
  · exact False.elim (MStarConcreteAlphabet.zero_ne_one hab.symm)
  · rfl

theorem encodeTimedInputTape_injective : Function.Injective
    (fun p : List Bool × ℕ => encodeTimedInputTape p.1 p.2) := by
  intro p q hpq
  apply encodeTimedInput_injective
  exact (List.map_injective_iff.mpr bitTape_injective) hpq

/-- The code has linear size, with a literal exact coefficient. -/
theorem encodeTimedInput_linear_bound (payload : List Bool) (timerWidth : ℕ) :
    (encodeTimedInput payload timerWidth).length ≤
      2 * (payload.length + timerWidth + 1) := by
  rw [encodeTimedInput_length]
  omega

/-! ## A finite-alphabet block codec

The timed source language above is binary already.  The normalizer will also
need to encode the finite tape alphabet of an arbitrary `BoundedProgram` on
that binary source tape.  We use the deliberately elementary prefix code

`a ↦ true^a.val ++ [false]`.

There is no hidden choice of an enumeration here: `Fin nt` supplies the
numeric symbol number.  The decoder below is executable, consumes exactly one
delimiter, and returns the unconsumed suffix.  This is the useful form for a
future one-tape scanner.
-/

/-- Count the initial run of `true` cells and leave the first `false` and all
following cells out of the count.  A word containing no delimiter fails. -/
def decodeTrueRun : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: suffix => some (0, suffix)
  | true :: suffix =>
      (decodeTrueRun suffix).map fun (n, rest) => (n + 1, rest)

/-- Unary, self-delimiting encoding of one `Fin nt` symbol. -/
def encodeFin {nt : ℕ} (a : Fin nt) : List Bool :=
  List.replicate a.val true ++ [false]

/-- Decode one finite-alphabet block and retain the unconsumed suffix. -/
def decodeFinPrefix (nt : ℕ) (code : List Bool) :
    Option (Fin nt × List Bool) := do
  let (value, suffix) ← decodeTrueRun code
  if h : value < nt then
    pure (⟨value, h⟩, suffix)
  else
    none

@[simp] theorem decodeTrueRun_replicate_true_false (n : ℕ)
    (suffix : List Bool) :
    decodeTrueRun (List.replicate n true ++ false :: suffix) =
      some (n, suffix) := by
  induction n with
  | zero => simp [decodeTrueRun]
  | succ n ih =>
      simp [List.replicate_succ, decodeTrueRun, ih]

@[simp] theorem encodeFin_length {nt : ℕ} (a : Fin nt) :
    (encodeFin a).length = a.val + 1 := by
  simp [encodeFin]

theorem decodeFinPrefix_encodeFin_append {nt : ℕ} (a : Fin nt)
    (suffix : List Bool) :
    decodeFinPrefix nt (encodeFin a ++ suffix) = some (a, suffix) := by
  simp [decodeFinPrefix, encodeFin, decodeTrueRun_replicate_true_false,
    a.isLt]

/-- Encode a finite-alphabet word by concatenating its self-delimiting
blocks. -/
def encodeFinList {nt : ℕ} : List (Fin nt) → List Bool
  | [] => []
  | a :: as => encodeFin a ++ encodeFinList as

/-- Decode a specified number of blocks and return the remaining input.  The
block count is explicit because a concatenation of blocks has no extra
end-marker; the enclosing source frame supplies this count in the later
simulator. -/
def decodeFinBlocks (nt : ℕ) : ℕ → List Bool →
    Option (List (Fin nt) × List Bool)
  | 0, code => some ([], code)
  | n + 1, code => do
      let (a, rest) ← decodeFinPrefix nt code
      let (as, suffix) ← decodeFinBlocks nt n rest
      pure (a :: as, suffix)

/-- Exact list decoder once the frame supplies the expected number of
finite-alphabet symbols. -/
def decodeFinListExact (nt count : ℕ) (code : List Bool) :
    Option (List (Fin nt)) := do
  let (symbols, suffix) ← decodeFinBlocks nt count code
  if suffix = [] then pure symbols else none

theorem decodeFinBlocks_encodeFinList_append {nt : ℕ}
    (symbols : List (Fin nt)) (suffix : List Bool) :
    decodeFinBlocks nt symbols.length (encodeFinList symbols ++ suffix) =
      some (symbols, suffix) := by
  induction symbols with
  | nil => simp [encodeFinList, decodeFinBlocks]
  | cons a symbols ih =>
      simp only [encodeFinList, List.length_cons, decodeFinBlocks,
        List.append_assoc]
      rw [decodeFinPrefix_encodeFin_append]
      simp [ih]

@[simp] theorem decodeFinListExact_encodeFinList {nt : ℕ}
    (symbols : List (Fin nt)) :
    decodeFinListExact nt symbols.length (encodeFinList symbols) =
      some symbols := by
  unfold decodeFinListExact
  rw [show decodeFinBlocks nt symbols.length (encodeFinList symbols) =
      some (symbols, ([] : List Bool)) by
        simpa using
          (decodeFinBlocks_encodeFinList_append symbols ([] : List Bool))]
  simp

@[simp] theorem encodeFinList_length {nt : ℕ}
    (symbols : List (Fin nt)) :
    (encodeFinList symbols).length =
      symbols.length + (symbols.map fun a => a.val).sum := by
  induction symbols with
  | nil => simp [encodeFinList]
  | cons a symbols ih =>
      simp only [encodeFinList, List.length_append, encodeFin_length,
        List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- Number of delimiter cells in a binary word.  This is used only to recover
the number of encoded finite symbols from an unframed concatenation. -/
def falseCount : List Bool → ℕ
  | [] => 0
  | false :: rest => 1 + falseCount rest
  | true :: rest => falseCount rest

@[simp] theorem falseCount_append (left right : List Bool) :
    falseCount (left ++ right) = falseCount left + falseCount right := by
  induction left with
  | nil => simp [falseCount]
  | cons bit left ih =>
      cases bit <;> simp [falseCount, ih, Nat.add_assoc]

@[simp] theorem falseCount_replicate_true (n : ℕ) :
    falseCount (List.replicate n true) = 0 := by
  induction n with
  | zero => simp [falseCount]
  | succ n ih => simp [List.replicate_succ, falseCount, ih]

@[simp] theorem falseCount_encodeFin {nt : ℕ} (a : Fin nt) :
    falseCount (encodeFin a) = 1 := by
  rw [encodeFin, falseCount_append]
  simp [falseCount]

@[simp] theorem falseCount_encodeFinList {nt : ℕ}
    (symbols : List (Fin nt)) :
    falseCount (encodeFinList symbols) = symbols.length := by
  induction symbols with
  | nil => simp [encodeFinList, falseCount]
  | cons a symbols ih =>
      simp [encodeFinList, ih, Nat.add_comm]

theorem encodeFin_injective {nt : ℕ} : Function.Injective
    (encodeFin : Fin nt → List Bool) := by
  intro a b hab
  have hdecoded := congrArg (decodeFinPrefix nt) hab
  have ha : decodeFinPrefix nt (encodeFin a) = some (a, ([] : List Bool)) :=
    by simpa using (decodeFinPrefix_encodeFin_append a ([] : List Bool))
  have hb : decodeFinPrefix nt (encodeFin b) = some (b, ([] : List Bool)) :=
    by simpa using (decodeFinPrefix_encodeFin_append b ([] : List Bool))
  rw [ha, hb] at hdecoded
  exact congrArg Prod.fst (Option.some.inj hdecoded)

theorem encodeFinList_injective {nt : ℕ} : Function.Injective
    (encodeFinList : List (Fin nt) → List Bool) := by
  intro xs ys hxy
  have hlength : xs.length = ys.length := by
    have hcount := congrArg falseCount hxy
    simpa using hcount
  have hx : decodeFinBlocks nt xs.length (encodeFinList xs) = some (xs, []) :=
    by simpa using (decodeFinBlocks_encodeFinList_append xs ([] : List Bool))
  have hy : decodeFinBlocks nt xs.length (encodeFinList ys) = some (ys, []) :=
    by simpa [hlength] using
      (decodeFinBlocks_encodeFinList_append ys ([] : List Bool))
  have hoptions : some (xs, ([] : List Bool)) = some (ys, ([] : List Bool)) := by
    calc
      some (xs, ([] : List Bool)) =
          decodeFinBlocks nt xs.length (encodeFinList xs) := hx.symm
      _ = decodeFinBlocks nt xs.length (encodeFinList ys) := congrArg _ hxy
      _ = some (ys, ([] : List Bool)) := hy
  exact congrArg Prod.fst (Option.some.inj hoptions)

/-- Realize a finite-alphabet word on the existing binary part of the
three-symbol physical tape. -/
def encodeFinListTape {nt : ℕ} (symbols : List (Fin nt)) :
    List ULogProgram.Tape :=
  (encodeFinList symbols).map ULogProgram.bitTape

@[simp] theorem encodeFinListTape_length {nt : ℕ}
    (symbols : List (Fin nt)) :
    (encodeFinListTape symbols).length =
      symbols.length + (symbols.map fun a => a.val).sum := by
  simp [encodeFinListTape]

/-- No block codec cell uses the third physical tape symbol. -/
theorem encodeFinListTape_symbols {nt : ℕ} (symbols : List (Fin nt))
    (cell : ULogProgram.Tape)
    (hcell : cell ∈ encodeFinListTape symbols) :
    cell = MStarConcreteAlphabet.zero ∨ cell = MStarConcreteAlphabet.one := by
  simp only [encodeFinListTape, List.mem_map] at hcell
  obtain ⟨bit, -, rfl⟩ := hcell
  cases bit <;> simp [ULogProgram.bitTape]

end PakFixedPolyomino.ULogSourceTimedNormalizer
