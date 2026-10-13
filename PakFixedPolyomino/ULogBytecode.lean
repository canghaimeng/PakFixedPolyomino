import PakFixedPolyomino.ULogAlphabet
import PakFixedPolyomino.FiniteOneTapeProgram
import Mathlib.Tactic

/-!
# Self-delimiting bytecode for the fixed universal source

This is the data language interpreted by `U_log`.  Natural fields use unary
`0^n 1`, so every instruction is decoded without an external length oracle.
The program starts with its instruction count.  These definitions are fully
executable and the round-trip theorems are the first half of the later
universal-interpreter refinement.
-/

namespace PakFixedPolyomino.ULogBytecode

open OneTapeTableau

def encodeNatField (n : ℕ) : List Bool :=
  List.replicate n false ++ [true]

@[simp] theorem length_encodeNatField (n : ℕ) :
    (encodeNatField n).length = n + 1 := by
  simp [encodeNatField]

def decodeNatField : List Bool → Option (ℕ × List Bool)
  | [] => none
  | true :: xs => some (0, xs)
  | false :: xs =>
      (decodeNatField xs).map fun (n, rest) => (n + 1, rest)

@[simp] theorem decodeNatField_encode_prefix (n : ℕ) (tail : List Bool) :
    decodeNatField (encodeNatField n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show encodeNatField (n + 1) = false :: encodeNatField n by
        simp [encodeNatField, List.replicate_succ, List.append_assoc]]
      simp [decodeNatField, ih]

def encodeMove : Move → List Bool
  | .left => [false, false]
  | .stay => [false, true]
  | .right => [true, false]

def decodeMove : List Bool → Option (Move × List Bool)
  | false :: false :: xs => some (.left, xs)
  | false :: true :: xs => some (.stay, xs)
  | true :: false :: xs => some (.right, xs)
  | _ => none

@[simp] theorem decodeMove_encode_prefix (m : Move) (tail : List Bool) :
    decodeMove (encodeMove m ++ tail) = some (m, tail) := by
  cases m <;> rfl

structure ActionCode where
  write : ℕ
  target : ℕ
  move : Move
  deriving DecidableEq, Repr

def encodeAction (a : ActionCode) : List Bool :=
  encodeNatField a.write ++ encodeNatField a.target ++ encodeMove a.move

def decodeAction (bits : List Bool) : Option (ActionCode × List Bool) := do
  let (write, bits) ← decodeNatField bits
  let (target, bits) ← decodeNatField bits
  let (move, bits) ← decodeMove bits
  pure (⟨write, target, move⟩, bits)

@[simp] theorem decodeAction_encode_prefix (a : ActionCode)
    (tail : List Bool) :
    decodeAction (encodeAction a ++ tail) = some (a, tail) := by
  cases a
  simp [encodeAction, decodeAction, List.append_assoc]

structure RuleCode where
  source : ℕ
  read : ℕ
  slot : Bool
  action : ActionCode
  deriving DecidableEq, Repr

def encodeRule (r : RuleCode) : List Bool :=
  encodeNatField r.source ++ encodeNatField r.read ++
    [r.slot] ++ encodeAction r.action

def decodeBit : List Bool → Option (Bool × List Bool)
  | [] => none
  | b :: bits => some (b, bits)

def decodeRule (bits : List Bool) : Option (RuleCode × List Bool) := do
  let (source, bits) ← decodeNatField bits
  let (read, bits) ← decodeNatField bits
  let (slot, bits) ← decodeBit bits
  let (action, bits) ← decodeAction bits
  pure (⟨source, read, slot, action⟩, bits)

@[simp] theorem decodeRule_encode_prefix (r : RuleCode) (tail : List Bool) :
    decodeRule (encodeRule r ++ tail) = some (r, tail) := by
  cases r
  simp [encodeRule, decodeRule, decodeBit, List.append_assoc]

def encodeRules : List RuleCode → List Bool
  | [] => []
  | r :: rs => encodeRule r ++ encodeRules rs

def decodeRules : ℕ → List Bool → Option (List RuleCode × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (r, bits) ← decodeRule bits
      let (rs, bits) ← decodeRules n bits
      pure (r :: rs, bits)

@[simp] theorem decodeRules_encode_prefix (rs : List RuleCode)
    (tail : List Bool) :
    decodeRules rs.length (encodeRules rs ++ tail) = some (rs, tail) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp [encodeRules, decodeRules, List.append_assoc, ih]

abbrev ProgramCode := List RuleCode

def encodeProgram (p : ProgramCode) : List Bool :=
  encodeNatField p.length ++ encodeRules p

def decodeProgramPrefix (bits : List Bool) :
    Option (ProgramCode × List Bool) := do
  let (n, bits) ← decodeNatField bits
  decodeRules n bits

def decodeProgram (bits : List Bool) : Option ProgramCode := do
  let (p, rest) ← decodeProgramPrefix bits
  if rest = [] then pure p else none

@[simp] theorem decodeProgramPrefix_encode_prefix (p : ProgramCode)
    (tail : List Bool) :
    decodeProgramPrefix (encodeProgram p ++ tail) = some (p, tail) := by
  simp [decodeProgramPrefix, encodeProgram, List.append_assoc]

@[simp] theorem decodeProgram_encode (p : ProgramCode) :
    decodeProgram (encodeProgram p) = some p := by
  unfold decodeProgram
  rw [show encodeProgram p = encodeProgram p ++ [] by simp,
    decodeProgramPrefix_encode_prefix]
  rfl

theorem encodeProgram_injective : Function.Injective encodeProgram := by
  intro p q h
  have hp := decodeProgram_encode p
  have hq := decodeProgram_encode q
  rw [h] at hp
  rw [hq] at hp
  exact Option.some.inj hp.symm

/-- A length-prefixed payload followed by arbitrary ignored clock padding. -/
def encodePayload (input padding : List Bool) : List Bool :=
  encodeNatField input.length ++ input ++ padding

@[simp] theorem length_encodePayload (input padding : List Bool) :
    (encodePayload input padding).length =
      2 * input.length + padding.length + 1 := by
  simp [encodePayload]
  omega

def decodePayload (bits : List Bool) : Option (List Bool) := do
  let (n, bits) ← decodeNatField bits
  pure (bits.take n)

def decodePayloadWithPadding (bits : List Bool) :
    Option (List Bool × ℕ) := do
  let (n, bits) ← decodeNatField bits
  pure (bits.take n, (bits.drop n).length)

@[simp] theorem decodePayload_encode (input padding : List Bool) :
    decodePayload (encodePayload input padding) = some input := by
  simp [decodePayload, encodePayload, List.append_assoc]

@[simp] theorem decodePayloadWithPadding_encode (input padding : List Bool) :
    decodePayloadWithPadding (encodePayload input padding) =
      some (input, padding.length) := by
  simp [decodePayloadWithPadding, encodePayload, List.append_assoc]

def slotIndex : Bool → Fin 2
  | false => 0
  | true => 1

def ruleMatches (q read : ℕ) (slot : Bool) (r : RuleCode) : Bool :=
  decide (r.source = q ∧ r.read = read ∧ r.slot = slot)

def lookupRule (p : ProgramCode) (q read : ℕ) (slot : Bool) :
    Option ActionCode :=
  (p.find? (ruleMatches q read slot)).map RuleCode.action

theorem lookupRule_some_mem {p : ProgramCode} {q read : ℕ} {slot : Bool}
    {a : ActionCode} (h : lookupRule p q read slot = some a) :
    ∃ r ∈ p, r.source = q ∧ r.read = read ∧ r.slot = slot ∧
      r.action = a := by
  induction p with
  | nil => simp [lookupRule] at h
  | cons r rs ih =>
      by_cases hr : ruleMatches q read slot r = true
      · simp [lookupRule, List.find?, hr] at h
        subst a
        simp [ruleMatches] at hr
        exact ⟨r, by simp, hr.1, hr.2.1, hr.2.2, rfl⟩
      · have hr' : ruleMatches q read slot r = false := by
          cases hval : ruleMatches q read slot r <;> simp_all
        have htail : lookupRule rs q read slot = some a := by
          simpa only [lookupRule, List.find?_cons, hr', Bool.false_eq_true,
            if_false] using h
        rcases ih htail with ⟨s, hs, hq, hread, hslot, ha⟩
        exact ⟨s, by simp [hs], hq, hread, hslot, ha⟩

end PakFixedPolyomino.ULogBytecode
