import PakFixedPolyomino.ULogTapeLayout
import Mathlib.Tactic

/-!
# Decoding the physical `U_log` tape layout

The round trips here turn the layout into an actual `Encoding` of clocked
semantic configurations over the fixed 53-letter core alphabet.
-/

namespace PakFixedPolyomino.ULogTapeDecoding

set_option maxHeartbeats 2000000

open ULogAlphabet ULogBytecode ULogTapeLayout

abbrev CoreTape := MStarConcreteAlphabet.CoreTape

theorem ulog_symbol_ne {a b : ULogLetter} (h : a ≠ b) :
    ulogCore a ≠ ulogCore b := by
  intro hab
  exact h (ulogCore_injective hab)

def decodeUnary (zero endMark : CoreTape) :
    List CoreTape → Option (ℕ × List CoreTape)
  | [] => none
  | x :: xs =>
      if x = endMark then some (0, xs)
      else if x = zero then
        (decodeUnary zero endMark xs).map fun (n, rest) => (n + 1, rest)
      else none

@[simp] theorem decodeUnary_encode_prefix (zero endMark : CoreTape)
    (hne : zero ≠ endMark) (n : ℕ) (tail : List CoreTape) :
    decodeUnary zero endMark (encodeUnary zero endMark n ++ tail) =
      some (n, tail) := by
  induction n with
  | zero => simp [encodeUnary, decodeUnary]
  | succ n ih =>
      rw [show encodeUnary zero endMark (n + 1) =
          zero :: encodeUnary zero endMark n by
        simp [encodeUnary, List.replicate_succ, List.append_assoc]]
      simp [decodeUnary, hne, ih]

def codeZeroCore : CoreTape := ulogCore ULogAlphabet.codeZero
def codeOneCore : CoreTape := ulogCore ULogAlphabet.codeOne
def codeEndCore : CoreTape := ulogCore ULogAlphabet.codeEnd

@[simp] theorem codeZero_ne_codeEnd : codeZeroCore ≠ codeEndCore := by
  native_decide
@[simp] theorem codeOne_ne_codeEnd : codeOneCore ≠ codeEndCore := by
  native_decide
@[simp] theorem codeOne_ne_codeZero : codeOneCore ≠ codeZeroCore := by
  native_decide

def decodeCodeBits : List CoreTape → Option (List Bool × List CoreTape)
  | [] => none
  | x :: xs =>
      if x = codeEndCore then some ([], xs)
      else if x = codeZeroCore then
        (decodeCodeBits xs).map fun (bits, rest) => (false :: bits, rest)
      else if x = codeOneCore then
        (decodeCodeBits xs).map fun (bits, rest) => (true :: bits, rest)
      else none

@[simp] theorem decodeCodeBits_encode_prefix (bits : List Bool)
    (tail : List CoreTape) :
    decodeCodeBits (encodeCodeBits bits ++ codeEndCore :: tail) =
      some (bits, tail) := by
  induction bits with
  | nil =>
      change decodeCodeBits (codeEndCore :: tail) = some ([], tail)
      simp [decodeCodeBits]
  | cons b bits ih =>
      cases b with
      | false =>
          change decodeCodeBits
            (codeZeroCore :: (encodeCodeBits bits ++ codeEndCore :: tail)) = _
          simp [decodeCodeBits, ih]
      | true =>
          change decodeCodeBits
            (codeOneCore :: (encodeCodeBits bits ++ codeEndCore :: tail)) = _
          simp [decodeCodeBits, ih]

@[simp] theorem decodeCodeBits_encode_prefix_core (bits : List Bool)
    (tail : List CoreTape) :
    decodeCodeBits
        (encodeCodeBits bits ++ ulogCore ULogAlphabet.codeEnd :: tail) =
      some (bits, tail) := by
  exact decodeCodeBits_encode_prefix bits tail

def dataZeroCore : CoreTape := ulogCore ULogAlphabet.dataZero
def dataSepCore : CoreTape := ulogCore ULogAlphabet.dataSep
def dataEndCore : CoreTape := ulogCore ULogAlphabet.dataEnd

@[simp] theorem dataSep_ne_dataEnd : dataSepCore ≠ dataEndCore := by
  native_decide
@[simp] theorem dataZero_ne_dataEnd : dataZeroCore ≠ dataEndCore := by
  native_decide
@[simp] theorem dataZero_ne_dataSep : dataZeroCore ≠ dataSepCore := by
  native_decide

def decodeNatListAux (current : ℕ) (acc : List ℕ) :
    List CoreTape → Option (List ℕ × List CoreTape)
  | [] => none
  | x :: xs =>
      if x = dataEndCore then some (acc.reverse, xs)
      else if x = dataSepCore then decodeNatListAux 0 (current :: acc) xs
      else if x = dataZeroCore then decodeNatListAux (current + 1) acc xs
      else none

def decodeNatListPrefix (tape : List CoreTape) :
    Option (List ℕ × List CoreTape) :=
  decodeNatListAux 0 [] tape

theorem decodeNatListAux_zeros (current : ℕ) (acc : List ℕ)
    (n : ℕ) (rest : List CoreTape) :
    decodeNatListAux current acc
        (List.replicate n dataZeroCore ++ dataSepCore :: rest) =
      decodeNatListAux 0 ((current + n) :: acc) rest := by
  induction n generalizing current with
  | zero =>
      simp [decodeNatListAux]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, decodeNatListAux,
        dataZero_ne_dataEnd, if_false, dataZero_ne_dataSep]
      rw [ih]
      rw [show current + 1 + n = current + (n + 1) by omega]
      simp

@[simp] theorem decodeNatListPrefix_encode_prefix (xs : List ℕ)
    (tail : List CoreTape) :
    decodeNatListPrefix (encodeNatList xs ++ tail) = some (xs, tail) := by
  unfold decodeNatListPrefix
  have aux : ∀ (ys : List ℕ) (acc : List ℕ),
      decodeNatListAux 0 acc (encodeNatList ys ++ tail) =
        some (acc.reverse ++ ys, tail) := by
    intro ys
    induction ys with
    | nil =>
        intro acc
        simp [encodeNatList, decodeNatListAux, dataEndCore]
    | cons n ns ih =>
        intro acc
        rw [show encodeNatList (n :: ns) ++ tail =
            List.replicate n dataZeroCore ++
              dataSepCore :: (encodeNatList ns ++ tail) by
          simp [encodeNatList, encodeUnary, dataZeroCore, dataSepCore,
            List.append_assoc]]
        rw [decodeNatListAux_zeros]
        simpa [List.append_assoc] using ih (n :: acc)
  simpa using aux xs []

def expect (symbol : CoreTape) :
    List CoreTape → Option (List CoreTape)
  | x :: xs => if x = symbol then some xs else none
  | [] => none

@[simp] theorem expect_cons (symbol : CoreTape) (tail : List CoreTape) :
    expect symbol (symbol :: tail) = some tail := by
  simp [expect]

@[simp] theorem decodeUnary_state (n : ℕ) (tail : List CoreTape) :
    decodeUnary (ulogCore stateZero) (ulogCore stateOne)
        (encodeUnary (ulogCore stateZero) (ulogCore stateOne) n ++ tail) =
      some (n, tail) :=
  decodeUnary_encode_prefix _ _ (ulog_symbol_ne (by native_decide)) n tail

@[simp] theorem decodeUnary_data (n : ℕ) (tail : List CoreTape) :
    decodeUnary (ulogCore dataZero) (ulogCore dataSep)
        (encodeUnary (ulogCore dataZero) (ulogCore dataSep) n ++ tail) =
      some (n, tail) :=
  decodeUnary_encode_prefix _ _ (ulog_symbol_ne (by native_decide)) n tail

@[simp] theorem decodeUnary_clock (n : ℕ) (tail : List CoreTape) :
    decodeUnary (ulogCore clockZero) (ulogCore clockOne)
        (encodeUnary (ulogCore clockZero) (ulogCore clockOne) n ++ tail) =
      some (n, tail) :=
  decodeUnary_encode_prefix _ _ (ulog_symbol_ne (by native_decide)) n tail

def decodeBasePrefix (tape : List CoreTape) :
    Option (ULogSemantics.Config × List CoreTape) := do
  let tape ← expect (ulogCore pcMark) tape
  let (programBits, tape) ← decodeCodeBits tape
  let program ← decodeProgram programBits
  let (state, tape) ← decodeUnary (ulogCore stateZero)
    (ulogCore stateOne) tape
  let tape ← expect (ulogCore stateSep) tape
  let (leftRev, tape) ← decodeNatListPrefix tape
  let tape ← expect (ulogCore headLeft) tape
  let (focus, tape) ← decodeUnary dataZeroCore dataSepCore tape
  let tape ← expect (ulogCore headHere) tape
  let (right, tape) ← decodeNatListPrefix tape
  let tape ← expect (ulogCore headRight) tape
  let tape ← expect (ulogCore returnMark) tape
  pure (⟨program, state, leftRev, focus, right⟩, tape)

@[simp] theorem decodeBasePrefix_encode_prefix (c : ULogSemantics.Config)
    (tail : List CoreTape) :
    decodeBasePrefix (encodeBase c ++ tail) = some (c, tail) := by
  have hstate : ulogCore stateZero ≠ ulogCore stateOne :=
    ulog_symbol_ne (by native_decide)
  have hdata : dataZeroCore ≠ dataSepCore := dataZero_ne_dataSep
  simp [decodeBasePrefix, encodeBase, codeEndCore, dataZeroCore,
    dataSepCore, hstate, hdata, List.append_assoc]

def decodeClockedPrefix (tape : List CoreTape) :
    Option (ULogClocked.Config × List CoreTape) := do
  let (base, tape) ← decodeBasePrefix tape
  let (remaining, tape) ← decodeUnary (ulogCore clockZero)
    (ulogCore clockOne) tape
  let tape ← expect (ulogCore clockSep) tape
  pure (⟨base, remaining⟩, tape)

@[simp] theorem decodeClockedPrefix_encode_prefix (c : ULogClocked.Config)
    (tail : List CoreTape) :
    decodeClockedPrefix (encodeClocked c ++ tail) = some (c, tail) := by
  simp [decodeClockedPrefix, encodeClocked, List.append_assoc]

def decodeClocked (tape : List CoreTape) : Option ULogClocked.Config :=
  (decodeClockedPrefix tape).map Prod.fst

@[simp] theorem decodeClocked_encode (c : ULogClocked.Config) :
    decodeClocked (encodeClocked c) = some c := by
  unfold decodeClocked
  rw [show encodeClocked c = encodeClocked c ++ [] by simp]
  rw [decodeClockedPrefix_encode_prefix]
  rfl

def configEncoding : Computability.Encoding ULogClocked.Config CoreTape where
  encode := encodeClocked
  decode := decodeClocked
  decode_encode := decodeClocked_encode

theorem encodeClocked_injective : Function.Injective encodeClocked :=
  configEncoding.encode_injective

def encodeClockedList (cs : List ULogClocked.Config) : List CoreTape :=
  encodeUnary (ulogCore branchZero) (ulogCore branchOne) cs.length ++
    cs.flatMap encodeClocked

def decodeClockedN : ℕ → List CoreTape →
    Option (List ULogClocked.Config × List CoreTape)
  | 0, tape => some ([], tape)
  | n + 1, tape => do
      let (c, tape) ← decodeClockedPrefix tape
      let (cs, tape) ← decodeClockedN n tape
      pure (c :: cs, tape)

@[simp] theorem decodeClockedN_encode_prefix (cs : List ULogClocked.Config)
    (tail : List CoreTape) :
    decodeClockedN cs.length (cs.flatMap encodeClocked ++ tail) =
      some (cs, tail) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [decodeClockedN, List.append_assoc, ih]

def decodeClockedList (tape : List CoreTape) :
    Option (List ULogClocked.Config) := do
  let (n, tape) ← decodeUnary (ulogCore branchZero)
    (ulogCore branchOne) tape
  (decodeClockedN n tape).map Prod.fst

@[simp] theorem decodeClockedList_encode (cs : List ULogClocked.Config) :
    decodeClockedList (encodeClockedList cs) = some cs := by
  have hbranch : ulogCore branchZero ≠ ulogCore branchOne :=
    ulog_symbol_ne (by native_decide)
  unfold decodeClockedList encodeClockedList
  change (decodeUnary (ulogCore branchZero) (ulogCore branchOne)
      (encodeUnary (ulogCore branchZero) (ulogCore branchOne) cs.length ++
        cs.flatMap encodeClocked)).bind _ = some cs
  rw [decodeUnary_encode_prefix _ _ hbranch]
  change Option.map Prod.fst
      (decodeClockedN cs.length (cs.flatMap encodeClocked)) = some cs
  rw [show cs.flatMap encodeClocked = cs.flatMap encodeClocked ++ [] by simp,
    decodeClockedN_encode_prefix]
  rfl

def configListEncoding :
    Computability.Encoding (List ULogClocked.Config) CoreTape where
  encode := encodeClockedList
  decode := decodeClockedList
  decode_encode := decodeClockedList_encode

end PakFixedPolyomino.ULogTapeDecoding
