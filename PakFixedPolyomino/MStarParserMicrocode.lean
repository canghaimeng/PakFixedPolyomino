import PakFixedPolyomino.MStarOuterProgram
import PakFixedPolyomino.ConcretePakSideEncoding
import Mathlib.Tactic

/-!
# Deterministic one-tape parser microcode for the accepted side language

The accepted proof describes a binary run counter but does not fix its finite
control table.  This module chooses an equivalent, simpler crossing-off
implementation of the same language:

* cross off the first 72 padding zeros;
* for every zero in the length run, cross off 72 more padding zeros;
* pair every length marker with exactly one payload bit;
* require a leading one followed immediately by a high-zero `work` letter.

It uses exactly the eight scratch letters already reserved by the accepted
construction.  The copy phase begins at `copyStart`; its transition table is
kept separate.
-/

namespace PakFixedPolyomino.MStarParserMicrocode

open OneTapeTableau FiniteOneTapeProgram MStarOuterProgram

/-- Two blocks of 73 counter states plus eighteen named control states.  The
sum representation keeps counter induction definitional in the refinement
proof while retaining the same 164-state alphabet. -/
abbrev ParserState := (Fin 73 ⊕ Fin 73) ⊕ Fin 18

def fixed (k : Fin 73) : ParserState := .inl (.inl k)
def cross (k : Fin 73) : ParserState := .inl (.inr k)
def control (k : Fin 18) : ParserState := .inr k

def scanPad : ParserState := control ⟨0, by decide⟩
def scanLen : ParserState := control ⟨1, by decide⟩
def seekSepPad : ParserState := control ⟨2, by decide⟩
def seekUnmarkedPad : ParserState := control ⟨3, by decide⟩
def returnSepPad : ParserState := control ⟨4, by decide⟩
def returnLen : ParserState := control ⟨5, by decide⟩
def checkSeekSepPad : ParserState := control ⟨6, by decide⟩
def checkPad : ParserState := control ⟨7, by decide⟩
def checkReturnSepPad : ParserState := control ⟨8, by decide⟩
def checkReturnSepLen : ParserState := control ⟨9, by decide⟩
def findLen : ParserState := control ⟨10, by decide⟩
def seekSepLenForPayload : ParserState := control ⟨11, by decide⟩
def seekPayload : ParserState := control ⟨12, by decide⟩
def returnSepLenAfterPayload : ParserState := control ⟨13, by decide⟩
def verifySeekSepLen : ParserState := control ⟨14, by decide⟩
def verifyPayload : ParserState := control ⟨15, by decide⟩
def verifyHigh : ParserState := control ⟨16, by decide⟩
def copyStart : ParserState := control ⟨17, by decide⟩

def stateCode : ParserState → Fin 164
  | .inl (.inl k) => ⟨k.1, by omega⟩
  | .inl (.inr k) => ⟨73 + k.1, by omega⟩
  | .inr k => ⟨146 + k.1, by omega⟩

@[simp] theorem card_parserState : Fintype.card ParserState = 164 := by simp

theorem padding_crossing_decomposition (m : ℕ) :
    ConcretePakSide.paddingLength m = 72 + 72 * m := by
  simp [ConcretePakSide.paddingLength]
  omega

/-- After pairing `k` length markers, precisely `72*(m-k)` non-fixed
padding cells remain to be crossed. -/
theorem remaining_padding_blocks {m k : ℕ} (hk : k ≤ m) :
    ConcretePakSide.paddingLength m - (72 + 72 * k) = 72 * (m - k) := by
  simp [ConcretePakSide.paddingLength]
  omega

theorem all_padding_crossed (m : ℕ) :
    ConcretePakSide.paddingLength m - (72 + 72 * m) = 0 := by
  rw [padding_crossing_decomposition]
  omega

def padDone : Tape UTape := .scratch 0
def sepPad : Tape UTape := .scratch 1
def lenDone : Tape UTape := .scratch 2
def sepLen : Tape UTape := .scratch 3
def pairedLen : Tape UTape := .scratch 4
def payloadZero : Tape UTape := .scratch 5
def payloadOne : Tape UTape := .scratch 6
/-- Reused by disjoint phases: the low padding endpoint during run checking,
then the leading-one marker during payload checking. -/
def endpointMark : Tape UTape := .scratch 7

variable {UState UTape : Type*}
variable [Fintype UState] [Fintype UTape]
variable [DecidableEq UState] [DecidableEq UTape]

abbrev OuterState (UState : Type*) := MStarOuterProgram.State ParserState UState
abbrev OuterTape (UTape : Type*) := MStarOuterProgram.Tape UTape

def go (write : OuterTape UTape) (target : ParserState) (move : Move) :
    Action (OuterState UState) (OuterTape UTape) :=
  { write := write, target := .parser target, move := move }

def reject (x : OuterTape UTape) : Action (OuterState UState) (OuterTape UTape) :=
  { write := x, target := .reject, move := .stay }

def next73 (k : Fin 73) (h : k.1 < 72) : Fin 73 := ⟨k.1 + 1, by omega⟩

def coreEq (a b : UTape) : Bool := decide (a = b)

/-- The complete deterministic M3 parser.  `copyStart` intentionally has no
rule here; M4 will extend that single state with its copier microcode. -/
def step (zero one work : UTape) (p : ParserState) (x : OuterTape UTape) :
    Option (Action (OuterState UState) (OuterTape UTape)) :=
  if hfix : (stateCode p).1 < 73 then
    let k : Fin 73 := ⟨(stateCode p).1, hfix⟩
    if hk : k.1 < 72 then
      match x with
      | .core a =>
          if coreEq a zero then
            some (go (if k.1 = 0 then endpointMark else padDone)
              (fixed (next73 k hk)) .right)
          else some (reject x)
      | _ => some (reject x)
    else some (go x scanPad .stay)
  else if hcross : (stateCode p).1 < 146 then
    let k : Fin 73 := ⟨(stateCode p).1 - 73, by omega⟩
    if hk : k.1 < 72 then
      match x with
      | .core a =>
          if coreEq a zero then
            some (go padDone (cross (next73 k hk)) .left)
          else some (reject x)
      | _ => some (reject x)
    else some (go x returnSepPad .stay)
  else if p = scanPad then
    match x with
    | .core a =>
        if coreEq a zero then some (go x scanPad .right)
        else if coreEq a one then some (go sepPad scanLen .right)
        else some (reject x)
    | _ => some (reject x)
  else if p = scanLen then
    match x with
    | .core a =>
        if coreEq a zero then some (go lenDone seekSepPad .left)
        else if coreEq a one then some (go sepLen checkSeekSepPad .left)
        else some (reject x)
    | _ => some (reject x)
  else if p = seekSepPad then
    if x = lenDone then some (go x seekSepPad .left)
    else if x = sepPad then some (go x seekUnmarkedPad .left)
    else some (reject x)
  else if p = seekUnmarkedPad then
    if x = padDone then some (go x seekUnmarkedPad .left)
    else match x with
      | .core a =>
          if coreEq a zero then some (go padDone (cross ⟨1, by decide⟩) .left)
          else some (reject x)
      | _ => some (reject x)
  else if p = returnSepPad then
    if x = sepPad then some (go x returnLen .right)
    else match x with
      | .core a =>
          if coreEq a zero then some (go x returnSepPad .right) else some (reject x)
      | .scratch 0 => some (go x returnSepPad .right)
      | _ => some (reject x)
  else if p = returnLen then
    if x = lenDone then some (go x returnLen .right)
    else some (go x scanLen .stay)
  else if p = checkSeekSepPad then
    if x = lenDone then some (go x checkSeekSepPad .left)
    else if x = sepPad then some (go x checkPad .left)
    else some (reject x)
  else if p = checkPad then
    if x = padDone then some (go x checkPad .left)
    else if x = endpointMark then some (go x checkReturnSepPad .right)
    else some (reject x)
  else if p = checkReturnSepPad then
    if x = sepPad then some (go x checkReturnSepLen .right)
    else if x = padDone then some (go x checkReturnSepPad .right)
    else some (reject x)
  else if p = checkReturnSepLen then
    if x = lenDone then some (go x checkReturnSepLen .right)
    else if x = sepLen then some (go x findLen .left)
    else some (reject x)
  else if p = findLen then
    if x = pairedLen then some (go x findLen .left)
    else if x = lenDone then some (go pairedLen seekSepLenForPayload .right)
    else if x = sepPad then some (go x verifySeekSepLen .right)
    else some (reject x)
  else if p = seekSepLenForPayload then
    if x = pairedLen ∨ x = lenDone then some (go x seekSepLenForPayload .right)
    else if x = sepLen then some (go x seekPayload .right)
    else some (reject x)
  else if p = seekPayload then
    if x = payloadZero ∨ x = payloadOne then some (go x seekPayload .right)
    else match x with
      | .core a =>
          if coreEq a zero then some (go payloadZero returnSepLenAfterPayload .left)
          else if coreEq a one then some (go payloadOne returnSepLenAfterPayload .left)
          else some (reject x)
      | _ => some (reject x)
  else if p = returnSepLenAfterPayload then
    if x = payloadZero ∨ x = payloadOne then
      some (go x returnSepLenAfterPayload .left)
    else if x = sepLen then some (go x findLen .left)
    else some (reject x)
  else if p = verifySeekSepLen then
    if x = pairedLen then some (go x verifySeekSepLen .right)
    else if x = sepLen then some (go x verifyPayload .right)
    else some (reject x)
  else if p = verifyPayload then
    if x = payloadZero ∨ x = payloadOne then some (go x verifyPayload .right)
    else match x with
      | .core a =>
          if coreEq a one then some (go endpointMark verifyHigh .right)
          else some (reject x)
      | _ => some (reject x)
  else if p = verifyHigh then
    match x with
    | .core a =>
        if coreEq a work then some (go x copyStart .stay) else some (reject x)
    | _ => some (reject x)
  else none

theorem fixed_seventy_two_enters_scan (zero one work : UTape)
    (x : OuterTape UTape) :
    step (UState := UState) zero one work (fixed ⟨72, by decide⟩) x =
      some (go x scanPad .stay) := by
  rfl

theorem copyStart_has_no_parser_rule (zero one work : UTape)
    (x : OuterTape UTape) :
    step (UState := UState) zero one work copyStart x = none := by
  rfl

/-- The microcode is a literal deterministic rule table in the outer shell. -/
def attach
    (uProgram : Program UState UTape) (uAccept uReject uStart : UState)
    (zero one work : UTape) :
    MStarOuterProgram.Data (ParserState := ParserState)
      (UState := UState) (UTape := UTape) where
  uProgram := uProgram
  uAccept := uAccept
  uReject := uReject
  uStart := uStart
  parserStart := fixed 0
  zero := zero
  one := one
  work := work
  parserStep := step zero one work

theorem attached_parser_slot_one_empty
    (uProgram : Program UState UTape) (uAccept uReject uStart : UState)
    (zero one work : UTape) (p : ParserState) (x : OuterTape UTape) :
    (MStarOuterProgram.program (attach uProgram uAccept uReject uStart zero one work)).rule
      (.parser p) x 1 = none :=
  MStarOuterProgram.parser_deterministic_slot_one _ p x

end PakFixedPolyomino.MStarParserMicrocode
