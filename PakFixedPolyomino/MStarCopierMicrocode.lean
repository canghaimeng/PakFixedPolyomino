import PakFixedPolyomino.MStarParserSoundness
import Mathlib.Tactic

/-!
# Concrete copier microcode after `copyStart`

This module extends the checked parser control by a finite copier control.
The first implemented kernel is the in-place unary doubling routine used to
create the two buffers of length `2^(8*(m+1))+1`.  A counter block is delimited
by `markL, markR`; `scratch 0` is an unprocessed cell and `scratch 1` is a
processed/appended cell.  One pass changes every old cell to `scratch 1` and
appends one further `scratch 1`, so newly appended cells are not mistaken for
old work.  The normalization pass changes the doubled block back to
`scratch 0`.  The `Fin 8` round component performs the literal eight doublings
of one exponent group.
-/

namespace PakFixedPolyomino.MStarCopierMicrocode

open OneTapeTableau FiniteOneTapeProgram MStarOuterProgram
open MStarParserMicrocode
open MStarConcreteAlphabet

inductive CopierState where
  | seedCell
  | seedBoundary
  | findOld : Fin 8 → CopierState
  | seekBoundary : Fin 8 → CopierState
  | placeBoundary : Fin 8 → CopierState
  | returnLeft : Fin 8 → CopierState
  | normalize : Fin 8 → CopierState
  | groupDone
  | groupSeekLen
  | groupReturn
  | finishReturn
  | counterToWork
  | payloadBoundary
  | payloadSeek
  | payloadCarry : Bool → CopierState
  | payloadPlace
  | payloadDoneReturn
  | finalSeekBoundary
  | rightBufferScan
  | finalReturn
  deriving DecidableEq, Fintype, Repr

abbrev Control := ParserState ⊕ CopierState
abbrev CopierOuterState (UState : Type*) := MStarOuterProgram.State Control UState
abbrev ConcreteTape := MStarOuterProgram.Tape CoreTape

def cellA : ConcreteTape := .scratch 0
def cellB : ConcreteTape := .scratch 1
def rightEnd : ConcreteTape := .scratch 2

def copyGo {UState : Type*} (write : ConcreteTape) (target : CopierState)
    (move : Move) : Action (CopierOuterState UState) ConcreteTape :=
  { write := write, target := .parser (.inr target), move := move }

def copyReject {UState : Type*} (x : ConcreteTape) :
    Action (CopierOuterState UState) ConcreteTape :=
  { write := x, target := .reject, move := .stay }

def copySim {UState : Type*} (uStart : UState) (write : ConcreteTape)
    (move : Move) : Action (CopierOuterState UState) ConcreteTape :=
  { write := write, target := .sim uStart, move := move }

def nextRound (r : Fin 8) (h : r.1 < 7) : Fin 8 := ⟨r.1 + 1, by omega⟩

/-- Literal local transition table for seeding and eight unary doublings. -/
def copierStep {UState : Type*} (uStart : UState) (q : CopierState)
    (x : ConcreteTape) :
    Option (Action (CopierOuterState UState) ConcreteTape) :=
  match q with
  | .seedCell =>
      if x = .core work then some (copyGo cellA .seedBoundary .right)
      else some (copyReject x)
  | .seedBoundary =>
      if x = .core work then some (copyGo .markR (.returnLeft 0) .left)
      else some (copyReject x)
  | .findOld r =>
      if x = cellA then some (copyGo cellB (.seekBoundary r) .right)
      else if x = cellB then some (copyGo x (.findOld r) .right)
      else if x = .markR then some (copyGo x (.normalize r) .left)
      else some (copyReject x)
  | .seekBoundary r =>
      if x = cellA ∨ x = cellB then some (copyGo x (.seekBoundary r) .right)
      else if x = .markR then some (copyGo cellB (.placeBoundary r) .right)
      else some (copyReject x)
  | .placeBoundary r =>
      if x = .core work then some (copyGo .markR (.returnLeft r) .left)
      else some (copyReject x)
  | .returnLeft r =>
      if x = cellA ∨ x = cellB then some (copyGo x (.returnLeft r) .left)
      else if x = .markL then some (copyGo x (.findOld r) .right)
      else some (copyReject x)
  | .normalize r =>
      if x = cellB then some (copyGo cellA (.normalize r) .left)
      else if x = .markL then
        if h : r.1 < 7 then some (copyGo x (.findOld (nextRound r h)) .right)
        else some (copyGo x .groupDone .stay)
      else some (copyReject x)
  | .groupDone =>
      if x = .markL then some (copyGo x .groupSeekLen .left)
      else some (copyReject x)
  | .groupSeekLen =>
      if x = MStarParserMicrocode.endpointMark ∨
          x = MStarParserMicrocode.payloadZero ∨
          x = MStarParserMicrocode.payloadOne ∨ x = MStarParserMicrocode.sepLen ∨
          x = MStarParserMicrocode.lenDone then
        some (copyGo x .groupSeekLen .left)
      else if x = MStarParserMicrocode.pairedLen then
        some (copyGo MStarParserMicrocode.lenDone .groupReturn .right)
      else if x = MStarParserMicrocode.sepPad then
        some (copyGo x .finishReturn .right)
      else some (copyReject x)
  | .groupReturn =>
      if x = MStarParserMicrocode.lenDone ∨ x = MStarParserMicrocode.sepLen ∨
          x = MStarParserMicrocode.payloadZero ∨
          x = MStarParserMicrocode.payloadOne ∨
          x = MStarParserMicrocode.endpointMark then
        some (copyGo x .groupReturn .right)
      else if x = .markL then some (copyGo x (.findOld 0) .right)
      else some (copyReject x)
  | .finishReturn =>
      if x = MStarParserMicrocode.lenDone ∨ x = MStarParserMicrocode.sepLen ∨
          x = MStarParserMicrocode.payloadZero ∨
          x = MStarParserMicrocode.payloadOne ∨
          x = MStarParserMicrocode.endpointMark then
        some (copyGo x .finishReturn .right)
      else if x = .markL then some (copyGo x .counterToWork .right)
      else some (copyReject x)
  | .counterToWork =>
      if x = cellA then some (copyGo (.core work) .counterToWork .right)
      else if x = .markR then some (copyGo (.core work) .payloadBoundary .right)
      else some (copyReject x)
  | .payloadBoundary =>
      if x = .core work then some (copyGo .markR .payloadSeek .left)
      else some (copyReject x)
  | .payloadSeek =>
      if x = .core work ∨ x = .core zero ∨ x = .core one ∨
          x = .markL ∨ x = MStarParserMicrocode.endpointMark ∨
          x = MStarParserMicrocode.lenDone then
        some (copyGo x .payloadSeek .left)
      else if x = MStarParserMicrocode.payloadZero then
        some (copyGo MStarParserMicrocode.lenDone (.payloadCarry false) .right)
      else if x = MStarParserMicrocode.payloadOne then
        some (copyGo MStarParserMicrocode.lenDone (.payloadCarry true) .right)
      else if x = MStarParserMicrocode.sepLen then
        some (copyGo x .payloadDoneReturn .right)
      else some (copyReject x)
  | .payloadCarry b =>
      if x = MStarParserMicrocode.lenDone ∨
          x = MStarParserMicrocode.endpointMark ∨ x = .markL ∨
          x = .core work ∨ x = .core zero ∨ x = .core one then
        some (copyGo x (.payloadCarry b) .right)
      else if x = .markR then
        some (copyGo (.core (if b then one else zero))
          .payloadPlace .right)
      else some (copyReject x)
  | .payloadPlace =>
      if x = .core work then some (copyGo .markR .payloadSeek .left)
      else some (copyReject x)
  | .payloadDoneReturn =>
      if x = MStarParserMicrocode.lenDone ∨
          x = MStarParserMicrocode.endpointMark then
        some (copyGo x .payloadDoneReturn .right)
      else if x = .markL then some (copyGo x .finalSeekBoundary .right)
      else some (copyReject x)
  | .finalSeekBoundary =>
      if x = .core work ∨ x = .core zero ∨ x = .core one then
        some (copyGo x .finalSeekBoundary .right)
      else if x = .markR then some (copyGo (.core work) .rightBufferScan .right)
      else some (copyReject x)
  | .rightBufferScan =>
      if x = .core work then some (copyGo x .rightBufferScan .right)
      else if x = rightEnd then some (copyGo .markR .finalReturn .left)
      else some (copyReject x)
  | .finalReturn =>
      if x = .core work ∨ x = .core zero ∨ x = .core one then
        some (copyGo x .finalReturn .left)
      else if x = .markL then some (copySim uStart x .right)
      else some (copyReject x)

def liftState {UState : Type*} :
    MStarOuterProgram.State ParserState UState → CopierOuterState UState
  | .start => .start
  | .accept => .accept
  | .reject => .reject
  | .parser p => .parser (.inl p)
  | .sim q => .sim q

def liftAction {UState : Type*}
    (a : Action (MStarOuterProgram.State ParserState UState) ConcreteTape) :
    Action (CopierOuterState UState) ConcreteTape :=
  { write := a.write, target := liftState a.target, move := a.move }

/-- Combined parser/copier table.  The former parser terminal `copyStart`
becomes the unique entry into the copier and writes the permanent left
delimiter on the checked high-zero cell. -/
def step {UState : Type*} (uStart : UState) (q : Control) (x : ConcreteTape) :
    Option (Action (CopierOuterState UState) ConcreteTape) :=
  match q with
  | .inl p =>
      if p = copyStart then
        if x = .core work then some (copyGo .markL .seedCell .right)
        else some (copyReject x)
      else
        (MStarParserMicrocode.step (UState := UState) zero one work p x).map liftAction
  | .inr c => copierStep uStart c x

variable {UState : Type*}
variable [Fintype UState] [DecidableEq UState]

def attach (uProgram : Program UState CoreTape)
    (uAccept uReject uStart : UState) :
    MStarOuterProgram.Data (ParserState := Control)
      (UState := UState) (UTape := CoreTape) where
  uProgram := uProgram
  uAccept := uAccept
  uReject := uReject
  uStart := uStart
  parserStart := .inl (fixed 0)
  zero := zero
  one := one
  work := work
  parserStep := step uStart

@[simp] theorem card_copierState : Fintype.card CopierState = 56 := by
  native_decide

@[simp] theorem card_control : Fintype.card Control = 220 := by
  native_decide

theorem copyStart_enters_copier :
    step (UState := UState) uStart (.inl copyStart) (.core work) =
      some (copyGo .markL .seedCell .right) := by
  rfl

theorem combined_slot_one_empty
    (uProgram : Program UState CoreTape) (uAccept uReject uStart : UState)
    (q : Control) (x : ConcreteTape) :
    (MStarOuterProgram.program (attach uProgram uAccept uReject uStart)).rule
      (.parser q) x 1 = none :=
  MStarOuterProgram.parser_deterministic_slot_one _ q x

theorem groupDone_enters_length_scan :
    copierStep (UState := UState) uStart .groupDone .markL =
      some (copyGo .markL .groupSeekLen .left) := by
  rfl

end PakFixedPolyomino.MStarCopierMicrocode
