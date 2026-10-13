import PakFixedPolyomino.ULogTapeDecoding
import PakFixedPolyomino.FiniteOneTapeProgram
import Mathlib.Tactic

/-!
# Finite control allocation for the physical `U_log` interpreter

These are the literal control registers used by the forthcoming local rule
table.  Parameterized constructors are all finite; no semantic configuration,
program counter, tape letter, or clock value is stored in control.
-/

namespace PakFixedPolyomino.ULogControl

open OneTapeTableau

set_option maxRecDepth 4096

inductive BytecodeField where
  | programCount
  | source
  | read
  | slot
  | write
  | target
  | move
  | payloadLength
  | clock
  deriving DecidableEq, Repr

instance : Fintype BytecodeField := Fintype.ofList
  [.programCount, .source, .read, .slot, .write, .target, .move,
    .payloadLength, .clock] (by intro x; cases x <;> simp)

inductive CompareKind where
  | source
  | read
  | slot
  | matchedSource
  deriving DecidableEq, Repr

instance : Fintype CompareKind := Fintype.ofList
  [.source, .read, .slot, .matchedSource] (by intro x; cases x <;> simp)

inductive ReadPhase where
  | countOne
  | countTwo
  | seekZero
  | seekOne
  | seekBlank
  | returning
  deriving DecidableEq, Repr

instance : Fintype ReadPhase := Fintype.ofList
  [.countOne, .countTwo, .seekZero, .seekOne, .seekBlank, .returning]
  (by intro x; cases x <;> simp)

inductive ActionPhase where
  | writeCountOne
  | writeCountTwo
  | seekWriteZero
  | seekWriteOne
  | seekWriteBlank
  | writeReturning
  | targetSeekState
  | targetReturning
  | targetGrowSep
  | targetGrowPlaceSep
  | targetFinishSeek
  | targetFinishSeenOne
  | targetFinishMany
  | targetRestoreState
  | targetShrink
  | targetShrinkErase
  | targetShrinkEraseOne
  | targetShrinkReturnBoundary
  | targetShrinkPlaceSep
  | moveStart
  | moveAfterZero
  | moveAfterOne
  | movePlaceLeft
  | movePlaceRight
  | returnMovedFromLeft
  | returnMovedFromRight
  deriving DecidableEq, Repr

instance : Fintype ActionPhase := Fintype.ofList
  [.writeCountOne, .writeCountTwo, .seekWriteZero, .seekWriteOne,
    .seekWriteBlank, .writeReturning, .targetSeekState, .targetReturning,
    .targetGrowSep, .targetGrowPlaceSep, .targetFinishSeek,
    .targetFinishSeenOne, .targetFinishMany, .targetRestoreState,
    .targetShrink, .moveStart, .moveAfterZero,
    .moveAfterOne, .targetShrinkErase, .targetShrinkEraseOne,
    .targetShrinkReturnBoundary, .targetShrinkPlaceSep,
    .movePlaceLeft, .movePlaceRight, .returnMovedFromLeft,
    .returnMovedFromRight]
  (by intro x; cases x <;> simp)

inductive ShiftPhase where
  | left : ULogTapeLayout.CoreTape → ShiftPhase
  | right : ULogTapeLayout.CoreTape → ShiftPhase
  | initRight : ULogTapeLayout.CoreTape → ShiftPhase
  deriving DecidableEq, Fintype, Repr

inductive State where
  | start
  | accept
  | reject
  | seekPayload
  | translateCode : Bool → State
  | translateReturn
  | framePayloadLength
  | payloadLengthStart
  | framePayload : Bool → State
  | framePadding
  | initializeState
  | initStateCell : Fin 5 → State
  | initializeClock
  | cycleStart
  | clockSeek
  | clockConsume
  | clockReturn
  | readHead
  | chooseSlot
  | ruleSeek
  | ruleSeekChoice : Bool → State
  | ruleCountSeek : Bool → State
  | fieldSeek : BytecodeField → State
  | fieldCompare : CompareKind → Bool → State
  | compareSeekState : Bool → State
  | compareReturnSource : Bool → State
  | compareFinishSource : Bool → State
  | compareRestoreSource : Bool → State
  | readPhase : ReadPhase → Bool → State
  | fieldReturn : BytecodeField → State
  | returnToPc : Bool → State
  | countScan : Bool → State
  | seekReturn : Bool → Bool → State
  | payloadReturn : Bool → State
  | payloadCount : Bool → State
  | payloadSeekReturn : Bool → Bool → State
  | payloadRestore : Bool → Bool → State
  | skipRule
  | skipMoveSecond : Bool → State
  | actionWrite
  | actionPhase : ActionPhase → State
  | actionTarget
  | seekSimHead
  | moveSimHead : Move → State
  | shiftRuntime : ShiftPhase → State
  | restoreRule : Bool → State
  | mismatchReturnToPc : Bool → State
  | mismatchCount : Bool → State
  | mismatchSeekBoundary : Bool → State
  | mismatchSkipSource : Bool → State
  | mismatchSkipRead : Bool → State
  | mismatchSkipSlot : Bool → State
  | mismatchSkipWrite : Bool → State
  | mismatchSkipTarget : Bool → State
  | mismatchSkipMoveFirst : Bool → State
  | mismatchSkipMoveSecond : Bool → State
  | restoreClock
  | restorePc
  | restoreHead
  deriving DecidableEq, Fintype, Repr

def qStart : State := .start
def qAccept : State := .accept
def qReject : State := .reject

@[simp] theorem card_field : Fintype.card BytecodeField = 9 := by native_decide
@[simp] theorem card_compareField : Fintype.card CompareKind = 4 := by
  native_decide
@[simp] theorem card_state : Fintype.card State = 315 := by native_decide

@[simp] theorem qStart_ne_qAccept : qStart ≠ qAccept := by decide
@[simp] theorem qStart_ne_qReject : qStart ≠ qReject := by decide
@[simp] theorem qAccept_ne_qReject : qAccept ≠ qReject := by decide

/-- Only `chooseSlot` will carry two occupied labels.  All other interpreter
states are deterministic once the local table is filled. -/
def branchingState : State → Bool
  | .chooseSlot => true
  | _ => false

@[simp] theorem branchingState_chooseSlot : branchingState .chooseSlot = true :=
  rfl

theorem branchingState_iff (q : State) :
    branchingState q = true ↔ q = .chooseSlot := by
  cases q <;> simp [branchingState]

end PakFixedPolyomino.ULogControl
