import PakFixedPolyomino.ULogControl
import Mathlib.Tactic

/-!
# First literal rules of the finite `U_log` program

The bootstrap kernel scans across the left work buffer, installs `pcMark`,
translates the framed binary instance to the disjoint code alphabet in place,
and stops at the program marker.  The unique nondeterministic control writes
one of the two labelled slot markers.  Remaining interpreter phases are added
to the same table below as their refinements are proved.
-/

namespace PakFixedPolyomino.ULogProgram

open OneTapeTableau FiniteOneTapeProgram ULogAlphabet ULogControl

abbrev Tape := MStarConcreteAlphabet.CoreTape

def go (write : Tape) (target : State) (move : Move) : Action State Tape :=
  ⟨write, target, move⟩

def reject (x : Tape) : Action State Tape := go x qReject .stay

def bitTape : Bool → Tape
  | false => MStarConcreteAlphabet.zero
  | true => MStarConcreteAlphabet.one

def codeTape : Bool → Tape
  | false => ulogCore codeZero
  | true => ulogCore codeOne

def branchTape : Bool → Tape
  | false => ulogCore branchZero
  | true => ulogCore branchOne

def payloadTape : Bool → Tape
  | false => ulogCore dataZero
  | true => ulogCore dataOne

def unheadTape (x : Tape) : Tape :=
  if x = ulogCore payloadHeadZero then payloadTape false
  else if x = ulogCore payloadHeadOne then payloadTape true
  else if x = ulogCore payloadHeadBlank then ulogCore payloadBlank
  else x

def headTapeOfCell (x : Tape) : Tape :=
  if x = payloadTape false then ulogCore payloadHeadZero
  else if x = payloadTape true then ulogCore payloadHeadOne
  else if x = ulogCore payloadBlank then ulogCore payloadHeadBlank
  else x

def restoreProgramCell (x : Tape) : Tape :=
  if x = ulogCore sourceBoundary then ulogCore codeOne
  else if x = ulogCore sourceBoundaryZero then ulogCore codeZero
  else if x = ulogCore sourceBoundaryOne then ulogCore codeOne
  else x

def choiceHead (x : Tape) : Bool :=
  decide (x = ulogCore payloadHeadZero ∨
    x = ulogCore payloadHeadOne ∨ x = ulogCore payloadHeadBlank)

def deterministicStep : State → Tape → Option (Action State Tape)
  | .start, x =>
      if x = MStarConcreteAlphabet.work then some (go x .start .right)
      else if x = MStarConcreteAlphabet.zero then
        some (go x (.translateCode false) .left)
      else if x = MStarConcreteAlphabet.one then
        some (go x (.translateCode true) .left)
      else some (reject x)
  | .translateCode b, x =>
      if x = MStarConcreteAlphabet.work then
        some (go (ulogCore pcMark) (.framePayload b) .right)
      else some (reject x)
  | .framePayload b, x =>
      if x = bitTape b then some (go (codeTape b) .seekPayload .right)
      else some (reject x)
  | .seekPayload, x =>
      if x = MStarConcreteAlphabet.zero then
        some (go (codeTape false) .seekPayload .right)
      else if x = MStarConcreteAlphabet.one then
        some (go (codeTape true) .seekPayload .right)
      else if x = MStarConcreteAlphabet.work then
        some (go (ulogCore codeEnd) .translateReturn .left)
      else some (reject x)
  | .translateReturn, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x .translateReturn .left)
      else if x = ulogCore pcMark then
        some (go x .framePayloadLength .stay)
      else some (reject x)
  | .framePayloadLength, x =>
      if x = ulogCore pcMark then
        some (go x (.fieldSeek .programCount) .right)
      else some (reject x)
  | .payloadLengthStart, x =>
      if x = codeTape false then
        some (go (ulogCore payloadStartZero) (.fieldSeek .payloadLength) .right)
      else if x = codeTape true then
        some (go (ulogCore payloadStartOne) (.fieldReturn .payloadLength) .right)
      else some (reject x)
  | .fieldSeek field, x =>
      if x = ulogCore codeZero then
        some (go x (.fieldSeek field) .right)
      else if x = ulogCore codeOne then
        some (go x (.fieldReturn field) .right)
      else some (reject x)
  | .fieldReturn .source, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.fieldSeek .read) .stay)
      else some (reject x)
  | .fieldReturn .read, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.fieldSeek .write) .right)
      else some (reject x)
  | .fieldReturn .write, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.fieldSeek .target) .stay)
      else some (reject x)
  | .fieldReturn .target, x =>
      if x = codeTape false then
        some (go x (.skipMoveSecond false) .right)
      else if x = codeTape true then
        some (go x (.skipMoveSecond true) .right)
      else some (reject x)
  | .skipMoveSecond first, x =>
      if first = true ∧ x = codeTape true then some (reject x)
      else if x = codeTape false ∨ x = codeTape true then
        some (go x .skipRule .right)
      else some (reject x)
  | .skipRule, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.fieldReturn .programCount) .stay)
      else if x = ulogCore codeEnd then
        some (go x (.fieldReturn .programCount) .right)
      else some (reject x)
  | .fieldReturn .payloadLength, x =>
      if x = codeTape false then
        some (go (branchTape false) (.payloadReturn false) .left)
      else if x = codeTape true then
        some (go (branchTape true) (.payloadReturn true) .left)
      else if x = ulogCore codeEnd then
        some (go x .framePadding .stay)
      else some (reject x)
  | .fieldReturn .programCount, x =>
      if x = codeTape false then
        some (go (branchTape false) (.returnToPc false) .left)
      else if x = codeTape true then
        some (go (branchTape true) (.returnToPc true) .left)
      else if x = ulogCore codeEnd then
        some (go x (.fieldReturn .programCount) .right)
      else some (reject x)
  | .returnToPc b, x =>
      if x = codeTape false ∨ x = codeTape true ∨ x = ulogCore pcDone ∨
          x = ulogCore codeEnd then
        some (go x (.returnToPc b) .left)
      else if x = ulogCore pcMark then
        some (go x (.countScan b) .right)
      else some (reject x)
  | .countScan b, x =>
      if x = ulogCore pcDone then some (go x (.countScan b) .right)
      else if x = codeTape false then
        some (go (ulogCore pcDone) (.seekReturn b false) .right)
      else if x = codeTape true then
        some (go x (.seekReturn b true) .right)
      else some (reject x)
  | .seekReturn b done, x =>
      if x = codeTape false ∨ x = codeTape true ∨ x = ulogCore pcDone ∨
          x = ulogCore codeEnd then
        some (go x (.seekReturn b done) .right)
      else if x = branchTape b then
        some (go (codeTape b)
          (if done then .payloadLengthStart else .fieldSeek .source) .stay)
      else some (reject x)
  | .payloadReturn b, x =>
      if x = payloadTape false ∨ x = payloadTape true then
        some (go x (.payloadReturn b) .left)
      else if x = ulogCore codeOne then
        some (go (ulogCore payloadEnd) (.payloadCount b) .left)
      else if x = ulogCore payloadEnd then
        some (go x (.payloadCount b) .left)
      else if x = ulogCore payloadStartOne then
        some (go x (.payloadRestore b true) .right)
      else some (reject x)
  | .payloadCount b, x =>
      if x = ulogCore payloadDone then
        some (go x (.payloadCount b) .left)
      else if x = ulogCore codeZero then
        some (go (ulogCore payloadDone) (.payloadSeekReturn b false) .right)
      else if x = ulogCore payloadStartZero then
        some (go (ulogCore payloadStartDone) (.payloadSeekReturn b false) .right)
      else if x = ulogCore payloadStartDone then
        some (go x (.payloadSeekReturn b true) .right)
      else some (reject x)
  | .payloadSeekReturn b done, x =>
      if x = ulogCore payloadDone then
        some (go x (.payloadSeekReturn b done) .right)
      else if x = ulogCore payloadEnd then
        some (go x (.payloadRestore b done) .right)
      else some (reject x)
  | .payloadRestore b done, x =>
      if x = payloadTape false ∨ x = payloadTape true then
        some (go x (.payloadRestore b done) .right)
      else if x = branchTape b then
        some (go (if done then codeTape b else payloadTape b)
          (if done then .framePadding else .fieldReturn .payloadLength)
          (if done then .stay else .right))
      else some (reject x)
  | .framePadding, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go (ulogCore clockZero) .framePadding .right)
      else if x = ulogCore codeEnd then
        some (go (ulogCore clockOne) .initializeClock .right)
      else some (reject x)
  | .initializeClock, x =>
      if x = MStarConcreteAlphabet.work then
        some (go (ulogCore clockSep) .initializeState .left)
      else some (reject x)
  | .initializeState, x =>
      if x = ulogCore clockOne then
        some (go x (.initStateCell 0) .right)
      else some (reject x)
  | .initStateCell i, x =>
      if i = 0 ∧ x = ulogCore clockSep then
        some (go x (.initStateCell 1) .right)
      else if i = 1 ∧ x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateZero) (.initStateCell 2) .right)
      else if i = 2 ∧ x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateZero) (.initStateCell 3) .right)
      else if i = 3 ∧ x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateOne) (.initStateCell 4) .right)
      else if i = 4 ∧ x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateSep) .seekSimHead .left)
      else some (reject x)
  | .seekSimHead, x =>
      if x = ulogCore stateZero ∨ x = ulogCore stateOne ∨
          x = ulogCore clockSep ∨ x = ulogCore clockZero ∨
          x = ulogCore clockOne ∨ x = payloadTape false ∨
          x = payloadTape true ∨ x = ulogCore payloadBlank then
        some (go x .seekSimHead .left)
      else if x = ulogCore payloadEnd then
        some (go x .readHead .right)
      else if x = ulogCore payloadStartOne then
        some (go x .readHead .right)
      else if choiceHead x then some (go x .cycleStart .stay)
      else some (reject x)
  | .readHead, x =>
      if x = payloadTape false then
        some (go (ulogCore payloadHeadZero) .cycleStart .stay)
      else if x = payloadTape true then
        some (go (ulogCore payloadHeadOne) .cycleStart .stay)
      else if x = ulogCore clockZero ∨ x = ulogCore clockOne then
        some (go (ulogCore payloadHeadBlank)
          (.shiftRuntime (.initRight x)) .right)
      else some (reject x)
  | .cycleStart, x =>
      if choiceHead x then some (go x .clockSeek .right)
      else some (reject x)
  | .clockSeek, x =>
      if x = payloadTape false ∨ x = payloadTape true ∨
          x = ulogCore payloadBlank then
        some (go x .clockSeek .right)
      else if x = ulogCore clockZero then
        some (go (ulogCore clockOne) .clockConsume .right)
      else if x = ulogCore clockOne then
        some (go (ulogCore clockZero) .clockReturn .left)
      else some (reject x)
  | .clockConsume, x =>
      if x = ulogCore clockZero then
        some (go (ulogCore clockOne) .clockConsume .right)
      else if x = ulogCore clockOne then
        some (go (ulogCore clockZero) .clockReturn .left)
      else if x = ulogCore clockSep then some (reject x)
      else some (reject x)
  | .clockReturn, x =>
      if x = ulogCore clockZero ∨ x = ulogCore clockOne ∨
          x = payloadTape false ∨ x = payloadTape true ∨
          x = ulogCore payloadBlank then
        some (go x .clockReturn .left)
      else if choiceHead x then some (go x .chooseSlot .stay)
      else some (reject x)
  | .ruleSeekChoice slot, x =>
      if x = ulogCore payloadEnd ∨ x = ulogCore payloadDone ∨
          x = ulogCore payloadStartDone ∨ x = ulogCore payloadStartOne ∨
          x = payloadTape false ∨ x = payloadTape true ∨
          x = ulogCore payloadBlank ∨
          x = codeTape false ∨ x = codeTape true ∨
          x = ulogCore pcDone then
        some (go x (.ruleSeekChoice slot) .left)
      else if x = ulogCore pcMark then
        some (go x (.ruleCountSeek slot) .right)
      else some (reject x)
  | .ruleCountSeek slot, x =>
      if x = ulogCore pcDone then
        some (go x (.ruleCountSeek slot) .right)
      else if x = ulogCore codeOne then
        some (go (ulogCore sourceBoundary) (.fieldCompare .source slot) .right)
      else some (reject x)
  | .fieldCompare .matchedSource slot, x =>
      if x = ulogCore codeZero then
        some (go x (.fieldCompare .matchedSource slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.fieldCompare .read slot) .right)
      else some (reject x)
  | .fieldCompare .source slot, x =>
      if x = ulogCore codeZero then
        some (go (ulogCore sourceMark) (.compareSeekState slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.compareFinishSource slot) .right)
      else some (reject x)
  | .fieldCompare .read slot, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore readBoundary) (.readPhase .seekZero slot) .right)
      else if x = ulogCore codeZero then
        some (go x (.readPhase .countOne slot) .right)
      else some (reject x)
  | .readPhase .countOne slot, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore readBoundary) (.readPhase .seekOne slot) .right)
      else if x = ulogCore codeZero then
        some (go x (.readPhase .countTwo slot) .right)
      else some (reject x)
  | .readPhase .countTwo slot, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore readBoundary) (.readPhase .seekBlank slot) .right)
      else if x = ulogCore codeZero then
        some (go x (.restoreRule slot) .left)
      else some (reject x)
  | .readPhase .seekZero slot, x =>
      if x = ulogCore payloadHeadZero then
        some (go x (.readPhase .returning slot) .left)
      else if x = ulogCore payloadHeadOne then
        some (go x (.restoreRule slot) .left)
      else if x = ulogCore payloadHeadBlank then
        some (go x (.restoreRule slot) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.readPhase .seekZero slot) .right)
  | .readPhase .seekOne slot, x =>
      if x = ulogCore payloadHeadZero then
        some (go x (.restoreRule slot) .left)
      else if x = ulogCore payloadHeadOne then
        some (go x (.readPhase .returning slot) .left)
      else if x = ulogCore payloadHeadBlank then
        some (go x (.restoreRule slot) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.readPhase .seekOne slot) .right)
  | .readPhase .seekBlank slot, x =>
      if x = ulogCore payloadHeadZero then
        some (go x (.restoreRule slot) .left)
      else if x = ulogCore payloadHeadOne then
        some (go x (.restoreRule slot) .left)
      else if x = ulogCore payloadHeadBlank then
        some (go x (.readPhase .returning slot) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.readPhase .seekBlank slot) .right)
  | .readPhase .returning slot, x =>
      if x = ulogCore readBoundary then
        some (go (ulogCore codeOne) (.fieldCompare .slot slot) .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.readPhase .returning slot) .left)
  | .fieldCompare .slot slot, x =>
      if x = codeTape slot then some (go x .actionWrite .right)
      else if x = codeTape (!slot) then some (go x (.restoreRule slot) .left)
      else some (reject x)
  | .actionWrite, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore actionBoundary) (.actionPhase .seekWriteZero) .right)
      else if x = ulogCore codeZero then
        some (go x (.actionPhase .writeCountOne) .right)
      else some (reject x)
  | .actionPhase .writeCountOne, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore actionBoundary) (.actionPhase .seekWriteOne) .right)
      else if x = ulogCore codeZero then
        some (go x (.actionPhase .writeCountTwo) .right)
      else some (reject x)
  | .actionPhase .writeCountTwo, x =>
      if x = ulogCore codeOne then
        some (go (ulogCore actionBoundary) (.actionPhase .seekWriteBlank) .right)
      else some (reject x)
  | .actionPhase .seekWriteZero, x =>
      if choiceHead x then
        some (go (ulogCore payloadHeadZero) (.actionPhase .writeReturning) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.actionPhase .seekWriteZero) .right)
  | .actionPhase .seekWriteOne, x =>
      if choiceHead x then
        some (go (ulogCore payloadHeadOne) (.actionPhase .writeReturning) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.actionPhase .seekWriteOne) .right)
  | .actionPhase .seekWriteBlank, x =>
      if choiceHead x then
        some (go (ulogCore payloadHeadBlank) (.actionPhase .writeReturning) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.actionPhase .seekWriteBlank) .right)
  | .actionPhase .writeReturning, x =>
      if x = ulogCore actionBoundary then
        some (go (ulogCore codeOne) .actionTarget .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.actionPhase .writeReturning) .left)
  | .actionTarget, x =>
      if x = ulogCore codeZero then
        some (go (ulogCore targetMark) (.actionPhase .targetSeekState) .right)
      else if x = ulogCore codeOne then
        some (go (ulogCore targetBoundary) (.actionPhase .targetFinishSeek) .right)
      else some (reject x)
  | .actionPhase .targetSeekState, x =>
      if x = ulogCore stateMark then
        some (go x (.actionPhase .targetSeekState) .right)
      else if x = ulogCore stateZero then
        some (go (ulogCore stateMark) (.actionPhase .targetReturning) .left)
      else if x = ulogCore stateOne then
        some (go (ulogCore stateMark) (.actionPhase .targetGrowSep) .right)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.actionPhase .targetSeekState) .right)
  | .actionPhase .targetGrowSep, x =>
      if x = ulogCore stateSep then
        some (go (ulogCore stateOne) (.actionPhase .targetGrowPlaceSep) .right)
      else some (reject x)
  | .actionPhase .targetGrowPlaceSep, x =>
      if x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateSep) (.actionPhase .targetReturning) .left)
      else some (reject x)
  | .actionPhase .targetReturning, x =>
      if x = ulogCore targetMark then
        some (go (ulogCore codeZero) .actionTarget .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.actionPhase .targetReturning) .left)
  | .actionPhase .targetFinishSeek, x =>
      if x = ulogCore stateMark then
        some (go x (.actionPhase .targetFinishSeenOne) .right)
      else if x = ulogCore stateOne ∨ x = ulogCore stateZero then
        some (go x qAccept .stay)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.actionPhase .targetFinishSeek) .right)
  | .actionPhase .targetFinishSeenOne, x =>
      if x = ulogCore stateMark then
        some (go x (.actionPhase .targetFinishMany) .right)
      else if x = ulogCore stateZero ∨ x = ulogCore stateOne then
        some (reject x)
      else some (reject x)
  | .actionPhase .targetFinishMany, x =>
      if x = ulogCore stateMark then
        some (go x (.actionPhase .targetFinishMany) .right)
      else if x = ulogCore stateOne then
        some (go x (.actionPhase .targetRestoreState) .left)
      else if x = ulogCore stateZero then
        some (go x (.actionPhase .targetShrink) .stay)
      else some (reject x)
  | .actionPhase .targetRestoreState, x =>
      if x = ulogCore stateMark then
        some (go (ulogCore stateZero) (.actionPhase .targetRestoreState) .left)
      else if x = ulogCore targetBoundary then
        some (go (ulogCore codeOne) (.actionPhase .moveStart) .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.actionPhase .targetRestoreState) .left)
  | .actionPhase .targetShrink, x =>
      if x = ulogCore stateZero then
        some (go (ulogCore stateShrinkBoundary)
          (.actionPhase .targetShrinkErase) .right)
      else some (reject x)
  | .actionPhase .targetShrinkErase, x =>
      if x = ulogCore stateZero then
        some (go MStarConcreteAlphabet.work
          (.actionPhase .targetShrinkErase) .right)
      else if x = ulogCore stateOne then
        some (go MStarConcreteAlphabet.work
          (.actionPhase .targetShrinkEraseOne) .right)
      else some (reject x)
  | .actionPhase .targetShrinkEraseOne, x =>
      if x = ulogCore stateSep then
        some (go MStarConcreteAlphabet.work
          (.actionPhase .targetShrinkReturnBoundary) .left)
      else some (reject x)
  | .actionPhase .targetShrinkReturnBoundary, x =>
      if x = MStarConcreteAlphabet.work then
        some (go x (.actionPhase .targetShrinkReturnBoundary) .left)
      else if x = ulogCore stateShrinkBoundary then
        some (go (ulogCore stateOne)
          (.actionPhase .targetShrinkPlaceSep) .right)
      else some (reject x)
  | .actionPhase .targetShrinkPlaceSep, x =>
      if x = MStarConcreteAlphabet.work then
        some (go (ulogCore stateSep)
          (.actionPhase .targetRestoreState) .left)
      else some (reject x)
  | .actionPhase .moveStart, x =>
      if x = codeTape false then
        some (go x (.actionPhase .moveAfterZero) .right)
      else if x = codeTape true then
        some (go x (.actionPhase .moveAfterOne) .right)
      else some (reject x)
  | .actionPhase .moveAfterZero, x =>
      if x = codeTape false then some (go x (.moveSimHead .left) .right)
      else if x = codeTape true then some (go x (.moveSimHead .stay) .right)
      else some (reject x)
  | .actionPhase .moveAfterOne, x =>
      if x = codeTape false then some (go x (.moveSimHead .right) .right)
      else some (reject x)
  | .moveSimHead move, x =>
      if choiceHead x then
        match move with
        | .stay => some (go x .restoreClock .stay)
        | .left =>
            some (go (unheadTape x) (.actionPhase .movePlaceLeft) .left)
        | .right =>
            some (go (unheadTape x) (.actionPhase .movePlaceRight) .right)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.moveSimHead move) .right)
  | .actionPhase .movePlaceLeft, x =>
      if x = payloadTape false ∨ x = payloadTape true ∨
          x = ulogCore payloadBlank then
        some (go (headTapeOfCell x) .restoreClock .stay)
      else if x = ulogCore payloadEnd ∨
          x = ulogCore payloadStartOne then
        some (go (ulogCore payloadHeadBlank) (.shiftRuntime (.left x)) .left)
      else some (reject x)
  | .actionPhase .movePlaceRight, x =>
      if x = payloadTape false ∨ x = payloadTape true ∨
          x = ulogCore payloadBlank then
        some (go (headTapeOfCell x) .restoreClock .stay)
      else if x = ulogCore clockZero ∨ x = ulogCore clockOne then
        some (go (ulogCore payloadHeadBlank) (.shiftRuntime (.right x)) .right)
      else some (reject x)
  | .shiftRuntime (.left carry), x =>
      if x = MStarConcreteAlphabet.work then
        some (go carry (.actionPhase .returnMovedFromLeft) .right)
      else some (go carry (.shiftRuntime (.left x)) .left)
  | .shiftRuntime (.right carry), x =>
      if x = MStarConcreteAlphabet.work then
        some (go carry (.actionPhase .returnMovedFromRight) .left)
      else some (go carry (.shiftRuntime (.right x)) .right)
  | .shiftRuntime (.initRight carry), x =>
      if x = MStarConcreteAlphabet.work then
        some (go carry .seekSimHead .left)
      else some (go carry (.shiftRuntime (.initRight x)) .right)
  | .actionPhase .returnMovedFromLeft, x =>
      if choiceHead x then some (go x .restoreClock .stay)
      else some (go x (.actionPhase .returnMovedFromLeft) .right)
  | .actionPhase .returnMovedFromRight, x =>
      if choiceHead x then some (go x .restoreClock .stay)
      else some (go x (.actionPhase .returnMovedFromRight) .left)
  | .restoreClock, x =>
      if x = ulogCore pcMark then some (go x .restorePc .right)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x .restoreClock .left)
  | .restorePc, x =>
      if x = ulogCore pcDone then some (go x .restorePc .right)
      else if x = ulogCore codeZero then
        some (go (ulogCore pcDone) .restorePc .right)
      else if x = ulogCore codeOne then some (go x .restoreHead .right)
      else if x = ulogCore sourceBoundary then
        some (go (ulogCore codeOne) .restoreHead .right)
      else some (reject x)
  | .restoreHead, x =>
      if choiceHead x then some (go x .cycleStart .stay)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go (restoreProgramCell x) .restoreHead .right)
  | .compareSeekState slot, x =>
      if x = ulogCore stateZero then
        some (go (ulogCore stateMark) (.compareReturnSource slot) .left)
      else if x = ulogCore stateOne then
        some (go x (.restoreRule slot) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.compareSeekState slot) .right)
  | .compareReturnSource slot, x =>
      if x = ulogCore sourceMark then
        some (go x (.fieldCompare .source slot) .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.compareReturnSource slot) .left)
  | .compareFinishSource slot, x =>
      if x = ulogCore stateMark then
        some (go x (.compareFinishSource slot) .right)
      else if x = ulogCore stateZero then
        some (go x (.restoreRule slot) .left)
      else if x = ulogCore stateOne then
        some (go x (.compareRestoreSource slot) .left)
      else if x = MStarConcreteAlphabet.work then some (reject x)
      else some (go x (.compareFinishSource slot) .right)
  | .compareRestoreSource slot, x =>
      if x = ulogCore stateMark then
        some (go (ulogCore stateZero) (.compareRestoreSource slot) .left)
      else if x = ulogCore sourceMark then
        some (go (ulogCore codeZero) (.compareRestoreSource slot) .left)
      else if x = ulogCore sourceBoundary then
        some (go x (.fieldCompare .matchedSource slot) .right)
      else if x = ulogCore sourceBoundaryZero then
        some (go x (.fieldCompare .matchedSource slot) .right)
      else if x = ulogCore sourceBoundaryOne then
        some (go x (.fieldCompare .matchedSource slot) .right)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.compareRestoreSource slot) .left)
  | .restoreRule slot, x =>
      if x = ulogCore stateMark then
        some (go (ulogCore stateZero) (.restoreRule slot) .left)
      else if x = ulogCore sourceMark then
        some (go (ulogCore codeZero) (.restoreRule slot) .left)
      else if x = ulogCore readBoundary then
        some (go (ulogCore codeOne) (.restoreRule slot) .left)
      else if x = ulogCore sourceBoundary ∨
          x = ulogCore sourceBoundaryZero ∨
          x = ulogCore sourceBoundaryOne then
        some (go x (.mismatchReturnToPc slot) .left)
      else if x = ulogCore pcMark then some (reject x)
      else some (go x (.restoreRule slot) .left)
  | .mismatchReturnToPc slot, x =>
      if x = ulogCore pcMark then
        some (go x (.mismatchCount slot) .right)
      else some (go x (.mismatchReturnToPc slot) .left)
  | .mismatchCount slot, x =>
      if x = ulogCore codeZero then
        some (go x (.mismatchCount slot) .right)
      else if x = ulogCore pcDone then
        some (go (ulogCore codeZero) (.mismatchSeekBoundary slot) .right)
      else if x = ulogCore codeOne then some (reject x)
      else some (reject x)
  | .mismatchSeekBoundary slot, x =>
      if x = ulogCore sourceBoundary then
        some (go (ulogCore codeOne) (.mismatchSkipSource slot) .right)
      else if x = ulogCore sourceBoundaryZero then
        some (go (ulogCore codeZero) (.mismatchSkipSource slot) .right)
      else if x = ulogCore sourceBoundaryOne then
        some (go (ulogCore codeOne) (.mismatchSkipSource slot) .right)
      else some (go x (.mismatchSeekBoundary slot) .right)
  | .mismatchSkipSource slot, x =>
      if x = ulogCore codeZero then
        some (go x (.mismatchSkipSource slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.mismatchSkipRead slot) .right)
      else some (reject x)
  | .mismatchSkipRead slot, x =>
      if x = ulogCore codeZero then
        some (go x (.mismatchSkipRead slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.mismatchSkipSlot slot) .right)
      else some (reject x)
  | .mismatchSkipSlot slot, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.mismatchSkipWrite slot) .right)
      else some (reject x)
  | .mismatchSkipWrite slot, x =>
      if x = ulogCore codeZero then
        some (go x (.mismatchSkipWrite slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.mismatchSkipTarget slot) .right)
      else some (reject x)
  | .mismatchSkipTarget slot, x =>
      if x = ulogCore codeZero then
        some (go x (.mismatchSkipTarget slot) .right)
      else if x = ulogCore codeOne then
        some (go x (.mismatchSkipMoveFirst slot) .right)
      else some (reject x)
  | .mismatchSkipMoveFirst slot, x =>
      if x = codeTape false ∨ x = codeTape true then
        some (go x (.mismatchSkipMoveSecond slot) .right)
      else some (reject x)
  | .mismatchSkipMoveSecond slot, x =>
      if x = codeTape false then
        some (go (ulogCore sourceBoundaryZero)
          (.fieldCompare .source slot) .right)
      else if x = codeTape true then
        some (go (ulogCore sourceBoundaryOne)
          (.fieldCompare .source slot) .right)
      else some (reject x)
  | _, _ => none

def rule (q : State) (x : Tape) (slot : Fin 2) :
    Option (Action State Tape) :=
  if q = .chooseSlot ∧ x = ulogCore returnMark then
    if slot = 0 then some (go (ulogCore branchZero) .ruleSeek .left)
    else some (go (ulogCore branchOne) .ruleSeek .left)
  else if q = .chooseSlot ∧ choiceHead x then
    if slot = 0 then some (go x (.ruleSeekChoice false) .left)
    else some (go x (.ruleSeekChoice true) .left)
  else if slot = 0 then deterministicStep q x
  else none

def program : Program State Tape := ⟨rule⟩

theorem chooseSlot_zero :
    program.rule .chooseSlot (ulogCore returnMark) 0 =
      some (go (ulogCore branchZero) .ruleSeek .left) := by
  rfl

theorem chooseSlot_one :
    program.rule .chooseSlot (ulogCore returnMark) 1 =
      some (go (ulogCore branchOne) .ruleSeek .left) := by
  rfl

theorem chooseSlot_actions_distinct :
    go (ulogCore branchZero) .ruleSeek .left ≠
      go (ulogCore branchOne) .ruleSeek .left := by
  intro h
  have hw := congrArg Action.write h
  exact (ULogTapeDecoding.ulog_symbol_ne (by native_decide)) hw

theorem slot_one_only_choose {q : State} {x : Tape}
    (h : program.rule q x 1 ≠ none) :
    q = .chooseSlot ∧ (x = ulogCore returnMark ∨ choiceHead x = true) := by
  unfold program rule at h
  by_cases hchoose : q = .chooseSlot ∧ x = ulogCore returnMark
  · exact ⟨hchoose.1, Or.inl hchoose.2⟩
  · by_cases hhead : q = .chooseSlot ∧ choiceHead x = true
    · exact ⟨hhead.1, Or.inr hhead.2⟩
    · simp [hchoose, hhead] at h

theorem accept_no_rule (x : Tape) (slot : Fin 2) :
    program.rule qAccept x slot = none := by
  fin_cases slot <;> simp [program, rule, deterministicStep, qAccept]

theorem reject_no_rule (x : Tape) (slot : Fin 2) :
    program.rule qReject x slot = none := by
  fin_cases slot <;> simp [program, rule, deterministicStep, qReject]

end PakFixedPolyomino.ULogProgram
