import PakFixedPolyomino.ULogProgram
import PakFixedPolyomino.MStarParserExecution
import Mathlib.Tactic

/-!
# Executable refinement of the `U_log` bootstrap kernel
-/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

inductive Result where
  | running : State → Zipper Tape → Result
  | accepted : Zipper Tape → Result
  | rejected
  | stuck
  deriving DecidableEq, Repr

def oneStepAt (slot : Fin 2) : Result → Result
  | .running q z =>
      match program.rule q z.focus slot with
      | none => .stuck
      | some a =>
          match applyAction z a with
          | none => .stuck
          | some z' =>
              if a.target = qAccept then .accepted z'
              else if a.target = qReject then .rejected
              else .running a.target z'
  | r => r

def oneStep : Result → Result
  | .running q z =>
      match program.rule q z.focus 0 with
      | none => .stuck
      | some a =>
          match applyAction z a with
          | none => .stuck
          | some z' =>
              if a.target = qAccept then .accepted z'
              else if a.target = qReject then .rejected
              else .running a.target z'
  | r => r

theorem oneStep_eq_slot_zero (r : Result) :
    oneStep r = oneStepAt 0 r := rfl

def labelledSuccessors (r : Result) : List Result :=
  [oneStepAt 0 r, oneStepAt 1 r]

def run : ℕ → Result → Result
  | 0, r => r
  | n + 1, r => run n (oneStep r)

def Reaches (r s : Result) : Prop := ∃ n, run n r = s

theorem reaches_refl (r : Result) : Reaches r r := ⟨0, rfl⟩

theorem reaches_step {r s : Result} (h : oneStep r = s) : Reaches r s :=
  ⟨1, h⟩

theorem run_add (a b : ℕ) (r : Result) : run (a + b) r = run b (run a r) := by
  induction a generalizing r with
  | zero => simp [run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (oneStep r)

theorem reaches_trans {r s t : Result} (h₀ : Reaches r s)
    (h₁ : Reaches s t) : Reaches r t := by
  rcases h₀ with ⟨a, ha⟩
  rcases h₁ with ⟨b, hb⟩
  exact ⟨a + b, by rw [run_add, ha, hb]⟩

theorem start_work_step (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .start
      ⟨left, MStarConcreteAlphabet.work, y :: right⟩) =
      .running .start
        ⟨MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem start_bit_step (b : Bool) (left right : List Tape) (y : Tape) :
    oneStep (.running .start ⟨y :: left, bitTape b, right⟩) =
      .running (.translateCode b) ⟨left, y, bitTape b :: right⟩ := by
  cases b <;> rfl

theorem translateCode_step (b : Bool) (left right : List Tape) (y : Tape) :
    oneStep (.running (.translateCode b)
      ⟨left, MStarConcreteAlphabet.work, y :: right⟩) =
      .running (.framePayload b)
        ⟨ulogCore pcMark :: left, y, right⟩ := by
  cases b <;> rfl

theorem framePayload_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.framePayload b)
      ⟨left, bitTape b, y :: right⟩) =
      .running .seekPayload ⟨codeTape b :: left, y, right⟩ := by
  cases b <;> rfl

theorem seekPayload_bit_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .seekPayload
      ⟨left, bitTape b, y :: right⟩) =
      .running .seekPayload ⟨codeTape b :: left, y, right⟩ := by
  cases b <;> rfl

theorem seekPayload_end_step (left right : List Tape) (y : Tape) :
    oneStep (.running .seekPayload
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running .translateReturn
        ⟨left, y, ulogCore codeEnd :: right⟩ := by
  rfl

theorem translateReturn_code_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .translateReturn
      ⟨y :: left, codeTape b, right⟩) =
      .running .translateReturn ⟨left, y, codeTape b :: right⟩ := by
  cases b <;> rfl

theorem translateReturn_mark_step (left right : List Tape) :
    oneStep (.running .translateReturn
      ⟨left, ulogCore pcMark, right⟩) =
      .running .framePayloadLength ⟨left, ulogCore pcMark, right⟩ := by
  rfl

theorem framePayloadLength_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .framePayloadLength
      ⟨left, ulogCore pcMark, y :: right⟩) =
      .running (.fieldSeek .programCount)
        ⟨ulogCore pcMark :: left, y, right⟩ := by
  rfl

theorem payloadLengthStart_zero_step (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .payloadLengthStart
      ⟨left, codeTape false, y :: right⟩) =
      .running (.fieldSeek .payloadLength)
        ⟨ulogCore payloadStartZero :: left, y, right⟩ := by
  rfl

theorem payloadLengthStart_one_step (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .payloadLengthStart
      ⟨left, codeTape true, y :: right⟩) =
      .running (.fieldReturn .payloadLength)
        ⟨ulogCore payloadStartOne :: left, y, right⟩ := by
  rfl

theorem fieldSeek_zero_step (field : BytecodeField) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldSeek field)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.fieldSeek field)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  rfl

theorem fieldSeek_one_step (field : BytecodeField) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldSeek field)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.fieldReturn field)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  rfl

theorem fieldReturn_source_step (b : Bool) (left right : List Tape) :
    oneStep (.running (.fieldReturn .source)
      ⟨left, codeTape b, right⟩) =
      .running (.fieldSeek .read) ⟨left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem fieldReturn_read_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldReturn .read)
      ⟨left, codeTape b, y :: right⟩) =
      .running (.fieldSeek .write)
        ⟨codeTape b :: left, y, right⟩ := by
  cases b <;> rfl

theorem fieldReturn_write_step (b : Bool) (left right : List Tape) :
    oneStep (.running (.fieldReturn .write)
      ⟨left, codeTape b, right⟩) =
      .running (.fieldSeek .target) ⟨left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem fieldReturn_target_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldReturn .target)
      ⟨left, codeTape b, y :: right⟩) =
      .running (.skipMoveSecond b)
        ⟨codeTape b :: left, y, right⟩ := by
  cases b <;> rfl

def moveFirst : OneTapeTableau.Move → Bool
  | .left => false
  | .stay => false
  | .right => true

def moveSecond : OneTapeTableau.Move → Bool
  | .left => false
  | .stay => true
  | .right => false

@[simp] theorem encodeMove_eq (m : OneTapeTableau.Move) :
    ULogBytecode.encodeMove m = [moveFirst m, moveSecond m] := by
  cases m <;> rfl

theorem skipMoveSecond_step (m : OneTapeTableau.Move) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.skipMoveSecond (moveFirst m))
      ⟨left, codeTape (moveSecond m), y :: right⟩) =
      .running .skipRule
        ⟨codeTape (moveSecond m) :: left, y, right⟩ := by
  cases m <;> rfl

theorem skipMoveSecond_illegal (left right : List Tape) :
    oneStep (.running (.skipMoveSecond true)
      ⟨left, codeTape true, right⟩) = .rejected := by
  rfl

theorem skipRule_next_step (b : Bool) (left right : List Tape) :
    oneStep (.running .skipRule ⟨left, codeTape b, right⟩) =
      .running (.fieldReturn .programCount)
        ⟨left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem skipRule_end_step (left : List Tape) (b : Bool)
    (right : List Tape) :
    oneStep (.running .skipRule
      ⟨left, ulogCore codeEnd, codeTape b :: right⟩) =
      .running (.fieldReturn .programCount)
        ⟨ulogCore codeEnd :: left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem fieldReturn_payload_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldReturn .payloadLength)
      ⟨y :: left, codeTape b, right⟩) =
      .running (.payloadReturn b)
        ⟨left, y, branchTape b :: right⟩ := by
  cases b <;> rfl

theorem fieldReturn_payload_end_step (left right : List Tape) :
    oneStep (.running (.fieldReturn .payloadLength)
      ⟨left, ulogCore codeEnd, right⟩) =
      .running .framePadding ⟨left, ulogCore codeEnd, right⟩ := by
  rfl

theorem payloadReturn_codeOne_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadReturn b)
      ⟨y :: left, ulogCore codeOne, right⟩) =
      .running (.payloadCount b)
        ⟨left, y, ulogCore payloadEnd :: right⟩ := by
  cases b <;> rfl

theorem payloadReturn_end_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadReturn b)
      ⟨y :: left, ulogCore payloadEnd, right⟩) =
      .running (.payloadCount b)
        ⟨left, y, ulogCore payloadEnd :: right⟩ := by
  cases b <;> rfl

theorem payloadReturn_pass_code (carry bit : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadReturn carry)
      ⟨y :: left, payloadTape bit, right⟩) =
      .running (.payloadReturn carry)
        ⟨left, y, payloadTape bit :: right⟩ := by
  cases carry <;> cases bit <;> rfl

theorem payloadReturn_empty_step (b : Bool) (left : List Tape)
    (right : List Tape) :
    oneStep (.running (.payloadReturn b)
      ⟨left, ulogCore payloadStartOne, branchTape b :: right⟩) =
      .running (.payloadRestore b true)
        ⟨ulogCore payloadStartOne :: left, branchTape b, right⟩ := by
  cases b <;> rfl

theorem payloadCount_done_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadCount b)
      ⟨y :: left, ulogCore payloadDone, right⟩) =
      .running (.payloadCount b)
        ⟨left, y, ulogCore payloadDone :: right⟩ := by
  cases b <;> rfl

theorem payloadCount_zero_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadCount b)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.payloadSeekReturn b false)
        ⟨ulogCore payloadDone :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadCount_start_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadCount b)
      ⟨left, ulogCore payloadStartZero, y :: right⟩) =
      .running (.payloadSeekReturn b false)
        ⟨ulogCore payloadStartDone :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadCount_exhausted_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadCount b)
      ⟨left, ulogCore payloadStartDone, y :: right⟩) =
      .running (.payloadSeekReturn b true)
        ⟨ulogCore payloadStartDone :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadSeek_done_step (b exhausted : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadSeekReturn b exhausted)
      ⟨left, ulogCore payloadDone, y :: right⟩) =
      .running (.payloadSeekReturn b exhausted)
        ⟨ulogCore payloadDone :: left, y, right⟩ := by
  cases b <;> cases exhausted <;> rfl

theorem payloadSeek_end_step (b exhausted : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadSeekReturn b exhausted)
      ⟨left, ulogCore payloadEnd, y :: right⟩) =
      .running (.payloadRestore b exhausted)
        ⟨ulogCore payloadEnd :: left, y, right⟩ := by
  cases b <;> cases exhausted <;> rfl

theorem payloadRestore_fresh_step (b next : Bool) (left : List Tape)
    (right : List Tape) :
    oneStep (.running (.payloadRestore b false)
      ⟨left, branchTape b, codeTape next :: right⟩) =
      .running (.fieldReturn .payloadLength)
        ⟨payloadTape b :: left, codeTape next, right⟩ := by
  cases b <;> cases next <;> rfl

theorem payloadRestore_fresh_any (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadRestore b false)
      ⟨left, branchTape b, y :: right⟩) =
      .running (.fieldReturn .payloadLength)
        ⟨payloadTape b :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadRestore_pass_code (carry exhausted bit : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.payloadRestore carry exhausted)
      ⟨left, payloadTape bit, y :: right⟩) =
      .running (.payloadRestore carry exhausted)
        ⟨payloadTape bit :: left, y, right⟩ := by
  cases carry <;> cases exhausted <;> cases bit <;> rfl

theorem payloadRestore_exhausted_step (b : Bool) (left right : List Tape) :
    oneStep (.running (.payloadRestore b true)
      ⟨left, branchTape b, right⟩) =
      .running .framePadding ⟨left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem framePadding_bit_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .framePadding
      ⟨left, codeTape b, y :: right⟩) =
      .running .framePadding
        ⟨ulogCore clockZero :: left, y, right⟩ := by
  cases b <;> rfl

theorem framePadding_end_step (left : List Tape) (right : List Tape) :
    oneStep (.running .framePadding
      ⟨left, ulogCore codeEnd, MStarConcreteAlphabet.work :: right⟩) =
      .running .initializeClock
        ⟨ulogCore clockOne :: left, MStarConcreteAlphabet.work, right⟩ := by
  rfl

theorem initializeClock_step (left : List Tape) (right : List Tape) :
    oneStep (.running .initializeClock
      ⟨ulogCore clockOne :: left, MStarConcreteAlphabet.work, right⟩) =
      .running .initializeState
        ⟨left, ulogCore clockOne, ulogCore clockSep :: right⟩ := by
  rfl

theorem initializeState_step (left : List Tape) (right : List Tape) :
    oneStep (.running .initializeState
      ⟨left, ulogCore clockOne, ulogCore clockSep :: right⟩) =
      .running (.initStateCell 0)
        ⟨ulogCore clockOne :: left, ulogCore clockSep, right⟩ := by
  rfl

theorem initStateCell_zero_step (left : List Tape) (right : List Tape) :
    oneStep (.running (.initStateCell 0)
      ⟨left, ulogCore clockSep, MStarConcreteAlphabet.work :: right⟩) =
      .running (.initStateCell 1)
        ⟨ulogCore clockSep :: left, MStarConcreteAlphabet.work, right⟩ := by
  rfl

theorem initStateCell_one_step (left : List Tape) (right : List Tape) :
    oneStep (.running (.initStateCell 1)
      ⟨left, MStarConcreteAlphabet.work,
        MStarConcreteAlphabet.work :: right⟩) =
      .running (.initStateCell 2)
        ⟨ulogCore stateZero :: left, MStarConcreteAlphabet.work, right⟩ := by
  rfl

theorem initStateCell_two_step (left : List Tape) (right : List Tape) :
    oneStep (.running (.initStateCell 2)
      ⟨left, MStarConcreteAlphabet.work,
        MStarConcreteAlphabet.work :: right⟩) =
      .running (.initStateCell 3)
        ⟨ulogCore stateZero :: left, MStarConcreteAlphabet.work, right⟩ := by
  rfl

theorem initStateCell_three_step (left : List Tape) (right : List Tape) :
    oneStep (.running (.initStateCell 3)
      ⟨left, MStarConcreteAlphabet.work,
        MStarConcreteAlphabet.work :: right⟩) =
      .running (.initStateCell 4)
        ⟨ulogCore stateOne :: left, MStarConcreteAlphabet.work, right⟩ := by
  rfl

theorem initStateCell_four_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.initStateCell 4)
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore stateSep :: right⟩ := by
  rfl

theorem seekSimHead_pass_stateZero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore stateZero, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore stateZero :: right⟩ := by
  rfl

theorem seekSimHead_pass_stateOne (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore stateOne, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore stateOne :: right⟩ := by
  rfl

theorem seekSimHead_pass_clockSep (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore clockSep, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore clockSep :: right⟩ := by
  rfl

theorem seekSimHead_pass_clockZero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore clockZero, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore clockZero :: right⟩ := by
  rfl

theorem seekSimHead_pass_clockOne (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore clockOne, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore clockOne :: right⟩ := by
  rfl

theorem seekSimHead_pass_payload (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, payloadTape b, right⟩) =
      .running .seekSimHead
        ⟨left, y, payloadTape b :: right⟩ := by
  cases b <;> rfl

theorem seekSimHead_pass_blank (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨y :: left, ulogCore payloadBlank, right⟩) =
      .running .seekSimHead
        ⟨left, y, ulogCore payloadBlank :: right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, applyAction,
    qAccept, qReject]

theorem seekSimHead_payloadEnd_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨left, ulogCore payloadEnd, y :: right⟩) =
      .running .readHead
        ⟨ulogCore payloadEnd :: left, y, right⟩ := by
  rfl

theorem seekSimHead_empty_step (left : List Tape) (boundary : Tape)
    (right : List Tape) :
    oneStep (.running .seekSimHead
      ⟨left, ulogCore payloadStartOne, boundary :: right⟩) =
      .running .readHead
        ⟨ulogCore payloadStartOne :: left, boundary, right⟩ := by
  rfl

theorem readHead_empty_boundary (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .readHead
      ⟨ulogCore payloadStartOne :: left, boundary, y :: right⟩) =
      .running (.shiftRuntime (.initRight boundary))
        ⟨ulogCore payloadHeadBlank :: ulogCore payloadStartOne :: left,
          y, right⟩ := by
  rcases hboundary with rfl | rfl <;> rfl

theorem initShiftRight_step (carry x : Tape)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.initRight carry))
      ⟨left, x, y :: right⟩) =
      .running (.shiftRuntime (.initRight x))
        ⟨carry :: left, y, right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, hwork,
    applyAction, qAccept, qReject]

theorem initShiftRight_end (carry : Tape) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.initRight carry))
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running .seekSimHead ⟨left, y, carry :: right⟩ := by
  rfl

theorem seekSimHead_existing_head (head : Tape)
    (hhead : choiceHead head = true) (left right : List Tape) :
    oneStep (.running .seekSimHead ⟨left, head, right⟩) =
      .running .cycleStart ⟨left, head, right⟩ := by
  unfold choiceHead at hhead
  simp at hhead
  rcases hhead with rfl | rfl | rfl <;> rfl

theorem readHead_step (b : Bool) (left right : List Tape) :
    oneStep (.running .readHead ⟨left, payloadTape b, right⟩) =
      .running .cycleStart
        ⟨left, if b then ulogCore payloadHeadOne
          else ulogCore payloadHeadZero, right⟩ := by
  cases b <;> rfl

theorem cycleStart_head_step (x : Tape) (hx : choiceHead x = true)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .cycleStart ⟨left, x, y :: right⟩) =
      .running .clockSeek ⟨x :: left, y, right⟩ := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem clockSeek_payload_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .clockSeek ⟨left, payloadTape b, y :: right⟩) =
      .running .clockSeek ⟨payloadTape b :: left, y, right⟩ := by
  cases b <;> rfl

theorem clockSeek_blank_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockSeek
      ⟨left, ulogCore payloadBlank, y :: right⟩) =
      .running .clockSeek ⟨ulogCore payloadBlank :: left, y, right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, applyAction,
    qAccept, qReject]

theorem clockSeek_zero_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockSeek
      ⟨left, ulogCore clockZero, y :: right⟩) =
      .running .clockConsume
        ⟨ulogCore clockOne :: left, y, right⟩ := by
  rfl

theorem clockSeek_one_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockSeek
      ⟨y :: left, ulogCore clockOne, right⟩) =
      .running .clockReturn
        ⟨left, y, ulogCore clockZero :: right⟩ := by
  rfl

theorem clockConsume_zero_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockConsume
      ⟨left, ulogCore clockZero, y :: right⟩) =
      .running .clockConsume
        ⟨ulogCore clockOne :: left, y, right⟩ := by
  rfl

theorem clockConsume_one_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockConsume
      ⟨y :: left, ulogCore clockOne, right⟩) =
      .running .clockReturn
        ⟨left, y, ulogCore clockZero :: right⟩ := by
  rfl

theorem clockConsume_exhausted (left right : List Tape) :
    oneStep (.running .clockConsume
      ⟨left, ulogCore clockSep, right⟩) = .rejected := by
  rfl

theorem clockReturn_clock_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .clockReturn
      ⟨y :: left, if b then ulogCore clockOne else ulogCore clockZero,
        right⟩) =
      .running .clockReturn
        ⟨left, y,
          (if b then ulogCore clockOne else ulogCore clockZero) :: right⟩ := by
  cases b <;> rfl

theorem clockReturn_payload_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .clockReturn
      ⟨y :: left, payloadTape b, right⟩) =
      .running .clockReturn
        ⟨left, y, payloadTape b :: right⟩ := by
  cases b <;> rfl

theorem clockReturn_blank_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .clockReturn
      ⟨y :: left, ulogCore payloadBlank, right⟩) =
      .running .clockReturn
        ⟨left, y, ulogCore payloadBlank :: right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, applyAction,
    qAccept, qReject]

theorem clockReturn_head_step (x : Tape) (hx : choiceHead x = true)
    (left right : List Tape) :
    oneStep (.running .clockReturn ⟨left, x, right⟩) =
      .running .chooseSlot ⟨left, x, right⟩ := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem chooseSlot_head_zero (x : Tape) (hx : choiceHead x = true) :
    program.rule .chooseSlot x 0 =
      some (go x (.ruleSeekChoice false) .left) := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem chooseSlot_head_one (x : Tape) (hx : choiceHead x = true) :
    program.rule .chooseSlot x 1 =
      some (go x (.ruleSeekChoice true) .left) := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem chooseSlot_head_actions_distinct (x : Tape) :
    go x (.ruleSeekChoice false) .left ≠
      go x (.ruleSeekChoice true) .left := by
  intro h
  have ht := congrArg (fun a => a.target) h
  have hne : State.ruleSeekChoice false ≠
      State.ruleSeekChoice true := by decide
  exact hne ht

theorem oneStepAt_chooseSlot_zero (x : Tape) (hx : choiceHead x = true)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStepAt 0 (.running .chooseSlot ⟨y :: left, x, right⟩) =
      .running (.ruleSeekChoice false) ⟨left, y, x :: right⟩ := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem oneStepAt_chooseSlot_one (x : Tape) (hx : choiceHead x = true)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStepAt 1 (.running .chooseSlot ⟨y :: left, x, right⟩) =
      .running (.ruleSeekChoice true) ⟨left, y, x :: right⟩ := by
  unfold choiceHead at hx
  simp at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem labelledSuccessors_chooseSlot (x : Tape)
    (hx : choiceHead x = true) (left : List Tape) (y : Tape)
    (right : List Tape) :
    labelledSuccessors (.running .chooseSlot ⟨y :: left, x, right⟩) =
      [.running (.ruleSeekChoice false) ⟨left, y, x :: right⟩,
        .running (.ruleSeekChoice true) ⟨left, y, x :: right⟩] := by
  simp [labelledSuccessors, oneStepAt_chooseSlot_zero x hx,
    oneStepAt_chooseSlot_one x hx]

theorem labelledSuccessors_chooseSlot_distinct (x : Tape)
    (hx : choiceHead x = true) (left : List Tape) (y : Tape)
    (right : List Tape) :
    List.Pairwise (· ≠ ·)
      (labelledSuccessors (.running .chooseSlot ⟨y :: left, x, right⟩)) := by
  rw [labelledSuccessors_chooseSlot x hx]
  simp

theorem ruleSeekChoice_pass (slot : Bool) (x : Tape)
    (hx : x = ulogCore payloadEnd ∨ x = ulogCore payloadDone ∨
      x = ulogCore payloadStartDone ∨ x = ulogCore payloadStartOne ∨
      x = payloadTape false ∨ x = payloadTape true ∨
      x = ulogCore payloadBlank ∨
      x = codeTape false ∨ x = codeTape true ∨ x = ulogCore pcDone)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleSeekChoice slot) ⟨y :: left, x, right⟩) =
      .running (.ruleSeekChoice slot) ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases slot <;>
      simp [oneStep, program, rule, deterministicStep, go, applyAction,
        qAccept, qReject]

theorem ruleSeekChoice_mark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleSeekChoice slot)
      ⟨left, ulogCore pcMark, y :: right⟩) =
      .running (.ruleCountSeek slot)
        ⟨ulogCore pcMark :: left, y, right⟩ := by
  cases slot <;> rfl

theorem ruleCountSeek_done (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleCountSeek slot)
      ⟨left, ulogCore pcDone, y :: right⟩) =
      .running (.ruleCountSeek slot)
        ⟨ulogCore pcDone :: left, y, right⟩ := by
  cases slot <;> rfl

theorem ruleCountSeek_end (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleCountSeek slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.fieldCompare .source slot)
        ⟨ulogCore sourceBoundary :: left, y, right⟩ := by
  cases slot <;> rfl

theorem fieldCompare_source_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .source slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.compareSeekState slot)
        ⟨ulogCore sourceMark :: left, y, right⟩ := by
  cases slot <;> rfl

theorem fieldCompare_source_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .source slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.compareFinishSource slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem compareSeekState_pass (slot : Bool) (x : Tape)
    (hzero : x ≠ ulogCore stateZero) (hone : x ≠ ulogCore stateOne)
    (hwork : x ≠ MStarConcreteAlphabet.work) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareSeekState slot) ⟨left, x, y :: right⟩) =
      .running (.compareSeekState slot) ⟨x :: left, y, right⟩ := by
  have ha : State.compareSeekState slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.compareSeekState slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go,
    hzero, hone, hwork, applyAction, ha, hr]

theorem compareSeekState_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareSeekState slot)
      ⟨y :: left, ulogCore stateZero, right⟩) =
      .running (.compareReturnSource slot)
        ⟨left, y, ulogCore stateMark :: right⟩ := by
  cases slot <;> rfl

theorem compareSeekState_one_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareSeekState slot)
      ⟨y :: left, ulogCore stateOne, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore stateOne :: right⟩ := by
  cases slot <;> rfl

theorem compareReturnSource_pass (slot : Bool) (x : Tape)
    (hmark : x ≠ ulogCore sourceMark) (hpc : x ≠ ulogCore pcMark)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareReturnSource slot)
      ⟨y :: left, x, right⟩) =
      .running (.compareReturnSource slot) ⟨left, y, x :: right⟩ := by
  have ha : State.compareReturnSource slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.compareReturnSource slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hpc, applyAction, ha, hr]

theorem compareReturnSource_mark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareReturnSource slot)
      ⟨left, ulogCore sourceMark, y :: right⟩) =
      .running (.fieldCompare .source slot)
        ⟨ulogCore sourceMark :: left, y, right⟩ := by
  cases slot <;> rfl

theorem compareFinishSource_pass (slot : Bool) (x : Tape)
    (hmark : x ≠ ulogCore stateMark) (hzero : x ≠ ulogCore stateZero)
    (hone : x ≠ ulogCore stateOne)
    (hwork : x ≠ MStarConcreteAlphabet.work) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareFinishSource slot) ⟨left, x, y :: right⟩) =
      .running (.compareFinishSource slot) ⟨x :: left, y, right⟩ := by
  have ha : State.compareFinishSource slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.compareFinishSource slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hzero, hone, hwork, applyAction, ha, hr]

theorem compareFinishSource_mark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareFinishSource slot)
      ⟨left, ulogCore stateMark, y :: right⟩) =
      .running (.compareFinishSource slot)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  cases slot <;> rfl

theorem compareFinishSource_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareFinishSource slot)
      ⟨y :: left, ulogCore stateOne, right⟩) =
      .running (.compareRestoreSource slot)
        ⟨left, y, ulogCore stateOne :: right⟩ := by
  cases slot <;> rfl

theorem compareFinishSource_zero_mismatch (slot : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareFinishSource slot)
      ⟨y :: left, ulogCore stateZero, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore stateZero :: right⟩ := by
  cases slot <;> rfl

theorem compareRestoreSource_stateMark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot)
      ⟨y :: left, ulogCore stateMark, right⟩) =
      .running (.compareRestoreSource slot)
        ⟨left, y, ulogCore stateZero :: right⟩ := by
  cases slot <;> rfl

theorem compareRestoreSource_sourceMark (slot : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot)
      ⟨y :: left, ulogCore sourceMark, right⟩) =
      .running (.compareRestoreSource slot)
        ⟨left, y, ulogCore codeZero :: right⟩ := by
  cases slot <;> rfl

theorem compareRestoreSource_boundary (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot)
      ⟨left, ulogCore sourceBoundary, y :: right⟩) =
      .running (.fieldCompare .matchedSource slot)
        ⟨ulogCore sourceBoundary :: left, y, right⟩ := by
  cases slot <;> rfl

theorem compareRestoreSource_boundaryZero (slot : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot)
      ⟨left, ulogCore sourceBoundaryZero, y :: right⟩) =
      .running (.fieldCompare .matchedSource slot)
        ⟨ulogCore sourceBoundaryZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem compareRestoreSource_boundaryOne (slot : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot)
      ⟨left, ulogCore sourceBoundaryOne, y :: right⟩) =
      .running (.fieldCompare .matchedSource slot)
        ⟨ulogCore sourceBoundaryOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem matchedSourceSeek_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .matchedSource slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.fieldCompare .matchedSource slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem matchedSourceSeek_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .matchedSource slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.fieldCompare .read slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem restoreRule_stateMark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot)
      ⟨y :: left, ulogCore stateMark, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore stateZero :: right⟩ := by
  cases slot <;> rfl

theorem restoreRule_sourceMark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot)
      ⟨y :: left, ulogCore sourceMark, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore codeZero :: right⟩ := by
  cases slot <;> rfl

theorem restoreRule_readBoundary (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot)
      ⟨y :: left, ulogCore readBoundary, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore codeOne :: right⟩ := by
  cases slot <;> rfl

theorem restoreRule_boundary (slot : Bool) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot)
      ⟨y :: left, ulogCore boundary, right⟩) =
      .running (.mismatchReturnToPc slot)
        ⟨left, y, ulogCore boundary :: right⟩ := by
  rcases hboundary with rfl | rfl | rfl <;> cases slot <;> rfl

theorem restoreRule_pass (slot : Bool) (x : Tape)
    (hstate : x ≠ ulogCore stateMark)
    (hsource : x ≠ ulogCore sourceMark)
    (hread : x ≠ ulogCore readBoundary)
    (hboundary : x ≠ ulogCore sourceBoundary)
    (hboundaryZero : x ≠ ulogCore sourceBoundaryZero)
    (hboundaryOne : x ≠ ulogCore sourceBoundaryOne)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot) ⟨y :: left, x, right⟩) =
      .running (.restoreRule slot) ⟨left, y, x :: right⟩ := by
  have ha : State.restoreRule slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.restoreRule slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hstate, hsource,
    hread, hboundary, hboundaryZero, hboundaryOne, hpc,
    applyAction, ha, hr]

theorem mismatchReturnToPc_pass (slot : Bool) (x : Tape)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchReturnToPc slot) ⟨y :: left, x, right⟩) =
      .running (.mismatchReturnToPc slot) ⟨left, y, x :: right⟩ := by
  have ha : State.mismatchReturnToPc slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.mismatchReturnToPc slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hpc,
    applyAction, ha, hr]

theorem mismatchReturnToPc_mark (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchReturnToPc slot)
      ⟨left, ulogCore pcMark, y :: right⟩) =
      .running (.mismatchCount slot)
        ⟨ulogCore pcMark :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchCount_consumed (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchCount slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.mismatchCount slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchCount_fresh (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchCount slot)
      ⟨left, ulogCore pcDone, y :: right⟩) =
      .running (.mismatchSeekBoundary slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchCount_exhausted (slot : Bool) (left : List Tape)
    (right : List Tape) :
    oneStep (.running (.mismatchCount slot)
      ⟨left, ulogCore codeOne, right⟩) = .rejected := by
  cases slot <;> rfl

theorem mismatchSeekBoundary_start (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSeekBoundary slot)
      ⟨left, ulogCore sourceBoundary, y :: right⟩) =
      .running (.mismatchSkipSource slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSeekBoundary_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSeekBoundary slot)
      ⟨left, ulogCore sourceBoundaryZero, y :: right⟩) =
      .running (.mismatchSkipSource slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSeekBoundary_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSeekBoundary slot)
      ⟨left, ulogCore sourceBoundaryOne, y :: right⟩) =
      .running (.mismatchSkipSource slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSeekBoundary_pass (slot : Bool) (x : Tape)
    (hstart : x ≠ ulogCore sourceBoundary)
    (hzero : x ≠ ulogCore sourceBoundaryZero)
    (hone : x ≠ ulogCore sourceBoundaryOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSeekBoundary slot) ⟨left, x, y :: right⟩) =
      .running (.mismatchSeekBoundary slot) ⟨x :: left, y, right⟩ := by
  have ha : State.mismatchSeekBoundary slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.mismatchSeekBoundary slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hstart, hzero,
    hone, applyAction, ha, hr]

theorem mismatchSeekBoundary_boundary (slot : Bool)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSeekBoundary slot)
      ⟨left, ulogCore boundary, y :: right⟩) =
      .running (.mismatchSkipSource slot)
        ⟨(if boundary = sourceBoundaryZero then ulogCore codeZero
          else ulogCore codeOne) :: left, y, right⟩ := by
  rcases hboundary with rfl | rfl | rfl
  · simpa [sourceBoundary, sourceBoundaryZero] using
      mismatchSeekBoundary_start slot left y right
  · simpa [sourceBoundaryZero] using
      mismatchSeekBoundary_zero slot left y right
  · simpa [sourceBoundaryOne, sourceBoundaryZero] using
      mismatchSeekBoundary_one slot left y right

theorem mismatchSkipSource_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipSource slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.mismatchSkipSource slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipSource_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipSource slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.mismatchSkipRead slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipRead_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipRead slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.mismatchSkipRead slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipRead_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipRead slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.mismatchSkipSlot slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipSlot_bit (slot bit : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipSlot slot)
      ⟨left, codeTape bit, y :: right⟩) =
      .running (.mismatchSkipWrite slot)
        ⟨codeTape bit :: left, y, right⟩ := by
  cases slot <;> cases bit <;> rfl

theorem mismatchSkipWrite_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipWrite slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.mismatchSkipWrite slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipWrite_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipWrite slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.mismatchSkipTarget slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipTarget_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipTarget slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.mismatchSkipTarget slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipTarget_one (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipTarget slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.mismatchSkipMoveFirst slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem mismatchSkipMoveFirst_bit (slot bit : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipMoveFirst slot)
      ⟨left, codeTape bit, y :: right⟩) =
      .running (.mismatchSkipMoveSecond slot)
        ⟨codeTape bit :: left, y, right⟩ := by
  cases slot <;> cases bit <;> rfl

theorem mismatchSkipMoveSecond_bit (slot bit : Bool)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.mismatchSkipMoveSecond slot)
      ⟨left, codeTape bit, y :: right⟩) =
      .running (.fieldCompare .source slot)
        ⟨(if bit then ulogCore sourceBoundaryOne
          else ulogCore sourceBoundaryZero) :: left, y, right⟩ := by
  cases slot <;> cases bit <;> rfl

theorem fieldCompare_read_zero (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .read slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.readPhase .seekZero slot)
        ⟨ulogCore readBoundary :: left, y, right⟩ := by
  cases slot <;> rfl

theorem fieldCompare_read_more (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .read slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.readPhase .countOne slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem readCountOne_done (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .countOne slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.readPhase .seekOne slot)
        ⟨ulogCore readBoundary :: left, y, right⟩ := by
  cases slot <;> rfl

theorem readCountOne_more (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .countOne slot)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.readPhase .countTwo slot)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  cases slot <;> rfl

theorem readCountTwo_done (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .countTwo slot)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.readPhase .seekBlank slot)
        ⟨ulogCore readBoundary :: left, y, right⟩ := by
  cases slot <;> rfl

theorem readCountTwo_tooLong (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .countTwo slot)
      ⟨y :: left, ulogCore codeZero, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore codeZero :: right⟩ := by
  cases slot <;> rfl

theorem readSeekZero_match (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekZero slot)
      ⟨y :: left, ulogCore payloadHeadZero, right⟩) =
      .running (.readPhase .returning slot)
        ⟨left, y, ulogCore payloadHeadZero :: right⟩ := by
  cases slot <;> rfl

theorem readSeekOne_match (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekOne slot)
      ⟨y :: left, ulogCore payloadHeadOne, right⟩) =
      .running (.readPhase .returning slot)
        ⟨left, y, ulogCore payloadHeadOne :: right⟩ := by
  cases slot <;> rfl

theorem readSeekBlank_match (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekBlank slot)
      ⟨y :: left, ulogCore payloadHeadBlank, right⟩) =
      .running (.readPhase .returning slot)
        ⟨left, y, ulogCore payloadHeadBlank :: right⟩ := by
  cases slot <;> rfl

theorem readSeekZero_one_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekZero slot)
      ⟨y :: left, ulogCore payloadHeadOne, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadOne :: right⟩ := by
  cases slot <;> rfl

theorem readSeekZero_blank_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekZero slot)
      ⟨y :: left, ulogCore payloadHeadBlank, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadBlank :: right⟩ := by
  cases slot <;> rfl

theorem readSeekOne_zero_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekOne slot)
      ⟨y :: left, ulogCore payloadHeadZero, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadZero :: right⟩ := by
  cases slot <;> rfl

theorem readSeekOne_blank_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekOne slot)
      ⟨y :: left, ulogCore payloadHeadBlank, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadBlank :: right⟩ := by
  cases slot <;> rfl

theorem readSeekBlank_zero_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekBlank slot)
      ⟨y :: left, ulogCore payloadHeadZero, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadZero :: right⟩ := by
  cases slot <;> rfl

theorem readSeekBlank_one_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekBlank slot)
      ⟨y :: left, ulogCore payloadHeadOne, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, ulogCore payloadHeadOne :: right⟩ := by
  cases slot <;> rfl

theorem readSeekZero_pass (slot : Bool) (x : Tape)
    (hzero : x ≠ ulogCore payloadHeadZero)
    (hone : x ≠ ulogCore payloadHeadOne)
    (hblank : x ≠ ulogCore payloadHeadBlank)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekZero slot) ⟨left, x, y :: right⟩) =
      .running (.readPhase .seekZero slot) ⟨x :: left, y, right⟩ := by
  have ha : State.readPhase .seekZero slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.readPhase .seekZero slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hzero, hone,
    hblank, hwork, applyAction, ha, hr]

theorem readSeekOne_pass (slot : Bool) (x : Tape)
    (hzero : x ≠ ulogCore payloadHeadZero)
    (hone : x ≠ ulogCore payloadHeadOne)
    (hblank : x ≠ ulogCore payloadHeadBlank)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekOne slot) ⟨left, x, y :: right⟩) =
      .running (.readPhase .seekOne slot) ⟨x :: left, y, right⟩ := by
  have ha : State.readPhase .seekOne slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.readPhase .seekOne slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hzero, hone,
    hblank, hwork, applyAction, ha, hr]

theorem readSeekBlank_pass (slot : Bool) (x : Tape)
    (hzero : x ≠ ulogCore payloadHeadZero)
    (hone : x ≠ ulogCore payloadHeadOne)
    (hblank : x ≠ ulogCore payloadHeadBlank)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .seekBlank slot) ⟨left, x, y :: right⟩) =
      .running (.readPhase .seekBlank slot) ⟨x :: left, y, right⟩ := by
  have ha : State.readPhase .seekBlank slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.readPhase .seekBlank slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hzero, hone,
    hblank, hwork, applyAction, ha, hr]

theorem readReturn_pass (slot : Bool) (x : Tape)
    (hboundary : x ≠ ulogCore readBoundary)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .returning slot) ⟨y :: left, x, right⟩) =
      .running (.readPhase .returning slot) ⟨left, y, x :: right⟩ := by
  have ha : State.readPhase .returning slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.readPhase .returning slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hboundary, hpc,
    applyAction, ha, hr]

theorem readReturn_boundary (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.readPhase .returning slot)
      ⟨left, ulogCore readBoundary, y :: right⟩) =
      .running (.fieldCompare .slot slot)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  cases slot <;> rfl

theorem fieldCompare_slot_match (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .slot slot)
      ⟨left, codeTape slot, y :: right⟩) =
      .running .actionWrite ⟨codeTape slot :: left, y, right⟩ := by
  cases slot <;> rfl

theorem fieldCompare_slot_mismatch (slot : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldCompare .slot slot)
      ⟨y :: left, codeTape (!slot), right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, codeTape (!slot) :: right⟩ := by
  cases slot <;> rfl

theorem actionWrite_zero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .actionWrite
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.actionPhase .seekWriteZero)
        ⟨ulogCore actionBoundary :: left, y, right⟩ := by
  rfl

theorem actionWrite_more (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .actionWrite
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.actionPhase .writeCountOne)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  rfl

theorem actionWriteOne_done (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .writeCountOne)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.actionPhase .seekWriteOne)
        ⟨ulogCore actionBoundary :: left, y, right⟩ := by
  rfl

theorem actionWriteOne_more (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .writeCountOne)
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.actionPhase .writeCountTwo)
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  rfl

theorem actionWriteTwo_done (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .writeCountTwo)
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.actionPhase .seekWriteBlank)
        ⟨ulogCore actionBoundary :: left, y, right⟩ := by
  rfl

theorem actionSeekWriteZero_head (head : Tape)
    (hhead : choiceHead head = true) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteZero)
      ⟨y :: left, head, right⟩) =
      .running (.actionPhase .writeReturning)
        ⟨left, y, ulogCore payloadHeadZero :: right⟩ := by
  have ha : State.actionPhase .seekWriteZero ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteZero ≠ qReject := by decide
  have hta : State.actionPhase .writeReturning ≠ qAccept := by decide
  have htr : State.actionPhase .writeReturning ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem actionSeekWriteOne_head (head : Tape)
    (hhead : choiceHead head = true) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteOne)
      ⟨y :: left, head, right⟩) =
      .running (.actionPhase .writeReturning)
        ⟨left, y, ulogCore payloadHeadOne :: right⟩ := by
  have ha : State.actionPhase .seekWriteOne ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteOne ≠ qReject := by decide
  have hta : State.actionPhase .writeReturning ≠ qAccept := by decide
  have htr : State.actionPhase .writeReturning ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem actionSeekWriteBlank_head (head : Tape)
    (hhead : choiceHead head = true) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteBlank)
      ⟨y :: left, head, right⟩) =
      .running (.actionPhase .writeReturning)
        ⟨left, y, ulogCore payloadHeadBlank :: right⟩ := by
  have ha : State.actionPhase .seekWriteBlank ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteBlank ≠ qReject := by decide
  have hta : State.actionPhase .writeReturning ≠ qAccept := by decide
  have htr : State.actionPhase .writeReturning ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem actionSeekWriteZero_pass (x : Tape)
    (hhead : choiceHead x = false)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteZero)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .seekWriteZero) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .seekWriteZero ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteZero ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead, hwork,
    applyAction, ha, hr]

theorem actionSeekWriteOne_pass (x : Tape)
    (hhead : choiceHead x = false)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteOne)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .seekWriteOne) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .seekWriteOne ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteOne ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead, hwork,
    applyAction, ha, hr]

theorem actionSeekWriteBlank_pass (x : Tape)
    (hhead : choiceHead x = false)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .seekWriteBlank)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .seekWriteBlank) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .seekWriteBlank ≠ qAccept := by decide
  have hr : State.actionPhase .seekWriteBlank ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead, hwork,
    applyAction, ha, hr]

theorem actionWriteReturn_boundary (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .writeReturning)
      ⟨left, ulogCore actionBoundary, y :: right⟩) =
      .running .actionTarget
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  rfl

theorem actionWriteReturn_pass (x : Tape)
    (hboundary : x ≠ ulogCore actionBoundary)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .writeReturning)
      ⟨y :: left, x, right⟩) =
      .running (.actionPhase .writeReturning) ⟨left, y, x :: right⟩ := by
  have ha : State.actionPhase .writeReturning ≠ qAccept := by decide
  have hr : State.actionPhase .writeReturning ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go,
    hboundary, hpc, applyAction, ha, hr]

theorem actionTarget_zero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .actionTarget
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running (.actionPhase .targetSeekState)
        ⟨ulogCore targetMark :: left, y, right⟩ := by
  rfl

theorem actionTarget_done (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .actionTarget
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running (.actionPhase .targetFinishSeek)
        ⟨ulogCore targetBoundary :: left, y, right⟩ := by
  rfl

theorem targetSeekState_mark (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetSeekState)
      ⟨left, ulogCore stateMark, y :: right⟩) =
      .running (.actionPhase .targetSeekState)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  rfl

theorem targetSeekState_zero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetSeekState)
      ⟨y :: left, ulogCore stateZero, right⟩) =
      .running (.actionPhase .targetReturning)
        ⟨left, y, ulogCore stateMark :: right⟩ := by
  rfl

theorem targetSeekState_one (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetSeekState)
      ⟨left, ulogCore stateOne, y :: right⟩) =
      .running (.actionPhase .targetGrowSep)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  rfl

theorem targetSeekState_pass (x : Tape)
    (hmark : x ≠ ulogCore stateMark)
    (hzero : x ≠ ulogCore stateZero)
    (hone : x ≠ ulogCore stateOne)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .targetSeekState)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .targetSeekState) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .targetSeekState ≠ qAccept := by decide
  have hr : State.actionPhase .targetSeekState ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hzero, hone, hwork, applyAction, ha, hr]

theorem targetGrowSep_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetGrowSep)
      ⟨left, ulogCore stateSep, y :: right⟩) =
      .running (.actionPhase .targetGrowPlaceSep)
        ⟨ulogCore stateOne :: left, y, right⟩ := by
  rfl

theorem targetGrowPlaceSep_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetGrowPlaceSep)
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running (.actionPhase .targetReturning)
        ⟨left, y, ulogCore stateSep :: right⟩ := by
  rfl

theorem targetReturning_mark (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetReturning)
      ⟨left, ulogCore targetMark, y :: right⟩) =
      .running .actionTarget
        ⟨ulogCore codeZero :: left, y, right⟩ := by
  rfl

theorem targetReturning_pass (x : Tape)
    (hmark : x ≠ ulogCore targetMark)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .targetReturning)
      ⟨y :: left, x, right⟩) =
      .running (.actionPhase .targetReturning) ⟨left, y, x :: right⟩ := by
  have ha : State.actionPhase .targetReturning ≠ qAccept := by decide
  have hr : State.actionPhase .targetReturning ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hpc, applyAction, ha, hr]

theorem targetFinishSeek_mark (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeek)
      ⟨left, ulogCore stateMark, y :: right⟩) =
      .running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  rfl

theorem targetFinishSeek_one (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeek)
      ⟨y :: left, ulogCore stateOne, right⟩) =
      .accepted ⟨y :: left, ulogCore stateOne, right⟩ := by
  rfl

theorem targetFinishSeek_one_any (left right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeek)
      ⟨left, ulogCore stateOne, right⟩) =
      .accepted ⟨left, ulogCore stateOne, right⟩ := by
  rfl

theorem targetFinishSeek_pass (x : Tape)
    (hmark : x ≠ ulogCore stateMark)
    (hzero : x ≠ ulogCore stateZero)
    (hone : x ≠ ulogCore stateOne)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeek)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .targetFinishSeek) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .targetFinishSeek ≠ qAccept := by decide
  have hr : State.actionPhase .targetFinishSeek ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hzero, hone, hwork, applyAction, ha, hr]

theorem targetFinishSeek_shorter (left : List Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeek)
      ⟨left, ulogCore stateZero, right⟩) =
      .accepted ⟨left, ulogCore stateZero, right⟩ := by
  rfl

theorem targetFinishSeenOne_mark_core (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeenOne)
      ⟨left, ulogCore stateMark, y :: right⟩) =
      .running (.actionPhase .targetFinishMany)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  rfl

theorem targetFinishSeenOne_zero_reject_core (left right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeenOne)
      ⟨left, ulogCore stateZero, right⟩) = .rejected := by
  rfl

theorem targetFinishSeenOne_one_reject_core (left right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishSeenOne)
      ⟨left, ulogCore stateOne, right⟩) = .rejected := by
  rfl

theorem targetFinishMany_mark_core (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishMany)
      ⟨left, ulogCore stateMark, y :: right⟩) =
      .running (.actionPhase .targetFinishMany)
        ⟨ulogCore stateMark :: left, y, right⟩ := by
  rfl

theorem targetFinishMany_one_core (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishMany)
      ⟨y :: left, ulogCore stateOne, right⟩) =
      .running (.actionPhase .targetRestoreState)
        ⟨left, y, ulogCore stateOne :: right⟩ := by
  rfl

theorem targetFinishMany_zero_core (left right : List Tape) :
    oneStep (.running (.actionPhase .targetFinishMany)
      ⟨left, ulogCore stateZero, right⟩) =
      .running (.actionPhase .targetShrink)
        ⟨left, ulogCore stateZero, right⟩ := by
  rfl

theorem targetShrink_start (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrink)
      ⟨left, ulogCore stateZero, y :: right⟩) =
      .running (.actionPhase .targetShrinkErase)
        ⟨ulogCore stateShrinkBoundary :: left, y, right⟩ := by
  rfl

theorem targetShrinkErase_zero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkErase)
      ⟨left, ulogCore stateZero, y :: right⟩) =
      .running (.actionPhase .targetShrinkErase)
        ⟨MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem targetShrinkErase_one (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkErase)
      ⟨left, ulogCore stateOne, y :: right⟩) =
      .running (.actionPhase .targetShrinkEraseOne)
        ⟨MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem targetShrinkEraseOne_sep (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkEraseOne)
      ⟨y :: left, ulogCore stateSep, right⟩) =
      .running (.actionPhase .targetShrinkReturnBoundary)
        ⟨left, y, MStarConcreteAlphabet.work :: right⟩ := by
  rfl

theorem targetShrinkReturn_work (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkReturnBoundary)
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running (.actionPhase .targetShrinkReturnBoundary)
        ⟨left, y, MStarConcreteAlphabet.work :: right⟩ := by
  rfl

theorem targetShrinkReturn_boundary (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkReturnBoundary)
      ⟨left, ulogCore stateShrinkBoundary, y :: right⟩) =
      .running (.actionPhase .targetShrinkPlaceSep)
        ⟨ulogCore stateOne :: left, y, right⟩ := by
  rfl

theorem targetShrinkPlaceSep_step (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetShrinkPlaceSep)
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running (.actionPhase .targetRestoreState)
        ⟨left, y, ulogCore stateSep :: right⟩ := by
  rfl

theorem targetRestoreState_mark (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetRestoreState)
      ⟨y :: left, ulogCore stateMark, right⟩) =
      .running (.actionPhase .targetRestoreState)
        ⟨left, y, ulogCore stateZero :: right⟩ := by
  rfl

theorem targetRestoreState_boundary (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running (.actionPhase .targetRestoreState)
      ⟨left, ulogCore targetBoundary, y :: right⟩) =
      .running (.actionPhase .moveStart)
        ⟨ulogCore codeOne :: left, y, right⟩ := by
  rfl

theorem targetRestoreState_pass (x : Tape)
    (hmark : x ≠ ulogCore stateMark)
    (hboundary : x ≠ ulogCore targetBoundary)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .targetRestoreState)
      ⟨y :: left, x, right⟩) =
      .running (.actionPhase .targetRestoreState) ⟨left, y, x :: right⟩ := by
  have ha : State.actionPhase .targetRestoreState ≠ qAccept := by decide
  have hr : State.actionPhase .targetRestoreState ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go,
    hmark, hboundary, hpc, applyAction, ha, hr]

theorem actionMoveStart_bit (bit : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .moveStart)
      ⟨left, codeTape bit, y :: right⟩) =
      .running (if bit then .actionPhase .moveAfterOne
        else .actionPhase .moveAfterZero)
        ⟨codeTape bit :: left, y, right⟩ := by
  cases bit <;> rfl

theorem actionMoveSecond (m : OneTapeTableau.Move) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running
      (if moveFirst m then .actionPhase .moveAfterOne
        else .actionPhase .moveAfterZero)
      ⟨left, codeTape (moveSecond m), y :: right⟩) =
      .running (.moveSimHead m)
        ⟨codeTape (moveSecond m) :: left, y, right⟩ := by
  cases m <;> rfl

theorem reaches_actionMove (m : OneTapeTableau.Move) (left : List Tape)
    (y : Tape) (right : List Tape) :
    Reaches
      (.running (.actionPhase .moveStart)
        ⟨left, codeTape (moveFirst m),
          codeTape (moveSecond m) :: y :: right⟩)
      (.running (.moveSimHead m)
        ⟨codeTape (moveSecond m) :: codeTape (moveFirst m) :: left,
          y, right⟩) := by
  refine ⟨2, ?_⟩
  cases m <;> simp [run, actionMoveStart_bit, actionMoveSecond]

theorem moveSimHead_pass (m : OneTapeTableau.Move) (x : Tape)
    (hhead : choiceHead x = false)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.moveSimHead m) ⟨left, x, y :: right⟩) =
      .running (.moveSimHead m) ⟨x :: left, y, right⟩ := by
  have ha : State.moveSimHead m ≠ qAccept := by cases m <;> decide
  have hr : State.moveSimHead m ≠ qReject := by cases m <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hhead, hwork,
    applyAction, ha, hr]

theorem moveSimHead_stay (head : Tape) (hhead : choiceHead head = true)
    (left right : List Tape) :
    oneStep (.running (.moveSimHead .stay) ⟨left, head, right⟩) =
      .running .restoreClock ⟨left, head, right⟩ := by
  have ha : State.moveSimHead .stay ≠ qAccept := by decide
  have hr : State.moveSimHead .stay ≠ qReject := by decide
  have hta : State.restoreClock ≠ qAccept := by decide
  have htr : State.restoreClock ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem moveSimHead_left (head : Tape) (hhead : choiceHead head = true)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.moveSimHead .left) ⟨y :: left, head, right⟩) =
      .running (.actionPhase .movePlaceLeft)
        ⟨left, y, unheadTape head :: right⟩ := by
  have ha : State.moveSimHead .left ≠ qAccept := by decide
  have hr : State.moveSimHead .left ≠ qReject := by decide
  have hta : State.actionPhase .movePlaceLeft ≠ qAccept := by decide
  have htr : State.actionPhase .movePlaceLeft ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem moveSimHead_right (head : Tape) (hhead : choiceHead head = true)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.moveSimHead .right) ⟨left, head, y :: right⟩) =
      .running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: left, y, right⟩ := by
  have ha : State.moveSimHead .right ≠ qAccept := by decide
  have hr : State.moveSimHead .right ≠ qReject := by decide
  have hta : State.actionPhase .movePlaceRight ≠ qAccept := by decide
  have htr : State.actionPhase .movePlaceRight ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem movePlaceLeft_cell (cell : Tape)
    (hcell : cell = payloadTape false ∨ cell = payloadTape true ∨
      cell = ulogCore payloadBlank) (left right : List Tape) :
    oneStep (.running (.actionPhase .movePlaceLeft)
      ⟨left, cell, right⟩) =
      .running .restoreClock ⟨left, headTapeOfCell cell, right⟩ := by
  rcases hcell with rfl | rfl | rfl <;> rfl

theorem movePlaceRight_cell (cell : Tape)
    (hcell : cell = payloadTape false ∨ cell = payloadTape true ∨
      cell = ulogCore payloadBlank) (left right : List Tape) :
    oneStep (.running (.actionPhase .movePlaceRight)
      ⟨left, cell, right⟩) =
      .running .restoreClock ⟨left, headTapeOfCell cell, right⟩ := by
  rcases hcell with rfl | rfl | rfl <;> rfl

theorem movePlaceRight_boundary (headBoundary : Tape)
    (hboundary : headBoundary = ulogCore clockZero ∨
      headBoundary = ulogCore clockOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .movePlaceRight)
      ⟨left, headBoundary, y :: right⟩) =
      .running (.shiftRuntime (.right headBoundary))
        ⟨ulogCore payloadHeadBlank :: left, y, right⟩ := by
  rcases hboundary with rfl | rfl <;> rfl

theorem movePlaceLeft_boundary (headBoundary : Tape)
    (hboundary : headBoundary = ulogCore payloadEnd ∨
      headBoundary = ulogCore payloadStartOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .movePlaceLeft)
      ⟨y :: left, headBoundary, right⟩) =
      .running (.shiftRuntime (.left headBoundary))
        ⟨left, y, ulogCore payloadHeadBlank :: right⟩ := by
  rcases hboundary with rfl | rfl <;> rfl

theorem shiftRuntimeRight_step (carry x : Tape)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.right carry))
      ⟨left, x, y :: right⟩) =
      .running (.shiftRuntime (.right x)) ⟨carry :: left, y, right⟩ := by
  have ha : State.shiftRuntime (.right carry) ≠ qAccept := by simp [qAccept]
  have hr : State.shiftRuntime (.right carry) ≠ qReject := by simp [qReject]
  have hta : State.shiftRuntime (.right x) ≠ qAccept := by simp [qAccept]
  have htr : State.shiftRuntime (.right x) ≠ qReject := by simp [qReject]
  simp [oneStep, program, rule, deterministicStep, go, hwork,
    applyAction, ha, hr, hta, htr]

theorem shiftRuntimeRight_end (carry : Tape) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.right carry))
      ⟨y :: left, MStarConcreteAlphabet.work, right⟩) =
      .running (.actionPhase .returnMovedFromRight)
        ⟨left, y, carry :: right⟩ := by
  rfl

theorem shiftRuntimeLeft_step (carry x : Tape)
    (hwork : x ≠ MStarConcreteAlphabet.work)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.left carry))
      ⟨y :: left, x, right⟩) =
      .running (.shiftRuntime (.left x)) ⟨left, y, carry :: right⟩ := by
  have ha : State.shiftRuntime (.left carry) ≠ qAccept := by simp [qAccept]
  have hr : State.shiftRuntime (.left carry) ≠ qReject := by simp [qReject]
  have hta : State.shiftRuntime (.left x) ≠ qAccept := by simp [qAccept]
  have htr : State.shiftRuntime (.left x) ≠ qReject := by simp [qReject]
  simp [oneStep, program, rule, deterministicStep, go, hwork,
    applyAction, ha, hr, hta, htr]

theorem shiftRuntimeLeft_end (carry : Tape) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.shiftRuntime (.left carry))
      ⟨left, MStarConcreteAlphabet.work, y :: right⟩) =
      .running (.actionPhase .returnMovedFromLeft)
        ⟨carry :: left, y, right⟩ := by
  rfl

theorem returnMovedFromLeft_pass (x : Tape)
    (hhead : choiceHead x = false) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .returnMovedFromLeft)
      ⟨left, x, y :: right⟩) =
      .running (.actionPhase .returnMovedFromLeft) ⟨x :: left, y, right⟩ := by
  have ha : State.actionPhase .returnMovedFromLeft ≠ qAccept := by decide
  have hr : State.actionPhase .returnMovedFromLeft ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr]

theorem returnMovedFromRight_pass (x : Tape)
    (hhead : choiceHead x = false) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.actionPhase .returnMovedFromRight)
      ⟨y :: left, x, right⟩) =
      .running (.actionPhase .returnMovedFromRight) ⟨left, y, x :: right⟩ := by
  have ha : State.actionPhase .returnMovedFromRight ≠ qAccept := by decide
  have hr : State.actionPhase .returnMovedFromRight ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr]

theorem returnMovedFromLeft_head (head : Tape)
    (hhead : choiceHead head = true) (left right : List Tape) :
    oneStep (.running (.actionPhase .returnMovedFromLeft)
      ⟨left, head, right⟩) =
      .running .restoreClock ⟨left, head, right⟩ := by
  have ha : State.actionPhase .returnMovedFromLeft ≠ qAccept := by decide
  have hr : State.actionPhase .returnMovedFromLeft ≠ qReject := by decide
  have hta : State.restoreClock ≠ qAccept := by decide
  have htr : State.restoreClock ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem returnMovedFromRight_head (head : Tape)
    (hhead : choiceHead head = true) (left right : List Tape) :
    oneStep (.running (.actionPhase .returnMovedFromRight)
      ⟨left, head, right⟩) =
      .running .restoreClock ⟨left, head, right⟩ := by
  have ha : State.actionPhase .returnMovedFromRight ≠ qAccept := by decide
  have hr : State.actionPhase .returnMovedFromRight ≠ qReject := by decide
  have hta : State.restoreClock ≠ qAccept := by decide
  have htr : State.restoreClock ≠ qReject := by decide
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, ha, hr, hta, htr]

theorem restoreClock_pass (x : Tape) (hpc : x ≠ ulogCore pcMark)
    (hwork : x ≠ MStarConcreteAlphabet.work) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .restoreClock ⟨y :: left, x, right⟩) =
      .running .restoreClock ⟨left, y, x :: right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, hpc, hwork,
    applyAction, qAccept, qReject]

theorem restoreClock_pc (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .restoreClock
      ⟨left, ulogCore pcMark, y :: right⟩) =
      .running .restorePc ⟨ulogCore pcMark :: left, y, right⟩ := by
  rfl

theorem restorePc_done (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .restorePc
      ⟨left, ulogCore pcDone, y :: right⟩) =
      .running .restorePc ⟨ulogCore pcDone :: left, y, right⟩ := by
  rfl

theorem restorePc_zero (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .restorePc
      ⟨left, ulogCore codeZero, y :: right⟩) =
      .running .restorePc ⟨ulogCore pcDone :: left, y, right⟩ := by
  rfl

theorem restorePc_end (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .restorePc
      ⟨left, ulogCore codeOne, y :: right⟩) =
      .running .restoreHead ⟨ulogCore codeOne :: left, y, right⟩ := by
  rfl

theorem restorePc_boundary (left : List Tape) (y : Tape)
    (right : List Tape) :
    oneStep (.running .restorePc
      ⟨left, ulogCore sourceBoundary, y :: right⟩) =
      .running .restoreHead ⟨ulogCore codeOne :: left, y, right⟩ := by
  rfl

theorem restoreHead_pass (x : Tape) (hhead : choiceHead x = false)
    (hwork : x ≠ MStarConcreteAlphabet.work) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .restoreHead ⟨left, x, y :: right⟩) =
      .running .restoreHead ⟨restoreProgramCell x :: left, y, right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, hhead, hwork,
    applyAction, qAccept, qReject]

theorem restoreHead_head (head : Tape) (hhead : choiceHead head = true)
    (left right : List Tape) :
    oneStep (.running .restoreHead ⟨left, head, right⟩) =
      .running .cycleStart ⟨left, head, right⟩ := by
  simp [oneStep, program, rule, deterministicStep, go, hhead,
    applyAction, qAccept, qReject]

theorem fieldReturn_count_step (b : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.fieldReturn .programCount)
      ⟨y :: left, codeTape b, right⟩) =
      .running (.returnToPc b)
        ⟨left, y, branchTape b :: right⟩ := by
  cases b <;> rfl

theorem fieldReturn_count_end_step (left : List Tape) (b : Bool)
    (right : List Tape) :
    oneStep (.running (.fieldReturn .programCount)
      ⟨left, ulogCore codeEnd, codeTape b :: right⟩) =
      .running (.fieldReturn .programCount)
        ⟨ulogCore codeEnd :: left, codeTape b, right⟩ := by
  cases b <;> rfl

theorem returnToPc_pass_code (carry bit : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry)
      ⟨y :: left, codeTape bit, right⟩) =
      .running (.returnToPc carry)
        ⟨left, y, codeTape bit :: right⟩ := by
  cases carry <;> cases bit <;> rfl

theorem returnToPc_pass_done (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry)
      ⟨y :: left, ulogCore pcDone, right⟩) =
      .running (.returnToPc carry)
        ⟨left, y, ulogCore pcDone :: right⟩ := by
  cases carry <;> rfl

theorem returnToPc_pass_end (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry)
      ⟨y :: left, ulogCore codeEnd, right⟩) =
      .running (.returnToPc carry)
        ⟨left, y, ulogCore codeEnd :: right⟩ := by
  cases carry <;> rfl

theorem returnToPc_mark (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry)
      ⟨left, ulogCore pcMark, y :: right⟩) =
      .running (.countScan carry)
        ⟨ulogCore pcMark :: left, y, right⟩ := by
  cases carry <;> rfl

theorem countScan_done (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.countScan carry)
      ⟨left, ulogCore pcDone, y :: right⟩) =
      .running (.countScan carry)
        ⟨ulogCore pcDone :: left, y, right⟩ := by
  cases carry <;> rfl

theorem countScan_fresh (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.countScan carry)
      ⟨left, codeTape false, y :: right⟩) =
      .running (.seekReturn carry false)
        ⟨ulogCore pcDone :: left, y, right⟩ := by
  cases carry <;> rfl

theorem countScan_exhausted (carry : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.countScan carry)
      ⟨left, codeTape true, y :: right⟩) =
      .running (.seekReturn carry true)
        ⟨codeTape true :: left, y, right⟩ := by
  cases carry <;> rfl

theorem seekReturn_pass_code (carry done bit : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.seekReturn carry done)
      ⟨left, codeTape bit, y :: right⟩) =
      .running (.seekReturn carry done)
        ⟨codeTape bit :: left, y, right⟩ := by
  cases carry <;> cases done <;> cases bit <;> rfl

theorem seekReturn_pass_done (carry done : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.seekReturn carry done)
      ⟨left, ulogCore pcDone, y :: right⟩) =
      .running (.seekReturn carry done)
        ⟨ulogCore pcDone :: left, y, right⟩ := by
  cases carry <;> cases done <;> rfl

theorem seekReturn_pass_end (carry done : Bool) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.seekReturn carry done)
      ⟨left, ulogCore codeEnd, y :: right⟩) =
      .running (.seekReturn carry done)
        ⟨ulogCore codeEnd :: left, y, right⟩ := by
  cases carry <;> cases done <;> rfl

theorem seekReturn_marker (carry done : Bool) (left right : List Tape) :
    oneStep (.running (.seekReturn carry done)
      ⟨left, branchTape carry, right⟩) =
      .running (if done then .payloadLengthStart else .fieldSeek .source)
        ⟨left, codeTape carry, right⟩ := by
  cases carry <;> cases done <;> rfl

def beforeLeftPath (xs : List Tape) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  match xs with
  | [] => ⟨left, y, right⟩
  | x :: xs => ⟨xs ++ y :: left, x, right⟩

def afterLeftPath (xs : List Tape) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  ⟨left, y, xs.reverse ++ right⟩

@[simp] theorem replicate_append_cons_self {α : Type*} (a : α)
    (n : ℕ) (xs : List α) :
    List.replicate n a ++ a :: xs = a :: List.replicate n a ++ xs := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem run_left_path_of (q : State) (xs : List Tape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨y :: left, x, right⟩) =
        .running q ⟨left, y, x :: right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run xs.length (.running q (beforeLeftPath xs left y right)) =
      .running q (afterLeftPath xs left y right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeLeftPath, afterLeftPath, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp, run]
          simp only [beforeLeftPath, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeLeftPath (z :: zs) left y (x :: right))) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterLeftPath, List.append_assoc]

def afterLeftPathMap (xs : List Tape) (f : Tape → Tape)
    (left : List Tape) (y : Tape) (right : List Tape) : Zipper Tape :=
  ⟨left, y, xs.reverse.map f ++ right⟩

theorem run_left_path_map_of (q : State) (xs : List Tape)
    (f : Tape → Tape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨y :: left, x, right⟩) =
        .running q ⟨left, y, f x :: right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run xs.length (.running q (beforeLeftPath xs left y right)) =
      .running q (afterLeftPathMap xs f left y right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeLeftPath, afterLeftPathMap, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp,
            run]
          simp only [beforeLeftPath, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeLeftPath (z :: zs) left y (f x :: right))) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterLeftPathMap, List.append_assoc]

def beforeRightPath (xs : List Tape) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  match xs with
  | [] => ⟨left, y, right⟩
  | x :: xs => ⟨left, x, xs ++ y :: right⟩

def afterRightPath (xs : List Tape) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  ⟨xs.reverse ++ left, y, right⟩

theorem run_right_path_of (q : State) (xs : List Tape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨left, x, y :: right⟩) =
        .running q ⟨x :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run xs.length (.running q (beforeRightPath xs left y right)) =
      .running q (afterRightPath xs left y right) := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeRightPath, afterRightPath, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp, run]
          simp only [beforeRightPath, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeRightPath (z :: zs) (x :: left) y right)) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterRightPath, List.append_assoc]

def afterRightPathMap (xs : List Tape) (f : Tape → Tape)
    (left : List Tape) (y : Tape) (right : List Tape) : Zipper Tape :=
  ⟨xs.reverse.map f ++ left, y, right⟩

theorem beforeLeftPath_append_singleton (xs : List Tape) (z : Tape)
    (hxs : xs ≠ []) (left : List Tape) (y : Tape) (right : List Tape) :
    beforeLeftPath (xs ++ [z]) left y right =
      beforeLeftPath xs (y :: left) z right := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs => simp [beforeLeftPath, List.append_assoc]

theorem beforeRightPath_append_singleton (xs : List Tape) (z : Tape)
    (hxs : xs ≠ []) (left : List Tape) (y : Tape) (right : List Tape) :
    beforeRightPath (xs ++ [z]) left y right =
      beforeRightPath xs left z (y :: right) := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs => simp [beforeRightPath, List.append_assoc]

theorem run_right_path_map_of (q : State) (xs : List Tape)
    (f : Tape → Tape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨left, x, y :: right⟩) =
        .running q ⟨f x :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run xs.length (.running q (beforeRightPath xs left y right)) =
      .running q (afterRightPathMap xs f left y right) := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeRightPath, afterRightPathMap, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp,
            run]
          simp only [beforeRightPath, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeRightPath (z :: zs) (f x :: left) y right)) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterRightPathMap, List.append_assoc]

theorem reaches_readHeadMatch_of (slot : Bool) (seekState : State)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hmatch : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, head, right⟩) =
        .running (.readPhase .returning slot) ⟨left, y, head :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore readBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    Reaches
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left) head suffix)) := by
  have h₀ : Reaches
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix)) :=
    ⟨path.length, run_right_path_of seekState path hpass
      (ulogCore readBoundary :: left) head suffix⟩
  have h₁ : Reaches
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.readPhase .returning slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
    apply reaches_step
    cases hr : path.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, hr] using
          (hmatch left (ulogCore readBoundary) suffix)
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (hmatch (xs ++ ulogCore readBoundary :: left) x suffix)
  have h₂ : Reaches
      (.running (.readPhase .returning slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix)))
      (.running (.readPhase .returning slot)
        (afterLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) :=
    ⟨path.reverse.length,
      run_left_path_of (.readPhase .returning slot) path.reverse (by
        intro x hx l y r
        have hx' : x ∈ path := by simpa using hx
        have h := hreturn x hx'
        exact readReturn_pass slot x h.1 h.2 l y r)
        left (ulogCore readBoundary) (head :: suffix)⟩
  have h₃ : Reaches
      (.running (.readPhase .returning slot)
        (afterLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix)))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left) head suffix)) := by
    apply reaches_step
    cases path with
    | nil =>
        simpa [afterLeftPath, beforeRightPath] using
          (readReturn_boundary slot left head suffix)
    | cons x xs =>
        simpa [afterLeftPath, beforeRightPath, List.append_assoc] using
          (readReturn_boundary slot left x (xs ++ head :: suffix))
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

theorem reaches_readHeadMismatch_of (slot : Bool) (seekState : State)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hmismatch : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, head, right⟩) =
        .running (.restoreRule slot) ⟨left, y, head :: right⟩)
    (left suffix : List Tape) :
    Reaches
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
  have h₀ : Reaches
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix)) :=
    ⟨path.length, run_right_path_of seekState path hpass
      (ulogCore readBoundary :: left) head suffix⟩
  have h₁ : Reaches
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
    apply reaches_step
    cases hr : path.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, hr] using
          (hmismatch left (ulogCore readBoundary) suffix)
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (hmismatch (xs ++ ulogCore readBoundary :: left) x suffix)
  exact reaches_trans h₀ h₁

def ReadCorridorSafe (path : List Tape) : Prop :=
  ∀ x ∈ path,
    x ≠ ulogCore payloadHeadZero ∧
      x ≠ ulogCore payloadHeadOne ∧
        x ≠ ulogCore payloadHeadBlank ∧
          x ≠ MStarConcreteAlphabet.work ∧
            x ≠ ulogCore readBoundary ∧ x ≠ ulogCore pcMark

theorem reaches_readZero_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadZero) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  exact reaches_readHeadMatch_of slot (.readPhase .seekZero slot)
    (ulogCore payloadHeadZero) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekZero_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekZero_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩)
    left suffix

theorem reaches_readOne_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadOne) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  exact reaches_readHeadMatch_of slot (.readPhase .seekOne slot)
    (ulogCore payloadHeadOne) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekOne_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekOne_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩)
    left suffix

theorem reaches_readBlank_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadBlank) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  exact reaches_readHeadMatch_of slot (.readPhase .seekBlank slot)
    (ulogCore payloadHeadBlank) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekBlank_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekBlank_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩)
    left suffix

theorem reaches_readZero_match (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  have h₀ : Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadZero) suffix)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, fieldCompare_read_zero, List.append_assoc]
  exact reaches_trans h₀ (reaches_readZero_head slot path hpath left suffix)

theorem reaches_readOne_match (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ ulogCore payloadHeadOne :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  have h₀ : Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ ulogCore payloadHeadOne :: suffix⟩)
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path
          (ulogCore readBoundary :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
    refine ⟨2, ?_⟩
    cases path <;>
      simp [run, beforeRightPath, fieldCompare_read_more,
        readCountOne_done, List.append_assoc]
  exact reaches_trans h₀
    (reaches_readOne_head slot path hpath (ulogCore codeZero :: left) suffix)

theorem reaches_readBlank_match (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ ulogCore payloadHeadBlank :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  have h₀ : Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ ulogCore payloadHeadBlank :: suffix⟩)
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path
          (ulogCore readBoundary :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
    refine ⟨3, ?_⟩
    cases path <;>
      simp [run, beforeRightPath, fieldCompare_read_more,
        readCountOne_more, readCountTwo_done, List.append_assoc]
  exact reaches_trans h₀
    (reaches_readBlank_head slot path hpath
      (ulogCore codeZero :: ulogCore codeZero :: left) suffix)

theorem reaches_readZero_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          codeTape slot :: path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  have h₀ := reaches_readZero_match slot (codeTape slot :: path)
    hpath left suffix
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore codeOne :: left) (ulogCore payloadHeadZero) suffix))
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, fieldCompare_slot_match, List.append_assoc]
  exact reaches_trans h₀ h₁

theorem reaches_readOne_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadOne :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  have h₀ := reaches_readOne_match slot (codeTape slot :: path)
    hpath left suffix
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore codeOne :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix))
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, fieldCompare_slot_match, List.append_assoc]
  exact reaches_trans h₀ h₁

theorem reaches_readBlank_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Reaches
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadBlank :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  have h₀ := reaches_readBlank_match slot (codeTape slot :: path)
    hpath left suffix
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix))
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, fieldCompare_slot_match, List.append_assoc]
  exact reaches_trans h₀ h₁

theorem reaches_actionWriteHead_of (seekState : State)
    (oldHead newHead : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hwrite : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, oldHead, right⟩) =
        .running (.actionPhase .writeReturning)
          ⟨left, y, newHead :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore actionBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    Reaches
      (.running seekState
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left) newHead suffix)) := by
  have h₀ : Reaches
      (.running seekState
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running seekState
        (afterRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix)) :=
    ⟨path.length, run_right_path_of seekState path hpass
      (ulogCore actionBoundary :: left) oldHead suffix⟩
  have h₁ : Reaches
      (.running seekState
        (afterRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running (.actionPhase .writeReturning)
        (beforeLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix))) := by
    apply reaches_step
    cases hr : path.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, hr] using
          (hwrite left (ulogCore actionBoundary) suffix)
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (hwrite (xs ++ ulogCore actionBoundary :: left) x suffix)
  have h₂ : Reaches
      (.running (.actionPhase .writeReturning)
        (beforeLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix)))
      (.running (.actionPhase .writeReturning)
        (afterLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix))) :=
    ⟨path.reverse.length,
      run_left_path_of (.actionPhase .writeReturning) path.reverse (by
        intro x hx l y r
        have hx' : x ∈ path := by simpa using hx
        have h := hreturn x hx'
        exact actionWriteReturn_pass x h.1 h.2 l y r)
        left (ulogCore actionBoundary) (newHead :: suffix)⟩
  have h₃ : Reaches
      (.running (.actionPhase .writeReturning)
        (afterLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left) newHead suffix)) := by
    apply reaches_step
    cases path with
    | nil =>
        simpa [afterLeftPath, beforeRightPath] using
          (actionWriteReturn_boundary left newHead suffix)
    | cons x xs =>
        simpa [afterLeftPath, beforeRightPath, List.append_assoc] using
          (actionWriteReturn_boundary left x (xs ++ newHead :: suffix))
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

def ActionWriteCorridorSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, choiceHead x = false ∧
    x ≠ MStarConcreteAlphabet.work ∧
      x ≠ ulogCore actionBoundary ∧ x ≠ ulogCore pcMark

theorem reaches_actionWriteZero_head (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.actionPhase .seekWriteZero)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  exact reaches_actionWriteHead_of (.actionPhase .seekWriteZero)
    oldHead (ulogCore payloadHeadZero) path
    (fun x hx l y r =>
      actionSeekWriteZero_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteZero_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

theorem reaches_actionWriteOne_head (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.actionPhase .seekWriteOne)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  exact reaches_actionWriteHead_of (.actionPhase .seekWriteOne)
    oldHead (ulogCore payloadHeadOne) path
    (fun x hx l y r =>
      actionSeekWriteOne_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteOne_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

theorem reaches_actionWriteBlank_head (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running (.actionPhase .seekWriteBlank)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  exact reaches_actionWriteHead_of (.actionPhase .seekWriteBlank)
    oldHead (ulogCore payloadHeadBlank) path
    (fun x hx l y r =>
      actionSeekWriteBlank_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteBlank_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

theorem reaches_actionWriteZero (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeOne, path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  have h₀ : Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeOne, path ++ oldHead :: suffix⟩)
      (.running (.actionPhase .seekWriteZero)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, actionWrite_zero, List.append_assoc]
  exact reaches_trans h₀
    (reaches_actionWriteZero_head oldHead hhead path hpath left suffix)

theorem reaches_actionWriteOne (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  have h₀ : Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ oldHead :: suffix⟩)
      (.running (.actionPhase .seekWriteOne)
        (beforeRightPath path
          (ulogCore actionBoundary :: ulogCore codeZero :: left)
          oldHead suffix)) := by
    refine ⟨2, ?_⟩
    cases path <;>
      simp [run, beforeRightPath, actionWrite_more,
        actionWriteOne_done, List.append_assoc]
  exact reaches_trans h₀
    (reaches_actionWriteOne_head oldHead hhead path hpath
      (ulogCore codeZero :: left) suffix)

theorem reaches_actionWriteBlank (oldHead : Tape)
    (hhead : choiceHead oldHead = true) (path : List Tape)
    (hpath : ActionWriteCorridorSafe path) (left suffix : List Tape) :
    Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  have h₀ : Reaches
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ oldHead :: suffix⟩)
      (.running (.actionPhase .seekWriteBlank)
        (beforeRightPath path
          (ulogCore actionBoundary :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          oldHead suffix)) := by
    refine ⟨3, ?_⟩
    cases path <;>
      simp [run, beforeRightPath, actionWrite_more,
        actionWriteOne_more, actionWriteTwo_done, List.append_assoc]
  exact reaches_trans h₀
    (reaches_actionWriteBlank_head oldHead hhead path hpath
      (ulogCore codeZero :: ulogCore codeZero :: left) suffix)

def TargetRoundCorridorSafe (path : List Tape) : Prop :=
  ∀ x ∈ path,
    x ≠ ulogCore stateMark ∧ x ≠ ulogCore stateZero ∧
      x ≠ ulogCore stateOne ∧ x ≠ MStarConcreteAlphabet.work ∧
        x ≠ ulogCore targetMark ∧ x ≠ ulogCore pcMark

def targetScanPath (path : List Tape) (done : ℕ) : List Tape :=
  path ++ List.replicate done (ulogCore stateMark)

theorem targetScanPath_seek_safe (path : List Tape) (done : ℕ)
    (hpath : TargetRoundCorridorSafe path) {x : Tape}
    (hx : x ∈ targetScanPath path done) :
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
      x ≠ MStarConcreteAlphabet.work := by
  unfold targetScanPath at hx
  rcases List.mem_append.mp hx with hp | hm
  · have h := hpath x hp
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
  · have h : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hm
    rw [h.2]
    decide

theorem targetScanPath_return_safe (path : List Tape) (done : ℕ)
    (hpath : TargetRoundCorridorSafe path) {x : Tape}
    (hx : x ∈ targetScanPath path done) :
    x ≠ ulogCore targetMark ∧ x ≠ ulogCore pcMark := by
  unfold targetScanPath at hx
  rcases List.mem_append.mp hx with hp | hm
  · have h := hpath x hp
    exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  · have h : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hm
    rw [h.2]
    decide

theorem reaches_targetRoundExisting (path : List Tape) (hpath : path ≠ [])
    (done : ℕ) (hsafe : TargetRoundCorridorSafe path)
    (left stateRest : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          targetScanPath path done ++ ulogCore stateZero :: stateRest⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++ stateRest))) := by
  let scanPath := targetScanPath path done
  have h₀ : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateZero :: stateRest⟩)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest)) := by
    apply reaches_step
    cases scanPath <;>
      simp [beforeRightPath, actionTarget_zero, List.append_assoc]
  have h₁ : Reaches
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest)) :=
    ⟨scanPath.length,
      run_right_path_of (.actionPhase .targetSeekState) scanPath (by
        intro x hx l y r
        by_cases hm : x = ulogCore stateMark
        · subst x
          exact targetSeekState_mark l y r
        · have h := targetScanPath_seek_safe path done hsafe hx
          exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
        (ulogCore targetMark :: left) (ulogCore stateZero) stateRest⟩
  have h₂ : Reaches
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest))) := by
    apply reaches_step
    cases hr : scanPath.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, hr] using
          (targetSeekState_zero left (ulogCore targetMark) stateRest)
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (targetSeekState_zero (xs ++ ulogCore targetMark :: left)
            x stateRest)
  have h₃ : Reaches
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest)))
      (.running (.actionPhase .targetReturning)
        (afterLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest))) :=
    ⟨scanPath.reverse.length,
      run_left_path_of (.actionPhase .targetReturning) scanPath.reverse (by
        intro x hx l y r
        have hx' : x ∈ scanPath := by simpa using hx
        have h := targetScanPath_return_safe path done hsafe hx'
        exact targetReturning_pass x h.1 h.2 l y r)
        left (ulogCore targetMark) (ulogCore stateMark :: stateRest)⟩
  have h₄ : Reaches
      (.running (.actionPhase .targetReturning)
        (afterLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++ stateRest))) := by
    apply reaches_step
    have hscan : scanPath.reverse.reverse =
        path ++ List.replicate done (ulogCore stateMark) := by
      simp [scanPath, targetScanPath]
    rw [show afterLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest) =
        ⟨left, ulogCore targetMark,
          path ++ List.replicate (done + 1) (ulogCore stateMark) ++
            stateRest⟩ by
      simp [afterLeftPath, hscan, List.replicate_succ',
        List.append_assoc]]
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [beforeRightPath, hp, List.replicate_succ,
          List.append_assoc] using
          (targetReturning_mark left x
            (xs ++ List.replicate (done + 1) (ulogCore stateMark) ++
              stateRest))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ h₄)))

def targetGrowReturnPath (scanPath : List Tape) : List Tape :=
  ulogCore stateOne :: ulogCore stateMark :: scanPath.reverse

theorem targetGrowReturnPath_safe (path : List Tape) (done : ℕ)
    (hsafe : TargetRoundCorridorSafe path) {x : Tape}
    (hx : x ∈ targetGrowReturnPath (targetScanPath path done)) :
    x ≠ ulogCore targetMark ∧ x ≠ ulogCore pcMark := by
  unfold targetGrowReturnPath at hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · decide
  · decide
  · have hx' : x ∈ targetScanPath path done := by simpa using hx
    exact targetScanPath_return_safe path done hsafe hx'

theorem reaches_targetRoundGrow (path : List Tape) (hpath : path ≠ [])
    (done : ℕ) (hsafe : TargetRoundCorridorSafe path)
    (left tail : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          targetScanPath path done ++ ulogCore stateOne ::
            ulogCore stateSep :: MStarConcreteAlphabet.work :: tail⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  let scanPath := targetScanPath path done
  let returnPath := targetGrowReturnPath scanPath
  have h₀ : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) := by
    apply reaches_step
    cases scanPath <;>
      simp [beforeRightPath, actionTarget_zero, List.append_assoc]
  have h₁ : Reaches
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) :=
    ⟨scanPath.length,
      run_right_path_of (.actionPhase .targetSeekState) scanPath (by
        intro x hx l y r
        by_cases hm : x = ulogCore stateMark
        · subst x
          exact targetSeekState_mark l y r
        · have h := targetScanPath_seek_safe path done hsafe hx
          exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
        (ulogCore targetMark :: left) (ulogCore stateOne)
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)⟩
  have h₂ : Reaches
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail))) := by
    refine ⟨3, ?_⟩
    cases hr : scanPath.reverse with
    | nil =>
        simp [run, afterRightPath, beforeLeftPath, returnPath,
          targetGrowReturnPath, hr, targetSeekState_one,
          targetGrowSep_step, targetGrowPlaceSep_step]
    | cons x xs =>
        simp [run, afterRightPath, beforeLeftPath, returnPath,
          targetGrowReturnPath, hr, targetSeekState_one,
          targetGrowSep_step, targetGrowPlaceSep_step,
          List.append_assoc]
  have h₃ : Reaches
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetReturning)
        (afterLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail))) :=
    ⟨returnPath.length,
      run_left_path_of (.actionPhase .targetReturning) returnPath (by
        intro x hx l y r
        have h := targetGrowReturnPath_safe path done hsafe (by
          simpa [returnPath, scanPath] using hx)
        exact targetReturning_pass x h.1 h.2 l y r)
        left (ulogCore targetMark) (ulogCore stateSep :: tail)⟩
  have h₄ : Reaches
      (.running (.actionPhase .targetReturning)
        (afterLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply reaches_step
    have hreturn : returnPath.reverse =
        path ++ List.replicate (done + 1) (ulogCore stateMark) ++
          [ulogCore stateOne] := by
      simp [returnPath, targetGrowReturnPath, scanPath, targetScanPath,
        List.reverse_append, List.replicate_succ', List.append_assoc]
    rw [show afterLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail) =
        ⟨left, ulogCore targetMark,
          path ++ List.replicate (done + 1) (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
      simp [afterLeftPath, hreturn, List.append_assoc]]
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [beforeRightPath, hp, List.replicate_succ,
          List.append_assoc] using
          (targetReturning_mark left x
            (xs ++ List.replicate (done + 1) (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ h₄)))

def TargetFinishCorridorSafe (path : List Tape) : Prop :=
  ∀ x ∈ path,
    x ≠ ulogCore stateMark ∧ x ≠ ulogCore stateZero ∧
      x ≠ ulogCore stateOne ∧ x ≠ MStarConcreteAlphabet.work ∧
        x ≠ ulogCore targetBoundary ∧ x ≠ ulogCore pcMark

def targetFinishPath (path : List Tape) (done : ℕ) : List Tape :=
  path ++ List.replicate done (ulogCore stateMark)

def restoreTargetCell (x : Tape) : Tape :=
  if x = ulogCore stateMark then ulogCore stateZero else x

theorem restoreTargetCell_path (path : List Tape)
    (hsafe : TargetFinishCorridorSafe path) :
    path.map restoreTargetCell = path := by
  induction path with
  | nil => rfl
  | cons x xs ih =>
      have hx := hsafe x (by simp)
      have hxs : TargetFinishCorridorSafe xs := by
        intro y hy
        exact hsafe y (by simp [hy])
      simp [restoreTargetCell, hx.1, ih hxs]

theorem targetFinishPath_seek_safe (path : List Tape) (done : ℕ)
    (hsafe : TargetFinishCorridorSafe path) {x : Tape}
    (hx : x ∈ targetFinishPath path done) :
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
      x ≠ MStarConcreteAlphabet.work := by
  unfold targetFinishPath at hx
  rcases List.mem_append.mp hx with hp | hm
  · have h := hsafe x hp
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
  · have h : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hm
    rw [h.2]
    native_decide

theorem targetFinishPath_restore_safe (path : List Tape) (done : ℕ)
    (hsafe : TargetFinishCorridorSafe path) {x : Tape}
    (hx : x ∈ targetFinishPath path done) :
    x ≠ ulogCore targetBoundary ∧ x ≠ ulogCore pcMark := by
  unfold targetFinishPath at hx
  rcases List.mem_append.mp hx with hp | hm
  · have h := hsafe x hp
    exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  · have h : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hm
    rw [h.2]
    decide

theorem reaches_targetFinishSeenOne_many_core (done : ℕ)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    Reaches
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨left, ulogCore stateMark,
          List.replicate done (ulogCore stateMark) ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishMany)
        ⟨List.replicate (done + 1) (ulogCore stateMark) ++ left,
          terminal, right⟩) := by
  have h₀ : Reaches
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨left, ulogCore stateMark,
          List.replicate done (ulogCore stateMark) ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishMany)
        (beforeRightPath (List.replicate done (ulogCore stateMark))
          (ulogCore stateMark :: left) terminal right)) := by
    apply reaches_step
    cases done <;>
      simp [beforeRightPath, targetFinishSeenOne_mark_core,
        List.replicate_succ]
  have h₁ : Reaches
      (.running (.actionPhase .targetFinishMany)
        (beforeRightPath (List.replicate done (ulogCore stateMark))
          (ulogCore stateMark :: left) terminal right))
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath (List.replicate done (ulogCore stateMark))
          (ulogCore stateMark :: left) terminal right)) :=
    ⟨_, run_right_path_of (.actionPhase .targetFinishMany)
      (List.replicate done (ulogCore stateMark)) (by
        intro x hx l y r
        have heq : x = ulogCore stateMark :=
          (by simpa only [List.mem_replicate] using hx :
            done ≠ 0 ∧ x = ulogCore stateMark).2
        rw [heq]
        exact targetFinishMany_mark_core l y r)
      (ulogCore stateMark :: left) terminal right⟩
  simpa [afterRightPath, List.replicate_succ, List.append_assoc] using
    reaches_trans h₀ h₁

theorem reaches_targetFinishSeek_accept (path : List Tape)
    (hsafe : TargetFinishCorridorSafe path) (left : List Tape)
    (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    Reaches
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path left terminal right))
      (.accepted (afterRightPath path left terminal right)) := by
  have hscan : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path left terminal right))
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path left terminal right)) :=
    ⟨path.length, run_right_path_of (.actionPhase .targetFinishSeek)
      path (by
        intro x hx l y r
        have h := hsafe x hx
        exact targetFinishSeek_pass x h.1 h.2.1 h.2.2.1 h.2.2.2.1
          l y r)
      left terminal right⟩
  have hhalt : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path left terminal right))
      (.accepted (afterRightPath path left terminal right)) := by
    apply reaches_step
    rcases hterminal with rfl | rfl
    · exact targetFinishSeek_shorter _ _
    · exact targetFinishSeek_one_any _ _
  exact reaches_trans hscan hhalt

theorem reaches_actionTargetFinishSeek_accept (path : List Tape)
    (hsafe : TargetFinishCorridorSafe path) (left : List Tape)
    (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne, path ++ terminal :: right⟩)
      (.accepted
        (afterRightPath path (ulogCore targetBoundary :: left)
          terminal right)) := by
  have hstart : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne, path ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path (ulogCore targetBoundary :: left)
          terminal right)) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, actionTarget_done, List.append_assoc]
  exact reaches_trans hstart
    (reaches_targetFinishSeek_accept path hsafe
      (ulogCore targetBoundary :: left) terminal hterminal right)

theorem reaches_targetFinishOneMark_reject (path : List Tape)
    (hsafe : TargetFinishCorridorSafe path) (left : List Tape)
    (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          path ++ ulogCore stateMark :: terminal :: right⟩)
      .rejected := by
  have hstart : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          path ++ ulogCore stateMark :: terminal :: right⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right))) := by
    apply reaches_step
    cases path <;>
      simp [beforeRightPath, actionTarget_done, List.append_assoc]
  have hscan : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right)))
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right))) :=
    ⟨path.length, run_right_path_of (.actionPhase .targetFinishSeek)
      path (by
        intro x hx l y r
        have h := hsafe x hx
        exact targetFinishSeek_pass x h.1 h.2.1 h.2.2.1 h.2.2.2.1
          l y r)
      (ulogCore targetBoundary :: left) (ulogCore stateMark)
      (terminal :: right)⟩
  have hmark : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right)))
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left,
          terminal, right⟩) := by
    apply reaches_step
    simpa [afterRightPath, List.append_assoc] using
      (targetFinishSeek_mark
        (path.reverse ++ ulogCore targetBoundary :: left) terminal right)
  have hreject : Reaches
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left,
          terminal, right⟩)
      .rejected := by
    apply reaches_step
    rcases hterminal with rfl | rfl
    · exact targetFinishSeenOne_zero_reject_core _ _
    · exact targetFinishSeenOne_one_reject_core _ _
  exact reaches_trans hstart
    (reaches_trans hscan (reaches_trans hmark hreject))

theorem reaches_targetFinishEqual (path : List Tape) (hpath : path ≠ [])
    (done : ℕ) (hdone : 2 ≤ done)
    (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateOne ::
            ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
  obtain ⟨k, rfl⟩ : ∃ k, done = k + 2 :=
    ⟨done - 2, by omega⟩
  let finishPath := targetFinishPath path (k + 2)
  have h₀ : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    apply reaches_step
    cases finishPath <;>
      simp [beforeRightPath, actionTarget_done, List.append_assoc]
  have h₁ : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    have hscan : Reaches
        (.running (.actionPhase .targetFinishSeek)
          (beforeRightPath finishPath (ulogCore targetBoundary :: left)
            (ulogCore stateOne) (ulogCore stateSep :: tail)))
        (.running (.actionPhase .targetFinishSeek)
          ⟨path.reverse ++ ulogCore targetBoundary :: left,
            ulogCore stateMark,
            ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
      have hrun : Reaches
          (.running (.actionPhase .targetFinishSeek)
            (beforeRightPath path (ulogCore targetBoundary :: left)
              (ulogCore stateMark)
              (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)))
          (.running (.actionPhase .targetFinishSeek)
            (afterRightPath path (ulogCore targetBoundary :: left)
              (ulogCore stateMark)
              (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep :: tail))) :=
        ⟨path.length, run_right_path_of (.actionPhase .targetFinishSeek)
          path (by
            intro x hx l y r
            have h := hsafe x hx
            exact targetFinishSeek_pass x h.1 h.2.1 h.2.2.1
              h.2.2.2.1 l y r)
          (ulogCore targetBoundary :: left) (ulogCore stateMark)
          (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)⟩
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [finishPath, targetFinishPath, beforeRightPath,
            afterRightPath, hp, List.replicate_succ,
            List.append_assoc] using hrun
    have hfirst : Reaches
        (.running (.actionPhase .targetFinishSeek)
          ⟨path.reverse ++ ulogCore targetBoundary :: left,
            ulogCore stateMark,
            ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
        (.running (.actionPhase .targetFinishSeenOne)
          ⟨ulogCore stateMark :: path.reverse ++
              ulogCore targetBoundary :: left,
            ulogCore stateMark,
            List.replicate k (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) :=
      reaches_step (targetFinishSeek_mark _ _ _)
    have hmany := reaches_targetFinishSeenOne_many_core k
      (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
      (ulogCore stateOne) (ulogCore stateSep :: tail)
    have hleftEq :
        List.replicate (k + 1) (ulogCore stateMark) ++
            (ulogCore stateMark ::
              path.reverse ++ ulogCore targetBoundary :: left) =
          ulogCore stateMark :: ulogCore stateMark ::
            List.replicate k (ulogCore stateMark) ++
              (path.reverse ++ ulogCore targetBoundary :: left) := by
      simp [List.replicate_succ, List.append_assoc]
    rw [hleftEq] at hmany
    simpa [finishPath, targetFinishPath, afterRightPath,
      List.replicate_succ, List.append_assoc] using
      reaches_trans hscan (reaches_trans hfirst
        (by simpa [← List.replicate_add, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmany))
  have h₂ : Reaches
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath finishPath.reverse left (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply reaches_step
    cases hr : finishPath.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, hr] using
          (targetFinishMany_one_core left (ulogCore targetBoundary)
            (ulogCore stateSep :: tail))
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (targetFinishMany_one_core (xs ++ ulogCore targetBoundary :: left)
            x (ulogCore stateSep :: tail))
  have h₃ : Reaches
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath finishPath.reverse left (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap finishPath.reverse restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail))) :=
    ⟨finishPath.reverse.length,
      run_left_path_map_of (.actionPhase .targetRestoreState)
        finishPath.reverse restoreTargetCell (by
          intro x hx l y r
          have hx' : x ∈ finishPath := by simpa using hx
          by_cases hm : x = ulogCore stateMark
          · subst x
            simpa [restoreTargetCell] using targetRestoreState_mark l y r
          · have h := targetFinishPath_restore_safe path (k + 2) hsafe hx'
            simpa [restoreTargetCell, hm] using
              targetRestoreState_pass x hm h.1 h.2 l y r)
        left (ulogCore targetBoundary)
        (ulogCore stateOne :: ulogCore stateSep :: tail)⟩
  have h₄ : Reaches
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap finishPath.reverse restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate (k + 2) (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
    apply reaches_step
    have hmap : finishPath.map restoreTargetCell =
        path ++ List.replicate (k + 2) (ulogCore stateZero) := by
      simp [finishPath, targetFinishPath, List.map_append,
        restoreTargetCell_path path hsafe, restoreTargetCell]
    rw [show afterLeftPathMap finishPath.reverse restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail) =
        ⟨left, ulogCore targetBoundary,
          path ++ List.replicate (k + 2) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [beforeRightPath, hp, List.append_assoc] using
          (targetRestoreState_boundary left x
            (xs ++ List.replicate (k + 2) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ h₄)))

theorem reaches_targetShrink (extra : ℕ) (left tail : List Tape) :
    Reaches
      (.running (.actionPhase .targetShrink)
        ⟨left, ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        ⟨left, ulogCore stateOne,
          ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
  have h₀ : Reaches
      (.running (.actionPhase .targetShrink)
        ⟨left, ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetShrinkErase)
        (beforeRightPath (List.replicate extra (ulogCore stateZero))
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
    apply reaches_step
    cases extra <;>
      simp [beforeRightPath, targetShrink_start,
        List.replicate_succ, List.append_assoc]
  have h₁ : Reaches
      (.running (.actionPhase .targetShrinkErase)
        (beforeRightPath (List.replicate extra (ulogCore stateZero))
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrinkErase)
        (afterRightPathMap (List.replicate extra (ulogCore stateZero))
          (fun _ => MStarConcreteAlphabet.work)
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) :=
    ⟨(List.replicate extra (ulogCore stateZero)).length,
      run_right_path_map_of (.actionPhase .targetShrinkErase)
        (List.replicate extra (ulogCore stateZero))
        (fun _ => MStarConcreteAlphabet.work) (by
          intro x hx l y r
          have hm : extra ≠ 0 ∧ x = ulogCore stateZero := by
            simpa only [List.mem_replicate] using hx
          rw [hm.2]
          exact targetShrinkErase_zero l y r)
        (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
        (ulogCore stateSep :: tail)⟩
  have h₂ : Reaches
      (.running (.actionPhase .targetShrinkErase)
        (afterRightPathMap (List.replicate extra (ulogCore stateZero))
          (fun _ => MStarConcreteAlphabet.work)
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrinkEraseOne)
        ⟨MStarConcreteAlphabet.work ::
            List.replicate extra MStarConcreteAlphabet.work ++
              ulogCore stateShrinkBoundary :: left,
          ulogCore stateSep, tail⟩) := by
    apply reaches_step
    simpa [afterRightPathMap, List.append_assoc] using
      (targetShrinkErase_one
        (List.replicate extra MStarConcreteAlphabet.work ++
          ulogCore stateShrinkBoundary :: left)
        (ulogCore stateSep) tail)
  have h₃ : Reaches
      (.running (.actionPhase .targetShrinkEraseOne)
        ⟨MStarConcreteAlphabet.work ::
            List.replicate extra MStarConcreteAlphabet.work ++
              ulogCore stateShrinkBoundary :: left,
          ulogCore stateSep, tail⟩)
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (beforeLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail))) := by
    apply reaches_step
    simpa [beforeLeftPath, List.replicate_succ,
      List.append_assoc] using
      (targetShrinkEraseOne_sep
        (List.replicate extra MStarConcreteAlphabet.work ++
          ulogCore stateShrinkBoundary :: left)
        MStarConcreteAlphabet.work tail)
  have h₄ : Reaches
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (beforeLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (afterLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail))) :=
    ⟨(List.replicate (extra + 1) MStarConcreteAlphabet.work).length,
      run_left_path_of (.actionPhase .targetShrinkReturnBoundary)
        (List.replicate (extra + 1) MStarConcreteAlphabet.work) (by
          intro x hx l y r
          have hm : extra + 1 ≠ 0 ∧ x = MStarConcreteAlphabet.work := by
            simpa only [List.mem_replicate] using hx
          rw [hm.2]
          exact targetShrinkReturn_work l y r)
        left (ulogCore stateShrinkBoundary)
        (MStarConcreteAlphabet.work :: tail)⟩
  have h₅ : Reaches
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (afterLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetRestoreState)
        ⟨left, ulogCore stateOne,
          ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
    have ha : Reaches
        (.running (.actionPhase .targetShrinkReturnBoundary)
          (afterLeftPath
            (List.replicate (extra + 1) MStarConcreteAlphabet.work)
            left (ulogCore stateShrinkBoundary)
            (MStarConcreteAlphabet.work :: tail)))
        (.running (.actionPhase .targetShrinkPlaceSep)
          ⟨ulogCore stateOne :: left, MStarConcreteAlphabet.work,
            List.replicate extra MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work :: tail⟩) := by
      apply reaches_step
      simpa [afterLeftPath, List.replicate_succ,
        List.append_assoc] using
        (targetShrinkReturn_boundary left MStarConcreteAlphabet.work
          (List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail))
    have hb : Reaches
        (.running (.actionPhase .targetShrinkPlaceSep)
          ⟨ulogCore stateOne :: left, MStarConcreteAlphabet.work,
            List.replicate extra MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work :: tail⟩)
        (.running (.actionPhase .targetRestoreState)
          ⟨left, ulogCore stateOne,
            ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
      apply reaches_step
      simpa [List.replicate_succ, List.append_assoc] using
        (targetShrinkPlaceSep_step left (ulogCore stateOne)
          (List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail))
    exact reaches_trans ha hb
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

theorem reaches_targetFinishShorter (path : List Tape) (hpath : path ≠ [])
    (done extra : ℕ) (hdone : 2 ≤ done)
    (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
  obtain ⟨k, rfl⟩ : ∃ k, done = k + 2 :=
    ⟨done - 2, by omega⟩
  let finishPath := targetFinishPath path (k + 2)
  have h₀ : Reaches
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply reaches_step
    cases finishPath <;>
      simp [beforeRightPath, actionTarget_done, List.append_assoc]
  have h₁ : Reaches
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    have hscan : Reaches
        (.running (.actionPhase .targetFinishSeek)
          (beforeRightPath finishPath (ulogCore targetBoundary :: left)
            (ulogCore stateZero)
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail)))
        (.running (.actionPhase .targetFinishSeek)
          ⟨path.reverse ++ ulogCore targetBoundary :: left,
            ulogCore stateMark,
            ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
              ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
      have hrun : Reaches
          (.running (.actionPhase .targetFinishSeek)
            (beforeRightPath path (ulogCore targetBoundary :: left)
              (ulogCore stateMark)
              (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
                ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail)))
          (.running (.actionPhase .targetFinishSeek)
            (afterRightPath path (ulogCore targetBoundary :: left)
              (ulogCore stateMark)
              (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
                ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail))) :=
        ⟨path.length, run_right_path_of (.actionPhase .targetFinishSeek)
          path (by
            intro x hx l y r
            have h := hsafe x hx
            exact targetFinishSeek_pass x h.1 h.2.1 h.2.2.1
              h.2.2.2.1 l y r)
          (ulogCore targetBoundary :: left) (ulogCore stateMark)
          (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail)⟩
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [finishPath, targetFinishPath, beforeRightPath,
            afterRightPath, hp, List.replicate_succ,
            List.append_assoc] using hrun
    have hfirst : Reaches
        (.running (.actionPhase .targetFinishSeek)
          ⟨path.reverse ++ ulogCore targetBoundary :: left,
            ulogCore stateMark,
            ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
              ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail⟩)
        (.running (.actionPhase .targetFinishSeenOne)
          ⟨ulogCore stateMark :: path.reverse ++
              ulogCore targetBoundary :: left,
            ulogCore stateMark,
            List.replicate k (ulogCore stateMark) ++
              ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail⟩) :=
      reaches_step (targetFinishSeek_mark _ _ _)
    have hmany := reaches_targetFinishSeenOne_many_core k
      (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
      (ulogCore stateZero)
      (List.replicate extra (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: tail)
    have hleftEq :
        List.replicate (k + 1) (ulogCore stateMark) ++
            (ulogCore stateMark ::
              path.reverse ++ ulogCore targetBoundary :: left) =
          ulogCore stateMark :: ulogCore stateMark ::
            List.replicate k (ulogCore stateMark) ++
              (path.reverse ++ ulogCore targetBoundary :: left) := by
      simp [List.replicate_succ, List.append_assoc]
    rw [hleftEq] at hmany
    simpa [finishPath, targetFinishPath, afterRightPath,
      List.replicate_succ, List.append_assoc] using
      reaches_trans hscan (reaches_trans hfirst
        (by simpa [← List.replicate_add, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmany))
  have h₂ : Reaches
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply reaches_step
    simpa [afterRightPath] using
      (targetFinishMany_zero_core
        (finishPath.reverse ++ ulogCore targetBoundary :: left)
        (List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
  have h₃ := reaches_targetShrink extra
    (finishPath.reverse ++ ulogCore targetBoundary :: left) tail
  let restorePath := ulogCore stateOne :: finishPath.reverse
  have h₄ : Reaches
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath restorePath left (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)))
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap restorePath restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) :=
    ⟨restorePath.length,
      run_left_path_map_of (.actionPhase .targetRestoreState)
        restorePath restoreTargetCell (by
          intro x hx l y r
          simp only [restorePath, List.mem_cons] at hx
          rcases hx with rfl | hx
          · have hm : ulogCore stateOne ≠ ulogCore stateMark :=
              ULogTapeDecoding.ulog_symbol_ne (by native_decide)
            have hb : ulogCore stateOne ≠ ulogCore targetBoundary :=
              ULogTapeDecoding.ulog_symbol_ne (by native_decide)
            have hp : ulogCore stateOne ≠ ulogCore pcMark :=
              ULogTapeDecoding.ulog_symbol_ne (by native_decide)
            simpa [restoreTargetCell, hm] using
              targetRestoreState_pass (ulogCore stateOne) hm hb hp l y r
          · have hx' : x ∈ finishPath := by simpa using hx
            by_cases hm : x = ulogCore stateMark
            · subst x
              simpa [restoreTargetCell] using targetRestoreState_mark l y r
            · have h := targetFinishPath_restore_safe path (k + 2) hsafe hx'
              simpa [restoreTargetCell, hm] using
                targetRestoreState_pass x hm h.1 h.2 l y r)
        left (ulogCore targetBoundary)
        (ulogCore stateSep ::
          List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)⟩
  have h₅ : Reaches
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap restorePath restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate (k + 2) (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    apply reaches_step
    have honeMark : ulogCore stateOne ≠ ulogCore stateMark :=
      ULogTapeDecoding.ulog_symbol_ne (by native_decide)
    have hmap : restorePath.reverse.map restoreTargetCell =
        path ++ List.replicate (k + 2) (ulogCore stateZero) ++
          [ulogCore stateOne] := by
      simp [restorePath, finishPath, targetFinishPath,
        List.reverse_append, List.map_append,
        restoreTargetCell_path path hsafe, restoreTargetCell, honeMark,
        List.append_assoc]
    rw [show afterLeftPathMap restorePath restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail) =
        ⟨left, ulogCore targetBoundary,
          path ++ List.replicate (k + 2) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [beforeRightPath, hp, List.append_assoc] using
          (targetRestoreState_boundary left x
            (xs ++ List.replicate (k + 2) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))
  have h₃' : Reaches
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath restorePath left (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    simpa [restorePath, beforeLeftPath, List.append_assoc] using h₃
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃' (reaches_trans h₄ h₅))))

def TargetRewriteCorridorSafe (path : List Tape) : Prop :=
  TargetRoundCorridorSafe path ∧ TargetFinishCorridorSafe path

theorem targetCodeCorridor_round_safe (n : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) :
    TargetRoundCorridorSafe
      (List.replicate n (ulogCore codeZero) ++
        ulogCore codeOne :: corridor) := by
  intro x hx
  simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hx
  rcases hx with h | rfl | hx
  · rw [h.2]
    decide
  · decide
  · exact hsafe.1 x hx

theorem targetCodeCorridor_finish_safe (n : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) :
    TargetFinishCorridorSafe
      (List.replicate n (ulogCore codeZero) ++
        ulogCore codeOne :: corridor) := by
  intro x hx
  simp only [List.mem_append, List.mem_replicate, List.mem_cons] at hx
  rcases hx with h | rfl | hx
  · rw [h.2]
    native_decide
  · native_decide
  · exact hsafe.2 x hx

def targetExistingStart (remaining done extra : ℕ)
    (corridor left tail : List Tape) : Result :=
  match remaining with
  | 0 => .running .actionTarget
      ⟨left, ulogCore codeOne,
        corridor ++ List.replicate done (ulogCore stateMark) ++
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩
  | n + 1 => .running .actionTarget
      ⟨left, ulogCore codeZero,
        targetScanPath
            (List.replicate n (ulogCore codeZero) ++
              ulogCore codeOne :: corridor) done ++
          ulogCore stateZero ::
            List.replicate n (ulogCore stateZero) ++
              List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩

def targetExistingDone (remaining done extra : ℕ)
    (corridor left tail : List Tape) : Result :=
  .running .actionTarget
    ⟨List.replicate remaining (ulogCore codeZero) ++ left,
      ulogCore codeOne,
      corridor ++
        List.replicate (done + remaining) (ulogCore stateMark) ++
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩

theorem reaches_targetExistingZeros (remaining done extra : ℕ)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetExistingStart remaining done extra corridor left tail)
      (targetExistingDone remaining done extra corridor left tail) := by
  induction remaining generalizing done left with
  | zero => exact reaches_refl _
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      have hround := reaches_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining (ulogCore stateZero) ++
          List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      have htail := ih (done + 1) (ulogCore codeZero :: left)
      have htail' : Reaches
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                List.replicate remaining (ulogCore stateZero) ++
                  List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail)))
          (targetExistingDone remaining (done + 1) extra corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetExistingStart, path, beforeRightPath,
            targetScanPath, List.replicate_succ, List.replicate_succ',
            List.append_assoc, Nat.add_assoc] using htail
      have hall := reaches_trans hround (by
        simpa only [List.append_assoc, List.cons_append] using htail')
      simpa [targetExistingStart, targetExistingDone, path,
        targetScanPath, List.replicate_succ, List.replicate_succ',
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

def targetGrowStart (remaining done : ℕ)
    (corridor left tail : List Tape) : Result :=
  match remaining with
  | 0 => .running .actionTarget
      ⟨left, ulogCore codeOne,
        corridor ++ List.replicate done (ulogCore stateMark) ++
          ulogCore stateOne :: ulogCore stateSep :: tail⟩
  | n + 1 => .running .actionTarget
      ⟨left, ulogCore codeZero,
        targetScanPath
            (List.replicate n (ulogCore codeZero) ++
              ulogCore codeOne :: corridor) done ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate (n + 1) MStarConcreteAlphabet.work ++ tail⟩

def targetGrowDone (remaining done : ℕ)
    (corridor left tail : List Tape) : Result :=
  .running .actionTarget
    ⟨List.replicate remaining (ulogCore codeZero) ++ left,
      ulogCore codeOne,
      corridor ++
        List.replicate (done + remaining) (ulogCore stateMark) ++
          ulogCore stateOne :: ulogCore stateSep :: tail⟩

theorem reaches_targetGrowZeros (remaining done : ℕ)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetGrowStart remaining done corridor left tail)
      (targetGrowDone remaining done corridor left tail) := by
  induction remaining generalizing done left with
  | zero => exact reaches_refl _
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      have hround := reaches_targetRoundGrow path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining MStarConcreteAlphabet.work ++ tail)
      have htail := ih (done + 1) (ulogCore codeZero :: left)
      have htail' : Reaches
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate remaining MStarConcreteAlphabet.work ++
                    tail)))
          (targetGrowDone remaining (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetGrowStart, path, beforeRightPath, targetScanPath,
            List.replicate_succ, List.replicate_succ', List.append_assoc,
            Nat.add_assoc] using htail
      have hall := reaches_trans hround (by
        simpa only [List.append_assoc, List.cons_append] using htail')
      simpa [targetGrowStart, targetGrowDone, path, targetScanPath,
        List.replicate_succ, List.replicate_succ', List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def targetRewriteFinished (target extra : ℕ)
    (corridor left tail : List Tape) : Result :=
  .running (.actionPhase .moveStart)
    (beforeRightPath
      (corridor ++ List.replicate target (ulogCore stateZero))
      (ulogCore codeOne ::
        List.replicate target (ulogCore codeZero) ++ left)
      (ulogCore stateOne)
      (ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ tail))

theorem reaches_targetExistingFinished (target extra : ℕ)
    (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ target)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetExistingStart target 0 extra corridor left tail)
      (targetRewriteFinished target extra corridor left tail) := by
  have h₀ := reaches_targetExistingZeros target 0 extra corridor hsafe
    left tail
  have h₁ : Reaches
      (targetExistingDone target 0 extra corridor left tail)
      (targetRewriteFinished target extra corridor left tail) := by
    cases extra with
    | zero =>
        simpa [targetExistingDone, targetRewriteFinished,
          targetFinishPath, List.append_assoc] using
          (reaches_targetFinishEqual corridor hcorridor target htarget hsafe.2
            (List.replicate target (ulogCore codeZero) ++ left) tail)
    | succ extra =>
        simpa [targetExistingDone, targetRewriteFinished,
          targetFinishPath, List.replicate_succ, List.append_assoc] using
          (reaches_targetFinishShorter corridor hcorridor target extra htarget hsafe.2
            (List.replicate target (ulogCore codeZero) ++ left) tail)
  exact reaches_trans h₀ h₁

theorem reaches_targetGrowFinished (growth done : ℕ)
    (corridor : List Tape) (hcorridor : corridor ≠ [])
    (hdone : 2 ≤ done + growth)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetGrowStart growth done corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (done + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate growth (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
  have h₀ := reaches_targetGrowZeros growth done corridor hsafe left tail
  have h₁ : Reaches
      (targetGrowDone growth done corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (done + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate growth (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa [targetGrowDone, targetFinishPath, List.append_assoc] using
      (reaches_targetFinishEqual corridor hcorridor (done + growth) hdone hsafe.2
        (List.replicate growth (ulogCore codeZero) ++ left) tail)
  exact reaches_trans h₀ h₁

def targetConsumeStart (remaining growth done : ℕ)
    (corridor left tail : List Tape) : Result :=
  match remaining with
  | 0 => targetGrowStart growth done corridor left tail
  | n + 1 => .running .actionTarget
      ⟨left, ulogCore codeZero,
        targetScanPath
            (List.replicate (growth + n) (ulogCore codeZero) ++
              ulogCore codeOne :: corridor) done ++
          ulogCore stateZero :: List.replicate n (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail⟩

def targetConsumeDone (remaining growth done : ℕ)
    (corridor left tail : List Tape) : Result :=
  targetGrowStart growth (done + remaining) corridor
    (List.replicate remaining (ulogCore codeZero) ++ left) tail

theorem reaches_targetConsumeState (remaining growth done : ℕ)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetConsumeStart remaining growth done corridor left tail)
      (targetConsumeDone remaining growth done corridor left tail) := by
  induction remaining generalizing done left with
  | zero => exact reaches_refl _
  | succ remaining ih =>
      let path := List.replicate (growth + remaining) (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      have hround := reaches_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe (growth + remaining) corridor hsafe)
        left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail)
      have htail := ih (done + 1) (ulogCore codeZero :: left)
      have hround' : Reaches
          (targetConsumeStart (remaining + 1) growth done corridor left tail)
          (targetConsumeStart remaining growth (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        dsimp [path] at hround
        cases remaining with
        | zero =>
            cases growth <;>
              simpa [targetConsumeStart, path, targetGrowStart,
                beforeRightPath, targetScanPath, List.replicate_succ,
                List.replicate_succ', List.cons_append, List.append_assoc,
                Nat.add_assoc] using hround
        | succ remaining =>
            have hcount : growth + (remaining + 1) =
                (growth + remaining) + 1 := by omega
            have hrepl :
                List.replicate (growth + (remaining + 1))
                    (ulogCore codeZero) =
                  ulogCore codeZero ::
                    List.replicate (growth + remaining)
                      (ulogCore codeZero) := by
              rw [hcount, List.replicate_succ]
            simpa [targetConsumeStart, path, targetGrowStart,
              beforeRightPath, targetScanPath, List.replicate_succ,
              List.replicate_succ', List.cons_append, List.append_assoc,
              Nat.add_assoc, hrepl] using hround
      have hall := reaches_trans hround' htail
      simpa [targetConsumeStart, targetConsumeDone, path,
        targetScanPath, List.replicate_succ, List.replicate_succ',
        List.cons_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall

def targetRawStart (target current : ℕ) (corridor left tail : List Tape) :
    Result :=
  match target with
  | 0 => .running .actionTarget
      ⟨left, ulogCore codeOne,
        corridor ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail⟩
  | n + 1 => .running .actionTarget
      ⟨left, ulogCore codeZero,
        List.replicate n (ulogCore codeZero) ++
          ulogCore codeOne :: corridor ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩

theorem reaches_targetRawZero_accept (current : ℕ)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    ∃ z, Reaches (targetRawStart 0 current corridor left tail)
      (.accepted z) := by
  cases current with
  | zero =>
      refine ⟨afterRightPath corridor (ulogCore targetBoundary :: left)
        (ulogCore stateOne) (ulogCore stateSep :: tail), ?_⟩
      simpa [targetRawStart, List.append_assoc] using
        (reaches_actionTargetFinishSeek_accept corridor hsafe.2 left
          (ulogCore stateOne) (Or.inr rfl) (ulogCore stateSep :: tail))
  | succ current =>
      refine ⟨afterRightPath corridor (ulogCore targetBoundary :: left)
        (ulogCore stateZero)
        (List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail), ?_⟩
      simpa [targetRawStart, List.replicate_succ,
        List.append_assoc] using
        (reaches_actionTargetFinishSeek_accept corridor hsafe.2 left
          (ulogCore stateZero) (Or.inl rfl)
          (List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))

theorem reaches_targetRawOneZero_reject
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches
      (targetRawStart 1 0 corridor left
        (MStarConcreteAlphabet.work :: tail)) .rejected := by
  have hwork := reaches_targetGrowZeros 1 0 corridor hsafe left tail
  have hhalt := reaches_targetFinishOneMark_reject corridor hsafe.2
    (ulogCore codeZero :: left) (ulogCore stateOne) (Or.inr rfl)
    (ulogCore stateSep :: tail)
  have hwork' : Reaches
      (targetRawStart 1 0 corridor left (MStarConcreteAlphabet.work :: tail))
      (targetGrowDone 1 0 corridor left tail) := by
    simpa [targetRawStart, targetGrowStart, targetScanPath,
      List.append_assoc] using hwork
  have hhalt' : Reaches (targetGrowDone 1 0 corridor left tail)
      .rejected := by
    simpa [targetGrowDone, List.replicate_succ,
      List.append_assoc] using hhalt
  exact reaches_trans hwork' hhalt'

theorem reaches_targetRawOnePositive_reject (extra : ℕ)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetRawStart 1 (extra + 1) corridor left tail)
      .rejected := by
  have hwork := reaches_targetExistingZeros 1 0 extra corridor hsafe
    left tail
  have hwork' : Reaches
      (targetRawStart 1 (extra + 1) corridor left tail)
      (targetExistingDone 1 0 extra corridor left tail) := by
    simpa [targetRawStart, targetExistingStart,
      targetScanPath, List.replicate_succ,
      List.append_assoc] using hwork
  cases extra with
  | zero =>
      have hhalt := reaches_targetFinishOneMark_reject corridor hsafe.2
        (ulogCore codeZero :: left) (ulogCore stateOne) (Or.inr rfl)
        (ulogCore stateSep :: tail)
      have hhalt' : Reaches
          (targetExistingDone 1 0 0 corridor left tail) .rejected := by
        simpa [targetExistingDone, List.replicate_succ,
          List.append_assoc] using hhalt
      exact reaches_trans hwork' hhalt'
  | succ extra =>
      have hhalt := reaches_targetFinishOneMark_reject corridor hsafe.2
        (ulogCore codeZero :: left) (ulogCore stateZero) (Or.inl rfl)
        (List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      have hhalt' : Reaches
          (targetExistingDone 1 0 (extra + 1) corridor left tail)
          .rejected := by
        simpa [targetExistingDone, List.replicate_succ,
          List.append_assoc] using hhalt
      exact reaches_trans hwork' hhalt'

theorem reaches_targetAtMostState (target extra : ℕ)
    (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ target)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches (targetRawStart target (target + extra) corridor left tail)
      (targetRewriteFinished target extra corridor left tail) := by
  have h := reaches_targetExistingFinished target extra corridor hcorridor
    htarget hsafe left tail
  cases target with
  | zero =>
      simpa [targetRawStart, targetExistingStart,
        List.append_assoc] using h
  | succ target =>
      have hrep :
          List.replicate ((target + 1) + extra) (ulogCore stateZero) =
            ulogCore stateZero ::
              List.replicate target (ulogCore stateZero) ++
                List.replicate extra (ulogCore stateZero) := by
        rw [List.replicate_add, List.replicate_succ]
      simpa [targetRawStart, targetExistingStart, targetScanPath,
        hrep, List.append_assoc] using h

theorem reaches_targetAtLeastState (current growth : ℕ)
    (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ current + growth)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Reaches
      (targetRawStart (current + growth) current corridor left
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++
            List.replicate (current + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
  have h₀ := reaches_targetConsumeState current growth 0 corridor hsafe left
    tail
  have h₁ := reaches_targetGrowFinished growth current corridor hcorridor
    (by simpa [Nat.add_comm] using htarget) hsafe
    (List.replicate current (ulogCore codeZero) ++ left) tail
  have h₁' : Reaches
      (targetConsumeDone current growth 0 corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth)
            (ulogCore stateZero))
          (ulogCore codeOne :: List.replicate growth (ulogCore codeZero) ++
            (List.replicate current (ulogCore codeZero) ++ left))
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa [targetConsumeDone] using h₁
  have hcodes :
      List.replicate growth (ulogCore codeZero) ++
          List.replicate current (ulogCore codeZero) =
        List.replicate (current + growth) (ulogCore codeZero) := by
    rw [← List.replicate_add, Nat.add_comm]
  have hleft :
      ulogCore codeOne :: List.replicate growth (ulogCore codeZero) ++
          (List.replicate current (ulogCore codeZero) ++ left) =
        ulogCore codeOne ::
          List.replicate (current + growth) (ulogCore codeZero) ++ left := by
    simp only [List.cons_append]
    congr 1
    rw [← List.append_assoc, hcodes]
  have h₁'' : Reaches
      (targetConsumeDone current growth 0 corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth)
            (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa only [hleft] using h₁'
  have hsource :
      targetRawStart (current + growth) current corridor left
          (List.replicate growth MStarConcreteAlphabet.work ++ tail) =
        targetConsumeStart current growth 0 corridor left tail := by
    cases current with
    | zero =>
        cases growth <;>
          simp [targetRawStart, targetConsumeStart, targetGrowStart,
            targetScanPath, List.replicate_succ, List.append_assoc]
    | succ current =>
        have hsum : current + growth = growth + current :=
          Nat.add_comm current growth
        have htarget : current + 1 + growth =
            (growth + current) + 1 := by omega
        rw [htarget]
        simp [targetRawStart, targetConsumeStart, targetScanPath,
          List.replicate_succ, hsum, List.append_assoc]
  rw [hsource]
  exact reaches_trans h₀ h₁''

def writeHeadNat : ℕ → Tape
  | 0 => ulogCore payloadHeadZero
  | 1 => ulogCore payloadHeadOne
  | _ => ulogCore payloadHeadBlank

def actionWriteStart (write : ℕ) (left path : List Tape)
    (oldHead : Tape) (suffix : List Tape) : Result :=
  match write with
  | 0 => .running .actionWrite
      ⟨left, ulogCore codeOne, path ++ oldHead :: suffix⟩
  | n + 1 => .running .actionWrite
      ⟨left, ulogCore codeZero,
        List.replicate n (ulogCore codeZero) ++
          ulogCore codeOne :: path ++ oldHead :: suffix⟩

theorem reaches_actionWriteValid (write : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Reaches (actionWriteStart write left path oldHead suffix)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne ::
            List.replicate write (ulogCore codeZero) ++ left)
          (writeHeadNat write) suffix)) := by
  interval_cases write
  · simpa [actionWriteStart, writeHeadNat] using
      (reaches_actionWriteZero oldHead hhead path hpath left suffix)
  · simpa [actionWriteStart, writeHeadNat, List.replicate_succ,
      List.append_assoc] using
      (reaches_actionWriteOne oldHead hhead path hpath left suffix)
  · simpa [actionWriteStart, writeHeadNat, List.replicate_succ,
      List.append_assoc] using
      (reaches_actionWriteBlank oldHead hhead path hpath left suffix)

def moveBits (m : OneTapeTableau.Move) : List Tape :=
  [codeTape (moveFirst m), codeTape (moveSecond m)]

def matchedMoveLeft (write target : ℕ) (m : OneTapeTableau.Move)
    (left : List Tape) : List Tape :=
  codeTape (moveSecond m) :: codeTape (moveFirst m) ::
    ulogCore codeOne :: List.replicate target (ulogCore codeZero) ++
      ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left

theorem reaches_matchedActionTargetZero
    (write current : ℕ) (hwrite : write < 3)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    ∃ z, Reaches
      (actionWriteStart write left
        (ulogCore codeOne :: moveBits m ++ movePath) oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.accepted z) := by
  let corridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  let actionLeft := ulogCore codeOne ::
    List.replicate write (ulogCore codeZero) ++ left
  have h₀ := reaches_actionWriteValid write hwrite oldHead hhead
    (ulogCore codeOne :: moveBits m ++ movePath) hwritePath left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have h₀' : Reaches
      (actionWriteStart write left
        (ulogCore codeOne :: moveBits m ++ movePath) oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart 0 current corridor actionLeft tail) := by
    simpa [targetRawStart, corridor, actionLeft, moveBits,
      beforeRightPath, List.append_assoc] using h₀
  obtain ⟨z, hz⟩ := reaches_targetRawZero_accept current corridor
    htargetPath actionLeft tail
  exact ⟨z, reaches_trans h₀' hz⟩

theorem reaches_matchedActionTargetOneZero
    (write : ℕ) (hwrite : write < 3)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Reaches
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail))
      .rejected := by
  let corridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  let actionLeft := ulogCore codeOne ::
    List.replicate write (ulogCore codeZero) ++ left
  have h₀ := reaches_actionWriteValid write hwrite oldHead hhead
    (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
    hwritePath left
    (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
      MStarConcreteAlphabet.work :: tail)
  have h₀' : Reaches
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail))
      (targetRawStart 1 0 corridor actionLeft
        (MStarConcreteAlphabet.work :: tail)) := by
    simpa [targetRawStart, corridor, actionLeft, moveBits,
      beforeRightPath, List.append_assoc] using h₀
  exact reaches_trans h₀'
    (reaches_targetRawOneZero_reject corridor htargetPath actionLeft tail)

theorem reaches_matchedActionTargetOnePositive
    (write extra : ℕ) (hwrite : write < 3)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Reaches
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      .rejected := by
  let corridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  let actionLeft := ulogCore codeOne ::
    List.replicate write (ulogCore codeZero) ++ left
  have h₀ := reaches_actionWriteValid write hwrite oldHead hhead
    (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
    hwritePath left
    (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have h₀' : Reaches
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart 1 (extra + 1) corridor actionLeft tail) := by
    simpa [targetRawStart, corridor, actionLeft, moveBits,
      beforeRightPath, List.replicate_succ,
      List.append_assoc] using h₀
  exact reaches_trans h₀'
    (reaches_targetRawOnePositive_reject extra corridor htargetPath
      actionLeft tail)

theorem reaches_matchedActionAtMostState
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Reaches
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++
          List.replicate (target + extra) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  let targetCorridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  have h₀ := reaches_actionWriteValid write hwrite oldHead hhead
    (List.replicate target (ulogCore codeZero) ++
      ulogCore codeOne :: moveBits m ++ movePath) hwritePath left
    (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have h₁ := reaches_targetAtMostState target extra targetCorridor
    (by simp [targetCorridor, moveBits]) htarget htargetPath
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail
  have h₀' : Reaches
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart target (target + extra) targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        tail) := by
    cases target <;>
      simpa [targetRawStart, targetCorridor, moveBits, beforeRightPath,
        List.replicate_succ, List.append_assoc] using h₀
  have h₂ : Reaches
      (targetRewriteFinished target extra targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        tail)
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
    let actionLeft := ulogCore codeOne ::
      List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left
    cases movePath with
    | nil =>
        have hm := reaches_actionMove m actionLeft (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail)
        simpa [targetRewriteFinished, targetCorridor, moveBits,
          matchedMoveLeft, beforeRightPath, actionLeft,
          List.append_assoc] using hm
    | cons x xs =>
        have hm := reaches_actionMove m actionLeft x
          (xs ++ writeHeadNat write :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail)
        simpa [targetRewriteFinished, targetCorridor, moveBits,
          matchedMoveLeft, beforeRightPath, actionLeft,
          List.append_assoc] using hm
  exact reaches_trans h₀' (reaches_trans h₁ h₂)

theorem reaches_matchedActionAtLeastState
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Reaches
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write (current + growth) m left)
          (writeHeadNat write)
          (runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  let target := current + growth
  let targetCorridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  have h₀ := reaches_actionWriteValid write hwrite oldHead hhead
    (List.replicate target (ulogCore codeZero) ++
      ulogCore codeOne :: moveBits m ++ movePath) hwritePath left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ tail)
  have h₁ := reaches_targetAtLeastState current growth targetCorridor
    (by simp [targetCorridor, moveBits]) htarget htargetPath
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail
  have h₀' : Reaches
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (targetRawStart target current targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        (List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    cases ht : target with
    | zero =>
        simpa [targetRawStart, target, ht, targetCorridor, moveBits,
          beforeRightPath, List.append_assoc] using h₀
    | succ target' =>
        simpa [targetRawStart, target, ht, targetCorridor, moveBits,
          beforeRightPath, List.replicate_succ, List.append_assoc] using h₀
  have h₂ : Reaches
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          (ulogCore codeOne :: List.replicate target (ulogCore codeZero) ++
            ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++
              left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left) (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    let actionLeft := ulogCore codeOne ::
      List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left
    cases movePath with
    | nil =>
        have hm := reaches_actionMove m actionLeft (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
        simpa [targetCorridor, moveBits, matchedMoveLeft,
          beforeRightPath, actionLeft, List.append_assoc] using hm
    | cons x xs =>
        have hm := reaches_actionMove m actionLeft x
          (xs ++ writeHeadNat write :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail)
        simpa [targetCorridor, moveBits, matchedMoveLeft,
          beforeRightPath, actionLeft, List.append_assoc] using hm
  have h₁' : Reaches
      (targetRawStart target current targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          (ulogCore codeOne :: List.replicate target (ulogCore codeZero) ++
            ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++
              left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa [target, List.append_assoc] using h₁
  simpa [target] using reaches_trans h₀' (reaches_trans h₁' h₂)

def MoveScanSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, choiceHead x = false ∧
    x ≠ MStarConcreteAlphabet.work

theorem reaches_moveScan (m : OneTapeTableau.Move) (path : List Tape)
    (hsafe : MoveScanSafe path) (left : List Tape)
    (head : Tape) (right : List Tape) :
    Reaches
      (.running (.moveSimHead m) (beforeRightPath path left head right))
      (.running (.moveSimHead m) (afterRightPath path left head right)) :=
  ⟨path.length, run_right_path_of (.moveSimHead m) path (by
    intro x hx l y r
    exact moveSimHead_pass m x (hsafe x hx).1 (hsafe x hx).2 l y r)
    left head right⟩

theorem reaches_moveStay (path : List Tape) (hsafe : MoveScanSafe path)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.moveSimHead .stay) (beforeRightPath path left head right))
      (.running .restoreClock ⟨path.reverse ++ left, head, right⟩) := by
  exact reaches_trans (reaches_moveScan .stay path hsafe left head right)
    (reaches_step (by
      simpa [afterRightPath] using
        (moveSimHead_stay head hhead (path.reverse ++ left) right)))

theorem reaches_moveRightInternal (path : List Tape)
    (hsafe : MoveScanSafe path) (left : List Tape)
    (head : Tape) (hhead : choiceHead head = true)
    (cell : Tape) (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (right : List Tape) :
    Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath path left head (cell :: right)))
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          headTapeOfCell cell, right⟩) := by
  have h₀ := reaches_moveScan .right path hsafe left head (cell :: right)
  have h₁ : Reaches
      (.running (.moveSimHead .right)
        (afterRightPath path left head (cell :: right)))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, cell, right⟩) := by
    apply reaches_step
    simpa [afterRightPath, List.append_assoc] using
      (moveSimHead_right head hhead (path.reverse ++ left) cell right)
  have h₂ : Reaches
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, cell, right⟩)
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          headTapeOfCell cell, right⟩) :=
    reaches_step (movePlaceRight_cell cell hcell
      (unheadTape head :: path.reverse ++ left) right)
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

theorem reaches_moveLeftInternal (pre : List Tape)
    (cell : Tape) (hsafe : MoveScanSafe (pre ++ [cell]))
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath (pre ++ [cell]) left head right))
      (.running .restoreClock
        ⟨pre.reverse ++ left, headTapeOfCell cell,
          unheadTape head :: right⟩) := by
  have h₀ := reaches_moveScan .left (pre ++ [cell]) hsafe left head right
  have h₁ : Reaches
      (.running (.moveSimHead .left)
        (afterRightPath (pre ++ [cell]) left head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre.reverse ++ left, cell, unheadTape head :: right⟩) := by
    apply reaches_step
    simpa [afterRightPath, List.reverse_append,
      List.append_assoc] using
      (moveSimHead_left head hhead (pre.reverse ++ left) cell right)
  have h₂ : Reaches
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre.reverse ++ left, cell, unheadTape head :: right⟩)
      (.running .restoreClock
        ⟨pre.reverse ++ left, headTapeOfCell cell,
          unheadTape head :: right⟩) :=
    reaches_step (movePlaceLeft_cell cell hcell
      (pre.reverse ++ left) (unheadTape head :: right))
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def ShiftRuntimeSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, x ≠ MStarConcreteAlphabet.work

def ReturnMovedSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, choiceHead x = false

def InitSeekReturnSafe (path : List Tape) : Prop :=
  ∀ x ∈ path,
    x = ulogCore stateZero ∨ x = ulogCore stateOne ∨
      x = ulogCore clockSep ∨ x = ulogCore clockZero ∨
        x = ulogCore clockOne ∨ x = payloadTape false ∨
          x = payloadTape true ∨ x = ulogCore payloadBlank

theorem seekSimHead_init_pass (x : Tape)
    (hx : x = ulogCore stateZero ∨ x = ulogCore stateOne ∨
      x = ulogCore clockSep ∨ x = ulogCore clockZero ∨
        x = ulogCore clockOne ∨ x = payloadTape false ∨
          x = payloadTape true ∨ x = ulogCore payloadBlank)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .seekSimHead ⟨y :: left, x, right⟩) =
      .running .seekSimHead ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact seekSimHead_pass_stateZero left y right
  · exact seekSimHead_pass_stateOne left y right
  · exact seekSimHead_pass_clockSep left y right
  · exact seekSimHead_pass_clockZero left y right
  · exact seekSimHead_pass_clockOne left y right
  · exact seekSimHead_pass_payload false left y right
  · exact seekSimHead_pass_payload true left y right
  · exact seekSimHead_pass_blank left y right

theorem reaches_initShiftRuntimeRight (carry : Tape) (pre : List Tape)
    (last : Tape) (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.initRight carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running .seekSimHead
        (beforeLeftPath (pre.reverse ++ [carry]) left head
          (last :: right))) := by
  induction pre generalizing carry left head with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work :=
        hsafe last (by simp)
      refine reaches_trans
        (reaches_step (initShiftRight_step carry last hlast
          (head :: left) MStarConcreteAlphabet.work right)) ?_
      apply reaches_step
      simpa [beforeLeftPath] using
        (initShiftRight_end last (head :: left) carry right)
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work :=
        hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have h₀ : Reaches
          (.running (.shiftRuntime (.initRight carry))
            (beforeRightPath ((x :: xs) ++ [last]) (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.initRight x))
            (beforeRightPath (xs ++ [last]) (carry :: head :: left)
              MStarConcreteAlphabet.work right)) := by
        apply reaches_step
        cases xs with
        | nil =>
            simpa [beforeRightPath] using
              (initShiftRight_step carry x hx (head :: left) last
                (MStarConcreteAlphabet.work :: right))
        | cons z zs =>
            simpa [beforeRightPath, List.append_assoc] using
              (initShiftRight_step carry x hx (head :: left) z
                (zs ++ last :: MStarConcreteAlphabet.work :: right))
      have h₁ := ih x hxs (head :: left) carry
      refine reaches_trans h₀ ?_
      rw [List.reverse_cons]
      rw [beforeLeftPath_append_singleton (xs.reverse ++ [x]) carry
        (by simp)]
      exact h₁

theorem reaches_seekSimHead_return (path : List Tape)
    (hsafe : InitSeekReturnSafe path) (left : List Tape)
    (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running .seekSimHead (beforeLeftPath path left head right))
      (.running .cycleStart (afterLeftPath path left head right)) := by
  have h₀ : Reaches
      (.running .seekSimHead (beforeLeftPath path left head right))
      (.running .seekSimHead (afterLeftPath path left head right)) :=
    ⟨path.length, run_left_path_of .seekSimHead path (by
      intro x hx l y r
      exact seekSimHead_init_pass x (hsafe x hx) l y r)
      left head right⟩
  exact reaches_trans h₀ (reaches_step (by
    simpa [afterLeftPath] using
      seekSimHead_existing_head head hhead left (path.reverse ++ right)))

theorem reaches_initShiftRuntimeRight_cycle (carry : Tape)
    (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : InitSeekReturnSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.initRight carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running .cycleStart
        ⟨left, head, carry :: pre ++ last :: right⟩) := by
  have h₀ := reaches_initShiftRuntimeRight carry pre last hshift
    left head right
  have h₁ := reaches_seekSimHead_return (pre.reverse ++ [carry]) hreturn
    left head hhead (last :: right)
  refine reaches_trans h₀ ?_
  simpa [afterLeftPath, List.reverse_append,
    List.append_assoc] using h₁

theorem reaches_returnMovedFromRight (path : List Tape)
    (hsafe : ReturnMovedSafe path) (left : List Tape)
    (head : Tape) (hhead : choiceHead head = true) (right : List Tape) :
    Reaches
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath path left head right))
      (.running .restoreClock (afterLeftPath path left head right)) := by
  have h₀ : Reaches
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath path left head right))
      (.running (.actionPhase .returnMovedFromRight)
        (afterLeftPath path left head right)) :=
    ⟨path.length, run_left_path_of (.actionPhase .returnMovedFromRight)
      path (by
        intro x hx l y r
        exact returnMovedFromRight_pass x (hsafe x hx) l y r)
      left head right⟩
  exact reaches_trans h₀ (reaches_step (by
    simpa [afterLeftPath] using
      (returnMovedFromRight_head head hhead left (path.reverse ++ right))))

theorem reaches_shiftRuntimeRight (carry : Tape) (pre : List Tape)
    (last : Tape) (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath (pre.reverse ++ [carry]) left head
          (last :: right))) := by
  induction pre generalizing carry left head with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work :=
        hsafe last (by simp)
      refine reaches_trans
        (reaches_step (shiftRuntimeRight_step carry last hlast
          (head :: left) MStarConcreteAlphabet.work right)) ?_
      apply reaches_step
      simpa [beforeLeftPath] using
        (shiftRuntimeRight_end last (head :: left) carry right)
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work :=
        hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have h₀ : Reaches
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath ((x :: xs) ++ [last]) (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.right x))
            (beforeRightPath (xs ++ [last]) (carry :: head :: left)
              MStarConcreteAlphabet.work right)) := by
        apply reaches_step
        cases xs with
        | nil =>
            simpa [beforeRightPath] using
              (shiftRuntimeRight_step carry x hx (head :: left) last
                (MStarConcreteAlphabet.work :: right))
        | cons z zs =>
            simpa [beforeRightPath, List.append_assoc] using
              (shiftRuntimeRight_step carry x hx (head :: left) z
                (zs ++ last :: MStarConcreteAlphabet.work :: right))
      have h₁ := ih x hxs (head :: left) carry
      refine reaches_trans h₀ ?_
      rw [List.reverse_cons]
      rw [beforeLeftPath_append_singleton (xs.reverse ++ [x]) carry (by simp)]
      exact h₁

theorem reaches_shiftRuntimeRight_restored (carry : Tape)
    (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running .restoreClock
        ⟨left, head, carry :: pre ++ last :: right⟩) := by
  have h₀ := reaches_shiftRuntimeRight carry pre last hshift left head right
  have h₁ := reaches_returnMovedFromRight (pre.reverse ++ [carry]) hreturn
    left head hhead (last :: right)
  refine reaches_trans h₀ ?_
  simpa [afterLeftPath, List.reverse_append,
    List.append_assoc] using h₁

theorem reaches_moveRightBoundary (path pre : List Tape)
    (hscan : MoveScanSafe path) (boundary last : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          ulogCore payloadHeadBlank, boundary :: pre ++ last :: right⟩) := by
  have h₀ := reaches_moveScan .right path hscan left head
    (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)
  have h₁ : Reaches
      (.running (.moveSimHead .right)
        (afterRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩) := by
    apply reaches_step
    simpa [afterRightPath, List.append_assoc] using
      (moveSimHead_right head hhead (path.reverse ++ left) boundary
        (pre ++ last :: MStarConcreteAlphabet.work :: right))
  have h₂ : Reaches
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩)
      (.running (.shiftRuntime (.right boundary))
        (beforeRightPath (pre ++ [last])
          (ulogCore payloadHeadBlank :: unheadTape head ::
            path.reverse ++ left) MStarConcreteAlphabet.work right)) := by
    apply reaches_step
    cases pre with
    | nil =>
        simpa [beforeRightPath] using
          (movePlaceRight_boundary boundary hboundary
            (unheadTape head :: path.reverse ++ left) last
            (MStarConcreteAlphabet.work :: right))
    | cons x xs =>
        simpa [beforeRightPath, List.append_assoc] using
          (movePlaceRight_boundary boundary hboundary
            (unheadTape head :: path.reverse ++ left) x
            (xs ++ last :: MStarConcreteAlphabet.work :: right))
  have h₃ := reaches_shiftRuntimeRight_restored boundary pre last hshift
    hreturn (unheadTape head :: path.reverse ++ left)
    (ulogCore payloadHeadBlank) (by native_decide) right
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

theorem reaches_returnMovedFromLeft (path : List Tape)
    (hsafe : ReturnMovedSafe path) (left : List Tape)
    (head : Tape) (hhead : choiceHead head = true) (right : List Tape) :
    Reaches
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath path left head right))
      (.running .restoreClock (afterRightPath path left head right)) := by
  have h₀ : Reaches
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath path left head right))
      (.running (.actionPhase .returnMovedFromLeft)
        (afterRightPath path left head right)) :=
    ⟨path.length, run_right_path_of (.actionPhase .returnMovedFromLeft)
      path (by
        intro x hx l y r
        exact returnMovedFromLeft_pass x (hsafe x hx) l y r)
      left head right⟩
  exact reaches_trans h₀ (reaches_step (by
    simpa [afterRightPath] using
      (returnMovedFromLeft_head head hhead (path.reverse ++ left) right)))

theorem reaches_shiftRuntimeLeft (carry : Tape) (pre : List Tape)
    (last : Tape) (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath (pre.reverse ++ [carry]) (last :: left) head
          right)) := by
  induction pre generalizing carry head right with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work :=
        hsafe last (by simp)
      refine reaches_trans
        (reaches_step (shiftRuntimeLeft_step carry last hlast
          left MStarConcreteAlphabet.work (head :: right))) ?_
      apply reaches_step
      simpa [beforeRightPath] using
        (shiftRuntimeLeft_end last left carry (head :: right))
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work :=
        hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have h₀ : Reaches
          (.running (.shiftRuntime (.left carry))
            (beforeLeftPath ((x :: xs) ++ [last]) left
              MStarConcreteAlphabet.work (head :: right)))
          (.running (.shiftRuntime (.left x))
            (beforeLeftPath (xs ++ [last]) left MStarConcreteAlphabet.work
              (carry :: head :: right))) := by
        apply reaches_step
        cases xs with
        | nil =>
            simpa [beforeLeftPath] using
              (shiftRuntimeLeft_step carry x hx
                (MStarConcreteAlphabet.work :: left) last
                (head :: right))
        | cons z zs =>
            simpa [beforeLeftPath, List.append_assoc] using
              (shiftRuntimeLeft_step carry x hx
                (zs ++ last :: MStarConcreteAlphabet.work :: left) z
                (head :: right))
      have h₁ := ih x hxs carry (head :: right)
      refine reaches_trans h₀ ?_
      rw [List.reverse_cons]
      rw [beforeRightPath_append_singleton (xs.reverse ++ [x]) carry (by simp)]
      exact h₁

theorem reaches_shiftRuntimeLeft_restored (carry : Tape)
    (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running .restoreClock
        ⟨carry :: pre ++ last :: left, head, right⟩) := by
  have h₀ := reaches_shiftRuntimeLeft carry pre last hshift left head right
  have h₁ := reaches_returnMovedFromLeft (pre.reverse ++ [carry]) hreturn
    (last :: left) head hhead right
  refine reaches_trans h₀ ?_
  simpa [afterRightPath, List.reverse_append,
    List.append_assoc] using h₁

theorem reaches_moveLeftBoundary (pre : List Tape) (last boundary : Tape)
    (hscan : MoveScanSafe ((pre ++ [last]).reverse ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath ((pre ++ [last]).reverse ++ [boundary])
          (MStarConcreteAlphabet.work :: left) head right))
      (.running .restoreClock
        ⟨boundary :: pre ++ last :: left, ulogCore payloadHeadBlank,
          unheadTape head :: right⟩) := by
  let scanPath := (pre ++ [last]).reverse ++ [boundary]
  have h₀ := reaches_moveScan .left scanPath hscan
    (MStarConcreteAlphabet.work :: left) head right
  have h₁ : Reaches
      (.running (.moveSimHead .left)
        (afterRightPath scanPath (MStarConcreteAlphabet.work :: left)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩) := by
    apply reaches_step
    simpa [scanPath, afterRightPath, List.reverse_append,
      List.append_assoc] using
      (moveSimHead_left head hhead
        (pre ++ last :: MStarConcreteAlphabet.work :: left) boundary right)
  have h₂ : Reaches
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply reaches_step
    cases pre with
    | nil =>
        simpa [beforeLeftPath] using
          (movePlaceLeft_boundary boundary hboundary
            (MStarConcreteAlphabet.work :: left) last
            (unheadTape head :: right))
    | cons x xs =>
        simpa [beforeLeftPath, List.append_assoc] using
          (movePlaceLeft_boundary boundary hboundary
            (xs ++ last :: MStarConcreteAlphabet.work :: left) x
            (unheadTape head :: right))
  have h₃ := reaches_shiftRuntimeLeft_restored boundary pre last hshift
    hreturn left (ulogCore payloadHeadBlank) (by native_decide)
    (unheadTape head :: right)
  have h₀' : Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath ((pre ++ [last]).reverse ++ [boundary])
          (MStarConcreteAlphabet.work :: left) head right))
      (.running (.moveSimHead .left)
        (afterRightPath scanPath (MStarConcreteAlphabet.work :: left)
          head right)) := by
    simpa [scanPath] using h₀
  exact reaches_trans h₀' (reaches_trans h₁ (reaches_trans h₂ h₃))

def RestoreClockSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, x ≠ ulogCore pcMark ∧
    x ≠ MStarConcreteAlphabet.work

def RestorePcSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, x = ulogCore pcDone ∨ x = ulogCore codeZero

def restorePcCell (x : Tape) : Tape :=
  if x = ulogCore codeZero then ulogCore pcDone else x

def RestoreHeadSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, choiceHead x = false ∧
    x ≠ MStarConcreteAlphabet.work

theorem restorePc_path_step (x : Tape)
    (hx : x = ulogCore pcDone ∨ x = ulogCore codeZero)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .restorePc ⟨left, x, y :: right⟩) =
      .running .restorePc ⟨restorePcCell x :: left, y, right⟩ := by
  rcases hx with rfl | rfl
  · have hne : ulogCore pcDone ≠ ulogCore codeZero :=
      ULogTapeDecoding.ulog_symbol_ne (by decide)
    simpa [restorePcCell, hne] using restorePc_done left y right
  · simpa [restorePcCell] using restorePc_zero left y right

theorem reaches_restoreCycle (pcPath : List Tape) (terminal : Tape)
    (programPath : List Tape) (outer : List Tape) (head : Tape)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: programPath).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe programPath)
    (hhead : choiceHead head = true)
    (right : List Tape) :
    Reaches
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩)
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer,
          head, right⟩) := by
  let clockPath := head :: (pcPath ++ terminal :: programPath).reverse
  have h₀ : Reaches
      (.running .restoreClock
        (beforeLeftPath clockPath outer (ulogCore pcMark) right))
      (.running .restoreClock
        (afterLeftPath clockPath outer (ulogCore pcMark) right)) :=
    ⟨clockPath.length, run_left_path_of .restoreClock clockPath (by
      intro x hx l y r
      exact restoreClock_pass x (hclock x hx).1 (hclock x hx).2 l y r)
      outer (ulogCore pcMark) right⟩
  have h₁ : Reaches
      (.running .restoreClock
        (afterLeftPath clockPath outer (ulogCore pcMark) right))
      (.running .restorePc
        (beforeRightPath pcPath (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right))) := by
    apply reaches_step
    cases pcPath with
    | nil =>
        simpa [clockPath, afterLeftPath, beforeRightPath,
          List.reverse_append, List.append_assoc] using
          (restoreClock_pc outer terminal (programPath ++ head :: right))
    | cons x xs =>
        simpa [clockPath, afterLeftPath, beforeRightPath,
          List.reverse_append, List.append_assoc] using
          (restoreClock_pc outer x
            (xs ++ terminal :: programPath ++ head :: right))
  have h₂ : Reaches
      (.running .restorePc
        (beforeRightPath pcPath (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right)))
      (.running .restorePc
        (afterRightPathMap pcPath restorePcCell
          (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right))) :=
    ⟨pcPath.length, run_right_path_map_of .restorePc pcPath restorePcCell
      (by
        intro x hx l y r
        exact restorePc_path_step x (hpc x hx) l y r)
      (ulogCore pcMark :: outer) terminal
      (programPath ++ head :: right)⟩
  have h₃ : Reaches
      (.running .restorePc
        (afterRightPathMap pcPath restorePcCell
          (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right)))
      (.running .restoreHead
        (beforeRightPath programPath
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right)) := by
    apply reaches_step
    rcases hterminal with rfl | rfl
    · cases programPath with
      | nil =>
          simpa [afterRightPathMap, beforeRightPath] using
            (restorePc_end
              (pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer) head right)
      | cons x xs =>
          simpa [afterRightPathMap, beforeRightPath,
            List.append_assoc] using
            (restorePc_end
              (pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer) x (xs ++ head :: right))
    · cases programPath with
      | nil =>
          simpa [afterRightPathMap, beforeRightPath] using
            (restorePc_boundary
              (pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer) head right)
      | cons x xs =>
          simpa [afterRightPathMap, beforeRightPath,
            List.append_assoc] using
            (restorePc_boundary
              (pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer) x (xs ++ head :: right))
  have h₄ : Reaches
      (.running .restoreHead
        (beforeRightPath programPath
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right))
      (.running .restoreHead
        (afterRightPathMap programPath restoreProgramCell
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right)) :=
    ⟨programPath.length,
      run_right_path_map_of .restoreHead programPath restoreProgramCell (by
        intro x hx l y r
        exact restoreHead_pass x (hprogram x hx).1 (hprogram x hx).2 l y r)
      (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
        ulogCore pcMark :: outer) head right⟩
  have h₅ : Reaches
      (.running .restoreHead
        (afterRightPathMap programPath restoreProgramCell
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right))
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer,
          head, right⟩) := by
    apply reaches_step
    simpa [afterRightPathMap, List.append_assoc] using
      (restoreHead_head head hhead
        (programPath.reverse.map restoreProgramCell ++
          ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) right)
  have h₀' : Reaches
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩)
      (.running .restoreClock
        (afterLeftPath clockPath outer (ulogCore pcMark) right)) := by
    simpa [clockPath, beforeLeftPath, List.append_assoc] using h₀
  exact reaches_trans h₀' (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

def restorePcPath (done remaining : ℕ) : List Tape :=
  List.replicate done (ulogCore codeZero) ++
    List.replicate remaining (ulogCore pcDone)

theorem restorePcPath_safe (done remaining : ℕ) :
    RestorePcSafe (restorePcPath done remaining) := by
  intro x hx
  simp only [restorePcPath, List.mem_append, List.mem_replicate] at hx
  rcases hx with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

theorem restorePcPath_map (done remaining : ℕ) :
    (restorePcPath done remaining).reverse.map restorePcCell =
      List.replicate (done + remaining) (ulogCore pcDone) := by
  have hne : ulogCore pcDone ≠ ulogCore codeZero :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hz : restorePcCell (ulogCore codeZero) = ulogCore pcDone := by
    rfl
  have hd : restorePcCell (ulogCore pcDone) = ulogCore pcDone := by
    simp [restorePcCell, hne]
  simp only [restorePcPath, List.reverse_append, List.reverse_replicate,
    List.map_append, List.map_replicate, hz, hd]
  rw [← List.replicate_add, Nat.add_comm]

theorem reaches_restoreCycle_counts (done remaining : ℕ)
    (terminal : Tape) (programPath : List Tape)
    (outer : List Tape) (head : Tape)
    (hclock : RestoreClockSafe
      (head :: (restorePcPath done remaining ++
        terminal :: programPath).reverse))
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe programPath)
    (hhead : choiceHead head = true) (right : List Tape) :
    Reaches
      (.running .restoreClock
        ⟨(restorePcPath done remaining ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩)
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne ::
              List.replicate (done + remaining) (ulogCore pcDone) ++
                ulogCore pcMark :: outer,
          head, right⟩) := by
  have h := reaches_restoreCycle (restorePcPath done remaining) terminal
    programPath outer head hclock (restorePcPath_safe done remaining)
    hterminal hprogram hhead right
  simpa only [restorePcPath_map, List.append_assoc] using h

theorem reaches_mismatchCount_fresh (slot : Bool) (done : ℕ)
    (left : List Tape) (y : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchCount slot)
        (beforeRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right)))
      (.running (.mismatchSeekBoundary slot)
        ⟨ulogCore codeZero ::
            (List.replicate done (ulogCore codeZero) ++ left),
          y, right⟩) := by
  have h₀ : Reaches
      (.running (.mismatchCount slot)
        (beforeRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right)))
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right))) :=
    ⟨done, by
      simpa using
        (run_right_path_of (.mismatchCount slot)
          (List.replicate done (ulogCore codeZero)) (by
            intro x hx l z r
            have hm : done ≠ 0 ∧ x = ulogCore codeZero := by
              simpa only [List.mem_replicate] using hx
            rw [hm.2]
            exact mismatchCount_consumed slot l z r)
          left (ulogCore pcDone) (y :: right))⟩
  have h₁ : Reaches
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right)))
      (.running (.mismatchSeekBoundary slot)
        ⟨ulogCore codeZero ::
            (List.replicate done (ulogCore codeZero) ++ left),
          y, right⟩) := by
    apply reaches_step
    simpa [afterRightPath] using
      (mismatchCount_fresh slot
        (List.replicate done (ulogCore codeZero) ++ left) y right)
  exact reaches_trans h₀ h₁

theorem reaches_mismatchCount_exhausted (slot : Bool) (done : ℕ)
    (left right : List Tape) :
    Reaches
      (.running (.mismatchCount slot)
        (beforeRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore codeOne) right))
      .rejected := by
  have h₀ : Reaches
      (.running (.mismatchCount slot)
        (beforeRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore codeOne) right))
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore codeOne) right)) :=
    ⟨done, by
      simpa using
        (run_right_path_of (.mismatchCount slot)
          (List.replicate done (ulogCore codeZero)) (by
            intro x hx l z r
            have hm : done ≠ 0 ∧ x = ulogCore codeZero := by
              simpa only [List.mem_replicate] using hx
            rw [hm.2]
            exact mismatchCount_consumed slot l z r)
          left (ulogCore codeOne) right)⟩
  have h₁ : Reaches
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore codeOne) right))
      .rejected := by
    apply reaches_step
    simpa [afterRightPath] using
      (mismatchCount_exhausted slot
        (List.replicate done (ulogCore codeZero) ++ left) right)
  exact reaches_trans h₀ h₁

theorem reaches_mismatchCount_prefix_fresh (slot : Bool) (done : ℕ)
    (path left : List Tape) (boundary : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchCount slot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          left boundary right))
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path
          (ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++ left)
          boundary right)) := by
  cases path with
  | nil =>
      cases done with
      | zero =>
          simpa [beforeRightPath] using
            (reaches_mismatchCount_fresh slot 0 left boundary right)
      | succ n =>
          simpa [beforeRightPath, List.replicate_succ,
            List.append_assoc] using
            (reaches_mismatchCount_fresh slot (n + 1) left boundary right)
  | cons x xs =>
      cases done with
      | zero =>
          simpa [beforeRightPath, List.append_assoc] using
            (reaches_mismatchCount_fresh slot 0 left x
              (xs ++ boundary :: right))
      | succ n =>
          simpa [beforeRightPath, List.replicate_succ,
            List.append_assoc] using
            (reaches_mismatchCount_fresh slot (n + 1) left x
              (xs ++ boundary :: right))

def MismatchBoundaryFree (path : List Tape) : Prop :=
  ∀ x ∈ path, x ≠ ulogCore sourceBoundary ∧
    x ≠ ulogCore sourceBoundaryZero ∧
      x ≠ ulogCore sourceBoundaryOne

theorem reaches_mismatchSeekBoundary (slot : Bool) (path : List Tape)
    (hpath : MismatchBoundaryFree path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary) (y :: right)))
      (.running (.mismatchSkipSource slot)
        ⟨(if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ left,
          y, right⟩) := by
  have h₀ : Reaches
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary) (y :: right)))
      (.running (.mismatchSeekBoundary slot)
        (afterRightPath path left (ulogCore boundary) (y :: right))) :=
    ⟨path.length, run_right_path_of (.mismatchSeekBoundary slot) path
      (by
        intro x hx l z r
        have h := hpath x hx
        exact mismatchSeekBoundary_pass slot x h.1 h.2.1 h.2.2 l z r)
      left (ulogCore boundary) (y :: right)⟩
  have h₁ : Reaches
      (.running (.mismatchSeekBoundary slot)
        (afterRightPath path left (ulogCore boundary) (y :: right)))
      (.running (.mismatchSkipSource slot)
        ⟨(if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ left,
          y, right⟩) := by
    apply reaches_step
    simpa [afterRightPath, List.append_assoc] using
      (mismatchSeekBoundary_boundary slot boundary hboundary
        (path.reverse ++ left) y right)
  exact reaches_trans h₀ h₁

def returnPath (skipped : List Bool) (remaining done : ℕ) : List Tape :=
  skipped.reverse.map codeTape ++ [codeTape true] ++
    List.replicate remaining (codeTape false) ++
      List.replicate done (ulogCore pcDone)

def seekPath (skipped : List Bool) (remaining : ℕ) : List Tape :=
  List.replicate remaining (codeTape false) ++
    codeTape true :: skipped.map codeTape

theorem returnPath_pass (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (x : Tape) (hx : x ∈ returnPath skipped remaining done)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry) ⟨y :: left, x, right⟩) =
      .running (.returnToPc carry) ⟨left, y, x :: right⟩ := by
  simp [returnPath] at hx
  rcases hx with hx | rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact returnToPc_pass_code carry _ left y right
  · exact returnToPc_pass_code carry true left y right
  · exact returnToPc_pass_code carry false left y right
  · exact returnToPc_pass_done carry left y right

theorem seekPath_pass (carry done : Bool) (skipped : List Bool)
    (remaining : ℕ) (x : Tape) (hx : x ∈ seekPath skipped remaining)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.seekReturn carry done) ⟨left, x, y :: right⟩) =
      .running (.seekReturn carry done) ⟨x :: left, y, right⟩ := by
  simp [seekPath] at hx
  rcases hx with ⟨-, rfl⟩ | rfl | hx
  · exact seekReturn_pass_code carry done false left y right
  · exact seekReturn_pass_code carry done true left y right
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact seekReturn_pass_code carry done _ left y right

theorem returnPath_reverse (skipped : List Bool) (remaining done : ℕ) :
    (returnPath skipped remaining done).reverse =
      List.replicate done (ulogCore pcDone) ++ seekPath skipped remaining := by
  simp [returnPath, seekPath, List.reverse_append, List.map_reverse,
    List.append_assoc]

def countCheckStart (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.fieldReturn .programCount)
    ⟨returnPath skipped remaining done ++ ulogCore pcMark :: left,
      codeTape carry, right⟩

def countReturnStarted (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.returnToPc carry)
    (beforeLeftPath (returnPath skipped remaining done) left
      (ulogCore pcMark) (branchTape carry :: right))

def countAtMark (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.returnToPc carry)
    (afterLeftPath (returnPath skipped remaining done) left
      (ulogCore pcMark) (branchTape carry :: right))

theorem reaches_countAtMark (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) :
    Reaches (countCheckStart carry skipped remaining done left right)
      (countAtMark carry skipped remaining done left right) := by
  have hne : returnPath skipped remaining done ≠ [] := by
    simp [returnPath]
  have h₀ : Reaches (countCheckStart carry skipped remaining done left right)
      (countReturnStarted carry skipped remaining done left right) := by
    cases hp : returnPath skipped remaining done with
    | nil => exact (hne hp).elim
    | cons x xs =>
        apply reaches_step
        simp [countCheckStart, countReturnStarted, beforeLeftPath, hp,
          fieldReturn_count_step]
  have h₁ : Reaches (countReturnStarted carry skipped remaining done left right)
      (countAtMark carry skipped remaining done left right) := by
    refine ⟨(returnPath skipped remaining done).length, ?_⟩
    apply run_left_path_of (.returnToPc carry)
      (returnPath skipped remaining done)
    intro x hx l y r
    exact returnPath_pass carry skipped remaining done x hx l y r
  exact reaches_trans h₀ h₁

def countScanStarted (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.countScan carry)
    (beforeRightPath (List.replicate done (ulogCore pcDone))
      (ulogCore pcMark :: left)
      (match seekPath skipped remaining with
        | [] => branchTape carry
        | x :: _ => x)
      ((seekPath skipped remaining).drop 1 ++ branchTape carry :: right))

def countAfterDone (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.countScan carry)
    (afterRightPath (List.replicate done (ulogCore pcDone))
      (ulogCore pcMark :: left)
      (match seekPath skipped remaining with
        | [] => branchTape carry
        | x :: _ => x)
      ((seekPath skipped remaining).drop 1 ++ branchTape carry :: right))

theorem reaches_countAfterDone (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) :
    Reaches (countAtMark carry skipped remaining done left right)
      (countAfterDone carry skipped remaining done left right) := by
  have hseek : seekPath skipped remaining ≠ [] := by simp [seekPath]
  have h₀ : Reaches (countAtMark carry skipped remaining done left right)
      (countScanStarted carry skipped remaining done left right) := by
    apply reaches_step
    cases hs : seekPath skipped remaining with
    | nil => exact (hseek hs).elim
    | cons x xs =>
        cases done <;>
          simp [countAtMark, countScanStarted, afterLeftPath,
            beforeRightPath, returnPath_reverse, hs, returnToPc_mark,
            List.replicate_succ, List.append_assoc]
  have h₁ : Reaches (countScanStarted carry skipped remaining done left right)
      (countAfterDone carry skipped remaining done left right) := by
    have hseek : seekPath skipped remaining ≠ [] := by simp [seekPath]
    cases hs : seekPath skipped remaining with
    | nil => exact (hseek hs).elim
    | cons x xs =>
        have hrun := run_right_path_of (.countScan carry)
          (List.replicate done (ulogCore pcDone)) (by
            intro z hz l y r
            have hzmem : done ≠ 0 ∧ z = ulogCore pcDone := by
              simpa only [List.mem_replicate] using hz
            have hz' : z = ulogCore pcDone := hzmem.2
            subst z
            exact countScan_done carry l y r)
          (ulogCore pcMark :: left) x (xs ++ branchTape carry :: right)
        exact ⟨done, by
          simpa [countScanStarted, countAfterDone, hs] using hrun⟩
  exact reaches_trans h₀ h₁

def countFreshStarted (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry false)
    (beforeRightPath (seekPath skipped remaining)
      (ulogCore pcDone :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def countFreshReturned (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry false)
    (afterRightPath (seekPath skipped remaining)
      (ulogCore pcDone :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def countFreshDone (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) : Result :=
  .running (.fieldSeek .source)
    ⟨(seekPath skipped remaining).reverse ++
        ulogCore pcDone :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left,
      codeTape carry, right⟩

theorem reaches_countFresh (carry : Bool) (skipped : List Bool)
    (remaining done : ℕ) (left right : List Tape) :
    Reaches (countCheckStart carry skipped (remaining + 1) done left right)
      (countFreshDone carry skipped remaining done left right) := by
  have h₀ := reaches_countAtMark carry skipped (remaining + 1) done left right
  have h₁ := reaches_countAfterDone carry skipped (remaining + 1) done left right
  have h₂ : Reaches
      (countAfterDone carry skipped (remaining + 1) done left right)
      (countFreshStarted carry skipped remaining done left right) := by
    apply reaches_step
    cases remaining <;>
      simp [countAfterDone, countFreshStarted, seekPath, beforeRightPath,
        afterRightPath, countScan_fresh, List.replicate_succ,
        List.append_assoc]
  have h₃ : Reaches
      (countFreshStarted carry skipped remaining done left right)
      (countFreshReturned carry skipped remaining done left right) := by
    exact ⟨(seekPath skipped remaining).length,
      run_right_path_of (.seekReturn carry false)
        (seekPath skipped remaining)
        (seekPath_pass carry false skipped remaining)
        (ulogCore pcDone :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        (branchTape carry) right⟩
  have h₄ : Reaches
      (countFreshReturned carry skipped remaining done left right)
      (countFreshDone carry skipped remaining done left right) := by
    apply reaches_step
    simp [countFreshReturned, countFreshDone, afterRightPath,
      seekReturn_marker]
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ h₄)))

def countExhaustedStarted (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry true)
    (beforeRightPath (skipped.map codeTape)
      (codeTape true :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def countExhaustedReturned (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry true)
    (afterRightPath (skipped.map codeTape)
      (codeTape true :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def countExhaustedDone (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running .payloadLengthStart
    ⟨(skipped.map codeTape).reverse ++
        codeTape true :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left,
      codeTape carry, right⟩

theorem reaches_countExhausted (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) :
    Reaches (countCheckStart carry skipped 0 done left right)
      (countExhaustedDone carry skipped done left right) := by
  have h₀ := reaches_countAtMark carry skipped 0 done left right
  have h₁ := reaches_countAfterDone carry skipped 0 done left right
  have h₂ : Reaches (countAfterDone carry skipped 0 done left right)
      (countExhaustedStarted carry skipped done left right) := by
    apply reaches_step
    cases skipped <;>
      simp [countAfterDone, countExhaustedStarted, seekPath,
        beforeRightPath, afterRightPath, countScan_exhausted,
        List.append_assoc]
  have h₃ : Reaches (countExhaustedStarted carry skipped done left right)
      (countExhaustedReturned carry skipped done left right) := by
    exact ⟨(skipped.map codeTape).length,
      run_right_path_of (.seekReturn carry true) (skipped.map codeTape)
        (by
          intro x hx l y r
          rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
          exact seekReturn_pass_code carry true b l y r)
        (codeTape true :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        (branchTape carry) right⟩
  have h₄ : Reaches (countExhaustedReturned carry skipped done left right)
      (countExhaustedDone carry skipped done left right) := by
    apply reaches_step
    simp [countExhaustedReturned, countExhaustedDone, afterRightPath,
      seekReturn_marker]
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ h₄)))

def finalReturnPath (skipped : List Bool) (done : ℕ) : List Tape :=
  ulogCore codeEnd :: skipped.reverse.map codeTape ++
    codeTape true :: List.replicate done (ulogCore pcDone)

def finalSeekPath (skipped : List Bool) : List Tape :=
  skipped.map codeTape ++ [ulogCore codeEnd]

@[simp] theorem finalReturnPath_reverse (skipped : List Bool) (done : ℕ) :
    (finalReturnPath skipped done).reverse =
      List.replicate done (ulogCore pcDone) ++
        codeTape true :: finalSeekPath skipped := by
  simp [finalReturnPath, finalSeekPath, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem finalReturnPath_pass (carry : Bool) (skipped : List Bool)
    (done : ℕ) (x : Tape) (hx : x ∈ finalReturnPath skipped done)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.returnToPc carry) ⟨y :: left, x, right⟩) =
      .running (.returnToPc carry) ⟨left, y, x :: right⟩ := by
  simp [finalReturnPath] at hx
  rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
  · exact returnToPc_pass_end carry left y right
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact returnToPc_pass_code carry _ left y right
  · exact returnToPc_pass_code carry true left y right
  · exact returnToPc_pass_done carry left y right

theorem finalSeekPath_pass (carry : Bool) (skipped : List Bool)
    (x : Tape) (hx : x ∈ finalSeekPath skipped) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.seekReturn carry true) ⟨left, x, y :: right⟩) =
      .running (.seekReturn carry true) ⟨x :: left, y, right⟩ := by
  simp [finalSeekPath] at hx
  rcases hx with hx | rfl
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact seekReturn_pass_code carry true _ left y right
  · exact seekReturn_pass_end carry true left y right

def finalCountCheckStart (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.fieldReturn .programCount)
    ⟨finalReturnPath skipped done ++ ulogCore pcMark :: left,
      codeTape carry, right⟩

def finalCountAtMark (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.returnToPc carry)
    (afterLeftPath (finalReturnPath skipped done) left
      (ulogCore pcMark) (branchTape carry :: right))

def finalCountAfterDone (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.countScan carry)
    (afterRightPath (List.replicate done (ulogCore pcDone))
      (ulogCore pcMark :: left) (codeTape true)
      (finalSeekPath skipped ++ branchTape carry :: right))

def finalSeekStarted (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry true)
    (beforeRightPath (finalSeekPath skipped)
      (codeTape true :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def finalSeekReturned (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running (.seekReturn carry true)
    (afterRightPath (finalSeekPath skipped)
      (codeTape true :: List.replicate done (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      (branchTape carry) right)

def finalCountDone (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) : Result :=
  .running .payloadLengthStart
    ⟨(finalSeekPath skipped).reverse ++
        codeTape true :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left,
      codeTape carry, right⟩

theorem reaches_finalCountExhausted (carry : Bool) (skipped : List Bool)
    (done : ℕ) (left right : List Tape) :
    Reaches (finalCountCheckStart carry skipped done left right)
      (finalCountDone carry skipped done left right) := by
  have hpath : finalReturnPath skipped done ≠ [] := by
    simp [finalReturnPath]
  have h₀ : Reaches (finalCountCheckStart carry skipped done left right)
      (.running (.returnToPc carry)
        (beforeLeftPath (finalReturnPath skipped done) left
          (ulogCore pcMark) (branchTape carry :: right))) := by
    apply reaches_step
    cases hp : finalReturnPath skipped done with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simp [finalCountCheckStart, beforeLeftPath, hp,
          fieldReturn_count_step]
  have h₁ : Reaches
      (.running (.returnToPc carry)
        (beforeLeftPath (finalReturnPath skipped done) left
          (ulogCore pcMark) (branchTape carry :: right)))
      (finalCountAtMark carry skipped done left right) :=
    ⟨(finalReturnPath skipped done).length,
      run_left_path_of (.returnToPc carry) (finalReturnPath skipped done)
        (finalReturnPath_pass carry skipped done) left (ulogCore pcMark)
        (branchTape carry :: right)⟩
  have h₂ : Reaches (finalCountAtMark carry skipped done left right)
      (.running (.countScan carry)
        (beforeRightPath (List.replicate done (ulogCore pcDone))
          (ulogCore pcMark :: left) (codeTape true)
          (finalSeekPath skipped ++ branchTape carry :: right))) := by
    apply reaches_step
    cases done <;>
      simp [finalCountAtMark, afterLeftPath, beforeRightPath,
        finalReturnPath_reverse, returnToPc_mark, List.replicate_succ,
        List.append_assoc]
  have h₃ : Reaches
      (.running (.countScan carry)
        (beforeRightPath (List.replicate done (ulogCore pcDone))
          (ulogCore pcMark :: left) (codeTape true)
          (finalSeekPath skipped ++ branchTape carry :: right)))
      (finalCountAfterDone carry skipped done left right) := by
    refine ⟨(List.replicate done (ulogCore pcDone)).length, ?_⟩
    simpa [finalCountAfterDone] using
      (run_right_path_of (.countScan carry)
        (List.replicate done (ulogCore pcDone)) (by
          intro x hx l y r
          have hm : done ≠ 0 ∧ x = ulogCore pcDone := by
            simpa only [List.mem_replicate] using hx
          rw [hm.2]
          exact countScan_done carry l y r)
        (ulogCore pcMark :: left) (codeTape true)
        (finalSeekPath skipped ++ branchTape carry :: right))
  have h₄ : Reaches (finalCountAfterDone carry skipped done left right)
      (finalSeekStarted carry skipped done left right) := by
    apply reaches_step
    cases skipped <;>
      simp [finalCountAfterDone, finalSeekStarted, finalSeekPath,
        afterRightPath, beforeRightPath, countScan_exhausted,
        List.append_assoc]
  have h₅ : Reaches (finalSeekStarted carry skipped done left right)
      (finalSeekReturned carry skipped done left right) :=
    ⟨(finalSeekPath skipped).length,
      run_right_path_of (.seekReturn carry true) (finalSeekPath skipped)
        (finalSeekPath_pass carry skipped)
        (codeTape true :: List.replicate done (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        (branchTape carry) right⟩
  have h₆ : Reaches (finalSeekReturned carry skipped done left right)
      (finalCountDone carry skipped done left right) := by
    apply reaches_step
    simp [finalSeekReturned, finalCountDone, afterRightPath,
      seekReturn_marker]
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ (reaches_trans h₄ (reaches_trans h₅ h₆)))))

def beforeFieldZeros (field : BytecodeField) (n : ℕ)
    (left : List Tape) (y : Tape) (right : List Tape) : Result :=
  match n with
  | 0 => .running (.fieldSeek field) ⟨left, ulogCore codeOne, y :: right⟩
  | k + 1 => .running (.fieldSeek field)
      ⟨left, ulogCore codeZero,
        List.replicate k (ulogCore codeZero) ++ ulogCore codeOne :: y :: right⟩

def afterFieldZeros (field : BytecodeField) (n : ℕ)
    (left : List Tape) (y : Tape) (right : List Tape) : Result :=
  .running (.fieldSeek field)
    ⟨List.replicate n (ulogCore codeZero) ++ left,
      ulogCore codeOne, y :: right⟩

theorem run_fieldSeek_zeros (field : BytecodeField) (n : ℕ)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run n (beforeFieldZeros field n left y right) =
      afterFieldZeros field n left y right := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run]
      rw [show oneStep (beforeFieldZeros field (n + 1) left y right) =
          beforeFieldZeros field n (ulogCore codeZero :: left) y right by
        cases n <;> simp [beforeFieldZeros, fieldSeek_zero_step,
          List.replicate_succ, List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running (.fieldSeek field))
      apply Zipper.ext <;>
        simp [afterFieldZeros, List.replicate_succ', List.append_assoc]

theorem reaches_field (field : BytecodeField) (n : ℕ)
    (left : List Tape) (y : Tape) (right : List Tape) :
    Reaches (beforeFieldZeros field n left y right)
      (.running (.fieldReturn field)
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
  have h₀ : Reaches (beforeFieldZeros field n left y right)
      (afterFieldZeros field n left y right) :=
    ⟨n, run_fieldSeek_zeros field n left y right⟩
  have h₁ : Reaches (afterFieldZeros field n left y right)
      (.running (.fieldReturn field)
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
    apply reaches_step
    exact fieldSeek_one_step field _ _ _
  exact reaches_trans h₀ h₁

def beforeUnaryState (q : State) (n : ℕ) (left : List Tape)
    (y : Tape) (right : List Tape) : Result :=
  match n with
  | 0 => .running q ⟨left, ulogCore codeOne, y :: right⟩
  | k + 1 => .running q
      ⟨left, ulogCore codeZero,
        List.replicate k (ulogCore codeZero) ++ ulogCore codeOne :: y :: right⟩

def afterUnaryState (q : State) (n : ℕ) (left : List Tape)
    (y : Tape) (right : List Tape) : Result :=
  .running q
    ⟨List.replicate n (ulogCore codeZero) ++ left,
      ulogCore codeOne, y :: right⟩

theorem run_unaryState_zeros_of (q : State) (n : ℕ)
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    run n (beforeUnaryState q n left y right) =
      afterUnaryState q n left y right := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run]
      rw [show oneStep (beforeUnaryState q (n + 1) left y right) =
          beforeUnaryState q n (ulogCore codeZero :: left) y right by
        cases n <;> simp [beforeUnaryState, hzero,
          List.replicate_succ, List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running q)
      apply Zipper.ext <;>
        simp [afterUnaryState, List.replicate_succ', List.append_assoc]

theorem reaches_unaryState_of (q qnext : State) (n : ℕ)
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (hone : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeOne, y :: right⟩) =
        .running qnext ⟨ulogCore codeOne :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    Reaches (beforeUnaryState q n left y right)
      (.running qnext
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
  have h₀ : Reaches (beforeUnaryState q n left y right)
      (afterUnaryState q n left y right) :=
    ⟨n, run_unaryState_zeros_of q n hzero left y right⟩
  have h₁ : Reaches (afterUnaryState q n left y right)
      (.running qnext
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
    apply reaches_step
    exact hone _ _ _
  exact reaches_trans h₀ h₁

def atBits (q : State) (bits : List Bool) (left : List Tape)
    (after : Tape) (right : List Tape) : Result :=
  match bits with
  | [] => .running q ⟨left, after, right⟩
  | b :: bs => .running q
      ⟨left, codeTape b, bs.map codeTape ++ after :: right⟩

theorem reaches_mismatchSeekBoundary_rule (slot : Bool)
    (path : List Tape) (hpath : MismatchBoundaryFree path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.mismatchSkipSource slot)
        (ULogBytecode.encodeRule r ++ next)
        ((if boundary = sourceBoundaryZero then ulogCore codeZero
          else ulogCore codeOne) :: path.reverse ++ left)
        after right) := by
  have henc : ULogBytecode.encodeRule r ≠ [] := by
    rcases r with ⟨source, read, ruleSlot, action⟩
    cases source <;>
      simp [ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
        List.replicate_succ]
  cases he : ULogBytecode.encodeRule r ++ next with
  | nil =>
      have hfalse : False := by simpa [henc] using he
      exact hfalse.elim
  | cons b bs =>
      have h := reaches_mismatchSeekBoundary slot path hpath boundary
        hboundary left (codeTape b) (bs.map codeTape ++ after :: right)
      simpa [atBits, he, List.map_append, List.append_assoc] using h

theorem reaches_unaryState_prefix_of (q qnext : State) (n : ℕ)
    (tail : List Bool) (htail : tail ≠ [])
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (hone : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeOne, y :: right⟩) =
        .running qnext ⟨ulogCore codeOne :: left, y, right⟩)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits q (ULogBytecode.encodeNatField n ++ tail) left after right)
      (atBits qnext tail
        ((ULogBytecode.encodeNatField n).reverse.map codeTape ++ left)
        after right) := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons b bs =>
      cases n with
      | zero =>
          simpa [atBits, beforeUnaryState, codeTape,
            ULogBytecode.encodeNatField, List.map_append,
            List.reverse_append, List.append_assoc] using
            (reaches_unaryState_of q qnext 0 hzero hone left
              (codeTape b) (bs.map codeTape ++ after :: right))
      | succ n =>
          simpa [atBits, beforeUnaryState, codeTape,
            ULogBytecode.encodeNatField, List.map_append,
            List.reverse_append, List.replicate_succ,
            List.append_assoc] using
            (reaches_unaryState_of q qnext (n + 1) hzero hone left
              (codeTape b) (bs.map codeTape ++ after :: right))

theorem reaches_field_prefix (field : BytecodeField) (n : ℕ)
    (tail : List Bool) (htail : tail ≠ []) (left : List Tape)
    (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.fieldSeek field)
        (ULogBytecode.encodeNatField n ++ tail) left after right)
      (atBits (.fieldReturn field) tail
        ((ULogBytecode.encodeNatField n).reverse.map codeTape ++ left)
        after right) := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons b bs =>
      cases n with
      | zero =>
          simpa [atBits, beforeFieldZeros, codeTape,
            ULogBytecode.encodeNatField, List.map_append,
            List.reverse_append, List.append_assoc] using
            (reaches_field field 0 left (codeTape b)
              (bs.map codeTape ++ after :: right))
      | succ n =>
          simpa [atBits, beforeFieldZeros, codeTape,
            ULogBytecode.encodeNatField, List.map_append,
            List.reverse_append, List.replicate_succ, List.append_assoc] using
            (reaches_field field (n + 1) left (codeTape b)
              (bs.map codeTape ++ after :: right))

theorem reaches_field_prefix_any (field : BytecodeField) (n : ℕ)
    (tail : List Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    Reaches
      (atBits (.fieldSeek field)
        (ULogBytecode.encodeNatField n ++ tail) left after right)
      (atBits (.fieldReturn field) tail
        ((ULogBytecode.encodeNatField n).reverse.map codeTape ++ left)
        after right) := by
  cases tail with
  | nil =>
      cases n with
      | zero =>
          simpa [atBits, beforeFieldZeros, codeTape,
            ULogBytecode.encodeNatField] using
            (reaches_field field 0 left after right)
      | succ n =>
          simpa [atBits, beforeFieldZeros, codeTape,
            ULogBytecode.encodeNatField, List.map_append,
            List.reverse_append, List.replicate_succ,
            List.append_assoc] using
            (reaches_field field (n + 1) left after right)
  | cons b bs =>
      exact reaches_field_prefix field n (b :: bs) (by simp)
        left after right

theorem atBits_source_handoff (b : Bool) (bits : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    oneStep (atBits (.fieldReturn .source) (b :: bits) left after right) =
      atBits (.fieldSeek .read) (b :: bits) left after right := by
  cases b <;> rfl

theorem atBits_source_handoff_nonempty (bits : List Bool)
    (hbits : bits ≠ []) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits (.fieldReturn .source) bits left after right) =
      atBits (.fieldSeek .read) bits left after right := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons b bs => exact atBits_source_handoff b bs left after right

theorem atBits_read_slot (b : Bool) (bits : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    oneStep (atBits (.fieldReturn .read) (b :: bits) left after right) =
      atBits (.fieldSeek .write) bits (codeTape b :: left) after right := by
  cases b <;> cases bits <;> rfl

theorem atBits_write_handoff (b : Bool) (bits : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    oneStep (atBits (.fieldReturn .write) (b :: bits) left after right) =
      atBits (.fieldSeek .target) (b :: bits) left after right := by
  cases b <;> rfl

theorem atBits_write_handoff_nonempty (bits : List Bool)
    (hbits : bits ≠ []) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits (.fieldReturn .write) bits left after right) =
      atBits (.fieldSeek .target) bits left after right := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons b bs => exact atBits_write_handoff b bs left after right

theorem atBits_target_first (b : Bool) (bits : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    oneStep (atBits (.fieldReturn .target) (b :: bits) left after right) =
      atBits (.skipMoveSecond b) bits (codeTape b :: left) after right := by
  cases b <;> cases bits <;> rfl

theorem atBits_move_second (m : OneTapeTableau.Move) (bits : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    oneStep (atBits (.skipMoveSecond (moveFirst m))
      (moveSecond m :: bits) left after right) =
      atBits .skipRule bits (codeTape (moveSecond m) :: left) after right := by
  cases m <;> cases bits <;> rfl

def mismatchBoundaryTape (b : Bool) : Tape :=
  if b then ulogCore sourceBoundaryOne else ulogCore sourceBoundaryZero

theorem atBits_mismatchSlot (lookupSlot ruleSlot : Bool)
    (bits : List Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits (.mismatchSkipSlot lookupSlot)
      (ruleSlot :: bits) left after right) =
      atBits (.mismatchSkipWrite lookupSlot) bits
        (codeTape ruleSlot :: left) after right := by
  cases lookupSlot <;> cases ruleSlot <;> cases bits <;> rfl

theorem atBits_mismatchMoveFirst (lookupSlot bit : Bool)
    (bits : List Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits (.mismatchSkipMoveFirst lookupSlot)
      (bit :: bits) left after right) =
      atBits (.mismatchSkipMoveSecond lookupSlot) bits
        (codeTape bit :: left) after right := by
  cases lookupSlot <;> cases bit <;> cases bits <;> rfl

theorem atBits_mismatchMoveSecond (lookupSlot bit : Bool)
    (bits : List Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits (.mismatchSkipMoveSecond lookupSlot)
      (bit :: bits) left after right) =
      atBits (.fieldCompare .source lookupSlot) bits
        (mismatchBoundaryTape bit :: left) after right := by
  cases lookupSlot <;> cases bit <;> cases bits <;> rfl

theorem reaches_mismatchSkipRule (lookupSlot : Bool)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r ++ next) left after right)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchBoundaryTape (moveSecond r.action.move) ::
          codeTape (moveFirst r.action.move) ::
            (ULogBytecode.encodeNatField r.action.target).reverse.map
              codeTape ++
            (ULogBytecode.encodeNatField r.action.write).reverse.map
              codeTape ++
            codeTape r.slot ::
            (ULogBytecode.encodeNatField r.read).reverse.map codeTape ++
            (ULogBytecode.encodeNatField r.source).reverse.map codeTape ++
            left)
        after right) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [moveFirst move, moveSecond move]
  let lS := sBits.reverse.map codeTape ++ left
  let lR := rBits.reverse.map codeTape ++ lS
  let lSlot := codeTape ruleSlot :: lR
  let lW := wBits.reverse.map codeTape ++ lSlot
  let lT := tBits.reverse.map codeTape ++ lW
  let lM₁ := codeTape (moveFirst move) :: lT
  let lM₂ := mismatchBoundaryTape (moveSecond move) :: lM₁
  have hS : Reaches
      (atBits (.mismatchSkipSource lookupSlot)
        (sBits ++ rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        left after right)
      (atBits (.mismatchSkipRead lookupSlot)
        (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        lS after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipSource lookupSlot) (.mismatchSkipRead lookupSlot)
        source (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        (by simp [rBits, ULogBytecode.encodeNatField])
        (fun l y rr => mismatchSkipSource_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipSource_one lookupSlot l y rr)
        left after right)
  have hR : Reaches
      (atBits (.mismatchSkipRead lookupSlot)
        (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        lS after right)
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipRead lookupSlot) (.mismatchSkipSlot lookupSlot)
        read ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) (by simp)
        (fun l y rr => mismatchSkipRead_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipRead_one lookupSlot l y rr)
        lS after right)
  have hSlot : Reaches
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right)
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right) := by
    exact reaches_step (by
      simpa [lSlot, List.append_assoc] using
        (atBits_mismatchSlot lookupSlot ruleSlot
          (wBits ++ tBits ++ mBits ++ next) lR after right))
  have hW : Reaches
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right)
      (atBits (.mismatchSkipTarget lookupSlot)
        (tBits ++ mBits ++ next) lW after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipWrite lookupSlot) (.mismatchSkipTarget lookupSlot)
        write (tBits ++ mBits ++ next)
        (by simp [tBits, ULogBytecode.encodeNatField])
        (fun l y rr => mismatchSkipWrite_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipWrite_one lookupSlot l y rr)
        lSlot after right)
  have hT : Reaches
      (atBits (.mismatchSkipTarget lookupSlot)
        (tBits ++ mBits ++ next) lW after right)
      (atBits (.mismatchSkipMoveFirst lookupSlot)
        (mBits ++ next) lT after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipTarget lookupSlot) (.mismatchSkipMoveFirst lookupSlot)
        target (mBits ++ next) (by simp [mBits])
        (fun l y rr => mismatchSkipTarget_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipTarget_one lookupSlot l y rr)
        lW after right)
  have hM₁ : Reaches
      (atBits (.mismatchSkipMoveFirst lookupSlot)
        (mBits ++ next) lT after right)
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right) := by
    exact reaches_step (by
      simpa [mBits, lM₁, List.append_assoc] using
        (atBits_mismatchMoveFirst lookupSlot (moveFirst move)
          (moveSecond move :: next) lT after right))
  have hM₂ : Reaches
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right)
      (atBits (.fieldCompare .source lookupSlot) next lM₂ after right) := by
    cases next with
    | nil => exact (hnext rfl).elim
    | cons b bs =>
        exact reaches_step (by
          simpa [lM₂] using
            (atBits_mismatchMoveSecond lookupSlot (moveSecond move)
              (b :: bs) lM₁ after right))
  have hall := reaches_trans hS (reaches_trans hR
    (reaches_trans hSlot (reaches_trans hW
      (reaches_trans hT (reaches_trans hM₁ hM₂)))))
  simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
    lT, lM₁, lM₂, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, List.reverse_append, List.map_append,
    List.append_assoc] using hall

def mismatchRulePrefix (r : ULogBytecode.RuleCode) : List Tape :=
  mismatchBoundaryTape (moveSecond r.action.move) ::
    codeTape (moveFirst r.action.move) ::
      (ULogBytecode.encodeNatField r.action.target).reverse.map codeTape ++
      (ULogBytecode.encodeNatField r.action.write).reverse.map codeTape ++
      codeTape r.slot ::
      (ULogBytecode.encodeNatField r.read).reverse.map codeTape ++
      (ULogBytecode.encodeNatField r.source).reverse.map codeTape

theorem reaches_mismatchCount_skipRule (lookupSlot : Bool) (done : ℕ)
    (path : List Tape) (hpath : MismatchBoundaryFree path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++ left)
        after right) := by
  let countLeft := ulogCore codeZero ::
    List.replicate done (ulogCore codeZero) ++ left
  let restoredLeft :=
    (if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: path.reverse ++ countLeft
  have h₀ := reaches_mismatchCount_prefix_fresh lookupSlot done path left
    (ulogCore boundary)
    ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
  have h₁ := reaches_mismatchSeekBoundary_rule lookupSlot path hpath
    boundary hboundary r next countLeft after right
  have h₂ := reaches_mismatchSkipRule lookupSlot r next hnext
    restoredLeft after right
  have hall := reaches_trans h₀ (reaches_trans h₁ h₂)
  simpa [countLeft, restoredLeft, mismatchRulePrefix,
    List.append_assoc] using hall

theorem reaches_skipRule (r : ULogBytecode.RuleCode)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.fieldSeek .source) (ULogBytecode.encodeRule r)
        left after right)
      (.running .skipRule
        ⟨(ULogBytecode.encodeRule r).reverse.map codeTape ++ left,
          after, right⟩) := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [moveFirst move, moveSecond move]
  let lS := sBits.reverse.map codeTape ++ left
  let lR := rBits.reverse.map codeTape ++ lS
  let lSlot := codeTape slot :: lR
  let lW := wBits.reverse.map codeTape ++ lSlot
  let lT := tBits.reverse.map codeTape ++ lW
  let lM₁ := codeTape (moveFirst move) :: lT
  let lM₂ := codeTape (moveSecond move) :: lM₁
  have hS : Reaches
      (atBits (.fieldSeek .source)
        (sBits ++ rBits ++ [slot] ++ wBits ++ tBits ++ mBits)
        left after right)
      (atBits (.fieldReturn .source)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right) := by
    simpa only [List.append_assoc] using
      (reaches_field_prefix .source source
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) (by
          simp [rBits, ULogBytecode.encodeNatField]) left after right)
  have hSH : Reaches
      (atBits (.fieldReturn .source)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right)
      (atBits (.fieldSeek .read)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right) :=
    reaches_step (atBits_source_handoff_nonempty _ (by
      simp [rBits, ULogBytecode.encodeNatField]) lS after right)
  have hR : Reaches
      (atBits (.fieldSeek .read)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right)
      (atBits (.fieldReturn .read)
        ([slot] ++ wBits ++ tBits ++ mBits) lR after right) := by
    simpa only [List.append_assoc] using
      (reaches_field_prefix .read read
        ([slot] ++ wBits ++ tBits ++ mBits) (by simp) lS after right)
  have hSlot : Reaches
      (atBits (.fieldReturn .read)
        ([slot] ++ wBits ++ tBits ++ mBits) lR after right)
      (atBits (.fieldSeek .write) (wBits ++ tBits ++ mBits)
        lSlot after right) := by
    exact reaches_step (by
      simpa [lSlot, List.append_assoc] using
        (atBits_read_slot slot (wBits ++ tBits ++ mBits) lR after right))
  have hW : Reaches
      (atBits (.fieldSeek .write) (wBits ++ tBits ++ mBits)
        lSlot after right)
      (atBits (.fieldReturn .write) (tBits ++ mBits) lW after right) := by
    simpa only [List.append_assoc] using
      (reaches_field_prefix .write write (tBits ++ mBits) (by
        simp [tBits, ULogBytecode.encodeNatField]) lSlot after right)
  have hWH : Reaches
      (atBits (.fieldReturn .write) (tBits ++ mBits) lW after right)
      (atBits (.fieldSeek .target) (tBits ++ mBits) lW after right) :=
    reaches_step (atBits_write_handoff_nonempty _ (by
      simp [tBits, ULogBytecode.encodeNatField]) lW after right)
  have hT : Reaches
      (atBits (.fieldSeek .target) (tBits ++ mBits) lW after right)
      (atBits (.fieldReturn .target) mBits lT after right) :=
    reaches_field_prefix .target target mBits (by simp [mBits]) lW after right
  have hM₁ : Reaches
      (atBits (.fieldReturn .target) mBits lT after right)
      (atBits (.skipMoveSecond (moveFirst move)) [moveSecond move]
        lM₁ after right) := by
    exact reaches_step (by
      simpa [mBits] using
        (atBits_target_first (moveFirst move) [moveSecond move]
          lT after right))
  have hM₂ : Reaches
      (atBits (.skipMoveSecond (moveFirst move)) [moveSecond move]
        lM₁ after right)
      (atBits .skipRule [] lM₂ after right) := by
    exact reaches_step (by
      simpa using (atBits_move_second move [] lM₁ after right))
  have hall := reaches_trans hS (reaches_trans hSH (reaches_trans hR
    (reaches_trans hSlot (reaches_trans hW (reaches_trans hWH
      (reaches_trans hT (reaches_trans hM₁ hM₂)))))))
  simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
    lT, lM₁, lM₂, atBits, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, List.reverse_append, List.map_append,
    List.append_assoc] using hall

theorem reaches_rule_to_next (r : ULogBytecode.RuleCode) (b : Bool)
    (left right : List Tape) :
    Reaches
      (atBits (.fieldSeek .source) (ULogBytecode.encodeRule r)
        left (codeTape b) right)
      (.running (.fieldReturn .programCount)
        ⟨(ULogBytecode.encodeRule r).reverse.map codeTape ++ left,
          codeTape b, right⟩) :=
  reaches_trans (reaches_skipRule r left (codeTape b) right)
    (reaches_step (skipRule_next_step b _ right))

theorem reaches_rule_to_end (r : ULogBytecode.RuleCode) (b : Bool)
    (left right : List Tape) :
    Reaches
      (atBits (.fieldSeek .source) (ULogBytecode.encodeRule r)
        left (ulogCore codeEnd) (codeTape b :: right))
      (.running (.fieldReturn .programCount)
        ⟨ulogCore codeEnd ::
            (ULogBytecode.encodeRule r).reverse.map codeTape ++ left,
          codeTape b, right⟩) :=
  reaches_trans
    (reaches_skipRule r left (ulogCore codeEnd) (codeTape b :: right))
    (reaches_step (skipRule_end_step _ b right))

def freshRuleLeft (skipped : List Bool) (remaining done : ℕ)
    (left : List Tape) : List Tape :=
  (seekPath skipped remaining).reverse ++
    ulogCore pcDone :: List.replicate done (ulogCore pcDone) ++
      ulogCore pcMark :: left

theorem reaches_countFresh_bits (bits : List Bool) (hbits : bits ≠ [])
    (skipped : List Bool) (remaining done : ℕ) (left : List Tape)
    (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount) bits
        (returnPath skipped (remaining + 1) done ++ ulogCore pcMark :: left)
        after right)
      (atBits (.fieldSeek .source) bits
        (freshRuleLeft skipped remaining done left) after right) := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons b bs =>
      simpa [atBits, countCheckStart, countFreshDone, freshRuleLeft] using
        (reaches_countFresh b skipped remaining done left
          (bs.map codeTape ++ after :: right))

theorem reaches_skipRule_prefix (r : ULogBytecode.RuleCode)
    (tail : List Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    Reaches
      (atBits (.fieldSeek .source)
        (ULogBytecode.encodeRule r ++ tail) left after right)
      (atBits .skipRule tail
        ((ULogBytecode.encodeRule r).reverse.map codeTape ++ left)
        after right) := by
  have hr : ULogBytecode.encodeRule r ≠ [] := by
    rcases r with ⟨source, read, slot, action⟩
    cases source <;>
      simp [ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
        List.replicate_succ]
  cases he : ULogBytecode.encodeRule r with
  | nil => exact (hr he).elim
  | cons b bs =>
      cases tail with
      | nil => simpa [atBits, he] using reaches_skipRule r left after right
      | cons c cs =>
          simpa [atBits, he, List.map_append, List.append_assoc] using
            (reaches_skipRule r left (codeTape c)
              (cs.map codeTape ++ after :: right))

theorem atBits_skipRule_next_nonempty (bits : List Bool)
    (hbits : bits ≠ []) (left : List Tape) (after : Tape)
    (right : List Tape) :
    oneStep (atBits .skipRule bits left after right) =
      atBits (.fieldReturn .programCount) bits left after right := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons b bs =>
      cases b <;> rfl

theorem freshRuleLeft_eq_returnPath (skipped : List Bool)
    (r : ULogBytecode.RuleCode) (remaining done : ℕ)
    (left : List Tape) :
    (ULogBytecode.encodeRule r).reverse.map codeTape ++
        freshRuleLeft skipped remaining done left =
      returnPath (skipped ++ ULogBytecode.encodeRule r) remaining (done + 1) ++
        ulogCore pcMark :: left := by
  simp [freshRuleLeft, returnPath, seekPath, List.reverse_append,
    List.map_append, List.replicate_succ, List.append_assoc]

theorem reaches_ruleRound_next (skipped : List Bool) (done remaining : ℕ)
    (r : ULogBytecode.RuleCode) (tail : List Bool) (htail : tail ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRule r ++ tail)
        (returnPath skipped (remaining + 1) done ++ ulogCore pcMark :: left)
        after right)
      (atBits (.fieldReturn .programCount) tail
        (returnPath (skipped ++ ULogBytecode.encodeRule r) remaining
            (done + 1) ++ ulogCore pcMark :: left)
        after right) := by
  have hbits : ULogBytecode.encodeRule r ++ tail ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [ULogBytecode.encodeRule, ULogBytecode.encodeNatField] at this
  have h₀ := reaches_countFresh_bits
    (ULogBytecode.encodeRule r ++ tail) hbits skipped remaining done
    left after right
  have h₁ := reaches_skipRule_prefix r tail
    (freshRuleLeft skipped remaining done left) after right
  have h₂ : Reaches
      (atBits .skipRule tail
        ((ULogBytecode.encodeRule r).reverse.map codeTape ++
          freshRuleLeft skipped remaining done left) after right)
      (atBits (.fieldReturn .programCount) tail
        ((ULogBytecode.encodeRule r).reverse.map codeTape ++
          freshRuleLeft skipped remaining done left) after right) :=
    reaches_step (atBits_skipRule_next_nonempty tail htail _ after right)
  have hall := reaches_trans h₀ (reaches_trans h₁ h₂)
  rw [freshRuleLeft_eq_returnPath skipped r remaining done left] at hall
  exact hall

theorem reaches_ruleRound_last (skipped : List Bool) (done : ℕ)
    (r : ULogBytecode.RuleCode) (payloadCarry : Bool)
    (left right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount) (ULogBytecode.encodeRule r)
        (returnPath skipped 1 done ++ ulogCore pcMark :: left)
        (ulogCore codeEnd) (codeTape payloadCarry :: right))
      (finalCountCheckStart payloadCarry
        (skipped ++ ULogBytecode.encodeRule r) (done + 1) left right) := by
  have hbits : ULogBytecode.encodeRule r ≠ [] := by
    rcases r with ⟨source, read, slot, action⟩
    cases source <;>
      simp [ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
        List.replicate_succ]
  have h₀ := reaches_countFresh_bits (ULogBytecode.encodeRule r) hbits
    skipped 0 done left (ulogCore codeEnd) (codeTape payloadCarry :: right)
  have h₁ := reaches_skipRule r (freshRuleLeft skipped 0 done left)
    (ulogCore codeEnd) (codeTape payloadCarry :: right)
  have h₂ : Reaches
      (.running .skipRule
        ⟨(ULogBytecode.encodeRule r).reverse.map codeTape ++
            freshRuleLeft skipped 0 done left,
          ulogCore codeEnd, codeTape payloadCarry :: right⟩)
      (.running (.fieldReturn .programCount)
        ⟨ulogCore codeEnd ::
            (ULogBytecode.encodeRule r).reverse.map codeTape ++
              freshRuleLeft skipped 0 done left,
          codeTape payloadCarry, right⟩) :=
    reaches_step (skipRule_end_step _ payloadCarry right)
  have hall := reaches_trans h₀ (reaches_trans h₁ h₂)
  have hleft :
      (ulogCore codeEnd ::
          (ULogBytecode.encodeRule r).reverse.map codeTape) ++
          freshRuleLeft skipped 0 done left =
        ulogCore codeEnd ::
          (returnPath (skipped ++ ULogBytecode.encodeRule r) 0 (done + 1) ++
            ulogCore pcMark :: left) := by
    rw [List.cons_append, freshRuleLeft_eq_returnPath]
  rw [hleft] at hall
  simpa [finalCountCheckStart, finalReturnPath, returnPath] using hall

theorem encodeRule_ne_nil (r : ULogBytecode.RuleCode) :
    ULogBytecode.encodeRule r ≠ [] := by
  rcases r with ⟨source, read, slot, action⟩
  cases source <;>
    simp [ULogBytecode.encodeRule, ULogBytecode.encodeNatField,
      List.replicate_succ]

theorem encodeRules_ne_nil {rules : List ULogBytecode.RuleCode}
    (hrules : rules ≠ []) : ULogBytecode.encodeRules rules ≠ [] := by
  cases rules with
  | nil => exact (hrules rfl).elim
  | cons r rs =>
      simp only [ULogBytecode.encodeRules]
      exact List.append_ne_nil_of_left_ne_nil (encodeRule_ne_nil r) _

theorem reaches_ruleList_aux (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (skipped : List Bool) (done : ℕ)
    (payloadCarry : Bool) (left right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount) (ULogBytecode.encodeRules rules)
        (returnPath skipped rules.length done ++ ulogCore pcMark :: left)
        (ulogCore codeEnd) (codeTape payloadCarry :: right))
      (finalCountCheckStart payloadCarry
        (skipped ++ ULogBytecode.encodeRules rules)
        (done + rules.length) left right) := by
  induction rules generalizing skipped done with
  | nil => exact (hrules rfl).elim
  | cons r rs ih =>
      cases rs with
      | nil =>
          simpa [ULogBytecode.encodeRules] using
            (reaches_ruleRound_last skipped done r payloadCarry left right)
      | cons s ss =>
          let tail := ULogBytecode.encodeRules (s :: ss)
          have htail : tail ≠ [] := encodeRules_ne_nil (by simp)
          have h₀ := reaches_ruleRound_next skipped done (s :: ss).length
            r tail htail left (ulogCore codeEnd)
            (codeTape payloadCarry :: right)
          have h₁ := ih (by simp) (skipped ++ ULogBytecode.encodeRule r)
            (done + 1)
          have hall := reaches_trans h₀ h₁
          simpa [tail, ULogBytecode.encodeRules, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem reaches_ruleList (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (payloadCarry : Bool)
    (left right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount) (ULogBytecode.encodeRules rules)
        (returnPath [] rules.length 0 ++ ulogCore pcMark :: left)
        (ulogCore codeEnd) (codeTape payloadCarry :: right))
      (finalCountDone payloadCarry (ULogBytecode.encodeRules rules)
        rules.length left right) :=
  reaches_trans
    (reaches_ruleList_aux rules hrules [] 0 payloadCarry left right)
    (by simpa using (reaches_finalCountExhausted payloadCarry
      (ULogBytecode.encodeRules rules) rules.length left right))

theorem reaches_programCount (n : ℕ) (left : List Tape)
    (y : Tape) (right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          List.replicate n (ulogCore codeZero) ++
            ulogCore codeOne :: y :: right⟩)
      (.running (.fieldReturn .programCount)
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++
              ulogCore pcMark :: left),
          y, right⟩) := by
  have h₀ : Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          List.replicate n (ulogCore codeZero) ++
            ulogCore codeOne :: y :: right⟩)
      (beforeFieldZeros .programCount n (ulogCore pcMark :: left) y right) := by
    apply reaches_step
    cases n <;> simp [beforeFieldZeros, framePayloadLength_step,
      List.replicate_succ, List.append_assoc]
  exact reaches_trans h₀ (reaches_field .programCount n _ y right)

theorem reaches_programCount_atRules (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (payloadCarry : Bool)
    (left right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules).map codeTape ++
            ulogCore codeEnd :: codeTape payloadCarry :: right⟩)
      (atBits (.fieldReturn .programCount) (ULogBytecode.encodeRules rules)
        (returnPath [] rules.length 0 ++ ulogCore pcMark :: left)
        (ulogCore codeEnd) (codeTape payloadCarry :: right)) := by
  have henc : ULogBytecode.encodeRules rules ≠ [] :=
    encodeRules_ne_nil hrules
  cases he : ULogBytecode.encodeRules rules with
  | nil => exact (henc he).elim
  | cons b bs =>
      simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField,
        atBits, returnPath, codeTape, he, List.map_append,
        List.append_assoc] using
        (reaches_programCount rules.length left (codeTape b)
          (bs.map codeTape ++ ulogCore codeEnd ::
            codeTape payloadCarry :: right))

theorem reaches_programRules (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (payloadCarry : Bool)
    (left right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules).map codeTape ++
            ulogCore codeEnd :: codeTape payloadCarry :: right⟩)
      (finalCountDone payloadCarry (ULogBytecode.encodeRules rules)
        rules.length left right) :=
  reaches_trans
    (reaches_programCount_atRules rules hrules payloadCarry left right)
    (reaches_ruleList rules hrules payloadCarry left right)

theorem reaches_programRules_empty (payloadCarry : Bool)
    (left right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram []).map codeTape ++
            ulogCore codeEnd :: codeTape payloadCarry :: right⟩)
      (finalCountDone payloadCarry [] 0 left right) := by
  have h₀ := reaches_programCount 0 left (ulogCore codeEnd)
    (codeTape payloadCarry :: right)
  have h₁ : Reaches
      (.running (.fieldReturn .programCount)
        ⟨ulogCore codeOne :: ulogCore pcMark :: left,
          ulogCore codeEnd, codeTape payloadCarry :: right⟩)
      (finalCountCheckStart payloadCarry [] 0 left right) := by
    apply reaches_step
    simpa [finalCountCheckStart, finalReturnPath, codeTape] using
      (fieldReturn_count_end_step
        (ulogCore codeOne :: ulogCore pcMark :: left) payloadCarry right)
  have hall := reaches_trans h₀
    (reaches_trans h₁
      (reaches_finalCountExhausted payloadCarry [] 0 left right))
  simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeRules,
    ULogBytecode.encodeNatField, codeTape] using hall

theorem reaches_programRules_all (rules : List ULogBytecode.RuleCode)
    (payloadCarry : Bool) (left right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules).map codeTape ++
            ulogCore codeEnd :: codeTape payloadCarry :: right⟩)
      (finalCountDone payloadCarry (ULogBytecode.encodeRules rules)
        rules.length left right) := by
  cases rules with
  | nil => exact reaches_programRules_empty payloadCarry left right
  | cons r rs =>
      exact reaches_programRules (r :: rs) (by simp) payloadCarry left right

/-- The actual self-delimiting program/payload boundary has no physical
separator: the first payload-length bit is the carry cell for the final
exhausted count round. -/
theorem reaches_ruleList_payload_aux (rules : List ULogBytecode.RuleCode)
    (skipped : List Bool) (done : ℕ) (payloadCarry : Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRules rules ++ [payloadCarry])
        (returnPath skipped rules.length done ++ ulogCore pcMark :: left)
        after right)
      (countCheckStart payloadCarry
        (skipped ++ ULogBytecode.encodeRules rules) 0
        (done + rules.length) left (after :: right)) := by
  induction rules generalizing skipped done with
  | nil =>
      simp [ULogBytecode.encodeRules, atBits, countCheckStart, returnPath]
      exact reaches_refl _
  | cons r rs ih =>
      let tail := ULogBytecode.encodeRules rs ++ [payloadCarry]
      have htail : tail ≠ [] := by simp [tail]
      have h₀ := reaches_ruleRound_next skipped done rs.length r tail htail
        left after right
      have h₁ := ih (skipped ++ ULogBytecode.encodeRule r) (done + 1)
      have hall := reaches_trans h₀ h₁
      simpa [tail, ULogBytecode.encodeRules, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem reaches_programCount_atPayload (rules : List ULogBytecode.RuleCode)
    (payloadCarry : Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++ [payloadCarry]).map codeTape ++
            after :: right⟩)
      (atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRules rules ++ [payloadCarry])
        (returnPath [] rules.length 0 ++ ulogCore pcMark :: left)
        after right) := by
  cases he : ULogBytecode.encodeRules rules with
  | nil =>
      simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField,
        atBits, returnPath, codeTape, he, List.map_append,
        List.append_assoc] using
        (reaches_programCount rules.length left (codeTape payloadCarry)
          (after :: right))
  | cons b bs =>
      simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField,
        atBits, returnPath, codeTape, he, List.map_append,
        List.append_assoc] using
        (reaches_programCount rules.length left (codeTape b)
          (bs.map codeTape ++ codeTape payloadCarry :: after :: right))

theorem reaches_programPayloadLength (rules : List ULogBytecode.RuleCode)
    (payloadCarry : Bool) (left : List Tape) (after : Tape)
    (right : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++ [payloadCarry]).map codeTape ++
            after :: right⟩)
      (countExhaustedDone payloadCarry (ULogBytecode.encodeRules rules)
        rules.length left (after :: right)) := by
  exact reaches_trans
    (reaches_programCount_atPayload rules payloadCarry left after right)
    (reaches_trans
      (reaches_ruleList_payload_aux rules [] 0 payloadCarry left after right)
      (by simpa using
        (reaches_countExhausted payloadCarry
          (ULogBytecode.encodeRules rules) rules.length left
          (after :: right))))

def programMarkedLeft (rules : List ULogBytecode.RuleCode)
    (left : List Tape) : List Tape :=
  ((ULogBytecode.encodeRules rules).map codeTape).reverse ++
    codeTape true :: List.replicate rules.length (ulogCore pcDone) ++
      ulogCore pcMark :: left

theorem encodePayload_ne_nil (input padding : List Bool) :
    ULogBytecode.encodePayload input padding ≠ [] := by
  simp [ULogBytecode.encodePayload, ULogBytecode.encodeNatField]

theorem reaches_programPayloadStart (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (left tail : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map codeTape ++
              ulogCore codeEnd :: tail⟩)
      (atBits .payloadLengthStart
        (ULogBytecode.encodePayload input padding)
        (programMarkedLeft rules left) (ulogCore codeEnd) tail) := by
  have hp := encodePayload_ne_nil input padding
  cases he : ULogBytecode.encodePayload input padding with
  | nil => exact (hp he).elim
  | cons b bs =>
      cases bs with
      | nil =>
          simpa [atBits, programMarkedLeft, countExhaustedDone, he,
            List.map_append,
            List.append_assoc] using
            (reaches_programPayloadLength rules b left
              (ulogCore codeEnd) tail)
      | cons c cs =>
          simpa [atBits, programMarkedLeft, countExhaustedDone, he,
            List.map_append,
            List.append_assoc] using
            (reaches_programPayloadLength rules b left (codeTape c)
              (cs.map codeTape ++ ulogCore codeEnd :: tail))

def payloadLengthMarkedLeft (inputLength : ℕ) (left : List Tape) : List Tape :=
  match inputLength with
  | 0 => ulogCore payloadStartOne :: left
  | n + 1 =>
      (ULogBytecode.encodeNatField n).reverse.map codeTape ++
        ulogCore payloadStartZero :: left

theorem reaches_payloadLengthDecoded (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (left tail : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map codeTape ++
              ulogCore codeEnd :: tail⟩)
      (atBits (.fieldReturn .payloadLength) (input ++ padding)
        (payloadLengthMarkedLeft input.length (programMarkedLeft rules left))
        (ulogCore codeEnd) tail) := by
  have h₀ := reaches_programPayloadStart rules input padding left tail
  cases input with
  | nil =>
      have h₁ : Reaches
          (atBits .payloadLengthStart
            (ULogBytecode.encodePayload [] padding)
            (programMarkedLeft rules left) (ulogCore codeEnd) tail)
          (atBits (.fieldReturn .payloadLength) padding
            (payloadLengthMarkedLeft 0 (programMarkedLeft rules left))
            (ulogCore codeEnd) tail) := by
        apply reaches_step
        cases padding <;>
          simp [ULogBytecode.encodePayload, ULogBytecode.encodeNatField,
            atBits, payloadLengthMarkedLeft, payloadLengthStart_one_step]
      exact reaches_trans h₀ h₁
  | cons b input =>
      have hstart : Reaches
          (atBits .payloadLengthStart
            (ULogBytecode.encodePayload (b :: input) padding)
            (programMarkedLeft rules left) (ulogCore codeEnd) tail)
          (atBits (.fieldSeek .payloadLength)
            (ULogBytecode.encodeNatField input.length ++
              ((b :: input) ++ padding))
            (ulogCore payloadStartZero :: programMarkedLeft rules left)
            (ulogCore codeEnd) tail) := by
        apply reaches_step
        cases input <;>
          simp [ULogBytecode.encodePayload, ULogBytecode.encodeNatField,
            atBits, payloadLengthStart_zero_step, List.replicate_succ,
            List.append_assoc]
      have hscan := reaches_field_prefix_any .payloadLength input.length
        ((b :: input) ++ padding)
        (ulogCore payloadStartZero :: programMarkedLeft rules left)
        (ulogCore codeEnd) tail
      have hall := reaches_trans h₀ (reaches_trans hstart hscan)
      simpa [payloadLengthMarkedLeft, List.append_assoc] using hall

theorem reaches_payloadReturn_end (carry : Bool) (processed : List Bool)
    (counter : List Tape) (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd :: counter,
          codeTape carry, right⟩)
      (.running (.payloadReturn carry)
        ⟨counter, ulogCore payloadEnd,
          processed.map payloadTape ++ branchTape carry :: right⟩) := by
  let path := processed.reverse.map payloadTape
  have h₀ : Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨path ++ ulogCore payloadEnd :: counter, codeTape carry, right⟩)
      (.running (.payloadReturn carry)
        (beforeLeftPath path counter (ulogCore payloadEnd)
          (branchTape carry :: right))) := by
    apply reaches_step
    cases hp : path with
    | nil =>
        simp [beforeLeftPath, hp, fieldReturn_payload_step]
    | cons x xs =>
        simp [beforeLeftPath, hp, fieldReturn_payload_step,
          List.cons_append]
  have h₁ : Reaches
      (.running (.payloadReturn carry)
        (beforeLeftPath path counter (ulogCore payloadEnd)
          (branchTape carry :: right)))
      (.running (.payloadReturn carry)
        (afterLeftPath path counter (ulogCore payloadEnd)
          (branchTape carry :: right))) := by
    exact ⟨path.length, run_left_path_of (.payloadReturn carry) path (by
      intro x hx l y r
      rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
      exact payloadReturn_pass_code carry b l y r)
      counter (ulogCore payloadEnd) (branchTape carry :: right)⟩
  have hall := reaches_trans h₀ h₁
  simpa [path, afterLeftPath, List.map_reverse, List.append_assoc] using hall

theorem reaches_payloadFreshZero (carry : Bool) (next : Tape)
    (processed : List Bool) (remaining done : ℕ)
    (base : List Tape) (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            List.replicate done (ulogCore payloadDone) ++
              List.replicate (remaining + 1) (ulogCore codeZero) ++
                ulogCore payloadStartZero :: base,
          codeTape carry, next :: right⟩)
      (.running (.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map payloadTape ++
            ulogCore payloadEnd ::
              List.replicate (done + 1) (ulogCore payloadDone) ++
                List.replicate remaining (ulogCore codeZero) ++
                  ulogCore payloadStartZero :: base,
          next, right⟩) := by
  let donePath := List.replicate done (ulogCore payloadDone)
  let freshRest := List.replicate remaining (ulogCore codeZero) ++
    ulogCore payloadStartZero :: base
  have h₀ := reaches_payloadReturn_end carry processed
    (donePath ++ ulogCore codeZero :: freshRest) (next :: right)
  have h₁ : Reaches
      (.running (.payloadReturn carry)
        ⟨donePath ++ ulogCore codeZero :: freshRest,
          ulogCore payloadEnd,
          processed.map payloadTape ++ branchTape carry ::
            next :: right⟩)
      (.running (.payloadCount carry)
        (beforeLeftPath donePath freshRest (ulogCore codeZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, beforeLeftPath, payloadReturn_end_step,
        List.replicate_succ, List.append_assoc]
  have h₂ : Reaches
      (.running (.payloadCount carry)
        (beforeLeftPath donePath freshRest (ulogCore codeZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right)))
      (.running (.payloadCount carry)
        (afterLeftPath donePath freshRest (ulogCore codeZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right))) := by
    exact ⟨donePath.length, run_left_path_of (.payloadCount carry) donePath (by
      intro x hx l y r
      have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
        simpa [donePath, List.mem_replicate] using hx
      rw [hm.2]
      exact payloadCount_done_step carry l y r)
      freshRest (ulogCore codeZero)
      (ulogCore payloadEnd :: processed.map payloadTape ++
        branchTape carry :: next :: right)⟩
  have h₃ : Reaches
      (.running (.payloadCount carry)
        (afterLeftPath donePath freshRest (ulogCore codeZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right)))
      (.running (.payloadSeekReturn carry false)
        (beforeRightPath donePath (ulogCore payloadDone :: freshRest)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry ::
            next :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, afterLeftPath, beforeRightPath,
        payloadCount_zero_step, List.replicate_succ,
        List.append_assoc]
  have h₄ : Reaches
      (.running (.payloadSeekReturn carry false)
        (beforeRightPath donePath (ulogCore payloadDone :: freshRest)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry ::
            next :: right)))
      (.running (.payloadSeekReturn carry false)
        (afterRightPath donePath (ulogCore payloadDone :: freshRest)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry ::
            next :: right))) := by
    exact ⟨donePath.length,
      run_right_path_of (.payloadSeekReturn carry false) donePath (by
        intro x hx l y r
        have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
          simpa [donePath, List.mem_replicate] using hx
        rw [hm.2]
        exact payloadSeek_done_step carry false l y r)
      (ulogCore payloadDone :: freshRest) (ulogCore payloadEnd)
      (processed.map payloadTape ++ branchTape carry ::
        next :: right)⟩
  have h₅ : Reaches
      (.running (.payloadSeekReturn carry false)
        (afterRightPath donePath (ulogCore payloadDone :: freshRest)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry ::
            next :: right)))
      (.running (.payloadRestore carry false)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: List.replicate (done + 1)
            (ulogCore payloadDone) ++ freshRest)
          (branchTape carry) (next :: right))) := by
    apply reaches_step
    cases done <;> cases processed <;>
      simp [donePath, freshRest, afterRightPath, beforeRightPath,
        payloadSeek_end_step, List.replicate_succ,
        List.append_assoc]
  have h₆ : Reaches
      (.running (.payloadRestore carry false)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: List.replicate (done + 1)
            (ulogCore payloadDone) ++ freshRest)
          (branchTape carry) (next :: right)))
      (.running (.payloadRestore carry false)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: List.replicate (done + 1)
            (ulogCore payloadDone) ++ freshRest)
          (branchTape carry) (next :: right))) := by
    exact ⟨(processed.map payloadTape).length,
      run_right_path_of (.payloadRestore carry false)
        (processed.map payloadTape) (by
          intro x hx l y r
          rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
          exact payloadRestore_pass_code carry false b l y r)
        (ulogCore payloadEnd :: List.replicate (done + 1)
          (ulogCore payloadDone) ++ freshRest)
        (branchTape carry) (next :: right)⟩
  have h₇ : Reaches
      (.running (.payloadRestore carry false)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: List.replicate (done + 1)
            (ulogCore payloadDone) ++ freshRest)
          (branchTape carry) (next :: right)))
      (.running (.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map payloadTape ++
            ulogCore payloadEnd :: List.replicate (done + 1)
              (ulogCore payloadDone) ++ freshRest,
          next, right⟩) := by
    apply reaches_step
    simp [afterRightPath, payloadRestore_fresh_any, List.map_reverse,
      List.reverse_append, List.append_assoc]
  have hall := reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ (reaches_trans h₄ (reaches_trans h₅
      (reaches_trans h₆ h₇))))))
  simpa [donePath, freshRest, List.replicate_succ,
    List.append_assoc] using hall

theorem reaches_payloadFirstZero (carry : Bool) (next : Tape) (remaining : ℕ)
    (base : List Tape) (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨ulogCore codeOne :: ulogCore codeZero ::
            List.replicate remaining (ulogCore codeZero) ++
              ulogCore payloadStartZero :: base,
          codeTape carry, next :: right⟩)
      (.running (.fieldReturn .payloadLength)
        ⟨payloadTape carry :: ulogCore payloadEnd ::
            ulogCore payloadDone ::
              List.replicate remaining (ulogCore codeZero) ++
                ulogCore payloadStartZero :: base,
          next, right⟩) := by
  refine ⟨5, ?_⟩
  simp [run, fieldReturn_payload_step, payloadReturn_codeOne_step,
    payloadCount_zero_step, payloadSeek_end_step,
    payloadRestore_fresh_any, List.append_assoc]

theorem reaches_payloadFirstStart (carry : Bool) (next : Tape)
    (base : List Tape) (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨ulogCore codeOne :: ulogCore payloadStartZero :: base,
          codeTape carry, next :: right⟩)
      (.running (.fieldReturn .payloadLength)
        ⟨payloadTape carry :: ulogCore payloadEnd ::
            ulogCore payloadStartDone :: base,
          next, right⟩) := by
  refine ⟨5, ?_⟩
  simp [run, fieldReturn_payload_step, payloadReturn_codeOne_step,
    payloadCount_start_step, payloadSeek_end_step,
    payloadRestore_fresh_any]

theorem reaches_payloadExhausted (carry : Bool) (processed : List Bool)
    (done : ℕ) (base : List Tape) (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            List.replicate done (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base,
          codeTape carry, right⟩)
      (.running .framePadding
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            List.replicate done (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base,
          codeTape carry, right⟩) := by
  let donePath := List.replicate done (ulogCore payloadDone)
  have h₀ := reaches_payloadReturn_end carry processed
    (donePath ++ ulogCore payloadStartDone :: base) right
  have h₁ : Reaches
      (.running (.payloadReturn carry)
        ⟨donePath ++ ulogCore payloadStartDone :: base,
          ulogCore payloadEnd,
          processed.map payloadTape ++ branchTape carry :: right⟩)
      (.running (.payloadCount carry)
        (beforeLeftPath donePath base (ulogCore payloadStartDone)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, beforeLeftPath, payloadReturn_end_step,
        List.replicate_succ, List.append_assoc]
  have h₂ : Reaches
      (.running (.payloadCount carry)
        (beforeLeftPath donePath base (ulogCore payloadStartDone)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: right)))
      (.running (.payloadCount carry)
        (afterLeftPath donePath base (ulogCore payloadStartDone)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: right))) := by
    exact ⟨donePath.length, run_left_path_of (.payloadCount carry) donePath (by
      intro x hx l y r
      have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
        simpa [donePath, List.mem_replicate] using hx
      rw [hm.2]
      exact payloadCount_done_step carry l y r)
      base (ulogCore payloadStartDone)
      (ulogCore payloadEnd :: processed.map payloadTape ++
        branchTape carry :: right)⟩
  have h₃ : Reaches
      (.running (.payloadCount carry)
        (afterLeftPath donePath base (ulogCore payloadStartDone)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: right)))
      (.running (.payloadSeekReturn carry true)
        (beforeRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, afterLeftPath, beforeRightPath,
        payloadCount_exhausted_step, List.replicate_succ,
        List.append_assoc]
  have h₄ : Reaches
      (.running (.payloadSeekReturn carry true)
        (beforeRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: right)))
      (.running (.payloadSeekReturn carry true)
        (afterRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: right))) := by
    exact ⟨donePath.length,
      run_right_path_of (.payloadSeekReturn carry true) donePath (by
        intro x hx l y r
        have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
          simpa [donePath, List.mem_replicate] using hx
        rw [hm.2]
        exact payloadSeek_done_step carry true l y r)
      (ulogCore payloadStartDone :: base) (ulogCore payloadEnd)
      (processed.map payloadTape ++ branchTape carry :: right)⟩
  have h₅ : Reaches
      (.running (.payloadSeekReturn carry true)
        (afterRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: right)))
      (.running (.payloadRestore carry true)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) right)) := by
    apply reaches_step
    cases done <;> cases processed <;>
      simp [donePath, afterRightPath, beforeRightPath,
        payloadSeek_end_step, List.replicate_succ,
        List.append_assoc]
  have h₆ : Reaches
      (.running (.payloadRestore carry true)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) right))
      (.running (.payloadRestore carry true)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) right)) := by
    exact ⟨(processed.map payloadTape).length,
      run_right_path_of (.payloadRestore carry true)
        (processed.map payloadTape) (by
          intro x hx l y r
          rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
          exact payloadRestore_pass_code carry true b l y r)
        (ulogCore payloadEnd :: donePath ++
          ulogCore payloadStartDone :: base)
        (branchTape carry) right⟩
  have h₇ : Reaches
      (.running (.payloadRestore carry true)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) right))
      (.running .framePadding
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            donePath ++ ulogCore payloadStartDone :: base,
          codeTape carry, right⟩) := by
    apply reaches_step
    simp [afterRightPath, payloadRestore_exhausted_step,
      List.map_reverse, List.append_assoc]
  have hall := reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ (reaches_trans h₄ (reaches_trans h₅
      (reaches_trans h₆ h₇))))))
  simpa [donePath, List.append_assoc] using hall

theorem reaches_payloadFreshStart (carry : Bool) (next : Tape)
    (processed : List Bool) (done : ℕ) (base : List Tape)
    (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            List.replicate done (ulogCore payloadDone) ++
              ulogCore payloadStartZero :: base,
          codeTape carry, next :: right⟩)
      (.running (.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map payloadTape ++
            ulogCore payloadEnd ::
              List.replicate done (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base,
          next, right⟩) := by
  let donePath := List.replicate done (ulogCore payloadDone)
  have h₀ := reaches_payloadReturn_end carry processed
    (donePath ++ ulogCore payloadStartZero :: base) (next :: right)
  have h₁ : Reaches
      (.running (.payloadReturn carry)
        ⟨donePath ++ ulogCore payloadStartZero :: base,
          ulogCore payloadEnd,
          processed.map payloadTape ++ branchTape carry :: next :: right⟩)
      (.running (.payloadCount carry)
        (beforeLeftPath donePath base (ulogCore payloadStartZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, beforeLeftPath, payloadReturn_end_step,
        List.replicate_succ, List.append_assoc]
  have h₂ : Reaches
      (.running (.payloadCount carry)
        (beforeLeftPath donePath base (ulogCore payloadStartZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right)))
      (.running (.payloadCount carry)
        (afterLeftPath donePath base (ulogCore payloadStartZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right))) := by
    exact ⟨donePath.length, run_left_path_of (.payloadCount carry) donePath (by
      intro x hx l y r
      have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
        simpa [donePath, List.mem_replicate] using hx
      rw [hm.2]
      exact payloadCount_done_step carry l y r)
      base (ulogCore payloadStartZero)
      (ulogCore payloadEnd :: processed.map payloadTape ++
        branchTape carry :: next :: right)⟩
  have h₃ : Reaches
      (.running (.payloadCount carry)
        (afterLeftPath donePath base (ulogCore payloadStartZero)
          (ulogCore payloadEnd :: processed.map payloadTape ++
            branchTape carry :: next :: right)))
      (.running (.payloadSeekReturn carry false)
        (beforeRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: next :: right))) := by
    apply reaches_step
    cases done <;>
      simp [donePath, afterLeftPath, beforeRightPath,
        payloadCount_start_step, List.replicate_succ,
        List.append_assoc]
  have h₄ : Reaches
      (.running (.payloadSeekReturn carry false)
        (beforeRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: next :: right)))
      (.running (.payloadSeekReturn carry false)
        (afterRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: next :: right))) := by
    exact ⟨donePath.length,
      run_right_path_of (.payloadSeekReturn carry false) donePath (by
        intro x hx l y r
        have hm : done ≠ 0 ∧ x = ulogCore payloadDone := by
          simpa [donePath, List.mem_replicate] using hx
        rw [hm.2]
        exact payloadSeek_done_step carry false l y r)
      (ulogCore payloadStartDone :: base) (ulogCore payloadEnd)
      (processed.map payloadTape ++ branchTape carry :: next :: right)⟩
  have h₅ : Reaches
      (.running (.payloadSeekReturn carry false)
        (afterRightPath donePath (ulogCore payloadStartDone :: base)
          (ulogCore payloadEnd)
          (processed.map payloadTape ++ branchTape carry :: next :: right)))
      (.running (.payloadRestore carry false)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) (next :: right))) := by
    apply reaches_step
    cases done <;> cases processed <;>
      simp [donePath, afterRightPath, beforeRightPath,
        payloadSeek_end_step, List.replicate_succ,
        List.append_assoc]
  have h₆ : Reaches
      (.running (.payloadRestore carry false)
        (beforeRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) (next :: right)))
      (.running (.payloadRestore carry false)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) (next :: right))) := by
    exact ⟨(processed.map payloadTape).length,
      run_right_path_of (.payloadRestore carry false)
        (processed.map payloadTape) (by
          intro x hx l y r
          rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
          exact payloadRestore_pass_code carry false b l y r)
        (ulogCore payloadEnd :: donePath ++
          ulogCore payloadStartDone :: base)
        (branchTape carry) (next :: right)⟩
  have h₇ : Reaches
      (.running (.payloadRestore carry false)
        (afterRightPath (processed.map payloadTape)
          (ulogCore payloadEnd :: donePath ++
            ulogCore payloadStartDone :: base)
          (branchTape carry) (next :: right)))
      (.running (.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map payloadTape ++
            ulogCore payloadEnd :: donePath ++
              ulogCore payloadStartDone :: base,
          next, right⟩) := by
    apply reaches_step
    simp [afterRightPath, payloadRestore_fresh_any,
      List.map_reverse, List.reverse_append, List.append_assoc]
  have hall := reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂
    (reaches_trans h₃ (reaches_trans h₄ (reaches_trans h₅
      (reaches_trans h₆ h₇))))))
  simpa [donePath, List.append_assoc] using hall

theorem reaches_payloadFold (carry : Bool) (pending processed : List Bool)
    (done : ℕ) (base : List Tape) (after : Tape)
    (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨processed.reverse.map payloadTape ++ ulogCore payloadEnd ::
            List.replicate done (ulogCore payloadDone) ++
              List.replicate pending.length (ulogCore codeZero) ++
                ulogCore payloadStartZero :: base,
          codeTape carry, pending.map codeTape ++ after :: right⟩)
      (.running (.fieldReturn .payloadLength)
        ⟨(processed ++ carry :: pending).reverse.map payloadTape ++
            ulogCore payloadEnd ::
              List.replicate (done + pending.length) (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base,
          after, right⟩) := by
  induction pending generalizing carry processed done with
  | nil =>
      simpa using
        (reaches_payloadFreshStart carry after processed done base right)
  | cons next pending ih =>
      have h₀ := reaches_payloadFreshZero carry (codeTape next) processed
        pending.length done base
        (pending.map codeTape ++ after :: right)
      have h₁ := ih next (processed ++ [carry]) (done + 1)
      have hall := reaches_trans h₀ h₁
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, List.replicate_succ] using hall

def payloadFoldedLeft (input : List Bool) (base : List Tape) : List Tape :=
  match input with
  | [] => ulogCore payloadStartOne :: base
  | b :: bs =>
      input.reverse.map payloadTape ++ ulogCore payloadEnd ::
        List.replicate bs.length (ulogCore payloadDone) ++
          ulogCore payloadStartDone :: base

theorem reaches_emptyPayloadProbe (probe : Bool) (base : List Tape)
    (right : List Tape) :
    Reaches
      (.running (.fieldReturn .payloadLength)
        ⟨ulogCore payloadStartOne :: base, codeTape probe, right⟩)
      (.running .framePadding
        ⟨ulogCore payloadStartOne :: base, codeTape probe, right⟩) := by
  refine ⟨3, ?_⟩
  simp [run, fieldReturn_payload_step, payloadReturn_empty_step,
    payloadRestore_exhausted_step]

theorem reaches_payloadFolded (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (left tail : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map codeTape ++
              ulogCore codeEnd :: tail⟩)
      (.running .framePadding
        (match padding with
        | [] =>
            ⟨payloadFoldedLeft input (programMarkedLeft rules left),
              ulogCore codeEnd, tail⟩
        | b :: bs =>
            ⟨payloadFoldedLeft input (programMarkedLeft rules left),
              codeTape b, bs.map codeTape ++ ulogCore codeEnd :: tail⟩)) := by
  have hdecode := reaches_payloadLengthDecoded rules input padding left tail
  cases input with
  | nil =>
      cases padding with
      | nil =>
          exact reaches_trans hdecode
            (reaches_step (fieldReturn_payload_end_step _ tail))
      | cons p ps =>
          simpa [payloadFoldedLeft, atBits, List.append_assoc] using
            reaches_trans hdecode
              (reaches_emptyPayloadProbe p
                (programMarkedLeft rules left)
                (ps.map codeTape ++ ulogCore codeEnd :: tail))
  | cons b bs =>
      cases padding with
      | nil =>
          cases bs with
          | nil =>
              have h₁ := reaches_payloadFirstStart b (ulogCore codeEnd)
                (programMarkedLeft rules left) tail
              have h₂ := reaches_payloadExhausted (carry := false)
              have hall := reaches_trans hdecode
                (reaches_trans h₁
                  (reaches_step (fieldReturn_payload_end_step _ tail)))
              simpa [payloadFoldedLeft, atBits] using hall
          | cons c cs =>
              have hdecode' : Reaches
                  (.running .framePayloadLength
                    ⟨left, ulogCore pcMark,
                      (ULogBytecode.encodeProgram rules ++
                        ULogBytecode.encodePayload (b :: c :: cs) []).map
                          codeTape ++ ulogCore codeEnd :: tail⟩)
                  (.running (.fieldReturn .payloadLength)
                    ⟨ulogCore codeOne :: ulogCore codeZero ::
                        List.replicate cs.length (ulogCore codeZero) ++
                          ulogCore payloadStartZero ::
                            programMarkedLeft rules left,
                      codeTape b,
                      codeTape c :: cs.map codeTape ++
                        ulogCore codeEnd :: tail⟩) := by
                simpa [payloadLengthMarkedLeft, ULogBytecode.encodeNatField,
                  atBits, codeTape, List.replicate_succ,
                  List.append_assoc] using hdecode
              have hall := reaches_trans hdecode'
                (reaches_trans
                  (reaches_payloadFirstZero b (codeTape c) cs.length
                    (programMarkedLeft rules left)
                    (cs.map codeTape ++ ulogCore codeEnd :: tail))
                  (reaches_trans
                    (reaches_payloadFold c cs [b] 1
                      (programMarkedLeft rules left) (ulogCore codeEnd) tail)
                    (reaches_step (fieldReturn_payload_end_step _ tail))))
              have hnat : 1 + cs.length = cs.length + 1 := by omega
              rw [hnat] at hall
              simpa [payloadFoldedLeft, atBits, List.append_assoc] using hall
      | cons p ps =>
          let rest := ps.map codeTape ++ ulogCore codeEnd :: tail
          cases bs with
          | nil =>
              have hall := reaches_trans hdecode
                (reaches_trans
                  (reaches_payloadFirstStart b (codeTape p)
                    (programMarkedLeft rules left) rest)
                  (reaches_payloadExhausted p [b] 0
                    (programMarkedLeft rules left) rest))
              simpa [payloadFoldedLeft, atBits, rest] using hall
          | cons c cs =>
              have hdecode' : Reaches
                  (.running .framePayloadLength
                    ⟨left, ulogCore pcMark,
                      (ULogBytecode.encodeProgram rules ++
                        ULogBytecode.encodePayload (b :: c :: cs)
                          (p :: ps)).map codeTape ++ ulogCore codeEnd :: tail⟩)
                  (.running (.fieldReturn .payloadLength)
                    ⟨ulogCore codeOne :: ulogCore codeZero ::
                        List.replicate cs.length (ulogCore codeZero) ++
                          ulogCore payloadStartZero ::
                            programMarkedLeft rules left,
                      codeTape b,
                      codeTape c :: cs.map codeTape ++ codeTape p :: rest⟩) := by
                simpa [payloadLengthMarkedLeft, ULogBytecode.encodeNatField,
                  atBits, codeTape, rest, List.replicate_succ,
                  List.append_assoc] using hdecode
              have hall := reaches_trans hdecode'
                (reaches_trans
                  (reaches_payloadFirstZero b (codeTape c) cs.length
                    (programMarkedLeft rules left)
                    (cs.map codeTape ++ codeTape p :: rest))
                  (reaches_trans
                    (reaches_payloadFold c cs [b] 1
                      (programMarkedLeft rules left) (codeTape p) rest)
                    (reaches_payloadExhausted p ([b] ++ c :: cs)
                      (1 + cs.length)
                      (programMarkedLeft rules left) rest)))
              have hnat : 1 + cs.length = cs.length + 1 := by omega
              rw [hnat] at hall
              simpa [payloadFoldedLeft, atBits, rest, List.append_assoc]
                using hall

def beforeClockPadding (padding : List Bool) (left : List Tape)
    (tail : List Tape) : Zipper Tape :=
  match padding with
  | [] => ⟨left, ulogCore codeEnd, MStarConcreteAlphabet.work :: tail⟩
  | b :: bs => ⟨left, codeTape b,
      bs.map codeTape ++ ulogCore codeEnd ::
        MStarConcreteAlphabet.work :: tail⟩

def afterClockPadding (padding : List Bool) (left : List Tape)
    (tail : List Tape) : Zipper Tape :=
  ⟨List.replicate padding.length (ulogCore clockZero) ++ left,
    ulogCore codeEnd, MStarConcreteAlphabet.work :: tail⟩

theorem run_framePadding (padding : List Bool) (left : List Tape)
    (tail : List Tape) :
    run padding.length
      (.running .framePadding (beforeClockPadding padding left tail)) =
      .running .framePadding (afterClockPadding padding left tail) := by
  induction padding generalizing left with
  | nil => rfl
  | cons b padding ih =>
      rw [show (b :: padding).length = padding.length + 1 by simp, run]
      rw [show oneStep (.running .framePadding
          (beforeClockPadding (b :: padding) left tail)) =
          .running .framePadding
            (beforeClockPadding padding (ulogCore clockZero :: left) tail) by
        cases padding <;>
          simp [beforeClockPadding, framePadding_bit_step,
            List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running .framePadding)
      apply Zipper.ext <;>
        simp [afterClockPadding, List.replicate_succ', List.append_assoc]

def initializedPowerClock (padding : List Bool) (left : List Tape)
    (tail : List Tape) : Result :=
  .running .initializeState
    ⟨List.replicate padding.length (ulogCore clockZero) ++ left,
      ulogCore clockOne, ulogCore clockSep :: tail⟩

theorem reaches_initializedPowerClock (padding : List Bool)
    (left tail : List Tape) :
    Reaches
      (.running .framePadding (beforeClockPadding padding left tail))
      (initializedPowerClock padding left tail) := by
  have h₀ : Reaches
      (.running .framePadding (beforeClockPadding padding left tail))
      (.running .framePadding (afterClockPadding padding left tail)) :=
    ⟨padding.length, run_framePadding padding left tail⟩
  have h₁ : Reaches
      (.running .framePadding (afterClockPadding padding left tail))
      (.running .initializeClock
        ⟨ulogCore clockOne ::
            (List.replicate padding.length (ulogCore clockZero) ++ left),
          MStarConcreteAlphabet.work, tail⟩) := by
    apply reaches_step
    simpa [afterClockPadding] using
      framePadding_end_step
        (List.replicate padding.length (ulogCore clockZero) ++ left) tail
  have h₂ : Reaches
      (.running .initializeClock
        ⟨ulogCore clockOne ::
            (List.replicate padding.length (ulogCore clockZero) ++ left),
          MStarConcreteAlphabet.work, tail⟩)
      (initializedPowerClock padding left tail) := by
    apply reaches_step
    exact initializeClock_step _ tail
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def decodePowerClock : List Tape → Option ℕ
  | [] => none
  | x :: xs =>
      if x = ulogCore clockOne then
        match xs with
        | y :: _ => if y = ulogCore clockSep then some 1 else none
        | [] => none
      else if x = ulogCore clockZero then
        (decodePowerClock xs).map (2 * ·)
      else none

def decodeBinaryClock : List Tape → Option ℕ
  | [] => none
  | x :: xs =>
      if x = ulogCore clockSep then some 0
      else if x = ulogCore clockZero then
        (decodeBinaryClock xs).map (2 * ·)
      else if x = ulogCore clockOne then
        (decodeBinaryClock xs).map (fun n => 1 + 2 * n)
      else none

@[simp] theorem decodePowerClock_initialized (k : ℕ) (tail : List Tape) :
    decodePowerClock
      (List.replicate k (ulogCore clockZero) ++
        ulogCore clockOne :: ulogCore clockSep :: tail) = some (2 ^ k) := by
  induction k with
  | zero => simp [decodePowerClock]
  | succ k ih =>
      rw [List.replicate_succ]
      have hne : ulogCore clockZero ≠ ulogCore clockOne :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      simp [decodePowerClock, hne, ih, pow_succ, Nat.mul_comm]

@[simp] theorem decodeBinaryClock_power (k : ℕ) (tail : List Tape) :
    decodeBinaryClock
      (List.replicate k (ulogCore clockZero) ++
        ulogCore clockOne :: ulogCore clockSep :: tail) = some (2 ^ k) := by
  induction k with
  | zero =>
      have hsep : ulogCore clockOne ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      have hzero : ulogCore clockOne ≠ ulogCore clockZero :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      simp [decodeBinaryClock, hsep, hzero]
  | succ k ih =>
      rw [List.replicate_succ]
      have hne : ulogCore clockZero ≠ ulogCore clockOne :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      have hsep : ulogCore clockZero ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      simp [decodeBinaryClock, hne, hsep, ih, pow_succ, Nat.mul_comm]

@[simp] theorem decodeBinaryClock_power_pred (k : ℕ)
    (tail : List Tape) :
    decodeBinaryClock
      (List.replicate k (ulogCore clockOne) ++
        ulogCore clockZero :: ulogCore clockSep :: tail) =
      some (2 ^ k - 1) := by
  induction k with
  | zero => simp [decodeBinaryClock]
  | succ k ih =>
      rw [List.replicate_succ]
      have honeSep : ulogCore clockOne ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      have honeZero : ulogCore clockOne ≠ ulogCore clockZero :=
        ULogTapeDecoding.ulog_symbol_ne (by native_decide)
      simp [decodeBinaryClock, honeSep, honeZero, ih, pow_succ]
      have hp : 0 < 2 ^ k := by positivity
      omega

theorem reaches_payloadClockInitialized
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (left tail : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map codeTape ++
              ulogCore codeEnd :: MStarConcreteAlphabet.work :: tail⟩)
      (initializedPowerClock padding
        (payloadFoldedLeft input (programMarkedLeft rules left)) tail) := by
  have h₀ := reaches_payloadFolded rules input padding left
    (MStarConcreteAlphabet.work :: tail)
  have h₁ := reaches_initializedPowerClock padding
    (payloadFoldedLeft input (programMarkedLeft rules left)) tail
  cases padding <;>
    simpa [beforeClockPadding] using reaches_trans h₀ h₁

def stateFrame : List Tape :=
  [ulogCore stateZero, ulogCore stateZero, ulogCore stateOne,
    ulogCore stateSep]

theorem reaches_stateFrameWritten (padding : List Bool)
    (left tail : List Tape) :
    Reaches
      (initializedPowerClock padding left
        (List.replicate 4 MStarConcreteAlphabet.work ++ tail))
      (.running .seekSimHead
        ⟨ulogCore stateZero :: ulogCore stateZero :: ulogCore clockSep ::
            ulogCore clockOne ::
              List.replicate padding.length (ulogCore clockZero) ++ left,
          ulogCore stateOne, ulogCore stateSep :: tail⟩) := by
  refine ⟨6, ?_⟩
  simp [run, initializedPowerClock, initializeState_step,
    initStateCell_zero_step, initStateCell_one_step,
    initStateCell_two_step, initStateCell_three_step,
    initStateCell_four_step, List.replicate_succ,
    List.append_assoc]

def headSeekPath (padding input : List Bool) : List Tape :=
  [ulogCore stateOne, ulogCore stateZero, ulogCore stateZero,
    ulogCore clockSep, ulogCore clockOne] ++
      List.replicate padding.length (ulogCore clockZero) ++
        input.reverse.map payloadTape

def runtimeSuffix (padding : List Bool) (tail : List Tape) : List Tape :=
  List.replicate padding.length (ulogCore clockZero) ++
    [ulogCore clockOne, ulogCore clockSep, ulogCore stateZero,
      ulogCore stateZero, ulogCore stateOne, ulogCore stateSep] ++ tail

def initializationWorkspace (input : List Bool)
    (tail : List Tape) : List Tape :=
  match input with
  | [] => List.replicate 5 MStarConcreteAlphabet.work ++ tail
  | _ :: _ => List.replicate 4 MStarConcreteAlphabet.work ++ tail

def payloadRuntimeWorkspace (input : List Bool)
    (tail : List Tape) : List Tape :=
  MStarConcreteAlphabet.work :: initializationWorkspace input tail

theorem headSeekPath_pass (padding input : List Bool) (x : Tape)
    (hx : x ∈ headSeekPath padding input) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .seekSimHead ⟨y :: left, x, right⟩) =
      .running .seekSimHead ⟨left, y, x :: right⟩ := by
  simp [headSeekPath] at hx
  rcases hx with rfl | rfl | rfl | rfl | hclock | hx
  · exact seekSimHead_pass_stateOne left y right
  · exact seekSimHead_pass_stateZero left y right
  · exact seekSimHead_pass_clockSep left y right
  · exact seekSimHead_pass_clockOne left y right
  · have hm : padding ≠ [] ∧ x = ulogCore clockZero := by
      simpa only [List.mem_replicate] using hclock
    rw [hm.2]
    exact seekSimHead_pass_clockZero left y right
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact seekSimHead_pass_payload _ left y right

theorem headSeekPath_reverse (padding input : List Bool) :
    (headSeekPath padding input).reverse ++ [ulogCore stateSep] =
      input.map payloadTape ++ runtimeSuffix padding [] := by
  simp [headSeekPath, runtimeSuffix, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem headSeekPath_reverse_append (padding input : List Bool)
    (tail : List Tape) :
    (headSeekPath padding input).reverse ++ ulogCore stateSep :: tail =
      input.map payloadTape ++ runtimeSuffix padding tail := by
  have h := congrArg (fun xs : List Tape => xs ++ tail)
    (headSeekPath_reverse padding input)
  simpa [runtimeSuffix, List.append_assoc] using h

def initializedRuntime (padding input : List Bool) (base : List Tape)
    (tail : List Tape) : Result :=
  match input with
  | [] => .running .cycleStart
      ⟨ulogCore payloadStartOne :: base,
        ulogCore payloadHeadBlank, runtimeSuffix padding tail⟩
  | b :: bs => .running .cycleStart
      ⟨ulogCore payloadEnd ::
          List.replicate bs.length (ulogCore payloadDone) ++
            ulogCore payloadStartDone :: base,
        if b then ulogCore payloadHeadOne else ulogCore payloadHeadZero,
        bs.map payloadTape ++ runtimeSuffix padding tail⟩

def emptyInitBoundary (padding : List Bool) : Tape :=
  match padding with
  | [] => ulogCore clockOne
  | _ :: _ => ulogCore clockZero

def emptyInitShiftPrefix (padding : List Bool) : List Tape :=
  match padding with
  | [] =>
      [ulogCore clockSep, ulogCore stateZero, ulogCore stateZero,
        ulogCore stateOne]
  | _ :: ps =>
      List.replicate ps.length (ulogCore clockZero) ++
        [ulogCore clockOne, ulogCore clockSep, ulogCore stateZero,
          ulogCore stateZero, ulogCore stateOne]

theorem runtimeSuffix_emptyInit (padding : List Bool) (tail : List Tape) :
    runtimeSuffix padding (MStarConcreteAlphabet.work :: tail) =
      emptyInitBoundary padding :: emptyInitShiftPrefix padding ++
        ulogCore stateSep :: MStarConcreteAlphabet.work :: tail := by
  cases padding <;>
    simp [runtimeSuffix, emptyInitBoundary, emptyInitShiftPrefix,
      List.replicate_succ, List.append_assoc]

theorem runtimeSuffix_emptyInit_after (padding : List Bool)
    (tail : List Tape) :
    runtimeSuffix padding tail =
      emptyInitBoundary padding :: emptyInitShiftPrefix padding ++
        ulogCore stateSep :: tail := by
  cases padding <;>
    simp [runtimeSuffix, emptyInitBoundary, emptyInitShiftPrefix,
      List.replicate_succ, List.append_assoc]

theorem emptyInit_boundary (padding : List Bool) :
    emptyInitBoundary padding = ulogCore clockZero ∨
      emptyInitBoundary padding = ulogCore clockOne := by
  cases padding <;> simp [emptyInitBoundary]

theorem emptyInitShiftPrefix_allowed (padding : List Bool)
    (x : Tape) (hx : x ∈ emptyInitShiftPrefix padding) :
    x = ulogCore clockZero ∨ x = ulogCore clockOne ∨
      x = ulogCore clockSep ∨ x = ulogCore stateZero ∨
        x = ulogCore stateOne := by
  cases padding with
  | nil =>
      simp [emptyInitShiftPrefix] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | cons b bs =>
      simp only [emptyInitShiftPrefix, List.mem_append,
        List.mem_replicate, List.mem_cons, List.mem_singleton] at hx
      rcases hx with hz | rfl | rfl | rfl | rfl | hlast
      · exact Or.inl hz.2
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · rcases hlast with rfl | hnil
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · simp at hnil

theorem emptyInit_shift_safe (padding : List Bool) :
    ShiftRuntimeSafe
      (emptyInitShiftPrefix padding ++ [ulogCore stateSep]) := by
  intro x hx
  rcases List.mem_append.mp hx with hp | hs
  · rcases emptyInitShiftPrefix_allowed padding x hp with
      rfl | rfl | rfl | rfl | rfl <;> exact (work_ne_ulogCore _).symm
  · have heq : x = ulogCore stateSep := by simpa using hs
    rw [heq]
    exact (work_ne_ulogCore _).symm

theorem emptyInit_return_safe (padding : List Bool) :
    InitSeekReturnSafe
      ((emptyInitShiftPrefix padding).reverse ++
        [emptyInitBoundary padding]) := by
  intro x hx
  rcases List.mem_append.mp hx with hp | hb
  · have hp' : x ∈ emptyInitShiftPrefix padding := by simpa using hp
    rcases emptyInitShiftPrefix_allowed padding x hp' with
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have heq : x = emptyInitBoundary padding := by simpa using hb
    rw [heq]
    rcases emptyInit_boundary padding with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem reaches_initializedRuntime (padding input : List Bool)
    (base tail : List Tape) :
    Reaches
      (initializedPowerClock padding (payloadFoldedLeft input base)
        (initializationWorkspace input tail))
      (initializedRuntime padding input base tail) := by
  cases input with
  | nil =>
      have hframeRaw := reaches_stateFrameWritten padding
        (payloadFoldedLeft [] base) (MStarConcreteAlphabet.work :: tail)
      have hframe : Reaches
          (initializedPowerClock padding (payloadFoldedLeft [] base)
            (initializationWorkspace [] tail))
          (.running .seekSimHead
            (beforeLeftPath (headSeekPath padding []) base
              (ulogCore payloadStartOne)
              (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) := by
        simpa [payloadFoldedLeft, headSeekPath, beforeLeftPath,
          initializationWorkspace, List.replicate_succ,
          List.append_assoc] using hframeRaw
      have hrun : Reaches
          (.running .seekSimHead
            (beforeLeftPath (headSeekPath padding []) base
              (ulogCore payloadStartOne)
              (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
          (.running .seekSimHead
            (afterLeftPath (headSeekPath padding []) base
              (ulogCore payloadStartOne)
              (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) :=
        ⟨(headSeekPath padding []).length,
          run_left_path_of .seekSimHead (headSeekPath padding [])
            (headSeekPath_pass padding []) base
            (ulogCore payloadStartOne)
            (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)⟩
      have hend : Reaches
          (.running .seekSimHead
            (afterLeftPath (headSeekPath padding []) base
              (ulogCore payloadStartOne)
              (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
          (initializedRuntime padding [] base tail) := by
        rw [show afterLeftPath (headSeekPath padding []) base
            (ulogCore payloadStartOne)
            (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail) =
          ⟨base, ulogCore payloadStartOne,
            (headSeekPath padding []).reverse ++
              ulogCore stateSep :: MStarConcreteAlphabet.work :: tail⟩ by rfl]
        rw [headSeekPath_reverse_append]
        rw [runtimeSuffix_emptyInit]
        have h₀ := reaches_step
          (seekSimHead_empty_step base (emptyInitBoundary padding)
            (emptyInitShiftPrefix padding ++
              ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))
        have hshift := reaches_initShiftRuntimeRight_cycle
          (emptyInitBoundary padding) (emptyInitShiftPrefix padding)
          (ulogCore stateSep) (emptyInit_shift_safe padding)
          (emptyInit_return_safe padding)
          (ulogCore payloadStartOne :: base)
          (ulogCore payloadHeadBlank) (by native_decide) tail
        have h₁' : Reaches
            (.running .readHead
              ⟨ulogCore payloadStartOne :: base,
                emptyInitBoundary padding,
                emptyInitShiftPrefix padding ++
                  ulogCore stateSep :: MStarConcreteAlphabet.work :: tail⟩)
            (.running (.shiftRuntime
              (.initRight (emptyInitBoundary padding)))
              (beforeRightPath
                (emptyInitShiftPrefix padding ++ [ulogCore stateSep])
                (ulogCore payloadHeadBlank ::
                  ulogCore payloadStartOne :: base)
                MStarConcreteAlphabet.work tail)) := by
          apply reaches_step
          cases hp : emptyInitShiftPrefix padding with
          | nil =>
              simpa [beforeRightPath, hp] using
                (readHead_empty_boundary (emptyInitBoundary padding)
                  (emptyInit_boundary padding) base (ulogCore stateSep)
                  (MStarConcreteAlphabet.work :: tail))
          | cons x xs =>
              simpa [beforeRightPath, hp, List.append_assoc] using
                (readHead_empty_boundary (emptyInitBoundary padding)
                  (emptyInit_boundary padding) base x
                  (xs ++ ulogCore stateSep ::
                    MStarConcreteAlphabet.work :: tail))
        have hall := reaches_trans h₀ (reaches_trans h₁' hshift)
        rw [← runtimeSuffix_emptyInit_after padding tail] at hall
        simpa [initializedRuntime] using hall
      have hall := reaches_trans hframe (reaches_trans hrun hend)
      simpa [payloadFoldedLeft, headSeekPath, beforeLeftPath,
        initializationWorkspace, List.append_assoc] using hall

  | cons b bs =>
      have hframeRaw := reaches_stateFrameWritten padding
        (payloadFoldedLeft (b :: bs) base) tail
      have hframe : Reaches
          (initializedPowerClock padding (payloadFoldedLeft (b :: bs) base)
            (List.replicate 4 MStarConcreteAlphabet.work ++ tail))
          (.running .seekSimHead
            (beforeLeftPath (headSeekPath padding (b :: bs))
              (List.replicate bs.length (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base)
              (ulogCore payloadEnd) (ulogCore stateSep :: tail))) := by
        simpa [payloadFoldedLeft, headSeekPath, beforeLeftPath,
          List.append_assoc] using hframeRaw
      have hrun : Reaches
          (.running .seekSimHead
            (beforeLeftPath (headSeekPath padding (b :: bs))
              (List.replicate bs.length (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base)
              (ulogCore payloadEnd) (ulogCore stateSep :: tail)))
          (.running .seekSimHead
            (afterLeftPath (headSeekPath padding (b :: bs))
              (List.replicate bs.length (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base)
              (ulogCore payloadEnd) (ulogCore stateSep :: tail))) :=
        ⟨(headSeekPath padding (b :: bs)).length,
          run_left_path_of .seekSimHead (headSeekPath padding (b :: bs))
            (headSeekPath_pass padding (b :: bs))
            (List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base)
            (ulogCore payloadEnd) (ulogCore stateSep :: tail)⟩
      have htoHead : Reaches
          (.running .seekSimHead
            (afterLeftPath (headSeekPath padding (b :: bs))
              (List.replicate bs.length (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base)
              (ulogCore payloadEnd) (ulogCore stateSep :: tail)))
          (.running .readHead
            ⟨ulogCore payloadEnd ::
                (List.replicate bs.length (ulogCore payloadDone) ++
                  ulogCore payloadStartDone :: base),
              payloadTape b,
              bs.map payloadTape ++ runtimeSuffix padding tail⟩) := by
        apply reaches_step
        rw [show afterLeftPath (headSeekPath padding (b :: bs))
            (List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base)
            (ulogCore payloadEnd) (ulogCore stateSep :: tail) =
          ⟨List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base,
            ulogCore payloadEnd,
            (headSeekPath padding (b :: bs)).reverse ++
              ulogCore stateSep :: tail⟩ by rfl]
        rw [headSeekPath_reverse_append]
        simpa [runtimeSuffix, List.append_assoc] using
          (seekSimHead_payloadEnd_step
            (List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadStartDone :: base)
            (payloadTape b)
            (bs.map payloadTape ++ runtimeSuffix padding tail))
      have hmark : Reaches
          (.running .readHead
            ⟨ulogCore payloadEnd ::
                (List.replicate bs.length (ulogCore payloadDone) ++
                  ulogCore payloadStartDone :: base),
              payloadTape b,
              bs.map payloadTape ++ runtimeSuffix padding tail⟩)
          (initializedRuntime padding (b :: bs) base tail) := by
        apply reaches_step
        simpa [initializedRuntime] using
          (readHead_step b
            (ulogCore payloadEnd ::
              (List.replicate bs.length (ulogCore payloadDone) ++
                ulogCore payloadStartDone :: base))
            (bs.map payloadTape ++ runtimeSuffix padding tail))
      have hall := reaches_trans hframe
        (reaches_trans hrun (reaches_trans htoHead hmark))
      simpa [payloadFoldedLeft, headSeekPath, beforeLeftPath,
        initializationWorkspace, List.append_assoc] using hall

theorem reaches_payloadRuntimeInitialized
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (left tail : List Tape) :
    Reaches
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map codeTape ++
              ulogCore codeEnd :: payloadRuntimeWorkspace input tail⟩)
      (initializedRuntime padding input (programMarkedLeft rules left) tail) := by
  have hclock := reaches_payloadClockInitialized rules input padding left
    (initializationWorkspace input tail)
  have hruntime := reaches_initializedRuntime padding input
    (programMarkedLeft rules left) tail
  have hall := reaches_trans hclock hruntime
  simpa [payloadRuntimeWorkspace, List.append_assoc] using hall

def beforeConsumeZeros (n : ℕ) (left : List Tape)
    (suffix : List Tape) : Zipper Tape :=
  match n with
  | 0 => ⟨left, ulogCore clockOne, suffix⟩
  | k + 1 => ⟨left, ulogCore clockZero,
      List.replicate k (ulogCore clockZero) ++
        ulogCore clockOne :: suffix⟩

def afterConsumeZeros (n : ℕ) (left : List Tape)
    (suffix : List Tape) : Zipper Tape :=
  ⟨List.replicate n (ulogCore clockOne) ++ left,
    ulogCore clockOne, suffix⟩

theorem run_clockConsume_zeros (n : ℕ) (left suffix : List Tape) :
    run n (.running .clockConsume (beforeConsumeZeros n left suffix)) =
      .running .clockConsume (afterConsumeZeros n left suffix) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run]
      rw [show oneStep (.running .clockConsume
          (beforeConsumeZeros (n + 1) left suffix)) =
          .running .clockConsume
            (beforeConsumeZeros n (ulogCore clockOne :: left) suffix) by
        cases n <;>
          simp [beforeConsumeZeros, clockConsume_zero_step,
            List.replicate_succ, List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running .clockConsume)
      apply Zipper.ext <;>
        simp [afterConsumeZeros, List.replicate_succ', List.append_assoc]

def clockReturnPath (k : ℕ) (tape : List Bool) : List Tape :=
  List.replicate k (ulogCore clockOne) ++ tape.reverse.map payloadTape

theorem clockReturnPath_pass (k : ℕ) (tape : List Bool) (x : Tape)
    (hx : x ∈ clockReturnPath k tape) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .clockReturn ⟨y :: left, x, right⟩) =
      .running .clockReturn ⟨left, y, x :: right⟩ := by
  simp [clockReturnPath] at hx
  rcases hx with hclock | htape
  · have hm : k ≠ 0 ∧ x = ulogCore clockOne := by
      simpa only [List.mem_replicate] using hclock
    rw [hm.2]
    exact clockReturn_clock_step true left y right
  · rcases htape with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact clockReturn_payload_step _ left y right

theorem clockReturnPath_reverse (k : ℕ) (tape : List Bool) :
    (clockReturnPath k tape).reverse =
      tape.map payloadTape ++ List.replicate k (ulogCore clockOne) := by
  simp [clockReturnPath, List.reverse_append, List.map_reverse,
    List.append_assoc]

theorem clockSeek_one_over_path (path : List Tape) (left : List Tape)
    (head : Tape) (suffix : List Tape) :
    oneStep (.running .clockSeek
      ⟨path ++ head :: left, ulogCore clockOne, suffix⟩) =
      .running .clockReturn
        (beforeLeftPath path left head (ulogCore clockZero :: suffix)) := by
  cases path with
  | nil => exact clockSeek_one_step left head suffix
  | cons x xs =>
      simpa [beforeLeftPath, List.append_assoc] using
        (clockSeek_one_step (xs ++ head :: left) x suffix)

theorem clockConsume_one_over_path (path : List Tape) (left : List Tape)
    (head : Tape) (suffix : List Tape) :
    oneStep (.running .clockConsume
      ⟨path ++ head :: left, ulogCore clockOne, suffix⟩) =
      .running .clockReturn
        (beforeLeftPath path left head (ulogCore clockZero :: suffix)) := by
  cases path with
  | nil => exact clockConsume_one_step left head suffix
  | cons x xs =>
      simpa [beforeLeftPath, List.append_assoc] using
        (clockConsume_one_step (xs ++ head :: left) x suffix)

theorem reaches_clockDecrementPower (head : Tape)
    (hhead : choiceHead head = true) (k : ℕ) (tape : List Bool)
    (left suffix : List Tape) :
    Reaches
      (.running .cycleStart
        ⟨left, head,
          tape.map payloadTape ++
            List.replicate k (ulogCore clockZero) ++
              ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head,
          tape.map payloadTape ++
            List.replicate k (ulogCore clockOne) ++
              ulogCore clockZero :: suffix⟩) := by
  let payloadPath := tape.map payloadTape
  let firstClock := if k = 0 then ulogCore clockOne else ulogCore clockZero
  let clockTail := match k with
    | 0 => suffix
    | n + 1 => List.replicate n (ulogCore clockZero) ++
        ulogCore clockOne :: suffix
  have hcycle : Reaches
      (.running .cycleStart
        ⟨left, head, payloadPath ++ firstClock :: clockTail⟩)
      (.running .clockSeek
        (beforeRightPath payloadPath (head :: left) firstClock clockTail)) := by
    apply reaches_step
    cases tape <;> cases k <;>
      simp [payloadPath, firstClock, clockTail, beforeRightPath,
        cycleStart_head_step head hhead, List.replicate_succ,
        List.append_assoc]
  have hscan : Reaches
      (.running .clockSeek
        (beforeRightPath payloadPath (head :: left) firstClock clockTail))
      (.running .clockSeek
        (afterRightPath payloadPath (head :: left) firstClock clockTail)) := by
    exact ⟨payloadPath.length,
      run_right_path_of .clockSeek payloadPath (by
        intro x hx l y r
        rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
        exact clockSeek_payload_step b l y r)
      (head :: left) firstClock clockTail⟩
  have hdec : Reaches
      (.running .clockSeek
        (afterRightPath payloadPath (head :: left) firstClock clockTail))
      (.running .clockReturn
        (beforeLeftPath (clockReturnPath k tape) left head
          (ulogCore clockZero :: suffix))) := by
    cases k with
    | zero =>
        apply reaches_step
        simpa [payloadPath, firstClock, clockTail, afterRightPath,
          clockReturnPath, List.map_reverse, List.append_assoc] using
          (clockSeek_one_over_path payloadPath.reverse left head suffix)
    | succ k =>
        have h₀ : Reaches
            (.running .clockSeek
              (afterRightPath payloadPath (head :: left) firstClock clockTail))
            (.running .clockConsume
              (beforeConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix)) := by
          apply reaches_step
          cases k <;>
            simp [payloadPath, firstClock, clockTail, afterRightPath,
              beforeConsumeZeros, clockSeek_zero_step,
              List.replicate_succ, List.append_assoc]
        have h₁ : Reaches
            (.running .clockConsume
              (beforeConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix))
            (.running .clockConsume
              (afterConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix)) :=
          ⟨k, run_clockConsume_zeros k _ _⟩
        have h₂ : Reaches
            (.running .clockConsume
              (afterConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix))
            (.running .clockReturn
              (beforeLeftPath (clockReturnPath (k + 1) tape) left head
                (ulogCore clockZero :: suffix))) := by
          apply reaches_step
          simpa [payloadPath, afterConsumeZeros, clockReturnPath,
            List.map_reverse, List.replicate_succ',
            List.append_assoc] using
            (clockConsume_one_over_path
              (clockReturnPath (k + 1) tape) left head suffix)
        exact reaches_trans h₀ (reaches_trans h₁ h₂)
  have hreturn : Reaches
      (.running .clockReturn
        (beforeLeftPath (clockReturnPath k tape) left head
          (ulogCore clockZero :: suffix)))
      (.running .clockReturn
        (afterLeftPath (clockReturnPath k tape) left head
          (ulogCore clockZero :: suffix))) :=
    ⟨(clockReturnPath k tape).length,
      run_left_path_of .clockReturn (clockReturnPath k tape)
        (clockReturnPath_pass k tape) left head
        (ulogCore clockZero :: suffix)⟩
  have hheadReturn : Reaches
      (.running .clockReturn
        (afterLeftPath (clockReturnPath k tape) left head
          (ulogCore clockZero :: suffix)))
      (.running .chooseSlot
        ⟨left, head,
          tape.map payloadTape ++
            List.replicate k (ulogCore clockOne) ++
              ulogCore clockZero :: suffix⟩) := by
    apply reaches_step
    simpa [afterLeftPath, clockReturnPath_reverse, List.append_assoc] using
      clockReturn_head_step head hhead left
        (tape.map payloadTape ++ List.replicate k (ulogCore clockOne) ++
          ulogCore clockZero :: suffix)
  have hall := reaches_trans hcycle (reaches_trans hscan
    (reaches_trans hdec (reaches_trans hreturn hheadReturn)))
  cases k <;>
    simpa [payloadPath, firstClock, clockTail, List.replicate_succ,
      List.append_assoc] using hall

def payloadProgramPrefix (input : List Bool) : List Tape :=
  match input with
  | [] => [ulogCore payloadStartOne]
  | _ :: bs =>
      ulogCore payloadEnd ::
        List.replicate bs.length (ulogCore payloadDone) ++
          [ulogCore payloadStartDone]

def ruleReturnPath (rules : List ULogBytecode.RuleCode)
    (input : List Bool) : List Tape :=
  payloadProgramPrefix input ++
    ((ULogBytecode.encodeRules rules).map codeTape).reverse ++
      codeTape true :: List.replicate rules.length (ulogCore pcDone)

theorem ruleReturnPath_ne_nil (rules : List ULogBytecode.RuleCode)
    (input : List Bool) : ruleReturnPath rules input ≠ [] := by
  simp [ruleReturnPath]

theorem payloadProgramPrefix_mem {input : List Bool} {x : Tape}
    (hx : x ∈ payloadProgramPrefix input) :
    x = ulogCore payloadEnd ∨ x = ulogCore payloadDone ∨
      x = ulogCore payloadStartDone ∨ x = ulogCore payloadStartOne := by
  cases input with
  | nil => simp [payloadProgramPrefix] at hx; exact Or.inr (Or.inr (Or.inr hx))
  | cons b bs =>
      simp [payloadProgramPrefix] at hx
      rcases hx with rfl | ⟨-, rfl⟩ | rfl <;> simp

theorem encodeRules_tape_mem {rules : List ULogBytecode.RuleCode}
    {x : Tape} (hx : x ∈ (ULogBytecode.encodeRules rules).map codeTape) :
    x = codeTape false ∨ x = codeTape true := by
  rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
  cases b <;> simp

theorem ruleReturnPath_pass (slot : Bool)
    (rules : List ULogBytecode.RuleCode) (input : List Bool)
    (x : Tape) (hx : x ∈ ruleReturnPath rules input)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.ruleSeekChoice slot) ⟨y :: left, x, right⟩) =
      .running (.ruleSeekChoice slot) ⟨left, y, x :: right⟩ := by
  apply ruleSeekChoice_pass slot x
  unfold ruleReturnPath at hx
  rcases List.mem_append.mp hx with hpm | hx
  rcases List.mem_append.mp hpm with hp | hcode
  · rcases payloadProgramPrefix_mem hp with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
  · have hm : x ∈ (ULogBytecode.encodeRules rules).map codeTape := by
      simpa only [List.mem_reverse] using hcode
    rcases encodeRules_tape_mem hm with h | h
    · simp [h]
    · simp [h]
  · simp only [List.mem_cons, List.mem_replicate] at hx
    rcases hx with h | h
    · simp [h]
    · simp [h.2]

theorem ruleReturnPath_reverse (rules : List ULogBytecode.RuleCode)
    (input : List Bool) :
    (ruleReturnPath rules input).reverse =
      List.replicate rules.length (ulogCore pcDone) ++
        codeTape true ::
          (ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse := by
  simp [ruleReturnPath, List.reverse_append, List.map_reverse,
    List.append_assoc]

def ruleSourceStarted (slot : Bool)
    (rules : List ULogBytecode.RuleCode) (input : List Bool)
    (left : List Tape) (head : Tape) (right : List Tape) : Result :=
  match ULogBytecode.encodeRules rules with
  | [] => .rejected
  | b :: bs =>
      .running (.fieldCompare .source slot)
        ⟨ulogCore sourceBoundary ::
            List.replicate rules.length (ulogCore pcDone) ++
              ulogCore pcMark :: left,
          codeTape b,
          bs.map codeTape ++ (payloadProgramPrefix input).reverse ++
            head :: right⟩

theorem reaches_ruleSourceStarted (slot : Bool)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (left : List Tape) (head : Tape)
    (right : List Tape) :
    Reaches
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath (ruleReturnPath rules input) left
          (ulogCore pcMark) (head :: right)))
      (ruleSourceStarted slot rules input left head right) := by
  let path := ruleReturnPath rules input
  have h₀ : Reaches
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath path left (ulogCore pcMark) (head :: right)))
      (.running (.ruleSeekChoice slot)
        (afterLeftPath path left (ulogCore pcMark) (head :: right))) :=
    ⟨path.length, run_left_path_of (.ruleSeekChoice slot) path
      (ruleReturnPath_pass slot rules input) left
      (ulogCore pcMark) (head :: right)⟩
  have h₁ : Reaches
      (.running (.ruleSeekChoice slot)
        (afterLeftPath path left (ulogCore pcMark) (head :: right)))
      (.running (.ruleCountSeek slot)
        (beforeRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ head :: right))) := by
    apply reaches_step
    cases rules with
    | nil => exact (hrules rfl).elim
    | cons r rs =>
        simp [path, afterLeftPath, beforeRightPath,
          ruleReturnPath_reverse, ruleSeekChoice_mark,
          codeTape, List.replicate_succ, List.append_assoc]
  have h₂ : Reaches
      (.running (.ruleCountSeek slot)
        (beforeRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ head :: right)))
      (.running (.ruleCountSeek slot)
        (afterRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ head :: right))) := by
    refine ⟨(List.replicate rules.length (ulogCore pcDone)).length, ?_⟩
    exact run_right_path_of (.ruleCountSeek slot)
        (List.replicate rules.length (ulogCore pcDone)) (by
          intro x hx l y r
          have hm : rules.length ≠ 0 ∧ x = ulogCore pcDone := by
            simpa only [List.mem_replicate] using hx
          rw [hm.2]
          exact ruleCountSeek_done slot l y r)
        (ulogCore pcMark :: left) (ulogCore codeOne)
        ((ULogBytecode.encodeRules rules).map codeTape ++
          (payloadProgramPrefix input).reverse ++ head :: right)
  have henc : ULogBytecode.encodeRules rules ≠ [] :=
    encodeRules_ne_nil hrules
  have h₃ : Reaches
      (.running (.ruleCountSeek slot)
        (afterRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: left) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ head :: right)))
      (ruleSourceStarted slot rules input left head right) := by
    cases he : ULogBytecode.encodeRules rules with
    | nil => exact (henc he).elim
    | cons b bs =>
        apply reaches_step
        simpa [ruleSourceStarted, afterRightPath, he,
          List.replicate_succ', List.append_assoc] using
          (ruleCountSeek_end slot
            (List.replicate rules.length (ulogCore pcDone) ++
              ulogCore pcMark :: left)
            (codeTape b)
            (bs.map codeTape ++ (payloadProgramPrefix input).reverse ++
              head :: right))
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

theorem chooseSlot_zero_starts_ruleSeek (rules : List ULogBytecode.RuleCode)
    (input : List Bool) (left : List Tape) (head : Tape)
    (hhead : choiceHead head = true) (right : List Tape) :
    oneStepAt 0
        (.running .chooseSlot
          ⟨ruleReturnPath rules input ++ ulogCore pcMark :: left,
            head, right⟩) =
      .running (.ruleSeekChoice false)
        (beforeLeftPath (ruleReturnPath rules input) left
          (ulogCore pcMark) (head :: right)) := by
  have hp := ruleReturnPath_ne_nil rules input
  cases he : ruleReturnPath rules input with
  | nil => exact (hp he).elim
  | cons x xs =>
      simpa [beforeLeftPath, he] using
        (oneStepAt_chooseSlot_zero head hhead
          (xs ++ ulogCore pcMark :: left) x right)

theorem chooseSlot_one_starts_ruleSeek (rules : List ULogBytecode.RuleCode)
    (input : List Bool) (left : List Tape) (head : Tape)
    (hhead : choiceHead head = true) (right : List Tape) :
    oneStepAt 1
        (.running .chooseSlot
          ⟨ruleReturnPath rules input ++ ulogCore pcMark :: left,
            head, right⟩) =
      .running (.ruleSeekChoice true)
        (beforeLeftPath (ruleReturnPath rules input) left
          (ulogCore pcMark) (head :: right)) := by
  have hp := ruleReturnPath_ne_nil rules input
  cases he : ruleReturnPath rules input with
  | nil => exact (hp he).elim
  | cons x xs =>
      simpa [beforeLeftPath, he] using
        (oneStepAt_chooseSlot_one head hhead
          (xs ++ ulogCore pcMark :: left) x right)

theorem chooseSlot_zero_reaches_ruleSource
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (left : List Tape) (head : Tape)
    (hhead : choiceHead head = true) (right : List Tape) :
    ∃ branchStart,
      oneStepAt 0
          (.running .chooseSlot
            ⟨ruleReturnPath rules input ++ ulogCore pcMark :: left,
              head, right⟩) = branchStart ∧
        Reaches branchStart
          (ruleSourceStarted false rules input left head right) := by
  refine ⟨.running (.ruleSeekChoice false)
      (beforeLeftPath (ruleReturnPath rules input) left
        (ulogCore pcMark) (head :: right)), ?_, ?_⟩
  · exact chooseSlot_zero_starts_ruleSeek rules input left head hhead right
  · exact reaches_ruleSourceStarted false rules hrules input left head right

theorem chooseSlot_one_reaches_ruleSource
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (left : List Tape) (head : Tape)
    (hhead : choiceHead head = true) (right : List Tape) :
    ∃ branchStart,
      oneStepAt 1
          (.running .chooseSlot
            ⟨ruleReturnPath rules input ++ ulogCore pcMark :: left,
              head, right⟩) = branchStart ∧
        Reaches branchStart
          (ruleSourceStarted true rules input left head right) := by
  refine ⟨.running (.ruleSeekChoice true)
      (beforeLeftPath (ruleReturnPath rules input) left
        (ulogCore pcMark) (head :: right)), ?_, ?_⟩
  · exact chooseSlot_one_starts_ruleSeek rules input left head hhead right
  · exact reaches_ruleSourceStarted true rules hrules input left head right

def sourceCompareScanPath (remaining : ℕ) (corridor : List Tape)
    (done : ℕ) : List Tape :=
  List.replicate remaining (ulogCore codeZero) ++
    ulogCore codeOne :: corridor ++
      List.replicate done (ulogCore stateMark)

def SourceCompareCorridorSafe (corridor : List Tape) : Prop :=
  ∀ x ∈ corridor,
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
      x ≠ MStarConcreteAlphabet.work ∧ x ≠ ulogCore sourceMark ∧
        x ≠ ulogCore pcMark ∧ x ≠ ulogCore stateMark ∧
          x ≠ ulogCore sourceBoundary ∧
            x ≠ ulogCore sourceBoundaryZero ∧
              x ≠ ulogCore sourceBoundaryOne

theorem sourceCompareScanPath_seek_safe {remaining done : ℕ}
    {corridor : List Tape} (hcorridor : SourceCompareCorridorSafe corridor)
    {x : Tape} (hx : x ∈ sourceCompareScanPath remaining corridor done) :
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
      x ≠ MStarConcreteAlphabet.work := by
  unfold sourceCompareScanPath at hx
  rcases List.mem_append.mp hx with hpre | hdone
  · rcases List.mem_append.mp hpre with hzero | honeCorridor
    · have hm : remaining ≠ 0 ∧ x = ulogCore codeZero := by
        simpa only [List.mem_replicate] using hzero
      rw [hm.2]
      decide
    · rcases List.mem_cons.mp honeCorridor with hone | hc
      · rw [hone]
        decide
      · have h := hcorridor x hc
        exact ⟨h.1, h.2.1, h.2.2.1⟩
  · have hm : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hdone
    rw [hm.2]
    decide

theorem sourceCompareScanPath_return_safe {remaining done : ℕ}
    {corridor : List Tape} (hcorridor : SourceCompareCorridorSafe corridor)
    {x : Tape} (hx : x ∈ sourceCompareScanPath remaining corridor done) :
    x ≠ ulogCore sourceMark ∧ x ≠ ulogCore pcMark := by
  unfold sourceCompareScanPath at hx
  rcases List.mem_append.mp hx with hpre | hdone
  · rcases List.mem_append.mp hpre with hzero | honeCorridor
    · have hm : remaining ≠ 0 ∧ x = ulogCore codeZero := by
        simpa only [List.mem_replicate] using hzero
      rw [hm.2]
      decide
    · rcases List.mem_cons.mp honeCorridor with hone | hc
      · rw [hone]
        decide
      · have h := hcorridor x hc
        exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
  · have hm : done ≠ 0 ∧ x = ulogCore stateMark := by
      simpa only [List.mem_replicate] using hdone
    rw [hm.2]
    decide

theorem sourceCompareScanPath_ne_nil (remaining : ℕ)
    (corridor : List Tape) (done : ℕ) :
    sourceCompareScanPath remaining corridor done ≠ [] := by
  simp [sourceCompareScanPath]

theorem reaches_sourceCompareRound (slot : Bool) (remaining done : ℕ)
    (corridor : List Tape)
    (hseek : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
        x ≠ MStarConcreteAlphabet.work)
    (hreturn : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore sourceMark ∧ x ≠ ulogCore pcMark)
    (left stateRest : List Tape) :
    Reaches
      (.running (.fieldCompare .source slot)
        ⟨left, ulogCore codeZero,
          sourceCompareScanPath remaining corridor done ++
            ulogCore stateZero :: stateRest⟩)
      (.running (.fieldCompare .source slot)
        (beforeRightPath (sourceCompareScanPath remaining corridor done)
          (ulogCore sourceMark :: left) (ulogCore stateMark) stateRest)) := by
  let path := sourceCompareScanPath remaining corridor done
  have hp : path ≠ [] := sourceCompareScanPath_ne_nil remaining corridor done
  have h₀ : Reaches
      (.running (.fieldCompare .source slot)
        ⟨left, ulogCore codeZero, path ++ ulogCore stateZero :: stateRest⟩)
      (.running (.compareSeekState slot)
        (beforeRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest)) := by
    apply reaches_step
    cases he : path with
    | nil => exact (hp he).elim
    | cons x xs =>
        simpa [beforeRightPath, he] using
          (fieldCompare_source_zero slot left x
            (xs ++ ulogCore stateZero :: stateRest))
  have h₁ : Reaches
      (.running (.compareSeekState slot)
        (beforeRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.compareSeekState slot)
        (afterRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest)) := by
    exact ⟨path.length,
      run_right_path_of (.compareSeekState slot) path (by
        intro x hx l y r
        have h := hseek x (by simpa [path] using hx)
        exact compareSeekState_pass slot x h.1 h.2.1 h.2.2 l y r)
      (ulogCore sourceMark :: left) (ulogCore stateZero) stateRest⟩
  have h₂ : Reaches
      (.running (.compareSeekState slot)
        (afterRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.compareReturnSource slot)
        (beforeLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest))) := by
    apply reaches_step
    have hpr : path.reverse ≠ [] := by simpa using hp
    cases he : path.reverse with
    | nil => exact (hpr he).elim
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, he,
          List.append_assoc] using
          (compareSeekState_zero slot (xs ++ ulogCore sourceMark :: left)
            x stateRest)
  have h₃ : Reaches
      (.running (.compareReturnSource slot)
        (beforeLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest)))
      (.running (.compareReturnSource slot)
        (afterLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest))) := by
    refine ⟨path.length, ?_⟩
    simpa using
      (run_left_path_of (.compareReturnSource slot) path.reverse (by
          intro x hx l y r
          have hx' : x ∈ path := by simpa using hx
          have h := hreturn x (by simpa [path] using hx')
          exact compareReturnSource_pass slot x h.1 h.2 l y r)
        left (ulogCore sourceMark) (ulogCore stateMark :: stateRest))
  have h₄ : Reaches
      (.running (.compareReturnSource slot)
        (afterLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest)))
      (.running (.fieldCompare .source slot)
        (beforeRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateMark) stateRest)) := by
    apply reaches_step
    cases he : path with
    | nil => exact (hp he).elim
    | cons x xs =>
        simpa [afterLeftPath, beforeRightPath, he,
          List.append_assoc] using
          (compareReturnSource_mark slot left x
            (xs ++ ulogCore stateMark :: stateRest))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ h₄)))

def sourceCompareStart (slot : Bool) (remaining done : ℕ)
    (corridor left suffix : List Tape) : Result :=
  match remaining with
  | 0 => .running (.fieldCompare .source slot)
      ⟨left, ulogCore codeOne,
        corridor ++ List.replicate done (ulogCore stateMark) ++
          ulogCore stateOne :: suffix⟩
  | n + 1 => .running (.fieldCompare .source slot)
      ⟨left, ulogCore codeZero,
        sourceCompareScanPath n corridor done ++
          ulogCore stateZero ::
            List.replicate n (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩

def sourceCompareAllMarked (slot : Bool) (remaining done : ℕ)
    (corridor left suffix : List Tape) : Result :=
  .running (.fieldCompare .source slot)
    ⟨List.replicate remaining (ulogCore sourceMark) ++ left,
      ulogCore codeOne,
      corridor ++
        List.replicate (done + remaining) (ulogCore stateMark) ++
          ulogCore stateOne :: suffix⟩

theorem reaches_sourceCompareZeros (slot : Bool) (remaining done : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) :
    Reaches (sourceCompareStart slot remaining done corridor left suffix)
      (sourceCompareAllMarked slot remaining done corridor left suffix) := by
  induction remaining generalizing done left with
  | zero =>
      apply reaches_refl
  | succ remaining ih =>
      have hround := reaches_sourceCompareRound slot remaining done corridor
        (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
        (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
        left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      have htail := ih (done + 1) (ulogCore sourceMark :: left)
      have htail' : Reaches
          (.running (.fieldCompare .source slot)
            (beforeRightPath (sourceCompareScanPath remaining corridor done)
              (ulogCore sourceMark :: left) (ulogCore stateMark)
              (List.replicate remaining (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)))
          (sourceCompareAllMarked slot remaining (done + 1) corridor
            (ulogCore sourceMark :: left) suffix) := by
        cases remaining <;>
          simpa [sourceCompareStart, sourceCompareScanPath, beforeRightPath,
            List.replicate_succ, List.replicate_succ',
            List.append_assoc] using htail
      have hall := reaches_trans hround htail'
      simpa [sourceCompareStart, sourceCompareAllMarked,
        sourceCompareScanPath, List.replicate_succ,
        List.replicate_succ', List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hall

def restoreSourceCell (x : Tape) : Tape :=
  if x = ulogCore stateMark then ulogCore stateZero
  else if x = ulogCore sourceMark then ulogCore codeZero
  else x

def restoreMismatchCell (x : Tape) : Tape :=
  if x = ulogCore stateMark then ulogCore stateZero
  else if x = ulogCore sourceMark then ulogCore codeZero
  else if x = ulogCore readBoundary then ulogCore codeOne
  else x

def MismatchRestorePathSafe (path : List Tape) : Prop :=
  ∀ x ∈ path,
    x ≠ ulogCore sourceBoundary ∧
      x ≠ ulogCore sourceBoundaryZero ∧
        x ≠ ulogCore sourceBoundaryOne ∧ x ≠ ulogCore pcMark

theorem restoreRule_step (slot : Bool) (x : Tape)
    (hboundary : x ≠ ulogCore sourceBoundary)
    (hboundaryZero : x ≠ ulogCore sourceBoundaryZero)
    (hboundaryOne : x ≠ ulogCore sourceBoundaryOne)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.restoreRule slot) ⟨y :: left, x, right⟩) =
      .running (.restoreRule slot)
        ⟨left, y, restoreMismatchCell x :: right⟩ := by
  by_cases hs : x = ulogCore stateMark
  · subst x
    simpa [restoreMismatchCell] using restoreRule_stateMark slot left y right
  · by_cases hm : x = ulogCore sourceMark
    · subst x
      have hne : ulogCore sourceMark ≠ ulogCore stateMark :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      simpa [restoreMismatchCell, hne] using
        restoreRule_sourceMark slot left y right
    · by_cases hr : x = ulogCore readBoundary
      · subst x
        have hstateRead : ulogCore readBoundary ≠ ulogCore stateMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        have hsourceRead : ulogCore readBoundary ≠ ulogCore sourceMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        simpa [restoreMismatchCell, hstateRead, hsourceRead] using
          restoreRule_readBoundary slot left y right
      · simpa [restoreMismatchCell, hs, hm, hr] using
          restoreRule_pass slot x hs hm hr hboundary hboundaryZero
            hboundaryOne hpc left y right

theorem reaches_restoreRule_boundary (slot : Bool) (path : List Tape)
    (hpath : MismatchRestorePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (outer : List Tape) (pcSide : Tape) (right : List Tape) :
    Reaches
      (.running (.restoreRule slot)
        (beforeLeftPath path (pcSide :: outer) (ulogCore boundary) right))
      (.running (.mismatchReturnToPc slot)
        ⟨outer, pcSide,
          ulogCore boundary :: path.reverse.map restoreMismatchCell ++ right⟩) := by
  have h₀ : Reaches
      (.running (.restoreRule slot)
        (beforeLeftPath path (pcSide :: outer) (ulogCore boundary) right))
      (.running (.restoreRule slot)
        (afterLeftPathMap path restoreMismatchCell (pcSide :: outer)
          (ulogCore boundary) right)) :=
    ⟨path.length, run_left_path_map_of (.restoreRule slot) path
      restoreMismatchCell (by
        intro x hx l y r
        have h := hpath x hx
        exact restoreRule_step slot x h.1 h.2.1 h.2.2.1 h.2.2.2 l y r)
      (pcSide :: outer) (ulogCore boundary) right⟩
  have h₁ : Reaches
      (.running (.restoreRule slot)
        (afterLeftPathMap path restoreMismatchCell (pcSide :: outer)
          (ulogCore boundary) right))
      (.running (.mismatchReturnToPc slot)
        ⟨outer, pcSide,
          ulogCore boundary :: path.reverse.map restoreMismatchCell ++ right⟩) := by
    apply reaches_step
    simpa [afterLeftPathMap] using
      (restoreRule_boundary slot boundary hboundary outer pcSide
        (path.reverse.map restoreMismatchCell ++ right))
  exact reaches_trans h₀ h₁

theorem reaches_mismatchReturnToPc (slot : Bool) (path : List Tape)
    (hpath : ∀ x ∈ path, x ≠ ulogCore pcMark)
    (outer : List Tape) (y : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchReturnToPc slot)
        (beforeLeftPath path outer (ulogCore pcMark) (y :: right)))
      (.running (.mismatchCount slot)
        (beforeRightPath path.reverse (ulogCore pcMark :: outer) y right)) := by
  have h₀ : Reaches
      (.running (.mismatchReturnToPc slot)
        (beforeLeftPath path outer (ulogCore pcMark) (y :: right)))
      (.running (.mismatchReturnToPc slot)
        (afterLeftPath path outer (ulogCore pcMark) (y :: right))) :=
    ⟨path.length, run_left_path_of (.mismatchReturnToPc slot) path
      (by
        intro x hx l z r
        exact mismatchReturnToPc_pass slot x (hpath x hx) l z r)
      outer (ulogCore pcMark) (y :: right)⟩
  have h₁ : Reaches
      (.running (.mismatchReturnToPc slot)
        (afterLeftPath path outer (ulogCore pcMark) (y :: right)))
      (.running (.mismatchCount slot)
        (beforeRightPath path.reverse (ulogCore pcMark :: outer) y right)) := by
    apply reaches_step
    cases hr : path.reverse with
    | nil =>
        simpa [afterLeftPath, beforeRightPath, hr] using
          (mismatchReturnToPc_mark slot outer y right)
    | cons x xs =>
        simpa [afterLeftPath, beforeRightPath, hr, List.append_assoc] using
          (mismatchReturnToPc_mark slot outer x (xs ++ y :: right))
  exact reaches_trans h₀ h₁

def MismatchAdvancePathSafe (path : List Tape) : Prop :=
  MismatchBoundaryFree path ∧
    ∀ x ∈ path, x ≠ ulogCore pcMark

theorem reaches_mismatchAdvanceRule (lookupSlot : Bool) (done : ℕ)
    (path : List Tape) (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (outer : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (.running (.mismatchReturnToPc lookupSlot)
        (beforeLeftPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse
          outer (ulogCore pcMark)
          (ulogCore boundary ::
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right)))
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++
              ulogCore pcMark :: outer)
        after right) := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturnSafe : ∀ x ∈ returnPath, x ≠ ulogCore pcMark := by
    intro x hx
    have hx' : x ∈ path ∨ x = ulogCore pcDone ∨
        (done ≠ 0 ∧ x = ulogCore codeZero) := by
      simpa [returnPath] using hx
    rcases hx' with hpath' | hdone | hzero
    · exact hpath.2 x hpath'
    · rw [hdone]
      native_decide
    · rw [hzero.2]
      native_decide
  have h₀ := reaches_mismatchReturnToPc lookupSlot returnPath hreturnSafe
    outer (ulogCore boundary)
    ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
  have h₀' : Reaches
      (.running (.mismatchReturnToPc lookupSlot)
        (beforeLeftPath returnPath outer (ulogCore pcMark)
          (ulogCore boundary ::
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right)))
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          (ulogCore pcMark :: outer) (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right))) := by
    simpa [returnPath] using h₀
  have h₁ := reaches_mismatchCount_skipRule lookupSlot done path hpath.1
    boundary hboundary r next hnext (ulogCore pcMark :: outer) after right
  exact reaches_trans h₀' h₁

def restoreAdvanceStarted (lookupSlot : Bool) (restorePath returnPath : List Tape)
    (outer : List Tape) (boundary : ULogLetter)
    (mismatchRight : List Tape) : Result :=
  match returnPath with
  | [] => .rejected
  | x :: xs =>
      .running (.restoreRule lookupSlot)
        (beforeLeftPath restorePath
          (x :: xs ++ ulogCore pcMark :: outer)
          (ulogCore boundary) mismatchRight)

theorem reaches_restoreMismatchAdvanceRule (lookupSlot : Bool) (done : ℕ)
    (path : List Tape) (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (restorePath : List Tape) (hrestoreSafe : MismatchRestorePathSafe restorePath)
    (mismatchRight : List Tape)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (outer : List Tape) (after : Tape) (right : List Tape)
    (hrestored : restorePath.reverse.map restoreMismatchCell ++ mismatchRight =
      (ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right) :
    Reaches
      (restoreAdvanceStarted lookupSlot restorePath
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse
        outer boundary mismatchRight)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++
              ulogCore pcMark :: outer)
        after right) := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      have h₀ := reaches_restoreRule_boundary lookupSlot restorePath
        hrestoreSafe boundary hboundary
        (xs ++ ulogCore pcMark :: outer) x mismatchRight
      have hrestored' :
          (restorePath.map restoreMismatchCell).reverse ++ mismatchRight =
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right := by
        simpa only [List.map_reverse] using hrestored
      have h₀' : Reaches
          (restoreAdvanceStarted lookupSlot restorePath returnPath
            outer boundary mismatchRight)
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right))) := by
        simpa [restoreAdvanceStarted, he, beforeLeftPath,
          hrestored', List.append_assoc] using h₀
      have h₁ := reaches_mismatchAdvanceRule lookupSlot done path hpath
        boundary hboundary r next hnext outer after right
      have h₁' : Reaches
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right)))
          (atBits (.fieldCompare .source lookupSlot) next
            (mismatchRulePrefix r ++
              (if boundary = sourceBoundaryZero then ulogCore codeZero
                else ulogCore codeOne) :: path.reverse ++
              ulogCore codeZero ::
                List.replicate done (ulogCore codeZero) ++
                  ulogCore pcMark :: outer)
            after right) := by
        simpa [returnPath] using h₁
      exact reaches_trans h₀' h₁'

theorem compareRestoreSource_pass (slot : Bool) (x : Tape)
    (hstate : x ≠ ulogCore stateMark)
    (hsource : x ≠ ulogCore sourceMark)
    (hboundary : x ≠ ulogCore sourceBoundary)
    (hboundaryZero : x ≠ ulogCore sourceBoundaryZero)
    (hboundaryOne : x ≠ ulogCore sourceBoundaryOne)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot) ⟨y :: left, x, right⟩) =
      .running (.compareRestoreSource slot) ⟨left, y, x :: right⟩ := by
  have ha : State.compareRestoreSource slot ≠ qAccept := by
    cases slot <;> decide
  have hr : State.compareRestoreSource slot ≠ qReject := by
    cases slot <;> decide
  simp [oneStep, program, rule, deterministicStep, go, hstate, hsource,
    hboundary, hboundaryZero, hboundaryOne, hpc, applyAction, ha, hr]

theorem compareRestoreSource_step (slot : Bool) (x : Tape)
    (hboundary : x ≠ ulogCore sourceBoundary)
    (hboundaryZero : x ≠ ulogCore sourceBoundaryZero)
    (hboundaryOne : x ≠ ulogCore sourceBoundaryOne)
    (hpc : x ≠ ulogCore pcMark) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running (.compareRestoreSource slot) ⟨y :: left, x, right⟩) =
      .running (.compareRestoreSource slot)
        ⟨left, y, restoreSourceCell x :: right⟩ := by
  by_cases hs : x = ulogCore stateMark
  · subst x
    simpa [restoreSourceCell] using
      compareRestoreSource_stateMark slot left y right
  · by_cases hm : x = ulogCore sourceMark
    · subst x
      have hne : ulogCore sourceMark ≠ ulogCore stateMark :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      simpa [restoreSourceCell, hne] using
        compareRestoreSource_sourceMark slot left y right
    · simpa [restoreSourceCell, hs, hm] using
        compareRestoreSource_pass slot x hs hm hboundary hboundaryZero
          hboundaryOne hpc left y right

def sourceFinishPath (q : ℕ) (corridor : List Tape) : List Tape :=
  corridor ++ List.replicate q (ulogCore stateMark)

def sourceRestorePath (q : ℕ) (corridor : List Tape) : List Tape :=
  (sourceFinishPath q corridor).reverse ++
    ulogCore codeOne :: List.replicate q (ulogCore sourceMark)

theorem compareFinishSource_one_over_path (slot : Bool)
    (path left : List Tape) (boundary : Tape) (suffix : List Tape) :
    oneStep (.running (.compareFinishSource slot)
      ⟨path ++ boundary :: left, ulogCore stateOne, suffix⟩) =
      .running (.compareRestoreSource slot)
        (beforeLeftPath path left boundary (ulogCore stateOne :: suffix)) := by
  cases path with
  | nil => exact compareFinishSource_one slot left boundary suffix
  | cons x xs =>
      simpa [beforeLeftPath, List.append_assoc] using
        (compareFinishSource_one slot (xs ++ boundary :: left) x suffix)

theorem restoreSourceCell_corridor {corridor : List Tape}
    (hcorridor : SourceCompareCorridorSafe corridor) :
    corridor.map restoreSourceCell = corridor := by
  induction corridor with
  | nil => rfl
  | cons x xs ih =>
      have hx := hcorridor x (by simp)
      have hxs : SourceCompareCorridorSafe xs := by
        intro y hy
        exact hcorridor y (by simp [hy])
      rw [List.map_cons, ih hxs]
      simp [restoreSourceCell, hx.2.2.2.1, hx.2.2.2.2.2.1]

theorem restoreSourceCell_finishPath (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor) :
    (sourceFinishPath q corridor).map restoreSourceCell =
      corridor ++ List.replicate q (ulogCore stateZero) := by
  simp [sourceFinishPath, List.map_append,
    restoreSourceCell_corridor hcorridor, restoreSourceCell]

theorem sourceRestorePath_safe (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor) {x : Tape}
    (hx : x ∈ sourceRestorePath q corridor) :
    x ≠ ulogCore sourceBoundary ∧
      x ≠ ulogCore sourceBoundaryZero ∧
        x ≠ ulogCore sourceBoundaryOne ∧
          x ≠ ulogCore pcMark := by
  unfold sourceRestorePath at hx
  rcases List.mem_append.mp hx with hfinish | htail
  · have hm : x ∈ sourceFinishPath q corridor := by simpa using hfinish
    unfold sourceFinishPath at hm
    rcases List.mem_append.mp hm with hc | hs
    · have h := hcorridor x hc
      exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2, h.2.2.2.2.1⟩
    · have hsm : q ≠ 0 ∧ x = ulogCore stateMark := by
        simpa only [List.mem_replicate] using hs
      rw [hsm.2]
      decide
  · simp only [List.mem_cons, List.mem_replicate] at htail
    rcases htail with h | h
    · rw [h]
      decide
    · rw [h.2]
      decide

theorem sourceRestorePath_map (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor) :
    (sourceRestorePath q corridor).reverse.map restoreSourceCell =
      List.replicate q (ulogCore codeZero) ++
        ulogCore codeOne :: corridor ++
          List.replicate q (ulogCore stateZero) := by
  have hstate : ulogCore stateMark ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hsourceState : ulogCore sourceMark ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeState : ulogCore codeOne ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeSource : ulogCore codeOne ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  simp [sourceRestorePath, List.reverse_append, List.map_reverse,
    List.map_append, restoreSourceCell, hstate, hsourceState,
    honeState, honeSource,
    restoreSourceCell_finishPath q corridor hcorridor,
    List.append_assoc]

def sourceFieldRestored (slot : Bool) (q : ℕ)
    (base corridor suffix : List Tape) : Result :=
  match q with
  | 0 => .running (.fieldCompare .matchedSource slot)
      ⟨ulogCore sourceBoundary :: base, ulogCore codeOne,
        corridor ++ ulogCore stateOne :: suffix⟩
  | n + 1 => .running (.fieldCompare .matchedSource slot)
      ⟨ulogCore sourceBoundary :: base, ulogCore codeZero,
        List.replicate n (ulogCore codeZero) ++ ulogCore codeOne ::
          corridor ++ List.replicate (n + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩

theorem reaches_sourceMatchRestored (slot : Bool) (q : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (base suffix : List Tape) :
    Reaches
      (sourceCompareStart slot q 0 corridor
        (ulogCore sourceBoundary :: base) suffix)
      (sourceFieldRestored slot q base corridor suffix) := by
  have h₀ := reaches_sourceCompareZeros slot q 0 corridor hcorridor
    (ulogCore sourceBoundary :: base) suffix
  let finishPath := sourceFinishPath q corridor
  let restorePath := sourceRestorePath q corridor
  have h₁ : Reaches
      (sourceCompareAllMarked slot q 0 corridor
        (ulogCore sourceBoundary :: base) suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne ::
            List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
          (ulogCore stateOne) suffix)) := by
    rw [show sourceCompareAllMarked slot q 0 corridor
          (ulogCore sourceBoundary :: base) suffix =
        .running (.fieldCompare .source slot)
          ⟨List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base,
            ulogCore codeOne,
            finishPath ++ ulogCore stateOne :: suffix⟩ by
      simp [sourceCompareAllMarked, finishPath, sourceFinishPath]]
    apply reaches_step
    cases he : finishPath with
    | nil =>
        simpa [sourceCompareAllMarked, finishPath, sourceFinishPath,
          beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
            (ulogCore stateOne) suffix)
    | cons x xs =>
        simpa [sourceCompareAllMarked, finishPath, sourceFinishPath,
          beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
            x (xs ++ ulogCore stateOne :: suffix))
  have h₂ : Reaches
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne ::
            List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
          (ulogCore stateOne) suffix))
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne ::
            List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
          (ulogCore stateOne) suffix)) := by
    refine ⟨finishPath.length, run_right_path_of
      (.compareFinishSource slot) finishPath ?_ _ _ _⟩
    intro x hx l y r
    unfold finishPath sourceFinishPath at hx
    rcases List.mem_append.mp hx with hc | hs
    · have h := hcorridor x hc
      exact compareFinishSource_pass slot x h.2.2.2.2.2.1 h.1
        h.2.1 h.2.2.1 l y r
    · have hm : q ≠ 0 ∧ x = ulogCore stateMark := by
        simpa only [List.mem_replicate] using hs
      rw [hm.2]
      exact compareFinishSource_mark slot l y r
  have h₃ : Reaches
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne ::
            List.replicate q (ulogCore sourceMark) ++
              ulogCore sourceBoundary :: base)
          (ulogCore stateOne) suffix))
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore sourceBoundary)
          (ulogCore stateOne :: suffix))) := by
    apply reaches_step
    simpa [finishPath, restorePath, sourceRestorePath,
      afterRightPath, List.append_assoc] using
      (compareFinishSource_one_over_path slot restorePath base
        (ulogCore sourceBoundary) suffix)
  have h₄ : Reaches
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore sourceBoundary)
          (ulogCore stateOne :: suffix)))
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore sourceBoundary) (ulogCore stateOne :: suffix))) := by
    refine ⟨restorePath.length, run_left_path_map_of
      (.compareRestoreSource slot) restorePath restoreSourceCell ?_
      base (ulogCore sourceBoundary) (ulogCore stateOne :: suffix)⟩
    intro x hx l y r
    have hsafe := sourceRestorePath_safe q corridor hcorridor
      (by simpa [restorePath] using hx)
    exact compareRestoreSource_step slot x hsafe.1 hsafe.2.1
      hsafe.2.2.1 hsafe.2.2.2 l y r
  have h₅ : Reaches
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore sourceBoundary) (ulogCore stateOne :: suffix)))
      (sourceFieldRestored slot q base corridor suffix) := by
    apply reaches_step
    have hmap : restorePath.reverse.map restoreSourceCell =
        List.replicate q (ulogCore codeZero) ++
          ulogCore codeOne :: corridor ++
            List.replicate q (ulogCore stateZero) := by
      simpa [restorePath] using sourceRestorePath_map q corridor hcorridor
    rw [show afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore sourceBoundary) (ulogCore stateOne :: suffix) =
        ⟨base, ulogCore sourceBoundary,
          List.replicate q (ulogCore codeZero) ++
            ulogCore codeOne :: corridor ++
              List.replicate q (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    cases q with
    | zero =>
        simpa [afterLeftPathMap, sourceFieldRestored,
          sourceRestorePath_map, restorePath, List.append_assoc] using
          (compareRestoreSource_boundary slot base
            (ulogCore codeOne) (corridor ++ ulogCore stateOne :: suffix))
    | succ q =>
        simpa [afterLeftPathMap, sourceFieldRestored,
          sourceRestorePath_map, restorePath, List.replicate_succ,
          List.append_assoc] using
          (compareRestoreSource_boundary slot base
            (ulogCore codeZero)
            (List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
              corridor ++ List.replicate (q + 1) (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

def sourceReadStarted (slot : Bool) (q : ℕ) (b : Bool)
    (base corridor suffix : List Tape) : Result :=
  .running (.fieldCompare .read slot)
    ⟨ulogCore codeOne ::
        (List.replicate q (ulogCore codeZero) ++
          ulogCore sourceBoundary :: base),
      codeTape b,
      corridor ++ List.replicate q (ulogCore stateZero) ++
        ulogCore stateOne :: suffix⟩

theorem reaches_sourceFieldRestored_read (slot : Bool) (q : ℕ) (b : Bool)
    (base corridor suffix : List Tape) :
    Reaches
      (sourceFieldRestored slot q base (codeTape b :: corridor) suffix)
      (sourceReadStarted slot q b base corridor suffix) := by
  have h := reaches_unaryState_of (.fieldCompare .matchedSource slot)
    (.fieldCompare .read slot) q (matchedSourceSeek_zero slot)
    (matchedSourceSeek_one slot) (ulogCore sourceBoundary :: base)
    (codeTape b)
    (corridor ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  cases q <;>
    simpa [sourceFieldRestored, sourceReadStarted, beforeUnaryState,
      List.replicate_succ, List.append_assoc] using h

theorem reaches_sourceReadZero_slotMatch (slot : Bool) (q : ℕ)
    (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStarted slot q true base
        (codeTape slot :: path ++ ulogCore payloadHeadZero :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeOne ::
            List.replicate q (ulogCore codeZero) ++
              ulogCore sourceBoundary :: base)
          (ulogCore payloadHeadZero)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readZero_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore sourceBoundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStarted, codeTape, List.append_assoc] using h

theorem reaches_sourceReadOne_slotMatch (slot : Bool) (q : ℕ)
    (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStarted slot q false base
        (ulogCore codeOne :: codeTape slot :: path ++
          ulogCore payloadHeadOne :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
              ulogCore sourceBoundary :: base)
          (ulogCore payloadHeadOne)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readOne_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore sourceBoundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStarted, codeTape, List.append_assoc] using h

theorem reaches_sourceReadBlank_slotMatch (slot : Bool) (q : ℕ)
    (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStarted slot q false base
        (ulogCore codeZero :: ulogCore codeOne :: codeTape slot ::
          path ++ ulogCore payloadHeadBlank :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: ulogCore codeOne ::
              List.replicate q (ulogCore codeZero) ++
                ulogCore sourceBoundary :: base)
          (ulogCore payloadHeadBlank)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readBlank_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore sourceBoundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStarted, codeTape, List.append_assoc] using h

def unaryFieldFirst : ℕ → Bool
  | 0 => true
  | _ + 1 => false

def readHeadNat : ℕ → Tape
  | 0 => ulogCore payloadHeadZero
  | 1 => ulogCore payloadHeadOne
  | _ => ulogCore payloadHeadBlank

def matchedReadLeft (slot : Bool) (source read : ℕ)
    (base : List Tape) : List Tape :=
  codeTape slot :: ulogCore codeOne ::
    List.replicate read (ulogCore codeZero) ++ ulogCore codeOne ::
      List.replicate source (ulogCore codeZero) ++
        ulogCore sourceBoundary :: base

def encodedActionPath (write target : ℕ) (m : OneTapeTableau.Move)
    (movePath : List Tape) : List Tape :=
  (ULogBytecode.encodeNatField write ++
    ULogBytecode.encodeNatField target).map codeTape ++
      moveBits m ++ movePath

def firstRuleCorridor (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (head : Tape) (runtimePrefix : List Tape) : List Tape :=
  ((ULogBytecode.encodeNatField r.read ++ [r.slot] ++
      ULogBytecode.encodeAction r.action ++ ULogBytecode.encodeRules rs).map
        codeTape) ++
    (payloadProgramPrefix input).reverse ++ head :: runtimePrefix

theorem firstRuleCorridor_safe (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool)
    (head : Tape) (runtimePrefix : List Tape)
    (htail : SourceCompareCorridorSafe (head :: runtimePrefix)) :
    SourceCompareCorridorSafe
      (firstRuleCorridor r rs input head runtimePrefix) := by
  intro x hx
  unfold firstRuleCorridor at hx
  rcases List.mem_append.mp hx with hprefix | htail'
  · rcases List.mem_append.mp hprefix with hcode | hpayload
    · rcases List.mem_map.mp hcode with ⟨b, -, rfl⟩
      cases b <;> native_decide
    · have hpayload' : x ∈ payloadProgramPrefix input := by
        simpa only [List.mem_reverse] using hpayload
      rcases payloadProgramPrefix_mem hpayload' with rfl | rfl | rfl | rfl <;>
        native_decide
  · exact htail x htail'

theorem ruleSourceStarted_cons_eq (slot : Bool)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (left : List Tape) (head : Tape)
    (runtimePrefix suffix : List Tape) :
    ruleSourceStarted slot (r :: rs) input left head
        (runtimePrefix ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      sourceCompareStart slot r.source 0
        (firstRuleCorridor r rs input head runtimePrefix)
        (ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: left)
        suffix := by
  rcases r with ⟨source, read, ruleSlot, action⟩
  cases source <;>
    simp [ruleSourceStarted, sourceCompareStart, firstRuleCorridor,
      ULogBytecode.encodeRules, ULogBytecode.encodeRule,
      ULogBytecode.encodeNatField, List.replicate_succ,
      List.map_append, List.append_assoc, sourceCompareScanPath, codeTape]

theorem reaches_ruleSourceMatch_read (slot : Bool)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (left : List Tape) (head : Tape)
    (runtimePrefix suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (firstRuleCorridor r rs input head runtimePrefix)) :
    Reaches
      (ruleSourceStarted slot (r :: rs) input left head
        (runtimePrefix ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (sourceReadStarted slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          (([r.slot] ++ ULogBytecode.encodeAction r.action ++
            ULogBytecode.encodeRules rs).map codeTape) ++
          (payloadProgramPrefix input).reverse ++ head :: runtimePrefix)
        suffix) := by
  rw [ruleSourceStarted_cons_eq]
  have h₀ := reaches_sourceMatchRestored slot r.source
    (firstRuleCorridor r rs input head runtimePrefix) hcorridor
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left) suffix
  have hcorridorEq :
      firstRuleCorridor r rs input head runtimePrefix =
        codeTape (unaryFieldFirst r.read) ::
          ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
            (([r.slot] ++ ULogBytecode.encodeAction r.action ++
              ULogBytecode.encodeRules rs).map codeTape) ++
            (payloadProgramPrefix input).reverse ++ head :: runtimePrefix) := by
    cases r with
    | mk source read ruleSlot action =>
        cases read <;>
          simp [firstRuleCorridor, ULogBytecode.encodeNatField,
            unaryFieldFirst, List.replicate_succ, List.map_append, codeTape,
            List.append_assoc]
  have h₁ : Reaches
      (sourceFieldRestored slot r.source
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        (firstRuleCorridor r rs input head runtimePrefix) suffix)
      (sourceReadStarted slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          (([r.slot] ++ ULogBytecode.encodeAction r.action ++
            ULogBytecode.encodeRules rs).map codeTape) ++
          (payloadProgramPrefix input).reverse ++ head :: runtimePrefix)
        suffix) := by
    rw [hcorridorEq]
    exact reaches_sourceFieldRestored_read slot r.source
      (unaryFieldFirst r.read)
      (List.replicate (r :: rs).length (ulogCore pcDone) ++
        ulogCore pcMark :: left)
      ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
        (([r.slot] ++ ULogBytecode.encodeAction r.action ++
          ULogBytecode.encodeRules rs).map codeTape) ++
        (payloadProgramPrefix input).reverse ++ head :: runtimePrefix)
      suffix
  exact reaches_trans h₀ h₁

def beforeStartWork (n : ℕ) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨left, MStarConcreteAlphabet.work,
      List.replicate k MStarConcreteAlphabet.work ++ y :: right⟩

def afterStartWork (n : ℕ) (left : List Tape) (y : Tape)
    (right : List Tape) : Zipper Tape :=
  ⟨List.replicate n MStarConcreteAlphabet.work ++ left, y, right⟩

theorem run_start_work (n : ℕ) (left : List Tape) (y : Tape)
    (right : List Tape) :
    run n (.running .start (beforeStartWork n left y right)) =
      .running .start (afterStartWork n left y right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run]
      rw [show oneStep (.running .start
          (beforeStartWork (n + 1) left y right)) =
          .running .start
            (beforeStartWork n (MStarConcreteAlphabet.work :: left) y right) by
        cases n <;> simp [beforeStartWork, start_work_step,
          List.replicate_succ, List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running .start)
      apply Zipper.ext <;>
        simp [afterStartWork, List.replicate_succ', List.append_assoc]

def beforePayload (bits : List Bool) (left tail : List Tape) : Zipper Tape :=
  match bits with
  | [] => ⟨left, MStarConcreteAlphabet.work, tail⟩
  | b :: bs => ⟨left, bitTape b,
      bs.map bitTape ++ MStarConcreteAlphabet.work :: tail⟩

def afterPayload (bits : List Bool) (left tail : List Tape) : Zipper Tape :=
  ⟨bits.reverse.map codeTape ++ left,
    MStarConcreteAlphabet.work, tail⟩

theorem run_seekPayload_bits (bits : List Bool) (left tail : List Tape) :
    run bits.length (.running .seekPayload (beforePayload bits left tail)) =
      .running .seekPayload (afterPayload bits left tail) := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bits ih =>
      rw [show (b :: bits).length = bits.length + 1 by simp, run]
      rw [show oneStep (.running .seekPayload
          (beforePayload (b :: bits) left tail)) =
          .running .seekPayload
            (beforePayload bits (codeTape b :: left) tail) by
        cases bits <;> simp [beforePayload, seekPayload_bit_step,
          List.append_assoc]]
      rw [ih]
      apply congrArg (Result.running .seekPayload)
      apply Zipper.ext <;>
        simp [afterPayload, List.map_reverse, List.append_assoc]

def beforeReturn (bits : List Bool) (left tail : List Tape) : Zipper Tape :=
  match bits.reverse with
  | [] => ⟨left, ulogCore pcMark, ulogCore codeEnd :: tail⟩
  | b :: bs => ⟨bs.map codeTape ++ ulogCore pcMark :: left,
      codeTape b, ulogCore codeEnd :: tail⟩

def afterReturn (bits : List Bool) (left tail : List Tape) : Zipper Tape :=
  ⟨left, ulogCore pcMark,
    bits.map codeTape ++ ulogCore codeEnd :: tail⟩

def beforeReturnList (xs : List Bool) (left right : List Tape) : Zipper Tape :=
  match xs with
  | [] => ⟨left, ulogCore pcMark, right⟩
  | b :: bs => ⟨bs.map codeTape ++ ulogCore pcMark :: left,
      codeTape b, right⟩

def afterReturnList (xs : List Bool) (left right : List Tape) : Zipper Tape :=
  ⟨left, ulogCore pcMark,
    xs.reverse.map codeTape ++ right⟩

theorem run_translateReturn_list (xs : List Bool)
    (left right : List Tape) :
    run xs.length (.running .translateReturn (beforeReturnList xs left right)) =
      .running .translateReturn (afterReturnList xs left right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons b xs ih =>
      rw [show (b :: xs).length = xs.length + 1 by simp, run]
      rw [show oneStep (.running .translateReturn
          (beforeReturnList (b :: xs) left right)) =
          .running .translateReturn
            (beforeReturnList xs left (codeTape b :: right)) by
        cases xs <;> exact translateReturn_code_step b _ _ _]
      rw [ih]
      apply congrArg (Result.running .translateReturn)
      apply Zipper.ext <;>
        simp [afterReturnList, List.map_reverse, List.append_assoc]

theorem run_translateReturn_bits (bits : List Bool)
    (left tail : List Tape) :
    run bits.length (.running .translateReturn (beforeReturn bits left tail)) =
      .running .translateReturn (afterReturn bits left tail) := by
  simpa [beforeReturn, afterReturn, beforeReturnList, afterReturnList,
    List.map_reverse] using
      (run_translateReturn_list bits.reverse left (ulogCore codeEnd :: tail))

theorem reaches_bootstrap_nonempty (b : Bool) (bits : List Bool)
    (left tail : List Tape) :
    Reaches
      (.running .start
        ⟨MStarConcreteAlphabet.work :: left, bitTape b,
          bits.map bitTape ++ MStarConcreteAlphabet.work :: tail⟩)
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (b :: bits).map codeTape ++ ulogCore codeEnd :: tail⟩) := by
  have h₀ : Reaches
      (.running .start
        ⟨MStarConcreteAlphabet.work :: left, bitTape b,
          bits.map bitTape ++ MStarConcreteAlphabet.work :: tail⟩)
      (.running .seekPayload
        (beforePayload bits (codeTape b :: ulogCore pcMark :: left) tail)) := by
    refine ⟨3, ?_⟩
    cases bits <;> simp [run, beforePayload, start_bit_step,
      translateCode_step, framePayload_step, List.append_assoc]
  have h₁ : Reaches
      (.running .seekPayload
        (beforePayload bits (codeTape b :: ulogCore pcMark :: left) tail))
      (.running .seekPayload
        (afterPayload bits (codeTape b :: ulogCore pcMark :: left) tail)) :=
    ⟨bits.length, run_seekPayload_bits bits _ tail⟩
  have h₂ : Reaches
      (.running .seekPayload
        (afterPayload bits (codeTape b :: ulogCore pcMark :: left) tail))
      (.running .translateReturn
        (beforeReturn (b :: bits) left tail)) := by
    apply reaches_step
    unfold beforeReturn afterPayload
    rw [show (b :: bits).reverse = bits.reverse ++ [b] by simp]
    cases hr : bits.reverse with
    | nil =>
        have hbits : bits = [] := by
          simpa using congrArg List.reverse hr
        subst bits
        exact seekPayload_end_step
          (ulogCore pcMark :: left) tail (codeTape b)
    | cons c cs =>
        have hmap : (bits.map codeTape).reverse =
            codeTape c :: cs.map codeTape := by
          calc
            (bits.map codeTape).reverse = bits.reverse.map codeTape := by
              exact (List.map_reverse (l := bits) (f := codeTape)).symm
            _ = codeTape c :: cs.map codeTape := by rw [hr]; rfl
        simp only [hmap, hr,
          List.cons_append, List.map_append, List.map_cons,
          List.map_nil, List.append_nil]
        simpa [List.append_assoc] using
          (seekPayload_end_step
            (cs.map codeTape ++ codeTape b :: ulogCore pcMark :: left)
            tail (codeTape c))
  have h₃ : Reaches
      (.running .translateReturn (beforeReturn (b :: bits) left tail))
      (.running .translateReturn (afterReturn (b :: bits) left tail)) :=
    ⟨(b :: bits).length, run_translateReturn_bits (b :: bits) left tail⟩
  have h₄ : Reaches
      (.running .translateReturn (afterReturn (b :: bits) left tail))
      (.running .framePayloadLength
        ⟨left, ulogCore pcMark,
          (b :: bits).map codeTape ++ ulogCore codeEnd :: tail⟩) := by
    apply reaches_step
    exact translateReturn_mark_step left _
  exact reaches_trans h₀
    (reaches_trans h₁ (reaches_trans h₂ (reaches_trans h₃ h₄)))

theorem reaches_bootstrap_from_workspace (n : ℕ) (b : Bool)
    (bits : List Bool) (source tail : List Tape) :
    Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++ bitTape b ::
            (bits.map bitTape ++ MStarConcreteAlphabet.work :: tail)⟩)
      (.running .framePayloadLength
        ⟨List.replicate n MStarConcreteAlphabet.work ++ source,
          ulogCore pcMark,
          (b :: bits).map codeTape ++ ulogCore codeEnd :: tail⟩) := by
  have hscan : Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++ bitTape b ::
            (bits.map bitTape ++ MStarConcreteAlphabet.work :: tail)⟩)
      (.running .start
        ⟨MStarConcreteAlphabet.work ::
            (List.replicate n MStarConcreteAlphabet.work ++ source),
          bitTape b,
          bits.map bitTape ++ MStarConcreteAlphabet.work :: tail⟩) := by
    refine ⟨n + 1, ?_⟩
    simpa [beforeStartWork, afterStartWork, List.replicate_succ,
      List.append_assoc] using
      (run_start_work (n + 1) source (bitTape b)
        (bits.map bitTape ++ MStarConcreteAlphabet.work :: tail))
  exact reaches_trans hscan
    (reaches_bootstrap_nonempty b bits
      (List.replicate n MStarConcreteAlphabet.work ++ source) tail)

theorem encodedUniversalInput_ne_nil (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBytecode.encodeProgram rules ++
        ULogBytecode.encodePayload input padding ≠ [] := by
  simp [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField]

/-- End-to-end executable front end from the copied workspace cell through
program-count folding and payload-length decoding on the actual universal
instance layout. -/
theorem reaches_bootstrap_payloadLengthDecoded
    (n : ℕ) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++
            (ULogBytecode.encodeProgram rules ++
              ULogBytecode.encodePayload input padding).map bitTape ++
                MStarConcreteAlphabet.work :: tail⟩)
      (atBits (.fieldReturn .payloadLength) (input ++ padding)
        (payloadLengthMarkedLeft input.length
          (programMarkedLeft rules
            (List.replicate n MStarConcreteAlphabet.work ++ source))
        )
        (ulogCore codeEnd) tail) := by
  let bits := ULogBytecode.encodeProgram rules ++
    ULogBytecode.encodePayload input padding
  have hbits : bits ≠ [] := encodedUniversalInput_ne_nil rules input padding
  cases he : bits with
  | nil => exact (hbits he).elim
  | cons b bs =>
      have h₀ := reaches_bootstrap_from_workspace n b bs source tail
      have h₁ := reaches_payloadLengthDecoded rules input padding
        (List.replicate n MStarConcreteAlphabet.work ++ source) tail
      have henc : ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding = b :: bs := by
        simpa [bits] using he
      rw [henc] at h₁
      have hall := reaches_trans h₀ h₁
      simpa [bits, he, List.map_append, List.append_assoc] using hall

/-- Full deterministic initialization from the copied universal instance to a
cycle-ready physical configuration with an exact `2^|padding|` binary clock,
the unary start-state record, and the semantic head marker. -/
theorem reaches_bootstrap_runtimeInitialized
    (n : ℕ) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++
            (ULogBytecode.encodeProgram rules ++
              ULogBytecode.encodePayload input padding).map bitTape ++
                MStarConcreteAlphabet.work ::
                  payloadRuntimeWorkspace input tail⟩)
      (initializedRuntime padding input
        (programMarkedLeft rules
          (List.replicate n MStarConcreteAlphabet.work ++ source)) tail) := by
  let bits := ULogBytecode.encodeProgram rules ++
    ULogBytecode.encodePayload input padding
  have hbits : bits ≠ [] := encodedUniversalInput_ne_nil rules input padding
  cases he : bits with
  | nil => exact (hbits he).elim
  | cons b bs =>
      have h₀ := reaches_bootstrap_from_workspace n b bs source
        (payloadRuntimeWorkspace input tail)
      have h₁ := reaches_payloadRuntimeInitialized rules input padding
        (List.replicate n MStarConcreteAlphabet.work ++ source) tail
      have henc : ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding = b :: bs := by
        simpa [bits] using he
      rw [henc] at h₁
      have h₁' : Reaches
          (.running .framePayloadLength
            ⟨List.replicate n MStarConcreteAlphabet.work ++ source,
              ulogCore pcMark,
              (b :: bs).map codeTape ++ ulogCore codeEnd ::
                payloadRuntimeWorkspace input tail⟩)
          (initializedRuntime padding input
            (programMarkedLeft rules
              (List.replicate n MStarConcreteAlphabet.work ++ source))
            tail) := by
        simpa [List.append_assoc] using h₁
      have hall := reaches_trans h₀ h₁'
      simpa [bits, he, List.map_append, List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
