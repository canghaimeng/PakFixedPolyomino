import PakFixedPolyomino.ULogConcreteTargetRawUnderflow
import PakFixedPolyomino.ULogConcreteRightBoundaryUnderflow

/-! Actual WRITE then target/move shortage from a literal before-WRITE start.
Two finite cases: requested target exceeds allocated WORK, and RIGHT
target=capacity consumes exact growth WORK then no-work shift. -/

namespace PakFixedPolyomino.ULogConcreteMatchedActionUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)

def writePath (target : Nat) (m : Move) (movePath : List Tape) : List Tape :=
  List.replicate target (ulogCore codeZero) ++
    ulogCore codeOne :: moveBits m ++ movePath

def targetCorridor (m : Move) (movePath runtime : List Tape) (write : Nat) :
    List Tape :=
  moveBits m ++ movePath ++ writeHeadNat write :: runtime

def actionLeft (write : Nat) (left : List Tape) : List Tape :=
  ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left

def writeStart (write target current available : Nat) (m : Move)
    (movePath runtime left : List Tape) (oldHead : Tape) : Result :=
  actionWriteStart write left (writePath target m movePath) oldHead
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate available MStarConcreteAlphabet.work)

def enlargedPre (pre : List Tape) (target : Nat) : List Tape :=
  pre ++ List.replicate target (ulogCore stateZero) ++ [ulogCore stateOne]

theorem writeStart_outside (write : Nat) (left path : List Tape)
    (oldHead : Tape) (suffix : List Tape) :
    preChoiceResult (actionWriteStart write left path oldHead suffix) =
      false := by
  cases write <;> rfl

theorem writeHeadNat_headed {write : Nat} (hwrite : write < 3) :
    choiceHead (writeHeadNat write) = true := by
  interval_cases write <;> decide

theorem shiftRuntimeSafe_enlarged {pre : List Tape} {target : Nat}
    (hpre : ShiftRuntimeSafe pre) :
    ShiftRuntimeSafe (enlargedPre pre target ++ [ulogCore stateSep]) := by
  intro x hx
  have hx' : x ∈ pre ∨ x ∈ List.replicate target (ulogCore stateZero) ∨
      x = ulogCore stateOne ∨ x = ulogCore stateSep := by
    simpa [enlargedPre, List.append_assoc] using hx
  rcases hx' with h | h | rfl | rfl
  · exact hpre x h
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
    exact (work_ne_ulogCore _).symm
  · exact (work_ne_ulogCore _).symm
  · exact (work_ne_ulogCore _).symm

theorem no_accepting_of_stuck {n : Nat} {start : Result}
    (hsf : StopFreeValidZeroRun n start .stuck)
    (outside : preChoiceResult start = false)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath start labels (.accepted tape) → False := by
  intro raw
  have noChoice :=
    ULogConcreteRightBoundaryUnderflow.no_choice_before
      hsf.valid hsf.stop_free outside
  obtain ⟨rest, _, fromPen⟩ :=
    zero_prefix_of_micro_accepting hsf.valid noChoice raw
  have halted := microPath_halted_start fromPen (by rfl)
  cases halted.2

/-- Case A: WRITE prefix lands on the raw target start with independent WORK. -/
noncomputable def stopFree_write_to_raw
    (write target current available : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ target) (m : Move) (movePath runtime left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe (writePath target m movePath)) :
    Σ n, StopFreeValidZeroRun n
      (writeStart write target current available m movePath runtime left
        oldHead)
      (targetRawStart target current
        (targetCorridor m movePath runtime write)
        (actionLeft write left)
        (List.replicate available MStarConcreteAlphabet.work)) := by
  obtain ⟨n, hwriteRun⟩ :=
    stopFree_actionWriteValid write hwrite oldHead hhead
      (writePath target m movePath) hwritePath left
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work)
  refine ⟨n, ?_⟩
  cases htg : target with
  | zero => omega
  | succ t =>
      simpa [writeStart, writePath, targetCorridor, actionLeft,
        targetRawStart, htg, beforeRightPath, List.replicate_succ,
        List.append_assoc] using hwriteRun

noncomputable def stopFree_capacity_underflow
    (write target current capacity : Nat) (hwrite : write < 3)
    (hc : current ≤ capacity) (ht : capacity < target) (hT : 2 ≤ target)
    (m : Move) (movePath runtime left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe (writePath target m movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor m movePath runtime write)) :
    Σ n, StopFreeValidZeroRun n
      (writeStart write target current (capacity - current) m movePath
        runtime left oldHead) .stuck := by
  obtain ⟨a, hwrite⟩ :=
    stopFree_write_to_raw write target current (capacity - current) hwrite
      hT m movePath runtime left oldHead hhead hwritePath
  obtain ⟨b, ⟨_, hraw⟩⟩ :=
    ULogConcreteTargetRawUnderflow.stopFree_to_stuck target current capacity
      hc ht (targetCorridor m movePath runtime write) htargetPath
      (actionLeft write left)
  exact ⟨a + b, hwrite.append hraw⟩

theorem no_accepting_capacity
    (write target current capacity : Nat) (hwrite : write < 3)
    (hc : current ≤ capacity) (ht : capacity < target) (hT : 2 ≤ target)
    (m : Move) (movePath runtime left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe (writePath target m movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor m movePath runtime write))
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (writeStart write target current (capacity - current) m movePath
        runtime left oldHead)
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_capacity_underflow write target current capacity hwrite hc ht hT
      m movePath runtime left oldHead hhead hwritePath htargetPath
  exact no_accepting_of_stuck hsf (by
    simpa [writeStart, writePath] using
      writeStart_outside write left (writePath target m movePath) oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate (capacity - current) MStarConcreteAlphabet.work))
    labels tape raw

/-- Case A joint: internally chosen fuel to stuck, and ALL raw acceptance
exclusion from the literal before-WRITE start. -/
noncomputable def capacity_underflow_spec
    (write target current capacity : Nat) (hwrite : write < 3)
    (hc : current ≤ capacity) (ht : capacity < target) (hT : 2 ≤ target)
    (m : Move) (movePath runtime left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe (writePath target m movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor m movePath runtime write)) :
    (Σ n, StopFreeValidZeroRun n
      (writeStart write target current (capacity - current) m movePath
        runtime left oldHead) .stuck) ×'
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (writeStart write target current (capacity - current) m movePath
          runtime left oldHead)
        labels (.accepted tape) → False) :=
  ⟨stopFree_capacity_underflow write target current capacity hwrite hc ht hT
      m movePath runtime left oldHead hhead hwritePath htargetPath,
    no_accepting_capacity write target current capacity hwrite hc ht hT
      m movePath runtime left oldHead hhead hwritePath htargetPath⟩

theorem matched_move_eq_shortage
    (write current growth : Nat) (movePath pre left : List Tape)
    (boundary : Tape) :
    .running (.moveSimHead .right)
      (beforeRightPath movePath
        (matchedMoveLeft write (current + growth) .right left)
        (writeHeadNat write)
        ((boundary :: pre) ++
          List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: [])) =
      ULogConcreteRightBoundaryUnderflow.start movePath
        (enlargedPre pre (current + growth)) boundary (ulogCore stateSep)
        (writeHeadNat write)
        (matchedMoveLeft write (current + growth) .right left) := by
  simp [ULogConcreteRightBoundaryUnderflow.start, enlargedPre,
    List.append_assoc]

noncomputable def stopFree_write_to_move
    (write current growth : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (movePath pre left : List Tape)
    (boundary : Tape) (oldHead : Tape)
    (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (writePath (current + growth) .right movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor .right movePath (boundary :: pre) write)) :
    Σ n, StopFreeValidZeroRun n
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead)
      (ULogConcreteRightBoundaryUnderflow.start movePath
        (enlargedPre pre (current + growth)) boundary (ulogCore stateSep)
        (writeHeadNat write)
        (matchedMoveLeft write (current + growth) .right left)) := by
  obtain ⟨n, hrun⟩ :=
    stopFree_matchedActionAtLeastState write current growth hwrite htarget
      .right movePath (boundary :: pre) oldHead hhead (by
        simpa [writePath] using hwritePath) (by
        simpa [targetCorridor] using htargetPath) left []
  refine ⟨n, ?_⟩
  simpa [writeStart, writePath, ULogConcreteRightBoundaryUnderflow.start,
    enlargedPre, List.append_assoc] using hrun

def movePenultimate (write current growth : Nat)
    (movePath pre left : List Tape) (boundary : Tape) : Result :=
  ULogConcreteRightBoundaryUnderflow.penultimate movePath
    (enlargedPre pre (current + growth)) boundary (ulogCore stateSep)
    (writeHeadNat write)
    (matchedMoveLeft write (current + growth) .right left)

noncomputable def stopFree_right_to_penultimate
    (write current growth : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (movePath pre left : List Tape)
    (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hscan : MoveScanSafe movePath) (hshiftPre : ShiftRuntimeSafe pre)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (writePath (current + growth) .right movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor .right movePath (boundary :: pre) write)) :
    Σ n, StopFreeValidZeroRun n
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead)
      (movePenultimate write current growth movePath pre left boundary) := by
  obtain ⟨a, hmove⟩ :=
    stopFree_write_to_move write current growth hwrite htarget movePath pre
      left boundary oldHead hhead hwritePath htargetPath
  have hshift := shiftRuntimeSafe_enlarged (target := current + growth)
    hshiftPre
  have hwalk :=
    ULogConcreteRightBoundaryUnderflow.stopFree_to_penultimate movePath
      (enlargedPre pre (current + growth)) hscan boundary
      (ulogCore stateSep) (writeHeadNat write) hboundary hshift
      (matchedMoveLeft write (current + growth) .right left)
      (writeHeadNat_headed hwrite)
  exact ⟨a + (movePath.length + (enlargedPre pre (current + growth)).length + 2),
    by simpa [movePenultimate] using hmove.append hwalk⟩

theorem right_penultimate_oneStep
    (write current growth : Nat) (_hwrite : write < 3)
    (movePath pre left : List Tape) (boundary : Tape)
    (hshiftPre : ShiftRuntimeSafe pre) :
    oneStep (movePenultimate write current growth movePath pre left
      boundary) = .stuck :=
  ULogConcreteRightBoundaryUnderflow.penultimate_oneStep movePath
    (enlargedPre pre (current + growth)) boundary (ulogCore stateSep)
    (writeHeadNat write) (shiftRuntimeSafe_enlarged hshiftPre)
    (matchedMoveLeft write (current + growth) .right left)

noncomputable def stopFree_right_underflow
    (write current growth : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (movePath pre left : List Tape)
    (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hscan : MoveScanSafe movePath) (hshiftPre : ShiftRuntimeSafe pre)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (writePath (current + growth) .right movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor .right movePath (boundary :: pre) write)) :
    Σ n, StopFreeValidZeroRun n
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead) .stuck := by
  obtain ⟨a, hmove⟩ :=
    stopFree_write_to_move write current growth hwrite htarget movePath pre
      left boundary oldHead hhead hwritePath htargetPath
  have hshift := shiftRuntimeSafe_enlarged (target := current + growth)
    hshiftPre
  have hstuck :=
    ULogConcreteRightBoundaryUnderflow.stopFree_to_stuck movePath
      (enlargedPre pre (current + growth)) hscan boundary
      (ulogCore stateSep) (writeHeadNat write) hboundary hshift
      (matchedMoveLeft write (current + growth) .right left)
      (writeHeadNat_headed hwrite)
  exact ⟨a + (movePath.length + (enlargedPre pre (current + growth)).length + 3),
    hmove.append hstuck⟩

theorem no_accepting_right
    (write current growth : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (movePath pre left : List Tape)
    (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hscan : MoveScanSafe movePath) (hshiftPre : ShiftRuntimeSafe pre)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (writePath (current + growth) .right movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor .right movePath (boundary :: pre) write))
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead)
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_right_underflow write current growth hwrite htarget movePath pre
      left boundary hboundary hscan hshiftPre oldHead hhead hwritePath
      htargetPath
  exact no_accepting_of_stuck hsf (by
    simpa [writeStart, writePath] using
      writeStart_outside write left
        (writePath (current + growth) .right movePath) oldHead
        ((boundary :: pre) ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work))
    labels tape raw

/-- Case B joint: WRITE+target consume exact growth WORK, no-work
shift reaches the changed penultimate, oneStep stuck, full run to stuck,
and ALL raw acceptance exclusion from the before-WRITE start. -/
noncomputable def right_matched_underflow_spec
    (write current growth : Nat) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (movePath pre left : List Tape)
    (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hscan : MoveScanSafe movePath) (hshiftPre : ShiftRuntimeSafe pre)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (writePath (current + growth) .right movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor .right movePath (boundary :: pre) write)) :
    (Σ n, StopFreeValidZeroRun n
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead)
      (movePenultimate write current growth movePath pre left boundary)) ×'
    (oneStep (movePenultimate write current growth movePath pre left
      boundary) = .stuck) ×'
    (Σ n, StopFreeValidZeroRun n
      (writeStart write (current + growth) current growth .right movePath
        (boundary :: pre) left oldHead) .stuck) ×'
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (writeStart write (current + growth) current growth .right movePath
          (boundary :: pre) left oldHead)
        labels (.accepted tape) → False) :=
  ⟨stopFree_right_to_penultimate write current growth hwrite htarget
      movePath pre left boundary hboundary hscan hshiftPre oldHead hhead
      hwritePath htargetPath,
    ⟨right_penultimate_oneStep write current growth hwrite movePath pre left
        boundary hshiftPre,
      ⟨stopFree_right_underflow write current growth hwrite htarget movePath
          pre left boundary hboundary hscan hshiftPre oldHead hhead
          hwritePath htargetPath,
        no_accepting_right write current growth hwrite htarget movePath pre
          left boundary hboundary hscan hshiftPre oldHead hhead hwritePath
          htargetPath⟩⟩⟩

end PakFixedPolyomino.ULogConcreteMatchedActionUnderflow
