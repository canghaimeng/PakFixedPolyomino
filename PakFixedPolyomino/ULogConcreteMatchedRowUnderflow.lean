import PakFixedPolyomino.ULogConcreteMatchedActionUnderflow

/-! Actual matching bytecode row before source/read/slot comparison, then
WRITE/target/move shortage. Central joints are propositions. -/

namespace PakFixedPolyomino.ULogConcreteMatchedRowUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open ULogBytecode (RuleCode)
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)
open ULogConcreteMatchedActionUnderflow
  (writeStart writePath targetCorridor movePenultimate
    stopFree_capacity_underflow stopFree_right_underflow
    stopFree_right_to_penultimate right_penultimate_oneStep
    no_accepting_of_stuck)

def rowStart (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (boundary : ULogLetter)
    (available : Nat) : Result :=
  atBitsTail (.fieldCompare .source r.slot)
    (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
    (programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work)

def rowWriteStart (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (boundary : ULogLetter)
    (available : Nat) : Result :=
  writeStart r.action.write r.action.target r.source available r.action.move
    (cursorMatchedMovePath rs programToHead) runtime
    (matchedReadLeftAt r.slot r.source r.read boundary base)
    (readHeadNat r.read)

theorem rowStart_outside (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (boundary : ULogLetter)
    (available : Nat) :
    preChoiceResult
      (rowStart r rs programToHead base runtime boundary available) =
      false := by
  unfold rowStart
  generalize hbits : ULogBytecode.encodeRules (r :: rs) = bits
  cases programToHead <;> cases bits <;>
    simp [atBitsTail, atBits, preChoiceResult, preChoice]

theorem readHeadNat_headed {read : Nat} (hread : read < 3) :
    choiceHead (readHeadNat read) = true := by
  interval_cases read <;> decide

theorem stuck_exists {n : Nat} {s : Result}
    (h : StopFreeValidZeroRun n s .stuck) :
    ∃ k, Nonempty (StopFreeValidZeroRun k s .stuck) ∧ run k s = .stuck :=
  ⟨n, ⟨⟨h⟩, h.valid.eq_run⟩⟩

theorem reached_exists {n : Nat} {s t : Result}
    (h : StopFreeValidZeroRun n s t) :
    ∃ k, Nonempty (StopFreeValidZeroRun k s t) ∧ run k s = t :=
  ⟨n, ⟨⟨h⟩, h.valid.eq_run⟩⟩

noncomputable def stopFree_row_to_write
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (hread : r.read < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (available : Nat) :
    Σ n, StopFreeValidZeroRun n
      (rowStart r rs programToHead base runtime boundary available)
      (rowWriteStart r rs programToHead base runtime boundary available) := by
  obtain ⟨n, hrun⟩ :=
    stopFree_ruleCursorMatched_actionWrite boundary hboundary r rs
      programToHead base runtime hread hcorridor hreadPath
      (ulogCore stateSep ::
        List.replicate available MStarConcreteAlphabet.work)
  refine ⟨n, ?_⟩
  simpa [rowStart, rowWriteStart, writeStart, writePath,
    List.append_assoc] using hrun

noncomputable def stopFree_row_capacity
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (capacity : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hc : r.source ≤ capacity) (ht : capacity < r.action.target)
    (hT : 2 ≤ r.action.target)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) runtime r.action.write)) :
    Σ n, StopFreeValidZeroRun n
      (rowStart r rs programToHead base runtime boundary
        (capacity - r.source)) .stuck := by
  obtain ⟨a, hrow⟩ :=
    stopFree_row_to_write boundary hboundary r rs programToHead base runtime
      hread hcorridor hreadPath (capacity - r.source)
  obtain ⟨b, hact⟩ :=
    stopFree_capacity_underflow r.action.write r.action.target r.source
      capacity hwrite hc ht hT r.action.move
      (cursorMatchedMovePath rs programToHead) runtime
      (matchedReadLeftAt r.slot r.source r.read boundary base)
      (readHeadNat r.read) (readHeadNat_headed hread) hwritePath htargetPath
  exact ⟨a + b, by simpa [rowWriteStart] using hrow.append hact⟩

theorem no_accepting_row_capacity
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (capacity : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hc : r.source ≤ capacity) (ht : capacity < r.action.target)
    (hT : 2 ≤ r.action.target)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) runtime r.action.write))
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (rowStart r rs programToHead base runtime boundary
        (capacity - r.source))
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_row_capacity boundary hboundary r rs programToHead base runtime
      capacity hread hwrite hc ht hT hcorridor hreadPath hwritePath
      htargetPath
  exact no_accepting_of_stuck hsf
    (rowStart_outside r rs programToHead base runtime boundary
      (capacity - r.source))
    labels tape raw

/-- Case A joint proposition: internally chosen stopped run to stuck, and
ALL labelled acceptance exclusion from the matched-row start. -/
theorem matched_row_capacity_underflow_spec
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base runtime : List Tape) (capacity : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hc : r.source ≤ capacity) (ht : capacity < r.action.target)
    (hT : 2 ≤ r.action.target)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) runtime r.action.write)) :
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (rowStart r rs programToHead base runtime boundary
            (capacity - r.source)) .stuck) ∧
      run n (rowStart r rs programToHead base runtime boundary
        (capacity - r.source)) = .stuck) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (rowStart r rs programToHead base runtime boundary
          (capacity - r.source))
        labels (.accepted tape) → False) := by
  obtain ⟨n, hsf⟩ :=
    stopFree_row_capacity boundary hboundary r rs programToHead base runtime
      capacity hread hwrite hc ht hT hcorridor hreadPath hwritePath
      htargetPath
  exact ⟨stuck_exists hsf,
    no_accepting_row_capacity boundary hboundary r rs programToHead base
      runtime capacity hread hwrite hc ht hT hcorridor hreadPath hwritePath
      htargetPath⟩

def rowMovePenultimate (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (srcBound : ULogLetter)
    (clkBound : Tape) (growth : Nat) : Result :=
  movePenultimate r.action.write r.source growth
    (cursorMatchedMovePath rs programToHead) pre
    (matchedReadLeftAt r.slot r.source r.read srcBound base) clkBound

noncomputable def stopFree_row_right_to_penultimate
    (srcBound : ULogLetter)
    (hsrc : srcBound = sourceBoundary ∨
      srcBound = sourceBoundaryZero ∨ srcBound = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htarget : r.action.target = r.source + growth)
    (hT : 2 ≤ r.action.target) (hmove : r.action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hshiftPre : ShiftRuntimeSafe pre)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write)) :
    Σ n, StopFreeValidZeroRun n
      (rowStart r rs programToHead base (clkBound :: pre) srcBound growth)
      (rowMovePenultimate r rs programToHead base pre srcBound clkBound
        growth) := by
  obtain ⟨a, hrow⟩ :=
    stopFree_row_to_write srcBound hsrc r rs programToHead base
      (clkBound :: pre) hread hcorridor hreadPath growth
  have hwp : ActionWriteCorridorSafe
      (writePath (r.source + growth) .right
        (cursorMatchedMovePath rs programToHead)) := by
    simpa [htarget, hmove] using hwritePath
  have htp : TargetRewriteCorridorSafe
      (targetCorridor .right (cursorMatchedMovePath rs programToHead)
        (clkBound :: pre) r.action.write) := by
    simpa [hmove] using htargetPath
  obtain ⟨b, hact⟩ :=
    stopFree_right_to_penultimate r.action.write r.source growth hwrite
      (by omega) (cursorMatchedMovePath rs programToHead) pre
      (matchedReadLeftAt r.slot r.source r.read srcBound base) clkBound
      hboundary hscan hshiftPre (readHeadNat r.read)
      (readHeadNat_headed hread) hwp htp
  have hact' : StopFreeValidZeroRun b
      (rowWriteStart r rs programToHead base (clkBound :: pre) srcBound
        growth)
      (rowMovePenultimate r rs programToHead base pre srcBound clkBound
        growth) := by
    simpa [rowWriteStart, rowMovePenultimate, htarget, hmove] using hact
  exact ⟨a + b, hrow.append hact'⟩

theorem row_right_penultimate_oneStep
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (srcBound : ULogLetter)
    (clkBound : Tape) (growth : Nat) (hwrite : r.action.write < 3)
    (_htarget : r.action.target = r.source + growth)
    (hshiftPre : ShiftRuntimeSafe pre) :
    oneStep (rowMovePenultimate r rs programToHead base pre srcBound
      clkBound growth) = .stuck := by
  simpa [rowMovePenultimate] using
    right_penultimate_oneStep r.action.write r.source growth hwrite
      (cursorMatchedMovePath rs programToHead) pre
      (matchedReadLeftAt r.slot r.source r.read srcBound base) clkBound
      hshiftPre

noncomputable def stopFree_row_right
    (srcBound : ULogLetter)
    (hsrc : srcBound = sourceBoundary ∨
      srcBound = sourceBoundaryZero ∨ srcBound = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htarget : r.action.target = r.source + growth)
    (hT : 2 ≤ r.action.target) (hmove : r.action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hshiftPre : ShiftRuntimeSafe pre)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write)) :
    Σ n, StopFreeValidZeroRun n
      (rowStart r rs programToHead base (clkBound :: pre) srcBound growth)
      .stuck := by
  obtain ⟨a, hrow⟩ :=
    stopFree_row_to_write srcBound hsrc r rs programToHead base
      (clkBound :: pre) hread hcorridor hreadPath growth
  have hwp : ActionWriteCorridorSafe
      (writePath (r.source + growth) .right
        (cursorMatchedMovePath rs programToHead)) := by
    simpa [htarget, hmove] using hwritePath
  have htp : TargetRewriteCorridorSafe
      (targetCorridor .right (cursorMatchedMovePath rs programToHead)
        (clkBound :: pre) r.action.write) := by
    simpa [hmove] using htargetPath
  obtain ⟨b, hact⟩ :=
    stopFree_right_underflow r.action.write r.source growth hwrite
      (by omega) (cursorMatchedMovePath rs programToHead) pre
      (matchedReadLeftAt r.slot r.source r.read srcBound base) clkBound
      hboundary hscan hshiftPre (readHeadNat r.read)
      (readHeadNat_headed hread) hwp htp
  have hact' : StopFreeValidZeroRun b
      (rowWriteStart r rs programToHead base (clkBound :: pre) srcBound
        growth) .stuck := by
    simpa [rowWriteStart, htarget, hmove] using hact
  exact ⟨a + b, hrow.append hact'⟩

theorem no_accepting_row_right
    (srcBound : ULogLetter)
    (hsrc : srcBound = sourceBoundary ∨
      srcBound = sourceBoundaryZero ∨ srcBound = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htarget : r.action.target = r.source + growth)
    (hT : 2 ≤ r.action.target) (hmove : r.action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hshiftPre : ShiftRuntimeSafe pre)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write))
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (rowStart r rs programToHead base (clkBound :: pre) srcBound growth)
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_row_right srcBound hsrc r rs programToHead base pre clkBound
      growth hread hwrite htarget hT hmove hboundary hscan hshiftPre
      hcorridor hreadPath hwritePath htargetPath
  exact no_accepting_of_stuck hsf
    (rowStart_outside r rs programToHead base (clkBound :: pre) srcBound
      growth)
    labels tape raw

/-- Case B joint proposition: reached changed penultimate, oneStep stuck,
stopped run to stuck, and ALL labelled acceptance exclusion. -/
theorem matched_row_right_underflow_spec
    (srcBound : ULogLetter)
    (hsrc : srcBound = sourceBoundary ∨
      srcBound = sourceBoundaryZero ∨ srcBound = sourceBoundaryOne)
    (r : RuleCode) (rs : List RuleCode)
    (programToHead base pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htarget : r.action.target = r.source + growth)
    (hT : 2 ≤ r.action.target) (hmove : r.action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hshiftPre : ShiftRuntimeSafe pre)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)))
    (htargetPath : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write)) :
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (rowStart r rs programToHead base (clkBound :: pre) srcBound
            growth)
          (rowMovePenultimate r rs programToHead base pre srcBound clkBound
            growth)) ∧
      run n (rowStart r rs programToHead base (clkBound :: pre) srcBound
        growth) =
        rowMovePenultimate r rs programToHead base pre srcBound clkBound
          growth) ∧
    oneStep (rowMovePenultimate r rs programToHead base pre srcBound
      clkBound growth) = .stuck ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (rowStart r rs programToHead base (clkBound :: pre) srcBound
            growth) .stuck) ∧
      run n (rowStart r rs programToHead base (clkBound :: pre) srcBound
        growth) = .stuck) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (rowStart r rs programToHead base (clkBound :: pre) srcBound growth)
        labels (.accepted tape) → False) := by
  obtain ⟨nPen, hPen⟩ :=
    stopFree_row_right_to_penultimate srcBound hsrc r rs programToHead base
      pre clkBound growth hread hwrite htarget hT hmove hboundary hscan
      hshiftPre hcorridor hreadPath hwritePath htargetPath
  obtain ⟨nSt, hSt⟩ :=
    stopFree_row_right srcBound hsrc r rs programToHead base pre clkBound
      growth hread hwrite htarget hT hmove hboundary hscan hshiftPre
      hcorridor hreadPath hwritePath htargetPath
  exact ⟨reached_exists hPen,
    ⟨row_right_penultimate_oneStep r rs programToHead base pre srcBound
        clkBound growth hwrite htarget hshiftPre,
      ⟨stuck_exists hSt,
        no_accepting_row_right srcBound hsrc r rs programToHead base pre
          clkBound growth hread hwrite htarget hT hmove hboundary hscan
          hshiftPre hcorridor hreadPath hwritePath htargetPath⟩⟩⟩

end PakFixedPolyomino.ULogConcreteMatchedRowUnderflow
