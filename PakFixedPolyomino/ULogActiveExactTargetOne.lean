import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Literal target-one first-hit rejection with kernel finite proofs.
The inherited source remains immutable; this independently names the exact
matched-rule/cycle proofs and removes their compiler-trust contributions. -/

namespace PakFixedPolyomino.ULogActiveExactTargetOne
open ULogBootstrapExecution ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

/-- A matched rule with target one rejects at its first concrete cycle stop
when the semantic source state is zero. -/
noncomputable def ruleCursorMatchedTargetOneZero_firstStop
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape)
    (hsource : r.source = 0) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) (tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail)) .rejected := by
  obtain ⟨a, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    boundary hboundary r rs programToHead base runtime hread hcorridor
    hreadPath (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)
  have hmatched' : StopFreeValidZeroRun a
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne ::
          moveBits r.action.move ++ cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail)) := by
    simpa [hsource, htarget] using hmatched
  have hreject := actionWriteTargetOneZero_firstStop r.action.write hwrite
    (readHeadNat r.read) (by interval_cases r.read <;> decide)
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) runtime
    hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  exact (hmatched'.append
    { valid := hreject.valid, stop_free := hreject.before }).toFirstHit
      hreject.hit

/-- A matched rule with target one rejects at its first concrete cycle stop
when the semantic source state is positive. -/
noncomputable def ruleCursorMatchedTargetOnePositive_firstStop
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (extra : ℕ)
    (hsource : r.source = extra + 1) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) (tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate (extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)) .rejected := by
  obtain ⟨a, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    boundary hboundary r rs programToHead base runtime hread hcorridor
    hreadPath (ulogCore stateSep :: tail)
  have hmatched' : StopFreeValidZeroRun a
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate (extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne ::
          moveBits r.action.move ++ cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [hsource, htarget] using hmatched
  have hreject := actionWriteTargetOnePositive_firstStop r.action.write extra
    hwrite (readHeadNat r.read)
    (by interval_cases r.read <;> decide)
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) runtime
    hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  exact (hmatched'.append
    { valid := hreject.valid, stop_free := hreject.before }).toFirstHit
      hreject.hit

/-- Semantic lookup of a target-one action has a canonical genuine
first-hit concrete rejecting cycle.  This is the exact counterpart of the
older `BranchedReaches` dispatch: both source-state cases retain the
stop-free proof all the way to `.rejected`. -/
theorem branchedCycle_semanticTargetOne_exact_nonempty
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) .rejected) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> decide
  let choiceLeft := dynamicRuleReturnPath (c.leftRev.map payloadNat)
    (skip ++ r :: rs) input ++ ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix
  have hchoice := clockDecrementCells_firstChoice (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    choiceLeft
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) := by
    simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
      clockCellsAfter, heq, choiceLeft, choiceRight,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot
    (c.leftRev.map payloadNat) (payloadNatList_safe c.leftRev)
    (skip ++ r :: rs) (by simp) input outer (readHeadNat c.focus) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
            input) outer (ulogCore pcMark) (readHeadNat c.focus :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil (c.leftRev.map payloadNat)
      (skip ++ r :: rs) input
    cases hePath : dynamicRuleReturnPath (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input with
    | nil => exact (hpne hePath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  obtain ⟨b, hmismatch⟩ := stopFree_mismatchPrefix
    cursorMismatchStopFreeStep slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix))
    trace
  have hmismatch' := hmismatch
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot c.state c.focus
    (c.leftRev.map payloadNat) input skip r rs
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix))] at hmismatch'
  have hmismatch'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight)
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) := by
    simpa [choiceRight, List.append_assoc] using hmismatch'
  have hmatched : FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) .rejected := by
    cases hstate : c.state with
    | zero =>
        let remaining := capacity - 1
        have hcapacityEq : capacity = remaining + 1 := by
          dsimp [remaining]
          omega
        have h := ruleCursorMatchedTargetOneZero_firstStop
          (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++ ulogCore pcDone ::
            (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer)
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          (by simpa [hstate] using hmatch.1) htarget rscan.read_valid hwrite
          (by simpa [hstate, hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (by simpa [htarget] using
            (matchedWritePath_safe r rs
              (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
          (List.replicate remaining MStarConcreteAlphabet.work ++ suffix)
        simpa [ruleCursorResult, ruleCursorBase, hstate, hcapacityEq,
          hmatch.2.1, hmatch.2.2, List.replicate_succ,
          List.append_assoc] using h
    | succ extra =>
        have h := ruleCursorMatchedTargetOnePositive_firstStop
          (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++ ulogCore pcDone ::
            (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer)
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          extra (by simpa [hstate] using hmatch.1) htarget
          rscan.read_valid hwrite
          (by simpa [hstate, hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (by simpa [htarget] using
            (matchedWritePath_safe r rs
              (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix)
        simpa [ruleCursorResult, ruleCursorBase, hstate, hmatch.2.1,
          hmatch.2.2, List.append_assoc] using h
  have hsuffix := (hdynamic'.append hmismatch'').append
    ({ valid := hmatched.valid
       stop_free := hmatched.before } : StopFreeValidZeroRun
        hmatched.steps _ .rejected)
  have hsuffix' : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      .rejected :=
    hsuffix.toFirstHit hmatched.hit
  exact ⟨exactConcreteCycleOfChoiceHead choiceLeft (readHeadNat c.focus)
    choiceRight hhead hchoice' hsuffix'⟩

end PakFixedPolyomino.ULogActiveExactTargetOne
