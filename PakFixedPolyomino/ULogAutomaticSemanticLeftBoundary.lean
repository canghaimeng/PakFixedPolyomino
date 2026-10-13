import PakFixedPolyomino.ULogSemanticPathCount

/-! Fully automatic semantic left-boundary refinement for either target order. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_semanticLeftBoundaryAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hleft : c.leftRev = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity (MStarConcreteAlphabet.work :: outer) suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          (payloadNat action.write :: c.right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpEmpty : PassivePath (cursorDynamicProgramToHead input []) := by
    simpa [hleft] using hp
  have hclockPath := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclockPath c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]; exact htarget
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input [])
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    (by simpa [hleft] using certs) (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hwork : List.replicate growth MStarConcreteAlphabet.work ++
      (List.replicate (capacity - r.action.target)
        MStarConcreteAlphabet.work ++ suffix) =
    List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
      suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hdec := reaches_clockDecrementCells (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    (dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++
          List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix)
  obtain ⟨branchStart, hbranch, hlookupRun⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot [] (by simp [PayloadPathSafe])
      (skip ++ r :: rs) (by simp) input (MStarConcreteAlphabet.work :: outer)
      (readHeadNat c.focus) hhead
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
              List.replicate (capacity - r.action.target)
                MStarConcreteAlphabet.work ++ suffix)
  have hsplit := cursorDynamicProgramToHead_emptyLeft_split input
  have hreadSafe := matchedReadPath_safe r.slot r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have hwriteSafe := matchedWritePath_safe r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have htargetSafe := matchedTargetPath_safe r hwrite rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclockPath
  have hscanSafe := passivePath_move (cursorMatchedMovePath_passive rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hcleanupClock := matchedCleanupClock_leftInternal_safe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty 2
  have hcleanupProgram := cursorCleanupProgramPath_restoreHeadSafe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hsplit, cursorMatchedMovePath, List.append_assoc]
  rw [hmoveSplit] at hcleanupClock hcleanupProgram
  have hrule := reaches_dynamicMismatchPrefix_matchedAtLeast_leftBoundary_general
    slot c.state c.focus input
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch growth
    htarget' rscan.read_valid hwrite htargetLower hmove hboundary
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by simpa [hleft] using hreadSafe)
    (by simpa [hleft] using hwriteSafe)
    (by simpa [hleft] using htargetSafe)
    (by simpa [hleft] using hscanSafe)
    (matchedLeftBoundary_shift_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input))
    (matchedLeftBoundary_return_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input)
      (leftBoundaryMarker input) (leftBoundaryMarker_passive input))
    (by
      have hblank : readHeadNat 2 = ulogCore payloadHeadBlank := by native_decide
      simpa [hblank, List.append_assoc] using hcleanupClock)
    (by simpa [List.append_assoc] using hcleanupProgram)
  have hrun := reaches_trans hlookupRun
    (by simpa only [List.cons_append, List.append_assoc] using hrule)
  rw [unhead_writeHeadNat] at hrun
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
          ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
        readHeadNat c.focus,
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++
                List.replicate (capacity - r.action.target)
                  MStarConcreteAlphabet.work ++ suffix⟩,
    branchStart, ?_, hbranch, ?_⟩
  · have hdec' := hdec
    have hstartRight := congrArg
      (fun ws =>
        clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: ws) hwork.symm
    have hstartRight' :
        clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
            stateWorkspace capacity c.state suffix =
          clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
                List.replicate c.state (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++
            (List.replicate (capacity - r.action.target)
              MStarConcreteAlphabet.work ++ suffix) := by
      simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
        hstartRight
    simp only [semanticCycleEncoding]
    rw [heq, hleft]
    simp only [List.map_nil]
    rw [hstartRight']
    simpa only [clockCellsBefore, clockCellsAfter, List.nil_append,
      List.cons_append, List.append_assoc] using hdec'
  · have hrun' : Reaches branchStart
        (.running .cycleStart
          ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
              ulogCore pcMark :: outer,
            ulogCore payloadHeadBlank,
            clockCellsAfter
                (payloadNat r.action.write :: c.right.map payloadNat)
                clockZeros runtime ++
              stateWorkspace capacity r.action.target suffix⟩) := by
      simpa [clockCellsAfter, stateWorkspace, List.append_assoc] using hrun
    simpa [semanticCycleEncoding, heq, hleft, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
      List.append_assoc] using hrun'

theorem branchedCycle_semanticLeftBoundary
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hleft : c.leftRev = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (htargetCapacity : action.target ≤ capacity)
    (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity (MStarConcreteAlphabet.work :: outer) suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          (payloadNat action.write :: c.right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  by_cases hle : action.target ≤ c.state
  · obtain ⟨extra, hstate⟩ : ∃ extra, c.state = action.target + extra :=
      ⟨c.state - action.target, by omega⟩
    exact branchedCycle_semanticLeftBoundaryAtMost c slot action hlookup
      hleft input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites extra hstate hstateCapacity htargetLower hmove
  · obtain ⟨growth, htarget⟩ :
        ∃ growth, action.target = c.state + growth :=
      ⟨action.target - c.state, by omega⟩
    exact branchedCycle_semanticLeftBoundaryAtLeast c slot action hlookup
      hleft input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites growth htarget htargetCapacity htargetLower hmove

end PakFixedPolyomino.ULogBootstrapExecution
