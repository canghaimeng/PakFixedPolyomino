import PakFixedPolyomino.ULogCertifiedFirstMatchRightBoundaryAtLeast

/-! Fully automatic semantic right-boundary refinement for either target order. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_semanticRightBoundaryAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hright : c.right = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target < capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    BranchedReaches slot
      (semanticCycleEncoding input (clockCellsBefore [] clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input (clockCellsAfter [] clockZeros runtime)
        (capacity - 1) outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclockPath := clockCellsAfter_passive ([] : List ℕ) clockZeros
    runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter [] clockZeros runtime)
      hp hclockPath c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]; exact htarget
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have htailSafe := clockTailAfter_passive clockZeros runtime hruntime
  have hcycle := branchedCycle_certifiedFirstMatchAtLeast_rightBoundary
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) clockZeros runtime outer
    (List.replicate ((capacity - 1) - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hdecomp] using certs) hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hmatch.2.1, hdecomp] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter [] clockZeros runtime) hp hclockPath
      simpa [hdecomp] using ht)
    (passivePath_move (cursorMatchedMovePath_passive rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedRightBoundary_shift_safe (clockTailAfter clockZeros runtime)
      htailSafe r.action.target)
    (matchedRightBoundary_return_safe (clockBoundaryAfter clockZeros)
      (clockBoundaryAfter_valid clockZeros)
      (clockTailAfter clockZeros runtime) htailSafe r.action.target)
    (by
      have hc := matchedCleanupClock_rightInternal_safe skip r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by native_decide
      simpa [hblank] using hc)
    (matchedCleanupProgram_appendUnhead_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + 1 + ((capacity - 1) - r.action.target) := by omega
  have hwork : List.replicate growth MStarConcreteAlphabet.work ++
        MStarConcreteAlphabet.work ::
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
      List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix := by
    rw [show MStarConcreteAlphabet.work ::
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate 1 MStarConcreteAlphabet.work ++
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) by simp]
    rw [← List.append_assoc, ← List.replicate_add]
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws => clockCellsBefore [] clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightIn' :
      clockCellsBefore [] clockZeros runtime ++
            List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work ::
                List.replicate ((capacity - 1) - r.action.target)
                  MStarConcreteAlphabet.work ++ suffix =
        clockCellsBefore [] clockZeros runtime ++
          stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  rw [unhead_writeHeadNat] at hcycle
  simpa [semanticCycleEncoding, stateWorkspace, heq, hright, hmove,
    ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
    hsourceState, List.append_assoc, hwork, hrightIn, hrightIn'] using hcycle

theorem branchedCycle_semanticRightBoundary
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hright : c.right = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (htargetCapacity : action.target < capacity)
    (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    BranchedReaches slot
      (semanticCycleEncoding input (clockCellsBefore [] clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input (clockCellsAfter [] clockZeros runtime)
        (capacity - 1) outer suffix (ULogSemantics.applyAction c action)) := by
  by_cases hlt : action.target < c.state
  · obtain ⟨extra, hstate⟩ :
        ∃ extra, c.state = action.target + (extra + 1) :=
      ⟨c.state - action.target - 1, by omega⟩
    exact branchedCycle_semanticRightBoundaryAtMost c slot action hlookup
      hright input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites extra hstate hstateCapacity htargetLower hmove
  · obtain ⟨growth, htarget⟩ :
        ∃ growth, action.target = c.state + growth :=
      ⟨action.target - c.state, by omega⟩
    exact branchedCycle_semanticRightBoundaryAtLeast c slot action hlookup
      hright input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites growth htarget htargetCapacity htargetLower hmove

end PakFixedPolyomino.ULogBootstrapExecution
