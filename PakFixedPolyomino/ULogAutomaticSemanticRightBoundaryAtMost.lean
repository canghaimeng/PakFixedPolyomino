import PakFixedPolyomino.ULogAutomaticSemanticLeftBoundary

/-! Automatic semantic right-boundary refinement, shrinking target branch. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem clockTailAfter_passive (k : ℕ) (runtime : List Tape)
    (hruntime : PassivePath runtime) : PassivePath (clockTailAfter k runtime) := by
  have hfull := clockCellsAfter_passive ([] : List ℕ) k runtime hruntime
  have hdecomp := clockCellsAfter_nil_decompose k runtime
  intro x hx
  have hx' : x ∈ clockCellsAfter [] k runtime := by
    rw [hdecomp]
    simp [hx]
  exact hfull x (by simpa using hx')

theorem branchedCycle_semanticRightBoundaryAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hright : c.right = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + (extra + 1))
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore [] clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter [] clockZeros runtime)
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
  have htarget : r.source = r.action.target + (extra + 1) :=
    hmatch.1.trans hstate
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have htailSafe := clockTailAfter_passive clockZeros runtime hruntime
  have hcycle := branchedCycle_certifiedFirstMatchAtMost_rightBoundary
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hdecomp] using certs) hmatch extra htarget
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
  have hsum : extra + (capacity - c.state) =
      (capacity - 1) - r.action.target := by omega
  have hwork : List.replicate extra MStarConcreteAlphabet.work ++
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix) =
    List.replicate ((capacity - 1) - r.action.target)
      MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  rw [unhead_writeHeadNat] at hcycle
  have hrightOut := congrArg
    (fun ws => clockCellsAfter [] clockZeros runtime ++
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
        (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix) =
      clockCellsAfter [] clockZeros runtime ++
        stateWorkspace (capacity - 1) r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [hrightOut'] at hcycle
  simpa [semanticCycleEncoding, stateWorkspace, heq, hright, hmove,
    ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
    hsourceState, List.append_assoc] using hcycle

end PakFixedPolyomino.ULogBootstrapExecution
