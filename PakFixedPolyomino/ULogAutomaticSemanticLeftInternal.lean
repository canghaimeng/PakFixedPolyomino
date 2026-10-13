import PakFixedPolyomino.ULogCertifiedFirstMatchLeftInternalAtLeast

/-! Fully automatic semantic refinement for internal left moves. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_semanticLeftInternalAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (leftTail : List ℕ) (hleft : c.leftRev = next :: leftTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          (payloadNat action.write :: c.right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpTail := cursorDynamicProgramToHead_passive input leftTail
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra := hmatch.1.trans hstate
  have hreadSafe := matchedReadPath_safe r.slot r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have hwriteSafe := matchedWritePath_safe r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have htargetSafe := matchedTargetPath_safe r hwrite rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
  have hscanSafe := passivePath_move (cursorMatchedMovePath_passive rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hcycle := branchedCycle_certifiedFirstMatchAtMost_leftInternal
    slot c.state c.focus input (payloadNat next) (leftTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: leftTail) x hx)
    (c.right.map payloadNat) (payloadNatList_safe c.right)
    clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch extra htarget
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by simpa [hleft] using hreadSafe)
    (by simpa [hleft] using hwriteSafe)
    (by simpa [hleft] using htargetSafe)
    (by simpa [hleft] using hscanSafe)
    (matchedCleanupClock_leftInternal_safe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail next)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + (capacity - c.state) =
      capacity - r.action.target := by omega
  have hwork :
      List.replicate extra MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix) =
        List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightOut := congrArg
    (fun ws =>
      clockCellsAfter (payloadNat r.action.write :: c.right.map payloadNat)
          clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter (payloadNat r.action.write :: c.right.map payloadNat)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
        (List.replicate (capacity - c.state)
          MStarConcreteAlphabet.work ++ suffix) =
      clockCellsAfter (payloadNat r.action.write :: c.right.map payloadNat)
          clockZeros runtime ++ stateWorkspace capacity r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [unhead_writeHeadNat, hrightOut'] at hcycle
  simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
    ULogSemantics.applyAction, hleft, hsourceState, List.append_assoc] using
    hcycle

theorem branchedCycle_semanticLeftInternalAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (leftTail : List ℕ) (hleft : c.leftRev = next :: leftTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          (payloadNat action.write :: c.right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpTail := cursorDynamicProgramToHead_passive input leftTail
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]; exact htarget
  have hreadSafe := matchedReadPath_safe r.slot r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have hwriteSafe := matchedWritePath_safe r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have htargetSafe := matchedTargetPath_safe r hwrite rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
  have hscanSafe := passivePath_move (cursorMatchedMovePath_passive rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hcycle := branchedCycle_certifiedFirstMatchAtLeast_leftInternal
    slot c.state c.focus input (payloadNat next) (leftTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: leftTail) x hx)
    (c.right.map payloadNat) (payloadNatList_safe c.right)
    clockZeros runtime outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by simpa [hleft] using hreadSafe)
    (by simpa [hleft] using hwriteSafe)
    (by simpa [hleft] using htargetSafe)
    (by simpa [hleft] using hscanSafe)
    (matchedCleanupClock_leftInternal_safe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail next)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hwork :
      List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - c.state)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws =>
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightIn' :
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  rw [unhead_writeHeadNat, hrightIn'] at hcycle
  simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
    ULogSemantics.applyAction, hleft, hsourceState, List.append_assoc] using
    hcycle

theorem branchedCycle_semanticLeftInternal
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (leftTail : List ℕ) (hleft : c.leftRev = next :: leftTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (htargetCapacity : action.target ≤ capacity)
    (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          (payloadNat action.write :: c.right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  by_cases hle : action.target ≤ c.state
  · obtain ⟨extra, hstate⟩ : ∃ extra, c.state = action.target + extra :=
      ⟨c.state - action.target, by omega⟩
    exact branchedCycle_semanticLeftInternalAtMost c slot action hlookup
      next leftTail hleft input clockZeros capacity runtime outer suffix
      hruntime hfocus hreads hwrites extra hstate hstateCapacity htargetLower hmove
  · obtain ⟨growth, htarget⟩ :
        ∃ growth, action.target = c.state + growth :=
      ⟨action.target - c.state, by omega⟩
    exact branchedCycle_semanticLeftInternalAtLeast c slot action hlookup
      next leftTail hleft input clockZeros capacity runtime outer suffix
      hruntime hfocus hreads hwrites growth htarget htargetCapacity htargetLower hmove

end PakFixedPolyomino.ULogBootstrapExecution
