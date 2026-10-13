import PakFixedPolyomino.ULogAutomaticActionSafety

/-! Fully automatic semantic stay refinement for either target ordering. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_semanticLookupSome_stayAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .stay) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra := by
    exact hmatch.1.trans hstate
  apply branchedCycle_semanticStayAtMost c slot input clockZeros capacity
    runtime outer suffix skip r rs heq certs hmatch extra htarget hcapacity
    rscan.read_valid hwrite htargetLower hmove
  · simpa [hmatch.2.1] using rscan.source_corridor
  · exact matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  · exact matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  · exact matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
  · exact passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  · exact matchedCleanupClock_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp hwrite
  · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp

theorem branchedCycle_semanticLookupSome_stayAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .stay) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  apply branchedCycle_semanticStayAtLeast c slot input clockZeros capacity
    runtime outer suffix skip r rs heq certs hmatch growth htarget' hcapacity
    rscan.read_valid hwrite htargetLower hmove
  · simpa [hmatch.2.1] using rscan.source_corridor
  · exact matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  · exact matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  · exact matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
  · exact passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  · exact matchedCleanupClock_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp hwrite
  · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp

theorem branchedCycle_semanticLookupSome_stay
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (htargetCapacity : action.target ≤ capacity)
    (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .stay) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action)) := by
  by_cases hle : action.target ≤ c.state
  · obtain ⟨extra, hstate⟩ : ∃ extra, c.state = action.target + extra :=
      ⟨c.state - action.target, by omega⟩
    exact branchedCycle_semanticLookupSome_stayAtMost c slot action
      hlookup input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites extra hstate hstateCapacity htargetLower hmove
  · have hstateLe : c.state ≤ action.target := by omega
    obtain ⟨growth, htarget⟩ :
        ∃ growth, action.target = c.state + growth :=
      ⟨action.target - c.state, by omega⟩
    exact branchedCycle_semanticLookupSome_stayAtLeast c slot action
      hlookup input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites growth htarget htargetCapacity htargetLower hmove

end PakFixedPolyomino.ULogBootstrapExecution
