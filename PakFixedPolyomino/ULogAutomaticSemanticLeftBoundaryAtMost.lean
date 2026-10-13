import PakFixedPolyomino.ULogDynamicCursorLeftBoundaryGeneralAtLeast

/-! Automatic semantic left-boundary refinement, shrinking target branch. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem leftBoundaryScanPrefix_passive (input : List Bool) :
    PassivePath (leftBoundaryScanPrefix input) := by
  cases input with
  | nil => simp [leftBoundaryScanPrefix, PassivePath]
  | cons b bs =>
      intro x hx
      simp only [leftBoundaryScanPrefix, List.mem_cons,
        List.mem_replicate] at hx
      rcases hx with rfl | hx
      · exact passiveCell_payloadStartDone
      · rw [hx.2]; exact passiveCell_payloadDone

theorem leftBoundaryMarker_passive (input : List Bool) :
    PassiveCell (leftBoundaryMarker input) := by
  cases input with
  | nil => exact passiveCell_payloadStartOne
  | cons b bs => exact passiveCell_payloadEnd

theorem matchedLeftBoundary_shift_safe_general
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (scanPrefix : List Tape)
    (hp : PassivePath scanPrefix) :
    ShiftRuntimeSafe
      ((cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
        [ulogCore pcMark]) := by
  have hbaseSafe : RestoreHeadSafe
      (cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs scanPrefix)) := by
    intro x hx
    rcases List.mem_append.mp hx with hpc | htail
    · exact cursorCleanupPcPath_restoreHeadSafe skip (r :: rs) x hpc
    · rcases List.mem_cons.mp htail with ht | hprogram
      · have hs := cursorCleanupTerminal_restoreHeadSafe skip
        exact hs x (by simpa [ht])
      · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs
          scanPrefix hp x hprogram
  intro x hx
  have heq : (cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse =
      (cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs scanPrefix)).reverse := by
    simp [List.reverse_append, List.append_assoc]
  rw [heq] at hx
  rcases List.mem_append.mp hx with hb | hmark
  · exact (hbaseSafe x (by simpa only [List.mem_reverse] using hb)).2
  · have hxm : x = ulogCore pcMark := by simpa using hmark
    rw [hxm]; decide

theorem matchedLeftBoundary_return_safe_general
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (scanPrefix : List Tape)
    (hp : PassivePath scanPrefix) (boundary : Tape)
    (hboundary : PassiveCell boundary) :
    ReturnMovedSafe
      (((cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [boundary]) := by
  have hbaseSafe : RestoreHeadSafe
      (cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs scanPrefix)) := by
    intro x hx
    rcases List.mem_append.mp hx with hpc | htail
    · exact cursorCleanupPcPath_restoreHeadSafe skip (r :: rs) x hpc
    · rcases List.mem_cons.mp htail with ht | hprogram
      · have hs := cursorCleanupTerminal_restoreHeadSafe skip
        exact hs x (by simpa [ht])
      · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs
          scanPrefix hp x hprogram
  intro x hx
  have heq : ((cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse =
      cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs scanPrefix) := by
    simp [List.reverse_append, List.append_assoc]
  rw [heq] at hx
  rcases List.mem_append.mp hx with hbBase | hb
  · exact (hbaseSafe x hbBase).1
  · have hxb : x = boundary := by simpa using hb
    rw [hxb]; exact hboundary.move.1

theorem branchedCycle_semanticLeftBoundaryAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hleft : c.leftRev = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
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
  have hclockPath := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclockPath c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra := hmatch.1.trans hstate
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input [])
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    (by simpa [hleft] using certs) (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    (dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  obtain ⟨branchStart, hbranch, hlookupRun⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot [] (by simp [PayloadPathSafe])
      (skip ++ r :: rs) (by simp) input (MStarConcreteAlphabet.work :: outer)
      (readHeadNat c.focus) hhead
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
              suffix)
  have hsplit := cursorDynamicProgramToHead_emptyLeft_split input
  have hreadSafe := matchedReadPath_safe r.slot r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have hwriteSafe := matchedWritePath_safe r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp
  have htargetSafe := matchedTargetPath_safe r hwrite rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp
    hclockPath
  have hscanSafe := passivePath_move (cursorMatchedMovePath_passive rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hpEmpty : PassivePath (cursorDynamicProgramToHead input []) := by
    simpa [hleft] using hp
  have hcleanupClock := matchedCleanupClock_leftInternal_safe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty 2
  have hcleanupProgram := cursorCleanupProgramPath_restoreHeadSafe
    skip r rs (cursorDynamicProgramToHead input []) hpEmpty
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hsplit, cursorMatchedMovePath, List.append_assoc]
  rw [hmoveSplit] at hcleanupClock hcleanupProgram
  have hrule := reaches_dynamicMismatchPrefix_matchedAtMost_leftBoundary_general
    slot c.state c.focus input
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch extra htarget
    rscan.read_valid hwrite htargetLower hmove hboundary
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
      have hblank : readHeadNat 2 = ulogCore payloadHeadBlank := by
        native_decide
      simpa [hblank, List.append_assoc] using hcleanupClock)
    (by simpa [List.append_assoc] using hcleanupProgram)
  have hrun := reaches_trans hlookupRun
    (by simpa [List.append_assoc] using hrule)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + (capacity - c.state) =
      capacity - r.action.target := by omega
  have hwork : List.replicate extra MStarConcreteAlphabet.work ++
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix) =
    List.replicate (capacity - r.action.target) MStarConcreteAlphabet.work ++
      suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightOut := congrArg
    (fun ws => unheadTape (writeHeadNat r.action.write) ::
      clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  rw [unhead_writeHeadNat] at hrightOut
  rw [show unheadTape (readHeadNat r.action.write) =
    payloadNat r.action.write by rfl] at hrun
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
          ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
        readHeadNat c.focus,
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix⟩,
    branchStart, ?_, hbranch, ?_⟩
  · simpa [semanticCycleEncoding, stateWorkspace, heq, hleft,
      clockCellsBefore, clockCellsAfter, List.append_assoc] using hdec
  · have hrightOut' :
        payloadNat r.action.write ::
            clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate extra MStarConcreteAlphabet.work ++
                    (List.replicate (capacity - c.state)
                      MStarConcreteAlphabet.work ++ suffix) =
          clockCellsAfter
              (payloadNat r.action.write :: c.right.map payloadNat)
              clockZeros runtime ++ stateWorkspace capacity
                r.action.target suffix := by
        simpa [clockCellsAfter, stateWorkspace, List.append_assoc] using
          hrightOut
    have hrun' : Reaches branchStart
        (.running .cycleStart
          ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
              ulogCore pcMark :: outer,
            ulogCore payloadHeadBlank,
            clockCellsAfter
                (payloadNat r.action.write :: c.right.map payloadNat)
                clockZeros runtime ++
              stateWorkspace capacity r.action.target suffix⟩) := by
      rw [← hrightOut']
      simpa [List.append_assoc] using hrun
    simpa [semanticCycleEncoding, heq, hleft, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode,
      readHeadNat, List.append_assoc] using hrun'

end PakFixedPolyomino.ULogBootstrapExecution
