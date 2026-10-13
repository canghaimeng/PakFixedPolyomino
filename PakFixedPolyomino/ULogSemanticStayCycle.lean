import PakFixedPolyomino.ULogSemanticConfigEncoding

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem branchedCycle_semanticStayAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hprogramEq : c.program = skip ++ r :: rs)
    (certs : MismatchCertificateList slot c.state c.focus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot c.state c.focus r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hcapacity : c.state ≤ capacity)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (readHeadNat r.read)
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input
              (c.leftRev.map payloadNat)))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input
              (c.leftRev.map payloadNat))))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) ++
        writeHeadNat r.action.write ::
          clockCellsAfter (c.right.map payloadNat) clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input
                  (c.leftRev.map payloadNat)))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)))) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c r.action)) := by
  have hcycle := branchedCycle_certifiedFirstMatchAtMost_stay
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (c.right.map payloadNat) (payloadNatList_safe c.leftRev)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs certs hmatch extra htarget hread hwrite htargetLower hmove hcorridor
    hreadPath hwritePath htargetPath hscan hrestoreClock hprogram
  have hsourceState : r.source = c.state := hmatch.1
  have hworkspace := stateWorkspace_atMost capacity r.source
    r.action.target extra htarget (by omega)
    suffix
  have hout :
      List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix =
        stateWorkspace capacity r.action.target suffix := by
    rw [hsourceState] at hworkspace
    simpa [List.append_assoc] using hworkspace
  have hright := congrArg
    (fun xs => clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      xs) hout
  have hright' :
      clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
              (List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity r.action.target suffix := by
    simpa only [List.append_assoc] using hright
  rw [hright'] at hcycle
  simpa [semanticCycleEncoding, stateWorkspace, hprogramEq, hmove,
    ULogSemantics.applyAction, hsourceState, List.append_assoc] using hcycle

end PakFixedPolyomino.ULogBootstrapExecution
