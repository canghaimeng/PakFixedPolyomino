import PakFixedPolyomino.ULogDynamicNoMatchRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem chooseSlot_dynamicCertifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last) :
    ∃ branchStart,
      oneStepAt (ULogBytecode.slotIndex slot)
          (.running .chooseSlot
            ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
                ulogCore pcMark :: outer,
              readHeadNat actual,
              runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) = branchStart ∧
        Reaches branchStart .rejected := by
  have hhead : choiceHead (readHeadNat actual) = true := by
    have hactual := cert.lastMismatch.actual_valid
    interval_cases actual <;> native_decide
  obtain ⟨branchStart, hbranch, hlookup⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot leftTape hleft
      (skip ++ [last]) (by simp) input outer (readHeadNat actual) hhead
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: suffix)
  have hreject := reaches_dynamicCertifiedNoMatch_reject slot current actual
    input leftTape runtime outer suffix skip last cert
  exact ⟨branchStart, hbranch, reaches_trans hlookup hreject⟩

theorem branchedCycle_dynamicCertifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape clockTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hclockTape : PayloadPathSafe clockTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter clockTape clockZeros runtime) skip last) :
    BranchedReaches slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩)
      .rejected := by
  have hhead : choiceHead (readHeadNat actual) = true := by
    have hactual := cert.lastMismatch.actual_valid
    interval_cases actual <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat actual) hhead
    clockZeros clockTape hclockTape
    (dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
      ulogCore pcMark :: outer)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  obtain ⟨branchStart, hbranch, hreject⟩ :=
    chooseSlot_dynamicCertifiedNoMatch_reject slot current actual input
      leftTape hleft (clockCellsAfter clockTape clockZeros runtime) outer
      suffix skip last cert
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
          ulogCore pcMark :: outer,
        readHeadNat actual,
        clockCellsAfter clockTape clockZeros runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩,
    branchStart, ?_, hbranch, hreject⟩
  simpa [clockCellsBefore, clockCellsAfter, List.append_assoc] using hdec

end PakFixedPolyomino.ULogBootstrapExecution
