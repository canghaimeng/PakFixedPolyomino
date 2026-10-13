import PakFixedPolyomino.ULogCertifiedNoMatchRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicCertifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (skip ++ [last]) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      .rejected := by
  have hcursor : Reaches
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ [last])) (skip ++ [last])
        (cursorDynamicProgramToHead input leftTape) runtime outer suffix)
      .rejected := by
    cases input with
    | nil =>
        apply reaches_certifiedNoMatch_reject slot current actual
          (cursorDynamicProgramToHead [] leftTape) runtime outer suffix
          skip last cert (ulogCore payloadStartOne)
          (leftTape.reverse ++ readHeadNat actual :: runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
        · simp [cursorDynamicProgramToHead, payloadProgramPrefix,
            List.append_assoc]
        · native_decide
        · native_decide
    | cons b bs =>
        apply reaches_certifiedNoMatch_reject slot current actual
          (cursorDynamicProgramToHead (b :: bs) leftTape) runtime outer suffix
          skip last cert (ulogCore payloadStartDone)
          (List.replicate bs.length (ulogCore payloadDone) ++
            ulogCore payloadEnd :: leftTape.reverse ++
              readHeadNat actual :: runtime ++
                List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)
        · simp [cursorDynamicProgramToHead, payloadProgramPrefix,
            List.reverse_append, List.append_assoc]
        · native_decide
        · native_decide
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip last [] runtime outer suffix] at hcursor
  exact hcursor

end PakFixedPolyomino.ULogBootstrapExecution
