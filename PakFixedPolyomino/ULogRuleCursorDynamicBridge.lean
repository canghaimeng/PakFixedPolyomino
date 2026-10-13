import PakFixedPolyomino.ULogRuleCursorBoundaryCleanup

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def cursorDynamicProgramToHead (input : List Bool)
    (leftTape : List Tape) : List Tape :=
  (payloadProgramPrefix input).reverse ++ leftTape.reverse

theorem cursorMatchedMovePath_dynamic (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (leftTape : List Tape) :
    cursorMatchedMovePath rs (cursorDynamicProgramToHead input leftTape) =
      dynamicMatchedRuleMovePath rs input leftTape := by
  simp [cursorMatchedMovePath, cursorDynamicProgramToHead,
    dynamicMatchedRuleMovePath, matchedRuleMovePath, List.append_assoc]

theorem dynamicRuleSourceStarted_eq_cursorResult
    (slot : Bool) (current actual : ℕ)
    (leftTape : List Tape) (input : List Bool)
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (runtime outer suffix : List Tape) :
    dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (cursorDynamicProgramToHead input leftTape) runtime outer suffix := by
  have henc : ULogBytecode.encodeRules (skip ++ r :: rs) ≠ [] :=
    encodeRules_ne_nil (by simp)
  have hlen : skip.length + (rs.length + 1) =
      (skip.length + rs.length) + 1 := by omega
  cases he : ULogBytecode.encodeRules (skip ++ r :: rs) with
  | nil => exact (henc he).elim
  | cons b bs =>
      cases input <;>
        simp [dynamicRuleSourceStarted, ruleCursorResult, initialRuleCursor,
          ruleCursorBase, cursorDynamicProgramToHead, atBitsTail, atBits,
          payloadProgramPrefix, he, hlen, List.replicate_succ,
          List.append_assoc]

theorem cursorDynamicProgramToHead_restored
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape) :
    (cursorDynamicProgramToHead input leftTape).map restoreProgramCell =
      cursorDynamicProgramToHead input leftTape := by
  have hleftRev : PayloadPathSafe leftTape.reverse := by
    intro x hx
    exact hleft x (by simpa using hx)
  simp [cursorDynamicProgramToHead, List.map_append, List.map_reverse,
    restoreProgramCell_payloadProgramPrefix,
    restoreProgramCell_payloadPath leftTape.reverse hleftRev]

theorem canonicalCursorCycleLeft_dynamic
    (rules : List ULogBytecode.RuleCode) (input : List Bool)
    (leftTape outer : List Tape) :
    canonicalCursorCycleLeft rules
        (cursorDynamicProgramToHead input leftTape) outer =
      dynamicRuleReturnPath leftTape rules input ++ ulogCore pcMark :: outer := by
  simp [canonicalCursorCycleLeft, cursorDynamicProgramToHead,
    dynamicRuleReturnPath, ruleReturnPath, List.reverse_append,
    codeTape, List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
