import PakFixedPolyomino.ULogLastRuleUnifiedRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

structure NoMatchCertificate (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (last : ULogBytecode.RuleCode) : Prop where
  mismatches : MismatchCertificateList slot current actual programToHead runtime
    skip [last]
  lastMismatch : RuleMismatchCertificate slot current actual programToHead runtime
    last []

theorem reaches_certifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual programToHead runtime
      skip last)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ [last])) (skip ++ [last])
        programToHead runtime outer suffix)
      .rejected := by
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead runtime cert.mismatches (by simp)
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer suffix trace
  have hboundary :
      (canonicalRuleCursor skip [last]).boundary = sourceBoundary ∨
        (canonicalRuleCursor skip [last]).boundary = sourceBoundaryZero ∨
          (canonicalRuleCursor skip [last]).boundary = sourceBoundaryOne :=
    boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hlast := reaches_ruleCursorResult_lastMismatch_reject
    slot current actual (canonicalRuleCursor skip [last]) last
    programToHead runtime outer suffix cert.lastMismatch.actual_valid
    (canonicalRuleCursor_path_safe skip [last]) hboundary
    cert.lastMismatch.mismatch cert.lastMismatch.read_valid
    cert.lastMismatch.source_corridor cert.lastMismatch.read_boundary_free
    cert.lastMismatch.read_scan cert.lastMismatch.read_restore
    cert.lastMismatch.slot_scan cert.lastMismatch.slot_restore
    cert.lastMismatch.program_restore
    after right hafter hzero hone
  exact reaches_trans hprefix hlast

end PakFixedPolyomino.ULogBootstrapExecution
