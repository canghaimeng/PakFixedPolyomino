import PakFixedPolyomino.ULogAutomaticScanCertificates

/-! Semantic lookup branches with automatically generated scan certificates. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem automatic_lookup_some
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (rules : List ULogBytecode.RuleCode)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action) :
    ∃ skip r rs,
      rules = skip ++ r :: rs ∧
        MismatchCertificateList slot current actual programToHead runtime
          skip (r :: rs) ∧
        RuleScanCertificate slot current actual programToHead runtime r rs ∧
        RuleMatchesCursor slot current actual r ∧ r.action = action := by
  exact certifiedProgramScan_lookup_some slot current actual programToHead
    runtime
    (certifiedProgramScan_of_passive slot current actual hactual
      programToHead runtime hp hruntime rules hreads)
    action hlookup

theorem automatic_lookup_none
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none) :
    ∃ skip last,
      rules = skip ++ [last] ∧
        NoMatchCertificate slot current actual programToHead runtime
          skip last := by
  exact certifiedProgramScan_lookup_none slot current actual programToHead
    runtime
    (certifiedProgramScan_of_passive slot current actual hactual
      programToHead runtime hp hruntime rules hreads)
    hrules hlookup

theorem branchedCycle_semanticNoRule
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot = none) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      .rejected := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, last, heq, cert⟩ := automatic_lookup_none
    slot c.state c.focus hfocus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    hp hclock c.program hrules hreads hlookup
  have hreject := branchedCycle_dynamicCertifiedNoMatch_reject
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (c.right.map payloadNat) (payloadNatList_safe c.leftRev)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (ulogCore stateSep ::
      List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip last cert
  simpa [semanticCycleEncoding, stateWorkspace, heq,
    List.append_assoc] using hreject

end PakFixedPolyomino.ULogBootstrapExecution
