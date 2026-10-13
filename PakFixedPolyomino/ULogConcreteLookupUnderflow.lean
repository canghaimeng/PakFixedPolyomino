import PakFixedPolyomino.ULogConcreteMatchedRowUnderflow
import PakFixedPolyomino.ULogAutomaticActionSafety

/-! Actual semantic lookup before any row source comparison, internally
generated mismatch prefix, then matching-row shortage.
Central joints are propositions. -/

namespace PakFixedPolyomino.ULogConcreteLookupUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open ULogBytecode (RuleCode ActionCode)
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)
open ULogConcreteMatchedRowUnderflow
open ULogConcreteMatchedActionUnderflow
  (writePath targetCorridor no_accepting_of_stuck)

def lookupStart (rules : List RuleCode) (slot : Bool) (current actual : Nat)
    (programToHead runtime outer : List Tape) (available : Nat) : Result :=
  ruleCursorResult slot current actual (initialRuleCursor rules) rules
    programToHead runtime outer
    (ulogCore stateSep :: List.replicate available MStarConcreteAlphabet.work)

def matchingBase (c : RuleCursorData) (outer : List Tape) : List Tape :=
  (List.replicate c.done (ulogCore codeZero) ++
    ulogCore pcDone :: c.path).reverse ++ ulogCore pcMark :: outer

def lookupMovePenultimate (skip : List RuleCode) (r : RuleCode)
    (rs : List RuleCode) (programToHead outer pre : List Tape)
    (clkBound : Tape) (growth : Nat) : Result :=
  rowMovePenultimate r rs programToHead
    (matchingBase (canonicalRuleCursor skip (r :: rs)) outer) pre
    (canonicalRuleCursor skip (r :: rs)).boundary clkBound growth

theorem lookupStart_outside (rules : List RuleCode) (slot : Bool)
    (current actual : Nat) (programToHead runtime outer : List Tape)
    (available : Nat) :
    preChoiceResult
      (lookupStart rules slot current actual programToHead runtime outer
        available) = false := by
  unfold lookupStart ruleCursorResult
  generalize hbits : ULogBytecode.encodeRules rules = bits
  cases programToHead <;> cases bits <;>
    simp [atBitsTail, atBits, preChoiceResult, preChoice]

theorem matching_rowStart_eq {slot : Bool} {current actual : Nat}
    (c : RuleCursorData) (r : RuleCode) (rs : List RuleCode)
    (programToHead runtime outer : List Tape) (available : Nat)
    (hmatch : RuleMatchesCursor slot current actual r) :
    ruleCursorResult slot current actual c (r :: rs)
      programToHead runtime outer
      (ulogCore stateSep ::
        List.replicate available MStarConcreteAlphabet.work) =
      rowStart r rs programToHead (matchingBase c outer) runtime
        c.boundary available := by
  rcases hmatch with ⟨hs, hr, hslot⟩
  simp [ruleCursorResult, rowStart, ruleCursorBase, matchingBase, hs, hr,
    hslot]

theorem shiftRuntimeSafe_of_passive {pre : List Tape} (h : PassivePath pre) :
    ShiftRuntimeSafe pre :=
  fun x hx => (h x hx).move.2

theorem clockCons_passive (clkBound : Tape)
    (h : clkBound = ulogCore clockZero ∨ clkBound = ulogCore clockOne)
    {pre : List Tape} (hpre : PassivePath pre) :
    PassivePath (clkBound :: pre) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases h with hclk | hclk
    · rw [hclk]; exact passiveCell_clockZero
    · rw [hclk]; exact passiveCell_clockOne
  · exact hpre x hx

noncomputable def lookupWitness
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime) :
    Σ skip r rs, PLift
      (rules = skip ++ r :: rs ∧
        MismatchCertificateList slot current actual programToHead runtime
          skip (r :: rs) ∧
        RuleScanCertificate slot current actual programToHead runtime r rs ∧
        RuleMatchesCursor slot current actual r ∧ r.action = action) :=
  Classical.choice <| by
    obtain ⟨skip, r, rs, h⟩ :=
      automatic_lookup_some slot current actual hactual programToHead runtime
        hp hruntime rules hreads action hlookup
    exact ⟨⟨skip, r, rs, ⟨h⟩⟩⟩

noncomputable def stopFree_lookup_capacity
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead runtime outer : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (capacity : Nat) (hc : current ≤ capacity)
    (ht : capacity < action.target) (hT : 2 ≤ action.target) :
    Σ n, StopFreeValidZeroRun n
      (lookupStart rules slot current actual programToHead runtime outer
        (capacity - current)) .stuck := by
  obtain ⟨skip, r, rs, hw⟩ :=
    lookupWitness slot current actual hactual rules hreads action hlookup
      programToHead runtime hp hruntime
  rcases hw.down with ⟨heq, certs, rscan, hmatch, haction⟩
  rcases hmatch with ⟨hsrc, hr, hslot⟩
  have hmatch' : RuleMatchesCursor slot current actual r :=
    ⟨hsrc, hr, hslot⟩
  have hwriteR : r.action.write < 3 := by simpa [haction] using hwrite
  have hcR : r.source ≤ capacity := by simpa [hsrc] using hc
  have htR : capacity < r.action.target := by simpa [haction] using ht
  have hTR : 2 ≤ r.action.target := by simpa [haction] using hT
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        runtime) := by
    simpa [hr] using rscan.source_corridor
  have hrp : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)) := by
    simpa [hslot] using matchedReadPath_safe slot r rs programToHead hp
  have hwp : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)) := by
    simpa [writePath] using matchedWritePath_safe r rs programToHead hp
  have htp : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) runtime
        r.action.write) := by
    simpa [targetCorridor] using
      matchedTargetPath_safe r hwriteR rs programToHead runtime hp hruntime
  have havail : capacity - current = capacity - r.source := by simp [hsrc]
  let c := canonicalRuleCursor skip (r :: rs)
  obtain ⟨a, hpre⟩ :=
    stopFree_mismatchPrefix cursorMismatchStopFreeStep slot current actual
      programToHead runtime outer
      (ulogCore stateSep ::
        List.replicate (capacity - current) MStarConcreteAlphabet.work)
      (mismatchCertificateList_initial_trace slot current actual
        programToHead runtime certs (by simp))
  obtain ⟨b, hrow⟩ :=
    stopFree_row_capacity c.boundary hboundary r rs programToHead
      (matchingBase c outer) runtime capacity rscan.read_valid hwriteR hcR
      htR hTR hcorridor hrp hwp htp
  have hpre' : StopFreeValidZeroRun a
      (lookupStart rules slot current actual programToHead runtime outer
        (capacity - current))
      (rowStart r rs programToHead (matchingBase c outer) runtime
        c.boundary (capacity - r.source)) := by
    have hrun := hpre
    rw [matching_rowStart_eq c r rs programToHead runtime outer
      (capacity - current) hmatch'] at hrun
    rw [havail] at hrun
    simpa [lookupStart, heq, havail] using hrun
  exact ⟨a + b, hpre'.append hrow⟩

theorem no_accepting_lookup_capacity
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead runtime outer : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (capacity : Nat) (hc : current ≤ capacity)
    (ht : capacity < action.target) (hT : 2 ≤ action.target)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (lookupStart rules slot current actual programToHead runtime outer
        (capacity - current))
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_lookup_capacity slot current actual hactual rules hreads action
      hwrite hlookup programToHead runtime outer hp hruntime capacity hc ht
      hT
  exact no_accepting_of_stuck hsf
    (lookupStart_outside rules slot current actual programToHead runtime
      outer (capacity - current))
    labels tape raw

/-- Case A joint: internally chosen stopped run from the actual lookup
start to stuck, and ALL labelled acceptance exclusion. -/
theorem lookup_capacity_underflow_spec
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead runtime outer : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (capacity : Nat) (hc : current ≤ capacity)
    (ht : capacity < action.target) (hT : 2 ≤ action.target) :
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (lookupStart rules slot current actual programToHead runtime outer
            (capacity - current)) .stuck) ∧
      run n
        (lookupStart rules slot current actual programToHead runtime outer
          (capacity - current)) = .stuck) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (lookupStart rules slot current actual programToHead runtime outer
          (capacity - current))
        labels (.accepted tape) → False) := by
  obtain ⟨n, hsf⟩ :=
    stopFree_lookup_capacity slot current actual hactual rules hreads action
      hwrite hlookup programToHead runtime outer hp hruntime capacity hc ht
      hT
  exact ⟨stuck_exists hsf,
    no_accepting_lookup_capacity slot current actual hactual rules hreads
      action hwrite hlookup programToHead runtime outer hp hruntime capacity
      hc ht hT⟩

noncomputable def stopFree_lookup_right_to_penultimate
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead outer pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hp : PassivePath programToHead) (hpre : PassivePath pre)
    (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    Σ skip r rs n,
      PLift (rules = skip ++ r :: rs ∧ r.action.write < 3 ∧
        r.action.target = r.source + growth) ×'
      StopFreeValidZeroRun n
        (lookupStart rules slot current actual programToHead
          (clkBound :: pre) outer growth)
        (lookupMovePenultimate skip r rs programToHead outer pre clkBound
          growth) := by
  obtain ⟨skip, r, rs, hw⟩ :=
    lookupWitness slot current actual hactual rules hreads action hlookup
      programToHead (clkBound :: pre) hp
      (clockCons_passive clkBound hboundary hpre)
  rcases hw.down with ⟨heq, certs, rscan, hmatch, haction⟩
  rcases hmatch with ⟨hsrc, hr, hslot⟩
  have hmatch' : RuleMatchesCursor slot current actual r :=
    ⟨hsrc, hr, hslot⟩
  have hwriteR : r.action.write < 3 := by simpa [haction] using hwrite
  have htargetR : r.action.target = r.source + growth := by
    simpa [haction, hsrc] using htarget
  have hTR : 2 ≤ r.action.target := by simpa [haction] using hT
  have hmoveR : r.action.move = .right := by simpa [haction] using hmove
  have hsrcBound := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)) := by
    simpa [hr] using rscan.source_corridor
  have hrp : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)) := by
    simpa [hslot] using matchedReadPath_safe slot r rs programToHead hp
  have hwp : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)) := by
    simpa [writePath] using matchedWritePath_safe r rs programToHead hp
  have htp : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write) := by
    simpa [targetCorridor] using
      matchedTargetPath_safe r hwriteR rs programToHead (clkBound :: pre) hp
        (clockCons_passive clkBound hboundary hpre)
  have hscan :=
    passivePath_move (cursorMatchedMovePath_passive rs programToHead hp)
  have hshift := shiftRuntimeSafe_of_passive hpre
  let c := canonicalRuleCursor skip (r :: rs)
  obtain ⟨a, hpreRun⟩ :=
    stopFree_mismatchPrefix cursorMismatchStopFreeStep slot current actual
      programToHead (clkBound :: pre) outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work)
      (mismatchCertificateList_initial_trace slot current actual
        programToHead (clkBound :: pre) certs (by simp))
  obtain ⟨b, hrow⟩ :=
    stopFree_row_right_to_penultimate c.boundary hsrcBound r rs
      programToHead (matchingBase c outer) pre clkBound growth
      rscan.read_valid hwriteR htargetR hTR hmoveR hboundary hscan hshift
      hcorridor hrp hwp htp
  have hpre' : StopFreeValidZeroRun a
      (lookupStart rules slot current actual programToHead
        (clkBound :: pre) outer growth)
      (rowStart r rs programToHead (matchingBase c outer)
        (clkBound :: pre) c.boundary growth) := by
    have hrun := hpreRun
    rw [matching_rowStart_eq c r rs programToHead (clkBound :: pre) outer
      growth hmatch'] at hrun
    simpa [lookupStart, heq] using hrun
  refine ⟨skip, r, rs, a + b, ⟨⟨heq, hwriteR, htargetR⟩, ?_⟩⟩
  simpa [lookupMovePenultimate] using hpre'.append hrow

noncomputable def stopFree_lookup_right
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead outer pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hp : PassivePath programToHead) (hpre : PassivePath pre)
    (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    Σ n, StopFreeValidZeroRun n
      (lookupStart rules slot current actual programToHead
        (clkBound :: pre) outer growth) .stuck := by
  obtain ⟨skip, r, rs, hw⟩ :=
    lookupWitness slot current actual hactual rules hreads action hlookup
      programToHead (clkBound :: pre) hp
      (clockCons_passive clkBound hboundary hpre)
  rcases hw.down with ⟨heq, certs, rscan, hmatch, haction⟩
  rcases hmatch with ⟨hsrc, hr, hslot⟩
  have hmatch' : RuleMatchesCursor slot current actual r :=
    ⟨hsrc, hr, hslot⟩
  have hwriteR : r.action.write < 3 := by simpa [haction] using hwrite
  have htargetR : r.action.target = r.source + growth := by
    simpa [haction, hsrc] using htarget
  have hTR : 2 ≤ r.action.target := by simpa [haction] using hT
  have hmoveR : r.action.move = .right := by simpa [haction] using hmove
  have hsrcBound := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read)
        (clkBound :: pre)) := by
    simpa [hr] using rscan.source_corridor
  have hrp : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead)) := by
    simpa [hslot] using matchedReadPath_safe slot r rs programToHead hp
  have hwp : ActionWriteCorridorSafe
      (writePath r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)) := by
    simpa [writePath] using matchedWritePath_safe r rs programToHead hp
  have htp : TargetRewriteCorridorSafe
      (targetCorridor r.action.move
        (cursorMatchedMovePath rs programToHead) (clkBound :: pre)
        r.action.write) := by
    simpa [targetCorridor] using
      matchedTargetPath_safe r hwriteR rs programToHead (clkBound :: pre) hp
        (clockCons_passive clkBound hboundary hpre)
  have hscan :=
    passivePath_move (cursorMatchedMovePath_passive rs programToHead hp)
  have hshift := shiftRuntimeSafe_of_passive hpre
  let c := canonicalRuleCursor skip (r :: rs)
  obtain ⟨a, hpreRun⟩ :=
    stopFree_mismatchPrefix cursorMismatchStopFreeStep slot current actual
      programToHead (clkBound :: pre) outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work)
      (mismatchCertificateList_initial_trace slot current actual
        programToHead (clkBound :: pre) certs (by simp))
  obtain ⟨b, hrow⟩ :=
    stopFree_row_right c.boundary hsrcBound r rs programToHead
      (matchingBase c outer) pre clkBound growth rscan.read_valid hwriteR
      htargetR hTR hmoveR hboundary hscan hshift hcorridor hrp hwp htp
  have hpre' : StopFreeValidZeroRun a
      (lookupStart rules slot current actual programToHead
        (clkBound :: pre) outer growth)
      (rowStart r rs programToHead (matchingBase c outer)
        (clkBound :: pre) c.boundary growth) := by
    have hrun := hpreRun
    rw [matching_rowStart_eq c r rs programToHead (clkBound :: pre) outer
      growth hmatch'] at hrun
    simpa [lookupStart, heq] using hrun
  exact ⟨a + b, hpre'.append hrow⟩

theorem lookup_right_penultimate_oneStep
    (skip : List RuleCode) (r : RuleCode) (rs : List RuleCode)
    (programToHead outer pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hwrite : r.action.write < 3)
    (htarget : r.action.target = r.source + growth)
    (hshiftPre : ShiftRuntimeSafe pre) :
    oneStep
      (lookupMovePenultimate skip r rs programToHead outer pre clkBound
        growth) = .stuck := by
  simpa [lookupMovePenultimate] using
    row_right_penultimate_oneStep r rs programToHead
      (matchingBase (canonicalRuleCursor skip (r :: rs)) outer) pre
      (canonicalRuleCursor skip (r :: rs)).boundary clkBound growth hwrite
      htarget hshiftPre

theorem no_accepting_lookup_right
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead outer pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hp : PassivePath programToHead) (hpre : PassivePath pre)
    (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (lookupStart rules slot current actual programToHead
        (clkBound :: pre) outer growth)
      labels (.accepted tape) → False := by
  intro raw
  obtain ⟨n, hsf⟩ :=
    stopFree_lookup_right slot current actual hactual rules hreads action
      hwrite hlookup programToHead outer pre clkBound growth hp hpre
      htarget hT hmove hboundary
  exact no_accepting_of_stuck hsf
    (lookupStart_outside rules slot current actual programToHead
      (clkBound :: pre) outer growth)
    labels tape raw

/-- Case B joint: internally selected matching row, reached changed
penultimate, oneStep stuck, stopped run to stuck, and ALL labelled
acceptance exclusion from the actual lookup start. -/
theorem lookup_right_underflow_spec
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (programToHead outer pre : List Tape) (clkBound : Tape) (growth : Nat)
    (hp : PassivePath programToHead) (hpre : PassivePath pre)
    (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    (∃ skip r rs n,
      rules = skip ++ r :: rs ∧
        Nonempty
          (StopFreeValidZeroRun n
            (lookupStart rules slot current actual programToHead
              (clkBound :: pre) outer growth)
            (lookupMovePenultimate skip r rs programToHead outer pre
              clkBound growth)) ∧
        run n
          (lookupStart rules slot current actual programToHead
            (clkBound :: pre) outer growth) =
          lookupMovePenultimate skip r rs programToHead outer pre clkBound
            growth ∧
        oneStep
          (lookupMovePenultimate skip r rs programToHead outer pre clkBound
            growth) = .stuck) ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (lookupStart rules slot current actual programToHead
            (clkBound :: pre) outer growth) .stuck) ∧
      run n
        (lookupStart rules slot current actual programToHead
          (clkBound :: pre) outer growth) = .stuck) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (lookupStart rules slot current actual programToHead
          (clkBound :: pre) outer growth)
        labels (.accepted tape) → False) := by
  obtain ⟨skip, r, rs, nPen, ⟨⟨heq, hwriteR, htargetR⟩, hPen⟩⟩ :=
    stopFree_lookup_right_to_penultimate slot current actual hactual rules
      hreads action hwrite hlookup programToHead outer pre clkBound growth
      hp hpre htarget hT hmove hboundary
  obtain ⟨nSt, hSt⟩ :=
    stopFree_lookup_right slot current actual hactual rules hreads action
      hwrite hlookup programToHead outer pre clkBound growth hp hpre
      htarget hT hmove hboundary
  exact ⟨⟨skip, r, rs, nPen, heq, ⟨⟨hPen⟩, hPen.valid.eq_run,
      lookup_right_penultimate_oneStep skip r rs programToHead outer pre
        clkBound growth hwriteR htargetR
        (shiftRuntimeSafe_of_passive hpre)⟩⟩,
    ⟨stuck_exists hSt,
      no_accepting_lookup_right slot current actual hactual rules hreads
        action hwrite hlookup programToHead outer pre clkBound growth hp
        hpre htarget hT hmove hboundary⟩⟩

end PakFixedPolyomino.ULogConcreteLookupUnderflow
