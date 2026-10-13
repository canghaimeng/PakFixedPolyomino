import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Actual first-hit no-rule rejection, with kernel checked finite proofs.
The literal interpreter, input/clock/tape/capacity and arbitrary raw-cycle
quantifiers are preserved. No image certificate or native compiler axiom
is introduced. The original audited declarations remain unchanged. -/

namespace PakFixedPolyomino.ULogActiveExactNoRule
open ULogBootstrapExecution ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

noncomputable def chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last)
    (after : Tape) (right : List Tape)
    (hafter : cursorDynamicProgramToHead input leftTape ++
        readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    ExactNoMatchBranchWitness slot
      (.running .chooseSlot
        ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          runtime ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩) := by
  have hhead : choiceHead (readHeadNat actual) = true := by
    have hactual := cert.lastMismatch.actual_valid
    interval_cases actual <;> decide
  have htail := firstStop_dynamicCertifiedNoMatch_reject slot current actual
    input leftTape runtime outer suffix skip last cert after right hafter
    hzero hone
  obtain ⟨n, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ [last]) (by simp) input outer (readHeadNat actual)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hbranch :
      oneStepAt (ULogBytecode.slotIndex slot)
          (.running .chooseSlot
            ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
                ulogCore pcMark :: outer,
              readHeadNat actual,
              runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) =
        .running (.ruleSeekChoice slot)
          (beforeLeftPath
            (dynamicRuleReturnPath leftTape (skip ++ [last]) input) outer
            (ulogCore pcMark)
            (readHeadNat actual ::
              (runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ [last]) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ [last]) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x
                (runtime ++ List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)
        | true =>
            simpa [beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x
                (runtime ++ List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)
  have hdynamic' : StopFreeValidZeroRun n
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
              ulogCore pcMark :: outer,
            readHeadNat actual,
            runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ [last]) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
    rw [hbranch]
    exact hdynamic
  exact
    { branchStart := .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ [last]) input) outer
          (ulogCore pcMark)
          (readHeadNat actual ::
            (runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))
      branch_eq := hbranch
      first_hit := by
        rw [← hbranch]
        exact hdynamic'.appendFirstHit htail }

/-- A semantic no-rule lookup has a canonical exact concrete rejecting cycle
for either selected slot.  Its construction follows the target-one exact
cycle discipline: clock decrement to the first choice, one selected branch,
then a stop-free scan ending at the first rejecting stop. -/
theorem branchedCycle_semanticNoRule_exact_nonempty
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) .rejected) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, last, heq, cert⟩ := automatic_lookup_none
    slot c.state c.focus hfocus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    hp hclock c.program hrules hreads hlookup
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> decide
  let choiceLeft := dynamicRuleReturnPath (c.leftRev.map payloadNat)
    (skip ++ [last]) input ++ ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix
  have hchoice := clockDecrementCells_firstChoice (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    choiceLeft
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) := by
    simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
      clockCellsAfter, heq, choiceLeft, choiceRight,
      List.append_assoc] using hchoice
  have hselected : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      .rejected := by
    cases hinput : input with
    | nil =>
        obtain ⟨branchStart, hbranch, hreject⟩ :=
          chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
            slot c.state c.focus [] (c.leftRev.map payloadNat)
            (payloadNatList_safe c.leftRev)
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            outer (ulogCore stateSep ::
              List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
                suffix)
            skip last (by simpa [hinput] using cert)
            (ulogCore payloadStartOne)
            ((c.leftRev.map payloadNat).reverse ++ readHeadNat c.focus ::
              clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate (capacity - c.state)
                    MStarConcreteAlphabet.work ++ suffix)
            (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
              List.append_assoc]) (by decide) (by decide)
        have hbranch' :
            oneStepAt (ULogBytecode.slotIndex slot)
                (.running .chooseSlot
                  ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
              branchStart := by
          simpa [choiceLeft, choiceRight, hinput, List.append_assoc] using
            hbranch
        rw [hbranch']
        exact hreject
    | cons b bs =>
        obtain ⟨branchStart, hbranch, hreject⟩ :=
          chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
            slot c.state c.focus (b :: bs) (c.leftRev.map payloadNat)
            (payloadNatList_safe c.leftRev)
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            outer (ulogCore stateSep ::
              List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
                suffix)
            skip last (by simpa [hinput] using cert)
            (ulogCore payloadStartDone)
            (List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadEnd :: (c.leftRev.map payloadNat).reverse ++
                readHeadNat c.focus ::
                  clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
                List.replicate c.state (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep ::
                    List.replicate (capacity - c.state)
                      MStarConcreteAlphabet.work ++ suffix)
            (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
              List.reverse_append, List.append_assoc])
            (by decide) (by decide)
        have hbranch' :
            oneStepAt (ULogBytecode.slotIndex slot)
                (.running .chooseSlot
                  ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
              branchStart := by
          simpa [choiceLeft, choiceRight, hinput, List.append_assoc] using
            hbranch
        rw [hbranch']
        exact hreject
  exact ⟨exactConcreteCycleOfChoiceHead choiceLeft (readHeadNat c.focus)
    choiceRight hhead hchoice' hselected⟩

/-- First-hit cycle uniqueness forces every raw exact no-rule cycle from the
same semantic encoding to end in rejection. -/
theorem exactConcreteCycle_semanticNoRule_finish_eq_rejected
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none)
    {finish : Result}
    (raw : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) finish) :
    finish = .rejected := by
  obtain ⟨canonical⟩ := branchedCycle_semanticNoRule_exact_nonempty c slot
    input clockZeros capacity runtime outer suffix hruntime hfocus hrules
    hreads hlookup
  exact raw.finish_unique canonical

/-- A no-rule exact cycle cannot be followed by an accepting raw slot run. -/
theorem exactConcreteCycle_semanticNoRule_not_accepting_tail
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none)
    {next : Result} {slots : List Bool} {z : Zipper Tape}
    (cycle : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) next)
    (tail : ExactConcreteSlotRun next slots (.accepted z)) : False := by
  have hnext := exactConcreteCycle_semanticNoRule_finish_eq_rejected c slot
    input clockZeros capacity runtime outer suffix hruntime hfocus hrules
    hreads hlookup cycle
  subst next
  obtain ⟨-, hfinish⟩ := tail.eq_nil_of_concreteHalted_start (by
    simp [concreteHalted])
  cases hfinish

end PakFixedPolyomino.ULogActiveExactNoRule
