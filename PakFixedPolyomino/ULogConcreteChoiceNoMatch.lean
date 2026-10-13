import PakFixedPolyomino.ULogConcreteChoiceLookupUnderflow
import PakFixedPolyomino.ULogActiveExactNoRule

/-! NONE semantic lookup from choiceStart, then mixed BOTH-slot
capacity and RIGHT shortage. Central joints are propositions. -/

namespace PakFixedPolyomino.ULogConcreteChoiceNoMatch

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open ULogBytecode (RuleCode ActionCode)
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)
open ULogConcreteChoiceLookupUnderflow
open ULogConcreteLookupUnderflow (clockCons_passive)
open ULogConcreteRightBoundaryUnderflow (no_choice_before)

noncomputable def noMatchWitness
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none)
    (input : List Bool) (leftTape runtime : List Tape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) :
    Σ skip last, PLift
      (rules = skip ++ [last] ∧
        NoMatchCertificate slot current actual
          (cursorDynamicProgramToHead input leftTape) runtime skip last) :=
  Classical.choice <| by
    obtain ⟨skip, last, h⟩ :=
      automatic_lookup_none slot current actual hactual
        (cursorDynamicProgramToHead input leftTape) runtime hp hruntime
        rules hrules hreads hlookup
    exact ⟨⟨skip, last, ⟨h⟩⟩⟩

noncomputable def choice_no_match_firstHit
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (available : Nat) :
    ExactNoMatchBranchWitness slot
      (choiceStart rules input leftTape runtime outer current actual
        available) := by
  obtain ⟨skip, last, hw⟩ :=
    noMatchWitness slot current actual hactual rules hrules hreads hlookup
      input leftTape runtime hp hruntime
  rcases hw.down with ⟨heq, cert⟩
  subst heq
  cases input with
  | nil =>
      simpa [choiceStart] using
        ULogActiveExactNoRule.chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
          slot current actual [] leftTape hleft runtime outer
          (ulogCore stateSep ::
            List.replicate available MStarConcreteAlphabet.work)
          skip last cert (ulogCore payloadStartOne)
          (leftTape.reverse ++ readHeadNat actual :: runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate available MStarConcreteAlphabet.work)
          (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
            List.append_assoc]) (by decide) (by decide)
  | cons b bs =>
      simpa [choiceStart] using
        ULogActiveExactNoRule.chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
          slot current actual (b :: bs) leftTape hleft runtime outer
          (ulogCore stateSep ::
            List.replicate available MStarConcreteAlphabet.work)
          skip last cert (ulogCore payloadStartDone)
          (List.replicate bs.length (ulogCore payloadDone) ++
            ulogCore payloadEnd :: leftTape.reverse ++
              readHeadNat actual :: runtime ++
                List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep ::
                    List.replicate available MStarConcreteAlphabet.work)
          (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
            List.reverse_append, List.append_assoc])
          (by decide) (by decide)

theorem no_accepting_choice_no_match
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (available : Nat)
    (rest : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (choiceStart rules input leftTape runtime outer current actual
        available)
      (ULogBytecode.slotIndex slot :: rest) (.accepted tape) → False := by
  intro raw
  cases raw with
  | cons start next finish label labels hedge htail =>
    let w :=
      choice_no_match_firstHit slot current actual hactual rules hrules
        hreads hlookup input leftTape runtime outer hleft hp hruntime
        available
    have hnext : next = w.branchStart :=
      Option.some.inj <| hedge.symm.trans <|
        (choiceStart_validStep slot rules input leftTape runtime outer
          current actual available hactual).trans <| by
            simp [choiceBranch, w.branch_eq]
    have houtside :=
      selected_branch_outside
        (choiceStart_isChoice rules input leftTape runtime outer current
          actual available) hedge
    have noChoice :=
      no_choice_before w.first_hit.valid w.first_hit.before
        (hnext ▸ houtside)
    obtain ⟨_, _, fromRej⟩ :=
      zero_prefix_of_micro_accepting w.first_hit.valid noChoice
        (hnext ▸ htail)
    have halted := microPath_halted_start fromRej (by rfl)
    cases halted.2

theorem choice_no_match_spec
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (available : Nat) :
    validStepAt (ULogBytecode.slotIndex slot)
      (choiceStart rules input leftTape runtime outer current actual
        available) =
      some (choiceBranch slot rules input leftTape runtime outer current
        actual available) ∧
    (∃ n, Nonempty
        (FirstValidZeroHit IsConcreteCycleStop
          (choiceBranch slot rules input leftTape runtime outer current
            actual available) .rejected) ∧
      run n
        (choiceBranch slot rules input leftTape runtime outer current
          actual available) = .rejected) ∧
    (∀ (rest : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (choiceStart rules input leftTape runtime outer current actual
          available)
        (ULogBytecode.slotIndex slot :: rest) (.accepted tape) →
          False) := by
  refine ⟨choiceStart_validStep slot rules input leftTape runtime outer
      current actual available hactual, ?_,
    no_accepting_choice_no_match slot current actual hactual rules hrules
      hreads hlookup input leftTape runtime outer hleft hp hruntime
      available⟩
  let w :=
    choice_no_match_firstHit slot current actual hactual rules hrules
      hreads hlookup input leftTape runtime outer hleft hp hruntime
      available
  refine ⟨w.first_hit.steps, ⟨⟨?_⟩, ?_⟩⟩
  · simpa [choiceBranch] using (w.branch_eq.symm ▸ w.first_hit)
  · have hr := w.first_hit.valid.eq_run
    simpa [choiceBranch] using (w.branch_eq.symm ▸ hr)

theorem choice_capacity_mixed_both_slots_spec
    (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (capacity : Nat)
    (hc : current ≤ capacity)
    (hboth : ∀ slot,
      ULogBytecode.lookupRule rules current actual slot = none ∨
        ∃ action,
          ULogBytecode.lookupRule rules current actual slot =
              some action ∧
            action.write < 3 ∧ capacity < action.target ∧
              2 ≤ action.target)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (choiceStart rules input leftTape runtime outer current actual
        (capacity - current))
      labels (.accepted tape) → False := by
  intro raw
  match labels with
  | [] =>
      cases microPath_nil_finish raw
  | label :: rest =>
      fin_cases label
      · rcases hboth false with hnone | hsome
        · exact no_accepting_choice_no_match false current actual hactual
            rules hrules hreads hnone input leftTape runtime outer hleft hp
            hruntime (capacity - current) rest tape raw
        · obtain ⟨action, hlookup, hwrite, ht, hT⟩ := hsome
          exact no_accepting_choice_capacity false current actual hactual
            rules hreads action hwrite hlookup input leftTape runtime outer
            hleft hp hruntime capacity hc ht hT rest tape raw
      · rcases hboth true with hnone | hsome
        · exact no_accepting_choice_no_match true current actual hactual
            rules hrules hreads hnone input leftTape runtime outer hleft hp
            hruntime (capacity - current) rest tape raw
        · obtain ⟨action, hlookup, hwrite, ht, hT⟩ := hsome
          exact no_accepting_choice_capacity true current actual hactual
            rules hreads action hwrite hlookup input leftTape runtime outer
            hleft hp hruntime capacity hc ht hT rest tape raw

theorem choice_right_mixed_both_slots_spec
    (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (input : List Bool) (leftTape outer pre : List Tape)
    (clkBound : Tape) (growth : Nat)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hpre : PassivePath pre)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne)
    (hboth : ∀ slot,
      ULogBytecode.lookupRule rules current actual slot = none ∨
        ∃ action,
          ULogBytecode.lookupRule rules current actual slot =
              some action ∧
            action.write < 3 ∧ action.target = current + growth ∧
              2 ≤ action.target ∧ action.move = .right)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (choiceStart rules input leftTape (clkBound :: pre) outer current
        actual growth)
      labels (.accepted tape) → False := by
  intro raw
  have hruntime := clockCons_passive clkBound hboundary hpre
  match labels with
  | [] =>
      cases microPath_nil_finish raw
  | label :: rest =>
      fin_cases label
      · rcases hboth false with hnone | hsome
        · exact no_accepting_choice_no_match false current actual hactual
            rules hrules hreads hnone input leftTape (clkBound :: pre) outer
            hleft hp hruntime growth rest tape raw
        · obtain ⟨action, hlookup, hwrite, htarget, hT, hmove⟩ := hsome
          exact no_accepting_choice_right false current actual hactual rules
            hreads action hwrite hlookup input leftTape outer pre clkBound
            growth hleft hp hpre htarget hT hmove hboundary rest tape raw
      · rcases hboth true with hnone | hsome
        · exact no_accepting_choice_no_match true current actual hactual
            rules hrules hreads hnone input leftTape (clkBound :: pre) outer
            hleft hp hruntime growth rest tape raw
        · obtain ⟨action, hlookup, hwrite, htarget, hT, hmove⟩ := hsome
          exact no_accepting_choice_right true current actual hactual rules
            hreads action hwrite hlookup input leftTape outer pre clkBound
            growth hleft hp hpre htarget hT hmove hboundary rest tape raw

end PakFixedPolyomino.ULogConcreteChoiceNoMatch
