import PakFixedPolyomino.ULogConcreteLookupUnderflow

/-! Labelled chooseSlot edge and dynamic return/count prefix onto lookup, then shortage. -/

namespace PakFixedPolyomino.ULogConcreteChoiceLookupUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open ULogBytecode (RuleCode ActionCode)
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)
open ULogConcreteLookupUnderflow
open ULogConcreteMatchedRowUnderflow
  (readHeadNat_headed stuck_exists reached_exists)
open ULogConcreteMatchedActionUnderflow (no_accepting_of_stuck)

def choiceStart (rules : List RuleCode) (input : List Bool)
    (leftTape runtime outer : List Tape) (current actual available : Nat) :
    Result :=
  .running .chooseSlot
    ⟨dynamicRuleReturnPath leftTape rules input ++ ulogCore pcMark :: outer,
      readHeadNat actual,
      runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work⟩

def choiceBranch (slot : Bool) (rules : List RuleCode) (input : List Bool)
    (leftTape runtime outer : List Tape) (current actual available : Nat) :
    Result :=
  oneStepAt (ULogBytecode.slotIndex slot)
    (choiceStart rules input leftTape runtime outer current actual available)

def choiceLookup (rules : List RuleCode) (slot : Bool) (input : List Bool)
    (leftTape runtime outer : List Tape) (current actual available : Nat) :
    Result :=
  lookupStart rules slot current actual
    (cursorDynamicProgramToHead input leftTape) runtime outer available

theorem choiceStart_isChoice (rules : List RuleCode) (input : List Bool)
    (leftTape runtime outer : List Tape) (current actual available : Nat) :
    IsConcreteChoice
      (choiceStart rules input leftTape runtime outer current actual
        available) := by
  simp [IsConcreteChoice, choiceStart]

theorem rules_ne_nil_of_lookup {rules : List RuleCode} {current actual : Nat}
    {slot : Bool} {action : ActionCode}
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action) :
    rules ≠ [] := by
  intro h
  subst h
  simp [ULogBytecode.lookupRule] at hlookup

theorem choice_oneStep (slot : Bool) (rules : List RuleCode)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (current actual available : Nat) (hactual : actual < 3) :
    choiceBranch slot rules input leftTape runtime outer current actual
      available =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath leftTape rules input) outer
          (ulogCore pcMark)
          (readHeadNat actual ::
            (runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate available MStarConcreteAlphabet.work))) := by
  have hhead := readHeadNat_headed hactual
  have hpne := dynamicRuleReturnPath_ne_nil leftTape rules input
  cases hpath : dynamicRuleReturnPath leftTape rules input with
  | nil => exact (hpne hpath).elim
  | cons x xs =>
      cases slot with
      | false =>
          simpa [choiceBranch, choiceStart, beforeLeftPath, hpath,
            ULogBytecode.slotIndex, List.append_assoc] using
            oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
              (xs ++ ulogCore pcMark :: outer) x
              (runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate available MStarConcreteAlphabet.work)
      | true =>
          simpa [choiceBranch, choiceStart, beforeLeftPath, hpath,
            ULogBytecode.slotIndex, List.append_assoc] using
            oneStepAt_chooseSlot_one (readHeadNat actual) hhead
              (xs ++ ulogCore pcMark :: outer) x
              (runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate available MStarConcreteAlphabet.work)

theorem choiceStart_validStep (slot : Bool) (rules : List RuleCode)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (current actual available : Nat) (hactual : actual < 3) :
    validStepAt (ULogBytecode.slotIndex slot)
      (choiceStart rules input leftTape runtime outer current actual
        available) =
      some (choiceBranch slot rules input leftTape runtime outer current
        actual available) := by
  simpa [choiceStart, choiceBranch] using
    validStepAt_chooseSlot slot
      (dynamicRuleReturnPath leftTape rules input ++
        ulogCore pcMark :: outer)
      (readHeadNat actual)
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work)
      (readHeadNat_headed hactual)

noncomputable def stopFree_choice_to_lookup
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (available : Nat) :
    Σ n, StopFreeValidZeroRun n
      (choiceBranch slot rules input leftTape runtime outer current actual
        available)
      (choiceLookup rules slot input leftTape runtime outer current actual
        available) := by
  have hrules := rules_ne_nil_of_lookup hlookup
  obtain ⟨skip, r, rs, hw⟩ :=
    lookupWitness slot current actual hactual rules hreads action hlookup
      (cursorDynamicProgramToHead input leftTape) runtime hp hruntime
  rcases hw.down with ⟨heq, _⟩
  obtain ⟨n, hrun⟩ :=
    stopFree_dynamicRuleSourceStarted slot leftTape hleft rules hrules input
      outer (readHeadNat actual)
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work)
  refine ⟨n, ?_⟩
  have hdest :
      dynamicRuleSourceStarted slot leftTape rules input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate available MStarConcreteAlphabet.work) =
      choiceLookup rules slot input leftTape runtime outer current actual
        available := by
    rw [heq]
    rw [dynamicRuleSourceStarted_eq_cursorResult slot current actual leftTape
      input skip r rs runtime outer
      (ulogCore stateSep ::
        List.replicate available MStarConcreteAlphabet.work)]
    simp [choiceLookup, lookupStart]
  rw [choice_oneStep slot rules input leftTape runtime outer current actual
    available hactual]
  rwa [← hdest]

noncomputable def stopFree_choice_capacity
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < action.target)
    (hT : 2 ≤ action.target) :
    Σ n, StopFreeValidZeroRun n
      (choiceBranch slot rules input leftTape runtime outer current actual
        (capacity - current)) .stuck := by
  obtain ⟨a, hpre⟩ :=
    stopFree_choice_to_lookup slot current actual hactual rules hreads
      action hlookup input leftTape runtime outer hleft hp hruntime
      (capacity - current)
  obtain ⟨b, hsuf⟩ :=
    stopFree_lookup_capacity slot current actual hactual rules hreads action
      hwrite hlookup (cursorDynamicProgramToHead input leftTape) runtime
      outer hp hruntime capacity hc ht hT
  simpa [choiceLookup] using ⟨a + b, hpre.append hsuf⟩

theorem no_accepting_choice_capacity
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < action.target)
    (hT : 2 ≤ action.target) (rest : List (Fin 2))
    (tape : Zipper Tape) :
    ConcreteMicroPath
      (choiceStart rules input leftTape runtime outer current actual
        (capacity - current))
      (ULogBytecode.slotIndex slot :: rest) (.accepted tape) → False := by
  intro raw
  cases raw with
  | cons start next finish label labels hedge htail =>
    have hnext :
        next = choiceBranch slot rules input leftTape runtime outer current
          actual (capacity - current) :=
      Option.some.inj <| hedge.symm.trans
        (choiceStart_validStep slot rules input leftTape runtime outer
          current actual (capacity - current) hactual)
    obtain ⟨n, hsf⟩ :=
      stopFree_choice_capacity slot current actual hactual rules hreads
        action hwrite hlookup input leftTape runtime outer hleft hp
        hruntime capacity hc ht hT
    exact no_accepting_of_stuck (hnext ▸ hsf)
      (selected_branch_outside
        (choiceStart_isChoice rules input leftTape runtime outer current
          actual (capacity - current)) hedge)
      rest tape htail

theorem choice_capacity_underflow_spec
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < action.target)
    (hT : 2 ≤ action.target) :
    validStepAt (ULogBytecode.slotIndex slot)
      (choiceStart rules input leftTape runtime outer current actual
        (capacity - current)) =
      some (choiceBranch slot rules input leftTape runtime outer current
        actual (capacity - current)) ∧
    choiceBranch slot rules input leftTape runtime outer current actual
      (capacity - current) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath leftTape rules input) outer
          (ulogCore pcMark)
          (readHeadNat actual ::
            (runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (capacity - current)
                  MStarConcreteAlphabet.work))) ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (choiceBranch slot rules input leftTape runtime outer current
            actual (capacity - current))
          (choiceLookup rules slot input leftTape runtime outer current
            actual (capacity - current))) ∧
      run n
        (choiceBranch slot rules input leftTape runtime outer current
          actual (capacity - current)) =
        choiceLookup rules slot input leftTape runtime outer current actual
          (capacity - current)) ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (choiceBranch slot rules input leftTape runtime outer current
            actual (capacity - current)) .stuck) ∧
      run n
        (choiceBranch slot rules input leftTape runtime outer current
          actual (capacity - current)) = .stuck) ∧
    (∀ (rest : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (choiceStart rules input leftTape runtime outer current actual
          (capacity - current))
        (ULogBytecode.slotIndex slot :: rest) (.accepted tape) → False) := by
  refine ⟨choiceStart_validStep slot rules input leftTape runtime outer
      current actual (capacity - current) hactual,
    choice_oneStep slot rules input leftTape runtime outer current actual
      (capacity - current) hactual, ?_, ?_, ?_⟩
  · obtain ⟨n, hsf⟩ :=
      stopFree_choice_to_lookup slot current actual hactual rules hreads
        action hlookup input leftTape runtime outer hleft hp hruntime
        (capacity - current)
    exact reached_exists hsf
  · obtain ⟨n, hsf⟩ :=
      stopFree_choice_capacity slot current actual hactual rules hreads
        action hwrite hlookup input leftTape runtime outer hleft hp
        hruntime capacity hc ht hT
    exact stuck_exists hsf
  · exact no_accepting_choice_capacity slot current actual hactual rules
      hreads action hwrite hlookup input leftTape runtime outer hleft hp
      hruntime capacity hc ht hT

theorem choice_capacity_both_slots_spec
    (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime) (capacity : Nat)
    (hc : current ≤ capacity)
    (hboth : ∀ slot, ∃ action,
      ULogBytecode.lookupRule rules current actual slot = some action ∧
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
      · obtain ⟨action, hlookup, hwrite, ht, hT⟩ := hboth false
        exact no_accepting_choice_capacity false current actual hactual
          rules hreads action hwrite hlookup input leftTape runtime outer
          hleft hp hruntime capacity hc ht hT rest tape raw
      · obtain ⟨action, hlookup, hwrite, ht, hT⟩ := hboth true
        exact no_accepting_choice_capacity true current actual hactual
          rules hreads action hwrite hlookup input leftTape runtime outer
          hleft hp hruntime capacity hc ht hT rest tape raw

noncomputable def stopFree_choice_right_to_penultimate
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape outer pre : List Tape)
    (clkBound : Tape) (growth : Nat)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hpre : PassivePath pre) (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    Σ skip r rs n,
      PLift (rules = skip ++ r :: rs ∧ r.action.write < 3 ∧
        r.action.target = r.source + growth) ×'
      StopFreeValidZeroRun n
        (choiceBranch slot rules input leftTape (clkBound :: pre) outer
          current actual growth)
        (lookupMovePenultimate skip r rs
          (cursorDynamicProgramToHead input leftTape) outer pre clkBound
          growth) := by
  obtain ⟨a, hpreRun⟩ :=
    stopFree_choice_to_lookup slot current actual hactual rules hreads
      action hlookup input leftTape (clkBound :: pre) outer hleft hp
      (clockCons_passive clkBound hboundary hpre) growth
  obtain ⟨skip, r, rs, b, ⟨hpile, hsuf⟩⟩ :=
    stopFree_lookup_right_to_penultimate slot current actual hactual rules
      hreads action hwrite hlookup
      (cursorDynamicProgramToHead input leftTape) outer pre clkBound growth
      hp hpre htarget hT hmove hboundary
  refine ⟨skip, r, rs, a + b, ⟨hpile, ?_⟩⟩
  simpa [choiceLookup] using hpreRun.append hsuf

noncomputable def stopFree_choice_right
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape outer pre : List Tape)
    (clkBound : Tape) (growth : Nat)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hpre : PassivePath pre) (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    Σ n, StopFreeValidZeroRun n
      (choiceBranch slot rules input leftTape (clkBound :: pre) outer
        current actual growth) .stuck := by
  obtain ⟨a, hpreRun⟩ :=
    stopFree_choice_to_lookup slot current actual hactual rules hreads
      action hlookup input leftTape (clkBound :: pre) outer hleft hp
      (clockCons_passive clkBound hboundary hpre) growth
  obtain ⟨b, hsuf⟩ :=
    stopFree_lookup_right slot current actual hactual rules hreads action
      hwrite hlookup (cursorDynamicProgramToHead input leftTape) outer pre
      clkBound growth hp hpre htarget hT hmove hboundary
  simpa [choiceLookup] using ⟨a + b, hpreRun.append hsuf⟩

theorem no_accepting_choice_right
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape outer pre : List Tape)
    (clkBound : Tape) (growth : Nat)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hpre : PassivePath pre) (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) (rest : List (Fin 2))
    (tape : Zipper Tape) :
    ConcreteMicroPath
      (choiceStart rules input leftTape (clkBound :: pre) outer current
        actual growth)
      (ULogBytecode.slotIndex slot :: rest) (.accepted tape) → False := by
  intro raw
  cases raw with
  | cons start next finish label labels hedge htail =>
    have hnext :
        next = choiceBranch slot rules input leftTape (clkBound :: pre)
          outer current actual growth :=
      Option.some.inj <| hedge.symm.trans
        (choiceStart_validStep slot rules input leftTape (clkBound :: pre)
          outer current actual growth hactual)
    obtain ⟨n, hsf⟩ :=
      stopFree_choice_right slot current actual hactual rules hreads action
        hwrite hlookup input leftTape outer pre clkBound growth hleft hp
        hpre htarget hT hmove hboundary
    exact no_accepting_of_stuck (hnext ▸ hsf)
      (selected_branch_outside
        (choiceStart_isChoice rules input leftTape (clkBound :: pre) outer
          current actual growth) hedge)
      rest tape htail

theorem choice_right_underflow_spec
    (slot : Bool) (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hreads : ∀ r ∈ rules, r.read < 3)
    (action : ActionCode) (hwrite : action.write < 3)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action)
    (input : List Bool) (leftTape outer pre : List Tape)
    (clkBound : Tape) (growth : Nat)
    (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hpre : PassivePath pre) (htarget : action.target = current + growth)
    (hT : 2 ≤ action.target) (hmove : action.move = .right)
    (hboundary : clkBound = ulogCore clockZero ∨
      clkBound = ulogCore clockOne) :
    validStepAt (ULogBytecode.slotIndex slot)
      (choiceStart rules input leftTape (clkBound :: pre) outer current
        actual growth) =
      some (choiceBranch slot rules input leftTape (clkBound :: pre) outer
        current actual growth) ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (choiceBranch slot rules input leftTape (clkBound :: pre) outer
            current actual growth)
          (choiceLookup rules slot input leftTape (clkBound :: pre) outer
            current actual growth)) ∧
      run n
        (choiceBranch slot rules input leftTape (clkBound :: pre) outer
          current actual growth) =
        choiceLookup rules slot input leftTape (clkBound :: pre) outer
          current actual growth) ∧
    (∃ skip r rs n,
      rules = skip ++ r :: rs ∧
        Nonempty
          (StopFreeValidZeroRun n
            (choiceBranch slot rules input leftTape (clkBound :: pre) outer
              current actual growth)
            (lookupMovePenultimate skip r rs
              (cursorDynamicProgramToHead input leftTape) outer pre
              clkBound growth)) ∧
        run n
          (choiceBranch slot rules input leftTape (clkBound :: pre) outer
            current actual growth) =
          lookupMovePenultimate skip r rs
            (cursorDynamicProgramToHead input leftTape) outer pre clkBound
            growth ∧
        oneStep
          (lookupMovePenultimate skip r rs
            (cursorDynamicProgramToHead input leftTape) outer pre clkBound
            growth) = .stuck) ∧
    (∃ n, Nonempty
        (StopFreeValidZeroRun n
          (choiceBranch slot rules input leftTape (clkBound :: pre) outer
            current actual growth) .stuck) ∧
      run n
        (choiceBranch slot rules input leftTape (clkBound :: pre) outer
          current actual growth) = .stuck) ∧
    (∀ (rest : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (choiceStart rules input leftTape (clkBound :: pre) outer current
          actual growth)
        (ULogBytecode.slotIndex slot :: rest) (.accepted tape) →
          False) := by
  refine ⟨choiceStart_validStep slot rules input leftTape (clkBound :: pre)
      outer current actual growth hactual, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hsf⟩ :=
      stopFree_choice_to_lookup slot current actual hactual rules hreads
        action hlookup input leftTape (clkBound :: pre) outer hleft hp
        (clockCons_passive clkBound hboundary hpre) growth
    exact reached_exists hsf
  · obtain ⟨skip, r, rs, nPen, ⟨⟨heq, hwriteR, htargetR⟩, hPen⟩⟩ :=
      stopFree_choice_right_to_penultimate slot current actual hactual rules
        hreads action hwrite hlookup input leftTape outer pre clkBound
        growth hleft hp hpre htarget hT hmove hboundary
    exact ⟨skip, r, rs, nPen, heq, ⟨⟨hPen⟩, hPen.valid.eq_run,
      lookup_right_penultimate_oneStep skip r rs
        (cursorDynamicProgramToHead input leftTape) outer pre clkBound
        growth hwriteR htargetR (shiftRuntimeSafe_of_passive hpre)⟩⟩
  · obtain ⟨n, hsf⟩ :=
      stopFree_choice_right slot current actual hactual rules hreads action
        hwrite hlookup input leftTape outer pre clkBound growth hleft hp
        hpre htarget hT hmove hboundary
    exact stuck_exists hsf
  · exact no_accepting_choice_right slot current actual hactual rules hreads
      action hwrite hlookup input leftTape outer pre clkBound growth hleft
      hp hpre htarget hT hmove hboundary

end PakFixedPolyomino.ULogConcreteChoiceLookupUnderflow
