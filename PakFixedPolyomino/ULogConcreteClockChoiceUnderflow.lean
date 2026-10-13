import PakFixedPolyomino.ULogConcreteChoiceNoMatch

/-! Actual first-choice clock prefix from cycleStart onto choiceStart, then mixed BOTH-slot shortage for every raw word. -/

namespace PakFixedPolyomino.ULogConcreteClockChoiceUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open ULogBytecode (RuleCode ActionCode)
open MStarParserExecution (Zipper)
open OneTapeTableau (Move)
open ULogConcreteChoiceLookupUnderflow
open ULogConcreteChoiceNoMatch
open ULogConcreteLookupUnderflow (clockCons_passive)

def cycleStart (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload runtime outer : List Tape)
    (current actual zeros available : Nat) : Result :=
  .running .cycleStart
    ⟨dynamicRuleReturnPath leftTape rules input ++ ulogCore pcMark :: outer,
      readHeadNat actual,
      clockCellsBefore clockPayload zeros runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate available MStarConcreteAlphabet.work⟩

def postClock (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload runtime outer : List Tape)
    (current actual zeros available : Nat) : Result :=
  choiceStart rules input leftTape
    (clockCellsAfter clockPayload zeros runtime) outer current actual
    available

def cycleStartZeroClock (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload outer suffix : List Tape)
    (actual width : Nat) : Result :=
  .running .cycleStart
    ⟨dynamicRuleReturnPath leftTape rules input ++ ulogCore pcMark :: outer,
      readHeadNat actual,
      clockPayload ++ List.replicate width (ulogCore clockZero) ++
        ulogCore clockSep :: suffix⟩

theorem choiceHead_of_actual {actual : Nat} (hactual : actual < 3) :
    choiceHead (readHeadNat actual) = true := by
  interval_cases actual <;> decide

theorem clockOnesZero_passive (zeros : Nat) {runtime : List Tape}
    (hruntime : PassivePath runtime) :
    PassivePath
      (List.replicate zeros (ulogCore clockOne) ++
        ulogCore clockZero :: runtime) := by
  apply passivePath_append
  · intro cell hcell
    have heq : cell = ulogCore clockOne :=
      (by simpa only [List.mem_replicate] using hcell :
        zeros ≠ 0 ∧ cell = ulogCore clockOne).2
    rw [heq]
    exact passiveCell_clockOne
  · intro cell hcell
    rcases List.mem_cons.mp hcell with rfl | hcell
    · exact passiveCell_clockZero
    · exact hruntime cell hcell

theorem clockAfter_passive {payload : List Tape}
    (hsafe : PayloadPathSafe payload) (k : Nat) {runtime : List Tape}
    (hruntime : PassivePath runtime) :
    PassivePath (clockCellsAfter payload k runtime) := by
  unfold clockCellsAfter
  apply passivePath_append
  · apply passivePath_append
    · intro x hx
      rcases hsafe x hx with h0 | h1 | hb
      · rw [h0]; exact passiveCell_payloadTape false
      · rw [h1]; exact passiveCell_payloadTape true
      · rw [hb]; exact passiveCell_payloadBlank
    · intro x hx
      have heq : x = ulogCore clockOne :=
        (by simpa only [List.mem_replicate] using hx :
          k ≠ 0 ∧ x = ulogCore clockOne).2
      rw [heq]; exact passiveCell_clockOne
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact passiveCell_clockZero
    · exact hruntime x hx

theorem clockAfter_empty_zero (runtime : List Tape) :
    clockCellsAfter [] 0 runtime = ulogCore clockZero :: runtime := by
  simp [clockCellsAfter]

theorem clockAfter_empty_succ (n : Nat) (runtime : List Tape) :
    clockCellsAfter [] (n + 1) runtime =
      ulogCore clockOne ::
        (List.replicate n (ulogCore clockOne) ++
          ulogCore clockZero :: runtime) := by
  simp [clockCellsAfter, List.replicate_succ]

noncomputable def cycle_first_choice
    (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload runtime outer : List Tape)
    (current actual zeros available : Nat) (hactual : actual < 3)
    (hpayload : PayloadPathSafe clockPayload) :
    FirstValidZeroHit IsConcreteChoice
      (cycleStart rules input leftTape clockPayload runtime outer current
        actual zeros available)
      (postClock rules input leftTape clockPayload runtime outer current
        actual zeros available) := by
  simpa [cycleStart, postClock, choiceStart, clockCellsBefore,
    clockCellsAfter, List.append_assoc] using
    clockDecrementCells_firstChoice (readHeadNat actual)
      (choiceHead_of_actual hactual) zeros clockPayload hpayload
      (dynamicRuleReturnPath leftTape rules input ++
        ulogCore pcMark :: outer)
      (runtime ++ List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work)

theorem cycle_first_choice_spec
    (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload runtime outer : List Tape)
    (current actual zeros available : Nat) (hactual : actual < 3)
    (hpayload : PayloadPathSafe clockPayload) :
    ∃ n, Nonempty
        (FirstValidZeroHit IsConcreteChoice
          (cycleStart rules input leftTape clockPayload runtime outer
            current actual zeros available)
          (postClock rules input leftTape clockPayload runtime outer
            current actual zeros available)) ∧
      run n
          (cycleStart rules input leftTape clockPayload runtime outer
            current actual zeros available) =
        postClock rules input leftTape clockPayload runtime outer current
          actual zeros available ∧
      ∀ (labels : List (Fin 2)) (tape : Zipper Tape),
        ConcreteMicroPath
          (cycleStart rules input leftTape clockPayload runtime outer
            current actual zeros available)
          labels (.accepted tape) →
          ∃ rest, labels = List.replicate n (0 : Fin 2) ++ rest ∧
            ConcreteMicroPath
              (postClock rules input leftTape clockPayload runtime outer
                current actual zeros available)
              rest (.accepted tape) := by
  let hit :=
    cycle_first_choice rules input leftTape clockPayload runtime outer
      current actual zeros available hactual hpayload
  refine ⟨hit.steps, ⟨⟨hit⟩, hit.valid.eq_run, ?_⟩⟩
  intro labels tape raw
  exact zero_prefix_of_micro_accepting hit.valid hit.before raw

theorem cycle_capacity_mixed_both_slots_spec
    (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (input : List Bool) (leftTape clockPayload runtime outer : List Tape)
    (zeros : Nat) (hleft : PayloadPathSafe leftTape)
    (hpayload : PayloadPathSafe clockPayload)
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
      (cycleStart rules input leftTape clockPayload runtime outer current
        actual zeros (capacity - current))
      labels (.accepted tape) → False := by
  intro raw
  let hit :=
    cycle_first_choice rules input leftTape clockPayload runtime outer
      current actual zeros (capacity - current) hactual hpayload
  obtain ⟨rest, _, hrest⟩ :=
    zero_prefix_of_micro_accepting hit.valid hit.before raw
  exact choice_capacity_mixed_both_slots_spec current actual hactual rules
    hrules hreads input leftTape
    (clockCellsAfter clockPayload zeros runtime) outer hleft hp
    (clockAfter_passive hpayload zeros hruntime) capacity hc hboth rest tape
    hrest

theorem cycle_right_mixed_both_slots_spec
    (current actual : Nat) (hactual : actual < 3)
    (rules : List RuleCode) (hrules : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (input : List Bool) (leftTape runtime outer : List Tape)
    (zeros growth : Nat) (hleft : PayloadPathSafe leftTape)
    (hp : PassivePath (cursorDynamicProgramToHead input leftTape))
    (hruntime : PassivePath runtime)
    (hboth : ∀ slot,
      ULogBytecode.lookupRule rules current actual slot = none ∨
        ∃ action,
          ULogBytecode.lookupRule rules current actual slot =
              some action ∧
            action.write < 3 ∧ action.target = current + growth ∧
              2 ≤ action.target ∧ action.move = .right)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath
      (cycleStart rules input leftTape [] runtime outer current actual
        zeros growth)
      labels (.accepted tape) → False := by
  intro raw
  let hit :=
    cycle_first_choice rules input leftTape [] runtime outer current
      actual zeros growth hactual (by simp [PayloadPathSafe])
  obtain ⟨rest, _, hrest⟩ :=
    zero_prefix_of_micro_accepting hit.valid hit.before raw
  cases zeros with
  | zero =>
      have hrest' :
          ConcreteMicroPath
            (choiceStart rules input leftTape
              (ulogCore clockZero :: runtime) outer current actual
              growth)
            rest (.accepted tape) := by
        simpa [postClock, clockAfter_empty_zero] using hrest
      exact choice_right_mixed_both_slots_spec current actual hactual
        rules hrules hreads input leftTape outer runtime
        (ulogCore clockZero) growth hleft hp hruntime (Or.inl rfl) hboth
        rest tape hrest'
  | succ n =>
      have hpre :
          PassivePath
            (List.replicate n (ulogCore clockOne) ++
              ulogCore clockZero :: runtime) :=
        clockOnesZero_passive n hruntime
      have hrest' :
          ConcreteMicroPath
            (choiceStart rules input leftTape
              (ulogCore clockOne ::
                (List.replicate n (ulogCore clockOne) ++
                  ulogCore clockZero :: runtime))
              outer current actual growth)
            rest (.accepted tape) := by
        simpa [postClock, clockAfter_empty_succ] using hrest
      exact choice_right_mixed_both_slots_spec current actual hactual
        rules hrules hreads input leftTape outer
        (List.replicate n (ulogCore clockOne) ++
          ulogCore clockZero :: runtime)
        (ulogCore clockOne) growth hleft hp hpre (Or.inr rfl) hboth rest
        tape hrest'

theorem clockSeek_sep (left right : List Tape) :
    oneStep (.running .clockSeek ⟨left, ulogCore clockSep, right⟩) =
      .rejected := by
  rfl

def beforeConsumeZeroSep (n : Nat) (left suffix : List Tape) :
    Zipper Tape :=
  match n with
  | 0 => ⟨left, ulogCore clockSep, suffix⟩
  | k + 1 =>
      ⟨left, ulogCore clockZero,
        List.replicate k (ulogCore clockZero) ++
          ulogCore clockSep :: suffix⟩

def afterConsumeZeroSep (n : Nat) (left suffix : List Tape) :
    Zipper Tape :=
  ⟨List.replicate n (ulogCore clockOne) ++ left, ulogCore clockSep, suffix⟩

def choiceFree_clockConsume_zeroSep (n : Nat) (left suffix : List Tape) :
    ChoiceFreeValidZeroRun n
      (.running .clockConsume (beforeConsumeZeroSep n left suffix))
      (.running .clockConsume (afterConsumeZeroSep n left suffix)) := by
  induction n generalizing left with
  | zero =>
      exact
        { valid := .nil _
          choice_free := by intro m hm; simp at hm }
  | succ n ih =>
      have hfirst : ChoiceFreeValidZeroRun 1
          (.running .clockConsume
            (beforeConsumeZeroSep (n + 1) left suffix))
          (.running .clockConsume
            (beforeConsumeZeroSep n (ulogCore clockOne :: left) suffix)) := by
        cases n with
        | zero =>
            simpa [beforeConsumeZeroSep] using
              choiceFree_clockConsume_zero_step left (ulogCore clockSep)
                suffix
        | succ n =>
            simpa [beforeConsumeZeroSep, List.replicate_succ,
              List.append_assoc] using
              choiceFree_clockConsume_zero_step left (ulogCore clockZero)
                (List.replicate n (ulogCore clockZero) ++
                  ulogCore clockSep :: suffix)
      have hrest := ih (ulogCore clockOne :: left)
      have hall := hfirst.append hrest
      simpa [afterConsumeZeroSep, List.replicate_succ', List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def choiceFree_clockConsume_sep (left right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockConsume ⟨left, ulogCore clockSep, right⟩) .rejected :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
      (by simp [concreteHalted])
      (by rw [clockConsume_exhausted]; simp))
    (by simp [IsConcreteChoice])

def choiceFree_clockSeek_sep (left right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockSeek ⟨left, ulogCore clockSep, right⟩) .rejected :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
      (by simp [concreteHalted])
      (by rw [clockSeek_sep]; simp))
    (by simp [IsConcreteChoice])

noncomputable def cycle_zero_clock_reject
    (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload outer suffix : List Tape)
    (actual width : Nat) (hactual : actual < 3)
    (hpayload : PayloadPathSafe clockPayload) :
    Σ n, ChoiceFreeValidZeroRun n
      (cycleStartZeroClock rules input leftTape clockPayload outer suffix
        actual width)
      .rejected := by
  have hhead := choiceHead_of_actual hactual
  let left :=
    dynamicRuleReturnPath leftTape rules input ++ ulogCore pcMark :: outer
  let head := readHeadNat actual
  cases width with
  | zero =>
      have hcycle : ChoiceFreeValidZeroRun 1
          (cycleStartZeroClock rules input leftTape clockPayload outer
            suffix actual 0)
          (.running .clockSeek
            (beforeRightPath clockPayload (head :: left)
              (ulogCore clockSep) suffix)) := by
        cases clockPayload with
        | nil =>
            simpa [cycleStartZeroClock, beforeRightPath, left, head] using
              choiceFree_cycleStart_head_step head hhead left
                (ulogCore clockSep) suffix
        | cons x xs =>
            simpa [cycleStartZeroClock, beforeRightPath, left, head,
              List.append_assoc] using
              choiceFree_cycleStart_head_step head hhead left x
                (xs ++ ulogCore clockSep :: suffix)
      have hscan :=
        choiceFree_clockSeek_payloadPath clockPayload hpayload
          (head :: left) (ulogCore clockSep) suffix
      have hrej :=
        choiceFree_clockSeek_sep (clockPayload.reverse ++ head :: left)
          suffix
      have hall := (hcycle.append hscan).append
        (by simpa [afterRightPath] using hrej)
      exact ⟨_, hall⟩
  | succ n =>
      have hcycle : ChoiceFreeValidZeroRun 1
          (cycleStartZeroClock rules input leftTape clockPayload outer
            suffix actual (n + 1))
          (.running .clockSeek
            (beforeRightPath clockPayload (head :: left)
              (ulogCore clockZero)
              (List.replicate n (ulogCore clockZero) ++
                ulogCore clockSep :: suffix))) := by
        cases clockPayload with
        | nil =>
            simpa [cycleStartZeroClock, beforeRightPath, left, head,
              List.replicate_succ, List.append_assoc] using
              choiceFree_cycleStart_head_step head hhead left
                (ulogCore clockZero)
                (List.replicate n (ulogCore clockZero) ++
                  ulogCore clockSep :: suffix)
        | cons x xs =>
            simpa [cycleStartZeroClock, beforeRightPath, left, head,
              List.replicate_succ, List.append_assoc] using
              choiceFree_cycleStart_head_step head hhead left x
                (xs ++ ulogCore clockZero ::
                  List.replicate n (ulogCore clockZero) ++
                    ulogCore clockSep :: suffix)
      have hscan :=
        choiceFree_clockSeek_payloadPath clockPayload hpayload
          (head :: left) (ulogCore clockZero)
          (List.replicate n (ulogCore clockZero) ++
            ulogCore clockSep :: suffix)
      have hseekZero : ChoiceFreeValidZeroRun 1
          (.running .clockSeek
            (afterRightPath clockPayload (head :: left)
              (ulogCore clockZero)
              (List.replicate n (ulogCore clockZero) ++
                ulogCore clockSep :: suffix)))
          (.running .clockConsume
            (beforeConsumeZeroSep n
              (ulogCore clockOne :: clockPayload.reverse ++ head :: left)
              suffix)) := by
        apply ChoiceFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases n with
          | zero =>
              simpa [afterRightPath, beforeConsumeZeroSep,
                List.append_assoc] using
                clockSeek_zero_step
                  (clockPayload.reverse ++ head :: left)
                  (ulogCore clockSep) suffix
          | succ n =>
              simpa [afterRightPath, beforeConsumeZeroSep,
                List.replicate_succ, List.append_assoc] using
                clockSeek_zero_step
                  (clockPayload.reverse ++ head :: left)
                  (ulogCore clockZero)
                  (List.replicate n (ulogCore clockZero) ++
                    ulogCore clockSep :: suffix)
        · simp [IsConcreteChoice]
      have hconsume :=
        choiceFree_clockConsume_zeroSep n
          (ulogCore clockOne :: clockPayload.reverse ++ head :: left)
          suffix
      have hrej :=
        choiceFree_clockConsume_sep
          (List.replicate n (ulogCore clockOne) ++
            ulogCore clockOne :: clockPayload.reverse ++ head :: left)
          suffix
      have hall :=
        (((hcycle.append hscan).append hseekZero).append hconsume).append
          (by simpa [afterConsumeZeroSep, List.append_assoc] using hrej)
      exact ⟨_, hall⟩

theorem cycle_zero_clock_exhausted_spec
    (rules : List RuleCode) (input : List Bool)
    (leftTape clockPayload outer suffix : List Tape)
    (actual width : Nat) (hactual : actual < 3)
    (hpayload : PayloadPathSafe clockPayload) :
    (∃ n, Nonempty
        (ValidZeroRun n
          (cycleStartZeroClock rules input leftTape clockPayload outer
            suffix actual width)
          .rejected) ∧
      run n
          (cycleStartZeroClock rules input leftTape clockPayload outer
            suffix actual width) =
        .rejected) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath
        (cycleStartZeroClock rules input leftTape clockPayload outer
          suffix actual width)
        labels (.accepted tape) → False) := by
  obtain ⟨n, w⟩ :=
    cycle_zero_clock_reject rules input leftTape clockPayload outer suffix
      actual width hactual hpayload
  refine ⟨⟨n, ⟨⟨w.valid⟩, w.valid.eq_run⟩⟩, ?_⟩
  intro labels tape raw
  obtain ⟨rest, _, fromRej⟩ :=
    zero_prefix_of_micro_accepting w.valid w.choice_free raw
  have halted := microPath_halted_start fromRej (by rfl)
  cases halted.2

end PakFixedPolyomino.ULogConcreteClockChoiceUnderflow
