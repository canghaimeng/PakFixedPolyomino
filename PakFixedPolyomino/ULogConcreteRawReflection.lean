import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Raw exact accepting traces reflect back to semantic accepting traces.

Unlike the older canonical-image statements, the concrete input below is an
`ExactConcreteAcceptingSlotTrace`: its only execution evidence is a sequence
of first-hit concrete cycles.  The reflection proof identifies each raw cycle
locally and never equips the raw subtype with semantic membership.
-/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

/-- A resource reserve may be shortened when fewer semantic cycles remain. -/
theorem FrameResourceInvariant.of_le
    {input : List Bool} {suffix : List Tape}
    {frame : SemanticCycleFrame input suffix} {small large : ℕ}
    (resources : FrameResourceInvariant frame large) (hsmall : small ≤ large) :
    FrameResourceInvariant frame small := by
  refine
    { tape_bounded := resources.tape_bounded
      program_nonempty := resources.program_nonempty
      reads_lt_three := resources.reads_lt_three
      writes_lt_three := resources.writes_lt_three
      state_le_capacity := resources.state_le_capacity
      target_capacity_reserve := ?_
      outer_work_reserve := ?_ }
  · intro rule hrule
    have hreserve := resources.target_capacity_reserve rule hrule
    omega
  · obtain ⟨tail, houter⟩ := resources.outer_work_reserve
    refine ⟨List.replicate (large - small) MStarConcreteAlphabet.work ++ tail, ?_⟩
    rw [houter, ← List.append_assoc, ← List.replicate_add]
    have hsplit : small + (large - small) = large :=
      Nat.add_sub_of_le hsmall
    have hlength : large + 1 = (small + 1) + (large - small) := by
      omega
    rw [hlength]

/-- An accepting trace remains accepting when its cycle budget is enlarged by
one. -/
theorem AcceptingSlotTrace.succ
    {t : ℕ} {c : ULogSemantics.Config} {slots : List Bool}
    (trace : AcceptingSlotTrace t c slots) :
    AcceptingSlotTrace (t + 1) c slots := by
  cases t with
  | zero =>
      rcases trace with ⟨hslots, hhalt, haccept⟩
      exact Or.inl ⟨hslots, hhalt, haccept⟩
  | succ t =>
      rcases trace with terminal | step
      · exact Or.inl terminal
      · rcases step with ⟨slot, next, rest, hslots, hhalt, hstep, htail⟩
        exact Or.inr ⟨slot, next, rest, hslots, hhalt, hstep, htail.succ⟩

/-- The logical accepting-trace predicate is monotone in its budget. -/
theorem AcceptingSlotTrace.mono
    {small large : ℕ} {c : ULogSemantics.Config} {slots : List Bool}
    (trace : AcceptingSlotTrace small c slots) (hsmall : small ≤ large) :
    AcceptingSlotTrace large c slots := by
  induction large, hsmall using Nat.le_induction with
  | base => exact trace
  | succ large _ ih => exact ih.succ

/-- Every genuinely raw, exact accepting slot trace from a resource-certified
nonhalting frame is a semantic accepting trace.  The strict clock guard is
one larger than the current word length, so a continuing raw cycle has enough
decoded clock to identify its positive endpoint before recursing. -/
theorem exactConcreteAcceptingSlotTrace_reflect
    {input : List Bool} {suffix : List Tape}
    {frame : SemanticCycleFrame input suffix} {slots : List Bool}
    (resources : FrameResourceInvariant frame slots.length)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    {budget : ℕ}
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : slots.length < budget)
    (trace : ExactConcreteAcceptingSlotTrace frame.encode slots) :
    AcceptingSlotTrace slots.length frame.config slots := by
  induction slots generalizing frame budget with
  | nil =>
      rcases trace with ⟨finish, run, haccept⟩
      cases run
      simp [SemanticCycleFrame.encode, semanticCycleEncoding,
        concreteAccepting] at haccept
  | cons slot rest ih =>
      rcases trace with ⟨finish, run, haccept⟩
      cases run with
      | cons _ next _ _ _ cycle tail =>
          cases hfinish : finish with
          | running state tape =>
              simp [hfinish, concreteAccepting] at haccept
          | rejected => simp [hfinish, concreteAccepting] at haccept
          | stuck => simp [hfinish, concreteAccepting] at haccept
          | accepted z =>
              subst finish
              have ready : FrameReady frame := resources.frameReady hruntime
              cases hlookup : ULogBytecode.lookupRule frame.config.program
                  frame.config.state frame.config.focus slot with
              | none =>
                  exact (by
                    simpa [SemanticCycleFrame.encode] using
                      (exactConcreteCycle_semanticNoRule_not_accepting_tail
                        frame.config slot input frame.clockZeros frame.capacity
                        frame.runtime frame.outer suffix hruntime
                        ready.focus_lt_three ready.program_nonempty
                        ready.reads_lt_three hlookup cycle tail))
              | some action =>
                  have hstep : ULogSemantics.stepSlot slot frame.config =
                      some (ULogSemantics.applyAction frame.config action) := by
                    simp [ULogSemantics.stepSlot, hstart, hlookup]
                  cases htarget : action.target with
                  | zero =>
                      have hacceptNext : ULogSemantics.accepting
                          (ULogSemantics.applyAction frame.config action) = true :=
                        (accepting_applyAction_iff_target_zero frame.config action).mpr
                          htarget
                      have hnext : next = .accepted
                          (exactAcceptingCycleRefinement frame slot ready
                            (ULogSemantics.applyAction frame.config action)
                            hstep hacceptNext).tape := by
                        exact exactConcreteCycle_finish_eq_accepting_of_semantic
                          frame slot ready
                          (ULogSemantics.applyAction frame.config action)
                          hstep hacceptNext cycle
                      subst next
                      obtain ⟨hrest, _⟩ :=
                        tail.eq_nil_of_concreteHalted_start (by
                          simp [concreteHalted])
                      subst rest
                      simp only [List.length_cons, List.length_nil,
                        Nat.zero_add]
                      unfold AcceptingSlotTrace
                      refine Or.inr ⟨slot,
                        ULogSemantics.applyAction frame.config action, [],
                        rfl, hstart, hstep, ?_⟩
                      exact ⟨rfl, ULogSemantics.accepting_halted hacceptNext,
                        hacceptNext⟩
                  | succ target =>
                      cases target with
                      | zero =>
                          have honeCapacity : 1 ≤ frame.capacity := by
                            have hcapacity := semanticCapacityReady_target_le
                              frame.config action frame.capacity
                              (ready.capacity_ready slot action hlookup)
                            omega
                          exact (by
                            simpa [SemanticCycleFrame.encode, htarget] using
                              (exactConcreteCycle_semanticTargetOne_not_accepting_tail
                                frame.config slot action hlookup htarget input
                                frame.clockZeros frame.capacity frame.runtime
                                frame.outer suffix hruntime ready.focus_lt_three
                                ready.reads_lt_three ready.writes_lt_three
                                ready.state_le_capacity honeCapacity cycle tail))
                      | succ positive =>
                          have hacceptNext : ULogSemantics.accepting
                              (ULogSemantics.applyAction frame.config action) = false := by
                            cases h : ULogSemantics.accepting
                                (ULogSemantics.applyAction frame.config action) <;>
                              simp_all [accepting_applyAction_iff_target_zero]
                          have hhaltNext : ULogSemantics.halted
                              (ULogSemantics.applyAction frame.config action) = false := by
                            cases h : ULogSemantics.halted
                                (ULogSemantics.applyAction frame.config action) <;>
                              simp_all [halted_applyAction_iff_target_lt_two]
                          have hclockPositive : 1 < budget := by
                            simp only [List.length_cons] at hbudget
                            omega
                          have hresources : FrameResourceInvariant frame
                              (rest.length + 1) := by
                            simpa using resources
                          obtain ⟨continuation, hnext⟩ :=
                            exactConcreteCycle_identify_positive_outcome frame slot
                              (ULogSemantics.applyAction frame.config action)
                              rest.length budget hresources hruntime hclock
                              hclockPositive hstep hacceptNext hhaltNext cycle
                          subst next
                          have tailTrace : ExactConcreteAcceptingSlotTrace
                              (frame.reframeNext continuation.action
                                continuation.reframe).encode rest :=
                            ⟨.accepted z, tail, rfl⟩
                          have hnextResources : FrameResourceInvariant
                              (frame.reframeNext continuation.action
                                continuation.reframe) rest.length :=
                            resources.next frame slot continuation.action rest.length
                              continuation.lookup continuation.reframe
                          have hrestBudget : rest.length < budget - 1 := by
                            simp only [List.length_cons] at hbudget
                            omega
                          have hnextStart : ULogSemantics.halted
                              (frame.reframeNext continuation.action
                                continuation.reframe).config = false := by
                            change ULogSemantics.halted
                              (ULogSemantics.applyAction frame.config
                                continuation.action) = false
                            rw [continuation.action_eq]
                            exact hhaltNext
                          have tailSemantic := ih hnextResources
                            continuation.reframe.runtime_passive hnextStart
                            continuation.clock_decoded hrestBudget tailTrace
                          simp only [List.length_cons]
                          unfold AcceptingSlotTrace
                          refine Or.inr ⟨slot,
                            ULogSemantics.applyAction frame.config action, rest,
                            rfl, hstart, hstep, ?_⟩
                          have htailConfig :
                              (frame.reframeNext continuation.action
                                continuation.reframe).config =
                                ULogSemantics.applyAction frame.config action := by
                            change ULogSemantics.applyAction frame.config
                              continuation.action =
                                ULogSemantics.applyAction frame.config action
                            rw [continuation.action_eq]
                          rw [← htailConfig]
                          exact tailSemantic

/-- Reflection on the raw accepting-word subtype.  The initial resource
certificate is shortened to the actual word length before raw recursion. -/
def exactConcreteAcceptingToSemantic
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    ExactConcreteAcceptingWords t frame.encode →
      SemanticAcceptingWords t frame.config :=
  fun word =>
    have hlength : word.1.length ≤ t := word.2.1
    let trace := exactConcreteAcceptingSlotTrace_reflect
      (resources.of_le hlength) hruntime hstart hclock (by omega) word.2.2
    ⟨word.1, (mem_acceptingSlotWords_iff t frame.config word.1).mpr
      (trace.mono word.2.1)⟩

/-- Resource- and clock-bounded semantic traces have genuine raw exact
realizations.  This forward map is independent of the obsolete global
continuation-refinement interfaces. -/
def semanticToBoundedExactConcreteAccepting
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    SemanticAcceptingWords t frame.config →
      ExactConcreteAcceptingWords t frame.encode :=
  fun word =>
    let trace := (mem_acceptingSlotWords_iff t frame.config word.1).mp word.2
    ⟨word.1, trace.length_le_budget,
      acceptingSlotTrace_has_boundedResource_concrete_exact_trace resources
        hruntime hstart trace (t + 1) hclock (by
          have hlength := trace.length_le_budget
          omega)⟩

theorem semanticToBoundedExactConcreteAccepting_apply_val
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1))
    (word : SemanticAcceptingWords t frame.config) :
    (semanticToBoundedExactConcreteAccepting t frame resources hruntime hstart
      hclock word).1 = word.1 := rfl

theorem semanticToBoundedExactConcreteAccepting_injective
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    Function.Injective
      (semanticToBoundedExactConcreteAccepting t frame resources hruntime hstart
        hclock) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun q : ExactConcreteAcceptingWords t frame.encode => q.1) hxy

/-- The bounded forward map and raw reflection are mutually inverse.  The
two subtypes retain the same slot word, but their membership proofs are
respectively semantic and genuinely concrete. -/
def semanticExactConcreteAcceptingEquiv
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    SemanticAcceptingWords t frame.config ≃
      ExactConcreteAcceptingWords t frame.encode where
  toFun := semanticToBoundedExactConcreteAccepting t frame resources hruntime
    hstart hclock
  invFun := exactConcreteAcceptingToSemantic t frame resources hruntime hstart
    hclock
  left_inv := by
    intro word
    apply Subtype.ext
    rfl
  right_inv := by
    intro word
    apply Subtype.ext
    rfl

/-- Compatibility form for callers which still carry the former refinement
arguments.  They are no longer used: the bounded concrete theorem supplies
the forward exact trace directly from `resources` and `hclock`. -/
def semanticExactConcreteAcceptingEquiv_of_refinements
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (_continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := suffix))
    (_acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := suffix))
    (_ready : FrameReady frame)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    SemanticAcceptingWords t frame.config ≃
      ExactConcreteAcceptingWords t frame.encode :=
  semanticExactConcreteAcceptingEquiv t frame resources hruntime hstart hclock

/-- The raw exact accepting-word subtype is finite through semantic
reflection, without changing its defining predicate. -/
noncomputable def exactConcreteAcceptingWordsFintype
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    Fintype (ExactConcreteAcceptingWords t frame.encode) := by
  letI : Fintype (SemanticAcceptingWords t frame.config) :=
    semanticAcceptingWordsFintype t frame.config
  exact Fintype.ofEquiv (SemanticAcceptingWords t frame.config)
    (semanticExactConcreteAcceptingEquiv t frame resources hruntime hstart hclock)

/-- Consequently, exact raw accepting words have the semantic accepting-path
count at the same bound. -/
theorem card_exactConcreteAcceptingWords
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some (t + 1)) :
    @Fintype.card (ExactConcreteAcceptingWords t frame.encode)
      (exactConcreteAcceptingWordsFintype t frame resources hruntime hstart
        hclock) =
      ULogSemantics.machine.acceptingPaths t frame.config := by
  letI : Fintype (ExactConcreteAcceptingWords t frame.encode) :=
    exactConcreteAcceptingWordsFintype t frame resources hruntime hstart hclock
  letI : Fintype (SemanticAcceptingWords t frame.config) :=
    semanticAcceptingWordsFintype t frame.config
  calc
    Fintype.card (ExactConcreteAcceptingWords t frame.encode) =
        Fintype.card (SemanticAcceptingWords t frame.config) :=
      Fintype.card_congr
        (semanticExactConcreteAcceptingEquiv t frame resources hruntime hstart
          hclock).symm
    _ = ULogSemantics.machine.acceptingPaths t frame.config :=
      card_semanticAcceptingWords t frame.config

end PakFixedPolyomino.ULogBootstrapExecution
