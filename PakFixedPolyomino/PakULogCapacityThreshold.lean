import PakFixedPolyomino.PakULogSlackInvariance
import PakFixedPolyomino.PakSlotOneScannerMultiplicity
import PakFixedPolyomino.ULogSource

/-!
# Capacity thresholds for exact raw accepting words

Above a uniform program-and-time threshold, raw exact accepting words are
canonically equivalent through their common semantic word.  Below that
threshold the count is not generally zero: an accepting branch can use less
capacity than another, unselected branch.  Consequently slot-one counting
must retain a capacity-weighted sum unless a stronger source normalization is
proved.
-/

namespace PakFixedPolyomino.PakULogCapacityThreshold

open ULogAlphabet ULogProgram
open ULogBootstrapExecution

def exactCapacityThreshold (rules : List ULogBytecode.RuleCode)
    (steps : ℕ) : ℕ :=
  max 2 (programTargetBound rules + steps + 1)

theorem exactCapacityThreshold_ge_two
    (rules : List ULogBytecode.RuleCode) (steps : ℕ) :
    2 ≤ exactCapacityThreshold rules steps :=
  Nat.le_max_left _ _

theorem target_add_lt_exactCapacityThreshold
    {rules : List ULogBytecode.RuleCode} {r : ULogBytecode.RuleCode}
    (steps : ℕ) (hr : r ∈ rules) :
    r.action.target + steps < exactCapacityThreshold rules steps := by
  have htarget := actionTarget_le_programTargetBound hr
  unfold exactCapacityThreshold
  omega

def thresholdFrame (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (capacity steps : ℕ) :
    SemanticCycleFrame input ([] : List Tape) :=
  bootstrapSemanticFrame rules input padding capacity
    (List.replicate steps MStarConcreteAlphabet.work)

theorem thresholdFrame_resources
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity steps : ℕ)
    (hcapacity : exactCapacityThreshold rules steps ≤ capacity)
    (hprogram : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3) :
    FrameResourceInvariant
      (thresholdFrame rules input padding capacity steps) steps := by
  have htwo : 2 ≤ capacity :=
    (exactCapacityThreshold_ge_two rules steps).trans hcapacity
  have htargets : ∀ r ∈ rules, r.action.target + steps < capacity := by
    intro r hr
    exact (target_add_lt_exactCapacityThreshold steps hr).trans_le hcapacity
  simpa [thresholdFrame, List.append_nil] using
    (bootstrapSemanticFrame_resources rules input padding capacity steps
      ([] : List Tape) hprogram htwo hreads hwrites htargets)

/-- Exact raw accepting languages stabilize once both capacities exceed the
uniform program/time threshold.  The equivalence preserves the Boolean word
literally. -/
noncomputable def exactAcceptingWordsEquiv_aboveThreshold
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity₁ capacity₂ steps : ℕ)
    (hcapacity₁ : exactCapacityThreshold rules steps ≤ capacity₁)
    (hcapacity₂ : exactCapacityThreshold rules steps ≤ capacity₂)
    (hprogram : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (hruntime : PassivePath
      (thresholdFrame rules input padding capacity₁ steps).runtime)
    (hstart : ULogSemantics.halted
      (thresholdFrame rules input padding capacity₁ steps).config = false)
    (hclock : decodeBinaryClock
      (List.replicate
          (thresholdFrame rules input padding capacity₁ steps).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne ::
          (thresholdFrame rules input padding capacity₁ steps).runtime) =
        some (steps + 1)) :
    ExactConcreteAcceptingWords steps
        (thresholdFrame rules input padding capacity₁ steps).encode ≃
      ExactConcreteAcceptingWords steps
        (thresholdFrame rules input padding capacity₂ steps).encode :=
  (semanticExactConcreteAcceptingEquiv steps
      (thresholdFrame rules input padding capacity₁ steps)
      (thresholdFrame_resources rules input padding capacity₁ steps
        hcapacity₁ hprogram hreads hwrites)
      hruntime hstart hclock).symm.trans
    (semanticExactConcreteAcceptingEquiv steps
      (thresholdFrame rules input padding capacity₂ steps)
      (thresholdFrame_resources rules input padding capacity₂ steps
        hcapacity₂ hprogram hreads hwrites)
      hruntime hstart hclock)

@[simp] theorem exactAcceptingWordsEquiv_aboveThreshold_apply_val
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity₁ capacity₂ steps : ℕ)
    (hcapacity₁ : exactCapacityThreshold rules steps ≤ capacity₁)
    (hcapacity₂ : exactCapacityThreshold rules steps ≤ capacity₂)
    (hprogram : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (hruntime : PassivePath
      (thresholdFrame rules input padding capacity₁ steps).runtime)
    (hstart : ULogSemantics.halted
      (thresholdFrame rules input padding capacity₁ steps).config = false)
    (hclock : decodeBinaryClock
      (List.replicate
          (thresholdFrame rules input padding capacity₁ steps).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne ::
          (thresholdFrame rules input padding capacity₁ steps).runtime) =
        some (steps + 1))
    (word : ExactConcreteAcceptingWords steps
      (thresholdFrame rules input padding capacity₁ steps).encode) :
    (exactAcceptingWordsEquiv_aboveThreshold rules input padding
      capacity₁ capacity₂ steps hcapacity₁ hcapacity₂ hprogram hreads
      hwrites hruntime hstart hclock word).1 = word.1 := by
  rfl

/-! ## A concrete obstruction to zero-below-threshold collapse -/

def regressionRules : List ULogBytecode.RuleCode :=
  ULogCompiler.compile ULogSource.regressionProgram

def regressionCapacityTwoFrame :
    SemanticCycleFrame ([] : List Bool) ([] : List Tape) :=
  bootstrapSemanticFrame regressionRules [] [] 2 []

theorem regressionRules_nonempty : regressionRules ≠ [] := by
  native_decide

theorem regressionCapacityTwoFrame_ready :
    FrameReady regressionCapacityTwoFrame := by
  apply bootstrapSemanticFrame_ready
  · exact regressionRules_nonempty
  · norm_num
  · native_decide +revert
  · native_decide +revert
  · native_decide +revert

theorem regression_false_slot_accepts :
    ∃ c', ULogSemantics.stepSlot false
        regressionCapacityTwoFrame.config = some c' ∧
      ULogSemantics.accepting c' = true := by
  native_decide

noncomputable def regressionCapacityTwoExactAcceptingWord :
    ExactConcreteAcceptingWords 1 regressionCapacityTwoFrame.encode := by
  let c' := Classical.choose regression_false_slot_accepts
  have hspec := Classical.choose_spec regression_false_slot_accepts
  have hstep : ULogSemantics.stepSlot false
      regressionCapacityTwoFrame.config = some c' := hspec.1
  have haccept : ULogSemantics.accepting c' = true := hspec.2
  let witness := exactAcceptingCycleRefinement regressionCapacityTwoFrame
    false regressionCapacityTwoFrame_ready c' hstep haccept
  refine ⟨[false], by simp, ?_⟩
  refine ⟨.accepted witness.tape, ?_, rfl⟩
  exact ExactConcreteSlotRun.cons _ _ _ false []
    witness.exact_cycle (ExactConcreteSlotRun.nil _)

theorem regression_capacity_two_below_uniform_threshold :
    2 < exactCapacityThreshold regressionRules 1 := by
  native_decide

theorem regression_below_threshold_nonempty :
    Nonempty
      (ExactConcreteAcceptingWords 1 regressionCapacityTwoFrame.encode) :=
  ⟨regressionCapacityTwoExactAcceptingWord⟩

/-! ## Backend contract for a genuine uniform-resource normal form -/

/-- This is exactly the numerical profile a source normalizer must induce.
It is intentionally stronger than FrameResourceInvariant: below one common
threshold every raw accepting fibre is empty, and above it every fibre has
the semantic accepting count. -/
structure UniformCapacityDemand
    (x : ConcretePakSide.Word) (minConsumed semanticCount : ℕ)
    (rawCount : ℕ → ℕ) where
  threshold : ℕ
  min_le_threshold : minConsumed ≤ threshold
  threshold_le_count :
    threshold ≤ PakSlotOneScannerMultiplicity.scannerCapacityCount x
  zero_below : ∀ c, minConsumed ≤ c → c < threshold → rawCount c = 0
  constant_above : ∀ c, threshold ≤ c →
    c < PakSlotOneScannerMultiplicity.scannerCapacityCount x →
      rawCount c = semanticCount

def UniformCapacityDemand.admissibleTailCount
    {x : ConcretePakSide.Word} {minConsumed semanticCount : ℕ}
    {rawCount : ℕ → ℕ}
    (D : UniformCapacityDemand x minConsumed semanticCount rawCount) : ℕ :=
  PakSlotOneScannerMultiplicity.scannerCapacityCount x - D.threshold

/-- Once the front normalizer supplies UniformCapacityDemand, the honest
capacity sum collapses to one known multiplier times the semantic count. -/
theorem UniformCapacityDemand.weightedCount_eq
    {x : ConcretePakSide.Word} {minConsumed semanticCount : ℕ}
    {rawCount : ℕ → ℕ}
    (D : UniformCapacityDemand x minConsumed semanticCount rawCount) :
    PakSlotOneScannerMultiplicity.capacityWeightedCount
        x minConsumed rawCount =
      D.admissibleTailCount * semanticCount := by
  rw [PakSlotOneScannerMultiplicity.capacityWeightedCount_split_stable_tail
    x minConsumed D.threshold semanticCount rawCount
    D.min_le_threshold D.threshold_le_count D.constant_above]
  have hzero :
      (∑ d ∈ Finset.range (D.threshold - minConsumed),
        rawCount (minConsumed + d)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_range] at hd
    exact D.zero_below (minConsumed + d) (by omega) (by omega)
  rw [hzero, Nat.zero_add]
  rfl

/-- One-query arithmetic decoder after subtracting the separately computable
scanner baseline. -/
def uniformCapacityPostprocess
    (baseline multiplier observed : ℕ) : ℕ :=
  (observed - baseline) / multiplier

theorem uniformCapacityPostprocess_correct
    (baseline multiplier semanticCount observed : ℕ)
    (hmultiplier : 0 < multiplier)
    (hobserved : observed = baseline + multiplier * semanticCount) :
    uniformCapacityPostprocess baseline multiplier observed = semanticCount := by
  subst observed
  simp [uniformCapacityPostprocess, Nat.add_sub_cancel_left,
    Nat.mul_div_left, hmultiplier]

/-- Final one-query metric algebra.  This isolates the missing mathematical
work entirely in the front-end demand certificate. -/
theorem UniformCapacityDemand.oneQuery_postprocess
    {x : ConcretePakSide.Word} {minConsumed semanticCount baseline : ℕ}
    {rawCount : ℕ → ℕ}
    (D : UniformCapacityDemand x minConsumed semanticCount rawCount)
    (hpositive : D.threshold <
      PakSlotOneScannerMultiplicity.scannerCapacityCount x) :
    uniformCapacityPostprocess baseline D.admissibleTailCount
      (baseline +
        PakSlotOneScannerMultiplicity.capacityWeightedCount
          x minConsumed rawCount) = semanticCount := by
  apply uniformCapacityPostprocess_correct
  · unfold UniformCapacityDemand.admissibleTailCount
    omega
  · rw [D.weightedCount_eq]

/-- Declarative front-end contract for the proposed repair.  exact_time,
the oblivious head schedule and the common gate are the structural invariants
the normalizer should prove.  The final uniform_capacity_profile field is
the physical adequacy theorem connecting those invariants to raw counting;
it is not supplied by the present compiler. -/
structure UniformResourceNormalForm
    (semanticStart : ULogSemantics.Config)
    (concreteStart : ℕ → Result) (steps : ℕ) where
  headSchedule : Fin (steps + 1) → Int
  commonGate : ℕ
  threshold : ℕ
  exact_time : ∀ w, AcceptingSlotTrace steps semanticStart w →
    w.length = steps
  common_gate_visited : ∀ w, AcceptingSlotTrace steps semanticStart w →
    ∃ pre suf, w = pre ++ suf
  uniform_capacity_profile : ∀ capacity w, w.length ≤ steps →
    (ExactConcreteAcceptingSlotTrace (concreteStart capacity) w ↔
      threshold ≤ capacity ∧ AcceptingSlotTrace steps semanticStart w)

theorem UniformResourceNormalForm.zero_below
    {semanticStart : ULogSemantics.Config}
    {concreteStart : ℕ → Result} {steps : ℕ}
    (N : UniformResourceNormalForm semanticStart concreteStart steps)
    {capacity : ℕ} (hcapacity : capacity < N.threshold)
    {w : List Bool} (hw : w.length ≤ steps) :
    ¬ ExactConcreteAcceptingSlotTrace (concreteStart capacity) w := by
  intro h
  have hprofile := N.uniform_capacity_profile capacity w
  have hp := (hprofile hw).mp h
  omega

theorem UniformResourceNormalForm.constant_above_word_iff
    {semanticStart : ULogSemantics.Config}
    {concreteStart : ℕ → Result} {steps : ℕ}
    (N : UniformResourceNormalForm semanticStart concreteStart steps)
    {capacity : ℕ} (hcapacity : N.threshold ≤ capacity)
    {w : List Bool} (hw : w.length ≤ steps) :
    ExactConcreteAcceptingSlotTrace (concreteStart capacity) w ↔
      AcceptingSlotTrace steps semanticStart w := by
  have hprofile := N.uniform_capacity_profile capacity w
  rw [hprofile hw]
  simp [hcapacity]

end PakFixedPolyomino.PakULogCapacityThreshold
