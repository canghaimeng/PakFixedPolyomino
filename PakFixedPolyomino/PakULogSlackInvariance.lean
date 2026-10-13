import PakFixedPolyomino.PakULogTraceResourceBound
import PakFixedPolyomino.ULogConcreteRawReflection

/-!
# Right-workspace slack does not change the accepted word language

The copier may leave extra `work` cells immediately before its physical
`rightEnd`.  They occur after the program and payload and therefore extend
only the unused bootstrap tail.  This file records that fact without any
canonical-coordinate uniqueness assumption: the extra cells are absorbed
as state-workspace capacity, while the semantic configuration, clock and
outer reserve remain unchanged.
-/

namespace PakFixedPolyomino.PakULogSlackInvariance

open ULogAlphabet ULogProgram
open ULogBootstrapExecution
open PakULogTraceResourceBound

def slackedCopiedBootstrapTail (x input : ConcretePakSide.Word)
    (slack : ℕ) : List Tape :=
  PakOuterULogBridge.copiedBootstrapTail x input ++
    List.replicate slack MStarConcreteAlphabet.work

def slackedCopiedSemanticCapacity (x input : ConcretePakSide.Word)
    (slack : ℕ) : ℕ :=
  (slackedCopiedBootstrapTail x input slack).length + 2

def slackedCopiedSemanticStartZipper
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack : ℕ) :
    MStarParserExecution.Zipper Tape :=
  ⟨ULogBootstrapExecution.dynamicRuleReturnPath
        ((ULogSemantics.startFrom rules input).leftRev.map
          ULogBootstrapExecution.payloadNat)
        (ULogSemantics.startFrom rules input).program input ++
      ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
        List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work,
    ULogBootstrapExecution.readHeadNat
      (ULogSemantics.startFrom rules input).focus,
    ULogBootstrapExecution.clockCellsBefore
        ((ULogSemantics.startFrom rules input).right.map
          ULogBootstrapExecution.payloadNat)
        padding.length [ULogAlphabet.ulogCore ULogAlphabet.clockSep] ++
      ULogBootstrapExecution.stateWorkspace 2
        (ULogSemantics.startFrom rules input).state
        (slackedCopiedBootstrapTail x input slack)⟩

/-- The direct copier interpretation: slack is initially an ordinary suffix
after the fixed two-cell state workspace. -/
theorem slackedCopiedSemanticStartEncoding_eq_running
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack : ℕ) :
    semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        2
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work)
        (slackedCopiedBootstrapTail x input slack)
        (ULogSemantics.startFrom rules input) =
      .running ULogControl.State.cycleStart
        (slackedCopiedSemanticStartZipper x rules input padding slack) := rfl

theorem slackedCopiedSemanticCapacity_eq
    (x input : ConcretePakSide.Word) (slack : ℕ) :
    slackedCopiedSemanticCapacity x input slack =
      copiedSemanticCapacity x input + slack := by
  simp [slackedCopiedSemanticCapacity, slackedCopiedBootstrapTail,
    copiedSemanticCapacity, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Extra copied work is merely a different parsing of the same physical
cycle-start zipper: it raises the state capacity and changes no semantic
field. -/
theorem slackedCopiedSemanticStart_eq_resourceBootstrapFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack : ℕ) :
    (bootstrapSemanticFrame rules input padding
      (slackedCopiedSemanticCapacity x input slack)
      (copiedSemanticOuterTail x)).encode =
      .running ULogControl.State.cycleStart
        (slackedCopiedSemanticStartZipper x rules input padding slack) := by
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  let R := PakOuterULogBridge.copiedCoreRadius x
  have houter : MStarConcreteAlphabet.work :: copiedSemanticOuterTail x =
      List.replicate R MStarConcreteAlphabet.work := by
    have hlen : R = (R - 1) + 1 := by omega
    rw [hlen, List.replicate_succ]
    rfl
  have hcap : slackedCopiedSemanticCapacity x input slack - 2 =
      (slackedCopiedBootstrapTail x input slack).length := by
    dsimp [slackedCopiedSemanticCapacity]
    omega
  have hwork : List.replicate
        (slackedCopiedSemanticCapacity x input slack - 2)
        MStarConcreteAlphabet.work =
      slackedCopiedBootstrapTail x input slack := by
    rw [hcap]
    unfold slackedCopiedBootstrapTail
    cases input with
    | nil =>
        unfold PakOuterULogBridge.copiedBootstrapTail
        rw [List.length_append, List.length_replicate,
          List.length_replicate]
        exact List.replicate_add _ _ _
    | cons b bs =>
        unfold PakOuterULogBridge.copiedBootstrapTail
        rw [List.length_append, List.length_replicate,
          List.length_replicate]
        exact List.replicate_add _ _ _
  simp [bootstrapSemanticFrame, SemanticCycleFrame.encode,
    semanticCycleEncoding, stateWorkspace,
    slackedCopiedSemanticStartZipper,
    ULogSemantics.startFrom, ULogSemantics.startCode, houter, hwork,
    R, List.append_assoc]

def canonicalCopiedSemanticFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : SemanticCycleFrame input ([] : List Tape) :=
  bootstrapSemanticFrame rules input padding
    (copiedSemanticCapacity x input) (copiedSemanticOuterTail x)

def slackedCopiedSemanticFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack : ℕ) :
    SemanticCycleFrame input ([] : List Tape) :=
  bootstrapSemanticFrame rules input padding
    (slackedCopiedSemanticCapacity x input slack)
    (copiedSemanticOuterTail x)

/-- Increasing the parsed state capacity preserves every resource
certificate.  No semantic or clock premise is strengthened. -/
theorem copiedFrame_resources_of_slack
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack t : ℕ)
    (resources : FrameResourceInvariant
      (canonicalCopiedSemanticFrame x rules input padding) t) :
    FrameResourceInvariant
      (slackedCopiedSemanticFrame x rules input padding slack) t := by
  have hcap : copiedSemanticCapacity x input ≤
      slackedCopiedSemanticCapacity x input slack := by
    rw [slackedCopiedSemanticCapacity_eq]
    omega
  refine
    { tape_bounded := resources.tape_bounded
      program_nonempty := resources.program_nonempty
      reads_lt_three := resources.reads_lt_three
      writes_lt_three := resources.writes_lt_three
      state_le_capacity := resources.state_le_capacity.trans hcap
      target_capacity_reserve := ?_
      outer_work_reserve := resources.outer_work_reserve }
  intro r hr
  exact (resources.target_capacity_reserve r hr).trans_le hcap

/-- Exact raw accepting words at canonical and slacked capacities are
equivalent, via their common semantic word.  This is stronger than equality
of counts: the equivalence preserves the underlying Boolean word literally.
-/
noncomputable def copiedExactAcceptingWordsEquivSlacked
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack t : ℕ)
    (resources : FrameResourceInvariant
      (canonicalCopiedSemanticFrame x rules input padding) t)
    (hruntime : PassivePath
      (canonicalCopiedSemanticFrame x rules input padding).runtime)
    (hstart : ULogSemantics.halted
      (canonicalCopiedSemanticFrame x rules input padding).config = false)
    (hclock : decodeBinaryClock
      (List.replicate (canonicalCopiedSemanticFrame x rules input padding).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne :: (canonicalCopiedSemanticFrame x rules input padding).runtime) =
          some (t + 1)) :
    ExactConcreteAcceptingWords t
        (canonicalCopiedSemanticFrame x rules input padding).encode ≃
      ExactConcreteAcceptingWords t
        (slackedCopiedSemanticFrame x rules input padding slack).encode :=
  (semanticExactConcreteAcceptingEquiv t
      (canonicalCopiedSemanticFrame x rules input padding) resources hruntime hstart
      hclock).symm.trans
    (semanticExactConcreteAcceptingEquiv t
      (slackedCopiedSemanticFrame x rules input padding slack)
      (copiedFrame_resources_of_slack x rules input padding slack t resources)
      hruntime hstart hclock)

@[simp] theorem copiedExactAcceptingWordsEquivSlacked_apply_val
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack t : ℕ)
    (resources : FrameResourceInvariant
      (canonicalCopiedSemanticFrame x rules input padding) t)
    (hruntime : PassivePath
      (canonicalCopiedSemanticFrame x rules input padding).runtime)
    (hstart : ULogSemantics.halted
      (canonicalCopiedSemanticFrame x rules input padding).config = false)
    (hclock : decodeBinaryClock
      (List.replicate (canonicalCopiedSemanticFrame x rules input padding).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne :: (canonicalCopiedSemanticFrame x rules input padding).runtime) =
          some (t + 1))
    (word : ExactConcreteAcceptingWords t
      (canonicalCopiedSemanticFrame x rules input padding).encode) :
    (copiedExactAcceptingWordsEquivSlacked x rules input padding slack t
      resources hruntime hstart hclock word).1 = word.1 := by
  rfl

/-- Predicate-level language invariance for callers which work with a fixed
raw slot word rather than the accepting-word subtype. -/
theorem exactConcreteAcceptingSlotTrace_iff_slacked
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack t : ℕ)
    (resources : FrameResourceInvariant
      (canonicalCopiedSemanticFrame x rules input padding) t)
    (hruntime : PassivePath
      (canonicalCopiedSemanticFrame x rules input padding).runtime)
    (hstart : ULogSemantics.halted
      (canonicalCopiedSemanticFrame x rules input padding).config = false)
    (hclock : decodeBinaryClock
      (List.replicate
          (canonicalCopiedSemanticFrame x rules input padding).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne ::
          (canonicalCopiedSemanticFrame x rules input padding).runtime) =
          some (t + 1))
    (word : List Bool) (hword : word.length ≤ t) :
    ExactConcreteAcceptingSlotTrace
        (canonicalCopiedSemanticFrame x rules input padding).encode word ↔
      ExactConcreteAcceptingSlotTrace
        (slackedCopiedSemanticFrame x rules input padding slack).encode word := by
  let e := copiedExactAcceptingWordsEquivSlacked x rules input padding slack t
    resources hruntime hstart hclock
  constructor
  · intro h
    let w : ExactConcreteAcceptingWords t
        (canonicalCopiedSemanticFrame x rules input padding).encode :=
      ⟨word, hword, h⟩
    have hval : (e w).1 = word := by
      exact copiedExactAcceptingWordsEquivSlacked_apply_val x rules input
        padding slack t resources hruntime hstart hclock w
    simpa [hval] using (e w).2.2
  · intro h
    let w : ExactConcreteAcceptingWords t
        (slackedCopiedSemanticFrame x rules input padding slack).encode :=
      ⟨word, hword, h⟩
    have hval : (e.symm w).1 = word := by
      rfl
    simpa [hval] using (e.symm w).2.2

/-- Consequently the raw exact accepting-word counts are independent of the
extra right-workspace slack. -/
theorem card_copiedExactAcceptingWords_eq_slacked
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (slack t : ℕ)
    (resources : FrameResourceInvariant
      (canonicalCopiedSemanticFrame x rules input padding) t)
    (hruntime : PassivePath
      (canonicalCopiedSemanticFrame x rules input padding).runtime)
    (hstart : ULogSemantics.halted
      (canonicalCopiedSemanticFrame x rules input padding).config = false)
    (hclock : decodeBinaryClock
      (List.replicate (canonicalCopiedSemanticFrame x rules input padding).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne :: (canonicalCopiedSemanticFrame x rules input padding).runtime) =
          some (t + 1)) :
    @Fintype.card
        (ExactConcreteAcceptingWords t
          (canonicalCopiedSemanticFrame x rules input padding).encode)
        (exactConcreteAcceptingWordsFintype t
          (canonicalCopiedSemanticFrame x rules input padding) resources hruntime hstart
          hclock) =
      @Fintype.card
        (ExactConcreteAcceptingWords t
          (slackedCopiedSemanticFrame x rules input padding slack).encode)
        (exactConcreteAcceptingWordsFintype t
          (slackedCopiedSemanticFrame x rules input padding slack)
          (copiedFrame_resources_of_slack x rules input padding slack t
            resources)
          hruntime hstart hclock) := by
  letI : Fintype
      (ExactConcreteAcceptingWords t
        (canonicalCopiedSemanticFrame x rules input padding).encode) :=
    exactConcreteAcceptingWordsFintype t
      (canonicalCopiedSemanticFrame x rules input padding) resources hruntime
      hstart hclock
  letI : Fintype
      (ExactConcreteAcceptingWords t
        (slackedCopiedSemanticFrame x rules input padding slack).encode) :=
    exactConcreteAcceptingWordsFintype t
      (slackedCopiedSemanticFrame x rules input padding slack)
      (copiedFrame_resources_of_slack x rules input padding slack t resources)
      hruntime hstart hclock
  exact Fintype.card_congr
    (copiedExactAcceptingWordsEquivSlacked x rules input padding slack t
      resources hruntime hstart hclock)

end PakFixedPolyomino.PakULogSlackInvariance
