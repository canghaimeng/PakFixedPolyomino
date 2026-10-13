import PakFixedPolyomino.PakULogCycleResourceBound
import PakFixedPolyomino.PakULogBootstrapExplicitFuel

/-!
# Quantitative ledger for complete raw `U_log` traces

This file lifts the per-cycle resource estimates to an exact labelled slot
run.  It keeps the exact `ExactSlotRunFuel` ledger and proves that a uniform
literal cycle budget multiplies by the actual number of labelled cycles.
-/

namespace PakFixedPolyomino.PakULogTraceResourceBound

open ULogBootstrapExecution
open ULogAlphabet ULogProgram
open PakULogSlotRunLedger
open PakULogCycleResourceBound

/-- One relation simultaneously records the exact ledger and a uniform
per-cycle bound.  Combining both in the same inductive avoids any illegal
attempt to identify Type-valued cycle witnesses through proof irrelevance of
`ExactConcreteSlotRun`. -/
inductive ExactSlotRunBoundedFuel (P : ℕ) :
    ∀ {start finish : Result} {slots : List Bool},
      ExactConcreteSlotRun start slots finish → ℕ → Prop
  | nil (r : Result) :
      ExactSlotRunBoundedFuel P (ExactConcreteSlotRun.nil r) 0
  | cons (start next finish : Result) (slot : Bool) (slots : List Bool)
      (cycle : ExactConcreteCycle slot start next)
      (tail : ExactConcreteSlotRun next slots finish)
      (tailFuel : ℕ)
      (hcycle : cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤ P)
      (htail : ExactSlotRunBoundedFuel P tail tailFuel) :
      ExactSlotRunBoundedFuel P
        (ExactConcreteSlotRun.cons start next finish slot slots cycle tail)
        (cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps + tailFuel)

/-- The combined relation projects to the pre-existing exact ledger. -/
theorem ExactSlotRunBoundedFuel.toExactFuel
    {P fuel : ℕ} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (h : ExactSlotRunBoundedFuel P run fuel) : ExactSlotRunFuel run fuel := by
  induction h with
  | nil r => exact .nil r
  | cons start next finish slot slots cycle tail tailFuel hcycle htail ih =>
      exact .cons start next finish slot slots cycle tail tailFuel ih

/-- Exact ledger sum under a uniform per-cycle bound. -/
theorem exactSlotRunFuel_le_length_mul
    {P fuel : ℕ} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (hbound : ExactSlotRunBoundedFuel P run fuel) :
    fuel ≤ slots.length * P := by
  induction hbound with
  | nil r =>
      simp
  | cons start next finish slot slots cycle tail tailFuel hcycle htail ih =>
      simp only [List.length_cons]
      calc
        cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps +
            tailFuel ≤ P + slots.length * P := Nat.add_le_add hcycle ih
        _ = (slots.length + 1) * P := by ring

/-- Radius form: at most `R` semantic labels and at most `P` raw arrows per
cycle give total exact simulation fuel at most `R*P`. -/
theorem exactSlotRunFuel_le_radius_mul
    {R P fuel : ℕ} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (hslots : slots.length ≤ R)
    (hbound : ExactSlotRunBoundedFuel P run fuel) :
    fuel ≤ R * P := by
  exact (exactSlotRunFuel_le_length_mul hbound).trans
    (Nat.mul_le_mul_right P hslots)

/-- The global per-cycle polynomial from `GlobalCopiedEnvelope`. -/
def globalCyclePolynomial (R : ℕ) : ℕ :=
  6 * (64 * R) ^ 3 + 23 * (64 * R) ^ 2 + 38 * (64 * R) + 28

theorem exactAcceptingCycle_le_globalCyclePolynomial
    {x : ConcretePakSide.Word} {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix) (elapsed : ℕ)
    (global : GlobalCopiedEnvelope x frame elapsed)
    (slot : Bool) (next : ULogSemantics.Config) (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = true) :
    let cycle :=
      (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x) := by
  let L := semanticFrameCursorRadius input frame
  let W := PakOuterULogBridge.copiedCoreRadius x
  let cycle :=
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
  rcases ULogSemantics.stepSlot_some_rule hstep with
    ⟨_, action, hlookup, _⟩
  have hL : L ≤ 64 * W := by
    dsimp [L, W]
    exact global.cursorRadius_le slot action hlookup ready.focus_lt_three
  have hcycle := exactAcceptingCycleRefinement_microFuel_le_frameRadius
    frame slot next ready hstep haccept
  change cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
    globalCyclePolynomial W
  exact hcycle.trans (by
    dsimp [globalCyclePolynomial]
    gcongr)

/-- A quantitative accepting trace stores the same exact physical slot run,
its exact accumulated fuel, and the uniform per-cycle certificate. -/
def ExactConcreteAcceptingBoundedFuel
    (P : ℕ) (start : Result) (slots : List Bool) : Prop :=
  ∃ (finish : Result) (run : ExactConcreteSlotRun start slots finish)
    (fuel : ℕ),
    concreteAccepting finish = true ∧ ExactSlotRunBoundedFuel P run fuel

/-- The bounded ledger is not merely semantic bookkeeping: it lifts to an
actual outer-machine history with the same literal arrow count. -/
theorem ExactConcreteAcceptingBoundedFuel.outerAtMost
    {P : ℕ} {start : Result} {slots : List Bool}
    (h : ExactConcreteAcceptingBoundedFuel P start slots)
    (origin : Int)
    (leftExtra rightExtra : List PakULogSlotRunLedger.LedgerOuterTape) :
    ∃ (fuel : ℕ) (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (startConfig : PakULogSlotRunLedger.LedgerOuterConfig),
      fuel ≤ slots.length * P ∧
      PakOuterULogTraceBridge.framedLiveConfig origin leftExtra rightExtra
        start = some startConfig ∧
      PakOuterFrontQuantitative.OuterReachesAtMost fuel startConfig
        (PakOuterULogBridge.anchoredFramedOuterAcceptConfig origin
          leftExtra rightExtra z) := by
  rcases h with ⟨finish, run, fuel, haccept, hbound⟩
  cases hfinish : finish with
  | running q z => simp [hfinish, concreteAccepting] at haccept
  | rejected => simp [hfinish, concreteAccepting] at haccept
  | stuck => simp [hfinish, concreteAccepting] at haccept
  | accepted z =>
      subst finish
      have hledger := hbound.toExactFuel
      rcases exactConcreteSlotRun_live_outerAtMost_exactFuel origin
          leftExtra rightExtra run hledger (by trivial) with
        ⟨startConfig, finishConfig, hstartConfig, hfinishConfig, hrun⟩
      have hfinishConfig' : finishConfig =
          PakOuterULogBridge.anchoredFramedOuterAcceptConfig origin
            leftExtra rightExtra z :=
        Option.some.inj (hfinishConfig.symm.trans rfl)
      subst finishConfig
      exact ⟨fuel, z, startConfig,
        exactSlotRunFuel_le_length_mul hbound, hstartConfig, hrun⟩

/-- Quantitative obligation for the nonterminal schedule.  The ten physical
target/move templates need only discharge this one common interface. -/
def PositiveContinuationCycleBound
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (schedule : ExactPositiveResourceSchedule
      (input := input) (suffix := suffix))
    (x : ConcretePakSide.Word) (P : ℕ) : Prop :=
  ∀ (frame : SemanticCycleFrame input suffix) (elapsed : ℕ)
    (_global : GlobalCopiedEnvelope x frame elapsed)
    (slot : Bool) (next : ULogSemantics.Config) (steps budget : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = false)
    (hhalt : ULogSemantics.halted next = false),
    let continuation := schedule frame slot next steps budget resources
      hruntime hclock hbudget hstep haccept hhalt
    continuation.exact_cycle.choicePrefix.steps + 1 +
      continuation.exact_cycle.cycleSuffix.steps ≤ P

/-- Trace-level quantitative recursion.  The semantic word itself controls
elapsed time, while `GlobalCopiedEnvelope.next` controls every reframed
physical state. -/
theorem acceptingSlotTrace_has_quantitative_exact_trace
    {x : ConcretePakSide.Word} {input : List Bool} {suffix : List ULogProgram.Tape}
    (schedule : ExactPositiveResourceSchedule
      (input := input) (suffix := suffix))
    (positiveBound : PositiveContinuationCycleBound schedule
      (input := input) (suffix := suffix) x
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x)))
    {t elapsed : ℕ} {frame : SemanticCycleFrame input suffix}
    {word : List Bool}
    (global : GlobalCopiedEnvelope x frame elapsed)
    (hglobalWord : elapsed + word.length ≤
      PakOuterULogBridge.copiedCoreRadius x)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ExactConcreteAcceptingBoundedFuel
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x))
      frame.encode word := by
  induction t generalizing frame word budget elapsed with
  | zero => simp [AcceptingSlotTrace, hstart] at trace
  | succ t ih =>
      have ready := resources.frameReady hruntime
      rcases trace with terminal |
        ⟨slot, next, rest, rfl, _, hstep, tailTrace⟩
      · simp [hstart] at terminal
      · by_cases haccept : ULogSemantics.accepting next = true
        · have hrest : rest = [] :=
            tailTrace.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          let witness := exactAcceptingCycleRefinement frame slot ready next
            hstep haccept
          have hcycleBound : witness.exact_cycle.choicePrefix.steps + 1 +
              witness.exact_cycle.cycleSuffix.steps ≤
                globalCyclePolynomial
                  (PakOuterULogBridge.copiedCoreRadius x) := by
            dsimp [witness]
            exact exactAcceptingCycle_le_globalCyclePolynomial frame elapsed
              global slot next ready hstep haccept
          refine ⟨.accepted witness.tape,
            .cons frame.encode (.accepted witness.tape)
              (.accepted witness.tape) slot [] witness.exact_cycle (.nil _),
            witness.exact_cycle.choicePrefix.steps + 1 +
              witness.exact_cycle.cycleSuffix.steps,
            rfl, ?_⟩
          exact .cons frame.encode (.accepted witness.tape)
            (.accepted witness.tape) slot [] witness.exact_cycle (.nil _)
            0 hcycleBound (.nil _)
        · have hacceptFalse : ULogSemantics.accepting next = false := by
            cases h : ULogSemantics.accepting next <;> simp_all
          by_cases hhalt : ULogSemantics.halted next = true
          · exact (tailTrace.false_of_halted_not_accepting hhalt
              hacceptFalse).elim
          · have hhaltFalse : ULogSemantics.halted next = false := by
              cases h : ULogSemantics.halted next <;> simp_all
            have hrestPositive : 0 < rest.length :=
              tailTrace.length_pos_of_not_halted hhaltFalse
            have hbudget : 1 < budget := by
              simp only [List.length_cons] at hwordBudget
              omega
            let continuation := schedule frame slot next t budget resources
              hruntime hclock hbudget hstep hacceptFalse hhaltFalse
            have hcycleBound := positiveBound frame elapsed global slot next
              t budget resources hruntime hclock hbudget hstep hacceptFalse
              hhaltFalse
            change continuation.exact_cycle.choicePrefix.steps + 1 +
              continuation.exact_cycle.cycleSuffix.steps ≤
                globalCyclePolynomial
                  (PakOuterULogBridge.copiedCoreRadius x) at hcycleBound
            obtain ⟨action, reframe, hlookup, haction, hnextClock,
                hcycle⟩ := continuation
            have nextResources : FrameResourceInvariant
                (frame.reframeNext action reframe) t :=
              resources.next frame slot action t hlookup reframe
            have tailTrace' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact tailTrace
            have hnextStart : ULogSemantics.halted
                (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            have hrestBudget : rest.length ≤ budget - 1 := by
              simp only [List.length_cons] at hwordBudget
              omega
            have helapsed : elapsed + 1 ≤
                PakOuterULogBridge.copiedCoreRadius x := by
              simp only [List.length_cons] at hglobalWord
              omega
            have nextGlobal : GlobalCopiedEnvelope x
                (frame.reframeNext action reframe) (elapsed + 1) :=
              global.next action reframe helapsed
            have hnextWord : elapsed + 1 + rest.length ≤
                PakOuterULogBridge.copiedCoreRadius x := by
              simp only [List.length_cons] at hglobalWord
              omega
            obtain ⟨finish, tailRun, tailFuel, hfinish, htailBound⟩ :=
              ih nextGlobal hnextWord nextResources reframe.runtime_passive
                hnextStart tailTrace' (budget - 1) hnextClock hrestBudget
            refine ⟨finish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                finish slot rest hcycle tailRun,
              hcycle.choicePrefix.steps + 1 + hcycle.cycleSuffix.steps +
                tailFuel,
              hfinish, ?_⟩
            exact .cons frame.encode (frame.reframeNext action reframe).encode
              finish slot rest hcycle tailRun tailFuel hcycleBound htailBound

/-- Multiplying the cubic cycle budget by at most `R` semantic cycles still
fits under the ninth-power copied-radius clock. -/
theorem radius_mul_globalCyclePolynomial_lt_pow_nine
    {R : ℕ} (hR : 256 ≤ R) :
    R * globalCyclePolynomial R < R ^ 9 := by
  have hR2 : 256 ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hR3 : 256 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have hR5 : 256 ^ 5 ≤ R ^ 5 := Nat.pow_le_pow_left hR 5
  have hpoly : globalCyclePolynomial R < 1836000 * R ^ 3 := by
    dsimp [globalCyclePolynomial]
    nlinarith [hR2, hR3]
  have hcoef : 1836000 < R ^ 5 := by
    have : 1836000 < 256 ^ 5 := by norm_num
    exact this.trans_le hR5
  have hR4pos : 0 < R ^ 4 := pow_pos (by omega) _
  calc
    R * globalCyclePolynomial R < R * (1836000 * R ^ 3) :=
      Nat.mul_lt_mul_of_pos_left hpoly (by omega)
    _ = 1836000 * R ^ 4 := by ring
    _ < R ^ 5 * R ^ 4 := Nat.mul_lt_mul_of_pos_right hcoef hR4pos
    _ = R ^ 9 := by ring

/-- Sharper margin used by the full outer assembly: simulation alone fits
below `R^8`, leaving an entire eighth-power block for bootstrap overhead. -/
theorem radius_mul_globalCyclePolynomial_lt_pow_eight
    {R : ℕ} (hR : 256 ≤ R) :
    R * globalCyclePolynomial R < R ^ 8 := by
  have hR2 : 256 ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hR3 : 256 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have hR4 : 256 ^ 4 ≤ R ^ 4 := Nat.pow_le_pow_left hR 4
  have hpoly : globalCyclePolynomial R < 1836000 * R ^ 3 := by
    dsimp [globalCyclePolynomial]
    nlinarith [hR2, hR3]
  have hcoef : 1836000 < R ^ 4 := by
    have : 1836000 < 256 ^ 4 := by norm_num
    exact this.trans_le hR4
  have hR4pos : 0 < R ^ 4 := pow_pos (by omega) _
  calc
    R * globalCyclePolynomial R < R * (1836000 * R ^ 3) :=
      Nat.mul_lt_mul_of_pos_left hpoly (by omega)
    _ = 1836000 * R ^ 4 := by ring
    _ < R ^ 4 * R ^ 4 := Nat.mul_lt_mul_of_pos_right hcoef hR4pos
    _ = R ^ 8 := by ring

/-- Final exact-ledger consequence. -/
theorem exactSlotRunFuel_lt_pow_nine
    {R fuel : ℕ} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (hR : 256 ≤ R) (hslots : slots.length ≤ R)
    (hbound : ExactSlotRunBoundedFuel (globalCyclePolynomial R) run fuel) :
    fuel < R ^ 9 :=
  (exactSlotRunFuel_le_radius_mul hslots hbound).trans_lt
    (radius_mul_globalCyclePolynomial_lt_pow_nine hR)

theorem exactSlotRunFuel_lt_pow_eight
    {R fuel : ℕ} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (hR : 256 ≤ R) (hslots : slots.length ≤ R)
    (hbound : ExactSlotRunBoundedFuel (globalCyclePolynomial R) run fuel) :
    fuel < R ^ 8 :=
  (exactSlotRunFuel_le_radius_mul hslots hbound).trans_lt
    (radius_mul_globalCyclePolynomial_lt_pow_eight hR)

/-- The trace recursion exposes an exact simulation ledger with the sharper
eighth-power bound. -/
theorem acceptingSlotTrace_has_quantitative_fuel_lt_pow_eight
    {x : ConcretePakSide.Word} {input : List Bool} {suffix : List ULogProgram.Tape}
    (schedule : ExactPositiveResourceSchedule
      (input := input) (suffix := suffix))
    (positiveBound : PositiveContinuationCycleBound schedule
      (input := input) (suffix := suffix) x
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x)))
    {t elapsed : ℕ} {frame : SemanticCycleFrame input suffix}
    {word : List Bool}
    (global : GlobalCopiedEnvelope x frame elapsed)
    (hglobalWord : elapsed + word.length ≤
      PakOuterULogBridge.copiedCoreRadius x)
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ∃ (finish : Result) (run : ExactConcreteSlotRun frame.encode word finish)
      (fuel : ℕ),
      concreteAccepting finish = true ∧
      ExactSlotRunBoundedFuel
        (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x))
        run fuel ∧
      fuel < (PakOuterULogBridge.copiedCoreRadius x) ^ 8 := by
  obtain ⟨finish, run, fuel, hfinish, hbound⟩ :=
    acceptingSlotTrace_has_quantitative_exact_trace schedule positiveBound
      global hglobalWord resources hruntime hstart trace budget hclock
      hwordBudget
  have hslots : word.length ≤ PakOuterULogBridge.copiedCoreRadius x := by
    omega
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  exact ⟨finish, run, fuel, hfinish, hbound,
    exactSlotRunFuel_lt_pow_eight hR hslots hbound⟩

/-- Final slack arithmetic for composing the independently bounded bootstrap
and simulation histories. -/
theorem add_two_pow_eight_bounds_lt_pow_nine
    {R bootstrapFuel simulationFuel : ℕ} (hR : 256 ≤ R)
    (hbootstrap : bootstrapFuel < R ^ 8)
    (hsimulation : simulationFuel < R ^ 8) :
    bootstrapFuel + simulationFuel < R ^ 9 := by
  calc
    bootstrapFuel + simulationFuel < R ^ 8 + R ^ 8 :=
      Nat.add_lt_add hbootstrap hsimulation
    _ ≤ R * R ^ 8 := by
      have htwo : 2 ≤ R := by omega
      nlinarith [Nat.zero_le (R ^ 8)]
    _ = R ^ 9 := by ring

theorem outerReachesAtMost_mono
    {a b : PakULogSlotRunLedger.LedgerOuterConfig} {m n : ℕ}
    (hmn : m ≤ n)
    (h : PakOuterFrontQuantitative.OuterReachesAtMost m a b) :
    PakOuterFrontQuantitative.OuterReachesAtMost n a b := by
  rcases h with ⟨arrows, harrows, hrun⟩
  exact ⟨arrows, harrows.trans hmn, hrun⟩

/-- Prepared top-level composition: the strengthened literal bootstrap and
any quantitative simulation history sharing its exact semantic-start outer
configuration fit jointly under `R^9`. -/
theorem copiedBootstrap_then_simulation_outerAtMost_pow_nine
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int)
    (leftExtra rightExtra : List PakULogSlotRunLedger.LedgerOuterTape)
    (finish : PakULogSlotRunLedger.LedgerOuterConfig)
    (simulationFuel : ℕ)
    (hsimulationFuel : simulationFuel <
      PakOuterULogBridge.copiedCoreRadius x ^ 8)
    (hsimulation : PakOuterFrontQuantitative.OuterReachesAtMost
      simulationFuel
      (PakOuterULogBridge.anchoredFramedULogConfig
        ULogControl.State.cycleStart origin leftExtra rightExtra
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding))
      finish) :
    PakOuterFrontQuantitative.OuterReachesAtMost
      (PakOuterULogBridge.copiedCoreRadius x ^ 9)
      (PakOuterULogBridge.anchoredFramedULogConfig ULogControl.qStart origin
        leftExtra rightExtra (PakOuterULogBridge.copiedULogStartZipper x))
      finish := by
  let R := PakOuterULogBridge.copiedCoreRadius x
  have hbootstrap :=
    PakULogBootstrapExplicitFuel.copiedULogStart_outer_reaches_semanticStart_radius_pow_eight_all
      x rules input padding hword origin leftExtra rightExtra
  have hjoined := PakOuterFrontQuantitative.outerReachesAtMost_trans
    hbootstrap hsimulation
  have hR : 256 ≤ R := by
    dsimp [R]
    exact PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hsum : R ^ 8 + simulationFuel < R ^ 9 := by
    calc
      R ^ 8 + simulationFuel < R ^ 8 + R ^ 8 :=
        Nat.add_lt_add_left hsimulationFuel _
      _ ≤ R * R ^ 8 := by
        have htwo : 2 ≤ R := by omega
        nlinarith [Nat.zero_le (R ^ 8)]
      _ = R ^ 9 := by ring
  exact outerReachesAtMost_mono (Nat.le_of_lt hsum) (by
    simpa [R] using hjoined)

/-! ## Physical identification of the resource-sized bootstrap frame -/

def copiedSemanticCapacity (x input : ConcretePakSide.Word) : ℕ :=
  (PakOuterULogBridge.copiedBootstrapTail x input).length + 2

def copiedSemanticOuterTail (x : ConcretePakSide.Word) : List ULogProgram.Tape :=
  List.replicate (PakOuterULogBridge.copiedCoreRadius x - 1)
    MStarConcreteAlphabet.work

/-- The capacity reserve is not a different physical tape.  It reclassifies
the copied tail work cells as the state-workspace suffix, while the outer
reserve is the same left work block. -/
theorem copiedSemanticStart_eq_resourceBootstrapFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    (bootstrapSemanticFrame rules input padding
      (copiedSemanticCapacity x input) (copiedSemanticOuterTail x)).encode =
      .running ULogControl.State.cycleStart
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) := by
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  let R := PakOuterULogBridge.copiedCoreRadius x
  have houter : MStarConcreteAlphabet.work :: copiedSemanticOuterTail x =
      List.replicate R MStarConcreteAlphabet.work := by
    have hlen : R = (R - 1) + 1 := by omega
    rw [hlen, List.replicate_succ]
    rfl
  have hcap : copiedSemanticCapacity x input - 2 =
      (PakOuterULogBridge.copiedBootstrapTail x input).length := by
    dsimp [copiedSemanticCapacity]
    omega
  have hwork : List.replicate (copiedSemanticCapacity x input - 2)
        MStarConcreteAlphabet.work =
      PakOuterULogBridge.copiedBootstrapTail x input := by
    rw [hcap]
    cases input <;>
      simp [PakOuterULogBridge.copiedBootstrapTail]
  simp [bootstrapSemanticFrame, SemanticCycleFrame.encode,
    semanticCycleEncoding, stateWorkspace,
    PakOuterULogBridge.copiedSemanticStartZipper,
    ULogSemantics.startFrom, ULogSemantics.startCode, houter, hwork,
    R, List.append_assoc]

/-- End-to-end quantitative outer assembly from the copied `qStart` frame to
the accepting outer state.  The only remaining machine-specific input is the
uniform nonterminal-cycle bound. -/
theorem copiedAcceptingTrace_outerAtMost_pow_nine
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (schedule : ExactPositiveResourceSchedule
      (input := input) (suffix := ([] : List ULogProgram.Tape)))
    (positiveBound : PositiveContinuationCycleBound schedule
      (input := input) (suffix := ([] : List ULogProgram.Tape)) x
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x)))
    {t : ℕ} {word : List Bool}
    (resources : FrameResourceInvariant
      (bootstrapSemanticFrame rules input padding
        (copiedSemanticCapacity x input) (copiedSemanticOuterTail x)) t)
    (hruntime : PassivePath
      (bootstrapSemanticFrame rules input padding
        (copiedSemanticCapacity x input)
        (copiedSemanticOuterTail x)).runtime)
    (hstart : ULogSemantics.halted
      (bootstrapSemanticFrame rules input padding
        (copiedSemanticCapacity x input)
        (copiedSemanticOuterTail x)).config = false)
    (trace : AcceptingSlotTrace t
      (bootstrapSemanticFrame rules input padding
        (copiedSemanticCapacity x input)
        (copiedSemanticOuterTail x)).config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate
          (bootstrapSemanticFrame rules input padding
            (copiedSemanticCapacity x input)
            (copiedSemanticOuterTail x)).clockZeros
          (ulogCore clockZero) ++
        ulogCore clockOne ::
          (bootstrapSemanticFrame rules input padding
            (copiedSemanticCapacity x input)
            (copiedSemanticOuterTail x)).runtime) = some budget)
    (hwordBudget : word.length ≤ budget)
    (hwordCopied : word.length ≤ PakOuterULogBridge.copiedCoreRadius x)
    (origin : Int)
    (leftExtra rightExtra : List PakULogSlotRunLedger.LedgerOuterTape) :
    ∃ z : MStarParserExecution.Zipper ULogProgram.Tape,
      PakOuterFrontQuantitative.OuterReachesAtMost
        (PakOuterULogBridge.copiedCoreRadius x ^ 9)
        (PakOuterULogBridge.anchoredFramedULogConfig ULogControl.qStart
          origin leftExtra rightExtra
          (PakOuterULogBridge.copiedULogStartZipper x))
        (PakOuterULogBridge.anchoredFramedOuterAcceptConfig origin
          leftExtra rightExtra z) := by
  let frame := bootstrapSemanticFrame rules input padding
    (copiedSemanticCapacity x input) (copiedSemanticOuterTail x)
  have global : GlobalCopiedEnvelope x frame 0 := by
    exact bootstrapSemanticFrame_globalEnvelope x rules input padding
      (copiedSemanticCapacity x input) (copiedSemanticOuterTail x) hword
  obtain ⟨finish, run, fuel, hfinish, hbound, hfuel⟩ :=
    acceptingSlotTrace_has_quantitative_fuel_lt_pow_eight schedule
      positiveBound global (by simpa [frame] using hwordCopied) resources
      hruntime hstart trace budget hclock hwordBudget
  have hquant : ExactConcreteAcceptingBoundedFuel
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x))
      frame.encode word := ⟨finish, run, fuel, hfinish, hbound⟩
  rcases hquant.outerAtMost origin leftExtra rightExtra with
    ⟨fuel', z, startConfig, hfuel', hstartConfig, hsimulation⟩
  have hfuelSim : fuel' < PakOuterULogBridge.copiedCoreRadius x ^ 8 := by
    have hmul : word.length *
          globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x) ≤
        PakOuterULogBridge.copiedCoreRadius x *
          globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius x) :=
      Nat.mul_le_mul_right _ hwordCopied
    exact (hfuel'.trans hmul).trans_lt
      (radius_mul_globalCyclePolynomial_lt_pow_eight
        (PakOuterULogBridge.copiedCoreRadius_ge_256 x))
  have hframe := copiedSemanticStart_eq_resourceBootstrapFrame x rules input
    padding
  have hstartExpected :
      PakOuterULogTraceBridge.framedLiveConfig origin leftExtra rightExtra
          frame.encode =
        some (PakOuterULogBridge.anchoredFramedULogConfig
          ULogControl.State.cycleStart origin leftExtra rightExtra
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) := by
    rw [show frame.encode =
        .running ULogControl.State.cycleStart
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) by
      simpa [frame] using hframe]
    rfl
  have hstartEq : startConfig =
      PakOuterULogBridge.anchoredFramedULogConfig
        ULogControl.State.cycleStart origin leftExtra rightExtra
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) :=
    Option.some.inj (hstartConfig.symm.trans hstartExpected)
  subst startConfig
  exact ⟨z, copiedBootstrap_then_simulation_outerAtMost_pow_nine
    x rules input padding hword origin leftExtra rightExtra
    (PakOuterULogBridge.anchoredFramedOuterAcceptConfig origin
      leftExtra rightExtra z)
    fuel' hfuelSim hsimulation⟩

end PakFixedPolyomino.PakULogTraceResourceBound
