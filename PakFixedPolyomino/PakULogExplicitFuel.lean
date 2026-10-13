import PakFixedPolyomino.PakOuterULogTraceBridge
import PakFixedPolyomino.PakOuterFrontQuantitative

/-!
# Explicit outer arrow-length ledger for raw `U_log` stages

The front parser/copier history already carries `OuterReachesAtMost`.
The raw bootstrap/simulation bridge still collapses `ValidZeroRun n` and
`ExactConcreteCycle` into existential `OuterReaches`, discarding the
indexed microstep counts.  This file restores the length witness at the
literal outer arrow layer without touching the green upstream modules.
-/

namespace PakFixedPolyomino.PakULogExplicitFuel

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge
open PakOuterULogBridge
  (simSlotArrow actionOf_simSlotArrow sim_slot_rule mapUState_eq_sim
    frameCoreZipper frameCoreZipper_applyAction
    anchoredFramedULogConfig anchoredFramedOuterAcceptConfig)
open PakOuterULogTraceBridge
  (ConcreteLive framedLiveConfig framedLiveConfig_some_iff
    validZeroRun_live_start validStepAt_live_start)
open PakOuterFrontQuantitative
  (OuterReachesAtMost outerReachesAtMost_refl outerReachesAtMost_trans)

/-- The simulated-slot singleton used by framed ULog edges is already a
length-1 outer arrow list. -/
theorem outer_simSlotArrow_length_at_most_one
    (c : OuterConfig) (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a)
    (hstate : c.state = .sim q) (hread : c.tape c.head = .core x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c a.write) (moveHead a.move c.head)) = true) :
    ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows c = some (afterAction c a) := by
  refine ⟨[simSlotArrow q x slot a hrule], by simp, ?_⟩
  simp only [run_cons, run_nil]
  simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
    actionOf_simSlotArrow, hstate, hread, hmovable, afterAction]

theorem outerReaches_simSlotArrow_atMostOne
    (c : OuterConfig) (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a)
    (hstate : c.state = .sim q) (hread : c.tape c.head = .core x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c a.write) (moveHead a.move c.head)) = true) :
    OuterReachesAtMost 1 c (afterAction c a) := by
  rcases outer_simSlotArrow_length_at_most_one c q x slot a hrule hstate hread
      hmovable with ⟨arrows, hlen, hrun⟩
  exact ⟨arrows, hlen, hrun⟩

/-- Length-aware form of `framedRunningStep_outer`. -/
theorem framedRunningStep_outer_atMostOne
    (q q' : ULogControl.State) (slot : Fin 2) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = q')
    (haccept : q' ≠ ULogControl.qAccept)
    (hreject : q' ≠ ULogControl.qReject) :
    OuterReachesAtMost 1
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  let a' := MStarOuterProgram.mapUAction MStarULogAssembly.data a
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
  let d := anchoredFramedULogConfig q' origin leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z a' = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' a happly
  have htarget' : a'.target = (.sim q' : OuterState) := by
    simp only [a', MStarOuterProgram.mapUAction]
    rw [htarget, mapUState_eq_sim haccept hreject]
  have hhead : origin + Z'.leftRev.length =
      moveHead a'.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' a' happly'
  have htape' : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) a'.write :=
    anchoredZipperTape_applyAction origin Z Z' a' happly'
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredFramedULogConfig, writtenTape]
    rw [htarget']
    congr 1
    · simpa only [Z, Z'] using hhead.symm
    · simpa only [Z, Z'] using htape'.symm
  have htape : writtenTape c a'.write = anchoredZipperTape origin Z' := by
    simpa only [c, anchoredFramedULogConfig, writtenTape, Z] using htape'.symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write)
        (moveHead a'.move (origin + Z.leftRev.length))) = true
    rw [htape, ← hhead, anchoredZipperTape_at_head]
    rfl
  change OuterReachesAtMost 1 c d
  rw [← hafter]
  exact outerReaches_simSlotArrow_atMostOne c q z.focus slot a'
    (sim_slot_rule q z.focus slot a hrule)
    (by simp [c, anchoredFramedULogConfig])
    (by
      change anchoredZipperTape origin Z (origin + Z.leftRev.length) =
        .core z.focus
      rw [anchoredZipperTape_at_head]
      rfl)
    hmove

/-- Length-aware form of `framedAcceptingStep_outer`. -/
theorem framedAcceptingStep_outer_atMostOne
    (q : ULogControl.State) (slot : Fin 2) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = ULogControl.qAccept) :
    OuterReachesAtMost 1
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z') := by
  let a' := MStarOuterProgram.mapUAction MStarULogAssembly.data a
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
  let d := anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z a' = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' a happly
  have htarget' : a'.target = (.accept : OuterState) := by
    simp only [a', MStarOuterProgram.mapUAction, htarget]
    exact MStarULogAssembly.simulated_accept_maps_to_outer_accept
  have hhead : origin + Z'.leftRev.length =
      moveHead a'.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' a' happly'
  have htape' : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) a'.write :=
    anchoredZipperTape_applyAction origin Z Z' a' happly'
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredFramedULogConfig,
      anchoredFramedOuterAcceptConfig, writtenTape]
    rw [htarget']
    congr 1
    · simpa only [Z, Z'] using hhead.symm
    · simpa only [Z, Z'] using htape'.symm
  have htape : writtenTape c a'.write = anchoredZipperTape origin Z' := by
    simpa only [c, anchoredFramedULogConfig, writtenTape, Z] using htape'.symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write)
        (moveHead a'.move (origin + Z.leftRev.length))) = true
    rw [htape, ← hhead, anchoredZipperTape_at_head]
    rfl
  change OuterReachesAtMost 1 c d
  rw [← hafter]
  exact outerReaches_simSlotArrow_atMostOne c q z.focus slot a'
    (sim_slot_rule q z.focus slot a hrule)
    (by simp [c, anchoredFramedULogConfig])
    (by
      change anchoredZipperTape origin Z (origin + Z.leftRev.length) =
        .core z.focus
      rw [anchoredZipperTape_at_head]
      rfl)
    hmove

/-- One live-ending labelled edge expands to at most one outer arrow. -/
theorem validStepAt_live_outerAtMost
    (slot : Fin 2) (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (next : ULogBootstrapExecution.Result)
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) =
      some next)
    (hlive : ConcreteLive next) :
    ∃ d,
      framedLiveConfig origin leftExtra rightExtra next = some d ∧
      OuterReachesAtMost 1
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) d := by
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [ULogBootstrapExecution.validStepAt, hrule] at hstep
  | some a =>
      have hnext : ULogBootstrapExecution.oneStepAt slot (.running q z) = next := by
        exact Option.some.inj (by
          simpa [ULogBootstrapExecution.validStepAt, hrule] using hstep)
      cases happly : MStarParserExecution.applyAction z a with
      | none =>
          simp [ULogBootstrapExecution.oneStepAt, hrule, happly] at hnext
          subst next
          simp [ConcreteLive] at hlive
      | some z' =>
          by_cases haccept : a.target = ULogControl.qAccept
          · have hnext' : next = .accepted z' := by
              simpa [ULogBootstrapExecution.oneStepAt, hrule, happly,
                haccept] using hnext.symm
            refine ⟨anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z',
              ?_, ?_⟩
            · simp [hnext', framedLiveConfig]
            exact framedAcceptingStep_outer_atMostOne q slot origin leftExtra
              rightExtra z z' a hrule happly haccept
          · by_cases hreject : a.target = ULogControl.qReject
            · have hnext' : next = .rejected := by
                simpa [ULogBootstrapExecution.oneStepAt, hrule, happly,
                  haccept, hreject, ULogControl.qAccept,
                  ULogControl.qReject] using hnext.symm
              rw [hnext'] at hlive
              exact hlive.elim
            · have hnext' : next = .running a.target z' := by
                simpa [ULogBootstrapExecution.oneStepAt, hrule, happly,
                  haccept, hreject] using hnext.symm
              refine ⟨anchoredFramedULogConfig a.target origin leftExtra
                rightExtra z', ?_, ?_⟩
              · simp [hnext', framedLiveConfig]
              exact framedRunningStep_outer_atMostOne q a.target slot origin
                leftExtra rightExtra z z' a hrule happly rfl haccept hreject

/-- A genuine slot-zero run of length `n` expands to at most `n` outer arrows. -/
theorem validZeroRun_live_outerAtMost
    {steps : ℕ} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (run : ULogBootstrapExecution.ValidZeroRun steps start finish)
    (hfinish : ConcreteLive finish) :
    ∃ c d,
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReachesAtMost steps c d := by
  induction run with
  | nil r =>
      rcases (framedLiveConfig_some_iff origin leftExtra rightExtra r).2
          hfinish with ⟨c, hc⟩
      exact ⟨c, c, hc, hc, outerReachesAtMost_refl c⟩
  | cons r next finish n hstep tail ih =>
      have hnextLive : ConcreteLive next :=
        validZeroRun_live_start tail hfinish
      cases r with
      | accepted z => simp [ULogBootstrapExecution.validStepAt] at hstep
      | rejected => simp [ULogBootstrapExecution.validStepAt] at hstep
      | stuck => simp [ULogBootstrapExecution.validStepAt] at hstep
      | running q z =>
          rcases validStepAt_live_outerAtMost 0 q z next origin leftExtra
              rightExtra hstep hnextLive with ⟨middle, hmiddle, hfirst⟩
          rcases ih hfinish with ⟨middle', last, hmiddle', hlast, htail⟩
          have hmm : middle = middle' :=
            Option.some.inj (hmiddle.symm.trans hmiddle')
          subst middle'
          exact ⟨anchoredFramedULogConfig q origin leftExtra rightExtra z,
            last, rfl, hlast,
            by
              simpa [Nat.succ_eq_add_one, Nat.add_comm] using
                outerReachesAtMost_trans hfirst htail⟩

/-- One exact first-hit cycle expands to at most
`choicePrefix.steps + 1 + cycleSuffix.steps` outer arrows. -/
theorem exactConcreteCycle_live_outerAtMost
    {slot : Bool} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot start finish)
    (hfinish : ConcreteLive finish) :
    ∃ c d,
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReachesAtMost
        (cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps) c d := by
  -- Destructure so `choice` and `choicePrefix` are independent binders;
  -- cases on `cycle.choice` otherwise rewrites the dependent length bound.
  rcases cycle with ⟨choice, branch, choicePrefix, selected, cycleSuffix⟩
  have hbranchLive : ConcreteLive branch :=
    validZeroRun_live_start cycleSuffix.valid hfinish
  have hchoiceLive : ConcreteLive choice :=
    validStepAt_live_start selected
  rcases validZeroRun_live_outerAtMost origin leftExtra rightExtra
      choicePrefix.valid hchoiceLive with
    ⟨startConfig, choiceConfig, hstart, hchoice, hprefix⟩
  cases choice with
  | accepted z =>
      simp [ULogBootstrapExecution.validStepAt] at selected
  | rejected =>
      simp [ULogBootstrapExecution.validStepAt] at selected
  | stuck =>
      simp [ULogBootstrapExecution.validStepAt] at selected
  | running q z =>
      rcases validStepAt_live_outerAtMost (ULogBytecode.slotIndex slot) q z
          branch origin leftExtra rightExtra selected hbranchLive with
        ⟨branchConfig, hbranch, hselectedBound⟩
      rcases validZeroRun_live_outerAtMost origin leftExtra rightExtra
          cycleSuffix.valid hfinish with
        ⟨branchConfig', finishConfig, hbranch', hfinishConfig, hsuffix⟩
      have hchoiceConfig : choiceConfig =
          anchoredFramedULogConfig q origin leftExtra rightExtra z :=
        Option.some.inj (hchoice.symm.trans rfl)
      have hbranchConfig : branchConfig = branchConfig' :=
        Option.some.inj (hbranch.symm.trans hbranch')
      subst choiceConfig
      subst branchConfig'
      exact ⟨startConfig, finishConfig, hstart, hfinishConfig,
        by
          have hmid : OuterReachesAtMost (choicePrefix.steps + 1)
              startConfig branchConfig :=
            outerReachesAtMost_trans hprefix hselectedBound
          simpa [Nat.add_assoc] using outerReachesAtMost_trans hmid hsuffix⟩

/-- A whole exact labelled slot run expands to an outer arrow list whose length
is the sum of the exact per-cycle fuels
`choicePrefix.steps + 1 + cycleSuffix.steps`. -/
theorem exactConcreteSlotRun_live_outerAtMost
    {slots : List Bool} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (run : ULogBootstrapExecution.ExactConcreteSlotRun start slots finish)
    (hfinish : ConcreteLive finish) :
    ∃ (fuel : ℕ) (c d : OuterConfig),
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReachesAtMost fuel c d := by
  induction run with
  | nil r =>
      rcases (framedLiveConfig_some_iff origin leftExtra rightExtra r).2
          hfinish with ⟨c, hc⟩
      exact ⟨0, c, c, hc, hc, outerReachesAtMost_refl c⟩
  | cons start next finish slot slots cycle tail ih =>
      rcases ih hfinish with
        ⟨fuelTail, nextConfig, finishConfig, hnextConfig, hfinishConfig, htail⟩
      have hnextLive : ConcreteLive next :=
        (framedLiveConfig_some_iff origin leftExtra rightExtra next).1
          ⟨nextConfig, hnextConfig⟩
      rcases exactConcreteCycle_live_outerAtMost origin leftExtra rightExtra
          cycle hnextLive with
        ⟨startConfig, nextConfig', hstartConfig, hnextConfig', hcycle⟩
      have hnextEq : nextConfig' = nextConfig :=
        Option.some.inj (hnextConfig'.symm.trans hnextConfig)
      subst nextConfig'
      exact ⟨cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps + fuelTail,
        startConfig, finishConfig, hstartConfig, hfinishConfig,
        by
          simpa [Nat.add_assoc] using
            outerReachesAtMost_trans hcycle htail⟩

/-- An exact accepting slot trace expands to a literal accepting outer path
with an explicit arrow-length fuel accumulated from its cycles. -/
theorem exactConcreteAcceptingSlotTrace_outerAtMost
    {slots : List Bool} {start : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (trace : ULogBootstrapExecution.ExactConcreteAcceptingSlotTrace start slots) :
    ∃ (fuel : ℕ) (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (startConfig : OuterConfig),
      framedLiveConfig origin leftExtra rightExtra start = some startConfig ∧
      OuterReachesAtMost fuel startConfig
        (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z) := by
  rcases trace with ⟨finish, run, haccept⟩
  cases hfinish : finish with
  | running q z =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | rejected =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | stuck =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | accepted z =>
      subst finish
      rcases exactConcreteSlotRun_live_outerAtMost origin leftExtra rightExtra
          run (by trivial) with
        ⟨fuel, startConfig, finishConfig, hstartConfig, hfinishConfig, hrun⟩
      have hfinishConfig' : finishConfig =
          anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z :=
        Option.some.inj (hfinishConfig.symm.trans rfl)
      subst finishConfig
      exact ⟨fuel, z, startConfig, hstartConfig, hrun⟩

/-- Length-aware form of `ulogReaches_running_outer_framed`: the exact fuel
witness of `Reaches` is retained as an outer arrow-length bound. -/
theorem ulogReaches_running_outer_framed_atMost
    (q q' : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (hreach : ULogBootstrapExecution.Reaches (.running q z) (.running q' z')) :
    ∃ (fuel : ℕ),
      OuterReachesAtMost fuel
        (anchoredFramedULogConfig q origin leftExtra rightExtra z)
        (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  rcases hreach with ⟨fuel, hrun⟩
  refine ⟨fuel, ?_⟩
  induction fuel generalizing q z with
  | zero =>
      simp only [ULogBootstrapExecution.run] at hrun
      cases hrun
      exact outerReachesAtMost_refl _
  | succ fuel ih =>
      change ULogBootstrapExecution.run fuel
        (ULogBootstrapExecution.oneStep (.running q z)) =
          .running q' z' at hrun
      cases hfirst : ULogBootstrapExecution.oneStep (.running q z) with
      | accepted za => simp [hfirst] at hrun
      | rejected => simp [hfirst] at hrun
      | stuck => simp [hfirst] at hrun
      | running q₁ z₁ =>
          have htail : ULogBootstrapExecution.run fuel (.running q₁ z₁) =
              .running q' z' := by simpa [hfirst] using hrun
          rcases (PakOuterULogBridge.ulogOneStep_eq_running_iff q q₁ z z₁).mp
              hfirst with ⟨a, hrule, happly, htarget, haccept, hreject⟩
          have hfirstBound :
              OuterReachesAtMost 1
                (anchoredFramedULogConfig q origin leftExtra rightExtra z)
                (anchoredFramedULogConfig q₁ origin leftExtra rightExtra z₁) :=
            framedRunningStep_outer_atMostOne q q₁ 0 origin leftExtra rightExtra
              z z₁ a hrule happly htarget haccept hreject
          have htailBound :
              OuterReachesAtMost fuel
                (anchoredFramedULogConfig q₁ origin leftExtra rightExtra z₁)
                (anchoredFramedULogConfig q' origin leftExtra rightExtra z') :=
            ih q₁ z₁ htail
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            outerReachesAtMost_trans hfirstBound htailBound

/-- Length-aware form of `copiedULogStart_outer_reaches_semanticStart`. -/
theorem copiedULogStart_outer_reaches_semanticStart_atMost
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    ∃ (fuel : ℕ),
      OuterReachesAtMost fuel
        (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
          (PakOuterULogBridge.copiedULogStartZipper x))
        (anchoredFramedULogConfig ULogControl.State.cycleStart origin
          leftExtra rightExtra
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) := by
  have h := PakOuterULogBridge.copiedULogStart_reaches_semanticStart
    x rules input padding hword
  rw [PakOuterULogBridge.copiedSemanticStartEncoding_eq_running] at h
  exact ulogReaches_running_outer_framed_atMost ULogControl.qStart
    ULogControl.State.cycleStart origin leftExtra rightExtra
    (PakOuterULogBridge.copiedULogStartZipper x)
    (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) h

/-- Exact constructive fuel for the nonempty bootstrap translation segment:
`3 + bits.length + 1 + (bits.length + 1) + 1 = 2 * bits.length + 6`. -/
theorem reaches_bootstrap_nonempty_fuel_le
    (b : Bool) (bits : List Bool) (left tail : List ULogProgram.Tape) :
    ∃ (fuel : ℕ),
      fuel ≤ 2 * bits.length + 6 ∧
      ULogBootstrapExecution.run fuel
          (.running .start
            ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
              bits.map ULogProgram.bitTape ++
                MStarConcreteAlphabet.work :: tail⟩) =
        .running .framePayloadLength
          ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
            (b :: bits).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  -- Reconstruct the same five-piece witness used by `reaches_bootstrap_nonempty`,
  -- then sum the exact fuels rather than discarding them in `reaches_trans`.
  have h₀ :
      ULogBootstrapExecution.run 3
          (.running .start
            ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
              bits.map ULogProgram.bitTape ++
                MStarConcreteAlphabet.work :: tail⟩) =
        .running .seekPayload
          (ULogBootstrapExecution.beforePayload bits
            (ULogProgram.codeTape b :: ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
              left) tail) := by
    cases bits <;>
      simp [ULogBootstrapExecution.run, ULogBootstrapExecution.beforePayload,
        ULogBootstrapExecution.start_bit_step,
        ULogBootstrapExecution.translateCode_step,
        ULogBootstrapExecution.framePayload_step, List.append_assoc]
  have h₁ :
      ULogBootstrapExecution.run bits.length
          (.running .seekPayload
            (ULogBootstrapExecution.beforePayload bits
              (ULogProgram.codeTape b :: ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
                left) tail)) =
        .running .seekPayload
          (ULogBootstrapExecution.afterPayload bits
            (ULogProgram.codeTape b :: ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
              left) tail) :=
    ULogBootstrapExecution.run_seekPayload_bits bits _ tail
  have h₂ :
      ULogBootstrapExecution.oneStep
          (.running .seekPayload
            (ULogBootstrapExecution.afterPayload bits
              (ULogProgram.codeTape b :: ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
                left) tail)) =
        .running .translateReturn
          (ULogBootstrapExecution.beforeReturn (b :: bits) left tail) := by
    -- Same case split as `reaches_bootstrap_nonempty`.
    unfold ULogBootstrapExecution.beforeReturn ULogBootstrapExecution.afterPayload
    rw [show (b :: bits).reverse = bits.reverse ++ [b] by simp]
    cases hr : bits.reverse with
    | nil =>
        have hbits : bits = [] := by
          simpa using congrArg List.reverse hr
        subst bits
        exact ULogBootstrapExecution.seekPayload_end_step
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail
          (ULogProgram.codeTape b)
    | cons c cs =>
        have hmap :
            (bits.map ULogProgram.codeTape).reverse =
              ULogProgram.codeTape c :: cs.map ULogProgram.codeTape := by
          calc
            (bits.map ULogProgram.codeTape).reverse =
                bits.reverse.map ULogProgram.codeTape := by
              exact (List.map_reverse (l := bits) (f := ULogProgram.codeTape)).symm
            _ = ULogProgram.codeTape c :: cs.map ULogProgram.codeTape := by
              rw [hr]; rfl
        simp only [hmap, hr, List.cons_append, List.map_append, List.map_cons,
          List.map_nil, List.append_nil]
        simpa [List.append_assoc] using
          (ULogBootstrapExecution.seekPayload_end_step
            (cs.map ULogProgram.codeTape ++
              ULogProgram.codeTape b ::
                ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            tail (ULogProgram.codeTape c))
  have h₃ :
      ULogBootstrapExecution.run (b :: bits).length
          (.running .translateReturn
            (ULogBootstrapExecution.beforeReturn (b :: bits) left tail)) =
        .running .translateReturn
          (ULogBootstrapExecution.afterReturn (b :: bits) left tail) :=
    ULogBootstrapExecution.run_translateReturn_bits (b :: bits) left tail
  have h₄ :
      ULogBootstrapExecution.oneStep
          (.running .translateReturn
            (ULogBootstrapExecution.afterReturn (b :: bits) left tail)) =
        .running .framePayloadLength
          ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
            (b :: bits).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ :=
    ULogBootstrapExecution.translateReturn_mark_step left _
  -- Compose the five exact runs: 3 + |bits| + 1 + (|bits|+1) + 1.
  refine ⟨3 + bits.length + 1 + (bits.length + 1) + 1, ?_, ?_⟩
  · omega
  · -- Unfold the cumulative fuel into the successive run pieces above.
    have h01 :
        ULogBootstrapExecution.run (3 + bits.length)
            (.running .start
              ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
                bits.map ULogProgram.bitTape ++
                  MStarConcreteAlphabet.work :: tail⟩) =
          .running .seekPayload
            (ULogBootstrapExecution.afterPayload bits
              (ULogProgram.codeTape b ::
                ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail) := by
      rw [ULogBootstrapExecution.run_add, h₀, h₁]
    have h012 :
        ULogBootstrapExecution.run (3 + bits.length + 1)
            (.running .start
              ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
                bits.map ULogProgram.bitTape ++
                  MStarConcreteAlphabet.work :: tail⟩) =
          .running .translateReturn
            (ULogBootstrapExecution.beforeReturn (b :: bits) left tail) := by
      rw [ULogBootstrapExecution.run_add, h01]
      simpa [ULogBootstrapExecution.run] using h₂
    have h0123 :
        ULogBootstrapExecution.run (3 + bits.length + 1 + (bits.length + 1))
            (.running .start
              ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
                bits.map ULogProgram.bitTape ++
                  MStarConcreteAlphabet.work :: tail⟩) =
          .running .translateReturn
            (ULogBootstrapExecution.afterReturn (b :: bits) left tail) := by
      rw [ULogBootstrapExecution.run_add, h012]
      simpa using h₃
    rw [ULogBootstrapExecution.run_add, h0123]
    simpa [ULogBootstrapExecution.run, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h₄

/-- Exact constructive fuel for the workspace bootstrap scan plus translation:
`(n + 1) + (2 * bits.length + 6)`. -/
theorem reaches_bootstrap_from_workspace_fuel_le
    (n : ℕ) (b : Bool) (bits : List Bool)
    (source tail : List ULogProgram.Tape) :
    ∃ (fuel : ℕ),
      fuel ≤ n + 2 * bits.length + 7 ∧
      ULogBootstrapExecution.run fuel
          (.running .start
            ⟨source, MStarConcreteAlphabet.work,
              List.replicate n MStarConcreteAlphabet.work ++
                ULogProgram.bitTape b ::
                  (bits.map ULogProgram.bitTape ++
                    MStarConcreteAlphabet.work :: tail)⟩) =
        .running .framePayloadLength
          ⟨List.replicate n MStarConcreteAlphabet.work ++ source,
            ULogAlphabet.ulogCore ULogAlphabet.pcMark,
            (b :: bits).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  have hscan :
      ULogBootstrapExecution.run (n + 1)
          (.running .start
            ⟨source, MStarConcreteAlphabet.work,
              List.replicate n MStarConcreteAlphabet.work ++
                ULogProgram.bitTape b ::
                  (bits.map ULogProgram.bitTape ++
                    MStarConcreteAlphabet.work :: tail)⟩) =
        .running .start
          ⟨MStarConcreteAlphabet.work ::
              (List.replicate n MStarConcreteAlphabet.work ++ source),
            ULogProgram.bitTape b,
            bits.map ULogProgram.bitTape ++
              MStarConcreteAlphabet.work :: tail⟩ := by
    simpa [ULogBootstrapExecution.beforeStartWork,
      ULogBootstrapExecution.afterStartWork, List.replicate_succ,
      List.append_assoc] using
      (ULogBootstrapExecution.run_start_work (n + 1) source
        (ULogProgram.bitTape b)
        (bits.map ULogProgram.bitTape ++
          MStarConcreteAlphabet.work :: tail))
  rcases reaches_bootstrap_nonempty_fuel_le b bits
      (List.replicate n MStarConcreteAlphabet.work ++ source) tail with
    ⟨fuel₂, hfuel₂, h₂⟩
  refine ⟨(n + 1) + fuel₂, ?_, ?_⟩
  · omega
  · rw [ULogBootstrapExecution.run_add, hscan, h₂]

/-- Crude closed form for the copied bootstrap outer-arrow fuel in terms of the
copied radius and the encoded universal instance length.  This is intentionally
loose; it only has to sit under `R^9`. -/
def copiedBootstrapOuterFuel (x : ConcretePakSide.Word) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 7

theorem copiedBootstrapOuterFuel_lt_radius_pow_nine
    (x : ConcretePakSide.Word) :
    copiedBootstrapOuterFuel x <
      (PakOuterULogBridge.copiedCoreRadius x) ^ 9 := by
  have hR : 256 ≤ PakOuterULogBridge.copiedCoreRadius x :=
    PakOuterULogBridge.copiedCoreRadius_ge_256 x
  -- For R ≥ 256 one already has R + 2|x| + 7 < R^9 once |x| ≤ R,
  -- and the copied word always fits inside the radius workspace.
  have hx : x.length ≤ PakOuterULogBridge.copiedCoreRadius x := by
    -- The encoded word is placed inside a radius-R work buffer; any concrete
    -- word length is dominated by R ≥ 256 ≥ 0.
    have : 0 ≤ PakOuterULogBridge.copiedCoreRadius x := Nat.zero_le _
    -- Use R ≥ 256 and the elementary inequality |x| ≤ 2^(8(|x|+1)) = R.
    have hexp :
        x.length ≤ 2 ^ (8 * (x.length + 1)) := by
      have hsmall : x.length ≤ 2 ^ x.length :=
        (x.length.lt_pow_self (by decide : 1 < 2)).le
      -- Strengthen to the actual radius exponent 8(|x|+1).
      have hmono :
          2 ^ x.length ≤ 2 ^ (8 * (x.length + 1)) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact Nat.le_trans hsmall hmono
    simpa [PakOuterULogBridge.copiedCoreRadius,
      MStarParserCopySpec.timeExponent] using hexp
  -- fuel = R + 2|x| + 7 ≤ R + 2R + 7 = 3R + 7 ≤ 3R + R = 4R < R^9 for R ≥ 256.
  unfold copiedBootstrapOuterFuel
  have hfuel : PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 7 ≤
      4 * PakOuterULogBridge.copiedCoreRadius x := by omega
  have hquad :
      4 * PakOuterULogBridge.copiedCoreRadius x <
        (PakOuterULogBridge.copiedCoreRadius x) ^ 2 := by
    simp only [pow_two]
    nlinarith
  have hpow :
      (PakOuterULogBridge.copiedCoreRadius x) ^ 2 ≤
        (PakOuterULogBridge.copiedCoreRadius x) ^ 9 :=
    Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 9)
  exact lt_of_le_of_lt hfuel (lt_of_lt_of_le hquad hpow)

end PakFixedPolyomino.PakULogExplicitFuel
