import PakFixedPolyomino.PakOuterULogBridge

/-!
# Raw exact `U_log` traces as literal outer arrow lists

This file turns the first-hit execution objects used by raw reflection into
the labelled-arrow histories needed by the tableau construction.
-/

namespace PakFixedPolyomino.PakOuterULogTraceBridge

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge PakOuterULogBridge

abbrev OuterTape := MStarULogAssembly.Tape
abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig

/-- An explicit configuration-by-configuration witness for a literal outer
arrow list.  Unlike `OuterReaches`, it retains every intermediate step. -/
inductive OuterArrowHistory : OuterConfig → List MStarULogAssembly.Arrow →
    OuterConfig → Type
  | nil (c : OuterConfig) : OuterArrowHistory c [] c
  | cons (c next finish : OuterConfig) (a : MStarULogAssembly.Arrow)
      (arrows : List MStarULogAssembly.Arrow)
      (step : FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some next)
      (tail : OuterArrowHistory next arrows finish) :
      OuterArrowHistory c (a :: arrows) finish

theorem OuterArrowHistory.run_eq
    {start finish : OuterConfig} {arrows : List MStarULogAssembly.Arrow}
    (h : OuterArrowHistory start arrows finish) :
    FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable arrows start = some finish := by
  induction h with
  | nil c => rfl
  | cons c next finish a arrows hstep tail ih =>
      simp [hstep, ih]

/-- Every successful literal run can be decomposed into its actual sequence
of configurations without adding a reachability certificate as input. -/
def OuterArrowHistory.of_run_eq
    (arrows : List MStarULogAssembly.Arrow) (start finish : OuterConfig)
    (h : FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable arrows start = some finish) :
    OuterArrowHistory start arrows finish := by
  induction arrows generalizing start with
  | nil =>
      simp only [FiniteOneTapeSemantics.run_nil] at h
      have hfinish : start = finish := Option.some.inj h
      subst finish
      exact .nil start
  | cons a arrows ih =>
      simp only [FiniteOneTapeSemantics.run_cons] at h
      cases hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
          MStarOuterProgram.movable start a with
      | none => simp [hstep] at h
      | some next =>
          have htail : FiniteOneTapeSemantics.run MStarULogAssembly.program
              MStarOuterProgram.movable arrows next = some finish := by
            simpa [hstep] using h
          exact .cons start next finish a arrows hstep (ih next htail)

theorem OuterReaches.has_history {start finish : OuterConfig}
    (h : OuterReaches start finish) :
    ∃ arrows, Nonempty (OuterArrowHistory start arrows finish) := by
  rcases h with ⟨arrows, hrun⟩
  exact ⟨arrows, ⟨OuterArrowHistory.of_run_eq arrows start finish hrun⟩⟩

/- The indexed-history view is being rebuilt in a separate structural batch.
The inductive history and its exact `run_eq`/`of_run_eq` bridge above remain
the public, kernel-checked interface in the meantime.

namespace OuterArrowHistory

def configAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    Fin (arrows.length + 1) → OuterConfig := by
  intro t
  induction H with
  | nil c => exact c
  | cons c next finish a arrows hstep tail ih =>
      by_cases ht : t.1 = 0
      · exact c
      · exact ih ⟨t.1 - 1, by simp at t; omega⟩

def arrowAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (_H : OuterArrowHistory start arrows finish) :
    Fin arrows.length → MStarULogAssembly.Arrow := fun k => arrows.get k

theorem configAt_zero {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configAt ⟨0, Nat.zero_lt_succ _⟩ = start := by
  cases H <;> simp [configAt]

theorem configAt_finish {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configAt ⟨arrows.length, Nat.lt_succ_self _⟩ = finish := by
  induction H with
  | nil c => rfl
  | cons c next finish a arrows hstep tail ih =>
      simp only [List.length_cons]
      rw [show (OuterArrowHistory.cons c next finish a arrows hstep tail).configAt
          ⟨arrows.length + 1, by omega⟩ =
          tail.configAt ⟨arrows.length, Nat.lt_succ_self _⟩ by
        simp [configAt]]
      exact ih

theorem arrowAt_get {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) (k : Fin arrows.length) :
    arrows.get k = H.arrowAt k := rfl

theorem step_configAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) (k : Fin arrows.length) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
      (H.configAt ⟨k.1, Nat.lt_succ_of_lt k.2⟩) (H.arrowAt k) =
        some (H.configAt ⟨k.1 + 1, by omega⟩) := by
  induction H with
  | nil c => exact Fin.elim0 k
  | cons c next finish a arrows hstep tail ih =>
      by_cases hk : k.1 = 0
      · have hk0 : k = ⟨0, by simp⟩ := Fin.eq_of_val_eq hk
        subst k
        simpa [configAt, arrowAt] using hstep
      · let k' : Fin arrows.length := ⟨k.1 - 1, by
          have hklt := k.2
          simp only [List.length_cons] at hklt
          omega⟩
        have hkval : k.1 = k'.1 + 1 := by
          dsimp [k']
          omega
        have hget : (a :: arrows).get k = arrows.get k' := by
          rcases k with ⟨kval, hklt⟩
          cases kval with
          | zero => exact (hk rfl).elim
          | succ kval => rfl
        rw [show (OuterArrowHistory.cons c next finish a arrows hstep tail).arrowAt k =
            tail.arrowAt k' by simpa [arrowAt] using hget]
        rw [show (OuterArrowHistory.cons c next finish a arrows hstep tail).configAt
            ⟨k.1, Nat.lt_succ_of_lt k.2⟩ =
              tail.configAt ⟨k'.1, Nat.lt_succ_of_lt k'.2⟩ by
          simp [configAt, hk, k', hkval]]
        rw [show (OuterArrowHistory.cons c next finish a arrows hstep tail).configAt
            ⟨k.1 + 1, by omega⟩ =
              tail.configAt ⟨k'.1 + 1, by omega⟩ by
          simp [configAt, k', hkval]]
        exact ih k'

end OuterArrowHistory
-/

namespace OuterArrowHistory

/-- Chronological configurations of an explicit history, including both
endpoints.  This nondependent list view avoids eliminating a history through
a dependent `Fin` motive. -/
def configs {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow} :
    OuterArrowHistory start arrows finish → List OuterConfig
  | .nil c => [c]
  | .cons c _ _ _ _ _ tail => c :: configs tail

@[simp] theorem configs_length {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configs.length = arrows.length + 1 := by
  induction H with
  | nil c => rfl
  | cons c next finish a arrows hstep tail ih => simp [configs, ih]

@[simp] theorem configs_head {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configs.head? = some start := by
  cases H <;> rfl

def configAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish)
    (t : Fin (arrows.length + 1)) : OuterConfig :=
  H.configs.get ⟨t.1, by simpa using t.2⟩

def arrowAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (_H : OuterArrowHistory start arrows finish)
    (k : Fin arrows.length) : MStarULogAssembly.Arrow := arrows.get k

@[simp] theorem configAt_zero {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configAt ⟨0, Nat.zero_lt_succ _⟩ = start := by
  cases H <;> rfl

@[simp] theorem configAt_finish {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) :
    H.configAt ⟨arrows.length, Nat.lt_succ_self _⟩ = finish := by
  induction H with
  | nil c => rfl
  | cons c next finish a arrows hstep tail ih =>
      simpa [configAt, configs] using ih

@[simp] theorem arrowAt_eq_get {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) (k : Fin arrows.length) :
    H.arrowAt k = arrows.get k := rfl

theorem step_configAt {start finish : OuterConfig}
    {arrows : List MStarULogAssembly.Arrow}
    (H : OuterArrowHistory start arrows finish) (k : Fin arrows.length) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
      (H.configAt ⟨k.1, Nat.lt_succ_of_lt k.2⟩) (H.arrowAt k) =
        some (H.configAt ⟨k.1 + 1, by omega⟩) := by
  induction H with
  | nil c => exact Fin.elim0 k
  | cons c next finish a arrows hstep tail ih =>
      rcases k with ⟨k, hk⟩
      cases k with
      | zero =>
          cases tail <;> simpa [configAt, arrowAt, configs] using hstep
      | succ k =>
          let k' : Fin arrows.length := ⟨k, by simpa using hk⟩
          simpa [configAt, arrowAt, configs, k'] using ih k'

end OuterArrowHistory

def copiedSemanticFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.SemanticCycleFrame input
      (PakOuterULogBridge.copiedBootstrapTail x input) where
  config := ULogSemantics.startFrom rules input
  clockZeros := padding.length
  runtime := [ULogAlphabet.ulogCore ULogAlphabet.clockSep]
  capacity := 2
  outer := List.replicate (PakOuterULogBridge.copiedCoreRadius x)
    MStarConcreteAlphabet.work

theorem copiedSemanticFrame_encode
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    (copiedSemanticFrame x rules input padding).encode =
      .running ULogControl.State.cycleStart
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) :=
  rfl

/-- The quantitative forward witness keeps every operational phase separate.
This is deliberately stronger than `OuterReaches`: later bounds can charge
the start edge, parser, copier entry, copier, bootstrap, and simulated cycles
independently without reconstructing a hidden concatenation. -/
structure SideOuterAcceptingStages
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) where
  front : PakParserOuterBridge.SideStartParserCopierStages x
  origin : Int
  leftExtra : List OuterTape
  group_eq : front.finish =
    anchoredFramedULogConfig ULogControl.qStart origin leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x)
      (PakOuterULogBridge.copiedULogStartZipper x)
  bootstrapArrows : List MStarULogAssembly.Arrow
  bootstrap_run : FiniteOneTapeSemantics.run MStarULogAssembly.program
    MStarOuterProgram.movable bootstrapArrows front.finish =
      some (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding))
  simulationArrows : List MStarULogAssembly.Arrow
  acceptZipper : MStarParserExecution.Zipper ULogProgram.Tape
  simulation_run : FiniteOneTapeSemantics.run MStarULogAssembly.program
    MStarOuterProgram.movable simulationArrows
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x)
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) =
      some (anchoredFramedOuterAcceptConfig origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x) acceptZipper)

namespace SideOuterAcceptingStages

def allArrows {x : ConcretePakSide.Word} {rules : List ULogBytecode.RuleCode}
    {input padding : List Bool}
    (S : SideOuterAcceptingStages x rules input padding) :
    List MStarULogAssembly.Arrow :=
  [S.front.startArrow] ++
    (S.front.parserArrows ++
      (S.front.entryArrows ++
        (S.front.copierArrows ++ (S.bootstrapArrows ++ S.simulationArrows))))

theorem allArrows_length {x : ConcretePakSide.Word}
    {rules : List ULogBytecode.RuleCode} {input padding : List Bool}
    (S : SideOuterAcceptingStages x rules input padding) :
    S.allArrows.length = 1 + S.front.parserArrows.length +
      S.front.entryArrows.length + S.front.copierArrows.length +
      S.bootstrapArrows.length + S.simulationArrows.length := by
  simp [allArrows]
  omega

theorem allArrows_run {x : ConcretePakSide.Word}
    {rules : List ULogBytecode.RuleCode} {input padding : List Bool}
    (S : SideOuterAcceptingStages x rules input padding) :
    FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable S.allArrows
      (PakSideScannerRow.sideEncodedStartConfig x) =
      some (anchoredFramedOuterAcceptConfig S.origin S.leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x) S.acceptZipper) := by
  unfold allArrows
  rw [PakParserOuterBridge.outerRun_append]
  simp only [FiniteOneTapeSemantics.run_cons, FiniteOneTapeSemantics.run_nil,
    S.front.start_step, Option.bind_some]
  rw [PakParserOuterBridge.outerRun_append, S.front.parser_run]
  simp only [Option.bind_some]
  rw [PakParserOuterBridge.outerRun_append, S.front.entry_run]
  simp only [Option.bind_some]
  rw [PakParserOuterBridge.outerRun_append, S.front.copier_run]
  simp only [Option.bind_some]
  rw [PakParserOuterBridge.outerRun_append, S.bootstrap_run]
  simp only [Option.bind_some]
  exact S.simulation_run

def toHistory {x : ConcretePakSide.Word} {rules : List ULogBytecode.RuleCode}
    {input padding : List Bool}
    (S : SideOuterAcceptingStages x rules input padding) :
    OuterArrowHistory (PakSideScannerRow.sideEncodedStartConfig x) S.allArrows
      (anchoredFramedOuterAcceptConfig S.origin S.leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x) S.acceptZipper) :=
  OuterArrowHistory.of_run_eq S.allArrows _ _ S.allArrows_run

end SideOuterAcceptingStages

def ConcreteLive : ULogBootstrapExecution.Result → Prop
  | .running _ _ | .accepted _ => True
  | .rejected | .stuck => False

def framedLiveConfig (origin : Int) (leftExtra rightExtra : List OuterTape) :
    ULogBootstrapExecution.Result → Option OuterConfig
  | .running q z => some
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
  | .accepted z => some
      (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z)
  | .rejected | .stuck => none

theorem framedLiveConfig_some_iff
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (r : ULogBootstrapExecution.Result) :
    (∃ c, framedLiveConfig origin leftExtra rightExtra r = some c) ↔
      ConcreteLive r := by
  cases r <;> simp [framedLiveConfig, ConcreteLive]

/-- A genuine zero-slot path ending live cannot have started at a terminal
result, since terminals have no valid outgoing slot. -/
theorem validZeroRun_live_start
    {steps : ℕ} {start finish : ULogBootstrapExecution.Result}
    (run : ULogBootstrapExecution.ValidZeroRun steps start finish)
    (hfinish : ConcreteLive finish) : ConcreteLive start := by
  induction run with
  | nil r => exact hfinish
  | cons r next finish n hstep tail ih =>
      cases r with
      | running q z => trivial
      | accepted z => simp [ULogBootstrapExecution.validStepAt] at hstep
      | rejected => simp [ULogBootstrapExecution.validStepAt] at hstep
      | stuck => simp [ULogBootstrapExecution.validStepAt] at hstep

/-- The immediate successor in a live-ending valid zero path is live as
well. -/
theorem validZeroRun_live_next
    {n : ℕ} {start next finish : ULogBootstrapExecution.Result}
    (hstep : ULogBootstrapExecution.validStepAt 0 start = some next)
    (tail : ULogBootstrapExecution.ValidZeroRun n next finish)
    (hfinish : ConcreteLive finish) : ConcreteLive next :=
  validZeroRun_live_start tail hfinish

/-- One valid labelled `U_log` edge whose successor is live becomes one
literal outer arrow.  Reject/stuck successors are excluded by `hlive`; no
semantic membership is used. -/
theorem validStepAt_live_outer
    (slot : Fin 2) (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (next : ULogBootstrapExecution.Result)
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) =
      some next)
    (hlive : ConcreteLive next) :
    ∃ d,
      framedLiveConfig origin leftExtra rightExtra next = some d ∧
      OuterReaches
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
            exact framedAcceptingStep_outer q slot origin leftExtra rightExtra
              z z' a hrule happly haccept
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
              exact framedRunningStep_outer q a.target slot origin leftExtra
                rightExtra z z' a hrule happly rfl haccept hreject

theorem validStepAt_live_start
    {slot : Fin 2} {start next : ULogBootstrapExecution.Result}
    (hstep : ULogBootstrapExecution.validStepAt slot start = some next) :
    ConcreteLive start := by
  cases start with
  | running q z => trivial
  | accepted z => simp [ULogBootstrapExecution.validStepAt] at hstep
  | rejected => simp [ULogBootstrapExecution.validStepAt] at hstep
  | stuck => simp [ULogBootstrapExecution.validStepAt] at hstep

/-- A whole genuine slot-zero run ending in a live result expands to a
literal outer arrow list between the corresponding framed configurations. -/
theorem validZeroRun_live_outer
    {steps : ℕ} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (run : ULogBootstrapExecution.ValidZeroRun steps start finish)
    (hfinish : ConcreteLive finish) :
    ∃ c d,
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReaches c d := by
  induction run with
  | nil r =>
      rcases (framedLiveConfig_some_iff origin leftExtra rightExtra r).2
          hfinish with ⟨c, hc⟩
      exact ⟨c, c, hc, hc, outerReaches_refl c⟩
  | cons r next finish n hstep tail ih =>
      have hnextLive : ConcreteLive next :=
        validZeroRun_live_start tail hfinish
      cases r with
      | accepted z => simp [ULogBootstrapExecution.validStepAt] at hstep
      | rejected => simp [ULogBootstrapExecution.validStepAt] at hstep
      | stuck => simp [ULogBootstrapExecution.validStepAt] at hstep
      | running q z =>
          rcases validStepAt_live_outer 0 q z next origin leftExtra rightExtra
              hstep hnextLive with ⟨middle, hmiddle, hfirst⟩
          rcases ih hfinish with ⟨middle', last, hmiddle', hlast, htail⟩
          have hmm : middle = middle' :=
            Option.some.inj (hmiddle.symm.trans hmiddle')
          subst middle'
          exact ⟨anchoredFramedULogConfig q origin leftExtra rightExtra z,
            last, rfl, hlast, outerReaches_trans hfirst htail⟩

/-- One exact first-hit cycle ending live expands to the concatenation of its
zero-prefix, selected labelled slot, and zero-suffix outer arrows. -/
theorem exactConcreteCycle_live_outer
    {slot : Bool} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot start finish)
    (hfinish : ConcreteLive finish) :
    ∃ c d,
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReaches c d := by
  have hbranchLive : ConcreteLive cycle.branch :=
    validZeroRun_live_start cycle.cycleSuffix.valid hfinish
  have hchoiceLive : ConcreteLive cycle.choice :=
    validStepAt_live_start cycle.selected
  rcases validZeroRun_live_outer origin leftExtra rightExtra
      cycle.choicePrefix.valid hchoiceLive with
    ⟨startConfig, choiceConfig, hstart, hchoice, hprefix⟩
  cases hchoiceResult : cycle.choice with
  | accepted z =>
      have hs := cycle.selected
      rw [hchoiceResult] at hs
      simp [ULogBootstrapExecution.validStepAt] at hs
  | rejected =>
      have hs := cycle.selected
      rw [hchoiceResult] at hs
      simp [ULogBootstrapExecution.validStepAt] at hs
  | stuck =>
      have hs := cycle.selected
      rw [hchoiceResult] at hs
      simp [ULogBootstrapExecution.validStepAt] at hs
  | running q z =>
      have hselected := cycle.selected
      rw [hchoiceResult] at hselected
      rcases validStepAt_live_outer (ULogBytecode.slotIndex slot) q z
          cycle.branch origin leftExtra rightExtra hselected hbranchLive with
        ⟨branchConfig, hbranch, hselected⟩
      rcases validZeroRun_live_outer origin leftExtra rightExtra
          cycle.cycleSuffix.valid hfinish with
        ⟨branchConfig', finishConfig, hbranch', hfinishConfig, hsuffix⟩
      have hchoiceConfig : choiceConfig =
          anchoredFramedULogConfig q origin leftExtra rightExtra z := by
        have hcanonical : framedLiveConfig origin leftExtra rightExtra
            cycle.choice = some
              (anchoredFramedULogConfig q origin leftExtra rightExtra z) := by
          rw [hchoiceResult]
          rfl
        exact Option.some.inj (hchoice.symm.trans hcanonical)
      have hbranchConfig : branchConfig = branchConfig' :=
        Option.some.inj (hbranch.symm.trans hbranch')
      subst choiceConfig
      subst branchConfig'
      exact ⟨startConfig, finishConfig, hstart, hfinishConfig,
        outerReaches_trans hprefix (outerReaches_trans hselected hsuffix)⟩

/-- Raw exact slot runs ending live lift compositionally; this is the direct
execution counterpart of the semantic reflection recursion. -/
theorem exactConcreteSlotRun_live_outer
    {slots : List Bool} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (run : ULogBootstrapExecution.ExactConcreteSlotRun start slots finish)
    (hfinish : ConcreteLive finish) :
    ∃ c d,
      framedLiveConfig origin leftExtra rightExtra start = some c ∧
      framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReaches c d := by
  induction run with
  | nil r =>
      rcases (framedLiveConfig_some_iff origin leftExtra rightExtra r).2
          hfinish with ⟨c, hc⟩
      exact ⟨c, c, hc, hc, outerReaches_refl c⟩
  | cons start next finish slot slots cycle tail ih =>
      rcases ih hfinish with
        ⟨nextConfig, finishConfig, hnextConfig, hfinishConfig, htail⟩
      have hnextLive : ConcreteLive next :=
        (framedLiveConfig_some_iff origin leftExtra rightExtra next).1
          ⟨nextConfig, hnextConfig⟩
      rcases exactConcreteCycle_live_outer origin leftExtra rightExtra cycle
          hnextLive with
        ⟨startConfig, nextConfig', hstartConfig, hnextConfig', hcycle⟩
      have hnextEq : nextConfig' = nextConfig :=
        Option.some.inj (hnextConfig'.symm.trans hnextConfig)
      subst nextConfig'
      exact ⟨startConfig, finishConfig, hstartConfig, hfinishConfig,
        outerReaches_trans hcycle htail⟩

theorem exactConcreteAcceptingSlotTrace_outer
    {slots : List Bool} {start : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (trace : ULogBootstrapExecution.ExactConcreteAcceptingSlotTrace start slots) :
    ∃ z startConfig,
      framedLiveConfig origin leftExtra rightExtra start = some startConfig ∧
      OuterReaches startConfig
        (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z) := by
  rcases trace with ⟨finish, run, haccept⟩
  cases hfinish : finish with
  | running q z => simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | rejected => simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | stuck => simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | accepted z =>
      subst finish
      rcases exactConcreteSlotRun_live_outer origin leftExtra rightExtra run
          (by trivial) with
        ⟨startConfig, finishConfig, hstartConfig, hfinishConfig, hrun⟩
      have hfinishConfig' : finishConfig =
          anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z :=
        Option.some.inj (hfinishConfig.symm.trans rfl)
      subst finishConfig
      exact ⟨z, startConfig, hstartConfig, hrun⟩

/-- A bounded semantic accepting word now yields a literal accepting path of
the full outer machine, starting at the scanner-derived slot-one input.  The
resource and decoded-clock premises are exactly those of the raw-reflection
equivalence; no canonical-image membership is introduced. -/
theorem semanticAcceptingWord_reaches_outerAccept
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (t : ℕ)
    (resources : ULogBootstrapExecution.FrameResourceInvariant
      (copiedSemanticFrame x rules input padding) t)
    (hstart : ULogSemantics.halted
      (copiedSemanticFrame x rules input padding).config = false)
    (hclock : ULogBootstrapExecution.decodeBinaryClock
      (List.replicate
          (copiedSemanticFrame x rules input padding).clockZeros
          (ULogAlphabet.ulogCore ULogAlphabet.clockZero) ++
        ULogAlphabet.ulogCore ULogAlphabet.clockOne ::
          (copiedSemanticFrame x rules input padding).runtime) = some (t + 1))
    (word : ULogBootstrapExecution.SemanticAcceptingWords t
      (copiedSemanticFrame x rules input padding).config) :
    ∃ origin leftExtra z,
      OuterReaches (PakSideScannerRow.sideEncodedStartConfig x)
        (anchoredFramedOuterAcceptConfig origin leftExtra
          (.markR :: PakSideScanner.sideCopierHashTail x) z) := by
  let frame := copiedSemanticFrame x rules input padding
  have hruntime : ULogBootstrapExecution.PassivePath frame.runtime := by
    intro cell hcell
    simp only [frame, copiedSemanticFrame, List.mem_singleton] at hcell
    subst cell
    constructor <;> native_decide
  let raw := ULogBootstrapExecution.semanticToBoundedExactConcreteAccepting
    t frame resources hruntime hstart hclock word
  rcases PakOuterULogBridge.sideStart_reaches_outerSemanticStart
      x rules input padding hword with ⟨origin, leftExtra, hprefix⟩
  rcases exactConcreteAcceptingSlotTrace_outer origin leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x) raw.2.2 with
    ⟨z, startConfig, hstartConfig, htrace⟩
  have hcanonical : framedLiveConfig origin leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x) frame.encode =
        some (anchoredFramedULogConfig ULogControl.State.cycleStart origin
          leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) := by
    rw [show frame.encode = .running ULogControl.State.cycleStart
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) by
      exact copiedSemanticFrame_encode x rules input padding]
    rfl
  have hstartEq : startConfig =
      anchoredFramedULogConfig ULogControl.State.cycleStart origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x)
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) :=
    Option.some.inj (hstartConfig.symm.trans hcanonical)
  subst startConfig
  exact ⟨origin, leftExtra, z, outerReaches_trans hprefix htrace⟩

theorem semanticAcceptingWord_outerStages
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (t : ℕ)
    (resources : ULogBootstrapExecution.FrameResourceInvariant
      (copiedSemanticFrame x rules input padding) t)
    (hstart : ULogSemantics.halted
      (copiedSemanticFrame x rules input padding).config = false)
    (hclock : ULogBootstrapExecution.decodeBinaryClock
      (List.replicate
          (copiedSemanticFrame x rules input padding).clockZeros
          (ULogAlphabet.ulogCore ULogAlphabet.clockZero) ++
        ULogAlphabet.ulogCore ULogAlphabet.clockOne ::
          (copiedSemanticFrame x rules input padding).runtime) = some (t + 1))
    (word : ULogBootstrapExecution.SemanticAcceptingWords t
      (copiedSemanticFrame x rules input padding).config) :
    Nonempty (SideOuterAcceptingStages x rules input padding) := by
  let frame := copiedSemanticFrame x rules input padding
  have hruntime : ULogBootstrapExecution.PassivePath frame.runtime := by
    intro cell hcell
    simp only [frame, copiedSemanticFrame, List.mem_singleton] at hcell
    subst cell
    constructor <;> native_decide
  let raw := ULogBootstrapExecution.semanticToBoundedExactConcreteAccepting
    t frame resources hruntime hstart hclock word
  let front := Classical.choice (PakParserOuterBridge.sideStartParserCopier_stages x)
  rcases PakOuterULogBridge.canonicalGroupReady_outer_eq_framedULogStart
      x front.groupZipper front.finish front.finish_ready with
    ⟨origin, leftExtra, hgroup⟩
  rcases PakOuterULogBridge.copiedULogStart_outer_reaches_semanticStart
      x rules input padding hword origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x) with
    ⟨bootstrapArrows, hbootstrap⟩
  have hbootstrap' : FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable bootstrapArrows front.finish =
        some (anchoredFramedULogConfig ULogControl.State.cycleStart origin
          leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) := by
    rw [hgroup]
    exact hbootstrap
  rcases exactConcreteAcceptingSlotTrace_outer origin leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x) raw.2.2 with
    ⟨z, startConfig, hstartConfig, hsimulation⟩
  have hcanonical : framedLiveConfig origin leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x) frame.encode =
        some (anchoredFramedULogConfig ULogControl.State.cycleStart origin
          leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)
          (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding)) := by
    rw [show frame.encode = .running ULogControl.State.cycleStart
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) by
      exact copiedSemanticFrame_encode x rules input padding]
    rfl
  have hstartEq : startConfig =
      anchoredFramedULogConfig ULogControl.State.cycleStart origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x)
        (PakOuterULogBridge.copiedSemanticStartZipper x rules input padding) :=
    Option.some.inj (hstartConfig.symm.trans hcanonical)
  subst startConfig
  rcases hsimulation with ⟨simulationArrows, hsimulation⟩
  exact ⟨
    { front := front
      origin := origin
      leftExtra := leftExtra
      group_eq := hgroup
      bootstrapArrows := bootstrapArrows
      bootstrap_run := hbootstrap'
      simulationArrows := simulationArrows
      acceptZipper := z
      simulation_run := hsimulation }⟩

end PakFixedPolyomino.PakOuterULogTraceBridge
