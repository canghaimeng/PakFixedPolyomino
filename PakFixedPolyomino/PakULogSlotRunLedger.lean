import PakFixedPolyomino.PakULogExplicitFuel

/-!
# Exact ledger relation for labelled raw `U_log` slot runs

`ExactConcreteSlotRun` was deliberately declared in `Prop`. Lean therefore
cannot eliminate a proof of it into a numerical `def`: its first-hit cycle
objects carry Type-valued data, while proof irrelevance erases that data from
ordinary computation. The correct non-erasing interface is the inductive
proposition `ExactSlotRunFuel` below. It records, constructor by constructor,
the exact sum of the zero-prefix, selected arrow, and zero-suffix fuels.
-/

namespace PakFixedPolyomino.PakULogSlotRunLedger

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge
open PakOuterULogBridge
  (anchoredFramedULogConfig anchoredFramedOuterAcceptConfig)
open PakOuterFrontQuantitative
  (OuterReachesAtMost outerReachesAtMost_refl outerReachesAtMost_trans)
open PakULogExplicitFuel (exactConcreteCycle_live_outerAtMost)
open ULogBootstrapExecution

abbrev LedgerOuterTape := PakParserOuterBridge.OuterTape
abbrev LedgerOuterConfig := PakOuterFrontQuantitative.OuterConfig

/-- The exact recursively accumulated literal outer-arrow fuel of a concrete
labelled slot run. A cycle contributes precisely
`choicePrefix.steps + 1 + cycleSuffix.steps`; no semantic-time premise is
inserted here. -/
inductive ExactSlotRunFuel :
    ∀ {start finish : ULogBootstrapExecution.Result} {slots : List Bool},
      ULogBootstrapExecution.ExactConcreteSlotRun start slots finish → ℕ → Prop
  | nil (r : ULogBootstrapExecution.Result) :
      ExactSlotRunFuel (ULogBootstrapExecution.ExactConcreteSlotRun.nil r) 0
  | cons (start next finish : ULogBootstrapExecution.Result)
      (slot : Bool) (slots : List Bool)
      (cycle : ULogBootstrapExecution.ExactConcreteCycle slot start next)
      (tail : ULogBootstrapExecution.ExactConcreteSlotRun next slots finish)
      (fuel : ℕ) :
      ExactSlotRunFuel tail fuel →
      ExactSlotRunFuel
        (ULogBootstrapExecution.ExactConcreteSlotRun.cons
          start next finish slot slots cycle tail)
        (cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps + fuel)

/-- Every existing exact slot-run certificate carries a recursively exact
fuel witness. This is a proposition-level sigma ledger because the source run
itself lives in `Prop`. -/
theorem exactConcreteSlotRun_hasExactFuel
    {start finish : ULogBootstrapExecution.Result} {slots : List Bool}
    (run : ULogBootstrapExecution.ExactConcreteSlotRun start slots finish) :
    ∃ fuel, ExactSlotRunFuel run fuel := by
  induction run with
  | nil r => exact ⟨0, .nil r⟩
  | cons start next finish slot slots cycle tail ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps + fuel,
        .cons start next finish slot slots cycle tail fuel hfuel⟩

/-- The exact ledger controls a whole framed literal outer run. -/
theorem exactConcreteSlotRun_live_outerAtMost_exactFuel
    {slots : List Bool} {start finish : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List LedgerOuterTape)
    (run : ULogBootstrapExecution.ExactConcreteSlotRun start slots finish)
    {fuel : ℕ} (hledger : ExactSlotRunFuel run fuel)
    (hfinish : PakOuterULogTraceBridge.ConcreteLive finish) :
    ∃ c d : LedgerOuterConfig,
      PakOuterULogTraceBridge.framedLiveConfig origin leftExtra rightExtra start = some c ∧
      PakOuterULogTraceBridge.framedLiveConfig origin leftExtra rightExtra finish = some d ∧
      OuterReachesAtMost fuel c d := by
  induction hledger with
  | nil r =>
      rcases (PakOuterULogTraceBridge.framedLiveConfig_some_iff
          origin leftExtra rightExtra r).2 hfinish with ⟨c, hc⟩
      exact ⟨c, c, hc, hc, outerReachesAtMost_refl c⟩
  | cons start next finish slot slots cycle tail fuel htail ih =>
      rcases ih hfinish with
        ⟨nextConfig, finishConfig, hnextConfig, hfinishConfig, htailOuter⟩
      have hnextLive : PakOuterULogTraceBridge.ConcreteLive next :=
        (PakOuterULogTraceBridge.framedLiveConfig_some_iff
          origin leftExtra rightExtra next).1 ⟨nextConfig, hnextConfig⟩
      rcases exactConcreteCycle_live_outerAtMost origin leftExtra rightExtra
          cycle hnextLive with
        ⟨startConfig, nextConfig', hstartConfig, hnextConfig', hcycle⟩
      have hnextEq : nextConfig' = nextConfig :=
        Option.some.inj (hnextConfig'.symm.trans hnextConfig)
      subst nextConfig'
      exact ⟨startConfig, finishConfig, hstartConfig, hfinishConfig,
        by
          simpa [Nat.add_assoc] using
            outerReachesAtMost_trans hcycle htailOuter⟩

/-- An accepting trace admits a literal accepting outer history together
with a *specific* exact cycle-by-cycle fuel ledger. This deliberately does
not weaken the ledger to an unstructured `∃ fuel`. -/
theorem exactConcreteAcceptingSlotTrace_outerAtMost_exactFuel
    {slots : List Bool} {start : ULogBootstrapExecution.Result}
    (origin : Int) (leftExtra rightExtra : List LedgerOuterTape)
    (trace : ULogBootstrapExecution.ExactConcreteAcceptingSlotTrace start slots) :
    ∃ (finish : ULogBootstrapExecution.Result)
      (run : ULogBootstrapExecution.ExactConcreteSlotRun start slots finish)
      (fuel : ℕ) (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (startConfig : LedgerOuterConfig),
      ULogBootstrapExecution.concreteAccepting finish = true ∧
      ExactSlotRunFuel run fuel ∧
      PakOuterULogTraceBridge.framedLiveConfig origin leftExtra rightExtra start =
        some startConfig ∧
      OuterReachesAtMost fuel startConfig
        (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z) := by
  rcases trace with ⟨finish, run, haccept⟩
  rcases exactConcreteSlotRun_hasExactFuel run with ⟨fuel, hledger⟩
  cases hfinish : finish with
  | running q z =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | rejected =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | stuck =>
      simp [hfinish, ULogBootstrapExecution.concreteAccepting] at haccept
  | accepted z =>
      subst finish
      rcases exactConcreteSlotRun_live_outerAtMost_exactFuel origin
          leftExtra rightExtra run hledger (by trivial) with
        ⟨startConfig, finishConfig, hstartConfig, hfinishConfig, hrun⟩
      have hfinishConfig' : finishConfig =
          anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z :=
        Option.some.inj (hfinishConfig.symm.trans rfl)
      subst finishConfig
      exact ⟨.accepted z, run, fuel, z, startConfig, haccept, hledger,
        hstartConfig, hrun⟩

end PakFixedPolyomino.PakULogSlotRunLedger
