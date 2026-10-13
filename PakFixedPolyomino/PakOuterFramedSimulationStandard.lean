import PakFixedPolyomino.PakOuterULogReflection
import PakFixedPolyomino.PakOuterULogKernelAcceptFacts

/-! Original guarded simulation readback with ordinary kernel accept/reject
and movement facts. This existence-only projection preserves ALL histories;
its full labelled word inverse/count correspondence remains separate. -/
namespace PakFixedPolyomino.PakOuterFramedSimulationStandard
open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge PakOuterULogBridge PakOuterULogReflection

abbrev OuterTape := MStarULogAssembly.Tape
abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig
abbrev OuterArrow := MStarULogAssembly.Arrow

private theorem actionOf_eq_of_rule_eq
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (P : FiniteOneTapeProgram.Program S T)
    (a : FiniteOneTapeProgram.Arrow P)
    (act : FiniteOneTapeProgram.Action S T)
    (h : P.rule a.1.1.1 a.1.1.2 a.1.2 = some act) :
    FiniteOneTapeProgram.actionOf P a = act := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.2 hnone).elim

private theorem ulog_rule_eq_actionOf (a : MStarULogAssembly.ULogArrow) :
    ULogProgram.program.rule a.1.1.1 a.1.1.2 a.1.2 =
      some (FiniteOneTapeProgram.actionOf ULogProgram.program a) := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact hfound
  · rename_i hnone
    exact (a.2 hnone).elim

private theorem reflected_actionOf_eq
    {q : ULogControl.State} {origin : Int}
    {leftExtra rightExtra : List OuterTape}
    {z : MStarParserExecution.Zipper ULogProgram.Tape}
    {d : OuterConfig} {a : OuterArrow}
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d)
    (R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
      z d a hstep)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus R.uarrow.1.2 = some act) :
    FiniteOneTapeProgram.actionOf ULogProgram.program R.uarrow = act := by
  have hval := congrArg Subtype.val R.outer_arrow_eq
  have hphysical := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) d a hstep
  have haSource : a.1.1.1 = (.sim q : MStarULogAssembly.State) :=
    hphysical.1.symm.trans rfl
  have hheadTape :
      (anchoredFramedULogConfig q origin leftExtra rightExtra z).tape
          (anchoredFramedULogConfig q origin leftExtra rightExtra z).head =
        (.core z.focus : OuterTape) := by
    change anchoredZipperTape origin
      (frameCoreZipper leftExtra rightExtra z)
        (origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length) =
      .core z.focus
    rw [anchoredZipperTape_at_head]
    rfl
  have haRead : a.1.1.2 = (.core z.focus : OuterTape) :=
    hphysical.2.symm.trans hheadTape
  have hsource : R.uarrow.1.1.1 = q := by
    have hs := congrArg (fun v => v.1.1) hval
    have hs' : (.sim R.uarrow.1.1.1 : MStarULogAssembly.State) = .sim q :=
      hs.trans haSource
    exact MStarOuterProgram.State.sim.inj hs'
  have hread : R.uarrow.1.1.2 = z.focus := by
    have hr := congrArg (fun v => v.1.2) hval
    have hr' : (.core R.uarrow.1.1.2 : OuterTape) = .core z.focus :=
      hr.trans haRead
    exact MStarOuterProgram.Tape.core.inj hr'
  apply actionOf_eq_of_rule_eq ULogProgram.program R.uarrow act
  simpa [hsource, hread] using hrule

theorem outerStep_from_framedSim_accepting_successor
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d)
    (hnext : ULogBootstrapExecution.oneStepAt
      (outerStep_from_framedSim_reflection q origin leftExtra rightExtra
        z d a hstep).uarrow.1.2 (.running q z) = .accepted z') :
    d = anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z' := by
  let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
    z d a hstep
  rcases (ulogOneStepAt_eq_accepted_iff R.uarrow.1.2 q z z').mp hnext with
    ⟨act, hrule, happly, htarget⟩
  have haction := reflected_actionOf_eq (R := R) hstep act hrule
  rw [R.successor_eq, haction]
  let mapped := MStarOuterProgram.mapUAction MStarULogAssembly.data act
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z mapped = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' act happly
  have htarget' : mapped.target = (.accept : MStarULogAssembly.State) := by
    simp only [mapped, MStarOuterProgram.mapUAction, htarget]
    exact PakOuterULogKernelAcceptFacts.simulated_accept_maps_to_outer_accept
  have hhead : origin + Z'.leftRev.length =
      moveHead mapped.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' mapped happly'
  have htape : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) mapped.write :=
    anchoredZipperTape_applyAction origin Z Z' mapped happly'
  simp only [PakParserOuterBridge.afterAction,
    anchoredFramedOuterAcceptConfig, anchoredFramedULogConfig, writtenTape]
  rw [htarget']
  congr 1
  · exact hhead.symm
  · exact htape.symm

theorem outerHistory_from_framedSim_to_concreteMicroPath
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (hstart : start = anchoredFramedULogConfig q origin leftExtra rightExtra z)
    (haccept : finish.state = .accept) :
    ∃ slots z',
      ULogBootstrapExecution.ConcreteMicroPath (.running q z) slots (.accepted z') ∧
      slots.length ≤ arrows.length := by
  induction H generalizing q z with
  | nil c =>
      rw [hstart] at haccept
      simp [anchoredFramedULogConfig] at haccept
  | cons c next finish a arrows hstep tail ih =>
      subst c
      let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
        z next a hstep
      have hvalid := R.valid
      cases hnext : ULogBootstrapExecution.oneStepAt R.uarrow.1.2
          (.running q z) with
      | running q' z' =>
          have hnextPhysical : next =
              anchoredFramedULogConfig q' origin leftExtra rightExtra z' :=
            outerStep_from_framedSim_running_successor q q' origin leftExtra
              rightExtra z z' next a hstep hnext
          rcases ih q' z' hnextPhysical haccept with
            ⟨slots, finishZ, hpath, hlength⟩
          refine ⟨R.uarrow.1.2 :: slots, finishZ, ?_, by simp; omega⟩
          apply ULogBootstrapExecution.ConcreteMicroPath.cons
            (.running q z) (.running q' z') (.accepted finishZ)
            R.uarrow.1.2 slots
          · simpa [hnext] using hvalid
          · exact hpath
      | accepted z' =>
          refine ⟨[R.uarrow.1.2], z', ?_, by simp⟩
          apply ULogBootstrapExecution.ConcreteMicroPath.cons
            (.running q z) (.accepted z') (.accepted z') R.uarrow.1.2 []
          · simpa [hnext] using hvalid
          · exact .nil (.accepted z')
      | rejected =>
          rcases (ulogOneStepAt_eq_rejected_iff R.uarrow.1.2 q z).mp hnext with
            ⟨act, z', hrule, happly, htarget⟩
          have haction := reflected_actionOf_eq (R := R) hstep act hrule
          have hnextState := outerStep_from_framedSim_target q origin leftExtra
            rightExtra z next a hstep
          have hrejectState : next.state = (.reject : MStarULogAssembly.State) := by
            calc
              next.state = MStarOuterProgram.mapUState MStarULogAssembly.data
                  act.target := by simpa [R, haction] using hnextState
              _ = MStarOuterProgram.mapUState MStarULogAssembly.data
                  ULogControl.qReject := congrArg _ htarget
              _ = .reject := PakOuterULogKernelAcceptFacts.simulated_reject_maps_to_outer_reject
          exact (reject_history_not_accept tail hrejectState haccept).elim
      | stuck =>
          let act := FiniteOneTapeProgram.actionOf ULogProgram.program R.uarrow
          have hrule : ULogProgram.program.rule q z.focus R.uarrow.1.2 =
              some act := by
            have hval := congrArg Subtype.val R.outer_arrow_eq
            have hphysical := FiniteOneTapeSemantics.step_some_forces_source
              MStarULogAssembly.program MStarOuterProgram.movable
                (anchoredFramedULogConfig q origin leftExtra rightExtra z)
                next a hstep
            have hsource : R.uarrow.1.1.1 = q := by
              have hs := congrArg (fun v => v.1.1) hval
              have ha : a.1.1.1 = (.sim q : MStarULogAssembly.State) :=
                hphysical.1.symm.trans rfl
              exact MStarOuterProgram.State.sim.inj (hs.trans ha)
            have hread : R.uarrow.1.1.2 = z.focus := by
              have hr := congrArg (fun v => v.1.2) hval
              have hheadTape :
                  (anchoredFramedULogConfig q origin leftExtra rightExtra z).tape
                      (anchoredFramedULogConfig q origin leftExtra rightExtra z).head =
                    (.core z.focus : OuterTape) := by
                change anchoredZipperTape origin
                  (frameCoreZipper leftExtra rightExtra z)
                    (origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length) =
                  .core z.focus
                rw [anchoredZipperTape_at_head]
                rfl
              have ha : a.1.1.2 = (.core z.focus : OuterTape) :=
                hphysical.2.symm.trans hheadTape
              exact MStarOuterProgram.Tape.core.inj (hr.trans ha)
            simpa [hsource, hread, act] using ulog_rule_eq_actionOf R.uarrow
          have happlyNone : MStarParserExecution.applyAction z act = none :=
            (ulogOneStepAt_eq_stuck_iff R.uarrow.1.2 q z act hrule).mp hnext
          have hnoncore : ∀ y : ULogProgram.Tape,
              next.tape next.head ≠ .core y := by
            rcases finiteApply_or_successor_noncore q origin leftExtra rightExtra
                guards z next a hstep with happlySome | hnoncore
            · rcases happlySome with ⟨w, hw⟩
              rw [show FiniteOneTapeProgram.actionOf ULogProgram.program
                  R.uarrow = act from rfl, happlyNone] at hw
              cases hw
            · exact hnoncore
          by_cases hacceptTarget : act.target = ULogControl.qAccept
          · have hmove := PakOuterULogKernelAcceptFacts.ulog_rule_target_accept_move_stay q z.focus
                R.uarrow.1.2 act hrule hacceptTarget
            rcases z with ⟨left, focus, right⟩
            simp [MStarParserExecution.applyAction, hmove] at happlyNone
          · by_cases hrejectTarget : act.target = ULogControl.qReject
            · have hnextState := outerStep_from_framedSim_target q origin
                  leftExtra rightExtra z next a hstep
              have haction := reflected_actionOf_eq (R := R) hstep act hrule
              have hrejectState :
                  next.state = (.reject : MStarULogAssembly.State) := by
                calc
                  next.state = MStarOuterProgram.mapUState MStarULogAssembly.data
                      act.target := by simpa [R, haction] using hnextState
                  _ = MStarOuterProgram.mapUState MStarULogAssembly.data
                      ULogControl.qReject := congrArg _ hrejectTarget
                  _ = .reject :=
                    PakOuterULogKernelAcceptFacts.simulated_reject_maps_to_outer_reject
              exact (reject_history_not_accept tail hrejectState haccept).elim
            · have hnextState := outerStep_from_framedSim_target q origin
                  leftExtra rightExtra z next a hstep
              have haction := reflected_actionOf_eq (R := R) hstep act hrule
              have hsimState : next.state =
                  (.sim act.target : MStarULogAssembly.State) := by
                calc
                  next.state = MStarOuterProgram.mapUState MStarULogAssembly.data
                      act.target := by simpa [R, haction] using hnextState
                  _ = .sim act.target :=
                    mapUState_eq_sim hacceptTarget hrejectTarget
              exact (sim_noncore_history_not_accept tail act.target hsimState
                hnoncore haccept).elim

def framed_simulation_readback_spec : Prop :=
  (∀ (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : step MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d),
    ULogBootstrapExecution.oneStepAt
      (outerStep_from_framedSim_reflection q origin leftExtra rightExtra z d a hstep).uarrow.1.2
      (.running q z) = .accepted z' →
    d = anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z') ∧
  (∀ (start finish : OuterConfig) (arrows : List OuterArrow),
    PakOuterULogTraceBridge.OuterArrowHistory start arrows finish →
    ∀ (q : ULogControl.State) (origin : Int) (leftExtra rightExtra : List OuterTape),
    FramingGuards leftExtra rightExtra →
    ∀ z : MStarParserExecution.Zipper ULogProgram.Tape,
    start = anchoredFramedULogConfig q origin leftExtra rightExtra z →
    finish.state = .accept →
    ∃ slots z', ULogBootstrapExecution.ConcreteMicroPath (.running q z) slots (.accepted z') ∧
      slots.length ≤ arrows.length)

theorem framed_simulation_readback_spec_holds : framed_simulation_readback_spec :=
  ⟨outerStep_from_framedSim_accepting_successor,
    fun _start _finish _arrows H => outerHistory_from_framedSim_to_concreteMicroPath H⟩

end PakFixedPolyomino.PakOuterFramedSimulationStandard
