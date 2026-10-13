import PakFixedPolyomino.PakOuterFramedSimulationStandard
import PakFixedPolyomino.MStarOccupiedSlotWordInjectivity
import PakFixedPolyomino.ULogConcreteMicroTimeCounts
import PakFixedPolyomino.ULogConcreteMicroCutoffMonotonicity

/-! EVERY original framed FirstHitWordsAtMost is equivalent, both inverses
and exact chronological length, to EVERY original RawAcceptingMicroWordsAtMost
from running q z. Outer-to-raw is labels.map occupied Fin 2 slots. -/

namespace PakFixedPolyomino.PakAllFramedFirstHitMicroBijection
open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge PakOuterULogBridge PakOuterULogReflection
open ULogBootstrapExecution MStarFirstHitPadding
open MStarOccupiedSlotWordInjectivity
open MStarFixedWidthFirstHitEquiv
open ULogConcreteMicroTimeCounts

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

def uarrowOf {q : ULogControl.State} {x : ULogProgram.Tape} {slot : Fin 2}
    {act : Action ULogControl.State ULogProgram.Tape}
    (hrule : ULogProgram.program.rule q x slot = some act) :
    MStarULogAssembly.ULogArrow :=
  ⟨((q, x), slot), by simp [hrule]⟩

private theorem step_eq_afterAction_of_match
    (c : OuterConfig) (a : OuterArrow)
    (hstate : c.state = a.1.1.1)
    (hread : c.tape c.head = a.1.1.2)
    (hmovable : MStarOuterProgram.movable
      (writtenTape c (actionOf MStarULogAssembly.program a).write
        (moveHead (actionOf MStarULogAssembly.program a).move c.head)) = true) :
    step MStarULogAssembly.program MStarOuterProgram.movable c a =
      some (afterAction c (actionOf MStarULogAssembly.program a)) := by
  unfold step
  dsimp only
  have hneq :
      ¬(c.state ≠ (transition MStarULogAssembly.program a).sourceState ∨
        c.tape c.head ≠ (transition MStarULogAssembly.program a).read) := by
    simp [transition, hstate, hread]
  have hmov : MStarOuterProgram.movable
      (writtenTape c (transition MStarULogAssembly.program a).write
        (moveHead (transition MStarULogAssembly.program a).move c.head)) = true := by
    simpa [transition] using hmovable
  rw [if_neg hneq, if_pos hmov]
  simp [afterAction, transition]

theorem reverse_step_core
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) (slot : Fin 2)
    (act : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some act)
    (happly : MStarParserExecution.applyAction z act = some z') :
    let mapped := MStarOuterProgram.mapUAction MStarULogAssembly.data act
    let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
    step MStarULogAssembly.program MStarOuterProgram.movable c
        (MStarULogAssembly.simArrow (uarrowOf hrule)) =
      some (afterAction c mapped) ∧
    afterAction c mapped =
      { state := mapped.target
        head := origin + (frameCoreZipper leftExtra rightExtra z').leftRev.length
        tape := anchoredZipperTape origin (frameCoreZipper leftExtra rightExtra z') } := by
  intro mapped c
  let ua := uarrowOf hrule
  let a := MStarULogAssembly.simArrow ua
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  have haction : actionOf MStarULogAssembly.program a = mapped := by
    have hua : actionOf ULogProgram.program ua = act :=
      actionOf_eq_of_rule_eq ULogProgram.program ua act (by
        simpa [ua, uarrowOf] using hrule)
    rw [MStarULogAssembly.actionOf_simArrow, hua]
  have happly' : MStarParserExecution.applyAction Z mapped = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' act happly
  have hhead := anchoredZipperHead_applyAction origin Z Z' mapped happly'
  have htape := anchoredZipperTape_applyAction origin Z Z' mapped happly'
  have hafter : afterAction c mapped =
      { state := mapped.target
        head := origin + Z'.leftRev.length
        tape := anchoredZipperTape origin Z' } := by
    simp only [c, afterAction, anchoredFramedULogConfig, writtenTape]
    congr 1
    · exact hhead.symm
    · exact htape.symm
  have hstate : c.state = a.1.1.1 := by
    simp [c, a, ua, uarrowOf, anchoredFramedULogConfig, MStarULogAssembly.simArrow]
  have hread : c.tape c.head = a.1.1.2 := by
    have hc : c.tape c.head = (.core z.focus : OuterTape) := by
      change anchoredZipperTape origin Z (origin + Z.leftRev.length) = .core z.focus
      rw [anchoredZipperTape_at_head]; rfl
    exact hc.trans (show a.1.1.2 = .core z.focus from rfl).symm
  have hmovable : MStarOuterProgram.movable
      (writtenTape c mapped.write (moveHead mapped.move c.head)) = true := by
    have htape' : writtenTape c mapped.write = anchoredZipperTape origin Z' := by
      simpa only [c, anchoredFramedULogConfig, writtenTape] using htape.symm
    change MStarOuterProgram.movable
      (writtenTape c mapped.write
        (moveHead mapped.move (origin + Z.leftRev.length))) = true
    rw [htape', ← hhead, anchoredZipperTape_at_head]; rfl
  have hstep := step_eq_afterAction_of_match c a hstate hread
    (by simpa [haction] using hmovable)
  exact ⟨by simpa [haction] using hstep, hafter⟩

theorem reverse_running_step
    (q q' : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) (slot : Fin 2)
    (act : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some act)
    (happly : MStarParserExecution.applyAction z act = some z')
    (htarget : act.target = q')
    (haccept : q' ≠ ULogControl.qAccept)
    (hreject : q' ≠ ULogControl.qReject) :
    step MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (MStarULogAssembly.simArrow (uarrowOf hrule)) =
      some (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  have hcore := reverse_step_core q origin leftExtra rightExtra z z' slot act
    hrule happly
  have htarget' :
      (MStarOuterProgram.mapUAction MStarULogAssembly.data act).target =
        (.sim q' : MStarULogAssembly.State) := by
    simp [MStarOuterProgram.mapUAction, htarget, mapUState_eq_sim haccept hreject]
  apply Eq.trans hcore.1
  rw [hcore.2, htarget']
  rfl

theorem reverse_accepting_step
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) (slot : Fin 2)
    (act : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some act)
    (happly : MStarParserExecution.applyAction z act = some z')
    (htarget : act.target = ULogControl.qAccept) :
    step MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (MStarULogAssembly.simArrow (uarrowOf hrule)) =
      some (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z') := by
  have hcore := reverse_step_core q origin leftExtra rightExtra z z' slot act
    hrule happly
  have htarget' :
      (MStarOuterProgram.mapUAction MStarULogAssembly.data act).target =
        (.accept : MStarULogAssembly.State) := by
    simp [MStarOuterProgram.mapUAction, htarget,
      PakOuterULogKernelAcceptFacts.simulated_accept_maps_to_outer_accept]
  apply Eq.trans hcore.1
  rw [hcore.2, htarget']
  rfl

theorem first_hit_of_cons_tail
    (c next d : OuterConfig) (a : OuterArrow) (rest : List OuterArrow)
    (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some next)
    (_hn : next.state ≠ .accept)
    (h : FirstHit c (a :: rest) d) : FirstHit next rest d := by
  refine ⟨by simpa [run_cons, hs] using h.1, h.2.1, ?_⟩
  intro k hk mid hm
  exact h.2.2 (k + 1) (by simpa using Nat.succ_lt_succ hk) mid
    (by simpa [List.take_succ_cons, run_cons, hs] using hm)

theorem first_hit_accepting_rest_nil
    (c next d : OuterConfig) (a : OuterArrow) (rest : List OuterArrow)
    (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some next)
    (hn : next.state = .accept)
    (h : FirstHit c (a :: rest) d) : rest = [] ∧ d = next := by
  have hempty : rest = [] := by
    by_contra hne
    have hk : 1 < (a :: rest).length := by
      cases rest with
      | nil => exact (hne rfl).elim
      | cons _ _ => simp
    exact h.2.2 1 hk next (by simp [run_cons, hs]) hn
  subst rest
  exact ⟨rfl, (Option.some.inj (by simpa [run_cons, hs] using h.1)).symm⟩

theorem concreteMicroPath_of_accepted
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (slots : List (Fin 2)) (finish : Result)
    (H : ConcreteMicroPath (.accepted z) slots finish) :
    slots = [] ∧ finish = .accepted z := by
  cases H with
  | nil r => exact ⟨rfl, rfl⟩
  | cons start next finish slot slots hvalid htail =>
      simp [validStepAt] at hvalid

theorem concreteMicroPath_of_rejected
    (slots : List (Fin 2)) (finish : Result)
    (H : ConcreteMicroPath .rejected slots finish) :
    slots = [] ∧ finish = .rejected := by
  cases H with
  | nil r => exact ⟨rfl, rfl⟩
  | cons start next finish slot slots hvalid htail =>
      simp [validStepAt] at hvalid

theorem concreteMicroPath_of_stuck
    (slots : List (Fin 2)) (finish : Result)
    (H : ConcreteMicroPath .stuck slots finish) :
    slots = [] ∧ finish = .stuck := by
  cases H with
  | nil r => exact ⟨rfl, rfl⟩
  | cons start next finish slot slots hvalid htail =>
      simp [validStepAt] at hvalid

theorem first_hit_nil_of_accept (c : OuterConfig) (hc : c.state = .accept) :
    FirstHit c [] c :=
  ⟨rfl, hc, by intro k hk; simp at hk⟩

private theorem reflected_actionOf_eq
    {q : ULogControl.State} {origin : Int}
    {leftExtra rightExtra : List OuterTape}
    {z : MStarParserExecution.Zipper ULogProgram.Tape}
    {d : OuterConfig} {a : OuterArrow}
    (hstep : step MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d)
    (R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
      z d a hstep)
    (act : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus R.uarrow.1.2 = some act) :
    actionOf ULogProgram.program R.uarrow = act := by
  have hval := congrArg Subtype.val R.outer_arrow_eq
  have hphysical := step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) d a hstep
  have haSource : a.1.1.1 = (.sim q : MStarULogAssembly.State) :=
    hphysical.1.symm.trans rfl
  have hheadTape :
      (anchoredFramedULogConfig q origin leftExtra rightExtra z).tape
          (anchoredFramedULogConfig q origin leftExtra rightExtra z).head =
        (.core z.focus : OuterTape) := by
    change anchoredZipperTape origin (frameCoreZipper leftExtra rightExtra z)
        (origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length) =
      .core z.focus
    rw [anchoredZipperTape_at_head]; rfl
  have haRead : a.1.1.2 = (.core z.focus : OuterTape) :=
    hphysical.2.symm.trans hheadTape
  have hsource : R.uarrow.1.1.1 = q :=
    MStarOuterProgram.State.sim.inj
      ((congrArg (fun v => v.1.1) hval).trans haSource)
  have hread : R.uarrow.1.1.2 = z.focus :=
    MStarOuterProgram.Tape.core.inj
      ((congrArg (fun v => v.1.2) hval).trans haRead)
  apply actionOf_eq_of_rule_eq ULogProgram.program R.uarrow act
  simpa [hsource, hread] using hrule

theorem first_hit_to_micro_path
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (hstart : start = anchoredFramedULogConfig q origin leftExtra rightExtra z)
    (hhit : FirstHit start arrows finish) :
    ∃ z', ConcreteMicroPath (.running q z)
      (arrows.map (fun a => a.val.2)) (.accepted z') := by
  induction H generalizing q z with
  | nil c =>
      have hc : c.state ≠ .accept := by
        rw [hstart]; simp [anchoredFramedULogConfig]
      exact ((first_hit_nonempty c c [] hc hhit) rfl).elim
  | cons c next finish a arrows hstep tail ih =>
      subst c
      let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
        z next a hstep
      have hvalid := R.valid
      have hslot : R.uarrow.1.2 = a.1.2 :=
        congrArg (fun arrow : OuterArrow => arrow.1.2) R.outer_arrow_eq
      cases hnext : oneStepAt R.uarrow.1.2 (.running q z) with
      | running q' z' =>
          have hnextPhysical : next =
              anchoredFramedULogConfig q' origin leftExtra rightExtra z' :=
            outerStep_from_framedSim_running_successor q q' origin leftExtra
              rightExtra z z' next a hstep hnext
          have hnacc : next.state ≠ .accept := by
            rw [hnextPhysical]; simp [anchoredFramedULogConfig]
          rcases ih q' z' hnextPhysical
            (first_hit_of_cons_tail _ next finish a arrows hstep hnacc hhit) with
            ⟨finishZ, hpath⟩
          refine ⟨finishZ, ?_⟩
          rw [List.map_cons]
          have hnext' : oneStepAt a.1.2 (.running q z) = .running q' z' := by
            simpa [hslot] using hnext
          exact ConcreteMicroPath.cons (.running q z) (.running q' z')
            (.accepted finishZ) a.1.2 (arrows.map (fun b => b.val.2))
            (by simpa [hslot, hnext'] using hvalid) hpath
      | accepted z' =>
          have hnextPhysical : next =
              anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z' :=
            PakOuterFramedSimulationStandard.outerStep_from_framedSim_accepting_successor
              q origin leftExtra rightExtra z z' next a hstep hnext
          have hnacc : next.state = .accept := by
            rw [hnextPhysical]; simp [anchoredFramedOuterAcceptConfig]
          obtain ⟨hrest, _⟩ := first_hit_accepting_rest_nil _ next finish a arrows
            hstep hnacc hhit
          subst arrows
          refine ⟨z', ?_⟩
          have hnext' : oneStepAt a.1.2 (.running q z) = .accepted z' := by
            simpa [hslot] using hnext
          exact ConcreteMicroPath.cons (.running q z) (.accepted z')
            (.accepted z') a.1.2 [] (by simpa [hslot, hnext'] using hvalid)
            (.nil (.accepted z'))
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
              _ = .reject :=
                PakOuterULogKernelAcceptFacts.simulated_reject_maps_to_outer_reject
          exact (reject_history_not_accept tail hrejectState hhit.2.1).elim
      | stuck =>
          cases hrule : ULogProgram.program.rule q z.focus R.uarrow.1.2 with
          | none => simp [validStepAt, hrule] at hvalid
          | some act =>
              have happlyNone : MStarParserExecution.applyAction z act = none :=
                (ulogOneStepAt_eq_stuck_iff R.uarrow.1.2 q z act hrule).mp hnext
              have hnoncore : ∀ y : ULogProgram.Tape,
                  next.tape next.head ≠ .core y := by
                rcases finiteApply_or_successor_noncore q origin leftExtra
                    rightExtra guards z next a hstep with happlySome | hnoncore
                · rcases happlySome with ⟨w, hw⟩
                  have hact := reflected_actionOf_eq (R := R) hstep act hrule
                  rw [hact, happlyNone] at hw; cases hw
                · exact hnoncore
              by_cases hacceptTarget : act.target = ULogControl.qAccept
              · have hmove :=
                  PakOuterULogKernelAcceptFacts.ulog_rule_target_accept_move_stay
                    q z.focus R.uarrow.1.2 act hrule hacceptTarget
                rcases z with ⟨left, focus, right⟩
                simp [MStarParserExecution.applyAction, hmove] at happlyNone
              · by_cases hrejectTarget : act.target = ULogControl.qReject
                · have hnextState := outerStep_from_framedSim_target q origin
                      leftExtra rightExtra z next a hstep
                  have haction := reflected_actionOf_eq (R := R) hstep act hrule
                  have hrejectState :
                      next.state = (.reject : MStarULogAssembly.State) := by
                    calc
                      next.state = MStarOuterProgram.mapUState
                          MStarULogAssembly.data act.target := by
                        simpa [R, haction] using hnextState
                      _ = MStarOuterProgram.mapUState MStarULogAssembly.data
                          ULogControl.qReject := congrArg _ hrejectTarget
                      _ = .reject :=
                        PakOuterULogKernelAcceptFacts.simulated_reject_maps_to_outer_reject
                  exact (reject_history_not_accept tail hrejectState hhit.2.1).elim
                · have hnextState := outerStep_from_framedSim_target q origin
                      leftExtra rightExtra z next a hstep
                  have haction := reflected_actionOf_eq (R := R) hstep act hrule
                  have hsimState : next.state =
                      (.sim act.target : MStarULogAssembly.State) := by
                    calc
                      next.state = MStarOuterProgram.mapUState
                          MStarULogAssembly.data act.target := by
                        simpa [R, haction] using hnextState
                      _ = .sim act.target :=
                        mapUState_eq_sim hacceptTarget hrejectTarget
                  exact (sim_noncore_history_not_accept tail act.target hsimState
                    hnoncore hhit.2.1).elim

theorem micro_path_to_first_hit
    {start : Result} {slots : List (Fin 2)} {finish : Result}
    (H : ConcreteMicroPath start slots finish)
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z tape : MStarParserExecution.Zipper ULogProgram.Tape)
    (hstart : start = .running q z)
    (hfinish : finish = .accepted tape) :
    ∃ arrows : List OuterArrow,
      arrows.map (fun a => a.val.2) = slots ∧
      FirstHit (anchoredFramedULogConfig q origin leftExtra rightExtra z) arrows
        (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra tape) := by
  induction H generalizing q z tape with
  | nil r =>
      rw [hstart] at hfinish; cases hfinish
  | cons start next finish slot slots hvalid htail ih =>
      subst hstart
      have hnextEq : next = oneStepAt slot (.running q z) :=
        (validStepAt_some_eq_oneStepAt hvalid).symm
      cases hrule : ULogProgram.program.rule q z.focus slot with
      | none => simp [validStepAt, hrule] at hvalid
      | some act =>
          cases happly : MStarParserExecution.applyAction z act with
          | none =>
              have hstuck : oneStepAt slot (.running q z) = .stuck := by
                simp [oneStepAt, hrule, happly]
              rw [hnextEq, hstuck] at htail
              cases (concreteMicroPath_of_stuck slots finish htail).2.symm.trans hfinish
          | some z' =>
              by_cases haccept : act.target = ULogControl.qAccept
              · have hacc : oneStepAt slot (.running q z) = .accepted z' := by
                  simp [oneStepAt, hrule, happly, haccept]
                rw [hnextEq, hacc] at htail
                obtain ⟨hslots, hfin⟩ :=
                  concreteMicroPath_of_accepted z' slots finish htail
                subst slots
                have htape : z' = tape :=
                  Result.accepted.inj (hfin.symm.trans hfinish)
                subst htape
                have hstep := reverse_accepting_step q origin leftExtra rightExtra
                  z z' slot act hrule happly haccept
                refine ⟨[MStarULogAssembly.simArrow (uarrowOf hrule)],
                  by simp [uarrowOf, MStarULogAssembly.simArrow], ?_⟩
                exact first_hit_cons
                  (anchoredFramedULogConfig q origin leftExtra rightExtra z)
                  (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z')
                  (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z')
                  (MStarULogAssembly.simArrow (uarrowOf hrule)) []
                  (by simp [anchoredFramedULogConfig]) hstep
                  (first_hit_nil_of_accept _
                    (by simp [anchoredFramedOuterAcceptConfig]))
              · by_cases hreject : act.target = ULogControl.qReject
                · have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
                  have hrej : oneStepAt slot (.running q z) = .rejected := by
                    simp [oneStepAt, hrule, happly, hreject, hqa]
                  rw [hnextEq, hrej] at htail
                  cases (concreteMicroPath_of_rejected slots finish htail).2.symm.trans
                    hfinish
                · have hrun : oneStepAt slot (.running q z) =
                      .running act.target z' := by
                    simp [oneStepAt, hrule, happly, haccept, hreject]
                  rw [hnextEq, hrun] at htail
                  have hstep := reverse_running_step q act.target origin leftExtra
                    rightExtra z z' slot act hrule happly rfl haccept hreject
                  rcases ih act.target z' tape (hnextEq.trans hrun) hfinish with
                    ⟨rest, hmap, hhit⟩
                  refine ⟨MStarULogAssembly.simArrow (uarrowOf hrule) :: rest,
                    by simp [uarrowOf, MStarULogAssembly.simArrow, hmap], ?_⟩
                  exact first_hit_cons
                    (anchoredFramedULogConfig q origin leftExtra rightExtra z)
                    (anchoredFramedULogConfig act.target origin leftExtra
                      rightExtra z')
                    (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra
                      tape)
                    (MStarULogAssembly.simArrow (uarrowOf hrule)) rest
                    (by simp [anchoredFramedULogConfig]) hstep hhit

noncomputable def rawTape
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) :
    MStarParserExecution.Zipper ULogProgram.Tape :=
  Classical.choose r.property.2

theorem rawPath
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) :
    ConcreteMicroPath (.running q z) r.val (.accepted (rawTape q z T r)) :=
  Classical.choose_spec r.property.2

noncomputable def outerArrows_of_raw
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) : List OuterArrow :=
  Classical.choose (micro_path_to_first_hit (rawPath q z T r) q origin
    leftExtra rightExtra z (rawTape q z T r) rfl rfl)

theorem outerArrows_of_raw_map
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) :
    (outerArrows_of_raw q origin leftExtra rightExtra z T r).map
      (fun a => a.val.2) = r.val :=
  (Classical.choose_spec (micro_path_to_first_hit (rawPath q z T r) q origin
    leftExtra rightExtra z (rawTape q z T r) rfl rfl)).1

theorem outerArrows_of_raw_firstHit
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) :
    FirstHit (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (outerArrows_of_raw q origin leftExtra rightExtra z T r)
      (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra
        (rawTape q z T r)) :=
  (Classical.choose_spec (micro_path_to_first_hit (rawPath q z T r) q origin
    leftExtra rightExtra z (rawTape q z T r) rfl rfl)).2

noncomputable def outerToRaw
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (w : FirstHitWordsAtMost
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) T) :
    RawAcceptingMicroWordsAtMost T (.running q z) :=
  ⟨slotWord w.val, by
    refine ⟨by simpa [slotWord_length] using w.property.1, ?_⟩
    obtain ⟨d, hd⟩ := w.property.2
    obtain ⟨z', hpath⟩ := first_hit_to_micro_path
      (PakOuterULogTraceBridge.OuterArrowHistory.of_run_eq w.val
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) d hd.1)
      q origin leftExtra rightExtra guards z rfl hd
    exact ⟨z', by simpa [slotWord] using hpath⟩⟩

noncomputable def rawToOuter
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat)
    (r : RawAcceptingMicroWordsAtMost T (.running q z)) :
    FirstHitWordsAtMost
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) T :=
  ⟨outerArrows_of_raw q origin leftExtra rightExtra z T r, by
    refine ⟨?_,
      ⟨anchoredFramedOuterAcceptConfig origin leftExtra rightExtra
        (rawTape q z T r),
        outerArrows_of_raw_firstHit q origin leftExtra rightExtra z T r⟩⟩
    have hmap := outerArrows_of_raw_map q origin leftExtra rightExtra z T r
    have hlen :
        (outerArrows_of_raw q origin leftExtra rightExtra z T r).length =
          r.val.length := by
      simpa [List.length_map] using congrArg List.length hmap
    exact hlen.trans_le r.property.1⟩

noncomputable def framedFirstHitMicroEquiv
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat) :
    FirstHitWordsAtMost
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) T ≃
    RawAcceptingMicroWordsAtMost T (.running q z) where
  toFun := outerToRaw q origin leftExtra rightExtra guards z T
  invFun := rawToOuter q origin leftExtra rightExtra z T
  left_inv w := by
    apply first_hit_slot_map_injective
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) T
    have hmap := outerArrows_of_raw_map q origin leftExtra rightExtra z T
      (outerToRaw q origin leftExtra rightExtra guards z T w)
    simp [slotWord, rawToOuter, outerToRaw] at hmap ⊢
    exact hmap
  right_inv r := by
    apply Subtype.ext
    have hmap := outerArrows_of_raw_map q origin leftExtra rightExtra z T r
    simp [slotWord, rawToOuter, outerToRaw] at hmap ⊢
    exact hmap

theorem framed_first_hit_micro_card
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat) :
    Nat.card (FirstHitWordsAtMost
      (anchoredFramedULogConfig q origin leftExtra rightExtra z) T) =
      Nat.card (RawAcceptingMicroWordsAtMost T (.running q z)) := by
  let := first_hit_words_finite
    (anchoredFramedULogConfig q origin leftExtra rightExtra z) T
  let := ULogConcreteMicroCutoffMonotonicity.finite_raw_cutoff T (.running q z)
  exact Nat.card_congr
    (framedFirstHitMicroEquiv q origin leftExtra rightExtra guards z T)

def all_framed_first_hit_micro_bijection_spec : Prop :=
  ∀ (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) (T : Nat),
    let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
    let toRaw := outerToRaw q origin leftExtra rightExtra guards z T
    let toOuter := rawToOuter q origin leftExtra rightExtra z T
    (∀ w : FirstHitWordsAtMost c T,
      (toRaw w).val = w.val.map (fun a => a.val.2) ∧
        (toRaw w).val.length = w.val.length) ∧
    (∀ r : RawAcceptingMicroWordsAtMost T (.running q z),
      (toOuter r).val.map (fun a => a.val.2) = r.val ∧
        (toOuter r).val.length = r.val.length) ∧
    Function.LeftInverse toOuter toRaw ∧
    Function.RightInverse toOuter toRaw ∧
    Nat.card (FirstHitWordsAtMost c T) =
      Nat.card (RawAcceptingMicroWordsAtMost T (.running q z))

theorem all_framed_first_hit_micro_bijection_spec_holds :
    all_framed_first_hit_micro_bijection_spec := by
  intro q origin leftExtra rightExtra guards z T
  let E := framedFirstHitMicroEquiv q origin leftExtra rightExtra guards z T
  refine ⟨?_, ?_, E.left_inv, E.right_inv,
    framed_first_hit_micro_card q origin leftExtra rightExtra guards z T⟩
  · intro w
    exact ⟨rfl, slotWord_length w.val⟩
  · intro r
    have hmap := outerArrows_of_raw_map q origin leftExtra rightExtra z T r
    refine ⟨hmap, ?_⟩
    simpa [rawToOuter, List.length_map] using congrArg List.length hmap

end PakFixedPolyomino.PakAllFramedFirstHitMicroBijection
