import PakFixedPolyomino.PakOuterULogTraceBridge
import PakFixedPolyomino.PakSlotOneCopierRightEndReflection
import PakFixedPolyomino.PakSlotOneExactCount
import PakFixedPolyomino.PakCopierSlackExecution
import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakULogSlackInvariance
import PakFixedPolyomino.PakULogGeneralCapacityBootstrap

/-! # Reflection of literal outer simulation arrows

The forward bridge maps every occupied `U_log` arrow to a literal arrow of
the outer M-star program.  Here we prove the missing local converse directly
from a successful physical step.  This is the atomic inverse used when a
chronological slot-one full-frame history is split into exact concrete ULog
cycles.
-/

namespace PakFixedPolyomino.PakOuterULogReflection

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge PakOuterULogBridge

abbrev OuterTape := MStarULogAssembly.Tape
abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig
abbrev OuterArrow := MStarULogAssembly.Arrow

private theorem outerConfig_ext (c d : OuterConfig)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp only at hstate hhead htape ⊢
  subst_vars
  rfl

private theorem outer_rule_eq_actionOf (a : OuterArrow) :
    MStarULogAssembly.program.rule a.1.1.1 a.1.1.2 a.1.2 =
      some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact hfound
  · rename_i hnone
    exact (a.2 hnone).elim

private theorem outerStep_eq_afterAction
    (c d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    d = PakParserOuterBridge.afterAction c
      (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
  unfold FiniteOneTapeSemantics.step at hstep
  dsimp only at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · exact (Option.some.inj hstep).symm
    · simp at hstep

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

/-- A simulated outer control has no transition on a framing letter. -/
theorem sim_noncore_rule_none
    (q : ULogControl.State) (x : OuterTape)
    (hcore : ∀ y : ULogProgram.Tape, x ≠ .core y)
    (slot : Fin 2) :
    MStarULogAssembly.program.rule (.sim q) x slot = none := by
  cases x with
  | core y => exact (hcore y rfl).elim
  | hash | markL | markR | scratch i =>
      simp [MStarULogAssembly.program, MStarULogAssembly.data,
        MStarOuterProgram.program]

/-- Consequently an actual physical step cannot start from a simulated state
whose head is already on a non-core framing symbol. -/
theorem no_outerStep_from_sim_noncore
    (q : ULogControl.State) (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state = (.sim q : MStarULogAssembly.State))
    (hcore : ∀ y : ULogProgram.Tape, c.tape c.head ≠ .core y)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) : False := by
  have hphysical := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hsource : a.1.1.1 = (.sim q : MStarULogAssembly.State) :=
    hphysical.1.symm.trans hstate
  have hread : a.1.1.2 = c.tape c.head := hphysical.2.symm
  apply a.2
  rw [hsource, hread]
  exact sim_noncore_rule_none q (c.tape c.head) hcore a.1.2

private theorem reject_outer_rule_target
    (x : OuterTape) (slot : Fin 2)
    (act : FiniteOneTapeProgram.Action MStarULogAssembly.State OuterTape)
    (hrule : MStarULogAssembly.program.rule (.reject : MStarULogAssembly.State)
      x slot = some act) : act.target = .reject := by
  cases x <;> fin_cases slot <;>
    simp [MStarULogAssembly.program, MStarULogAssembly.data,
      MStarOuterProgram.program] at hrule <;>
    cases hrule <;> rfl

/-- The literal outer reject control is absorbing along every successful
labelled step. -/
theorem outerStep_reject_state
    (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state = (.reject : MStarULogAssembly.State))
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    d.state = .reject := by
  have hphysical := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hsource : a.1.1.1 = (.reject : MStarULogAssembly.State) :=
    hphysical.1.symm.trans hstate
  have hrule := outer_rule_eq_actionOf a
  have htarget := reject_outer_rule_target a.1.1.2 a.1.2
    (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) (by
      simpa [hsource] using hrule)
  have hd := FiniteOneTapeSemantics.step_some_state
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  simpa [FiniteOneTapeProgram.transition, htarget] using hd

/-- A chronological outer history starting in reject cannot end in accept. -/
theorem reject_history_not_accept
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (hstart : start.state = (.reject : MStarULogAssembly.State)) :
    finish.state ≠ .accept := by
  induction H with
  | nil c =>
      simpa [hstart] using
        (show (.reject : MStarULogAssembly.State) ≠ .accept by decide)
  | cons c next finish a arrows hstep tail ih =>
      exact ih (outerStep_reject_state c next a hstart hstep)

/-- A simulated configuration on a non-core head cannot be the beginning of
an accepting chronological history. -/
theorem sim_noncore_history_not_accept
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (q : ULogControl.State)
    (hstate : start.state = (.sim q : MStarULogAssembly.State))
    (hcore : ∀ y : ULogProgram.Tape, start.tape start.head ≠ .core y) :
    finish.state ≠ .accept := by
  cases H with
  | nil c =>
      simpa [hstate] using
        (show (.sim q : MStarULogAssembly.State) ≠ .accept by decide)
  | cons c next finish a arrows hstep tail =>
      exact (no_outerStep_from_sim_noncore q start next a hstate hcore hstep).elim

/-- A one-step copier transition into `groupReady` exposes the physical left
marker as the nearest left cell of its output zipper. -/
theorem copier_oneStep_groupReady_leftRev_markL
    (q : MStarCopierMicrocode.CopierState)
    (z out : MStarParserExecution.Zipper OuterTape)
    (hstep : MStarCopierExecution.oneStep (.running q z) = .groupReady out) :
    ∃ rest, out.leftRev = .markL :: rest := by
  have hcontrol :=
    PakSlotOneCopierRightEndReflection.oneStep_running_to_groupReady q z out hstep
  rcases z with ⟨left, focus, right⟩
  simp only [MStarParserExecution.Zipper.focus] at hcontrol
  rcases hcontrol with ⟨hq, hfocus⟩
  subst q
  subst focus
  cases right with
  | nil =>
      simp [MStarCopierExecution.oneStep, MStarCopierMicrocode.copierStep,
        MStarCopierMicrocode.copySim, MStarParserExecution.applyAction] at hstep
  | cons y right =>
      have hexact := MStarCopierExecution.finalReturn_mark_step left y right
      rw [hexact] at hstep
      have hout : out = ⟨.markL :: left, y, right⟩ :=
        MStarCopierExecution.Result.groupReady.inj hstep.symm
      subst out
      exact ⟨left, rfl⟩

/-- The same marker fact holds for an arbitrarily long successful copier
run. -/
theorem copier_run_groupReady_leftRev_markL :
    ∀ (fuel : ℕ) (q : MStarCopierMicrocode.CopierState)
      (z out : MStarParserExecution.Zipper OuterTape),
      MStarCopierExecution.run fuel (.running q z) = .groupReady out →
      ∃ rest, out.leftRev = .markL :: rest := by
  intro fuel
  induction fuel with
  | zero =>
      intro q z out hrun
      cases hrun
  | succ fuel ih =>
      intro q z out hrun
      cases hnext : MStarCopierExecution.oneStep (.running q z) with
      | rejected =>
          rw [MStarCopierExecution.run_succ, hnext,
            MStarCopierExecution.rejected_absorbing] at hrun
          cases hrun
      | stuck =>
          rw [MStarCopierExecution.run_succ, hnext,
            MStarCopierExecution.stuck_absorbing] at hrun
          cases hrun
      | groupReady w =>
          have hw : w = out := by
            have hready : MStarCopierExecution.run fuel (.groupReady w) =
                .groupReady out := by
              simpa [MStarCopierExecution.run_succ, hnext] using hrun
            simpa [MStarCopierExecution.run, MStarCopierExecution.oneStep] using
              hready
          subst out
          exact copier_oneStep_groupReady_leftRev_markL q z w hnext
      | running q' z' =>
          apply ih q' z' out
          simpa [MStarCopierExecution.run_succ, hnext] using hrun

/-- Canonical copier completion therefore supplies the two non-core boundary
guards required by ULog history reflection. -/
theorem canonicalGroupReady_has_markL_left
    (x : ConcretePakSide.Word)
    (z : MStarParserExecution.Zipper OuterTape)
    (h : PakParserOuterBridge.SideCopierCanonical x (.groupReady z)) :
    ∃ rest, z.leftRev = .markL :: rest := by
  rcases h.1 with ⟨fuel, hrun⟩
  exact copier_run_groupReady_leftRev_markL fuel .seedCell
    (PakSideScanner.sideCopierSeedZipper x) z hrun

def NonCoreHead (xs : List OuterTape) : Prop :=
  ∀ y : ULogProgram.Tape, xs.head? ≠ some (.core y)

structure FramingGuards (leftExtra rightExtra : List OuterTape) : Prop where
  left : NonCoreHead leftExtra
  right : NonCoreHead rightExtra

theorem framingGuards_markers (left right : List OuterTape) :
    FramingGuards (.markL :: left) (.markR :: right) := by
  constructor <;> intro y <;> simp [NonCoreHead]

/-- An occupied outer rule at a simulated core source is the image of a
unique occupied ULog rule with the same physical slot label. -/
theorem simArrow_exists_unique_of_outer_rule
    (q : ULogControl.State) (x : ULogProgram.Tape)
    (a : OuterArrow)
    (hsource : a.1.1.1 = (.sim q : MStarULogAssembly.State))
    (hread : a.1.1.2 = (.core x : OuterTape)) :
    ∃! ua : MStarULogAssembly.ULogArrow,
      MStarULogAssembly.simArrow ua = a := by
  have hoccupied : ULogProgram.program.rule q x a.1.2 ≠ none := by
    intro hnone
    apply a.2
    rw [hsource, hread, MStarULogAssembly.sim_rule_eq, hnone]
    rfl
  let ua : MStarULogAssembly.ULogArrow :=
    ⟨((q, x), a.1.2), hoccupied⟩
  refine ⟨ua, ?_, ?_⟩
  · apply Subtype.ext
    exact Prod.ext (Prod.ext hsource.symm hread.symm) rfl
  · intro ub hub
    apply MStarULogAssembly.simArrow_injective
    exact hub.trans (by
      apply Subtype.ext
      exact Prod.ext (Prod.ext hsource hread) rfl)

/-- A successful literal step out of a framed simulated configuration has a
unique finite ULog arrow.  In particular its labelled successor is a genuine
`validStepAt`, not an absorbing auxiliary `stuck` introduced by `oneStepAt`.

The conclusion intentionally stops before asserting that the successor still
has the same physical framing.  That spatial statement is the next history
invariant: an isolated last core cell could move into a framing marker even
though the current outer step itself is successful. -/
theorem outerStep_from_framedSim_reflects_validStep
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d) :
    ∃! ua : MStarULogAssembly.ULogArrow,
      MStarULogAssembly.simArrow ua = a ∧
      ULogBootstrapExecution.validStepAt ua.1.2 (.running q z) =
        some (ULogBootstrapExecution.oneStepAt ua.1.2 (.running q z)) := by
  let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
  have hphysical := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hsource : a.1.1.1 = (.sim q : MStarULogAssembly.State) := by
    exact hphysical.1.symm.trans (by rfl)
  have hheadTape : c.tape c.head = (.core z.focus : OuterTape) := by
    change anchoredZipperTape origin
      (frameCoreZipper leftExtra rightExtra z)
        (origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length) =
      .core z.focus
    rw [anchoredZipperTape_at_head]
    rfl
  have hread : a.1.1.2 = (.core z.focus : OuterTape) :=
    hphysical.2.symm.trans hheadTape
  rcases simArrow_exists_unique_of_outer_rule q z.focus a hsource hread with
    ⟨ua, hua, hunique⟩
  have hslot : ua.1.2 = a.1.2 := by
    have h := congrArg (fun arrow : OuterArrow => arrow.1.2) hua
    exact h
  have hoccupied : ULogProgram.program.rule q z.focus ua.1.2 ≠ none := by
    rw [hslot]
    intro hnone
    apply a.2
    rw [hsource, hread, MStarULogAssembly.sim_rule_eq, hnone]
    rfl
  have hvalid : ULogBootstrapExecution.validStepAt ua.1.2 (.running q z) =
      some (ULogBootstrapExecution.oneStepAt ua.1.2 (.running q z)) := by
    cases hrule : ULogProgram.program.rule q z.focus ua.1.2 with
    | none => exact (hoccupied hrule).elim
    | some action => simp [ULogBootstrapExecution.validStepAt, hrule]
  refine ⟨ua, ⟨hua, hvalid⟩, ?_⟩
  intro ub hub
  exact hunique ub hub.1

/-- Complete local reflection package for one chronological outer step.  The
physical successor is the literal `afterAction` of the mapped finite action;
this equality is what the history induction uses to decide whether the head
remains in the finite core or has escaped into a framing marker. -/
structure FramedSimStepReflection
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow) : Type where
  uarrow : MStarULogAssembly.ULogArrow
  outer_arrow_eq : MStarULogAssembly.simArrow uarrow = a
  valid : ULogBootstrapExecution.validStepAt uarrow.1.2 (.running q z) =
    some (ULogBootstrapExecution.oneStepAt uarrow.1.2 (.running q z))
  successor_eq : d = PakParserOuterBridge.afterAction
    (anchoredFramedULogConfig q origin leftExtra rightExtra z)
    (MStarOuterProgram.mapUAction MStarULogAssembly.data
      (FiniteOneTapeProgram.actionOf ULogProgram.program uarrow))

/-- Construct the complete local reflection package from the actual successful
outer step. -/
noncomputable def outerStep_from_framedSim_reflection
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d) :
    FramedSimStepReflection q origin leftExtra rightExtra z d a := by
  let hex := ExistsUnique.exists
    (outerStep_from_framedSim_reflects_validStep q origin leftExtra
      rightExtra z d a hstep)
  let ua := Classical.choose hex
  have hua := Classical.choose_spec hex
  refine
    { uarrow := ua
      outer_arrow_eq := hua.1
      valid := hua.2
      successor_eq := ?_ }
  have hd := outerStep_eq_afterAction
    (anchoredFramedULogConfig q origin leftExtra rightExtra z) d a hstep
  rw [← hua.1] at hd
  rw [MStarULogAssembly.actionOf_simArrow] at hd
  exact hd

/-- The target control of a reflected physical step is exactly the outer
image of the target control in its unique finite ULog action. -/
theorem outerStep_from_framedSim_target
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d) :
    let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
      z d a hstep
    d.state = MStarOuterProgram.mapUState MStarULogAssembly.data
      (FiniteOneTapeProgram.actionOf ULogProgram.program R.uarrow).target := by
  let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
    z d a hstep
  have hstate := congrArg (fun c : OuterConfig => c.state) R.successor_eq
  simpa [PakParserOuterBridge.afterAction,
    MStarOuterProgram.mapUAction] using hstate

/-- Slot-parametric form of the finite one-step running inversion. -/
theorem ulogOneStepAt_eq_running_iff
    (slot : Fin 2) (q q' : ULogControl.State)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.oneStepAt slot (.running q z) = .running q' z' ↔
      ∃ act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape,
        ULogProgram.program.rule q z.focus slot = some act ∧
        MStarParserExecution.applyAction z act = some z' ∧
        act.target = q' ∧ q' ≠ ULogControl.qAccept ∧
        q' ≠ ULogControl.qReject := by
  constructor
  · intro h
    simp only [ULogBootstrapExecution.oneStepAt] at h
    split at h
    · contradiction
    · rename_i act hrule
      split at h
      · contradiction
      · rename_i next happly
        split at h
        · contradiction
        · rename_i haccept
          split at h
          · contradiction
          · rename_i hreject
            have hp : act.target = q' ∧ next = z' := by
              simpa only [ULogBootstrapExecution.Result.running.injEq] using h
            refine ⟨act, hrule, happly.trans (congrArg some hp.2), hp.1, ?_, ?_⟩
            · intro hq
              exact haccept (hp.1.trans hq)
            · intro hq
              exact hreject (hp.1.trans hq)
  · rintro ⟨act, hrule, happly, rfl, haccept, hreject⟩
    simp [ULogBootstrapExecution.oneStepAt, hrule, happly, haccept, hreject]

/-- Slot-parametric inversion for a finite accepting step. -/
theorem ulogOneStepAt_eq_accepted_iff
    (slot : Fin 2) (q : ULogControl.State)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.oneStepAt slot (.running q z) = .accepted z' ↔
      ∃ act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape,
        ULogProgram.program.rule q z.focus slot = some act ∧
        MStarParserExecution.applyAction z act = some z' ∧
        act.target = ULogControl.qAccept := by
  constructor
  · intro h
    simp only [ULogBootstrapExecution.oneStepAt] at h
    split at h
    · contradiction
    · rename_i act hrule
      split at h
      · contradiction
      · rename_i next happly
        split at h
        · rename_i haccept
          have hz : next = z' := by
            simpa only [ULogBootstrapExecution.Result.accepted.injEq] using h
          exact ⟨act, hrule, happly.trans (congrArg some hz), haccept⟩
        · split at h <;> contradiction
  · rintro ⟨act, hrule, happly, htarget⟩
    simp [ULogBootstrapExecution.oneStepAt, hrule, happly, htarget]

theorem ulogOneStepAt_eq_stuck_iff
    (slot : Fin 2) (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some act) :
    ULogBootstrapExecution.oneStepAt slot (.running q z) = .stuck ↔
      MStarParserExecution.applyAction z act = none := by
  cases happly : MStarParserExecution.applyAction z act with
  | none => simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
  | some z' =>
      by_cases haccept : act.target = ULogControl.qAccept
      · simp [ULogBootstrapExecution.oneStepAt, hrule, happly, haccept]
      · by_cases hreject : act.target = ULogControl.qReject
        · have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
          simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hreject, hqa]
        · simp [ULogBootstrapExecution.oneStepAt, hrule, happly, haccept,
            hreject]

theorem ulogOneStepAt_eq_rejected_iff
    (slot : Fin 2) (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.oneStepAt slot (.running q z) = .rejected ↔
      ∃ act z', ULogProgram.program.rule q z.focus slot = some act ∧
        MStarParserExecution.applyAction z act = some z' ∧
        act.target = ULogControl.qReject := by
  constructor
  · intro h
    simp only [ULogBootstrapExecution.oneStepAt] at h
    split at h
    · contradiction
    · rename_i act hrule
      split at h
      · contradiction
      · rename_i z' happly
        split at h
        · contradiction
        · rename_i haccept
          split at h
          · rename_i hreject
            exact ⟨act, z', hrule, happly, hreject⟩
          · contradiction
  · rintro ⟨act, z', hrule, happly, htarget⟩
    have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
    simp [ULogBootstrapExecution.oneStepAt, hrule, happly, htarget, hqa]

theorem ulog_rule_target_accept_move_stay :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
      (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape),
      ULogProgram.program.rule q x slot = some act →
      act.target = ULogControl.qAccept → act.move = .stay := by
  native_decide

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

/-- If the reflected finite step is running, the physical successor retains
exactly the same framing lists. -/
theorem outerStep_from_framedSim_running_successor
    (q q' : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d)
    (hnext : ULogBootstrapExecution.oneStepAt
      (outerStep_from_framedSim_reflection q origin leftExtra rightExtra
        z d a hstep).uarrow.1.2 (.running q z) = .running q' z') :
    d = anchoredFramedULogConfig q' origin leftExtra rightExtra z' := by
  let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
    z d a hstep
  rcases (ulogOneStepAt_eq_running_iff R.uarrow.1.2 q q' z z').mp hnext with
    ⟨act, hrule, happly, htarget, haccept, hreject⟩
  have haction := reflected_actionOf_eq (R := R) hstep act hrule
  rw [R.successor_eq, haction]
  let mapped := MStarOuterProgram.mapUAction MStarULogAssembly.data act
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z mapped = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' act happly
  have htarget' : mapped.target = (.sim q' : MStarULogAssembly.State) := by
    simp only [mapped, MStarOuterProgram.mapUAction]
    rw [htarget, mapUState_eq_sim haccept hreject]
  have hhead : origin + Z'.leftRev.length =
      moveHead mapped.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' mapped happly'
  have htape : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) mapped.write :=
    anchoredZipperTape_applyAction origin Z Z' mapped happly'
  simp only [PakParserOuterBridge.afterAction, anchoredFramedULogConfig,
    writtenTape]
  rw [htarget']
  congr 1
  · exact hhead.symm
  · exact htape.symm

/-- The accepting case likewise preserves the framing and reflects to the
literal outer accept configuration. -/
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
    exact MStarULogAssembly.simulated_accept_maps_to_outer_accept
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

private theorem frameCoreZipper_tape_right_boundary
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (left : List ULogProgram.Tape) (focus : ULogProgram.Tape) :
    anchoredZipperTape origin
        (frameCoreZipper leftExtra rightExtra ⟨left, focus, []⟩)
        (origin +
          (frameCoreZipper leftExtra rightExtra
            ⟨left, focus, []⟩).leftRev.length + 1) =
      rightExtra.getD 0 .hash := by
  have hindex : origin +
      (frameCoreZipper leftExtra rightExtra
        ⟨left, focus, []⟩).leftRev.length + 1 =
      origin + (((frameCoreZipper leftExtra rightExtra
        ⟨left, focus, []⟩).leftRev.length + 1 : ℕ) : Int) := by
    push_cast
    ring
  rw [hindex]
  rw [anchoredZipperTape_at_offset]
  let pre : List OuterTape :=
    leftExtra.reverse ++
      (left.map (fun x => (.core x : OuterTape))).reverse ++ [.core focus]
  have hpre : pre.length = leftExtra.length + left.length + 1 := by
    simp [pre]
    omega
  have hcells : anchoredZipperCells
      (frameCoreZipper leftExtra rightExtra ⟨left, focus, []⟩) =
      pre ++ rightExtra := by
    simp [PakParserOuterBridge.anchoredZipperCells, frameCoreZipper, pre,
      List.append_assoc]
  rw [hcells]
  simp only [frameCoreZipper, MStarParserExecution.Zipper.leftRev,
    List.length_append, List.length_map]
  rw [List.getD_append_right]
  · congr 1
    rw [hpre]
    omega
  · rw [hpre]
    omega

private theorem frameCoreZipper_tape_left_boundary
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (focus : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    anchoredZipperTape origin
        (frameCoreZipper leftExtra rightExtra ⟨[], focus, right⟩)
        (origin +
          (frameCoreZipper leftExtra rightExtra
            ⟨[], focus, right⟩).leftRev.length - 1) =
      match leftExtra with
      | [] => .hash
      | boundary :: _ => boundary := by
  cases leftExtra with
  | nil =>
      simp [frameCoreZipper, PakParserOuterBridge.anchoredZipperTape,
        PakParserOuterBridge.anchoredZipperCells]
  | cons boundary rest =>
      rw [show origin +
          (frameCoreZipper (boundary :: rest) rightExtra
            ⟨[], focus, right⟩).leftRev.length - 1 =
          origin + rest.length by
        simp [frameCoreZipper]
        omega]
      rw [anchoredZipperTape_at_offset]
      simp [frameCoreZipper, PakParserOuterBridge.anchoredZipperCells]

/-- If the finite zipper action reflected from a physical step cannot be
performed, the physical head has crossed one of the two guarded boundaries.
Its successor therefore reads a non-core framing symbol. -/
theorem finiteApply_or_successor_noncore
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d) :
    let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
      z d a hstep
    (∃ z', MStarParserExecution.applyAction z
      (FiniteOneTapeProgram.actionOf ULogProgram.program R.uarrow) = some z') ∨
      ∀ y : ULogProgram.Tape, d.tape d.head ≠ .core y := by
  let R := outerStep_from_framedSim_reflection q origin leftExtra rightExtra
    z d a hstep
  generalize hact : FiniteOneTapeProgram.actionOf ULogProgram.program R.uarrow = act
  by_cases happly : ∃ z', MStarParserExecution.applyAction z act = some z'
  · refine Or.inl ?_
    rw [hact]
    exact happly
  · right
    have hnone : MStarParserExecution.applyAction z act = none := by
      cases h : MStarParserExecution.applyAction z act with
      | none => rfl
      | some z' => exact (happly ⟨z', h⟩).elim
    rcases z with ⟨left, focus, right⟩
    rcases act with ⟨write, target, move⟩
    cases move with
    | stay => simp [MStarParserExecution.applyAction] at hnone
    | right =>
        cases right with
        | cons next rest =>
            simp [MStarParserExecution.applyAction] at hnone
        | nil =>
            intro y hy
            rw [R.successor_eq, hact] at hy
            have hyBoundary : rightExtra.getD 0 .hash = (.core y : OuterTape) := by
              calc
                rightExtra.getD 0 .hash =
                    anchoredZipperTape origin
                      (frameCoreZipper leftExtra rightExtra
                        ⟨left, focus, []⟩)
                      (origin +
                        (frameCoreZipper leftExtra rightExtra
                          ⟨left, focus, []⟩).leftRev.length + 1) :=
                  (frameCoreZipper_tape_right_boundary origin leftExtra
                    rightExtra left focus).symm
                _ = .core y := by
                  simpa [PakParserOuterBridge.afterAction,
                    MStarOuterProgram.mapUAction, anchoredFramedULogConfig,
                    frameCoreZipper, FiniteOneTapeSemantics.moveHead,
                    FiniteOneTapeSemantics.writtenTape, Function.update] using hy
            cases rightExtra with
            | nil => simp at hyBoundary
            | cons boundary rest =>
                apply guards.right y
                simpa [NonCoreHead] using congrArg some hyBoundary
    | left =>
        cases left with
        | cons previous rest =>
            simp [MStarParserExecution.applyAction] at hnone
        | nil =>
            intro y hy
            rw [R.successor_eq, hact] at hy
            have hyBoundary :
                (match leftExtra with
                  | [] => .hash
                  | boundary :: _ => boundary) = (.core y : OuterTape) := by
              calc
                (match leftExtra with
                  | [] => .hash
                  | boundary :: _ => boundary) =
                    anchoredZipperTape origin
                      (frameCoreZipper leftExtra rightExtra
                        ⟨[], focus, right⟩)
                      (origin +
                        (frameCoreZipper leftExtra rightExtra
                          ⟨[], focus, right⟩).leftRev.length - 1) :=
                  (frameCoreZipper_tape_left_boundary origin leftExtra
                    rightExtra focus right).symm
                _ = .core y := by
                  simpa [PakParserOuterBridge.afterAction,
                    MStarOuterProgram.mapUAction, anchoredFramedULogConfig,
                    frameCoreZipper, FiniteOneTapeSemantics.moveHead,
                    FiniteOneTapeSemantics.writtenTape, Function.update] using hy
            cases leftExtra with
            | nil => simp at hyBoundary
            | cons boundary rest =>
                apply guards.left y
                simpa [NonCoreHead] using congrArg some hyBoundary

/-- A complete accepting outer history beginning at a guarded framed ULog
configuration projects to one genuine finite `ConcreteMicroPath`.  The list
of finite slot labels is the chronological prefix of physical labels up to
the first outer accept; later deterministic accept-padding arrows are not
mistaken for additional ULog choices. -/
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
              _ = .reject := MStarULogAssembly.simulated_reject_maps_to_outer_reject
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
          · have hmove := ulog_rule_target_accept_move_stay q z.focus
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
                    MStarULogAssembly.simulated_reject_maps_to_outer_reject
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

/-- A first zero-run hit of `chooseSlot` splits every accepting labelled
micro-path at exactly that occurrence.  Thus the deterministic prefix cannot
hide a slot-one edge. -/
theorem firstChoice_split_acceptingMicroPath :
    ∀ (steps : ℕ) (start choice : ULogBootstrapExecution.Result)
      (slots : List (Fin 2)) (acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape),
      ULogBootstrapExecution.ValidZeroRun steps start choice →
      (∀ m, m < steps →
        ¬ ULogBootstrapExecution.IsConcreteChoice
          (ULogBootstrapExecution.run m start)) →
      ULogBootstrapExecution.ConcreteMicroPath start slots (.accepted acceptedZ) →
      ∃ rest,
        slots = List.replicate steps (0 : Fin 2) ++ rest ∧
        ULogBootstrapExecution.ConcreteMicroPath choice rest (.accepted acceptedZ) := by
  intro steps
  induction steps with
  | zero =>
      intro start choice slots acceptedZ hzero _ path
      cases hzero
      exact ⟨slots, by simp, path⟩
  | succ steps ih =>
      intro start choice slots acceptedZ hzero hbefore path
      cases hzero with
      | cons r next choice n hhead htail =>
          cases path with
          | nil r =>
              simp [ULogBootstrapExecution.validStepAt] at hhead
          | cons r next' finish slot rest hslot pathTail =>
              have hnotChoice :
                  ¬ ULogBootstrapExecution.IsConcreteChoice start := by
                simpa [ULogBootstrapExecution.run] using hbefore 0 (by omega)
              have hslotZero : slot = 0 := by
                cases start with
                | accepted z => simp [ULogBootstrapExecution.validStepAt] at hslot
                | rejected => simp [ULogBootstrapExecution.validStepAt] at hslot
                | stuck => simp [ULogBootstrapExecution.validStepAt] at hslot
                | running q z =>
                    have hq : q ≠ .chooseSlot := by
                      intro hq
                      subst q
                      exact hnotChoice (by simp [ULogBootstrapExecution.IsConcreteChoice])
                    have hcases : slot.1 = 0 ∨ slot.1 = 1 := by omega
                    rcases hcases with hzero | hone
                    · exact Fin.ext hzero
                    · have hslotOne : slot = 1 := Fin.ext hone
                      subst slot
                      have hnone :=
                        ULogBootstrapExecution.validStepAt_one_nonchoose q hq z
                      rw [hnone] at hslot
                      cases hslot
              subst slot
              have hnext : next' = next := by
                apply Option.some.inj
                exact hslot.symm.trans hhead
              subst next'
              have hbeforeTail : ∀ m, m < steps →
                  ¬ ULogBootstrapExecution.IsConcreteChoice
                    (ULogBootstrapExecution.run m next) := by
                intro m hm
                have hrun : ULogBootstrapExecution.run (m + 1) start =
                    ULogBootstrapExecution.run m next := by
                  simp only [ULogBootstrapExecution.run]
                  rw [ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                rw [← hrun]
                exact hbefore (m + 1) (by omega)
              rcases ih next choice rest acceptedZ htail hbeforeTail pathTail with
                ⟨suffix, hrest, hsuffix⟩
              refine ⟨suffix, ?_, hsuffix⟩
              simp [hrest, List.replicate_succ]

/-! ## Post-choice control phase

The only second binary choice must occur in the next semantic cycle.  The
following finite control predicate makes this fact executable and auditable.
-/

def PostChoiceControl : ULogControl.State → Bool
  | .ruleSeek | .ruleSeekChoice _ | .ruleCountSeek _
  | .fieldCompare _ _ | .compareSeekState _
  | .compareReturnSource _ | .compareFinishSource _
  | .compareRestoreSource _ | .readPhase _ _
  | .actionWrite | .actionPhase _ | .actionTarget | .seekSimHead
  | .moveSimHead _ | .shiftRuntime _ | .restoreRule _
  | .mismatchReturnToPc _ | .mismatchCount _ | .mismatchSeekBoundary _
  | .mismatchSkipSource _ | .mismatchSkipRead _ | .mismatchSkipSlot _
  | .mismatchSkipWrite _ | .mismatchSkipTarget _
  | .mismatchSkipMoveFirst _ | .mismatchSkipMoveSecond _
  | .restoreClock | .restorePc | .restoreHead | .readHead => true
  | _ => false

def ChoiceTargetOk (q : ULogControl.State) : Bool :=
  decide (q = ULogControl.qAccept) || decide (q = ULogControl.qReject) ||
    PostChoiceControl q

def PostTargetOk (q : ULogControl.State) : Bool :=
  decide (q = ULogControl.qAccept) || decide (q = ULogControl.qReject) ||
    decide (q = ULogControl.State.cycleStart) || PostChoiceControl q

private def optionChoiceTargetOk
    (a : Option (FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)) :
    Bool := a.elim true (fun act => ChoiceTargetOk act.target)

private def optionPostTargetOk
    (a : Option (FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)) :
    Bool := a.elim true (fun act => PostTargetOk act.target)

private theorem chooseSlot_target_postChoice_or_terminal_table :
    ∀ (x : ULogProgram.Tape) (slot : Fin 2),
      optionChoiceTargetOk (ULogProgram.program.rule .chooseSlot x slot) = true := by
  native_decide

theorem chooseSlot_target_postChoice_or_terminal
    (x : ULogProgram.Tape) (slot : Fin 2)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule .chooseSlot x slot = some act) :
    act.target = ULogControl.qAccept ∨
      act.target = ULogControl.qReject ∨ PostChoiceControl act.target = true := by
  have h := chooseSlot_target_postChoice_or_terminal_table x slot
  simp [optionChoiceTargetOk, hrule, ChoiceTargetOk] at h
  rcases h with (ha | hr) | hp
  · exact Or.inl ha
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr hp)

private theorem postChoice_target_closed_table :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      PostChoiceControl q = true →
      optionPostTargetOk (ULogProgram.program.rule q x slot) = true := by
  native_decide

theorem postChoice_target_closed
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hpost : PostChoiceControl q = true)
    (hrule : ULogProgram.program.rule q x slot = some act) :
    act.target = ULogControl.qAccept ∨ act.target = ULogControl.qReject ∨
      act.target = .cycleStart ∨ PostChoiceControl act.target = true := by
  have h := postChoice_target_closed_table q x slot hpost
  simp [optionPostTargetOk, hrule, PostTargetOk] at h
  rcases h with ((ha | hr) | hc) | hp
  · exact Or.inl ha
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr hp))

theorem postChoice_ne_chooseSlot {q : ULogControl.State}
    (h : PostChoiceControl q = true) : q ≠ .chooseSlot := by
  intro hq
  subst q
  change false = true at h
  cases h

/-- One genuine edge from the post-choice phase which has not yet reached a
cycle stop remains in that phase. -/
theorem postChoice_validStep_nonstop
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (slot : Fin 2) (next : ULogBootstrapExecution.Result)
    (hpost : PostChoiceControl q = true)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) = some next)
    (hstop : ¬ ULogBootstrapExecution.IsConcreteCycleStop next) :
    ∃ q' z', next = .running q' z' ∧ PostChoiceControl q' = true := by
  simp only [ULogBootstrapExecution.validStepAt] at hstep
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [hrule] at hstep
  | some act =>
      have hnext : next = ULogBootstrapExecution.oneStepAt slot (.running q z) := by
        have hs : some (ULogBootstrapExecution.oneStepAt slot (.running q z)) =
            some next := by simpa [hrule] using hstep
        exact (Option.some.inj hs).symm
      rcases postChoice_target_closed q z.focus slot act hpost hrule with
        haccept | hreject | hcycle | hpostTarget
      · rw [hnext] at hstop
        cases happly : MStarParserExecution.applyAction z act <;>
          simp [ULogBootstrapExecution.oneStepAt, hrule, happly, haccept,
            ULogBootstrapExecution.IsConcreteCycleStop,
            ULogBootstrapExecution.concreteHalted] at hstop
      · rw [hnext] at hstop
        cases happly : MStarParserExecution.applyAction z act with
        | none =>
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
        | some z' =>
            have hne : act.target ≠ ULogControl.qAccept := by
              intro h
              have : ULogControl.qReject = ULogControl.qAccept := hreject.symm.trans h
              exact ULogControl.qAccept_ne_qReject this.symm
            have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hreject, hne,
              hqa,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
      · rw [hnext] at hstop
        cases happly : MStarParserExecution.applyAction z act with
        | none =>
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
        | some z' =>
            have hnotAccept : act.target ≠ ULogControl.qAccept := by
              intro h
              have : ULogControl.State.cycleStart = ULogControl.qAccept :=
                hcycle.symm.trans h
              cases this
            have hnotReject : act.target ≠ ULogControl.qReject := by
              intro h
              have : ULogControl.State.cycleStart = ULogControl.qReject :=
                hcycle.symm.trans h
              cases this
            have hnextCycle :
                ULogBootstrapExecution.oneStepAt slot (.running q z) =
                  .running .cycleStart z' := by
              have hca : ULogControl.State.cycleStart ≠ ULogControl.qAccept := by
                decide
              have hcr : ULogControl.State.cycleStart ≠ ULogControl.qReject := by
                decide
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hcycle,
                hnotAccept, hnotReject, hca, hcr]
            change ¬ ULogBootstrapExecution.IsConcreteCycleStop
              (ULogBootstrapExecution.oneStepAt slot (.running q z)) at hstop
            rw [hnextCycle] at hstop
            exact (hstop (Or.inl (by
              simp [ULogBootstrapExecution.IsConcreteCycleBoundary]))).elim
      ·
        cases happly : MStarParserExecution.applyAction z act with
        | none =>
            rw [hnext] at hstop
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
        | some z' =>
            have hnotAccept : act.target ≠ ULogControl.qAccept := by
              intro h
              rw [h] at hpostTarget
              change false = true at hpostTarget
              cases hpostTarget
            have hnotReject : act.target ≠ ULogControl.qReject := by
              intro h
              rw [h] at hpostTarget
              change false = true at hpostTarget
              cases hpostTarget
            refine ⟨act.target, z', ?_, hpostTarget⟩
            rw [hnext]
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotAccept, hnotReject]

/-- A deterministic first-stop suffix beginning in the post-choice phase has
no second binary-choice state before its endpoint. -/
theorem postChoice_zeroRun_no_choice_before :
    ∀ (steps : ℕ) (q : ULogControl.State)
      (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (finish : ULogBootstrapExecution.Result),
      PostChoiceControl q = true →
      ULogBootstrapExecution.ValidZeroRun steps (.running q z) finish →
      (∀ m, m < steps → ¬ ULogBootstrapExecution.IsConcreteCycleStop
        (ULogBootstrapExecution.run m (.running q z))) →
      ∀ m, m < steps → ¬ ULogBootstrapExecution.IsConcreteChoice
        (ULogBootstrapExecution.run m (.running q z)) := by
  intro steps
  induction steps with
  | zero => simp
  | succ steps ih =>
      intro q z finish hpost hrun hbefore m hm
      cases hrun with
      | cons start next finish n hhead htail =>
          cases m with
          | zero =>
              simp only [ULogBootstrapExecution.run]
              intro hchoice
              apply postChoice_ne_chooseSlot hpost
              cases q <;>
                simp [ULogBootstrapExecution.IsConcreteChoice] at hchoice ⊢
          | succ m =>
              have hm' : m < steps := by omega
              have hnextStop :
                  ¬ ULogBootstrapExecution.IsConcreteCycleStop next := by
                have h := hbefore 1 (by omega)
                simpa [ULogBootstrapExecution.run,
                  ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                  using h
              rcases postChoice_validStep_nonstop q z 0 next hpost hhead hnextStop with
                ⟨q', z', rfl, hpost'⟩
              have hbefore' : ∀ k, k < steps →
                  ¬ ULogBootstrapExecution.IsConcreteCycleStop
                    (ULogBootstrapExecution.run k (.running q' z')) := by
                intro k hk
                have h := hbefore (k + 1) (by omega)
                simpa [ULogBootstrapExecution.run,
                  ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                  using h
              have htailNo := ih q' z' finish hpost' htail hbefore' m hm'
              simpa [ULogBootstrapExecution.run,
                ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                using htailNo

/-- The exact-cycle suffix cannot contain another binary choice before its
first cycle boundary or terminal.  This was implicit in the microcode but was
not previously recorded by `ExactConcreteCycle`. -/
theorem exactConcreteCycle_suffix_no_hidden_choice
    {slot : Bool} {start finish : ULogBootstrapExecution.Result}
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot start finish) :
    ∀ m, m < cycle.cycleSuffix.steps →
      ¬ ULogBootstrapExecution.IsConcreteChoice
        (ULogBootstrapExecution.run m cycle.branch) := by
  intro m hm
  cases hchoice : cycle.choice with
  | accepted z =>
      have hhit := cycle.choicePrefix.hit
      rw [hchoice] at hhit
      simp [ULogBootstrapExecution.IsConcreteChoice] at hhit
  | rejected =>
      have hhit := cycle.choicePrefix.hit
      rw [hchoice] at hhit
      simp [ULogBootstrapExecution.IsConcreteChoice] at hhit
  | stuck =>
      have hhit := cycle.choicePrefix.hit
      rw [hchoice] at hhit
      simp [ULogBootstrapExecution.IsConcreteChoice] at hhit
  | running choiceQ choiceZ =>
      have hchoiceControl : choiceQ = .chooseSlot := by
        have hhit := cycle.choicePrefix.hit
        rw [hchoice] at hhit
        cases choiceQ <;>
          simp [ULogBootstrapExecution.IsConcreteChoice] at hhit ⊢
      subst choiceQ
      have hbranchStep : ULogBootstrapExecution.oneStepAt
          (ULogBytecode.slotIndex slot) (.running .chooseSlot choiceZ) =
          cycle.branch := by
        have hs := ULogBootstrapExecution.validStepAt_some_eq_oneStepAt
          cycle.selected
        simpa [hchoice] using hs
      cases hbranch : cycle.branch with
      | accepted z | rejected | stuck =>
          have hbefore := cycle.cycleSuffix.before 0 (by omega)
          rw [hbranch] at hbefore
          simp [ULogBootstrapExecution.run,
            ULogBootstrapExecution.IsConcreteCycleStop,
            ULogBootstrapExecution.concreteHalted] at hbefore
      | running q z =>
          rw [hbranch] at hbranchStep
          rcases (ulogOneStepAt_eq_running_iff (ULogBytecode.slotIndex slot)
              .chooseSlot q choiceZ z).mp hbranchStep with
            ⟨act, hrule, happly, htarget, haccept, hreject⟩
          rcases chooseSlot_target_postChoice_or_terminal choiceZ.focus
              (ULogBytecode.slotIndex slot) act hrule with
            hacceptTarget | hrejectTarget | hpost
          · exact (haccept (htarget.symm.trans hacceptTarget)).elim
          · exact (hreject (htarget.symm.trans hrejectTarget)).elim
          · have hpostQ : PostChoiceControl q = true := by
              rw [← htarget]
              exact hpost
            have hno := postChoice_zeroRun_no_choice_before
              cycle.cycleSuffix.steps q z finish hpostQ
              (by simpa [hbranch] using cycle.cycleSuffix.valid)
              (by
                intro k hk
                have hb := cycle.cycleSuffix.before k hk
                simpa [hbranch] using hb)
              m hm
            simpa [hbranch] using hno

/-- An accepting micro-path whose selected edge agrees with a certified exact
cycle splits after precisely that cycle; all labels in the cycle suffix are
zero. -/
theorem exactConcreteCycle_split_acceptingMicroPath
    {slot : Bool} {start finish : ULogBootstrapExecution.Result}
    (cycle : ULogBootstrapExecution.ExactConcreteCycle slot start finish)
    {tailSlots : List (Fin 2)}
    {acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (path : ULogBootstrapExecution.ConcreteMicroPath cycle.branch tailSlots
      (.accepted acceptedZ)) :
    ∃ rest,
      tailSlots = List.replicate cycle.cycleSuffix.steps (0 : Fin 2) ++ rest ∧
      ULogBootstrapExecution.ConcreteMicroPath finish rest (.accepted acceptedZ) := by
  exact firstChoice_split_acceptingMicroPath cycle.cycleSuffix.steps
    cycle.branch finish tailSlots acceptedZ cycle.cycleSuffix.valid
    (exactConcreteCycle_suffix_no_hidden_choice cycle) path

theorem postChoice_ne_cycleStart {q : ULogControl.State}
    (h : PostChoiceControl q = true) : q ≠ .cycleStart := by
  intro hq
  subst q
  change false = true at h
  cases h

set_option maxRecDepth 100000 in
theorem isConcreteCycleBoundary_running_iff
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.IsConcreteCycleBoundary (.running q z) ↔
      q = .cycleStart := by
  cases q <;> simp [ULogBootstrapExecution.IsConcreteCycleBoundary]

/-- Parse the first cycle stop directly from an actual accepting micro-path
after its selected edge. -/
theorem postChoice_path_firstStop :
    ∀ (q : ULogControl.State)
      (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (slots : List (Fin 2))
      (acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape),
      PostChoiceControl q = true →
      ULogBootstrapExecution.ConcreteMicroPath (.running q z) slots
        (.accepted acceptedZ) →
      ∃ stop,
        ∃ hit : ULogBootstrapExecution.FirstValidZeroHit
          ULogBootstrapExecution.IsConcreteCycleStop (.running q z) stop,
        ∃ rest,
          ULogBootstrapExecution.ConcreteMicroPath stop rest (.accepted acceptedZ) ∧
          slots = List.replicate hit.steps (0 : Fin 2) ++ rest := by
  intro q z slots
  induction slots generalizing q z with
  | nil =>
      intro acceptedZ hpost path
      cases path
  | cons slot rest ih =>
      intro acceptedZ hpost path
      cases path with
      | cons start next finish slot rest hhead tail =>
        have hslotZero : slot = 0 := by
          have hq : q ≠ .chooseSlot := postChoice_ne_chooseSlot hpost
          have hcases : slot.1 = 0 ∨ slot.1 = 1 := by omega
          rcases hcases with hzero | hone
          · exact Fin.ext hzero
          · have hs : slot = 1 := Fin.ext hone
            subst slot
            have hnone := ULogBootstrapExecution.validStepAt_one_nonchoose q hq z
            rw [hnone] at hhead
            cases hhead
        subst slot
        by_cases hstop : ULogBootstrapExecution.IsConcreteCycleStop next
        · let hit : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteCycleStop (.running q z) next :=
            { steps := 1
              valid := .cons (.running q z) next next 0 hhead (.nil next)
              hit := hstop
              before := by
                intro m hm
                have hm0 : m = 0 := by omega
                subst m
                simp only [ULogBootstrapExecution.run]
                intro hs
                rcases hs with hcycle | hhalt
                · exact postChoice_ne_cycleStart hpost
                    ((isConcreteCycleBoundary_running_iff q z).mp hcycle)
                · simp [ULogBootstrapExecution.concreteHalted] at hhalt }
          refine ⟨next, hit, rest, tail, ?_⟩
          simp [hit]
        · rcases postChoice_validStep_nonstop q z 0 next hpost hhead hstop with
            ⟨q', z', hnext, hpost'⟩
          subst next
          rcases ih q' z' acceptedZ hpost' tail with
            ⟨stop, hit, suffix, tail', hrest⟩
          let hit' : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteCycleStop (.running q z) stop :=
            { steps := hit.steps + 1
              valid := .cons (.running q z) (.running q' z') stop hit.steps
                hhead hit.valid
              hit := hit.hit
              before := by
                intro m hm
                cases m with
                | zero =>
                    simp only [ULogBootstrapExecution.run]
                    intro hs
                    rcases hs with hcycle | hhalt
                    · exact postChoice_ne_cycleStart hpost
                        ((isConcreteCycleBoundary_running_iff q z).mp hcycle)
                    · simp [ULogBootstrapExecution.concreteHalted] at hhalt
                | succ m =>
                    have hm' : m < hit.steps := by omega
                    simpa [ULogBootstrapExecution.run,
                      ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                      using hit.before m hm' }
          refine ⟨stop, hit', suffix, tail', ?_⟩
          simp [hit', hrest, List.replicate_succ]

theorem concreteMicroPath_halted_start_eq_finish
    {start finish : ULogBootstrapExecution.Result}
    {slots : List (Fin 2)}
    (path : ULogBootstrapExecution.ConcreteMicroPath start slots finish)
    (hhalt : ULogBootstrapExecution.concreteHalted start = true) :
    start = finish := by
  cases path with
  | nil r => rfl
  | cons start next finish slot rest hhead tail =>
      cases start <;>
        simp [ULogBootstrapExecution.concreteHalted,
          ULogBootstrapExecution.validStepAt] at hhalt hhead

theorem concreteMicroPath_slots_eq_nil_of_halted_start
    {start finish : ULogBootstrapExecution.Result}
    {slots : List (Fin 2)}
    (path : ULogBootstrapExecution.ConcreteMicroPath start slots finish)
    (hhalt : ULogBootstrapExecution.concreteHalted start = true) :
    slots = [] := by
  cases path with
  | nil r => rfl
  | cons start next finish slot rest hhead tail =>
      cases start <;>
        simp [ULogBootstrapExecution.concreteHalted,
          ULogBootstrapExecution.validStepAt] at hhalt hhead

def PreChoiceControl : ULogControl.State → Bool
  | .cycleStart | .clockSeek | .clockConsume | .clockReturn => true
  | _ => false

def PreTargetOk (q : ULogControl.State) : Bool :=
  decide (q = ULogControl.qReject) || decide (q = .chooseSlot) ||
    PreChoiceControl q

private def optionPreTargetOk
    (a : Option (FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)) :
    Bool := a.elim true (fun act => PreTargetOk act.target)

private theorem preChoice_target_closed_table :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      PreChoiceControl q = true →
      optionPreTargetOk (ULogProgram.program.rule q x slot) = true := by
  native_decide

theorem preChoice_target_closed
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hpre : PreChoiceControl q = true)
    (hrule : ULogProgram.program.rule q x slot = some act) :
    act.target = ULogControl.qReject ∨ act.target = .chooseSlot ∨
      PreChoiceControl act.target = true := by
  have h := preChoice_target_closed_table q x slot hpre
  simp [optionPreTargetOk, hrule, PreTargetOk] at h
  rcases h with (hr | hc) | hp
  · exact Or.inl hr
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hp)

theorem preChoice_ne_chooseSlot {q : ULogControl.State}
    (h : PreChoiceControl q = true) : q ≠ .chooseSlot := by
  intro hq
  subst q
  change false = true at h
  cases h

theorem preChoice_validStep_nonchoice_live
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (slot : Fin 2) (next : ULogBootstrapExecution.Result)
    (hpre : PreChoiceControl q = true)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) = some next)
    (hchoice : ¬ ULogBootstrapExecution.IsConcreteChoice next)
    {rest : List (Fin 2)}
    {acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (tail : ULogBootstrapExecution.ConcreteMicroPath next rest (.accepted acceptedZ)) :
    ∃ q' z', next = .running q' z' ∧ PreChoiceControl q' = true := by
  simp only [ULogBootstrapExecution.validStepAt] at hstep
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [hrule] at hstep
  | some act =>
      have hnext : next = ULogBootstrapExecution.oneStepAt slot (.running q z) := by
        have hs : some (ULogBootstrapExecution.oneStepAt slot (.running q z)) =
            some next := by simpa [hrule] using hstep
        exact (Option.some.inj hs).symm
      rcases preChoice_target_closed q z.focus slot act hpre hrule with
        hreject | hchoose | hpreTarget
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
            have hrejectNext : next = .rejected := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hreject, hqa]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hrejectNext]
              rfl)
            rw [hrejectNext] at heq
            cases heq
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hca : ULogControl.State.chooseSlot ≠ ULogControl.qAccept := by
              decide
            have hcr : ULogControl.State.chooseSlot ≠ ULogControl.qReject := by
              decide
            rw [hnext] at hchoice
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hchoose,
              hca, hcr, ULogBootstrapExecution.IsConcreteChoice] at hchoice
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hnotAccept : act.target ≠ ULogControl.qAccept := by
              intro h
              rw [h] at hpreTarget
              change false = true at hpreTarget
              cases hpreTarget
            have hnotReject : act.target ≠ ULogControl.qReject := by
              intro h
              rw [h] at hpreTarget
              change false = true at hpreTarget
              cases hpreTarget
            refine ⟨act.target, z', ?_, hpreTarget⟩
            rw [hnext]
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotAccept, hnotReject]

set_option maxRecDepth 100000 in
theorem isConcreteChoice_iff_exists (r : ULogBootstrapExecution.Result) :
    ULogBootstrapExecution.IsConcreteChoice r ↔
      ∃ z, r = .running .chooseSlot z := by
  cases r with
  | accepted z | rejected | stuck =>
      simp [ULogBootstrapExecution.IsConcreteChoice]
  | running q z =>
      cases q <;> simp [ULogBootstrapExecution.IsConcreteChoice]

/-- Parse the first actual binary choice from any accepting path beginning in
the four-state pre-choice clock phase. -/
theorem preChoice_path_firstChoice :
    ∀ (q : ULogControl.State)
      (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (slots : List (Fin 2))
      (acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape),
      PreChoiceControl q = true →
      ULogBootstrapExecution.ConcreteMicroPath (.running q z) slots
        (.accepted acceptedZ) →
      ∃ choiceZ,
        ∃ hit : ULogBootstrapExecution.FirstValidZeroHit
          ULogBootstrapExecution.IsConcreteChoice (.running q z)
            (.running .chooseSlot choiceZ),
        ∃ rest,
          ULogBootstrapExecution.ConcreteMicroPath (.running .chooseSlot choiceZ)
            rest (.accepted acceptedZ) ∧
          slots = List.replicate hit.steps (0 : Fin 2) ++ rest := by
  intro q z slots
  induction slots generalizing q z with
  | nil =>
      intro acceptedZ hpre path
      cases path
  | cons slot rest ih =>
      intro acceptedZ hpre path
      cases path with
      | cons start next finish slot rest hhead tail =>
        have hslotZero : slot = 0 := by
          have hq : q ≠ .chooseSlot := preChoice_ne_chooseSlot hpre
          have hcases : slot.1 = 0 ∨ slot.1 = 1 := by omega
          rcases hcases with hzero | hone
          · exact Fin.ext hzero
          · have hs : slot = 1 := Fin.ext hone
            subst slot
            have hnone := ULogBootstrapExecution.validStepAt_one_nonchoose q hq z
            rw [hnone] at hhead
            cases hhead
        subst slot
        by_cases hchoice : ULogBootstrapExecution.IsConcreteChoice next
        · rcases (isConcreteChoice_iff_exists next).mp hchoice with
            ⟨choiceZ, hnext⟩
          subst next
          let hit : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteChoice (.running q z)
                (.running .chooseSlot choiceZ) :=
            { steps := 1
              valid := .cons (.running q z) (.running .chooseSlot choiceZ)
                (.running .chooseSlot choiceZ) 0 hhead (.nil _)
              hit := by simp [ULogBootstrapExecution.IsConcreteChoice]
              before := by
                intro m hm
                have hm0 : m = 0 := by omega
                subst m
                simp only [ULogBootstrapExecution.run]
                intro hs
                rcases (isConcreteChoice_iff_exists (.running q z)).mp hs with
                  ⟨w, hw⟩
                have hq : q = .chooseSlot :=
                  ULogBootstrapExecution.Result.running.inj hw |>.1
                exact preChoice_ne_chooseSlot hpre hq }
          refine ⟨choiceZ, hit, rest, tail, ?_⟩
          simp [hit]
        · rcases preChoice_validStep_nonchoice_live q z 0 next hpre hhead
              hchoice tail with ⟨q', z', hnext, hpre'⟩
          subst next
          rcases ih q' z' acceptedZ hpre' tail with
            ⟨choiceZ, hit, suffix, tail', hrest⟩
          let hit' : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteChoice (.running q z)
                (.running .chooseSlot choiceZ) :=
            { steps := hit.steps + 1
              valid := .cons (.running q z) (.running q' z')
                (.running .chooseSlot choiceZ) hit.steps hhead hit.valid
              hit := hit.hit
              before := by
                intro m hm
                cases m with
                | zero =>
                    simp only [ULogBootstrapExecution.run]
                    intro hs
                    rcases (isConcreteChoice_iff_exists (.running q z)).mp hs with
                      ⟨w, hw⟩
                    have hq : q = .chooseSlot :=
                      ULogBootstrapExecution.Result.running.inj hw |>.1
                    exact preChoice_ne_chooseSlot hpre hq
                | succ m =>
                    have hm' : m < hit.steps := by omega
                    simpa [ULogBootstrapExecution.run,
                      ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                      using hit.before m hm' }
          refine ⟨choiceZ, hit', suffix, tail', ?_⟩
          simp [hit', hrest, List.replicate_succ]

theorem choose_validStep_nonstop_postChoice
    (choiceZ : MStarParserExecution.Zipper ULogProgram.Tape)
    (slot : Fin 2) (branch : ULogBootstrapExecution.Result)
    (hselected : ULogBootstrapExecution.validStepAt slot
      (.running .chooseSlot choiceZ) = some branch)
    (hstop : ¬ ULogBootstrapExecution.IsConcreteCycleStop branch) :
    ∃ q z, branch = .running q z ∧ PostChoiceControl q = true := by
  simp only [ULogBootstrapExecution.validStepAt] at hselected
  cases hrule : ULogProgram.program.rule .chooseSlot choiceZ.focus slot with
  | none => simp [hrule] at hselected
  | some act =>
      have hbranch : branch = ULogBootstrapExecution.oneStepAt slot
          (.running .chooseSlot choiceZ) := by
        have hs : some (ULogBootstrapExecution.oneStepAt slot
            (.running .chooseSlot choiceZ)) = some branch := by
          simpa [hrule] using hselected
        exact (Option.some.inj hs).symm
      rcases chooseSlot_target_postChoice_or_terminal choiceZ.focus slot act
          hrule with haccept | hreject | hpost
      · rw [hbranch] at hstop
        cases happly : MStarParserExecution.applyAction choiceZ act <;>
          simp [ULogBootstrapExecution.oneStepAt, hrule, happly, haccept,
            ULogBootstrapExecution.IsConcreteCycleStop,
            ULogBootstrapExecution.concreteHalted] at hstop
      · rw [hbranch] at hstop
        cases happly : MStarParserExecution.applyAction choiceZ act with
        | none =>
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
        | some z =>
            have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hreject, hqa,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
      · cases happly : MStarParserExecution.applyAction choiceZ act with
        | none =>
            rw [hbranch] at hstop
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              ULogBootstrapExecution.IsConcreteCycleStop,
              ULogBootstrapExecution.concreteHalted] at hstop
        | some z =>
            have hnotAccept : act.target ≠ ULogControl.qAccept := by
              intro h
              rw [h] at hpost
              change false = true at hpost
              cases hpost
            have hnotReject : act.target ≠ ULogControl.qReject := by
              intro h
              rw [h] at hpost
              change false = true at hpost
              cases hpost
            refine ⟨act.target, z, ?_, hpost⟩
            rw [hbranch]
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotAccept, hnotReject]

theorem selectedPath_firstCycleStop
    (choiceZ : MStarParserExecution.Zipper ULogProgram.Tape)
    (slot : Fin 2) (branch : ULogBootstrapExecution.Result)
    {slots : List (Fin 2)}
    {acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (hselected : ULogBootstrapExecution.validStepAt slot
      (.running .chooseSlot choiceZ) = some branch)
    (path : ULogBootstrapExecution.ConcreteMicroPath branch slots
      (.accepted acceptedZ)) :
    ∃ stop,
      ∃ hit : ULogBootstrapExecution.FirstValidZeroHit
        ULogBootstrapExecution.IsConcreteCycleStop branch stop,
      ∃ rest,
        ULogBootstrapExecution.ConcreteMicroPath stop rest (.accepted acceptedZ) ∧
        slots = List.replicate hit.steps (0 : Fin 2) ++ rest := by
  by_cases hstop : ULogBootstrapExecution.IsConcreteCycleStop branch
  · let hit : ULogBootstrapExecution.FirstValidZeroHit
        ULogBootstrapExecution.IsConcreteCycleStop branch branch :=
      { steps := 0
        valid := .nil branch
        hit := hstop
        before := by simp }
    exact ⟨branch, hit, slots, path, by simp [hit]⟩
  · rcases choose_validStep_nonstop_postChoice choiceZ slot branch hselected
        hstop with ⟨q, z, hbranch, hpost⟩
    subst branch
    exact postChoice_path_firstStop q z slots acceptedZ hpost path

def boolOfSlot (slot : Fin 2) : Bool := decide (slot = 1)

@[simp] theorem slotIndex_boolOfSlot (slot : Fin 2) :
    ULogBytecode.slotIndex (boolOfSlot slot) = slot := by
  have hcases : slot.1 = 0 ∨ slot.1 = 1 := by omega
  rcases hcases with hzero | hone
  · have hs : slot = 0 := Fin.ext hzero
    subst slot
    rfl
  · have hs : slot = 1 := Fin.ext hone
    subst slot
    rfl

/-- Purely operational junk completeness for the ULog cycle grammar: every
accepting micro-path from a `cycleStart` configuration decomposes into an
exact first-hit slot word. -/
theorem cycleStartMicroPath_to_exactConcreteSlotRun :
    ∀ (physicalSlots : List (Fin 2))
      (startZ acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape),
      ULogBootstrapExecution.ConcreteMicroPath (.running .cycleStart startZ)
        physicalSlots (.accepted acceptedZ) →
      ∃ word : List Bool,
        ULogBootstrapExecution.ExactConcreteSlotRun
          (.running .cycleStart startZ) word (.accepted acceptedZ) ∧
        word.length ≤ physicalSlots.length := by
  intro physicalSlots
  induction hn : physicalSlots.length using Nat.strong_induction_on
      generalizing physicalSlots with
  | h n ih =>
      intro startZ acceptedZ path
      rcases preChoice_path_firstChoice .cycleStart startZ physicalSlots
          acceptedZ rfl path with
        ⟨choiceZ, choiceHit, choiceRest, choicePath, hphysical⟩
      cases choicePath with
      | cons choice branch finish selectedSlot afterSelected hselected selectedTail =>
          let selected : Bool := boolOfSlot selectedSlot
          have hselected' : ULogBootstrapExecution.validStepAt
              (ULogBytecode.slotIndex selected) (.running .chooseSlot choiceZ) =
              some branch := by
            simpa [selected] using hselected
          rcases selectedPath_firstCycleStop choiceZ selectedSlot branch
              hselected selectedTail with
            ⟨stop, stopHit, afterCycle, cycleTail, hselectedRest⟩
          let cycle : ULogBootstrapExecution.ExactConcreteCycle selected
              (.running .cycleStart startZ) stop :=
            { choice := .running .chooseSlot choiceZ
              branch := branch
              choicePrefix := choiceHit
              selected := hselected'
              cycleSuffix := stopHit }
          cases hstop : stop with
          | accepted z =>
              have hterminal : stop = .accepted acceptedZ :=
                concreteMicroPath_halted_start_eq_finish cycleTail (by
                  rw [hstop]
                  rfl)
              have hz : z = acceptedZ := by
                rw [hstop] at hterminal
                exact ULogBootstrapExecution.Result.accepted.inj hterminal
              subst z
              have htailSlots : afterCycle = [] :=
                concreteMicroPath_slots_eq_nil_of_halted_start cycleTail (by
                  rw [hterminal]
                  rfl)
              subst afterCycle
              refine ⟨[selected], ?_, ?_⟩
              · exact .cons (.running .cycleStart startZ) (.accepted acceptedZ)
                  (.accepted acceptedZ) selected [] (by simpa [cycle, hstop] using cycle)
                  (.nil (.accepted acceptedZ))
              · have hp := congrArg List.length hphysical
                have hs := congrArg List.length hselectedRest
                simp at hp hs ⊢
                omega
          | rejected =>
              have heq := concreteMicroPath_halted_start_eq_finish cycleTail (by
                rw [hstop]
                rfl)
              rw [hstop] at heq
              cases heq
          | stuck =>
              have heq := concreteMicroPath_halted_start_eq_finish cycleTail (by
                rw [hstop]
                rfl)
              rw [hstop] at heq
              cases heq
          | running q z =>
              have hboundary : q = .cycleStart := by
                have hhit := stopHit.hit
                rw [hstop] at hhit
                rcases hhit with hcycle | hhalt
                · exact (isConcreteCycleBoundary_running_iff q z).mp hcycle
                · simp [ULogBootstrapExecution.concreteHalted] at hhalt
              subst q
              have hlt : afterCycle.length < physicalSlots.length := by
                have hp := congrArg List.length hphysical
                have hs := congrArg List.length hselectedRest
                simp at hp hs
                omega
              have hltN : afterCycle.length < n := by
                rw [← hn]
                exact hlt
              have hlen : afterCycle.length = afterCycle.length := rfl
              have cycleTail' : ULogBootstrapExecution.ConcreteMicroPath
                  (.running .cycleStart z) afterCycle (.accepted acceptedZ) := by
                simpa [hstop] using cycleTail
              rcases ih afterCycle.length hltN afterCycle hlen z acceptedZ
                  cycleTail' with
                ⟨word, tailRun, hwordLen⟩
              refine ⟨selected :: word, ?_, ?_⟩
              · exact .cons (.running .cycleStart startZ)
                  (.running .cycleStart z) (.accepted acceptedZ)
                  selected word (by simpa [cycle, hstop] using cycle) tailRun
              · have hp := congrArg List.length hphysical
                have hs := congrArg List.length hselectedRest
                simp at hp hs ⊢
                omega

/-- The preceding grammar theorem packaged in the raw accepting-trace
predicate used by the semantic/raw equivalence. -/
theorem cycleStartMicroPath_to_exactConcreteAcceptingTrace
    {physicalSlots : List (Fin 2)}
    {startZ acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (path : ULogBootstrapExecution.ConcreteMicroPath (.running .cycleStart startZ)
      physicalSlots (.accepted acceptedZ)) :
    ∃ word : List Bool,
      ULogBootstrapExecution.ExactConcreteAcceptingSlotTrace
        (.running .cycleStart startZ) word ∧
      word.length ≤ physicalSlots.length := by
  rcases cycleStartMicroPath_to_exactConcreteSlotRun physicalSlots startZ
      acceptedZ path with ⟨word, run, hlen⟩
  exact ⟨word, ⟨.accepted acceptedZ, run, rfl⟩, hlen⟩

/-- End-to-end reflection of a chronological framed outer ULog suffix into
the raw exact accepting-word type.  This is the missing outer-to-finite
direction; its only quantitative input is the literal length of the supplied
outer history. -/
theorem outerHistory_from_framedCycleStart_to_exactConcreteWords
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (startZ : MStarParserExecution.Zipper ULogProgram.Tape)
    (hstart : start = anchoredFramedULogConfig .cycleStart origin
      leftExtra rightExtra startZ)
    (haccept : finish.state = .accept)
    (budget : ℕ) (hlength : arrows.length ≤ budget) :
    Nonempty (ULogBootstrapExecution.ExactConcreteAcceptingWords budget
      (.running .cycleStart startZ)) := by
  rcases outerHistory_from_framedSim_to_concreteMicroPath H .cycleStart origin
      leftExtra rightExtra guards startZ hstart haccept with
    ⟨physicalSlots, acceptedZ, micro, hphysicalLength⟩
  rcases cycleStartMicroPath_to_exactConcreteAcceptingTrace micro with
    ⟨slots, exactTrace, hslotLength⟩
  refine ⟨⟨slots, ?_, exactTrace⟩⟩
  exact hslotLength.trans (hphysicalLength.trans hlength)

/-! ## Operational splitting of the deterministic bootstrap

The raw cycle grammar starts at `cycleStart`, whereas a physical copier
hands control to `qStart`.  The following finite predicate describes exactly
the controls which can occur before the first cycle boundary.  Its closure is
checked against the literal rule table; the subsequent theorem then splits
one *actual* accepting micro-history at its first `cycleStart` occurrence.
-/

def BootstrapControl : ULogControl.State → Bool
  | .start | .seekPayload | .translateCode _ | .translateReturn
  | .framePayloadLength | .payloadLengthStart | .framePayload _
  | .framePadding | .initializeState | .initStateCell _ | .initializeClock
  | .fieldSeek .programCount | .fieldSeek .source | .fieldSeek .read
  | .fieldSeek .write | .fieldSeek .target | .fieldSeek .payloadLength
  | .fieldReturn .programCount | .fieldReturn .source | .fieldReturn .read
  | .fieldReturn .write | .fieldReturn .target | .fieldReturn .payloadLength
  | .returnToPc _ | .countScan _ | .seekReturn _ _ | .payloadReturn _
  | .payloadCount _ | .payloadSeekReturn _ _ | .payloadRestore _ _
  | .skipRule | .skipMoveSecond _ | .seekSimHead | .readHead
  | .shiftRuntime (.initRight _) => true
  | _ => false

def BootstrapTargetOk (q : ULogControl.State) : Bool :=
  decide (q = ULogControl.qReject) || decide (q = .cycleStart) ||
    BootstrapControl q

private def optionBootstrapTargetOk
    (a : Option (FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)) :
    Bool := a.elim true (fun act => BootstrapTargetOk act.target)

private def bootstrapTargetClosedTest
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2) : Bool :=
  if BootstrapControl q then
    optionBootstrapTargetOk (ULogProgram.program.rule q x slot)
  else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem bootstrap_target_closed_table_test :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      bootstrapTargetClosedTest q x slot = true := by
  decide

private theorem bootstrap_target_closed_table :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      BootstrapControl q = true →
      optionBootstrapTargetOk (ULogProgram.program.rule q x slot) = true := by
  intro q x slot hboot
  have tested := bootstrap_target_closed_table_test q x slot
  simpa [bootstrapTargetClosedTest, hboot] using tested

theorem bootstrap_target_closed
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape)
    (hboot : BootstrapControl q = true)
    (hrule : ULogProgram.program.rule q x slot = some act) :
    act.target = ULogControl.qReject ∨ act.target = .cycleStart ∨
      BootstrapControl act.target = true := by
  have h := bootstrap_target_closed_table q x slot hboot
  simp [optionBootstrapTargetOk, hrule, BootstrapTargetOk] at h
  rcases h with (hr | hc) | hb
  · exact Or.inl hr
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hb)

theorem bootstrap_ne_chooseSlot {q : ULogControl.State}
    (h : BootstrapControl q = true) : q ≠ .chooseSlot := by
  intro hq
  subst q
  change false = true at h
  cases h

theorem bootstrap_ne_cycleStart {q : ULogControl.State}
    (h : BootstrapControl q = true) : q ≠ .cycleStart := by
  intro hq
  subst q
  change false = true at h
  cases h

theorem bootstrap_validStep_nonboundary_live
    (q : ULogControl.State)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (slot : Fin 2) (next : ULogBootstrapExecution.Result)
    (hboot : BootstrapControl q = true)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) = some next)
    (hboundary : ¬ ULogBootstrapExecution.IsConcreteCycleBoundary next)
    {rest : List (Fin 2)}
    {acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (tail : ULogBootstrapExecution.ConcreteMicroPath next rest (.accepted acceptedZ)) :
    ∃ q' z', next = .running q' z' ∧ BootstrapControl q' = true := by
  simp only [ULogBootstrapExecution.validStepAt] at hstep
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [hrule] at hstep
  | some act =>
      have hnext : next = ULogBootstrapExecution.oneStepAt slot (.running q z) := by
        have hs : some (ULogBootstrapExecution.oneStepAt slot (.running q z)) =
            some next := by simpa [hrule] using hstep
        exact (Option.some.inj hs).symm
      rcases bootstrap_target_closed q z.focus slot act hboot hrule with
        hreject | hcycle | hbootTarget
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hqa : ULogControl.qReject ≠ ULogControl.qAccept := by decide
            have hrejectNext : next = .rejected := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hreject,
                hqa]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hrejectNext]
              rfl)
            rw [hrejectNext] at heq
            cases heq
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hca : ULogControl.State.cycleStart ≠ ULogControl.qAccept := by
              decide
            have hcr : ULogControl.State.cycleStart ≠ ULogControl.qReject := by
              decide
            apply False.elim
            apply hboundary
            rw [hnext]
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly, hcycle,
              hca, hcr, ULogBootstrapExecution.IsConcreteCycleBoundary]
      · cases happly : MStarParserExecution.applyAction z act with
        | none =>
            have hstuck : next = .stuck := by
              rw [hnext]
              simp [ULogBootstrapExecution.oneStepAt, hrule, happly]
            have heq := concreteMicroPath_halted_start_eq_finish tail (by
              rw [hstuck]
              rfl)
            rw [hstuck] at heq
            cases heq
        | some z' =>
            have hnotAccept : act.target ≠ ULogControl.qAccept := by
              intro h
              rw [h] at hbootTarget
              change false = true at hbootTarget
              cases hbootTarget
            have hnotReject : act.target ≠ ULogControl.qReject := by
              intro h
              rw [h] at hbootTarget
              change false = true at hbootTarget
              cases hbootTarget
            refine ⟨act.target, z', ?_, hbootTarget⟩
            rw [hnext]
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotAccept, hnotReject]

set_option maxRecDepth 100000 in
theorem isConcreteCycleBoundary_iff_exists
    (r : ULogBootstrapExecution.Result) :
    ULogBootstrapExecution.IsConcreteCycleBoundary r ↔
      ∃ z, r = .running .cycleStart z := by
  cases r with
  | accepted z | rejected | stuck =>
      simp [ULogBootstrapExecution.IsConcreteCycleBoundary]
  | running q z =>
      cases q <;> simp [ULogBootstrapExecution.IsConcreteCycleBoundary]

/-- Split an actual accepting path from a bootstrap control at the first
literal `cycleStart`.  The prefix contains only occupied slot-zero edges and
the returned suffix is the very same chronological history. -/
theorem bootstrap_path_firstCycleStart :
    ∀ (q : ULogControl.State)
      (z : MStarParserExecution.Zipper ULogProgram.Tape)
      (slots : List (Fin 2))
      (acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape),
      BootstrapControl q = true →
      ULogBootstrapExecution.ConcreteMicroPath (.running q z) slots
        (.accepted acceptedZ) →
      ∃ cycleZ,
        ∃ hit : ULogBootstrapExecution.FirstValidZeroHit
          ULogBootstrapExecution.IsConcreteCycleBoundary (.running q z)
            (.running .cycleStart cycleZ),
        ∃ rest,
          ULogBootstrapExecution.ConcreteMicroPath
            (.running .cycleStart cycleZ) rest (.accepted acceptedZ) ∧
          slots = List.replicate hit.steps (0 : Fin 2) ++ rest := by
  intro q z slots
  induction slots generalizing q z with
  | nil =>
      intro acceptedZ hboot path
      cases path
  | cons slot rest ih =>
      intro acceptedZ hboot path
      cases path with
      | cons start next finish slot rest hhead tail =>
        have hslotZero : slot = 0 := by
          have hq : q ≠ .chooseSlot := bootstrap_ne_chooseSlot hboot
          have hcases : slot.1 = 0 ∨ slot.1 = 1 := by omega
          rcases hcases with hzero | hone
          · exact Fin.ext hzero
          · have hs : slot = 1 := Fin.ext hone
            subst slot
            have hnone := ULogBootstrapExecution.validStepAt_one_nonchoose q hq z
            rw [hnone] at hhead
            cases hhead
        subst slot
        by_cases hboundary :
            ULogBootstrapExecution.IsConcreteCycleBoundary next
        · rcases (isConcreteCycleBoundary_iff_exists next).mp hboundary with
            ⟨cycleZ, hnext⟩
          subst next
          let hit : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteCycleBoundary (.running q z)
                (.running .cycleStart cycleZ) :=
            { steps := 1
              valid := .cons (.running q z) (.running .cycleStart cycleZ)
                (.running .cycleStart cycleZ) 0 hhead (.nil _)
              hit := by
                simp [ULogBootstrapExecution.IsConcreteCycleBoundary]
              before := by
                intro m hm
                have hm0 : m = 0 := by omega
                subst m
                simp only [ULogBootstrapExecution.run]
                intro hs
                exact bootstrap_ne_cycleStart hboot
                  ((isConcreteCycleBoundary_running_iff q z).mp hs) }
          exact ⟨cycleZ, hit, rest, tail, by simp [hit]⟩
        · rcases bootstrap_validStep_nonboundary_live q z 0 next hboot hhead
              hboundary tail with ⟨q', z', hnext, hboot'⟩
          subst next
          rcases ih q' z' acceptedZ hboot' tail with
            ⟨cycleZ, hit, suffix, tail', hrest⟩
          let hit' : ULogBootstrapExecution.FirstValidZeroHit
              ULogBootstrapExecution.IsConcreteCycleBoundary (.running q z)
                (.running .cycleStart cycleZ) :=
            { steps := hit.steps + 1
              valid := .cons (.running q z) (.running q' z')
                (.running .cycleStart cycleZ) hit.steps hhead hit.valid
              hit := hit.hit
              before := by
                intro m hm
                cases m with
                | zero =>
                    simp only [ULogBootstrapExecution.run]
                    intro hs
                    exact bootstrap_ne_cycleStart hboot
                      ((isConcreteCycleBoundary_running_iff q z).mp hs)
                | succ m =>
                    have hm' : m < hit.steps := by omega
                    simpa [ULogBootstrapExecution.run,
                      ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead]
                      using hit.before m hm' }
          exact ⟨cycleZ, hit', suffix, tail', by
            simp [hit', hrest, List.replicate_succ]⟩

/-- End-to-end operational reflection from a guarded physical `qStart`
suffix.  The existential cycle zipper is not guessed: it is the first actual
cycle boundary in the supplied chronological history. -/
theorem outerHistory_from_framedQStart_to_exactConcreteWords
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (origin : Int) (leftExtra rightExtra : List OuterTape)
    (guards : FramingGuards leftExtra rightExtra)
    (startZ : MStarParserExecution.Zipper ULogProgram.Tape)
    (hstart : start = anchoredFramedULogConfig ULogControl.qStart origin
      leftExtra rightExtra startZ)
    (haccept : finish.state = .accept)
    (budget : ℕ) (hlength : arrows.length ≤ budget) :
    ∃ cycleZ,
      Nonempty (ULogBootstrapExecution.ExactConcreteAcceptingWords budget
        (.running .cycleStart cycleZ)) := by
  rcases outerHistory_from_framedSim_to_concreteMicroPath H ULogControl.qStart
      origin leftExtra rightExtra guards startZ hstart haccept with
    ⟨physicalSlots, acceptedZ, micro, hphysicalLength⟩
  rcases bootstrap_path_firstCycleStart ULogControl.qStart startZ physicalSlots
      acceptedZ rfl micro with
    ⟨cycleZ, hit, rest, suffix, hphysical⟩
  rcases cycleStartMicroPath_to_exactConcreteAcceptingTrace suffix with
    ⟨word, exactTrace, hwordLength⟩
  refine ⟨cycleZ, ⟨⟨word, ?_, exactTrace⟩⟩⟩
  have hrestLength : rest.length ≤ physicalSlots.length := by
    have h := congrArg List.length hphysical
    simp at h
    omega
  exact hwordLength.trans
    (hrestLength.trans (hphysicalLength.trans hlength))

/-! ## Preserving the actual FullFrame suffix

The older parser/copier reflection returned only a finite reachability fact.
The following splitters retain the exact remaining physical history. -/

noncomputable def windowedHistoryToOuterHistory
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h') :
    PakOuterULogTraceBridge.OuterArrowHistory c as e := by
  induction H with
  | nil c h => exact .nil c
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      exact .cons c d e a as hstep ih

/-- The trace-derived history retains its exact chronological length.  This
strengthens the older existential constructor only at the call site where a
FullFrame time budget is required. -/
noncomputable def historyOfTraceFromWithLength {n : ℕ}
    (T : PakOuterParserListExitReflection.WindowedOuterListTrace n)
    (k : ℕ) (hk : k ≤ n) :
    ∃ as : List OuterArrow,
      Nonempty (PakOuterParserListExitReflection.WindowedOuterHistory n
        (T.configs.get ⟨k, by
          simpa [T.configs_length] using Nat.lt_succ_of_le hk⟩)
        (T.heads.get ⟨k, by
          simpa [T.heads_length] using Nat.lt_succ_of_le hk⟩)
        as
        (T.configs.get ⟨n, by
          simpa [T.configs_length] using Nat.lt_succ_self n⟩)
        (T.heads.get ⟨n, by
          simpa [T.heads_length] using Nat.lt_succ_self n⟩)) ∧
      as.length = n - k := by
  by_cases hlast : k = n
  · subst k
    exact ⟨[], ⟨PakOuterParserListExitReflection.WindowedOuterHistory.nil _ _⟩,
      by simp⟩
  · have hklt : k < n := lt_of_le_of_ne hk hlast
    rcases historyOfTraceFromWithLength T (k + 1) (by omega) with
      ⟨as, ⟨tail⟩, hlength⟩
    let i : Fin n := ⟨k, hklt⟩
    refine ⟨T.arrows.get ⟨k, by simpa [T.arrows_length] using hklt⟩ :: as,
      ⟨PakOuterParserListExitReflection.WindowedOuterHistory.cons
        (T.arrows.get ⟨k, by simpa [T.arrows_length] using hklt⟩)
        ?_ ?_ ?_ ?_ ?_ tail⟩, ?_⟩
    · simpa [i] using T.step i
    · simpa [i] using T.head_eq ⟨k, by omega⟩
    · simpa [i] using T.head_eq ⟨k + 1, by omega⟩
    · simpa [i] using T.hash_outside ⟨k, by omega⟩
    · simpa [i] using T.hash_outside ⟨k + 1, by omega⟩
    · simp only [List.length_cons]
      omega
termination_by n - k
decreasing_by omega

theorem slotOneWindowedHistoryWithLength {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ as : List OuterArrow,
      Nonempty (PakOuterParserListExitReflection.WindowedOuterHistory n
        ((PakOuterParserListExitReflection.slotOneListTrace F).configs.get
          ⟨1, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).configs_length]
            have := F.1.width_pos
            omega⟩)
        ((PakOuterParserListExitReflection.slotOneListTrace F).heads.get
          ⟨1, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).heads_length]
            have := F.1.width_pos
            omega⟩)
        as
        ((PakOuterParserListExitReflection.slotOneListTrace F).configs.get
          ⟨n, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).configs_length]
            omega⟩)
        ((PakOuterParserListExitReflection.slotOneListTrace F).heads.get
          ⟨n, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).heads_length]
            omega⟩)) ∧
      as.length = n - 1 ∧
      ((PakOuterParserListExitReflection.slotOneListTrace F).configs.get
        ⟨n, by
          rw [(PakOuterParserListExitReflection.slotOneListTrace F).configs_length]
          omega⟩).state = .accept := by
  rcases historyOfTraceFromWithLength
      (PakOuterParserListExitReflection.slotOneListTrace F) 1 (by
        have := F.1.width_pos
        omega) with ⟨as, has, hlength⟩
  exact ⟨as, has, hlength,
    by simpa using
      (PakOuterParserListExitReflection.slotOneListTrace F).final_accept⟩

/-- The apparently arbitrary core block before the recovered scanner
terminator is in fact all work.  The side-value proof already establishes
the high/mid scanner invariant on this interval; retaining the final field of
`legalScan_midHigh_to_core` identifies each emitted physical core letter. -/
theorem slotOne_remaining_eq_work_replicate {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash) :
    remaining = List.replicate remaining.length MStarConcreteAlphabet.work := by
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  · intro a ha
    rcases List.mem_iff_getElem.mp ha with ⟨j, hj, hja⟩
    let L := (ConcretePakSide.encodedWord x).length
    let k := L + 3 + j
    have ht := PakSlotOneSideValueReflection.terminalIndex_lt
      F x remaining hashes hshape
    have hkTerminal : k <
        PakSlotOneSideValueReflection.terminalIndex x remaining := by
      simp [k, L, PakSlotOneSideValueReflection.terminalIndex]
      omega
    have hkWindow : k < n - 1 := hkTerminal.trans ht
    have hsource :=
      (PakSlotOneSideValueReflection.core_interval_false_midHigh
        F x remaining hashes hshape (2 + j) (by
          simp [L, PakSlotOneSideValueReflection.terminalIndex]
          omega)).2
    let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
    have hsourceIndex :
        (⟨(ConcretePakSide.encodedWord x).length + (2 + j) + 1, by
          have := hkWindow
          dsimp [k, L] at this
          omega⟩ : Fin (n + 1)) = ⟨k, by omega⟩ := by
      apply Fin.ext
      dsimp [k, L]
      omega
    have hsource' :
        (P.states ⟨k, by omega⟩).phase = .mid ∧
          (P.states ⟨k, by omega⟩).mode = .high := by
      change (P.states
        ⟨(ConcretePakSide.encodedWord x).length + (2 + j) + 1, by
          have := hkWindow
          dsimp [k, L] at this
          omega⟩).phase = .mid ∧
        (P.states
          ⟨(ConcretePakSide.encodedWord x).length + (2 + j) + 1, by
            have := hkWindow
            dsimp [k, L] at this
            omega⟩).mode = .high at hsource
      rw [hsourceIndex] at hsource
      exact hsource
    have hcell :
        ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD k
            (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero) =
          MStarOuterProgram.Tape.core a := by
      let pre := MStarParserExecution.inputCells MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work]
      have hpreLength : pre.length = L + 3 := by
        simp [pre, L, MStarParserExecution.inputCells]
      let afterPre := remaining.map MStarOuterProgram.Tape.core ++
        MStarCopierMicrocode.rightEnd ::
          List.replicate hashes MStarOuterProgram.Tape.hash
      have hdecomp :
          MStarParserExecution.inputCells MStarConcreteAlphabet.zero
                MStarConcreteAlphabet.one MStarConcreteAlphabet.work
                (ConcretePakSide.encodedWord x) ++
              [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
                MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
              remaining.map MStarOuterProgram.Tape.core ++
              [MStarCopierMicrocode.rightEnd] ++
              List.replicate hashes MStarOuterProgram.Tape.hash =
            pre ++ afterPre := by
        simp [pre, afterPre, List.append_assoc]
      rw [hshape, hdecomp, List.getD_append_right]
      · have hsub : k - pre.length = j := by
          dsimp [k]
          rw [hpreLength]
          omega
        change afterPre.getD (k - pre.length)
            (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero) = _
        rw [hsub]
        unfold afterPre
        rw [List.getD_append]
        · rw [List.getD_map]
          rw [List.getD_eq_getElem remaining MStarConcreteAlphabet.zero hj]
          exact congrArg MStarOuterProgram.Tape.core hja
        · simpa using hj
      · rw [hpreLength]
        dsimp [k]
        omega
    have hletter : PakScannerRawShape.scannerTapeLetter
        (P.states ⟨k + 1, by omega⟩).centre =
          MStarOuterProgram.Tape.core a := by
      calc
        _ = ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
              (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD k
                (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero) :=
          (PakSlotOneSideIdentification.slotOneTrimmedZipper_getD_eq_scannerTapeLetter
            F k hkWindow).symm
        _ = _ := hcell
    have hstage :=
      PakSlotOneSideIdentification.scannerTapeLetter_core_forces_stage_core
        _ a hletter
    have hlegal := P.legal (⟨k, by omega⟩ : Fin n)
    have hwork :=
      (PakSlotOneSideIdentification.legalScan_midHigh_to_core
        (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
        (n.testBit k) hsource'.1 hsource'.2 (by simpa using hlegal) hstage).2.2.2
    exact MStarOuterProgram.Tape.core.inj (hletter.symm.trans hwork)

theorem slotOne_remaining_tail_eq_slackCopierReserve_of_le {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hreserve : PakSideScannerRow.copierWorkCount x.length ≤ remaining.length) :
    remaining.map MStarOuterProgram.Tape.core ++
        MStarCopierMicrocode.rightEnd ::
          List.replicate hashes MStarOuterProgram.Tape.hash =
      PakCopierSlackExecution.slackCopierReserve x.length
        (remaining.length - PakSideScannerRow.copierWorkCount x.length)
        (List.replicate hashes MStarOuterProgram.Tape.hash) := by
  have hremaining := slotOne_remaining_eq_work_replicate
    F x remaining hashes hshape
  rw [hremaining,
    PakCopierSlackExecution.slackCopierReserve_eq_work_rightEnd]
  simp only [List.map_replicate, List.length_replicate]
  rw [Nat.add_sub_of_le hreserve]

/-- Once the sole numerical reserve lower bound is supplied, the copier
endpoint extracted from the actual slot-one frame is exactly the parametric
slack endpoint.  This theorem keeps the physical seed configuration in the
output so it can be matched with the chronological FullFrame suffix. -/
theorem slotOne_successfulCopier_eq_slackOutput_of_le {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hreserve : PakSideScannerRow.copierWorkCount x.length ≤ remaining.length) :
    ∃ (copyConfig seedConfig : OuterConfig) (copyHead seedHead : Fin n)
      (fuel : ℕ) (out : MStarParserExecution.Zipper OuterTape),
      PakOuterParserReflection.windowZipper n seedConfig seedHead =
        PakCopierSlackExecution.sideSlackCopierSeedZipper x
          (remaining.length - PakSideScannerRow.copierWorkCount x.length)
          (List.replicate hashes MStarOuterProgram.Tape.hash) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell
          (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out ∧
      out = PakCopierSlackExecution.sideSlackGroupZipper x
        (remaining.length - PakSideScannerRow.copierWorkCount x.length)
        (List.replicate hashes MStarOuterProgram.Tape.hash) := by
  let rawTail : List OuterTape :=
    [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
      remaining.map MStarOuterProgram.Tape.core ++
        MStarCopierMicrocode.rightEnd ::
          List.replicate hashes MStarOuterProgram.Tape.hash
  have hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x) ++ rawTail := by
    simpa [rawTail, List.append_assoc] using hshape
  rcases PakSlotOneCopierRightEndReflection.slotOne_copyStart_origin
      F x rawTail hprefix with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hcopy, hseedApply, hseedState, hrun⟩
  let slack := remaining.length - PakSideScannerRow.copierWorkCount x.length
  have htail := slotOne_remaining_tail_eq_slackCopierReserve_of_le
    F x remaining hashes hshape hreserve
  have hrawTail : rawTail =
      [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
        MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
        PakCopierSlackExecution.slackCopierReserve x.length slack
          (List.replicate hashes MStarOuterProgram.Tape.hash) := by
    dsimp [rawTail, slack]
    rw [htail]
  have hseed : PakOuterParserReflection.windowZipper n seedConfig seedHead =
      PakCopierSlackExecution.sideSlackCopierSeedZipper x slack
        (List.replicate hashes MStarOuterProgram.Tape.hash) := by
    rw [hcopy] at hseedApply
    apply Option.some.inj
    simpa [hrawTail, PakSlotOneParserDecode.appendLeftHash,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
      PakCopierSlackExecution.sideSlackCopierSeedZipper,
      MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      List.append_assoc] using hseedApply.symm
  have hout := PakCopierSlackExecution.successful_sideSlackCopier_groupReady_eq
    x slack fuel (List.replicate hashes MStarOuterProgram.Tape.hash) out (by
      rw [← hseed]
      exact hrun)
  exact ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
    hseed, hrun, hout⟩

/-- The actual accepting FullFrame supplies enough work for the unchanged
copier's true minimum, even though it need not supply the larger canonical
reserve. -/
theorem slotOne_remaining_ge_minimumSuccessful {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash) :
    PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤
      remaining.length := by
  let rawTail : List OuterTape :=
    [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
      remaining.map MStarOuterProgram.Tape.core ++
        MStarCopierMicrocode.rightEnd ::
          List.replicate hashes MStarOuterProgram.Tape.hash
  have hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x) ++ rawTail := by
    simpa [rawTail, List.append_assoc] using hshape
  rcases PakSlotOneCopierRightEndReflection.slotOne_copyStart_origin
      F x rawTail hprefix with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hcopy, hseedApply, hseedState, hrun⟩
  have hremaining := slotOne_remaining_eq_work_replicate
    F x remaining hashes hshape
  have hrawTail : rawTail =
      [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
        MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
        List.replicate remaining.length
            (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd ::
            List.replicate hashes MStarOuterProgram.Tape.hash := by
    dsimp [rawTail]
    rw [hremaining]
    simp only [List.map_replicate, List.length_replicate]
  have hseed :
      (MStarCopierExecution.Result.running .seedCell
        (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
      PakCopierReserveLowerBound.rawCopierSeed x remaining.length
        (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])
        (List.replicate hashes MStarOuterProgram.Tape.hash) := by
    unfold PakCopierReserveLowerBound.rawCopierSeed
    congr 1
    rw [hcopy] at hseedApply
    apply Option.some.inj
    simpa [hrawTail, PakSlotOneParserDecode.appendLeftHash,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
      PakCopierReserveLowerBound.rawCopierSeed,
      MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      List.append_assoc] using hseedApply.symm
  apply PakCopierReserveLowerBound.successful_rawCopier_forces_minimum x
    remaining.length (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])
    (List.replicate hashes MStarOuterProgram.Tape.hash)
  exact ⟨fuel, out, by rw [← hseed]; exact hrun⟩

theorem copierHistory_to_groupReady_tail
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h')
    (hfinal : e.state = .accept)
    (q : MStarCopierMicrocode.CopierState)
    (hstate : c.state = (.parser (.inr q) : MStarULogAssembly.State)) :
    ∃ (d : OuterConfig) (hd : Fin n) (tailArrows : List OuterArrow)
      (tailHead : Fin n),
      Nonempty (PakOuterParserListExitReflection.WindowedOuterHistory n d hd
        tailArrows e tailHead) ∧
      tailArrows.length ≤ as.length ∧
      ∃ fuel out,
        MStarCopierExecution.run fuel
          (.running q (PakOuterParserReflection.windowZipper n c h)) =
            .groupReady out ∧
        out = PakOuterParserReflection.windowZipper n d hd ∧
        d.state = (.sim ULogControl.qStart : MStarULogAssembly.State) := by
  induction H generalizing q with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      rcases PakSlotOneCopierRightEndReflection.outerStep_from_copier_target_classification
          q c d a hstate hstep with
        ⟨q', hstate'⟩ | ⟨u, hsim⟩ | hreject
      · rcases ih hfinal q' hstate' with
          ⟨g, hg, tailArrows, tailHead, tailH, hlength, fuel, out,
            hrun, hout, hgstate⟩
        have hone := PakSlotOneCopierRightEndReflection.copier_to_copier_oneStep_reflection
          n q q' c d a h h' hstate hstate' hhead hhead' hhash hhash' hstep
        refine ⟨g, hg, tailArrows, tailHead, tailH,
          hlength.trans (by simp), fuel + 1, out, ?_, hout, hgstate⟩
        rw [MStarCopierExecution.run_succ, hone]
        exact hrun
      · have hone := PakSlotOneCopierRightEndReflection.copier_to_sim_oneStep_reflection
          n q c d a h h' hstate ⟨u, hsim⟩ hhead hhead' hhash hhash' hstep
        have hu : u = ULogControl.qStart := by
          rcases PakSlotOneCopierRightEndReflection.copierUnitAction_of_outerStep
              q c d a hstate hstep with ⟨ua, huRule, hslot, haction, hafter⟩
          have ht := congrArg (fun cfg : OuterConfig => cfg.state) hafter
          have htarget :
              (PakParserOuterBridge.changeUnitCopierAction
                MStarULogAssembly.data.uStart ua).target =
                  (MStarOuterProgram.State.sim u) := by
            exact ht.symm.trans hsim
          change PakParserOuterBridge.changeUnitCopierState
              MStarULogAssembly.data.uStart ua.target =
            MStarOuterProgram.State.sim u at htarget
          cases hua : ua.target with
          | sim unit =>
              rw [hua] at htarget
              have heq : ULogControl.qStart = u :=
                MStarOuterProgram.State.sim.inj htarget
              exact heq.symm
          | start =>
              rw [hua] at htarget
              cases htarget
          | accept =>
              rw [hua] at htarget
              cases htarget
          | reject =>
              rw [hua] at htarget
              cases htarget
          | parser p =>
              rw [hua] at htarget
              cases htarget
        subst u
        refine ⟨d, h', as, h'', ⟨tail⟩, by simp, 1,
          PakOuterParserReflection.windowZipper n d h', ?_, rfl, hsim⟩
        simpa using hone
      · have hend := tail.reject_suffix hreject
        rw [hfinal] at hend
        cases hend

theorem parserHistory_to_groupReady_tail
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h')
    (hfinal : e.state = .accept)
    (p : MStarParserMicrocode.ParserState)
    (hstate : c.state = (.parser (.inl p) : MStarULogAssembly.State)) :
    ∃ (d : OuterConfig) (hd : Fin n) (tailArrows : List OuterArrow)
      (tailHead : Fin n),
      Nonempty (PakOuterParserListExitReflection.WindowedOuterHistory n d hd
        tailArrows e tailHead) ∧
      tailArrows.length ≤ as.length ∧
      ∃ copyConfig copyHead seedConfig seedHead fuel out,
        MStarParserExecution.Reaches MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (.running p (PakOuterParserReflection.windowZipper n c h))
          (.running MStarParserMicrocode.copyStart
            (PakOuterParserReflection.windowZipper n copyConfig copyHead)) ∧
        MStarParserExecution.applyAction
          (PakOuterParserReflection.windowZipper n copyConfig copyHead)
          (MStarCopierMicrocode.copyGo (UState := Unit)
            .markL .seedCell .right) =
          some (PakOuterParserReflection.windowZipper n seedConfig seedHead) ∧
        seedConfig.state = (.parser (.inr .seedCell) : MStarULogAssembly.State) ∧
        MStarCopierExecution.run fuel
          (.running .seedCell
            (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
            .groupReady out ∧
        out = PakOuterParserReflection.windowZipper n d hd ∧
        d.state = (.sim ULogControl.qStart : MStarULogAssembly.State) := by
  induction H generalizing p with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        rcases PakSlotOneCopierRightEndReflection.copyStart_outer_target_classification
            c d a hstate hstep with ⟨hseed, hseedAction⟩ | hreject
        · rcases copierHistory_to_groupReady_tail tail hfinal .seedCell hseed with
            ⟨g, hg, tailArrows, tailHead, tailH, hlength, fuel, out,
              hrun, hout, hgstate⟩
          have hseedApply :=
            PakSlotOneCopierRightEndReflection.copyStart_to_seed_window_applyAction
              n c d a h h' hhead hhead' hhash hhash' hseedAction hstep
          exact ⟨g, hg, tailArrows, tailHead, tailH,
            hlength.trans (by simp),
            c, h, d, h', fuel, out,
            MStarParserExecution.reaches_refl _ _ _ _, hseedApply,
            hseed, hrun, hout, hgstate⟩
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

      · rcases PakOuterParserListExitReflection.history_noncopy_target_parser_or_reject
            p a hstep hstate hp with ⟨p', hstate'⟩ | hreject
        · rcases ih hfinal p' hstate' with
            ⟨g, hg, tailArrows, tailHead, tailH, hlength,
              copyConfig, copyHead, seedConfig, seedHead, fuel, out,
              hparser, hseedApply, hseed, hrun, hout, hgstate⟩
          have hone :=
            PakOuterParserReflection.noncopy_parser_oneStep_reflection
              n p p' c d a h h' hstate hstate' hp hhead hhead'
                hhash hhash' hstep
          refine ⟨g, hg, tailArrows, tailHead, tailH,
            hlength.trans (by simp),
            copyConfig, copyHead, seedConfig, seedHead, fuel, out, ?_,
            hseedApply, hseed, hrun, hout, hgstate⟩
          exact MStarParserExecution.reaches_trans
            MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
            MStarConcreteAlphabet.work
            (MStarParserExecution.reaches_of_oneStep
              MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
              MStarConcreteAlphabet.work hone) hparser
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

theorem slotOne_copyStartZipper_eq_of_reaches {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List OuterTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (ConcretePakSide.encodedWord x) ++ tail)
    (zfull : MStarParserExecution.Zipper OuterTape)
    (hparser : MStarParserExecution.Reaches MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTimeOneZipper F))
      (.running MStarParserMicrocode.copyStart zfull)) :
    zfull = PakSlotOneParserDecode.appendLeftHash
      (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) tail) := by
  rcases hparser with ⟨parserFuel, hparser⟩
  have hfull : PakSlotOneParserDecode.slotOneTimeOneZipper F =
      PakSlotOneParserDecode.appendLeftHash
        (PakSlotOneParserDecode.slotOneTrimmedZipper F) :=
    PakSlotOneParserDecode.slotOneTimeOneZipper_eq_appendLeftHash F
  have hparser' : MStarParserExecution.run MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work parserFuel
      (PakSlotOneParserDecode.appendLeftHashResult
        (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
          (PakSlotOneParserDecode.slotOneTrimmedZipper F))) =
      .running MStarParserMicrocode.copyStart zfull := by
    simpa [PakSlotOneParserDecode.appendLeftHashResult, hfull] using hparser
  rcases PakSlotOneCopierRightEndReflection.run_appendLeftHash_to_copyStart_reflect
      parserFuel
      (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTrimmedZipper F)) zfull hparser' with
    ⟨z, hzfull, hzrun⟩
  have hinitial :=
    PakSlotOneCopierRightEndReflection.trimmed_initial_eq_extendResultRight
      F x tail hprefix
  have hactual : MStarParserExecution.run MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work (parserFuel + 1)
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x)) tail) = .copyReady z := by
    rw [← hinitial, MStarParserExecution.run_add, hzrun]
    rfl
  rcases MStarConcreteAlphabet.reaches_parser_encodedWord_with_tail x tail with
    ⟨canonicalFuel, hcanonical⟩
  have hz : z = MStarParserExecution.extendRight
      (MStarConcreteAlphabet.finalZipper x.reverse) tail :=
    MStarParserExecution.copyReady_output_unique
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work _ (parserFuel + 1) canonicalFuel z
      (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) tail)
      hactual hcanonical
  rw [hzfull, hz]

def corePrefix : List OuterTape → List ULogProgram.Tape
  | .core x :: xs => x :: corePrefix xs
  | _ => []

def afterCorePrefix : List OuterTape → List OuterTape
  | .core _ :: xs => afterCorePrefix xs
  | xs => xs

theorem corePrefix_decomposition (xs : List OuterTape) :
    xs = (corePrefix xs).map (fun x => (.core x : OuterTape)) ++
      afterCorePrefix xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | core y =>
          simp only [corePrefix, afterCorePrefix, List.map_cons,
            List.cons_append]
          exact congrArg (List.cons (.core y)) ih
      | hash | markL | markR | scratch => rfl

theorem afterCorePrefix_nonCoreHead (xs : List OuterTape) :
    NonCoreHead (afterCorePrefix xs) := by
  induction xs with
  | nil => intro y; simp [afterCorePrefix]
  | cons x xs ih =>
      cases x with
      | core y => exact ih
      | hash | markL | markR | scratch <;>
          intro y <;> simp only [afterCorePrefix, NonCoreHead,
            List.head?_cons, ne_eq, Option.some.injEq] <;> intro h <;> cases h

def maximalRightCoreZipper (focus : ULogProgram.Tape)
    (right : List OuterTape) :
    MStarParserExecution.Zipper ULogProgram.Tape :=
  ⟨[], focus, corePrefix right⟩

theorem frame_maximalRightCoreZipper
    (left : List OuterTape) (focus : ULogProgram.Tape)
    (right : List OuterTape) :
    frameCoreZipper left (afterCorePrefix right)
      (maximalRightCoreZipper focus right) = ⟨left, .core focus, right⟩ := by
  apply MStarParserExecution.Zipper.ext
  · rfl
  · rfl
  · exact (corePrefix_decomposition right).symm

theorem simAcceptingHistory_focus_core
    {start finish : OuterConfig} {arrows : List OuterArrow}
    (H : PakOuterULogTraceBridge.OuterArrowHistory start arrows finish)
    (q : ULogControl.State)
    (hstate : start.state = (.sim q : MStarULogAssembly.State))
    (haccept : finish.state = .accept) :
    ∃ x : ULogProgram.Tape, start.tape start.head = .core x := by
  cases H with
  | nil c =>
      rw [hstate] at haccept
      cases haccept
  | cons c next finish a arrows hstep tail =>
      cases hx : start.tape start.head with
      | core x => exact ⟨x, rfl⟩
      | hash | markL | markR | scratch i =>
          exfalso
          apply no_outerStep_from_sim_noncore q start next a hstate
          · intro y hy
            rw [hx] at hy
            cases hy
          · exact hstep

theorem groupReadyTail_to_framedQStart
    {n : ℕ} {seedConfig d e : OuterConfig} {seedHead hd he : Fin n}
    {arrows : List OuterArrow}
    (tailH : PakOuterParserListExitReflection.WindowedOuterHistory n d hd
      arrows e he)
    (hfinal : e.state = .accept)
    (fuel : ℕ) (out : MStarParserExecution.Zipper OuterTape)
    (hrun : MStarCopierExecution.run fuel
      (.running .seedCell
        (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out)
    (hout : out = PakOuterParserReflection.windowZipper n d hd)
    (hstate : d.state = (.sim ULogControl.qStart : MStarULogAssembly.State)) :
    ∃ leftExtra rightExtra,
      ∃ z : MStarParserExecution.Zipper ULogProgram.Tape,
      FramingGuards leftExtra rightExtra ∧
      d = anchoredFramedULogConfig ULogControl.qStart 0 leftExtra rightExtra z ∧
      Nonempty (PakOuterULogTraceBridge.OuterArrowHistory d arrows e) := by
  have outerH := windowedHistoryToOuterHistory tailH
  rcases simAcceptingHistory_focus_core outerH ULogControl.qStart hstate hfinal with
    ⟨focus, hfocus⟩
  have hleft := copier_run_groupReady_leftRev_markL fuel .seedCell
    (PakOuterParserReflection.windowZipper n seedConfig seedHead) out hrun
  rw [hout] at hleft
  rcases hleft with ⟨leftTail, hleft⟩
  cases tailH with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c next finish h h' h'' rest a hstep hhead hhead' hhash hhash' tail =>
      let full := PakOuterParserReflection.windowZipper n d hd
      have hfullFocus : full.focus = (.core focus : OuterTape) := by
        have hf := PakOuterParserReflection.windowZipper_focus_eq_head n d hd hhead
        exact hf.trans hfocus
      let z := maximalRightCoreZipper focus full.right
      let leftExtra := full.leftRev
      let rightExtra := afterCorePrefix full.right
      have hframe : frameCoreZipper leftExtra rightExtra z = full := by
        rcases full with ⟨left, physicalFocus, right⟩
        change frameCoreZipper left (afterCorePrefix right)
          (maximalRightCoreZipper focus right) = ⟨left, physicalFocus, right⟩
        change physicalFocus = (.core focus : OuterTape) at hfullFocus
        subst physicalFocus
        exact frame_maximalRightCoreZipper left focus right
      have hguardLeft : NonCoreHead leftExtra := by
        rw [show leftExtra = full.leftRev from rfl, hleft]
        exact (framingGuards_markers leftTail []).left
      have hguards : FramingGuards leftExtra rightExtra :=
        ⟨hguardLeft, afterCorePrefix_nonCoreHead full.right⟩
      have hdTape := PakOuterParserReflection.anchoredZipperTape_windowZipper_eq
        n d hd hhash
      have hcfg : anchoredFramedULogConfig ULogControl.qStart 0
          leftExtra rightExtra z = d := by
        apply outerConfig_ext
        · exact hstate.symm
        · simp [anchoredFramedULogConfig, z, maximalRightCoreZipper,
            leftExtra, full, PakOuterParserReflection.windowZipper,
            PakOuterParserReflection.windowCells, hhead, Nat.le_of_lt hd.2]
        · change anchoredZipperTape 0 (frameCoreZipper leftExtra rightExtra z) =
              d.tape
          rw [hframe]
          exact hdTape
      exact ⟨leftExtra, rightExtra, z, hguards, hcfg.symm, ⟨outerH⟩⟩

/-- Canonical specialization of the preceding physical framing theorem.  If
the successful copier endpoint is known to arise from the canonical side
seed for `x`, its finite core is definitionally the advertised copied ULog
start zipper, rather than an existential maximal core block. -/
theorem canonicalGroupReadyTail_to_copiedQStart
    {n : ℕ} {d e : OuterConfig} {hd he : Fin n}
    {arrows : List OuterArrow}
    (x : ConcretePakSide.Word)
    (tailH : PakOuterParserListExitReflection.WindowedOuterHistory n d hd
      arrows e he)
    (hfinal : e.state = .accept)
    (out : MStarParserExecution.Zipper OuterTape)
    (hout : out = PakOuterParserReflection.windowZipper n d hd)
    (hstate : d.state = (.sim ULogControl.qStart : MStarULogAssembly.State))
    (hcanonical : PakParserOuterBridge.SideCopierCanonical x (.groupReady out)) :
    ∃ leftExtra,
      d = anchoredFramedULogConfig ULogControl.qStart 0 leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x)
        (PakOuterULogBridge.copiedULogStartZipper x) ∧
      Nonempty (PakOuterULogTraceBridge.OuterArrowHistory d arrows e) := by
  have outerH := windowedHistoryToOuterHistory tailH
  have houtFrame :=
    PakOuterULogBridge.SideCopierCanonical.groupReady_eq_framedULogStart
      x out hcanonical
  let leftExtra := out.leftRev
  have hframe : frameCoreZipper leftExtra
      (.markR :: PakSideScanner.sideCopierHashTail x)
      (PakOuterULogBridge.copiedULogStartZipper x) =
        PakOuterParserReflection.windowZipper n d hd := by
    calc
      frameCoreZipper leftExtra
          (.markR :: PakSideScanner.sideCopierHashTail x)
          (PakOuterULogBridge.copiedULogStartZipper x) = out := by
        simpa [leftExtra] using houtFrame.symm
      _ = PakOuterParserReflection.windowZipper n d hd := hout
  cases tailH with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c next finish h h' h'' rest a hstep hhead hhead' hhash hhash' tail =>
      have hdTape := PakOuterParserReflection.anchoredZipperTape_windowZipper_eq
        n d hd hhash
      have hcfg : anchoredFramedULogConfig ULogControl.qStart 0 leftExtra
          (.markR :: PakSideScanner.sideCopierHashTail x)
          (PakOuterULogBridge.copiedULogStartZipper x) = d := by
        apply outerConfig_ext
        · exact hstate.symm
        · simp [anchoredFramedULogConfig, hframe,
            PakOuterParserReflection.windowZipper,
            PakOuterParserReflection.windowCells, hhead, Nat.le_of_lt hd.2]
        · change anchoredZipperTape 0
              (frameCoreZipper leftExtra
                (.markR :: PakSideScanner.sideCopierHashTail x)
                (PakOuterULogBridge.copiedULogStartZipper x)) = d.tape
          rw [hframe]
          exact hdTape
      exact ⟨leftExtra, hcfg.symm, ⟨outerH⟩⟩

theorem generalCapacityGroupReadyTail_to_qStart
    {n : ℕ} {d e : OuterConfig} {hd he : Fin n}
    {arrows : List OuterArrow}
    (x : ConcretePakSide.Word) (physicalCapacity : ℕ)
    (junk external : List MStarCopierMicrocode.ConcreteTape)
    (tailH : PakOuterParserListExitReflection.WindowedOuterHistory n d hd
      arrows e he)
    (hfinal : e.state = .accept)
    (out : MStarParserExecution.Zipper OuterTape)
    (hout : out = PakOuterParserReflection.windowZipper n d hd)
    (hstate : d.state = (.sim ULogControl.qStart : MStarULogAssembly.State))
    (hnormal : out = PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper
      x physicalCapacity junk external) :
    ∃ leftExtra,
      FramingGuards leftExtra (.markR :: external) ∧
      d = anchoredFramedULogConfig ULogControl.qStart 0 leftExtra
        (.markR :: external)
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
          x physicalCapacity) ∧
      Nonempty (PakOuterULogTraceBridge.OuterArrowHistory d arrows e) := by
  have outerH := windowedHistoryToOuterHistory tailH
  have hgroupFrame :=
    PakULogGeneralCapacityBootstrap.rawGeneralCapacityGroupZipper_eq_framed
      x physicalCapacity junk external
  rw [← hnormal] at hgroupFrame
  let leftExtra := out.leftRev
  have hguards : FramingGuards leftExtra (.markR :: external) := by
    constructor
    · intro y
      dsimp [leftExtra]
      rw [hnormal]
      simp [PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper,
        NonCoreHead]
    · exact (framingGuards_markers [] external).right
  have hframe : frameCoreZipper leftExtra (.markR :: external)
      (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
        x physicalCapacity) = PakOuterParserReflection.windowZipper n d hd := by
    calc
      frameCoreZipper leftExtra (.markR :: external)
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            x physicalCapacity) = out := by
        simpa [leftExtra] using hgroupFrame.symm
      _ = PakOuterParserReflection.windowZipper n d hd := hout
  cases tailH with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c next finish h h' h'' rest a hstep hhead hhead' hhash hhash' tail =>
      have hdTape := PakOuterParserReflection.anchoredZipperTape_windowZipper_eq
        n d hd hhash
      have hcfg : anchoredFramedULogConfig ULogControl.qStart 0 leftExtra
          (.markR :: external)
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            x physicalCapacity) = d := by
        apply outerConfig_ext
        · exact hstate.symm
        · simp [anchoredFramedULogConfig, hframe,
            PakOuterParserReflection.windowZipper,
            PakOuterParserReflection.windowCells, hhead, Nat.le_of_lt hd.2]
        · change anchoredZipperTape 0
              (frameCoreZipper leftExtra (.markR :: external)
                (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
                  x physicalCapacity)) = d.tape
          rw [hframe]
          exact hdTape
      exact ⟨leftExtra, hguards, hcfg.symm, ⟨outerH⟩⟩

theorem slotOneFrame_generalCapacityQStart_history {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash) :
    ∃ leftExtra finish arrows,
      FramingGuards leftExtra
          (.markR :: List.replicate hashes MStarOuterProgram.Tape.hash) ∧
      finish.state = .accept ∧ arrows.length ≤ n ∧
      Nonempty (PakOuterULogTraceBridge.OuterArrowHistory
        (anchoredFramedULogConfig ULogControl.qStart 0 leftExtra
          (.markR :: List.replicate hashes MStarOuterProgram.Tape.hash)
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x
            (PakCopierReserveLowerBound.actualFinalCapacity
              x.length remaining.length))) arrows finish) := by
  rcases slotOneWindowedHistoryWithLength F with
    ⟨as, ⟨H⟩, hasLength, hfinal⟩
  rcases parserHistory_to_groupReady_tail H hfinal
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (PakOuterParserListExitReflection.slotOneListTrace F).time_one_parserStart with
    ⟨d, hd, tailArrows, tailHead, ⟨tailH⟩, htailLength,
      copyConfig, copyHead, seedConfig, seedHead, fuel, out,
      hparser, hseedApply, hseedState, hrun, hout, hstate⟩
  have hc := PakOuterParserListExitReflection.traceConfigs_get F
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hh := PakOuterParserListExitReflection.traceHeads_get F
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hc' :
      (PakOuterParserListExitReflection.slotOneListTrace F).configs.get
          ⟨1, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).configs_length]
            have := F.1.width_pos
            omega⟩ =
        (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [PakOuterParserListExitReflection.slotOneListTrace] using hc
  have hh' :
      (PakOuterParserListExitReflection.slotOneListTrace F).heads.get
          ⟨1, by
            rw [(PakOuterParserListExitReflection.slotOneListTrace F).heads_length]
            have := F.1.width_pos
            omega⟩ =
        (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).head_index
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [PakOuterParserListExitReflection.slotOneListTrace] using hh
  have hparser' : MStarParserExecution.Reaches MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTimeOneZipper F))
      (.running MStarParserMicrocode.copyStart
        (PakOuterParserReflection.windowZipper n copyConfig copyHead)) := by
    rw [hc', hh'] at hparser
    simpa only [PakSlotOneParserDecode.slotOneTimeOneZipper] using hparser
  let rawTail : List OuterTape :=
    [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
      remaining.map MStarOuterProgram.Tape.core ++
        MStarCopierMicrocode.rightEnd ::
          List.replicate hashes MStarOuterProgram.Tape.hash
  have hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x) ++ rawTail := by
    simpa [rawTail, List.append_assoc] using hshape
  have hcopy := slotOne_copyStartZipper_eq_of_reaches F x rawTail hprefix
    (PakOuterParserReflection.windowZipper n copyConfig copyHead) hparser'
  have hremaining := slotOne_remaining_eq_work_replicate
    F x remaining hashes hshape
  have hrawTail : rawTail =
      [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
        MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
        List.replicate remaining.length
            (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd ::
            List.replicate hashes MStarOuterProgram.Tape.hash := by
    dsimp [rawTail]
    rw [hremaining]
    simp only [List.map_replicate, List.length_replicate]
  have hseed :
      (MStarCopierExecution.Result.running .seedCell
        (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
      PakCopierReserveLowerBound.rawCopierSeed x remaining.length
        (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])
        (List.replicate hashes MStarOuterProgram.Tape.hash) := by
    unfold PakCopierReserveLowerBound.rawCopierSeed
    congr 1
    rw [hcopy] at hseedApply
    apply Option.some.inj
    simpa [hrawTail, PakSlotOneParserDecode.appendLeftHash,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
      MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      List.append_assoc] using hseedApply.symm
  have hnormal :=
    PakCopierReserveLowerBound.successful_rawCopier_groupReady_eq_generalCapacity
      x remaining.length fuel
      (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])
      (List.replicate hashes MStarOuterProgram.Tape.hash) out (by
        rw [← hseed]
        exact hrun)
  rcases generalCapacityGroupReadyTail_to_qStart x
      (PakCopierReserveLowerBound.actualFinalCapacity x.length remaining.length)
      (MStarConcreteAlphabet.pairingPad x.length ++ [.hash])
      (List.replicate hashes MStarOuterProgram.Tape.hash)
      tailH hfinal out hout hstate hnormal with
    ⟨leftExtra, guards, hd, ⟨outerH⟩⟩
  have hbudget : tailArrows.length ≤ n := by
    calc
      tailArrows.length ≤ as.length := htailLength
      _ = n - 1 := hasLength
      _ ≤ n := Nat.sub_le _ _
  subst d
  exact ⟨leftExtra, _, tailArrows, guards, hfinal, hbudget, ⟨outerH⟩⟩

/-- The capacity-normalized `qStart` suffix projects to one actual finite
slot history.  The capacity and the accepting suffix come from the same
physical FullFrame; no separately chosen reachability witness is used. -/
theorem slotOneFrame_generalCapacityQStart_microPath {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash) :
    ∃ slots acceptedZ,
      ULogBootstrapExecution.ConcreteMicroPath
        (.running ULogControl.qStart
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x
            (PakCopierReserveLowerBound.actualFinalCapacity
              x.length remaining.length)))
        slots (.accepted acceptedZ) ∧
      slots.length ≤ n := by
  rcases slotOneFrame_generalCapacityQStart_history F x remaining hashes hshape with
    ⟨leftExtra, finish, arrows, guards, hfinal, hlength, ⟨outerH⟩⟩
  rcases outerHistory_from_framedSim_to_concreteMicroPath outerH
      ULogControl.qStart 0 leftExtra
      (.markR :: List.replicate hashes MStarOuterProgram.Tape.hash)
      guards
      (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x
        (PakCopierReserveLowerBound.actualFinalCapacity
          x.length remaining.length)) rfl hfinal with
    ⟨slots, acceptedZ, micro, hmicroLength⟩
  exact ⟨slots, acceptedZ, micro, hmicroLength.trans hlength⟩

/-- Every physical slot-one full frame yields an exact raw accepting word at
the first actual ULog cycle boundary, within the literal square-height
budget.  This is the FullFrame-to-raw direction of junk completeness; no
cardinality equality or separately chosen reachability witness is used. -/
theorem slotOneFrame_to_exactConcreteWords_someStart {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ cycleZ,
      Nonempty (ULogBootstrapExecution.ExactConcreteAcceptingWords n
        (.running .cycleStart cycleZ)) := by
  rcases slotOneWindowedHistoryWithLength F with
    ⟨as, ⟨H⟩, hasLength, hfinal⟩
  rcases parserHistory_to_groupReady_tail H hfinal
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (PakOuterParserListExitReflection.slotOneListTrace F).time_one_parserStart with
    ⟨d, hd, tailArrows, tailHead, ⟨tailH⟩, htailLength,
      copyConfig, copyHead, seedConfig, seedHead, fuel, out,
      hparser, hseedApply, hseedState, hrun, hout, hstate⟩
  rcases groupReadyTail_to_framedQStart tailH hfinal fuel out hrun hout hstate with
    ⟨leftExtra, rightExtra, z, guards, hcfg, ⟨outerH⟩⟩
  have hbudget : tailArrows.length ≤ n := by
    calc
      tailArrows.length ≤ as.length := htailLength
      _ = n - 1 := hasLength
      _ ≤ n := Nat.sub_le _ _
  exact outerHistory_from_framedQStart_to_exactConcreteWords outerH 0
    leftExtra rightExtra guards z hcfg hfinal n hbudget

/-- The exact raw execution reflected from a slot-one frame, including the
physical first-cycle zipper which has not yet been identified with the
canonical semantic start. -/
abbrev ReflectedSlotOneRawExecution (n : ℕ) :=
  Σ cycleZ : MStarParserExecution.Zipper ULogProgram.Tape,
    ULogBootstrapExecution.ExactConcreteAcceptingWords n
      (.running .cycleStart cycleZ)

noncomputable def slotOneReflectedRawExecution {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ReflectedSlotOneRawExecution n := by
  let cycleZ := Classical.choose
    (slotOneFrame_to_exactConcreteWords_someStart F)
  let hword := Classical.choose_spec
    (slotOneFrame_to_exactConcreteWords_someStart F)
  exact ⟨cycleZ, Classical.choice hword⟩

abbrev SlotOneOperationalRawSignature (n : ℕ) :=
  PakSlotOneExactCount.SlotOneOperationalSignature n ×
    ReflectedSlotOneRawExecution n

/-- The common-state readback map.  Its first component is definitionally
the established physical operational signature; its second component is
obtained by splitting that same history, not by choosing an unrelated raw
run. -/
noncomputable def slotOneOperationalRawReadback {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    SlotOneOperationalRawSignature n :=
  (PakSlotOneExactCount.slotOneOperationalReadback F,
    slotOneReflectedRawExecution F)

@[simp] theorem slotOneOperationalRawReadback_fst {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (slotOneOperationalRawReadback F).1 =
      PakSlotOneExactCount.slotOneOperationalReadback F := rfl

/-- No physical multiplicity is introduced by adjoining the reflected raw
execution: equality of the common-state signatures implies equality of the
original FullFrames. -/
theorem slotOneOperationalRawReadback_injective {n : ℕ} :
    Function.Injective (slotOneOperationalRawReadback (n := n)) := by
  intro F G h
  apply PakSlotOneExactCount.slotOneOperationalReadback_injective
  exact congrArg Prod.fst h

abbrev SlotOneOperationalRawImage (n : ℕ) :=
  Set.range (slotOneOperationalRawReadback (n := n))

/-- Explicit left inverse onto the genuine common-state image. -/
noncomputable def slotOneOperationalRawEquiv (n : ℕ) :
    PakSlotOneFullFrameReflection.SlotOneFullFrame n ≃
      SlotOneOperationalRawImage n :=
  Equiv.ofInjective (slotOneOperationalRawReadback (n := n))
    slotOneOperationalRawReadback_injective

def semanticFrameChoiceConfig
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix) :
    ULogBootstrapExecution.Result :=
  .running .chooseSlot
    ⟨ULogBootstrapExecution.dynamicRuleReturnPath
          (frame.config.leftRev.map ULogBootstrapExecution.payloadNat)
          frame.config.program input ++
        ULogAlphabet.ulogCore ULogAlphabet.pcMark :: frame.outer,
      ULogBootstrapExecution.readHeadNat frame.config.focus,
      ULogBootstrapExecution.clockCellsAfter
          (frame.config.right.map ULogBootstrapExecution.payloadNat)
          frame.clockZeros frame.runtime ++
        ULogBootstrapExecution.stateWorkspace frame.capacity
          frame.config.state suffix⟩

/-- Every ready semantic frame has a concrete first-choice certificate. -/
noncomputable def semanticFrameFirstChoice
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix)
    (ready : ULogBootstrapExecution.FrameReady frame) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteChoice frame.encode
      (semanticFrameChoiceConfig frame) := by
  have hhead : ULogProgram.choiceHead
      (ULogBootstrapExecution.readHeadNat frame.config.focus) = true := by
    have hf := ready.focus_lt_three
    interval_cases frame.config.focus <;> native_decide
  let left := ULogBootstrapExecution.dynamicRuleReturnPath
      (frame.config.leftRev.map ULogBootstrapExecution.payloadNat)
      frame.config.program input ++
    ULogAlphabet.ulogCore ULogAlphabet.pcMark :: frame.outer
  let right := ULogBootstrapExecution.clockCellsAfter
      (frame.config.right.map ULogBootstrapExecution.payloadNat)
      frame.clockZeros frame.runtime ++
    ULogBootstrapExecution.stateWorkspace frame.capacity frame.config.state suffix
  have hchoice := ULogBootstrapExecution.clockDecrementCells_firstChoice
    (ULogBootstrapExecution.readHeadNat frame.config.focus) hhead
    frame.clockZeros
    (frame.config.right.map ULogBootstrapExecution.payloadNat)
    (ULogBootstrapExecution.payloadNatList_safe frame.config.right)
    left (frame.runtime ++
      ULogBootstrapExecution.stateWorkspace frame.capacity frame.config.state suffix)
  simpa [ULogBootstrapExecution.SemanticCycleFrame.encode,
    ULogBootstrapExecution.semanticCycleEncoding,
    ULogBootstrapExecution.clockCellsBefore,
    ULogBootstrapExecution.clockCellsAfter, semanticFrameChoiceConfig,
    left, right, List.append_assoc]
    using hchoice

/-- The first actual nondeterministic label and its remaining micro-path are
read directly from an accepting micro execution of a ready frame. -/
theorem semanticFrameMicroPath_first_selected
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : ULogBootstrapExecution.SemanticCycleFrame input suffix)
    (ready : ULogBootstrapExecution.FrameReady frame)
    {physicalSlots : List (Fin 2)}
    {acceptedZ : MStarParserExecution.Zipper ULogProgram.Tape}
    (path : ULogBootstrapExecution.ConcreteMicroPath frame.encode physicalSlots
      (.accepted acceptedZ)) :
    ∃ choice slot branch rest,
      choice = semanticFrameChoiceConfig frame ∧
      ULogBootstrapExecution.validStepAt slot choice = some branch ∧
      ULogBootstrapExecution.ConcreteMicroPath branch rest (.accepted acceptedZ) ∧
      physicalSlots = List.replicate (semanticFrameFirstChoice frame ready).steps
        (0 : Fin 2) ++ slot :: rest := by
  let first := semanticFrameFirstChoice frame ready
  rcases firstChoice_split_acceptingMicroPath first.steps frame.encode
      _ physicalSlots acceptedZ first.valid first.before path with
    ⟨afterPrefix, hslots, hpath⟩
  cases hpath with
  | cons choice branch finish slot rest hselected htail =>
      refine ⟨semanticFrameChoiceConfig frame, slot, branch, rest,
        rfl, hselected, htail, ?_⟩
      rw [hslots]

/-- The ULog slot label reflected from a successful physical simulation step
is literally the slot label carried by that outer arrow. -/
theorem reflectedULogArrow_slot
    (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape)
    (d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable
        (anchoredFramedULogConfig q origin leftExtra rightExtra z) a = some d) :
    (Classical.choose
      (ExistsUnique.exists
        (outerStep_from_framedSim_reflects_validStep q origin leftExtra
          rightExtra z d a hstep))).1.2 = a.1.2 := by
  let hua := Classical.choose_spec
    (ExistsUnique.exists
      (outerStep_from_framedSim_reflects_validStep q origin leftExtra
        rightExtra z d a hstep))
  have heq := congrArg (fun arrow : MStarULogAssembly.Arrow => arrow.1.2) hua.1
  exact heq

end PakFixedPolyomino.PakOuterULogReflection
