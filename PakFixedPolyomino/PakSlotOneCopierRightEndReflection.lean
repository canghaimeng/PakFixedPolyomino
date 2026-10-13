import PakFixedPolyomino.PakSlotOneSideIdentification
import PakFixedPolyomino.PakCopierOuterBridge

/-! # Copier right-end reflection

The finite control facts below isolate the unique successful entrance to the
copier's final-return phase.  The later spatial lifting must additionally
track the permanent `markR` barrier: parser `lenDone` is also `scratch 2`, but
it lies to the left of that barrier and is not the cell read by
`rightBufferScan`. -/

namespace PakFixedPolyomino.PakSlotOneCopierRightEndReflection

open MStarCopierMicrocode
open MStarOuterProgram
open MStarConcreteAlphabet
open PakMStarCouplingCorrectness
open PakParserOuterBridge

/-- A copier action can enter the universal simulation only from the final
return control. -/
theorem copierStep_sim_forces_finalReturn :
    ∀ (q : CopierState) (x : ConcreteTape)
      (a : FiniteOneTapeProgram.Action (CopierOuterState Unit) ConcreteTape),
      copierStep (UState := Unit) () q x = some a →
      a.target = .sim () → q = .finalReturn ∧ x = .markL := by
  intro q x a hstep htarget
  cases q <;>
    simp [copierStep, copyGo, copyReject, copySim] at hstep <;>
    all_goals
      repeat' first | split at hstep
      all_goals cases hstep
      all_goals simp_all

/-- The unique edge entering `finalReturn` reads the physical right-end
symbol in `rightBufferScan`. -/
theorem copierStep_finalReturn_forces_rightEnd :
    ∀ (q : CopierState) (x : ConcreteTape)
      (a : FiniteOneTapeProgram.Action (CopierOuterState Unit) ConcreteTape),
      copierStep (UState := Unit) () q x = some a →
      a.target = .parser (.inr CopierState.finalReturn) →
      q = .finalReturn ∨ (q = .rightBufferScan ∧ x = rightEnd) := by
  intro q x a hstep htarget
  cases q <;>
    simp [copierStep, copyGo, copyReject, copySim] at hstep <;>
    all_goals
      repeat' first | split at hstep
      all_goals cases hstep
      all_goals simp_all

theorem oneStep_running_to_finalReturn
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hstep : MStarCopierExecution.oneStep (.running q z) =
      .running .finalReturn z') :
    q = .finalReturn ∨ (q = .rightBufferScan ∧ z.focus = rightEnd) := by
  simp only [MStarCopierExecution.oneStep] at hstep
  cases htable : copierStep (UState := Unit) () q z.focus with
  | none => simp [htable] at hstep
  | some a =>
      simp only [htable] at hstep
      cases happly : MStarParserExecution.applyAction z a with
      | none => simp [happly] at hstep
      | some w =>
          simp only [happly] at hstep
          cases htarget : a.target with
          | parser p =>
              cases p with
              | inl p => simp [htarget] at hstep
              | inr q' =>
                  have hq' : q' = .finalReturn := by
                    have hstep' : MStarCopierExecution.Result.running q' w =
                        .running .finalReturn z' := by
                      simpa [htarget] using hstep
                    exact (MStarCopierExecution.Result.running.inj hstep').1
                  subst q'
                  exact copierStep_finalReturn_forces_rightEnd q z.focus a
                    htable htarget
          | sim u | start | accept | reject => simp [htarget] at hstep

theorem oneStep_running_to_groupReady
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hstep : MStarCopierExecution.oneStep (.running q z) = .groupReady z') :
    q = .finalReturn ∧ z.focus = .markL := by
  simp only [MStarCopierExecution.oneStep] at hstep
  cases htable : copierStep (UState := Unit) () q z.focus with
  | none => simp [htable] at hstep
  | some a =>
      simp only [htable] at hstep
      cases happly : MStarParserExecution.applyAction z a with
      | none => simp [happly] at hstep
      | some w =>
          simp only [happly] at hstep
          cases htarget : a.target with
          | sim u =>
              exact copierStep_sim_forces_finalReturn q z.focus a htable (by
                simpa [htarget])
          | parser p =>
              cases p <;> simp [htarget] at hstep
          | start | accept | reject => simp [htarget] at hstep

def CopierReadsRightEnd : MStarCopierExecution.Result → Prop
  | .running .rightBufferScan z => z.focus = rightEnd
  | _ => False

def ReadsRightEnd : ℕ → MStarCopierExecution.Result → Prop
  | 0, _ => False
  | fuel + 1, r => CopierReadsRightEnd r ∨
      ReadsRightEnd fuel (MStarCopierExecution.oneStep r)

theorem run_to_groupReady_reads_or_starts_finalReturn :
    ∀ (fuel : ℕ) (q : CopierState)
      (z out : MStarParserExecution.Zipper ConcreteTape),
      MStarCopierExecution.run fuel (.running q z) = .groupReady out →
      q = .finalReturn ∨ ReadsRightEnd fuel (.running q z) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q z out hrun
      cases hrun
  | succ fuel ih =>
      intro q z out hrun
      rw [MStarCopierExecution.run_succ] at hrun
      cases hnext : MStarCopierExecution.oneStep (.running q z) with
      | rejected =>
          rw [hnext, MStarCopierExecution.rejected_absorbing] at hrun
          cases hrun
      | stuck =>
          rw [hnext, MStarCopierExecution.stuck_absorbing] at hrun
          cases hrun
      | groupReady w =>
          have hfirst := oneStep_running_to_groupReady q z w hnext
          exact Or.inl hfirst.1
      | running q' z' =>
          have htail : MStarCopierExecution.run fuel (.running q' z') =
              .groupReady out := by
            simpa [hnext] using hrun
          rcases ih q' z' out htail with hfinal | hreads
          · subst q'
            rcases oneStep_running_to_finalReturn q z z' hnext with hq | hread
            · exact Or.inl hq
            · right
              simp [ReadsRightEnd, CopierReadsRightEnd, hread.1, hread.2]
          · right
            simp [ReadsRightEnd, hnext, hreads]

theorem seed_run_to_groupReady_reads_rightEnd (fuel : ℕ)
    (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : MStarCopierExecution.run fuel (.running .seedCell z) =
      .groupReady out) :
    ReadsRightEnd fuel (.running .seedCell z) := by
  rcases run_to_groupReady_reads_or_starts_finalReturn fuel .seedCell z out hrun with
    hbad | hread
  · cases hbad
  · exact hread

theorem ReadsRightEnd.exists_run_prefix :
    ∀ {fuel : ℕ} {r : MStarCopierExecution.Result},
      ReadsRightEnd fuel r →
      ∃ k left right, k < fuel ∧
        MStarCopierExecution.run k r =
          .running .rightBufferScan ⟨left, rightEnd, right⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro r h
      exact h.elim
  | succ fuel ih =>
      intro r h
      rcases h with hnow | hlater
      · cases r with
        | running q z =>
            cases q <;> simp [CopierReadsRightEnd] at hnow
            rcases z with ⟨left, focus, right⟩
            change focus = rightEnd at hnow
            subst focus
            exact ⟨0, left, right, by omega, rfl⟩
        | groupReady z | rejected | stuck =>
            simp [CopierReadsRightEnd] at hnow
      · rcases ih hlater with ⟨k, left, right, hk, hrun⟩
        refine ⟨k + 1, left, right, by omega, ?_⟩
        rw [MStarCopierExecution.run_succ]
        exact hrun

theorem seed_run_to_groupReady_has_rightEnd_time (fuel : ℕ)
    (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : MStarCopierExecution.run fuel (.running .seedCell z) =
      .groupReady out) :
    ∃ k left right, k < fuel ∧
      MStarCopierExecution.run k (.running .seedCell z) =
        .running .rightBufferScan ⟨left, rightEnd, right⟩ :=
  (seed_run_to_groupReady_reads_rightEnd fuel z out hrun).exists_run_prefix

private theorem outer_rule_eq_actionOf (a : OuterArrow) :
    MStarULogAssembly.program.rule a.1.1.1 a.1.1.2 a.1.2 =
      some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact hfound
  · rename_i hnone
    exact (a.2 hnone).elim

theorem copier_outer_rule_inverse
    (q : CopierState) (x : OuterTape) (slot : Fin 2) (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.parser (.inr q)) x slot =
      some act) :
    ∃ ua : FiniteOneTapeProgram.Action (CopierOuterState Unit) OuterTape,
      copierStep (UState := Unit) () q x = some ua ∧
      act = changeUnitCopierAction MStarULogAssembly.data.uStart ua := by
  have hslot : slot = 0 := by
    fin_cases slot
    · rfl
    · simp [MStarULogAssembly.program, MStarULogAssembly.data,
        MStarOuterProgram.program] at hrule
  subst slot
  have hcombined : copierStep MStarULogAssembly.data.uStart q x =
      some act := by
    simpa [MStarULogAssembly.program, MStarULogAssembly.data,
      MStarOuterProgram.program, MStarCopierMicrocode.attach,
      MStarCopierMicrocode.step] using hrule
  rw [PakParserOuterBridge.copierStep_changeUState_all q x] at hcombined
  rcases Option.map_eq_some_iff.mp hcombined with ⟨ua, hua, hmap⟩
  exact ⟨ua, hua, hmap.symm⟩

theorem copierUnitAction_of_outerStep
    (q : CopierState) (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state = .parser (.inr q))
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    ∃ ua : FiniteOneTapeProgram.Action (CopierOuterState Unit) OuterTape,
      copierStep (UState := Unit) () q (c.tape c.head) = some ua ∧
      a.1.2 = 0 ∧
      FiniteOneTapeProgram.actionOf MStarULogAssembly.program a =
        changeUnitCopierAction MStarULogAssembly.data.uStart ua ∧
      d = PakParserOuterBridge.afterAction c
        (changeUnitCopierAction MStarULogAssembly.data.uStart ua) := by
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hq : a.1.1.1 = (.parser (.inr q) : OuterState) :=
    hsource.1.symm.trans hstate
  have hx : a.1.1.2 = c.tape c.head := hsource.2.symm
  have hrule : MStarULogAssembly.program.rule (.parser (.inr q))
      (c.tape c.head) a.1.2 =
        some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
    simpa [hq, hx] using outer_rule_eq_actionOf a
  rcases copier_outer_rule_inverse q (c.tape c.head) a.1.2
      (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) hrule with
    ⟨ua, hu, haction⟩
  have hslot : a.1.2 = 0 := by
    by_contra hne
    have hone : a.1.2 = 1 := by
      apply Fin.ext
      omega
    have hnone : MStarULogAssembly.program.rule
        (.parser (.inr q)) a.1.1.2 1 = none := by
      simpa [MStarULogAssembly.program, MStarULogAssembly.data] using
        (MStarCopierMicrocode.combined_slot_one_empty
          ULogProgram.program ULogControl.qAccept ULogControl.qReject
          ULogControl.qStart (.inr q) a.1.1.2)
    apply a.2
    simpa [hq, hone] using hnone
  refine ⟨ua, hu, hslot, haction, ?_⟩
  have hafter := PakOuterParserReflection.outerStep_eq_afterAction c d a hstep
  rw [haction] at hafter
  exact hafter

theorem windowZipper_applyAction_of_copier_after
    (n : ℕ) (c d : OuterConfig) (h h' : Fin n)
    (ua : FiniteOneTapeProgram.Action (CopierOuterState Unit) OuterTape)
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hafter : d = PakParserOuterBridge.afterAction c
      (changeUnitCopierAction MStarULogAssembly.data.uStart ua)) :
    MStarParserExecution.applyAction
      (PakOuterParserReflection.windowZipper n c h) ua =
      some (PakOuterParserReflection.windowZipper n d h') := by
  let z := PakOuterParserReflection.windowZipper n c h
  let lifted := changeUnitCopierAction MStarULogAssembly.data.uStart ua
  have hmove : d.head = FiniteOneTapeSemantics.moveHead ua.move c.head := by
    have hm := congrArg (fun e : OuterConfig => e.head) hafter
    simpa [PakParserOuterBridge.afterAction, lifted,
      changeUnitCopierAction] using hm
  have happly : ∃ z', MStarParserExecution.applyAction z ua = some z' := by
    cases hmoveact : ua.move with
    | stay =>
        exact ⟨{z with focus := ua.write}, by
          simp [z, MStarParserExecution.applyAction, hmoveact]⟩
    | right =>
        have hnext : h.1 + 1 < n := by
          have hm : (h'.1 : Int) = (h.1 : Int) + 1 := by
            rw [← hhead', hmove, hhead]
            simp [FiniteOneTapeSemantics.moveHead, hmoveact]
          omega
        have hright : z.right ≠ [] := by
          intro hnil
          have hdrop : (PakOuterParserReflection.windowCells n c).drop
              (h.1 + 1) = [] := by
            simpa [z, PakOuterParserReflection.windowZipper] using hnil
          have hle := List.drop_eq_nil_iff.mp hdrop
          have hlen : (PakOuterParserReflection.windowCells n c).length = n := by
            simp [PakOuterParserReflection.windowCells]
          omega
        cases hzright : z.right with
        | nil => exact (hright hzright).elim
        | cons x xs =>
            exact ⟨⟨ua.write :: z.leftRev, x, xs⟩, by
              simp [MStarParserExecution.applyAction, hmoveact, hzright]⟩
    | left =>
        have hpositive : 0 < h.1 := by
          have hm : (h'.1 : Int) = (h.1 : Int) - 1 := by
            rw [← hhead', hmove, hhead]
            simp [FiniteOneTapeSemantics.moveHead, hmoveact]
          omega
        have hleft : z.leftRev ≠ [] := by
          intro hnil
          have hlen : z.leftRev.length = h.1 := by
            simp [z, PakOuterParserReflection.windowZipper,
              PakOuterParserReflection.windowCells, Nat.le_of_lt h.2]
          simp [hnil] at hlen
          omega
        cases hzleft : z.leftRev with
        | nil => exact (hleft hzleft).elim
        | cons x xs =>
            exact ⟨⟨xs, x, ua.write :: z.right⟩, by
              simp [MStarParserExecution.applyAction, hmoveact, hzleft]⟩
  rcases happly with ⟨z', happly⟩
  have happlyLift : MStarParserExecution.applyAction z lifted = some z' := by
    unfold lifted
    rw [PakParserOuterBridge.applyAction_changeUnitCopierAction]
    exact happly
  have hcTape : PakParserOuterBridge.anchoredZipperTape 0 z = c.tape := by
    simpa [z] using PakOuterParserReflection.anchoredZipperTape_windowZipper_eq
      n c h hhash
  have htape : PakParserOuterBridge.anchoredZipperTape 0 z' = d.tape := by
    rw [PakParserOuterBridge.anchoredZipperTape_applyAction 0 z z' lifted
      happlyLift, hcTape]
    have hzhead : (z.leftRev.length : Int) = c.head := by
      simp [z, PakOuterParserReflection.windowZipper,
        PakOuterParserReflection.windowCells, hhead, Nat.le_of_lt h.2]
    rw [hzhead]
    have ht := congrArg (fun e : OuterConfig => e.tape) hafter
    simpa [PakParserOuterBridge.afterAction, lifted,
      changeUnitCopierAction, FiniteOneTapeSemantics.writtenTape] using ht.symm
  have hleftlen : z'.leftRev.length =
      (PakOuterParserReflection.windowZipper n d h').leftRev.length := by
    have hzhead := PakParserOuterBridge.anchoredZipperHead_applyAction
      0 z z' lifted happlyLift
    have hm := congrArg (fun e : OuterConfig => e.head) hafter
    have hzval : (z'.leftRev.length : Int) = d.head := by
      calc
        (z'.leftRev.length : Int) =
            FiniteOneTapeSemantics.moveHead lifted.move z.leftRev.length := by
              simpa using hzhead
        _ = FiniteOneTapeSemantics.moveHead lifted.move c.head := by
              congr 2
              simp [z, PakOuterParserReflection.windowZipper,
                PakOuterParserReflection.windowCells, hhead,
                Nat.le_of_lt h.2]
        _ = d.head := by
              simpa [PakParserOuterBridge.afterAction] using hm.symm
    simp [PakOuterParserReflection.windowZipper,
      PakOuterParserReflection.windowCells, Nat.le_of_lt h'.2]
    exact_mod_cast hzval.trans hhead'
  have hzlen : (PakParserOuterBridge.anchoredZipperCells z').length = n := by
    rw [PakParserOuterBridge.anchoredZipperCells_applyAction z z' ua happly]
    rw [List.length_set,
      PakOuterParserReflection.anchoredZipperCells_windowZipper]
    simp [PakOuterParserReflection.windowCells]
  have hwlen : (PakParserOuterBridge.anchoredZipperCells
      (PakOuterParserReflection.windowZipper n d h')).length = n := by
    rw [PakOuterParserReflection.anchoredZipperCells_windowZipper]
    simp [PakOuterParserReflection.windowCells]
  have hdTape := PakOuterParserReflection.anchoredZipperTape_windowZipper_eq
    n d h' hhash'
  have hcells : PakParserOuterBridge.anchoredZipperCells z' =
      PakParserOuterBridge.anchoredZipperCells
        (PakOuterParserReflection.windowZipper n d h') := by
    apply List.ext_get (hzlen.trans hwlen.symm)
    intro i hiz hiw
    have hpoint := congrFun (htape.trans hdTape.symm) (i : Int)
    have hzoff : PakParserOuterBridge.anchoredZipperTape 0 z' (i : Int) =
        (PakParserOuterBridge.anchoredZipperCells z').getD i .hash := by
      simpa using PakParserOuterBridge.anchoredZipperTape_at_offset 0 z' i
    have hwoff : PakParserOuterBridge.anchoredZipperTape 0
        (PakOuterParserReflection.windowZipper n d h') (i : Int) =
        (PakParserOuterBridge.anchoredZipperCells
          (PakOuterParserReflection.windowZipper n d h')).getD i .hash := by
      simpa using PakParserOuterBridge.anchoredZipperTape_at_offset 0
        (PakOuterParserReflection.windowZipper n d h') i
    rw [hzoff, hwoff] at hpoint
    rw [List.getD_eq_get (PakParserOuterBridge.anchoredZipperCells z')
        (.hash : OuterTape) ⟨i, hiz⟩,
      List.getD_eq_get (PakParserOuterBridge.anchoredZipperCells
        (PakOuterParserReflection.windowZipper n d h'))
        (.hash : OuterTape) ⟨i, hiw⟩] at hpoint
    simpa using hpoint
  have hleft : z'.leftRev =
      (PakOuterParserReflection.windowZipper n d h').leftRev := by
    have ht := congrArg (fun xs : List OuterTape => xs.take z'.leftRev.length) hcells
    simpa [PakParserOuterBridge.anchoredZipperCells, hleftlen] using
      congrArg List.reverse ht
  have htail : z'.focus :: z'.right =
      (PakOuterParserReflection.windowZipper n d h').focus ::
        (PakOuterParserReflection.windowZipper n d h').right := by
    have ht := congrArg (fun xs : List OuterTape => xs.drop z'.leftRev.length) hcells
    simpa [PakParserOuterBridge.anchoredZipperCells, hleftlen] using ht
  have hz' : z' = PakOuterParserReflection.windowZipper n d h' := by
    apply MStarParserExecution.Zipper.ext
    · exact hleft
    · exact List.cons.inj htail |>.1
    · exact List.cons.inj htail |>.2
  exact happly.trans (congrArg some hz')

theorem copierStep_target_classification
    (q : CopierState) (x : ConcreteTape)
    (a : FiniteOneTapeProgram.Action (CopierOuterState Unit) ConcreteTape)
    (hstep : copierStep (UState := Unit) () q x = some a) :
    (∃ q', a.target = .parser (.inr q')) ∨
      a.target = .sim () ∨ a.target = .reject := by
  cases q <;>
    simp [copierStep, copyGo, copyReject, copySim] at hstep <;>
    all_goals
      repeat' first | split at hstep
      all_goals cases hstep
      all_goals simp

theorem outerStep_from_copier_target_classification
    (q : CopierState) (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state = .parser (.inr q))
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    (∃ q', d.state = (.parser (.inr q') : OuterState)) ∨
      (∃ u, d.state = (.sim u : OuterState)) ∨
      d.state = MStarOuterProgram.State.reject := by
  rcases copierUnitAction_of_outerStep q c d a hstate hstep with
    ⟨ua, hu, _slot, _haction, hafter⟩
  have hstateAfter := congrArg (fun e : OuterConfig => e.state) hafter
  rcases copierStep_target_classification q (c.tape c.head) ua hu with
    ⟨q', htarget⟩ | hsim | hreject
  · left
    exact ⟨q', by simpa [PakParserOuterBridge.afterAction,
      PakParserOuterBridge.changeUnitCopierAction,
      PakParserOuterBridge.changeUnitCopierState, htarget] using hstateAfter⟩
  · right; left
    exact ⟨MStarULogAssembly.data.uStart, by
      simpa [PakParserOuterBridge.afterAction,
        PakParserOuterBridge.changeUnitCopierAction,
        PakParserOuterBridge.changeUnitCopierState, hsim] using hstateAfter⟩
  · right; right
    simpa [PakParserOuterBridge.afterAction,
      PakParserOuterBridge.changeUnitCopierAction,
      PakParserOuterBridge.changeUnitCopierState, hreject] using hstateAfter

theorem copier_to_copier_oneStep_reflection
    (n : ℕ) (q q' : CopierState) (c d : OuterConfig) (a : OuterArrow)
    (h h' : Fin n)
    (hstate : c.state = .parser (.inr q))
    (hstate' : d.state = .parser (.inr q'))
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    MStarCopierExecution.oneStep (.running q
      (PakOuterParserReflection.windowZipper n c h)) =
      .running q' (PakOuterParserReflection.windowZipper n d h') := by
  rcases copierUnitAction_of_outerStep q c d a hstate hstep with
    ⟨ua, hu, _slot, _haction, hafter⟩
  have happly := windowZipper_applyAction_of_copier_after n c d h h' ua
    hhead hhead' hhash hhash' hafter
  have houterTarget :
      (changeUnitCopierAction MStarULogAssembly.data.uStart ua).target =
        (.parser (.inr q') : OuterState) := by
    have hs := congrArg (fun e : OuterConfig => e.state) hafter
    exact hs.symm.trans hstate'
  have htarget : ua.target = .parser (.inr q') := by
    cases ht : ua.target with
    | parser p =>
        cases p with
        | inl p => simp [changeUnitCopierAction, changeUnitCopierState, ht] at houterTarget
        | inr r =>
            have hr : r = q' := by
              simpa [changeUnitCopierAction, changeUnitCopierState, ht] using houterTarget
            subst r
            rfl
    | start | accept | reject | sim u =>
        simp [changeUnitCopierAction, changeUnitCopierState, ht] at houterTarget
  have hfocus := PakOuterParserReflection.windowZipper_focus_eq_head
    n c h hhead
  simp [MStarCopierExecution.oneStep, hfocus, hu, happly, htarget]

theorem copier_to_sim_oneStep_reflection
    (n : ℕ) (q : CopierState) (c d : OuterConfig) (a : OuterArrow)
    (h h' : Fin n)
    (hstate : c.state = .parser (.inr q))
    (hstate' : ∃ u, d.state = (.sim u : OuterState))
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    MStarCopierExecution.oneStep (.running q
      (PakOuterParserReflection.windowZipper n c h)) =
      .groupReady (PakOuterParserReflection.windowZipper n d h') := by
  rcases hstate' with ⟨u, hstate'⟩
  rcases copierUnitAction_of_outerStep q c d a hstate hstep with
    ⟨ua, hu, _slot, _haction, hafter⟩
  have happly := windowZipper_applyAction_of_copier_after n c d h h' ua
    hhead hhead' hhash hhash' hafter
  have houterTarget :
      (changeUnitCopierAction MStarULogAssembly.data.uStart ua).target =
        (.sim u : OuterState) := by
    have hs := congrArg (fun e : OuterConfig => e.state) hafter
    exact hs.symm.trans hstate'
  have htarget : ua.target = .sim () := by
    cases ht : ua.target with
    | sim v => simpa using ht
    | start | accept | reject | parser =>
        simp [changeUnitCopierAction, changeUnitCopierState, ht] at houterTarget
  have hfocus := PakOuterParserReflection.windowZipper_focus_eq_head
    n c h hhead
  simp [MStarCopierExecution.oneStep, hfocus, hu, happly, htarget]

theorem PakOuterParserListExitReflection.WindowedOuterHistory.copierRun_to_groupReady
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h')
    (hfinal : e.state = MStarOuterProgram.State.accept)
    (q : CopierState) (hstate : c.state = (.parser (.inr q) : OuterState)) :
    ∃ fuel out, MStarCopierExecution.run fuel
      (.running q (PakOuterParserReflection.windowZipper n c h)) =
        .groupReady out := by
  induction H generalizing q with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      rcases outerStep_from_copier_target_classification q c d a hstate hstep with
        ⟨q', hstate'⟩ | ⟨u, hsim⟩ | hreject
      · rcases ih hfinal q' hstate' with ⟨fuel, out, hrun⟩
        refine ⟨fuel + 1, out, ?_⟩
        rw [MStarCopierExecution.run_succ]
        rw [copier_to_copier_oneStep_reflection n q q' c d a h h'
          hstate hstate' hhead hhead' hhash hhash' hstep]
        exact hrun
      · refine ⟨1, PakOuterParserReflection.windowZipper n d h', ?_⟩
        simpa using copier_to_sim_oneStep_reflection n q c d a h h'
          hstate ⟨u, hsim⟩ hhead hhead' hhash hhash' hstep
      · have hend := tail.reject_suffix hreject
        rw [hfinal] at hend
        cases hend

theorem copyStart_outer_target_classification
    (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state =
      (.parser (.inl MStarParserMicrocode.copyStart) : OuterState))
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    (d.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      FiniteOneTapeProgram.actionOf MStarULogAssembly.program a =
        MStarCopierMicrocode.copyGo .markL .seedCell .right) ∨
      d.state = MStarOuterProgram.State.reject := by
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hq : a.1.1.1 =
      (.parser (.inl MStarParserMicrocode.copyStart) : OuterState) :=
    hsource.1.symm.trans hstate
  have hx : a.1.1.2 = c.tape c.head := hsource.2.symm
  have hslot : a.1.2 = 0 := by
    by_contra hne
    have hone : a.1.2 = 1 := by
      apply Fin.ext
      omega
    have hnone : MStarULogAssembly.program.rule
        (.parser (.inl MStarParserMicrocode.copyStart)) a.1.1.2 1 = none := by
      simpa [MStarULogAssembly.program, MStarULogAssembly.data] using
        (MStarCopierMicrocode.combined_slot_one_empty
          ULogProgram.program ULogControl.qAccept ULogControl.qReject
          ULogControl.qStart (.inl MStarParserMicrocode.copyStart) a.1.1.2)
    apply a.2
    simpa [hq, hone] using hnone
  have hrule : MStarULogAssembly.program.rule
      (.parser (.inl MStarParserMicrocode.copyStart)) (c.tape c.head) 0 =
      some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
    simpa [hq, hx, hslot] using outer_rule_eq_actionOf a
  have hcombined : MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      (.inl MStarParserMicrocode.copyStart) (c.tape c.head) =
      some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
    simpa [MStarULogAssembly.program, MStarULogAssembly.data,
      MStarOuterProgram.program, MStarCopierMicrocode.attach] using hrule
  have hafter := PakOuterParserReflection.outerStep_eq_afterAction c d a hstep
  have htarget := congrArg (fun e : OuterConfig => e.state) hafter
  cases htape : c.tape c.head with
  | core x =>
      by_cases hw : x = MStarConcreteAlphabet.work
      · subst x
        left
        have hm := congrArg (Option.map fun act => act.target) hcombined
        have ha : (FiniteOneTapeProgram.actionOf
            MStarULogAssembly.program a).target =
            (.parser (.inr CopierState.seedCell) : OuterState) := by
          simpa [htape, MStarCopierMicrocode.step,
            MStarCopierMicrocode.copyGo] using hm.symm
        have hact : FiniteOneTapeProgram.actionOf MStarULogAssembly.program a =
            MStarCopierMicrocode.copyGo .markL .seedCell .right := by
          rw [htape] at hcombined
          exact Option.some.inj (hcombined.symm.trans (by
            simp [MStarCopierMicrocode.step]))
        exact ⟨htarget.trans ha, hact⟩
      · right
        have hm := congrArg (Option.map fun act => act.target) hcombined
        have ha : (FiniteOneTapeProgram.actionOf
            MStarULogAssembly.program a).target =
            MStarOuterProgram.State.reject := by
          simpa [htape, MStarCopierMicrocode.step, hw,
            MStarCopierMicrocode.copyReject] using hm.symm
        exact htarget.trans ha
  | hash | markL | markR | scratch =>
      right
      have hm := congrArg (Option.map fun act => act.target) hcombined
      have ha : (FiniteOneTapeProgram.actionOf
          MStarULogAssembly.program a).target =
          MStarOuterProgram.State.reject := by
        simpa [htape, MStarCopierMicrocode.step,
          MStarCopierMicrocode.copyReject] using hm.symm
      exact htarget.trans ha

theorem PakOuterParserListExitReflection.WindowedOuterHistory.parser_to_seedRun
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h')
    (hfinal : e.state = MStarOuterProgram.State.accept)
    (p : MStarParserMicrocode.ParserState)
    (hstate : c.state = (.parser (.inl p) : OuterState)) :
    ∃ (d : OuterConfig) (hd : Fin n) (fuel : ℕ)
      (out : MStarParserExecution.Zipper OuterTape),
      d.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell (PakOuterParserReflection.windowZipper n d hd)) =
          .groupReady out := by
  induction H generalizing p with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        rcases copyStart_outer_target_classification c d a hstate hstep with
          ⟨hseed, hseedAction⟩ | hreject
        · rcases PakOuterParserListExitReflection.WindowedOuterHistory.copierRun_to_groupReady
            tail hfinal .seedCell hseed with
            ⟨fuel, out, hrun⟩
          exact ⟨d, h', fuel, out, hseed, hrun⟩
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend
      · rcases PakOuterParserListExitReflection.history_noncopy_target_parser_or_reject
          p a hstep hstate hp with ⟨p', hstate'⟩ | hreject
        · exact ih hfinal p' hstate'
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

theorem slotOneFrame_has_seedRun {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ (d : OuterConfig) (hd : Fin n) (fuel : ℕ)
      (out : MStarParserExecution.Zipper OuterTape),
      d.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell (PakOuterParserReflection.windowZipper n d hd)) =
          .groupReady out := by
  rcases PakOuterParserListExitReflection.slotOneWindowedHistory F with
    ⟨as, ⟨H⟩, hfinal⟩
  exact PakOuterParserListExitReflection.WindowedOuterHistory.parser_to_seedRun
    H hfinal (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (PakOuterParserListExitReflection.slotOneListTrace F).time_one_parserStart

theorem slotOneFrame_has_rightEnd_read {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ (d : OuterConfig) (hd : Fin n) (fuel k : ℕ)
      (out : MStarParserExecution.Zipper OuterTape)
      (left right : List OuterTape),
      d.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      k < fuel ∧
      MStarCopierExecution.run fuel
        (.running .seedCell (PakOuterParserReflection.windowZipper n d hd)) =
          .groupReady out ∧
      MStarCopierExecution.run k
        (.running .seedCell (PakOuterParserReflection.windowZipper n d hd)) =
          .running .rightBufferScan ⟨left, rightEnd, right⟩ := by
  rcases slotOneFrame_has_seedRun F with ⟨d, hd, fuel, out, hstate, hrun⟩
  rcases seed_run_to_groupReady_has_rightEnd_time fuel
      (PakOuterParserReflection.windowZipper n d hd) out hrun with
    ⟨k, left, right, hk, hprefix⟩
  exact ⟨d, hd, fuel, k, out, left, right, hstate, hk, hrun, hprefix⟩

theorem copyStart_to_seed_window_applyAction
    (n : ℕ) (c d : OuterConfig) (a : OuterArrow) (h h' : Fin n)
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (haction : FiniteOneTapeProgram.actionOf MStarULogAssembly.program a =
      MStarCopierMicrocode.copyGo .markL .seedCell .right)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    MStarParserExecution.applyAction
      (PakOuterParserReflection.windowZipper n c h)
      (MStarCopierMicrocode.copyGo (UState := Unit)
        .markL .seedCell .right) =
      some (PakOuterParserReflection.windowZipper n d h') := by
  have hafter := PakOuterParserReflection.outerStep_eq_afterAction c d a hstep
  rw [haction] at hafter
  have hafter' : d = PakParserOuterBridge.afterAction c
      (PakParserOuterBridge.changeUnitCopierAction
        MStarULogAssembly.data.uStart
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right)) := by
    simpa [PakParserOuterBridge.changeUnitCopierAction,
      PakParserOuterBridge.changeUnitCopierState,
      MStarCopierMicrocode.copyGo] using hafter
  exact windowZipper_applyAction_of_copier_after n c d h h'
    (MStarCopierMicrocode.copyGo (UState := Unit)
      .markL .seedCell .right) hhead hhead' hhash hhash' hafter'

theorem PakOuterParserListExitReflection.WindowedOuterHistory.parser_to_copyStart_seedRun
    {n : ℕ} {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : PakOuterParserListExitReflection.WindowedOuterHistory n c h as e h')
    (hfinal : e.state = MStarOuterProgram.State.accept)
    (p : MStarParserMicrocode.ParserState)
    (hstate : c.state = (.parser (.inl p) : OuterState)) :
    ∃ (copyConfig seedConfig : OuterConfig) (copyHead seedHead : Fin n)
      (fuel : ℕ) (out : MStarParserExecution.Zipper OuterTape),
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
      seedConfig.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell
          (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out := by
  induction H generalizing p with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        rcases copyStart_outer_target_classification c d a hstate hstep with
          ⟨hseed, hseedAction⟩ | hreject
        · rcases PakOuterParserListExitReflection.WindowedOuterHistory.copierRun_to_groupReady
            tail hfinal .seedCell hseed with ⟨fuel, out, hrun⟩
          refine ⟨c, d, h, h', fuel, out,
            MStarParserExecution.reaches_refl _ _ _ _, ?_, hseed, hrun⟩
          exact copyStart_to_seed_window_applyAction n c d a h h'
            hhead hhead' hhash hhash' hseedAction hstep
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend
      · rcases PakOuterParserListExitReflection.history_noncopy_target_parser_or_reject
          p a hstep hstate hp with ⟨p', hstate'⟩ | hreject
        · rcases ih hfinal p' hstate' with
            ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
              hparser, hseedApply, hseedState, hrun⟩
          have hone := PakOuterParserReflection.noncopy_parser_oneStep_reflection
            n p p' c d a h h' hstate hstate' hp hhead hhead'
              hhash hhash' hstep
          refine ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out, ?_,
            hseedApply, hseedState, hrun⟩
          exact MStarParserExecution.reaches_trans
            MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
            MStarConcreteAlphabet.work
            (MStarParserExecution.reaches_of_oneStep
              MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
              MStarConcreteAlphabet.work hone) hparser
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

theorem slotOneFrame_copyStart_seedRun {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ (copyConfig seedConfig : OuterConfig) (copyHead seedHead : Fin n)
      (fuel : ℕ) (out : MStarParserExecution.Zipper OuterTape),
      MStarParserExecution.Reaches MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
          (PakSlotOneParserDecode.slotOneTimeOneZipper F))
        (.running MStarParserMicrocode.copyStart
          (PakOuterParserReflection.windowZipper n copyConfig copyHead)) ∧
      MStarParserExecution.applyAction
        (PakOuterParserReflection.windowZipper n copyConfig copyHead)
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
        some (PakOuterParserReflection.windowZipper n seedConfig seedHead) ∧
      seedConfig.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell
          (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out := by
  rcases PakOuterParserListExitReflection.slotOneWindowedHistory F with
    ⟨as, ⟨H⟩, hfinal⟩
  rcases PakOuterParserListExitReflection.WindowedOuterHistory.parser_to_copyStart_seedRun
      H hfinal (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakOuterParserListExitReflection.slotOneListTrace F).time_one_parserStart with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hparser, hseedApply, hseedState, hrun⟩
  have hc := PakOuterParserListExitReflection.traceConfigs_get F
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hh := PakOuterParserListExitReflection.traceHeads_get F
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hc' : (PakOuterParserListExitReflection.slotOneListTrace F).configs.get
      ⟨1, by
        rw [(PakOuterParserListExitReflection.slotOneListTrace F).configs_length]
        have := F.1.width_pos
        omega⟩ =
      (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [PakOuterParserListExitReflection.slotOneListTrace] using hc
  have hh' : (PakOuterParserListExitReflection.slotOneListTrace F).heads.get
      ⟨1, by
        rw [(PakOuterParserListExitReflection.slotOneListTrace F).heads_length]
        have := F.1.width_pos
        omega⟩ =
      (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).head_index
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [PakOuterParserListExitReflection.slotOneListTrace] using hh
  refine ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out, ?_,
    hseedApply, hseedState, hrun⟩
  rw [hc', hh'] at hparser
  simpa only [PakSlotOneParserDecode.slotOneTimeOneZipper] using hparser

theorem run_appendLeftHash_to_copyStart_reflect :
    ∀ (fuel : ℕ) (r : MStarParserExecution.Result CoreTape)
      (zfull : MStarParserExecution.Zipper OuterTape),
      MStarParserExecution.run zero one work fuel
        (PakSlotOneParserDecode.appendLeftHashResult r) =
          .running MStarParserMicrocode.copyStart zfull →
      ∃ z,
        zfull = PakSlotOneParserDecode.appendLeftHash z ∧
        MStarParserExecution.run zero one work fuel r =
          .running MStarParserMicrocode.copyStart z := by
  intro fuel
  induction fuel with
  | zero =>
      intro r zfull hrun
      cases r with
      | running p z =>
          simp only [MStarParserExecution.run,
            PakSlotOneParserDecode.appendLeftHashResult] at hrun
          have hp := MStarParserExecution.Result.running.inj hrun
          rcases hp with ⟨rfl, hz⟩
          exact ⟨z, hz.symm, rfl⟩
      | copyReady z | rejected | stuck =>
          simp [MStarParserExecution.run,
            PakSlotOneParserDecode.appendLeftHashResult] at hrun
  | succ fuel ih =>
      intro r zfull hrun
      have haccept : MStarParserSoundness.CanAcceptResult
          (PakSlotOneParserDecode.appendLeftHashResult r) := by
        refine ⟨fuel + 2, zfull, ?_⟩
        rw [show fuel + 2 = (fuel + 1) + 1 by omega,
          MStarParserExecution.run_add, hrun]
        rfl
      have hcomm := PakSlotOneParserDecode.oneStep_appendLeftHash_of_canAccept
        r haccept
      rw [MStarParserExecution.run_succ, hcomm] at hrun
      rcases ih (MStarParserExecution.oneStep zero one work r) zfull hrun with
        ⟨z, hzfull, hzrun⟩
      exact ⟨z, hzfull, hzrun⟩

theorem trimmed_initial_eq_extendResultRight {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List OuterTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells zero one work
        (ConcretePakSide.encodedWord x) ++ tail) :
    (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTrimmedZipper F) :
      MStarParserExecution.Result CoreTape) =
      MStarParserExecution.extendResultRight
        (MStarParserExecution.initial zero one work
          (ConcretePakSide.encodedWord x)) tail := by
  cases hcells : MStarParserExecution.inputCells zero one work
      (ConcretePakSide.encodedWord x) with
  | nil =>
      exact (MStarParserExecution.inputCells_ne_nil zero one work
        (ConcretePakSide.encodedWord x) hcells).elim
  | cons y ys =>
      unfold MStarParserExecution.initial
      rw [hcells]
      simp only [MStarParserExecution.extendResultRight,
        MStarParserExecution.extendRight]
      congr 1
      apply MStarParserExecution.Zipper.ext
      · rfl
      · have ht := List.cons.inj (by
          simpa [hcells, List.append_assoc] using hprefix)
        exact ht.1
      · have ht := List.cons.inj (by
          simpa [hcells, List.append_assoc] using hprefix)
        exact ht.2

theorem slotOne_copyStart_origin {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (tail : List OuterTape)
    (hprefix : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      MStarParserExecution.inputCells zero one work
        (ConcretePakSide.encodedWord x) ++ tail) :
    ∃ (copyConfig seedConfig : OuterConfig) (copyHead seedHead : Fin n)
      (fuel : ℕ) (out : MStarParserExecution.Zipper OuterTape),
      PakOuterParserReflection.windowZipper n copyConfig copyHead =
        PakSlotOneParserDecode.appendLeftHash
          (MStarParserExecution.extendRight
            (MStarConcreteAlphabet.finalZipper x.reverse) tail) ∧
      MStarParserExecution.applyAction
        (PakOuterParserReflection.windowZipper n copyConfig copyHead)
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
        some (PakOuterParserReflection.windowZipper n seedConfig seedHead) ∧
      seedConfig.state = (.parser (.inr CopierState.seedCell) : OuterState) ∧
      MStarCopierExecution.run fuel
        (.running .seedCell
          (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out := by
  rcases slotOneFrame_copyStart_seedRun F with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      hparser, hseedApply, hseedState, hrun⟩
  rcases hparser with ⟨parserFuel, hparser⟩
  have hfull : PakSlotOneParserDecode.slotOneTimeOneZipper F =
      PakSlotOneParserDecode.appendLeftHash
        (PakSlotOneParserDecode.slotOneTrimmedZipper F) :=
    PakSlotOneParserDecode.slotOneTimeOneZipper_eq_appendLeftHash F
  have hparser' : MStarParserExecution.run zero one work parserFuel
      (PakSlotOneParserDecode.appendLeftHashResult
        (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
          (PakSlotOneParserDecode.slotOneTrimmedZipper F))) =
      .running MStarParserMicrocode.copyStart
        (PakOuterParserReflection.windowZipper n copyConfig copyHead) := by
    simpa [PakSlotOneParserDecode.appendLeftHashResult, hfull] using hparser
  rcases run_appendLeftHash_to_copyStart_reflect parserFuel
      (.running (MStarParserMicrocode.fixed ⟨0, by decide⟩)
        (PakSlotOneParserDecode.slotOneTrimmedZipper F))
      (PakOuterParserReflection.windowZipper n copyConfig copyHead) hparser' with
    ⟨copyTrim, hcopyFull, hcopyTrim⟩
  have hinitial := trimmed_initial_eq_extendResultRight F x tail hprefix
  have hactual : MStarParserExecution.run zero one work (parserFuel + 1)
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial zero one work
          (ConcretePakSide.encodedWord x)) tail) = .copyReady copyTrim := by
    rw [← hinitial, MStarParserExecution.run_add, hcopyTrim]
    rfl
  rcases MStarConcreteAlphabet.reaches_parser_encodedWord_with_tail x tail with
    ⟨canonicalFuel, hcanonical⟩
  have hcopyTrimEq : copyTrim = MStarParserExecution.extendRight
      (MStarConcreteAlphabet.finalZipper x.reverse) tail :=
    MStarParserExecution.copyReady_output_unique zero one work _
      (parserFuel + 1) canonicalFuel copyTrim
      (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) tail)
      hactual hcanonical
  refine ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out, ?_,
    hseedApply, hseedState, hrun⟩
  rw [hcopyFull, hcopyTrimEq]

end PakFixedPolyomino.PakSlotOneCopierRightEndReflection
