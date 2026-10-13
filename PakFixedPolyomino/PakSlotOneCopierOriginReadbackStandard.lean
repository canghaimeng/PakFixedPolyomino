import PakFixedPolyomino.PakSlotOneCopierRightEndReflection
import PakFixedPolyomino.PakSlotOneParserDecodeStandard

/-! Actual parser-to-copier origin from EVERY original slot-one full frame
and an explicit encoded prefix with arbitrary tail. Original window and
zipper functions retained; only contaminated parser compositions replaced. -/
namespace PakFixedPolyomino.PakSlotOneCopierOriginReadbackStandard
open MStarCopierMicrocode MStarOuterProgram MStarConcreteAlphabet
open PakMStarCouplingCorrectness PakParserOuterBridge
open PakSlotOneCopierRightEndReflection
set_option maxHeartbeats 3000000

theorem history_parser_to_copyStart_seedRun
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
      · rcases PakOuterParserListExitReflectionStandard.history_noncopy_target_parser_or_reject
          p a hstep hstate hp with ⟨p', hstate'⟩ | hreject
        · rcases ih hfinal p' hstate' with
            ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
              hparser, hseedApply, hseedState, hrun⟩
          have hone := PakOuterParserReflectionStandard.noncopy_parser_oneStep_reflection
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
  rcases history_parser_to_copyStart_seedRun
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
      have hcomm : MStarParserExecution.oneStep zero one work
          (PakSlotOneParserDecode.appendLeftHashResult r) =
          PakSlotOneParserDecode.appendLeftHashResult
            (MStarParserExecution.oneStep zero one work r) :=
        PakSlotOneParserDecodeStandard.oneStep_appendLeftHash_of_canAccept r haccept
      rw [MStarParserExecution.run_succ, hcomm] at hrun
      rcases ih (MStarParserExecution.oneStep zero one work r) zfull hrun with
        ⟨z, hzfull, hzrun⟩
      exact ⟨z, hzfull, hzrun⟩

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
    PakSlotOneParserDecodeStandard.slotOneTimeOneZipper_eq_appendLeftHash F
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

end PakFixedPolyomino.PakSlotOneCopierOriginReadbackStandard
