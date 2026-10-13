import PakFixedPolyomino.PakOuterParserListExitReflection
import PakFixedPolyomino.PakOuterParserPrefixStandard
import PakFixedPolyomino.PakParserKernelOutcomeFacts

/-! Standard reflection on the unchanged ALL literal windowed history, trace
and full-frame carriers. Original compiler-trust source is preserved. -/
namespace PakFixedPolyomino.PakOuterParserListExitReflectionStandard
open PakParserOuterBridge PakOuterParserReflection PakFullFrameTableauReadback
open PakMStarCouplingCorrectness PakOuterParserListExitReflection

abbrev OuterConfig := PakParserOuterBridge.OuterConfig

set_option maxRecDepth 10000 in
/-- The first actual transition of a history from a non-copy parser state
either remains in original parser control or reaches literal outer reject. -/
theorem history_noncopy_target_parser_or_reject {c d : OuterConfig}
    (p : MStarParserMicrocode.ParserState)
    (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d)
    (hstate : c.state = .parser (.inl p))
    (hp : p ≠ MStarParserMicrocode.copyStart) :
    (∃ p', d.state = (.parser (.inl p') : OuterState)) ∨
      d.state = MStarOuterProgram.State.reject := by
  rcases PakOuterParserReflectionStandard.parserUnitAction_of_outerStep
      p c d a hstate hp hstep with
    ⟨ua, hua, _slot, haction, hafter⟩
  have hkind := PakParserKernelOutcomeFacts.every_unit_outcome_good p (c.tape c.head)
  rw [hua] at hkind
  simp only [PakParserKernelOutcomeFacts.unitParserOutcomeGood] at hkind
  change PakParserKernelOutcomeFacts.unitParserTargetGood ua.target = true at hkind
  generalize htarget : ua.target = target at hkind
  cases target with
  | parser p' =>
      left
      refine ⟨p', ?_⟩
      have hs := congrArg (fun q : OuterConfig => q.state) hafter
      simpa [afterAction, liftUnitParserAction, liftUnitParserState, htarget] using hs
  | reject =>
      right
      have hs := congrArg (fun q : OuterConfig => q.state) hafter
      simpa [afterAction, liftUnitParserAction, liftUnitParserState, htarget] using hs
  | start => contradiction
  | accept => contradiction
  | sim q => contradiction

/-- Structural backward reflection needs no first-exit index: a parser state
at the head of any literal history ending in accept has a concrete parser
prefix terminating at `copyStart`. -/
theorem parser_prefix_to_accept {n : ℕ}
    {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : WindowedOuterHistory n c h as e h')
    (hfinal : e.state = MStarOuterProgram.State.accept)
    (p : MStarParserMicrocode.ParserState)
    (hstate : c.state = (.parser (.inl p) : OuterState)) :
    PakOuterParserPrefixReflection.OuterParserPrefix n c h p := by
  induction H generalizing p with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        exact .copyStart c h
      · rcases history_noncopy_target_parser_or_reject p a hstep
            hstate hp with
          ⟨p', hstate'⟩ | hreject
        · exact .step a hstate hstate' hp hhead hhead' hhash hhash' hstep
            (ih hfinal p' hstate')
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

/-- No parser-prefix certificate is supplied: the literal slot-one frame
itself structurally yields an accepting parser computation from time one. -/
theorem slotOneListTrace_parser_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    MStarParserSoundness.CanAcceptResult (.running
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (windowZipper n
        ((slotOneListTrace F).configs.get ⟨1, by
          rw [(slotOneListTrace F).configs_length]
          have := F.1.width_pos
          omega⟩)
        ((slotOneListTrace F).heads.get ⟨1, by
          rw [(slotOneListTrace F).heads_length]
          have := F.1.width_pos
          omega⟩))) := by
  rcases slotOneWindowedHistory F with ⟨as, ⟨H⟩, hfinal⟩
  exact PakOuterParserPrefixStandard.outer_parser_prefix_canAccept
    (parser_prefix_to_accept H hfinal
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (slotOneListTrace F).time_one_parserStart)

/-- Parameter-free slot-one parser soundness at the actual FullFrame time-one
window. -/
theorem slotOneFrame_parser_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    MStarParserSoundness.CanAcceptResult (.running
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (windowZipper n
        ((FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
        ((FullFrame.toUniformWindowedRun F.1).head_index
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩))) := by
  have h := slotOneListTrace_parser_canAccept F
  have hc := traceConfigs_get F ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hh := traceHeads_get F ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hc' : (slotOneListTrace F).configs.get ⟨1, by
        rw [(slotOneListTrace F).configs_length]
        have := F.1.width_pos
        omega⟩ =
      (FullFrame.toUniformWindowedRun F.1).config
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [slotOneListTrace] using hc
  have hh' : (slotOneListTrace F).heads.get ⟨1, by
        rw [(slotOneListTrace F).heads_length]
        have := F.1.width_pos
        omega⟩ =
      (FullFrame.toUniformWindowedRun F.1).head_index
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [slotOneListTrace] using hh
  rw [hc', hh'] at h
  exact h

end PakFixedPolyomino.PakOuterParserListExitReflectionStandard
