import PakFixedPolyomino.PakCopierOuterBridge

/-! # Quantitative literal outer lifts -/

namespace PakFixedPolyomino.PakOuterFrontQuantitative

open FiniteOneTapeSemantics
open PakParserOuterBridge

abbrev OuterConfig := PakParserOuterBridge.OuterConfig
abbrev OuterArrow := PakParserOuterBridge.OuterArrow

def OuterReachesAtMost (k : ℕ) (c d : OuterConfig) : Prop :=
  ∃ arrows : List OuterArrow, arrows.length ≤ k ∧
    FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable arrows c = some d

theorem outerReachesAtMost_refl (c : OuterConfig) : OuterReachesAtMost 0 c c :=
  ⟨[], by simp, rfl⟩

theorem outerReachesAtMost_trans {k l : ℕ} {c d e : OuterConfig}
    (hcd : OuterReachesAtMost k c d) (hde : OuterReachesAtMost l d e) :
    OuterReachesAtMost (k + l) c e := by
  rcases hcd with ⟨xs, hxs, rxs⟩
  rcases hde with ⟨ys, hys, rys⟩
  refine ⟨xs ++ ys, by simpa using Nat.add_le_add hxs hys, ?_⟩
  rw [outerRun_append xs ys c, rxs]
  exact rys

theorem outerSlotZeroArrow_atMostOne (c : OuterConfig)
    (q : PakParserOuterBridge.OuterState) (x : PakParserOuterBridge.OuterTape)
    (act : FiniteOneTapeProgram.Action PakParserOuterBridge.OuterState
      PakParserOuterBridge.OuterTape)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act)
    (hstate : c.state = q) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true) :
    OuterReachesAtMost 1 c (afterAction c act) := by
  rcases outer_slotZeroArrow_length_at_most_one c q x act hrule hstate hread
      hmovable with ⟨arrows, hlen, hrun⟩
  exact ⟨arrows, hlen, hrun⟩

theorem canonical_ready_atMostOne
    {Result : Type*} (realize : Result → OuterConfig → Prop)
    {r : Result} {c : OuterConfig} (hrealize : realize r c) :
    ∃ d, realize r d ∧ OuterReachesAtMost 1 c d :=
  ⟨c, hrealize, ⟨[], by simp, rfl⟩⟩

def ParserOuterOneStepSimulation
    (zero one work : MStarULogAssembly.CoreTape)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c → MStarParserExecution.oneStep zero one work r = s →
    ∃ d, realize s d ∧ OuterReachesAtMost 1 c d

theorem canonicalSideParser_oneStepAtMostOne (x : ConcretePakSide.Word) :
    ParserOuterOneStepSimulation MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (CanonicalSideParserRealize x) := by
  intro r s c hrealize hrun
  rcases canonicalSideParser_outerStepSimulation_atMostOne x r s c hrealize
      hrun with ⟨d, hd, arrows, hlen, harrows⟩
  exact ⟨d, hd, ⟨arrows, hlen, harrows⟩⟩

theorem parserRun_outerAtMost
    (zero one work : MStarULogAssembly.CoreTape)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop)
    (hsim : ParserOuterOneStepSimulation zero one work realize)
    (fuel : ℕ) {r s : MStarParserExecution.Result MStarULogAssembly.CoreTape}
    {c : OuterConfig} (hrun : MStarParserExecution.run zero one work fuel r = s)
    (hrealize : realize r c) :
    ∃ d, realize s d ∧ OuterReachesAtMost fuel c d := by
  induction fuel generalizing r c with
  | zero =>
      simp only [MStarParserExecution.run_zero] at hrun
      subst s
      exact ⟨c, hrealize, outerReachesAtMost_refl c⟩
  | succ fuel ih =>
      change MStarParserExecution.run zero one work fuel
        (MStarParserExecution.oneStep zero one work r) = s at hrun
      rcases hsim r _ c hrealize rfl with ⟨d, hd, hcd⟩
      rcases ih hrun hd with ⟨e, he, hde⟩
      exact ⟨e, he, by
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          outerReachesAtMost_trans hcd hde⟩

def CopierOuterOneStepSimulation
    (realize : MStarCopierExecution.Result → OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c → MStarCopierExecution.oneStep r = s →
    ∃ d, realize s d ∧ OuterReachesAtMost 1 c d

theorem canonicalSideCopier_oneStepAtMostOne (x : ConcretePakSide.Word) :
    CopierOuterOneStepSimulation (CanonicalSideCopierRealize x) := by
  intro r s c hrealize hrun
  rcases canonicalSideCopier_outerStepSimulation_atMostOne x r s c hrealize
      hrun with ⟨d, hd, arrows, hlen, harrows⟩
  exact ⟨d, hd, ⟨arrows, hlen, harrows⟩⟩

theorem copierRun_outerAtMost
    (realize : MStarCopierExecution.Result → OuterConfig → Prop)
    (hsim : CopierOuterOneStepSimulation realize)
    (fuel : ℕ) {r s : MStarCopierExecution.Result} {c : OuterConfig}
    (hrun : MStarCopierExecution.run fuel r = s) (hrealize : realize r c) :
    ∃ d, realize s d ∧ OuterReachesAtMost fuel c d := by
  induction fuel generalizing r c with
  | zero =>
      simp only [MStarCopierExecution.run_zero] at hrun
      subst s
      exact ⟨c, hrealize, outerReachesAtMost_refl c⟩
  | succ fuel ih =>
      change MStarCopierExecution.run fuel (MStarCopierExecution.oneStep r) = s at hrun
      rcases hsim r _ c hrealize rfl with ⟨d, hd, hcd⟩
      rcases ih hrun hd with ⟨e, he, hde⟩
      exact ⟨e, he, by
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          outerReachesAtMost_trans hcd hde⟩

structure QuantitativeFrontStages (x : ConcretePakSide.Word) where
  stages : SideStartParserCopierStages x
  parserFuel : ℕ
  copierFuel : ℕ
  parser_length_le : stages.parserArrows.length ≤ parserFuel
  entry_length_le : stages.entryArrows.length ≤ 1
  copier_length_le : stages.copierArrows.length ≤ copierFuel

theorem quantitativeFrontStages (x : ConcretePakSide.Word) :
    Nonempty (QuantitativeFrontStages x) := by
  let parserTarget : MStarParserExecution.Result MStarULogAssembly.CoreTape :=
    .copyReady (MStarParserExecution.extendRight
      (MStarConcreteAlphabet.finalZipper x.reverse)
      (MStarCopierExecution.parserCopierReserve x ++
        PakSideScanner.sideCopierHashTail x))
  have hparserReach : MStarParserExecution.Reaches
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work (sideParserInitialResult x) parserTarget := by
    simpa [parserTarget, sideParserInitialResult] using
      (PakSideScanner.parser_reaches_sideCopierReserve x)
  rcases hparserReach with ⟨parserFuel, hparserAbstract⟩
  rcases parserRun_outerAtMost MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (CanonicalSideParserRealize x) (canonicalSideParser_oneStepAtMostOne x)
      parserFuel hparserAbstract (sideParserCanonicalRealize_initial x) with
    ⟨parserEnd, hparserReady, parserArrows, hparserLen, hparserRun⟩
  rcases sideCopyReady_enters_canonicalCopier_atMostOne x parserEnd
      hparserReady with
    ⟨seedEnd, hseedReady, entryArrows, hentryLen, hentryRun⟩
  rcases (PakSideScanner.side_parser_then_copier x).2.2 with
    ⟨z, hcopierReach, hsegment⟩
  rcases hcopierReach with ⟨copierFuel, hcopierAbstract⟩
  rcases copierRun_outerAtMost (CanonicalSideCopierRealize x)
      (canonicalSideCopier_oneStepAtMostOne x) copierFuel hcopierAbstract
      hseedReady with
    ⟨finish, hfinishReady, copierArrows, hcopierLen, hcopierRun⟩
  let stages : SideStartParserCopierStages x :=
    { parserEnd := parserEnd
      seedEnd := seedEnd
      finish := finish
      groupZipper := z
      startArrow := PakEncodedStart.startOneArrow
      startArrow_eq := rfl
      parserArrows := parserArrows
      entryArrows := entryArrows
      copierArrows := copierArrows
      start_step := PakSideScannerRow.sideEncodedStart_slotOne_step x
      parser_run := hparserRun
      parser_ready := hparserReady
      entry_run := hentryRun
      seed_ready := hseedReady
      copier_run := hcopierRun
      finish_ready := hfinishReady }
  exact ⟨
    { stages := stages
      parserFuel := parserFuel
      copierFuel := copierFuel
      parser_length_le := hparserLen
      entry_length_le := hentryLen
      copier_length_le := hcopierLen }⟩

end PakFixedPolyomino.PakOuterFrontQuantitative
