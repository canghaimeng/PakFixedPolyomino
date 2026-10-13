import PakFixedPolyomino.PakGeneralCapacityOuterFrontFuel

/-! The actual capacity parser/copier front has parser-state sources at every
occupied arrow, until the final simulated qStart. The trace and arrow bound
are derived internally from literal parser/copier fuel, including absorbing
abstract endpoints. This supplies execution data for deterministic first-hit
cancellation; it is not an assumed frame/source counting inverse. -/
namespace PakFixedPolyomino.PakCapacityOuterFrontParserPrefix
open FiniteOneTapeSemantics MStarConcreteAlphabet
open PakParserOuterBridge PakGeneralCapacityInitialWindow
open PakGeneralCapacityParserCopierFront PakGeneralCapacityOuterFrontStandard
open PakGeneralCapacityOuterFrontFuel PakSlotOneScannerMultiplicity

abbrev OuterConfig := PakParserOuterBridge.OuterConfig
abbrev OuterArrow := PakParserOuterBridge.OuterArrow
abbrev Result := MStarParserExecution.Result MStarULogAssembly.CoreTape

inductive ParserPrefix : List OuterArrow → OuterConfig → OuterConfig → Prop
  | nil (c : OuterConfig) : ParserPrefix [] c c
  | cons {c d e : OuterConfig} {labels : List OuterArrow} (a : OuterArrow)
      (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d)
      (hp : ∃ q, c.state = .parser q) (tail : ParserPrefix labels d e) :
      ParserPrefix (a :: labels) c e

theorem ParserPrefix.run {c d : OuterConfig} {labels : List OuterArrow}
    (h : ParserPrefix labels c d) :
    run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d := by
  induction h with
  | nil => rfl
  | cons a hs hp tail ih => simpa [run_cons, hs] using ih

theorem ParserPrefix.append {c d e : OuterConfig} {xs ys : List OuterArrow}
    (h : ParserPrefix xs c d) (g : ParserPrefix ys d e) :
    ParserPrefix (xs ++ ys) c e := by
  induction h with
  | nil => exact g
  | cons a hs hp tail ih => exact .cons a hs hp (ih g)

theorem parserPrefix_of_run_atMostOne (c d : OuterConfig) (labels : List OuterArrow)
    (hp : ∃ q, c.state = .parser q) (hl : labels.length ≤ 1)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d) :
    ParserPrefix labels c d := by
  cases labels with
  | nil =>
      have hd : c = d := Option.some.inj hr
      subst d
      exact .nil c
  | cons a labels =>
      have ht : labels.length = 0 := by simp only [List.length_cons] at hl; omega
      have hn : labels = [] := List.eq_nil_of_length_eq_zero ht
      subst labels
      have hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d := by
        cases he : step MStarULogAssembly.program MStarOuterProgram.movable c a with
        | none => simp [run_cons, he] at hr
        | some next =>
            have hd : next = d := Option.some.inj (by simpa [run_cons, he] using hr)
            simpa [hd] using he
      exact .cons a hs hp (.nil d)

theorem capacityParserRealize_source_parser (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (r : Result) (c : OuterConfig)
    (h : CapacitySideParserRealize x cap r c) : ∃ q, c.state = .parser q := by
  cases r with
  | rejected => exact h.2.elim
  | stuck => exact h.2.elim
  | running p z =>
      obtain ⟨origin, rfl⟩ := h.2
      exact ⟨.inl p, rfl⟩
  | copyReady z =>
      obtain ⟨origin, rfl⟩ := h.2
      exact ⟨.inl MStarParserMicrocode.copyStart, rfl⟩

theorem parser_run_prefix (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (fuel : Nat) (r s : Result) (c : OuterConfig)
    (hr : MStarParserExecution.run zero one work fuel r = s)
    (hc : CapacitySideParserRealize x cap r c) :
    ∃ d labels, CapacitySideParserRealize x cap s d ∧
      labels.length ≤ fuel ∧ ParserPrefix labels c d := by
  induction fuel generalizing r c with
  | zero =>
      have he : r = s := hr
      subst s
      exact ⟨c, [], hc, Nat.zero_le _, .nil c⟩
  | succ fuel ih =>
      obtain ⟨d, hd, xs, hb, hrun⟩ :=
        capacitySideParser_outerStepSimulation_atMostOne x cap r
          (MStarParserExecution.oneStep zero one work r) c hc rfl
      have hp := parserPrefix_of_run_atMostOne c d xs
        (capacityParserRealize_source_parser x cap r c hc) hb hrun
      obtain ⟨e, ys, he, hy, hprefix⟩ := ih
        (MStarParserExecution.oneStep zero one work r) d hr hd
      exact ⟨e, xs ++ ys, he, by simp only [List.length_append]; omega,
        hp.append hprefix⟩

theorem copier_run_prefix (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val)
    (fuel : Nat) (r s : MStarCopierExecution.Result) (c : OuterConfig)
    (hr : MStarCopierExecution.run fuel r = s)
    (hc : CapacitySideCopierRealize x cap hmin r c) :
    ∃ d labels, CapacitySideCopierRealize x cap hmin s d ∧
      labels.length ≤ fuel ∧ ParserPrefix labels c d := by
  induction fuel generalizing r c with
  | zero =>
      have he : r = s := hr
      subst s
      exact ⟨c, [], hc, Nat.zero_le _, .nil c⟩
  | succ fuel ih =>
      cases r with
      | rejected => exact hc.2.elim
      | stuck => exact hc.2.elim
      | groupReady z =>
          have he : MStarCopierExecution.Result.groupReady z = s := by
            simpa only [MStarCopierExecution.groupReady_absorbing] using hr
          refine ⟨c, [], ?_, Nat.zero_le _, .nil c⟩
          rw [← he]
          exact hc
      | running q z =>
          have hp : ∃ p, c.state = .parser p := by
            obtain ⟨origin, he⟩ := hc.2
            rw [he]
            exact ⟨.inr q, rfl⟩
          obtain ⟨d, hd, xs, hb, hrun⟩ :=
            capacitySideCopier_outerStepSimulation_atMostOne x cap hmin
              (.running q z) (MStarCopierExecution.oneStep (.running q z)) c hc rfl
          have hx := parserPrefix_of_run_atMostOne c d xs hp hb hrun
          obtain ⟨e, ys, he, hy, hprefix⟩ := ih
            (MStarCopierExecution.oneStep (.running q z)) d hr hd
          exact ⟨e, xs ++ ys, he, by simp only [List.length_append]; omega,
            hx.append hprefix⟩

theorem capacity_outer_front_parser_prefix (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d labels, CapacitySideCopierRealize x cap hmin
        (.groupReady (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
          (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.val)
          (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      labels.length ≤ generalOuterFrontFuel x cap.val ∧
      ParserPrefix labels (capacityEncodedParserConfig x cap) d := by
  obtain ⟨parserEnd, pre, hready, hpbound, hparser⟩ := parser_run_prefix x cap
    (PakOuterParserNumericSuffix.parserExplicitFuel x) _ _ _
    (run_capacityParserInitial_explicitFuel x cap) (capacitySideParserRealize_initial x cap)
  obtain ⟨seedEnd, hseed, entry, hebound, heRun⟩ :=
    capacityCopyReady_enters_capacityCopier_atMostOne x cap hmin parserEnd hready
  have hentry := parserPrefix_of_run_atMostOne parserEnd seedEnd entry
    (capacityParserRealize_source_parser x cap _ parserEnd hready) hebound heRun
  have hcRun := PakCopierGeneralCompleteFuel.run_raw_copier_complete x cap.val
    (capacityCopierJunk x) (capacityHashTail x cap) hmin
  rw [rawCopierSeed_eq_capacityRawCopierSeedZipper] at hcRun
  obtain ⟨finish, tail, hfinish, htbound, hcopier⟩ := copier_run_prefix x cap hmin
    (PakCopierGeneralCompleteFuel.generalCopierFuel x cap.val) _ _ seedEnd hcRun hseed
  refine ⟨finish, pre ++ entry ++ tail, hfinish, ?_,
    (hparser.append hentry).append hcopier⟩
  simp only [List.length_append]
  unfold generalOuterFrontFuel
  omega

end PakFixedPolyomino.PakCapacityOuterFrontParserPrefix
