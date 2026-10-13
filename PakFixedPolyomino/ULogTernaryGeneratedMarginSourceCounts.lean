import PakFixedPolyomino.ULogTernaryBalancedMarginEncoding
import PakFixedPolyomino.ULogSourceObliviousExteriorZipper
import PakFixedPolyomino.StandardMachineCanonicalCodes
import PakFixedPolyomino.ULogSourceObliviousSemanticAcceptance

/-! Source counts at the literal scanner window specified by the compact
reserve. ALL semantic accepting leaves are counted. The actual feedback
loader-to-scanner execution and physical capacity/time remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginSourceCounts
open StandardNondeterministicMachine StandardMachineWindowBridge
open ULogCompiler ULogSourceObliviousBytecode
open ULogFiniteProgramZipperRunBridge ULogFiniteProgramZipperCounts
open ULogTernaryBalancedMarginEncoding (marginBits)
variable {ns nt : Nat}

noncomputable def copies (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryMarginReserveBudget.iterations nt
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.width nt p x) x.length
noncomputable def radius (nt : Nat) (p : Polynomial Nat) (x : List Bool) : Nat := copies nt p x - 1

theorem copies_positive (nt : Nat) (p : Polynomial Nat) (x : List Bool) : 0 < copies nt p x := by
  have h := (ULogTernaryMarginReserveBudget.compact_reserve_budget nt p x).2.1
  change ULogTernaryGeneratedWindowBudget.radius p x + 1 ≤ copies nt p x at h
  omega

theorem radius_ge_time (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    2 ^ p.eval x.length ≤ radius nt p x :=
  (ULogTernaryMarginReserveBudget.compact_reserve_budget nt p x).2.2.1

noncomputable def scannerInitial (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (left suffix : List (Fin 3)) : BoundedConfig (2 + Fintype.card (Active M)) 3 :=
  ⟨stateEquiv M (.atLeft M.start), left, 2,
    ULogTernaryRetainedCounterPump.cells (marginBits M x (copies nt p x)) ++ 2 :: suffix⟩

theorem scanner_initial_eq (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (left suffix : List (Fin 3)) :
    scannerInitial M p x left suffix =
      ULogSourceObliviousExteriorZipper.zipper M (inputWindow M x (radius nt p x)) left suffix := by
  unfold scannerInitial ULogSourceObliviousExteriorZipper.zipper
  rw [ULogTernaryBalancedMarginEncoding.exact_input_window M x _ (copies_positive nt p x)]
  rfl

theorem ordinary_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (left suffix : List (Fin 3)) :
    acceptingCount M x (2 ^ p.eval x.length) =
      Nat.card (SemanticLeaves (boundedProgram M) (scannerInitial M p x left suffix)) := by
  have hlarge := radius_ge_time nt p x
  have ht : RunsAtMost M x (radius nt p x) := fun w out hw => (htime w out hw).trans hlarge
  rw [scanner_initial_eq]
  exact (acceptingCount_eq_of_bounds M x _ _ _ htime (Nat.le_refl _) hlarge).trans
    (ULogSourceObliviousExteriorZipper.ordinary_semantic_count M x _ ht left suffix)

theorem all_raw_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (left suffix : List (Fin 3))
    (slots : List Bool) (out : ULogSemantics.Config)
    (hsem : semanticRun (liftConfig (boundedProgram M) (scannerInitial M p x left suffix))
      slots = some out) :
    slots.length ≤ ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) := by
  have hmap : (zipperSlotRun (boundedProgram M) slots 0 (scannerInitial M p x left suffix)).map
      (fun hz => liftConfig (boundedProgram M) hz.2) = some out := by
    simpa only [zipperSlotRun_lift] using hsem
  obtain ⟨hz, hzip, _⟩ := Option.map_eq_some_iff.mp hmap
  obtain ⟨word, _, hlen, hrun⟩ := successful_zipper_to_arrows (boundedProgram M)
    slots 0 (scannerInitial M p x left suffix) hz.1 hz.2 hzip
  rw [scanner_initial_eq, ULogSourceObliviousExteriorZipper.zipper_physical] at hrun
  let haltWord := word.map (ULogSourceObliviousBytecodeRunBridge.arrowEquiv M).symm
  have hrestore : haltWord.map (ULogSourceObliviousBytecodeRunBridge.arrowEquiv M) = word :=
    ULogSourceObliviousBytecodeRunBridge.map_arrowEquiv_right M word
  have hnum : FiniteOneTapeSemantics.run
      (ULogSourceObliviousBytecodeRunBridge.numericalProgram M) (fun _ => true)
      (haltWord.map (ULogSourceObliviousBytecodeRunBridge.arrowEquiv M))
      (ULogSourceObliviousBytecodeRunBridge.encodeConfig M
        (ULogSourceObliviousInitialWindowExecution.initialWindowConfig M.start
          (inputWindow M x (radius nt p x))
          (ULogSourceObliviousExteriorZipper.exterior M
            (inputWindow M x (radius nt p x)) left suffix))) =
      some (StandardMachineZipperBridge.physical (2 : Fin 3) hz.1 hz.2) := by
    rw [hrestore]
    exact hrun
  have hhaltmap : (FiniteOneTapeSemantics.run
      (ULogSourceObliviousHaltingProgram.haltProgram M) (fun _ => true) haltWord
      (ULogSourceObliviousInitialWindowExecution.initialWindowConfig M.start
        (inputWindow M x (radius nt p x))
        (ULogSourceObliviousExteriorZipper.exterior M
          (inputWindow M x (radius nt p x)) left suffix))).map
      (ULogSourceObliviousBytecodeRunBridge.encodeConfig M) =
      some (StandardMachineZipperBridge.physical (2 : Fin 3) hz.1 hz.2) := by
    simpa only [ULogSourceObliviousBytecodeRunBridge.run_arrowEquiv] using hnum
  obtain ⟨outHalt, hhaltRun, _⟩ := Option.map_eq_some_iff.mp hhaltmap
  have ht : RunsAtMost M x (radius nt p x) :=
    fun w out hw => (htime w out hw).trans (radius_ge_time nt p x)
  have hbound := ULogSourceObliviousRunTime.all_halt_runs_length_le M x _ ht
    (ULogSourceObliviousExteriorZipper.exterior M (inputWindow M x (radius nt p x)) left suffix)
    haltWord outHalt hhaltRun
  have hl : haltWord.length = word.length := by
    dsimp only [haltWord]
    exact List.length_map _
  have he : haltWord.length = slots.length := hl.trans hlen
  exact he ▸ hbound

theorem cutoff_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (left suffix : List (Fin 3))
    (T : Nat) (hT : ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤ T) :
    acceptingCount M x (2 ^ p.eval x.length) = ULogSemantics.machine.acceptingPaths T
      (liftConfig (boundedProgram M) (scannerInitial M p x left suffix)) := by
  let e : SemanticLeaves (boundedProgram M) (scannerInitial M p x left suffix) ≃
      ULogSourceObliviousSemanticAcceptance.SemanticCutoff
        (liftConfig (boundedProgram M) (scannerInitial M p x left suffix)) T :=
    { toFun := fun leaf => ⟨leaf.val, leaf.property, by
        obtain ⟨out, hrun, _⟩ := leaf.property
        exact (all_raw_length M p x htime left suffix leaf.val out hrun).trans hT⟩
      invFun := fun leaf => ⟨leaf.val, leaf.property.1⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [ordinary_count M p x htime left suffix, Nat.card_congr e]
  exact ULogSourceObliviousSemanticAcceptance.cutoff_card _ T

theorem scanner_count_and_time_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (left suffix : List (Fin 3)) :
    (∀ slots out, semanticRun (liftConfig (boundedProgram M) (scannerInitial M p x left suffix))
        slots = some out →
      slots.length ≤ ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x)) ∧
    (∀ T, ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤ T →
      acceptingCount M x (2 ^ p.eval x.length) = ULogSemantics.machine.acceptingPaths T
        (liftConfig (boundedProgram M) (scannerInitial M p x left suffix))) :=
  ⟨fun slots out => all_raw_length M p x htime left suffix slots out,
    cutoff_count M p x htime left suffix⟩

theorem compact_margin_source_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (htime : ∀ x, RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime
      (ULogTernaryGeneratedMarginEntry.input (Nat.zero_lt_of_lt M.blank.isLt)
        (ULogTernaryMarginMarkedLayout.codes M) M.blank p) ∧
    (∀ x, 0 < copies nt p x ∧ 2 ^ p.eval x.length ≤ radius nt p x ∧
      ∀ left suffix, acceptingCount M x (2 ^ p.eval x.length) =
        Nat.card (SemanticLeaves (boundedProgram M) (scannerInitial M p x left suffix))) :=
  ⟨ULogTernaryGeneratedMarginEntry.input_polyBitTime _ _ _ p,
    fun x => ⟨copies_positive nt p x, radius_ge_time nt p x,
      fun left suffix => ordinary_count M p x (htime x) left suffix⟩⟩

/-- Arbitrary finite branching, duplicate labels and immediate acceptance
are handled by the audited ordinary normalization; no normalized-source
hardness premise is supplied. This remains a scanner endpoint count. -/
theorem sharpEXP_compact_margin_source (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      (M.start.val = 2 ∧ M.accept.val = 0 ∧ M.reject.val = 1 ∧
        M.zero.val = 0 ∧ M.one.val = 1 ∧ M.blank.val = 2) ∧
      StandardBitTime.PolyBitTime
        (ULogTernaryGeneratedMarginEntry.input (Nat.zero_lt_of_lt M.blank.isLt)
          (ULogTernaryMarginMarkedLayout.codes M) M.blank p) ∧
      ∀ x, RunsAtMost M x (2 ^ p.eval x.length) ∧
        2 ^ p.eval x.length ≤ radius nt p x ∧
        ∀ left suffix, f x =
          Nat.card (SemanticLeaves (boundedProgram M) (scannerInitial M p x left suffix)) ∧
          (∀ slots out, semanticRun (liftConfig (boundedProgram M) (scannerInitial M p x left suffix))
              slots = some out →
            slots.length ≤ ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x)) ∧
          (∀ T, ULogSourceObliviousSemanticAcceptance.scannerBudget nt x (radius nt p x) ≤ T →
            f x = ULogSemantics.machine.acceptingPaths T
              (liftConfig (boundedProgram M) (scannerInitial M p x left suffix))) := by
  obtain ⟨ns, nt, M, p, hc, hM⟩ := StandardMachineCanonicalCodes.sharpEXP_to_canonical f hf
  refine ⟨ns, nt, M, p, hc, ULogTernaryGeneratedMarginEntry.input_polyBitTime _ _ _ p, ?_⟩
  intro x
  obtain ⟨htime, hcount⟩ := hM x
  exact ⟨htime, radius_ge_time nt p x,
    fun left suffix => ⟨hcount.trans (ordinary_count M p x htime left suffix),
      fun slots out => all_raw_length M p x htime left suffix slots out,
      fun T hT => hcount.trans (cutoff_count M p x htime left suffix T hT)⟩⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginSourceCounts
