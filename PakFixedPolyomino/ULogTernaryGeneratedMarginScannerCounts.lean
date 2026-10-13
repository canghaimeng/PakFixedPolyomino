import PakFixedPolyomino.ULogTernaryGeneratedMarginScanner
import PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts

/-! Concrete count transfer from the actual compact loader to the original
ordinary scanner. All generic first-child hypotheses are discharged from
the actual caller. Physical interpreter time/capacity and square tilings
remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCounts
open ULogCompiler ULogFiniteTapeZipperRun
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)
open ULogTernaryGeneratedMarginScanner
variable {ns nt : Nat}

noncomputable def budget (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  bootDeadline M p x + 14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2

theorem fresh_cutoff (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths (T + 1)
      (liftConfig (scannerProgram M) (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x))) =
      ULogSemantics.machine.acceptingPaths T
        (liftConfig (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x)) := by
  have h := ULogFreshEntryExteriorBoot.cutoff_succ
    (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x)
    (ULogFreshEntryExteriorBoot.scanner_right_nonempty M p x
      (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x)) T
  simpa [scannerProgram, scannerState, scannerStates, scannerInitial,
    ULogTernaryGeneratedMarginSourceCounts.scannerInitial] using h

theorem cutoff_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x)) =
      if ULogTernaryGeneratedMarginLoop.deadline M p x + 3 ≤ T then
        ULogSemantics.machine.acceptingPaths
          (T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 3))
          (liftConfig (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x))
      else 0 := by
  have hg := ULogFiniteTapeGuardedStageLeafCounts.cutoff_acceptingPaths
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) T
  rw [start_input]
  change ULogSemantics.machine.acceptingPaths T
    (liftConfig (ULogFiniteTapeGuardedStageComposition.program
      (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
      (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right)
      (ULogFiniteTapeGuardedStageComposition.leftConfig
        (ULogTernaryGeneratedMarginLoop.initial nt p x))) = _
  rw [hg]
  by_cases h3 : ULogTernaryGeneratedMarginLoop.deadline M p x + 3 ≤ T
  · have h2 : ULogTernaryGeneratedMarginLoop.deadline M p x + 2 ≤ T := by omega
    have hd : T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 2) =
        (T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 3)) + 1 := by omega
    rw [if_pos h2, if_pos h3, handoff_start M p x, hd, fresh_cutoff]
  · rw [if_neg h3]
    by_cases h2 : ULogTernaryGeneratedMarginLoop.deadline M p x + 2 ≤ T
    · have hd : T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 2) = 0 := by omega
      rw [if_pos h2, handoff_start M p x, hd]
      have hl := ULogFreshEntryExteriorBoot.initial_live (scannerInitial M p x)
      change ULogSemantics.machine.acceptingPaths 0
        (liftConfig (ULogFreshEntry.program (ULogSourceObliviousBytecode.boundedProgram M)
          (scannerInitial M p x).state) (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x))) = 0
      have hh : ULogSemantics.halted
          (liftConfig (ULogFreshEntry.program (ULogSourceObliviousBytecode.boundedProgram M)
            (scannerInitial M p x).state) (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x))) = false := hl
      simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine,
        hh]
    · rw [if_neg h2]

theorem large_cutoff_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (T : Nat) (hT : budget M p x ≤ T) :
    acceptingCount M x (2 ^ p.eval x.length) =
      ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x)) := by
  have hg := ULogFiniteTapeGuardedStageLeafCounts.cutoff_acceptingPaths
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x) T
  have hbound : ULogTernaryGeneratedMarginLoop.deadline M p x + 3 +
      14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 ≤ T := hT
  have hle : ULogTernaryGeneratedMarginLoop.deadline M p x + 2 ≤ T := by omega
  have hdiff : T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 2) =
      (T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 3)) + 1 := by omega
  rw [if_pos hle, handoff_start M p x, hdiff, fresh_cutoff] at hg
  have hs := ULogTernaryGeneratedMarginSourceClock.large_cutoff_count M p x htime
    (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x)
    (T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 3)) (by omega)
  rw [start_input]
  exact hs.trans hg.symm

theorem all_raw_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length))
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (hw : run (program M p) 2 w 0 (initial M p x) = some (hf, out)) :
    w.length ≤ budget M p x := by
  have hg := ULogFiniteTapeGuardedStageLeafCounts.all_raw_length_le
    (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
    (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
    (ULogTernaryGeneratedMarginLoop.initial nt p x) (ULogTernaryGeneratedMarginLoop.final M p x)
    0 (ULogTernaryGeneratedMarginLoop.head nt p x) (ULogTernaryGeneratedMarginLoop.deadline M p x)
    (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
    (ULogTernaryGeneratedMarginLoop.actual_run M p x)
    (ULogTernaryGeneratedMarginLoop.final_accepts M p x)
    (14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 + 1) (by
      intro v hv zq hq
      rw [handoff_start M p x] at hq
      have hs := ULogFiniteTapeGuardedStageLeafCounts.semantic_of_run (scannerProgram M) v
        (FiniteOneTapeSemantics.moveHead .right (ULogTernaryGeneratedMarginLoop.head nt p x)) hv
        (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x)) zq hq
      apply ULogFreshEntryExteriorBoot.scanner_all_raw_length M p x htime
        (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x) v
        (liftConfig (scannerProgram M) zq)
      simpa [scannerProgram, scannerState, scannerStates, scannerInitial,
        ULogTernaryGeneratedMarginSourceCounts.scannerInitial] using hs) w hf out hw
  unfold budget bootDeadline
  omega

theorem all_semantic_raw_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input M p x)) w = some out) :
    w.length ≤ budget M p x := by
  rw [start_input] at hw
  have hmap : (run (program M p) (2 : Fin 3) w 0 (initial M p x)).map
      (fun hz => liftConfig (program M p) hz.2) = some out := by
    rw [run_lift _ (2 : Fin 3) rfl]
    exact hw
  obtain ⟨hz, hzip, _⟩ := Option.map_eq_some_iff.mp hmap
  exact all_raw_length M p x htime w hz.1 hz.2 hzip

theorem all_bridge_semantic_raw_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (out : ULogSemantics.Config)
    (hw : ULogFiniteProgramZipperRunBridge.semanticRun
      (liftConfig (program M p) (initial M p x)) w = some out) :
    w.length ≤ budget M p x := by
  obtain ⟨hf, zf, hzip, _⟩ := ULogFiniteTapeGuardedStageLeafCounts.run_of_semantic
    (program M p) w 0 (initial M p x) out hw
  exact all_raw_length M p x htime w hf zf hzip

theorem ordinary_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) :
    acceptingCount M x (2 ^ p.eval x.length) =
      Nat.card (ULogFiniteProgramZipperRunBridge.SemanticLeaves (program M p) (initial M p x)) := by
  let e : ULogFiniteProgramZipperRunBridge.SemanticLeaves (program M p) (initial M p x) ≃
      ULogSourceObliviousSemanticAcceptance.SemanticCutoff
        (ULogSemantics.start (input M p x)) (budget M p x) :=
    { toFun := fun leaf => ⟨leaf.val, by simpa only [start_input] using leaf.property, by
        obtain ⟨out, hrun, _⟩ := leaf.property
        exact all_bridge_semantic_raw_length M p x htime leaf.val out hrun⟩
      invFun := fun leaf => ⟨leaf.val, by simpa only [start_input] using leaf.property.1⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  rw [Nat.card_congr e, ULogSourceObliviousSemanticAcceptance.cutoff_card]
  exact large_cutoff_count M p x htime (budget M p x) (Nat.le_refl _)

theorem generated_margin_scanner_count_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    acceptingCount M x (2 ^ p.eval x.length) =
      Nat.card (ULogFiniteProgramZipperRunBridge.SemanticLeaves (program M p) (initial M p x)) ∧
    (∀ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) →
      w.length ≤ budget M p x) ∧
    (∀ w out, semanticRun (ULogSemantics.start (input M p x)) w = some out →
      w.length ≤ budget M p x) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x)) =
      if ULogTernaryGeneratedMarginLoop.deadline M p x + 3 ≤ T then
        ULogSemantics.machine.acceptingPaths
          (T - (ULogTernaryGeneratedMarginLoop.deadline M p x + 3))
          (liftConfig (ULogSourceObliviousBytecode.boundedProgram M) (scannerInitial M p x))
      else 0) ∧
    (∀ T, budget M p x ≤ T → acceptingCount M x (2 ^ p.eval x.length) =
      ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x))) :=
  ⟨input_polyBitTime M p, ordinary_count M p x htime,
    all_raw_length M p x htime, all_semantic_raw_length M p x htime,
    cutoff_count M p x, large_cutoff_count M p x htime⟩

theorem sharpEXP_compact_margin_scanner (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      StandardBitTime.PolyBitTime (input M p) ∧
      ∀ x, RunsAtMost M x (2 ^ p.eval x.length) ∧
        f x = Nat.card (ULogFiniteProgramZipperRunBridge.SemanticLeaves
          (program M p) (initial M p x)) ∧
        (∀ w out, semanticRun (ULogSemantics.start (input M p x)) w = some out →
          w.length ≤ budget M p x) ∧
        (∀ T, budget M p x ≤ T →
          f x = ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input M p x))) := by
  obtain ⟨ns, nt, M, p, _, hM⟩ := StandardMachineCanonicalCodes.sharpEXP_to_canonical f hf
  refine ⟨ns, nt, M, p, input_polyBitTime M p, ?_⟩
  intro x
  obtain ⟨htime, hcount⟩ := hM x
  exact ⟨htime, hcount.trans (ordinary_count M p x htime), all_semantic_raw_length M p x htime,
    fun T hT => hcount.trans (large_cutoff_count M p x htime T hT)⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCounts
