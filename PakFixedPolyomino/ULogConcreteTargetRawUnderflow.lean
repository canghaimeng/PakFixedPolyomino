import PakFixedPolyomino.ULogConcreteTargetGrowthReachableUnderflow

/-! Actual target rewrite before existing state cells are consumed. The
number of requested new state cells and number of available work cells are
separate. A literal shortage cannot accept on ANY physical labelled path.
This selected rewrite stage is not a complete low-capacity cycle theorem. -/
namespace PakFixedPolyomino.ULogConcreteTargetRawUnderflow
open ULogAlphabet ULogProgram ULogBootstrapExecution ULogConcreteChoiceBarrier
open ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)

def consumeStart (remaining growth done available : Nat)
    (corridor left : List Tape) : Result :=
  .running .actionTarget
    ⟨left, ulogCore codeZero,
      targetScanPath (ULogConcreteTargetGrowthUnderflow.targetPath (remaining + growth) corridor) done ++
        List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate available MStarConcreteAlphabet.work⟩

theorem existing_round_ticks (path : List Tape) (hne : path ≠ []) (done : Nat)
    (hsafe : TargetRoundCorridorSafe path) (left rest : List Tape) :
    (stopFree_targetRoundExisting path hne done hsafe left rest).1 =
      2 * (path.length + done) + 3 := by
  change 1 + (targetScanPath path done).length + 1 +
    (targetScanPath path done).reverse.length + 1 = _
  simp [targetScanPath]; omega

def consume_existing (remaining growth done available : Nat)
    (hg : 0 < growth) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape) :
    Σ n, PProd
      (n ≤ (2 * (remaining + growth + done + corridor.length) + 3) * remaining)
      (StopFreeValidZeroRun n (consumeStart remaining growth done available corridor left)
        (ULogConcreteTargetGrowthUnderflow.start growth (done + remaining) available corridor
          (List.replicate remaining (ulogCore codeZero) ++ left))) := by
  induction remaining generalizing done left with
  | zero =>
      refine ⟨0, ⟨Nat.le_refl 0, ?_⟩⟩
      simpa [consumeStart, ULogConcreteTargetGrowthUnderflow.start] using
        ({ valid := ValidZeroRun.nil (ULogConcreteTargetGrowthUnderflow.start growth done available corridor left)
           stop_free := fun m hm => (Nat.not_lt_zero m hm).elim } :
          StopFreeValidZeroRun 0 (ULogConcreteTargetGrowthUnderflow.start growth done available corridor left)
            (ULogConcreteTargetGrowthUnderflow.start growth done available corridor left))
  | succ remaining ih =>
      let path := ULogConcreteTargetGrowthUnderflow.targetPath (remaining + 1 + growth) corridor
      have hne : path ≠ [] := ULogConcreteTargetGrowthUnderflow.targetPath_ne_nil _ _
      have hr : TargetRoundCorridorSafe path :=
        targetCodeCorridor_round_safe (remaining + 1 + growth - 1) corridor hsafe
      let rest := List.replicate remaining (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work
      let step := stopFree_targetRoundExisting path hne done hr left rest
      have hround : StopFreeValidZeroRun step.1
          (consumeStart (remaining + 1) growth done available corridor left)
          (consumeStart remaining growth (done + 1) available corridor
            (ulogCore codeZero :: left)) := by
        have hs : remaining + 1 + growth = (remaining + growth) + 1 := by omega
        have hp : path = ulogCore codeZero ::
            ULogConcreteTargetGrowthUnderflow.targetPath (remaining + growth) corridor := by
          dsimp [path]; rw [hs]
          exact ULogConcreteTargetGrowthUnderflow.targetPath_cons (by omega) corridor
        have hp' : ULogConcreteTargetGrowthUnderflow.targetPath
            (remaining + 1 + growth) corridor = ulogCore codeZero ::
              ULogConcreteTargetGrowthUnderflow.targetPath (remaining + growth) corridor := hp
        simpa [consumeStart, rest, beforeRightPath, path, hp', targetScanPath,
          List.replicate_succ, List.append_assoc] using step.2
      obtain ⟨b, ⟨hb, htail⟩⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have htail' : StopFreeValidZeroRun b
          (consumeStart remaining growth (done + 1) available corridor
            (ulogCore codeZero :: left))
          (ULogConcreteTargetGrowthUnderflow.start growth (done + (remaining + 1)) available corridor
            (List.replicate (remaining + 1) (ulogCore codeZero) ++ left)) := by
        have hn : done + 1 + remaining = done + (remaining + 1) := by omega
        simpa [hn, List.replicate_succ'] using htail
      refine ⟨step.1 + b, ⟨?_, hround.append htail'⟩⟩
      have ht := existing_round_ticks path hne done hr left rest
      have hl : path.length = remaining + 1 + growth + corridor.length := by
        simpa [path, targetScanPath] using
          (ULogConcreteTargetGrowthUnderflow.scanPath_length
            (remaining := remaining + 1 + growth) (by omega) 0 corridor)
      have he : remaining + growth + (done + 1) + corridor.length =
          remaining + 1 + growth + done + corridor.length := by omega
      rw [he] at hb
      rw [ht, hl]
      calc
        2 * (remaining + 1 + growth + corridor.length + done) + 3 + b
            ≤ 2 * (remaining + 1 + growth + corridor.length + done) + 3 +
              (2 * (remaining + 1 + growth + done + corridor.length) + 3) * remaining := by
                omega
        _ = (2 * (remaining + 1 + growth + done + corridor.length) + 3) *
              (remaining + 1) := by ring

def fuelBound (target current capacity : Nat) (corridor : List Tape) : Nat :=
  (2 * (target + corridor.length) + 3) * current +
    ULogConcreteTargetGrowthUnderflow.fuelBound (target - current) current (capacity - current) corridor

theorem raw_start_eq (target current capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < target) (corridor left : List Tape) :
    targetRawStart target current corridor left
        (List.replicate (capacity - current) MStarConcreteAlphabet.work) =
      consumeStart current (target - current) 0 (capacity - current) corridor left := by
  have hp : 0 < target := by omega
  have he : current + (target - current) = target := by omega
  cases target with
  | zero => omega
  | succ target =>
      simp [targetRawStart, consumeStart, ULogConcreteTargetGrowthUnderflow.targetPath, targetScanPath,
        he, List.append_assoc]

def stopFree_to_stuck (target current capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < target) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape) :
    Σ n, PProd (n ≤ fuelBound target current capacity corridor)
      (StopFreeValidZeroRun n
        (targetRawStart target current corridor left
          (List.replicate (capacity - current) MStarConcreteAlphabet.work)) .stuck) := by
  have hg : 0 < target - current := by omega
  have hgt : capacity - current < target - current := by omega
  obtain ⟨a, ⟨ha, hconsume⟩⟩ :=
    consume_existing current (target - current) 0 (capacity - current) hg corridor hsafe left
  obtain ⟨b, ⟨hb, hgrow⟩⟩ :=
    ULogConcreteTargetGrowthUnderflow.stopFree_to_stuck (target - current) current (capacity - current) hgt
      corridor hsafe (List.replicate current (ulogCore codeZero) ++ left)
  have hconsume' : StopFreeValidZeroRun a
      (targetRawStart target current corridor left
        (List.replicate (capacity - current) MStarConcreteAlphabet.work))
      (ULogConcreteTargetGrowthUnderflow.start (target - current) current (capacity - current) corridor
        (List.replicate current (ulogCore codeZero) ++ left)) := by
    rw [raw_start_eq target current capacity hc ht]
    simpa using hconsume
  refine ⟨a + b, ⟨?_, hconsume'.append hgrow⟩⟩
  have he : current + (target - current) + 0 + corridor.length =
      target + corridor.length := by omega
  rw [he] at ha
  unfold fuelBound
  omega

theorem no_accepting_path (target current capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < target) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath (targetRawStart target current corridor left
      (List.replicate (capacity - current) MStarConcreteAlphabet.work)) labels
      (.accepted tape) → False := by
  intro raw
  obtain ⟨n, ⟨_, hsf⟩⟩ := stopFree_to_stuck target current capacity hc ht corridor hsafe left
  have outside : preChoiceResult (targetRawStart target current corridor left
      (List.replicate (capacity - current) MStarConcreteAlphabet.work)) = false := by
    cases target <;> rfl
  have noChoice := ULogConcreteTargetGrowthUnderflow.no_choice_before hsf.valid hsf.stop_free outside
  obtain ⟨rest, _, after⟩ := zero_prefix_of_micro_accepting hsf.valid noChoice raw
  have halted := microPath_halted_start after (by rfl)
  cases halted.2

theorem target_raw_underflow_spec (target current capacity : Nat)
    (hc : current ≤ capacity) (ht : capacity < target) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape) :
    (∃ fuel, fuel ≤ fuelBound target current capacity corridor ∧
      ValidZeroRun fuel (targetRawStart target current corridor left
        (List.replicate (capacity - current) MStarConcreteAlphabet.work)) .stuck ∧
      (∀ m, m < fuel → ¬ IsConcreteCycleStop (run m
        (targetRawStart target current corridor left
          (List.replicate (capacity - current) MStarConcreteAlphabet.work)))) ∧
      run fuel (targetRawStart target current corridor left
        (List.replicate (capacity - current) MStarConcreteAlphabet.work)) = .stuck) ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath (targetRawStart target current corridor left
        (List.replicate (capacity - current) MStarConcreteAlphabet.work)) labels
        (.accepted tape) → False) := by
  constructor
  · obtain ⟨n, ⟨hn, hsf⟩⟩ := stopFree_to_stuck target current capacity hc ht corridor hsafe left
    exact ⟨n, hn, hsf.valid, hsf.stop_free, hsf.valid.eq_run⟩
  · exact no_accepting_path target current capacity hc ht corridor hsafe left

end PakFixedPolyomino.ULogConcreteTargetRawUnderflow
