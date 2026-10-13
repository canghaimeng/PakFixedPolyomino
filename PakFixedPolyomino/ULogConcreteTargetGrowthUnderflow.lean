import PakFixedPolyomino.ULogBootstrapMicroPrefix

/-! Genuine selected target-state growth exhaustion: `remaining` exceeds the
actual allocated work cells, so the next grow RIGHT is stuck on a literal
empty finite suffix. -/

namespace PakFixedPolyomino.ULogConcreteTargetGrowthUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper applyAction)

def targetPath (remaining : Nat) (corridor : List Tape) : List Tape :=
  List.replicate (remaining - 1) (ulogCore codeZero) ++
    ulogCore codeOne :: corridor

def start (remaining done available : Nat)
    (corridor left : List Tape) : Result :=
  .running .actionTarget
    ⟨left, ulogCore codeZero,
      targetScanPath (targetPath remaining corridor) done ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate available MStarConcreteAlphabet.work⟩

/-- Reachable growSep configuration after `available` actual growth rounds. -/
def penultimate (remaining done : Nat)
    (corridor left : List Tape) : Result :=
  .running (.actionPhase .targetGrowSep)
    ⟨ulogCore stateMark ::
        (targetScanPath (targetPath remaining corridor) done).reverse ++
          ulogCore targetMark :: left,
      ulogCore stateSep, []⟩

def reachedPenultimate (remaining done available : Nat)
    (corridor left : List Tape) : Result :=
  penultimate (remaining - available) (done + available) corridor
    (List.replicate available (ulogCore codeZero) ++ left)

def fuelBound (remaining done available : Nat) (corridor : List Tape) : Nat :=
  20 * (remaining + done + corridor.length + available + 2) * (available + 1)

theorem targetPath_cons {remaining : Nat} (hrem : 0 < remaining)
    (corridor : List Tape) :
    targetPath (remaining + 1) corridor =
      ulogCore codeZero :: targetPath remaining corridor := by
  cases remaining with
  | zero => cases hrem
  | succ n => simp [targetPath, List.replicate_succ]

theorem targetPath_ne_nil (remaining : Nat) (corridor : List Tape) :
    targetPath remaining corridor ≠ [] := by
  simp [targetPath]

theorem scanPath_length {remaining : Nat} (hrem : 0 < remaining)
    (done : Nat) (corridor : List Tape) :
    (targetScanPath (targetPath remaining corridor) done).length =
      remaining + done + corridor.length := by
  simp [targetScanPath, targetPath]; omega

theorem not_cycleStart_seek :
    State.actionPhase .targetSeekState ≠ .cycleStart := by intro h; cases h

theorem not_cycleStart_return :
    State.actionPhase .targetReturning ≠ .cycleStart := by intro h; cases h

theorem start_outside (remaining done available : Nat)
    (corridor left : List Tape) :
    preChoiceResult (start remaining done available corridor left) = false :=
  rfl

theorem targetGrowSep_rule :
    program.rule (.actionPhase .targetGrowSep) (ulogCore stateSep) 0 =
      some (go (ulogCore stateOne) (.actionPhase .targetGrowPlaceSep) .right) := by
  simp [program, rule, deterministicStep]

theorem targetGrowSep_empty_stuck (left : List Tape) :
    oneStep (.running (.actionPhase .targetGrowSep)
      ⟨left, ulogCore stateSep, []⟩) = .stuck := by
  simp [oneStep, targetGrowSep_rule, applyAction, go]

theorem validStepAt_targetGrowSep_empty (left : List Tape) :
    validStepAt 0 (.running (.actionPhase .targetGrowSep)
      ⟨left, ulogCore stateSep, []⟩) = some .stuck := by
  simp [validStepAt, targetGrowSep_rule, oneStepAt, applyAction, go]

/-- One certified grow round, with explicit physical step count. -/
def stopFree_oneGrow {remaining : Nat} (hrem : 0 < remaining)
    (done available : Nat)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    StopFreeValidZeroRun
      (2 * (targetScanPath (targetPath (remaining + 1) corridor) done).length + 7)
      (start (remaining + 1) done (available + 1) corridor left)
      (start remaining (done + 1) available corridor
        (ulogCore codeZero :: left)) := by
  let tail := List.replicate available MStarConcreteAlphabet.work
  let path := targetPath (remaining + 1) corridor
  let scanPath := targetScanPath path done
  let returnPath := targetGrowReturnPath scanPath
  have hpath : path ≠ [] := targetPath_ne_nil (remaining + 1) corridor
  have hsafeP : TargetRoundCorridorSafe path :=
    targetCodeCorridor_round_safe remaining corridor hsafe
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases scanPath <;> simp [beforeRightPath, actionTarget_zero]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hseek := stopFree_rightPath_of (.actionPhase .targetSeekState)
    not_cycleStart_seek scanPath (by
      intro x hx l y r
      by_cases hm : x = ulogCore stateMark
      · subst x; exact targetSeekState_mark l y r
      · have h := targetScanPath_seek_safe path done hsafeP hx
        exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
    (ulogCore targetMark :: left) (ulogCore stateOne)
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)
  have hone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetGrowSep)
        ⟨ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          ulogCore stateSep, MStarConcreteAlphabet.work :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        targetSeekState_one
          (scanPath.reverse ++ ulogCore targetMark :: left)
          (ulogCore stateSep) (MStarConcreteAlphabet.work :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hsep : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetGrowSep)
        ⟨ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          ulogCore stateSep, MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetGrowPlaceSep)
        ⟨ulogCore stateOne :: ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          MStarConcreteAlphabet.work, tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetGrowSep_step
        (ulogCore stateMark :: scanPath.reverse ++ ulogCore targetMark :: left)
        MStarConcreteAlphabet.work tail
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetGrowPlaceSep)
        ⟨ulogCore stateOne :: ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          MStarConcreteAlphabet.work, tail⟩)
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [returnPath, targetGrowReturnPath, beforeLeftPath] using
        targetGrowPlaceSep_step
          (ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left)
          (ulogCore stateOne) tail
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hreturn := stopFree_leftPath_of (.actionPhase .targetReturning)
    not_cycleStart_return returnPath (by
      intro x hx l y r
      have h := targetGrowReturnPath_safe path done hsafeP (by
        simpa [returnPath, scanPath] using hx)
      exact targetReturning_pass x h.1 h.2 l y r)
    left (ulogCore targetMark) (ulogCore stateSep :: tail)
  have hdone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetReturning)
        (afterLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hrev : returnPath.reverse =
          path ++ List.replicate (done + 1) (ulogCore stateMark) ++
            [ulogCore stateOne] := by
        simp [returnPath, targetGrowReturnPath, scanPath, targetScanPath,
          List.reverse_append, List.replicate_succ']
      rw [show afterLeftPath returnPath left (ulogCore targetMark)
            (ulogCore stateSep :: tail) =
          ⟨left, ulogCore targetMark,
            path ++ List.replicate (done + 1) (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
          simp [afterLeftPath, hrev]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.replicate_succ] using
            targetReturning_mark left x
              (xs ++ List.replicate (done + 1) (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hall :=
    (((((hstart.append hseek).append hone).append hsep).append hplace).append
      hreturn).append hdone
  have hn : 1 + scanPath.length + 1 + 1 + 1 + returnPath.length + 1 =
      2 * scanPath.length + 7 := by
    simp [returnPath, targetGrowReturnPath]; omega
  have hsrc : start (remaining + 1) done (available + 1) corridor left =
      .running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail⟩ := by
    simp [start, path, scanPath, tail, List.replicate_succ]
  have hdst : start remaining (done + 1) available corridor
        (ulogCore codeZero :: left) =
      .running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simp [start, beforeRightPath, targetPath_cons hrem, path, targetScanPath,
      tail, List.replicate_succ]
  have hn' : 2 * (targetScanPath (targetPath (remaining + 1) corridor) done).length + 7 =
      1 + scanPath.length + 1 + 1 + 1 + returnPath.length + 1 := by
    change 2 * scanPath.length + 7 = _
    exact hn.symm
  rw [hsrc, hdst, hn']
  exact hall

def stopFree_grows (remaining done available : Nat)
    (hgt : available < remaining)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    Σ n, PProd (n ≤ (2 * (remaining + done + corridor.length) + 7) * available)
      (StopFreeValidZeroRun n
        (start remaining done available corridor left)
        (start (remaining - available) (done + available) 0 corridor
          (List.replicate available (ulogCore codeZero) ++ left))) := by
  induction available generalizing remaining done left with
  | zero =>
      refine ⟨0, ⟨Nat.le_refl 0, ?_⟩⟩
      simpa using
        ({ valid := ValidZeroRun.nil (start remaining done 0 corridor left)
           stop_free := fun m hm => (Nat.not_lt_zero m hm).elim } :
          StopFreeValidZeroRun 0
            (start remaining done 0 corridor left)
            (start remaining done 0 corridor left))
  | succ available ih =>
      have hrem : 0 < remaining - 1 := by omega
      have hgt' : available < remaining - 1 := by omega
      have hround := stopFree_oneGrow hrem done available corridor hsafe left
      have hsrc : remaining - 1 + 1 = remaining := by omega
      have hround' : StopFreeValidZeroRun
          (2 * (targetScanPath (targetPath remaining corridor) done).length + 7)
          (start remaining done (available + 1) corridor left)
          (start (remaining - 1) (done + 1) available corridor
            (ulogCore codeZero :: left)) := by
        simpa [hsrc] using hround
      obtain ⟨b, ⟨hb, htail⟩⟩ :=
        ih (remaining - 1) (done + 1) hgt' (ulogCore codeZero :: left)
      have htail' : StopFreeValidZeroRun b
          (start (remaining - 1) (done + 1) available corridor
            (ulogCore codeZero :: left))
          (start (remaining - (available + 1)) (done + (available + 1)) 0 corridor
            (List.replicate (available + 1) (ulogCore codeZero) ++ left)) := by
        have hre : remaining - 1 - available = remaining - (available + 1) := by omega
        have hdo : done + 1 + available = done + (available + 1) := by omega
        simpa [hre, hdo, List.replicate_succ'] using htail
      have hlen := scanPath_length (by omega : 0 < remaining) done corridor
      have hL : remaining - 1 + (done + 1) + corridor.length =
          remaining + done + corridor.length := by omega
      have hb' : b ≤ (2 * (remaining + done + corridor.length) + 7) * available := by
        rw [← hL]; exact hb
      have hbound :
          2 * (targetScanPath (targetPath remaining corridor) done).length + 7 + b ≤
            (2 * (remaining + done + corridor.length) + 7) * (available + 1) := by
        rw [hlen]
        calc
          2 * (remaining + done + corridor.length) + 7 + b
              ≤ 2 * (remaining + done + corridor.length) + 7 +
                  (2 * (remaining + done + corridor.length) + 7) * available :=
                Nat.add_le_add_left hb' _
          _ = (2 * (remaining + done + corridor.length) + 7) * (available + 1) := by
                ring
      exact ⟨_, ⟨hbound, hround'.append htail'⟩⟩

def stopFree_finalScan {remaining : Nat} (hrem : 0 < remaining) (done : Nat)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    StopFreeValidZeroRun
      ((targetScanPath (targetPath remaining corridor) done).length + 2)
      (start remaining done 0 corridor left)
      (penultimate remaining done corridor left) := by
  let path := targetPath remaining corridor
  let scanPath := targetScanPath path done
  have hsafeP : TargetRoundCorridorSafe path :=
    targetCodeCorridor_round_safe (remaining - 1) corridor hsafe
  have hne : scanPath ≠ [] := by simp [scanPath, targetScanPath, path, targetPath]
  have hstart : StopFreeValidZeroRun 1
      (start remaining done 0 corridor left)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne) [ulogCore stateSep])) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hsp : scanPath with
      | nil => exact (hne hsp).elim
      | cons x xs =>
          simpa [start, scanPath, path, hsp, beforeRightPath] using
            actionTarget_zero left x
              (xs ++ ulogCore stateOne :: [ulogCore stateSep])
    · simp [start, IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hseek := stopFree_rightPath_of (.actionPhase .targetSeekState)
    not_cycleStart_seek scanPath (by
      intro x hx l y r
      by_cases hm : x = ulogCore stateMark
      · subst x; exact targetSeekState_mark l y r
      · have h := targetScanPath_seek_safe path done hsafeP hx
        exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
    (ulogCore targetMark :: left) (ulogCore stateOne) [ulogCore stateSep]
  have hone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne) [ulogCore stateSep]))
      (penultimate remaining done corridor left) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, penultimate, scanPath, path] using
        targetSeekState_one
          (scanPath.reverse ++ ulogCore targetMark :: left)
          (ulogCore stateSep) []
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hall := (hstart.append hseek).append hone
  have hn : (targetScanPath (targetPath remaining corridor) done).length + 2 =
      1 + scanPath.length + 1 := by
    simp [path, scanPath]; omega
  rw [hn]
  exact hall

def stopFree_to_stuck (remaining done available : Nat)
    (hgt : available < remaining)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    Σ n, PProd (n ≤ fuelBound remaining done available corridor)
      (StopFreeValidZeroRun n
        (start remaining done available corridor left) .stuck) := by
  have hrem : 0 < remaining - available := by omega
  obtain ⟨a, ⟨ha, hgrows⟩⟩ :=
    stopFree_grows remaining done available hgt corridor hsafe left
  have hscan := stopFree_finalScan hrem (done + available) corridor hsafe
    (List.replicate available (ulogCore codeZero) ++ left)
  have hstuck : StopFreeValidZeroRun 1
      (reachedPenultimate remaining done available corridor left) .stuck := by
    apply StopFreeValidZeroRun.one
    · simpa [reachedPenultimate, penultimate] using
        validStepAt_targetGrowSep_empty
          (ulogCore stateMark ::
            (targetScanPath
              (targetPath (remaining - available) corridor)
              (done + available)).reverse ++
              ulogCore targetMark ::
                (List.replicate available (ulogCore codeZero) ++ left))
    · simp [reachedPenultimate, penultimate, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hall := (hgrows.append hscan).append hstuck
  have hlen := scanPath_length hrem (done + available) corridor
  refine ⟨a + (targetScanPath (targetPath (remaining - available) corridor)
      (done + available)).length + 2 + 1, ⟨?_, hall⟩⟩
  · rw [hlen]
    have hsum : remaining - available + (done + available) + corridor.length =
        remaining + done + corridor.length := by omega
    rw [hsum]
    set L := remaining + done + corridor.length
    have h1 : a + L + 3 ≤ (2 * L + 7) * (available + 1) := by
      have : (2 * L + 7) * available + L + 3 ≤ (2 * L + 7) * (available + 1) := by
        simp [Nat.mul_add]; omega
      omega
    have h2 : (2 * L + 7) * (available + 1) ≤
        fuelBound remaining done available corridor := by
      simp only [fuelBound]
      exact Nat.mul_le_mul_right _ (by omega)
    have hfuel : a + L + 3 ≤ fuelBound remaining done available corridor :=
      h1.trans h2
    have : a + L + 2 + 1 = a + L + 3 := by omega
    rw [this]
    exact hfuel

theorem run_to_stuck (remaining done available : Nat)
    (hgt : available < remaining)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    ∃ fuel, fuel ≤ fuelBound remaining done available corridor ∧
      ValidZeroRun fuel (start remaining done available corridor left) .stuck ∧
      (∀ m, m < fuel →
        ¬ IsConcreteCycleStop (run m (start remaining done available corridor left))) ∧
      run fuel (start remaining done available corridor left) = .stuck := by
  obtain ⟨n, ⟨hn, hsf⟩⟩ :=
    stopFree_to_stuck remaining done available hgt corridor hsafe left
  exact ⟨n, hn, hsf.valid, hsf.stop_free, hsf.valid.eq_run⟩

theorem no_choice_before {n : Nat} {start finish : Result}
    (valid : ValidZeroRun n start finish)
    (noStop : ∀ m, m < n → ¬ IsConcreteCycleStop (run m start))
    (outside : preChoiceResult start = false) :
    ∀ m, m < n → ¬ IsConcreteChoice (run m start) := by
  have allOutside := outside_before_boundary valid noStop outside
  intro m hm choice
  have current := allOutside m (Nat.le_of_lt hm)
  cases h : run m start with
  | accepted z => simp [h, IsConcreteChoice] at choice
  | rejected => simp [h, IsConcreteChoice] at choice
  | stuck => simp [h, IsConcreteChoice] at choice
  | running q z =>
      have hq : q = .chooseSlot := by cases q <;> simp_all [h, IsConcreteChoice]
      simp [h, hq, preChoiceResult, preChoice] at current

theorem no_accepting_path (remaining done available : Nat)
    (hgt : available < remaining)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath (start remaining done available corridor left) labels
      (.accepted tape) → False := by
  intro raw
  obtain ⟨n, ⟨_, hsf⟩⟩ :=
    stopFree_to_stuck remaining done available hgt corridor hsafe left
  have noChoice :=
    no_choice_before hsf.valid hsf.stop_free
      (start_outside remaining done available corridor left)
  obtain ⟨rest, _, fromPen⟩ :=
    zero_prefix_of_micro_accepting hsf.valid noChoice raw
  have halted := microPath_halted_start fromPen (by rfl)
  cases halted.2

theorem reachedPenultimate_oneStep (remaining done available : Nat)
    (corridor left : List Tape) :
    oneStep (reachedPenultimate remaining done available corridor left) = .stuck := by
  simpa [reachedPenultimate, penultimate] using targetGrowSep_empty_stuck _

theorem target_growth_underflow_spec
    (remaining done available : Nat)
    (hgt : available < remaining)
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left : List Tape) :
    (∃ fuel, fuel ≤ fuelBound remaining done available corridor ∧
      ValidZeroRun fuel (start remaining done available corridor left) .stuck ∧
      (∀ m, m < fuel →
        ¬ IsConcreteCycleStop
            (run m (start remaining done available corridor left))) ∧
      run fuel (start remaining done available corridor left) = .stuck) ∧
    oneStep (reachedPenultimate remaining done available corridor left) = .stuck ∧
    (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
      ConcreteMicroPath (start remaining done available corridor left) labels
        (.accepted tape) → False) :=
  ⟨run_to_stuck remaining done available hgt corridor hsafe left,
    reachedPenultimate_oneStep remaining done available corridor left,
    no_accepting_path remaining done available hgt corridor hsafe left⟩

end PakFixedPolyomino.ULogConcreteTargetGrowthUnderflow
