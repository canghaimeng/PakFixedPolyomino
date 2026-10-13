import PakFixedPolyomino.PakULogGeneralCapacityUnderCapacity

/-!
# Turning a bootstrap underflow ledger into a no-accept theorem

The machine may become stuck only after a long deterministic prefix.  The
lemma below keeps the quantifiers honest: a certified bootstrap-only prefix
rules out an earlier cycle boundary, while absorption of `stuck` rules out a
later one.
-/

namespace PakFixedPolyomino.PakULogGeneralCapacityUnderCapacityNoAccept

open PakOuterULogReflection
open PakULogGeneralCapacityBootstrapFirstHit
open PakULogGeneralCapacityUnderCapacity

abbrev Result := ULogBootstrapExecution.Result
abbrev Zipper := MStarParserExecution.Zipper ULogProgram.Tape

/-- A bootstrap-controlled penultimate iterate supplies the whole strict
bootstrap prefix by reverse control closure. -/
theorem bootstrapRunPrefix_of_penultimate
    (start : Result) (steps : ℕ) (hpositive : 0 < steps)
    (hpenultimate : IsBootstrapRunning
      (ULogBootstrapExecution.run (steps - 1) start)) :
    BootstrapRunPrefix start steps := by
  cases hrun : ULogBootstrapExecution.run (steps - 1) start with
  | accepted z => simp [hrun, IsBootstrapRunning] at hpenultimate
  | rejected => simp [hrun, IsBootstrapRunning] at hpenultimate
  | stuck => simp [hrun, IsBootstrapRunning] at hpenultimate
  | running q z =>
      rw [hrun] at hpenultimate
      have hvalid := ULogBootstrapExecution.validZeroRun_of_run_eq_running hrun
      intro m hm
      exact bootstrapRunPrefix_le_of_validZeroRun_finish_bootstrap
        hvalid hpenultimate m (by omega)

/-- If the deterministic zero-slot run is bootstrap-controlled until it
becomes stuck, no genuine labelled accepting micro-history can start there. -/
theorem no_acceptingMicroPath_of_bootstrapPrefix_run_stuck
    (start : Result) (steps : ℕ)
    (hstuck : ULogBootstrapExecution.run steps start = .stuck)
    (hprefix : BootstrapRunPrefix start steps)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath start slots
      (.accepted acceptedZ)) : False := by
  cases start with
  | accepted z => simp [ULogBootstrapExecution.run_accepted] at hstuck
  | rejected => simp [ULogBootstrapExecution.run] at hstuck
  | stuck =>
      cases micro with
      | cons start next finish slot rest hhead tail =>
          simp [ULogBootstrapExecution.validStepAt] at hhead
  | running q z =>
      have hbootStart := hprefix 0 (by
        by_contra hzero
        have : steps = 0 := Nat.eq_zero_of_not_pos hzero
        subst steps
        simp [ULogBootstrapExecution.run] at hstuck)
      rcases hbootStart with ⟨q0, z0, hzero, hboot0⟩
      simp only [ULogBootstrapExecution.run] at hzero
      have hq : q = q0 := by injection hzero
      have hz : z = z0 := by injection hzero
      subst q0
      subst z0
      rcases bootstrap_path_firstCycleStart q z slots acceptedZ hboot0 micro with
        ⟨cycleZ, hit, rest, suffix, hphysical⟩
      by_cases hlt : hit.steps < steps
      · rcases hprefix hit.steps hlt with ⟨qb, zb, hrun, hboot⟩
        have hhitRun := hit.valid.eq_run
        rw [hrun] at hhitRun
        have hqcycle : qb = ULogControl.State.cycleStart := by
          injection hhitRun
        exact bootstrap_ne_cycleStart hboot hqcycle
      · have hle : steps ≤ hit.steps := Nat.le_of_not_gt hlt
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        have hhitRun := hit.valid.eq_run
        rw [hk, ULogBootstrapExecution.run_add, hstuck] at hhitRun
        simp [ULogBootstrapExecution.run] at hhitRun

/-- Convenient underflow form: an exact stuck ledger and one literal
bootstrap penultimate state already exclude every labelled accepting path. -/
theorem no_acceptingMicroPath_of_penultimate_run_stuck
    (start : Result) (steps : ℕ) (hpositive : 0 < steps)
    (hstuck : ULogBootstrapExecution.run steps start = .stuck)
    (hpenultimate : IsBootstrapRunning
      (ULogBootstrapExecution.run (steps - 1) start))
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath start slots
      (.accepted acceptedZ)) : False :=
  no_acceptingMicroPath_of_bootstrapPrefix_run_stuck start steps hstuck
    (bootstrapRunPrefix_of_penultimate start steps hpositive hpenultimate)
    slots acceptedZ micro

def zeroUnderflowFuel (x : ConcretePakSide.Word) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + x.length + 3

def oneUnderflowFuel (x : ConcretePakSide.Word)
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      payloadClockNoWorkspaceFuel input padding

def shortUnderflowFuel (x : ConcretePakSide.Word)
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (k : ℕ) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      PakULogBootstrapExplicitFuel.payloadClockFuel input padding + (k + 2)

def emptySixUnderflowFuel (x : ConcretePakSide.Word)
    (rules : List ULogBytecode.RuleCode) (padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
        (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
          (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3)

theorem no_acceptingMicroPath_capacity_zero
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 0))
      slots (.accepted acceptedZ)) : False := by
  apply no_acceptingMicroPath_of_penultimate_run_stuck _
    (zeroUnderflowFuel x) _
    (run_generalCapacity_zero_stuck x rules input padding hword)
    (run_generalCapacity_zero_penultimate x rules input padding hword)
    slots acceptedZ micro
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  unfold zeroUnderflowFuel
  omega

theorem no_acceptingMicroPath_capacity_one
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 1))
      slots (.accepted acceptedZ)) : False := by
  apply no_acceptingMicroPath_of_penultimate_run_stuck _
    (oneUnderflowFuel x rules input padding) _
    (run_generalCapacity_one_stuck x rules input padding hword)
    (run_generalCapacity_one_penultimate x rules input padding hword)
    slots acceptedZ micro
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  unfold oneUnderflowFuel
  omega

theorem no_acceptingMicroPath_short_capacity
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (k : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) (hk : k < 4)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x (2 + k)))
      slots (.accepted acceptedZ)) : False := by
  apply no_acceptingMicroPath_of_penultimate_run_stuck _
    (shortUnderflowFuel x rules input padding k) _
    (run_generalCapacity_shortWorkspace_stuck x rules input padding k hword hk)
    (run_generalCapacity_shortWorkspace_penultimate x rules input padding k hword hk)
    slots acceptedZ micro
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  unfold shortUnderflowFuel
  omega

theorem no_acceptingMicroPath_empty_capacity_six
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload [] padding)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 6))
      slots (.accepted acceptedZ)) : False := by
  apply no_acceptingMicroPath_of_penultimate_run_stuck _
    (emptySixUnderflowFuel x rules padding) _
    (run_generalCapacity_empty_six_stuck x rules padding hword)
    (run_generalCapacity_empty_six_penultimate x rules padding hword)
    slots acceptedZ micro
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  unfold emptySixUnderflowFuel
  omega

/-- Any actual accepting history from a general-capacity `qStart` source
forces the exact physical workspace threshold.  All seven possible
under-capacity values are discharged by the literal stuck ledgers above. -/
theorem bootstrapWorkspaceOverhead_le_of_acceptingMicroPath
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (slots : List (Fin 2)) (acceptedZ : Zipper)
    (micro : ULogBootstrapExecution.ConcreteMicroPath
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
          x physicalCapacity)) slots (.accepted acceptedZ)) :
    PakULogGeneralCapacityBootstrap.bootstrapWorkspaceOverhead input ≤
      physicalCapacity := by
  by_contra hnot
  have hlt : physicalCapacity <
      PakULogGeneralCapacityBootstrap.bootstrapWorkspaceOverhead input :=
    Nat.lt_of_not_ge hnot
  cases input with
  | nil =>
      change physicalCapacity < 7 at hlt
      interval_cases physicalCapacity
      · exact no_acceptingMicroPath_capacity_zero x rules [] padding hword
          slots acceptedZ micro
      · exact no_acceptingMicroPath_capacity_one x rules [] padding hword
          slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules [] padding 0 hword
          (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules [] padding 1 hword
          (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules [] padding 2 hword
          (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules [] padding 3 hword
          (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_empty_capacity_six x rules padding hword
          slots acceptedZ micro
  | cons b bs =>
      change physicalCapacity < 6 at hlt
      interval_cases physicalCapacity
      · exact no_acceptingMicroPath_capacity_zero x rules (b :: bs) padding
          hword slots acceptedZ micro
      · exact no_acceptingMicroPath_capacity_one x rules (b :: bs) padding
          hword slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules (b :: bs) padding 0
          hword (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules (b :: bs) padding 1
          hword (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules (b :: bs) padding 2
          hword (by omega) slots acceptedZ micro
      · exact no_acceptingMicroPath_short_capacity x rules (b :: bs) padding 3
          hword (by omega) slots acceptedZ micro

end PakFixedPolyomino.PakULogGeneralCapacityUnderCapacityNoAccept
