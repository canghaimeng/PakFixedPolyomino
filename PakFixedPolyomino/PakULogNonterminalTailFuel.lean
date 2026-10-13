import PakFixedPolyomino.PakULogCycleResourceBound

/-!
# Explicit fuel for nonterminal `U_log` rule tails

The quantitative mismatch fold is common to every selected rule.  This file
first isolates the remaining matched-source/read prefix, ending at the actual
`actionWriteStart` configuration.  The target/move/cleanup tails can then be
bounded independently for the ten nonterminal branches (two target-size
directions times stay, internal-left/right, and boundary-left/right).

Every certificate below retains its literal `StopFreeValidZeroRun`; no length
is recovered from an erased reachability witness.
-/

namespace PakFixedPolyomino.PakULogNonterminalTailFuel

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution
open ULogBootstrapExecution
open PakULogCycleResourceBound

theorem choiceHead_readHeadNat_of_lt_three (n : ℕ) (h : n < 3) :
    choiceHead (readHeadNat n) = true := by
  interval_cases n <;> decide

theorem cursorCleanupProgramPrefix_length_le
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    (cursorCleanupProgramPrefix skip r).length ≤
      (ULogBytecode.encodeRules skip).length +
        (ULogBytecode.encodeRule r).length + 1 := by
  cases skip with
  | nil => simp [cursorCleanupProgramPrefix, ULogBytecode.encodeRules]
  | cons s ss =>
      have ht : (mismatchHistory sourceBoundary (s :: ss)).tail.length ≤
          (mismatchHistory sourceBoundary (s :: ss)).length := by
        cases h : mismatchHistory sourceBoundary (s :: ss) <;> simp
      have hh : (mismatchHistory sourceBoundary (s :: ss)).length =
          (ULogBytecode.encodeRules (s :: ss)).length :=
        mismatchHistory_length_eq_encodeRules sourceBoundary (s :: ss)
      calc
        (cursorCleanupProgramPrefix (s :: ss) r).length =
            (ULogBytecode.encodeRule r).length + 1 +
              (mismatchHistory sourceBoundary (s :: ss)).tail.length := by
          simp [cursorCleanupProgramPrefix, List.length_append,
            List.length_map]
          omega
        _ ≤ (ULogBytecode.encodeRule r).length + 1 +
              (mismatchHistory sourceBoundary (s :: ss)).length :=
          Nat.add_le_add_left ht _
        _ = (ULogBytecode.encodeRules (s :: ss)).length +
              (ULogBytecode.encodeRule r).length + 1 := by
          rw [hh]
          omega

/-- The part common to all matched nonterminal branches: decode the matching
source field and dispatch the matching read symbol, stopping exactly at the
write microprogram. -/
theorem ruleCursorMatched_actionWrite_bounded_radius
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime suffix : List Tape)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    {R : ℕ}
    (hsource : r.source ≤ R)
    (hsourceCorridor :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime).length ≤ R)
    (hreadCorridor :
      (encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 11 * R + 13)
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))) := by
  obtain ⟨sourceRun⟩ := ruleCursorSourceMatch_read_bounded_radius r.slot
    boundary hboundary r rs programToHead base (readHeadNat r.read) runtime
    suffix hcorridor hsource hsourceCorridor
  obtain ⟨readRun⟩ := sourceReadAtValid_actionWrite_bounded_radius r.slot
    r.source r.read r.action.write r.action.target boundary r.action.move
    hread hwrite base (cursorMatchedMovePath rs programToHead) runtime suffix
    hreadPath hreadCorridor
  refine ⟨
    { steps := sourceRun.steps + readRun.steps
      le_bound := ?_
      run := sourceRun.run.append readRun.run }⟩
  have hs := sourceRun.le_bound
  have hr := readRun.le_bound
  omega

/-! ## Stay cleanup -/

/-- The restoration pass crosses the clock/program word once to the left and
then crosses the pc/program pieces once to the right. -/
theorem restoreCycle_fuel_eq
    (pcPath : List Tape) (terminal : Tape)
    (programPath : List Tape) (outer : List Tape) (head : Tape)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: programPath).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe programPath)
    (hhead : choiceHead head = true) (right : List Tape) :
    (stopFree_restoreCycle pcPath terminal programPath outer head hclock hpc
      hterminal hprogram hhead right).1 =
      2 * pcPath.length + 2 * programPath.length + 5 := by
  simp [stopFree_restoreCycle]
  omega

/-- Exact literal fuel of the common stay cleanup. -/
theorem moveStay_cleanup_fuel_eq
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    (hhead : choiceHead head = true) :
    (stopFree_moveStay_cleanup programPrefix scanPath pcPath terminal outer
      head right hscan hclock hpc hterminal hprogram hhead).1 =
      2 * programPrefix.length + 3 * scanPath.length +
        2 * pcPath.length + 6 := by
  simp [stopFree_moveStay_cleanup, stopFree_moveStay,
    restoreCycle_fuel_eq]
  omega

/-- Radius form used by both target-at-most and target-at-least stay
branches.  The certificate is the actual cleanup run, not merely its number
of steps. -/
theorem moveStay_cleanup_bounded_radius
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    (hhead : choiceHead head = true) {R : ℕ}
    (hprogramPrefix : programPrefix.length ≤ R)
    (hscanPath : scanPath.length ≤ R)
    (hpcPath : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (7 * R + 6)
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer) head right))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          head, right⟩)) := by
  let run := stopFree_moveStay_cleanup programPrefix scanPath pcPath terminal
    outer head right hscan hclock hpc hterminal hprogram hhead
  refine ⟨
    { steps := run.1
      le_bound := ?_
      run := run.2 }⟩
  rw [show run.1 = 2 * programPrefix.length + 3 * scanPath.length +
      2 * pcPath.length + 6 by
    dsimp [run]
    exact moveStay_cleanup_fuel_eq programPrefix scanPath pcPath terminal outer
      head right hscan hclock hpc hterminal hprogram hhead]
  omega

/-! ## Target rewrite fuel atoms -/

theorem targetRoundExisting_fuel_eq
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hsafe : TargetRoundCorridorSafe path) (left stateRest : List Tape) :
    (stopFree_targetRoundExisting path hpath done hsafe left stateRest).1 =
      2 * (path.length + done) + 3 := by
  simp [stopFree_targetRoundExisting, targetScanPath]
  omega

theorem targetRoundGrow_fuel_eq
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hsafe : TargetRoundCorridorSafe path) (left tail : List Tape) :
    (stopFree_targetRoundGrow path hpath done hsafe left tail).1 =
      2 * (path.length + done) + 7 := by
  simp [stopFree_targetRoundGrow, targetScanPath, targetGrowReturnPath]
  omega

theorem targetFinishSeenOne_many_fuel_eq
    (done : ℕ) (left : List Tape) (terminal : Tape) (right : List Tape) :
    (stopFree_targetFinishSeenOne_many_core done left terminal right).1 =
      done + 1 := by
  simp [stopFree_targetFinishSeenOne_many_core]
  omega

theorem targetShrink_fuel_eq (extra : ℕ) (left tail : List Tape) :
    (stopFree_targetShrink extra left tail).1 = 2 * extra + 6 := by
  simp [stopFree_targetShrink]
  omega

/-- Choice-free quantitative fold of all existing-state target rounds. -/
theorem targetExistingZeros_bounded
    (remaining done extra : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Nonempty (BoundedStopFreeRun
      (remaining * (2 * (remaining + done + corridor.length) + 3))
      (targetExistingStart remaining done extra corridor left tail)
      (targetExistingDone remaining done extra corridor left tail)) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run := by
            simpa [targetExistingStart, targetExistingDone] using
              ({ valid := ValidZeroRun.nil _
                 stop_free := by intro m hm; simp at hm } :
                StopFreeValidZeroRun 0
                  (targetExistingStart 0 done extra corridor left tail)
                  (targetExistingStart 0 done extra corridor left tail)) }⟩
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      let round := stopFree_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining (ulogCore stateZero) ++
          List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      obtain ⟨tailRun⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have htail : StopFreeValidZeroRun tailRun.steps
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                List.replicate remaining (ulogCore stateZero) ++
                List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)))
          (targetExistingDone remaining (done + 1) extra corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetExistingStart, path, beforeRightPath,
            targetScanPath, List.replicate_succ, List.replicate_succ',
            List.append_assoc, Nat.add_assoc] using tailRun.run
      have htailJoin : StopFreeValidZeroRun tailRun.steps
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                (List.replicate remaining (ulogCore stateZero) ++
                  List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail))))
          (targetExistingDone remaining (done + 1) extra corridor
            (ulogCore codeZero :: left) tail) := by
        simpa only [List.append_assoc] using htail
      refine ⟨
        { steps := round.1 + tailRun.steps
          le_bound := ?_
          run := by
            have joined := round.2.append htailJoin
            simpa [targetExistingStart, targetExistingDone, path,
              targetScanPath, List.replicate_succ, List.replicate_succ',
              List.append_assoc, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using joined }⟩
      have hround : round.1 = 2 * (path.length + done) + 3 := by
        dsimp [round]
        exact targetRoundExisting_fuel_eq path hpath done
          (targetCodeCorridor_round_safe remaining corridor hsafe) left
          (List.replicate remaining (ulogCore stateZero) ++
            List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
      rw [hround]
      have ht := tailRun.le_bound
      simp [path] at ⊢
      nlinarith

/-- Quantitative fold of all workspace-growth target rounds. -/
theorem targetGrowZeros_bounded
    (remaining done : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Nonempty (BoundedStopFreeRun
      (remaining * (2 * (remaining + done + corridor.length) + 7))
      (targetGrowStart remaining done corridor left tail)
      (targetGrowDone remaining done corridor left tail)) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run := by
            simpa [targetGrowStart, targetGrowDone] using
              ({ valid := ValidZeroRun.nil _
                 stop_free := by intro m hm; simp at hm } :
                StopFreeValidZeroRun 0
                  (targetGrowStart 0 done corridor left tail)
                  (targetGrowStart 0 done corridor left tail)) }⟩
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      let round := stopFree_targetRoundGrow path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining MStarConcreteAlphabet.work ++ tail)
      obtain ⟨tailRun⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have htail : StopFreeValidZeroRun tailRun.steps
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate remaining MStarConcreteAlphabet.work ++
                    tail)))
          (targetGrowDone remaining (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetGrowStart, path, beforeRightPath, targetScanPath,
            List.replicate_succ, List.replicate_succ', List.append_assoc,
            Nat.add_assoc] using tailRun.run
      have htailJoin : StopFreeValidZeroRun tailRun.steps
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                (ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate remaining MStarConcreteAlphabet.work ++
                    tail))))
          (targetGrowDone remaining (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        simpa only [List.append_assoc] using htail
      refine ⟨
        { steps := round.1 + tailRun.steps
          le_bound := ?_
          run := by
            have joined := round.2.append htailJoin
            simpa [targetGrowStart, targetGrowDone, path, targetScanPath,
              List.replicate_succ, List.replicate_succ', List.append_assoc,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined }⟩
      have hround : round.1 = 2 * (path.length + done) + 7 := by
        dsimp [round]
        exact targetRoundGrow_fuel_eq path hpath done
          (targetCodeCorridor_round_safe remaining corridor hsafe) left
          (List.replicate remaining MStarConcreteAlphabet.work ++ tail)
      rw [hround]
      have ht := tailRun.le_bound
      simp [path] at ⊢
      nlinarith

/-- Quantitative fold of the existing-state cells consumed before a growing
target rewrite. -/
theorem targetConsumeState_bounded
    (remaining growth done : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Nonempty (BoundedStopFreeRun
      (remaining *
        (2 * (remaining + growth + done + corridor.length) + 3))
      (targetConsumeStart remaining growth done corridor left tail)
      (targetConsumeDone remaining growth done corridor left tail)) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run := by
            simpa [targetConsumeStart, targetConsumeDone] using
              ({ valid := ValidZeroRun.nil _
                 stop_free := by intro m hm; simp at hm } :
                StopFreeValidZeroRun 0
                  (targetConsumeStart 0 growth done corridor left tail)
                  (targetConsumeStart 0 growth done corridor left tail)) }⟩
  | succ remaining ih =>
      let path := List.replicate (growth + remaining) (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      let round := stopFree_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe (growth + remaining) corridor hsafe)
        left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail)
      let a := round.1
      have hroundFuel : a = 2 * (path.length + done) + 3 := by
        dsimp [a, round]
        exact targetRoundExisting_fuel_eq path hpath done
          (targetCodeCorridor_round_safe (growth + remaining) corridor hsafe)
          left
          (List.replicate remaining (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail)
      have hround := round.2
      dsimp [path] at hround
      obtain ⟨tailRun⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have hroundRun : StopFreeValidZeroRun a
          (targetConsumeStart (remaining + 1) growth done corridor left tail)
          (targetConsumeStart remaining growth (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining with
        | zero =>
            cases growth <;>
              simpa [targetConsumeStart, targetGrowStart, beforeRightPath,
                targetScanPath, List.replicate_succ, List.replicate_succ',
                List.cons_append, List.append_assoc, Nat.add_assoc] using
                hround
        | succ remaining =>
            have hcount : growth + (remaining + 1) =
                (growth + remaining) + 1 := by omega
            have hrepl :
                List.replicate (growth + (remaining + 1))
                    (ulogCore codeZero) =
                  ulogCore codeZero ::
                    List.replicate (growth + remaining)
                      (ulogCore codeZero) := by
              rw [hcount, List.replicate_succ]
            simpa [targetConsumeStart, targetGrowStart, beforeRightPath,
              targetScanPath, List.replicate_succ, List.replicate_succ',
              List.cons_append, List.append_assoc, Nat.add_assoc, hrepl] using
              hround
      refine ⟨
        { steps := a + tailRun.steps
          le_bound := ?_
          run := by
            have joined := hroundRun.append tailRun.run
            simpa [targetConsumeStart, targetConsumeDone, path,
              targetScanPath, List.replicate_succ, List.replicate_succ',
              List.cons_append, List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using joined }⟩
      rw [hroundFuel]
      have ht := tailRun.le_bound
      simp [path] at ⊢
      nlinarith

/-- Quantitative equal-target finish.  The witness is rebuilt from the
literal sweep pieces so its length does not pass through the old sigma-valued
wrapper. -/
theorem targetFinishEqual_bounded
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hdone : 2 ≤ done) (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Nonempty (BoundedStopFreeRun
      (2 * path.length + 2 * done + 3)
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateOne ::
            ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail)))) := by
  obtain ⟨k, hdoneEq⟩ : ∃ k, done = k + 2 := ⟨done - 2, by omega⟩
  let finishPath := targetFinishPath path done
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases finishPath <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan0 := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) (ulogCore stateMark)
    (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hscan : StopFreeValidZeroRun path.length
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [finishPath, targetFinishPath, hdoneEq, beforeRightPath,
          afterRightPath, hp, List.replicate_succ,
          List.append_assoc] using hscan0
  have hmark : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetFinishSeek_mark
        (path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateMark)
        (List.replicate k (ulogCore stateMark) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  let many0 := stopFree_targetFinishSeenOne_many_core k
    (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
    (ulogCore stateOne) (ulogCore stateSep :: tail)
  have hmany0 : StopFreeValidZeroRun (k + 1)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        ⟨List.replicate (k + 1) (ulogCore stateMark) ++
            (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left),
          ulogCore stateOne, ulogCore stateSep :: tail⟩) := by
    have hfuel : many0.1 = k + 1 := by
      dsimp [many0]
      exact targetFinishSeenOne_many_fuel_eq k
        (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateOne) (ulogCore stateSep :: tail)
    simpa only [hfuel, List.append_assoc, List.cons_append] using many0.2
  have hmany : StopFreeValidZeroRun (k + 1)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    have hmarks : List.replicate (k + 2) (ulogCore stateMark) =
        ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark) := by
      have hk : k + 2 = Nat.succ (Nat.succ k) := by omega
      rw [hk, List.replicate_succ, List.replicate_succ]
    have hfinishLeft :
        (ulogCore stateMark :: ulogCore stateMark ::
            List.replicate k (ulogCore stateMark)) ++
          (path.reverse ++ ulogCore targetBoundary :: left) =
        finishPath.reverse ++ ulogCore targetBoundary :: left := by
      simp [finishPath, targetFinishPath, hdoneEq, List.reverse_append,
        hmarks, List.append_assoc]
    rw [show List.replicate (k + 1) (ulogCore stateMark) ++
          (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left) =
        (ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark)) ++
            (path.reverse ++ ulogCore targetBoundary :: left) by
      simp [List.replicate_succ, List.append_assoc]] at hmany0
    rw [hfinishLeft] at hmany0
    simpa [afterRightPath] using hmany0
  have hrestoreStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath finishPath.reverse left (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : finishPath.reverse with
      | nil =>
          simpa [afterRightPath, beforeLeftPath, hr] using
            targetFinishMany_one_core left (ulogCore targetBoundary)
              (ulogCore stateSep :: tail)
      | cons x xs =>
          simpa [afterRightPath, beforeLeftPath, hr, List.append_assoc] using
            targetFinishMany_one_core
              (xs ++ ulogCore targetBoundary :: left) x
              (ulogCore stateSep :: tail)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hrestore := stopFree_leftPathMap_of
    (.actionPhase .targetRestoreState) (by decide) finishPath.reverse
    restoreTargetCell (by
      intro x hx l y r
      have hx' : x ∈ finishPath := by simpa using hx
      by_cases hm : x = ulogCore stateMark
      · subst x
        simpa [restoreTargetCell] using targetRestoreState_mark l y r
      · have h := targetFinishPath_restore_safe path done hsafe hx'
        simpa [restoreTargetCell, hm] using
          targetRestoreState_pass x hm h.1 h.2 l y r)
    left (ulogCore targetBoundary)
    (ulogCore stateOne :: ulogCore stateSep :: tail)
  have hmoveStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap finishPath.reverse restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hmap : finishPath.map restoreTargetCell =
          path ++ List.replicate done (ulogCore stateZero) := by
        simp [finishPath, targetFinishPath, List.map_append,
          restoreTargetCell_path path hsafe, restoreTargetCell]
      rw [show afterLeftPathMap finishPath.reverse restoreTargetCell left
            (ulogCore targetBoundary)
            (ulogCore stateOne :: ulogCore stateSep :: tail) =
          ⟨left, ulogCore targetBoundary,
            path ++ List.replicate done (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
        simp [afterLeftPathMap, hmap, List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.append_assoc] using
            targetRestoreState_boundary left x
              (xs ++ List.replicate done (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [afterLeftPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let joined := (((((hstart.append hscan).append hmark).append hmany).append
    hrestoreStart).append hrestore).append hmoveStart
  refine ⟨
    { steps := 1 + path.length + 1 + (k + 1) + 1 +
        finishPath.reverse.length + 1
      le_bound := ?_
      run := by
        simpa [joined, finishPath] using joined }⟩
  simp [finishPath, targetFinishPath, hdoneEq]
  omega

/-- Quantitative strictly-shorter target finish, including the erase/return
of the surplus unary state cells. -/
theorem targetFinishShorter_bounded
    (path : List Tape) (hpath : path ≠ []) (done extra : ℕ)
    (hdone : 2 ≤ done) (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Nonempty (BoundedStopFreeRun
      (2 * path.length + 2 * done + 2 * extra + 10)
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)))) := by
  obtain ⟨k, hdoneEq⟩ : ∃ k, done = k + 2 := ⟨done - 2, by omega⟩
  let finishPath := targetFinishPath path done
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases finishPath <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan0 := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) (ulogCore stateMark)
    (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
      ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: tail)
  have hscan : StopFreeValidZeroRun path.length
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [finishPath, targetFinishPath, hdoneEq, beforeRightPath,
          afterRightPath, hp, List.replicate_succ,
          List.append_assoc] using hscan0
  have hmark : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetFinishSeek_mark
        (path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateMark)
        (List.replicate k (ulogCore stateMark) ++
          ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  let many0 := stopFree_targetFinishSeenOne_many_core k
    (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
    (ulogCore stateZero)
    (List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hmany0 : StopFreeValidZeroRun (k + 1)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        ⟨List.replicate (k + 1) (ulogCore stateMark) ++
            (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left),
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    have hfuel : many0.1 = k + 1 := by
      dsimp [many0]
      exact targetFinishSeenOne_many_fuel_eq k
        (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateZero)
        (List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
    simpa only [hfuel, List.append_assoc, List.cons_append] using many0.2
  have hmany : StopFreeValidZeroRun (k + 1)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    have hmarks : List.replicate (k + 2) (ulogCore stateMark) =
        ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark) := by
      have hk : k + 2 = Nat.succ (Nat.succ k) := by omega
      rw [hk, List.replicate_succ, List.replicate_succ]
    have hfinishLeft :
        (ulogCore stateMark :: ulogCore stateMark ::
            List.replicate k (ulogCore stateMark)) ++
          (path.reverse ++ ulogCore targetBoundary :: left) =
        finishPath.reverse ++ ulogCore targetBoundary :: left := by
      simp [finishPath, targetFinishPath, hdoneEq, List.reverse_append,
        hmarks, List.append_assoc]
    rw [show List.replicate (k + 1) (ulogCore stateMark) ++
          (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left) =
        (ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark)) ++
            (path.reverse ++ ulogCore targetBoundary :: left) by
      simp [List.replicate_succ, List.append_assoc]] at hmany0
    rw [hfinishLeft] at hmany0
    simpa [afterRightPath] using hmany0
  have hshrinkStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        targetFinishMany_zero_core
          (finishPath.reverse ++ ulogCore targetBoundary :: left)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let shrink := stopFree_targetShrink extra
    (finishPath.reverse ++ ulogCore targetBoundary :: left) tail
  have hshrink : StopFreeValidZeroRun (2 * extra + 6)
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateOne,
          ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
    have hfuel : shrink.1 = 2 * extra + 6 := by
      dsimp [shrink]
      exact targetShrink_fuel_eq extra
        (finishPath.reverse ++ ulogCore targetBoundary :: left) tail
    simpa only [hfuel] using shrink.2
  let restorePath := ulogCore stateOne :: finishPath.reverse
  have hshrink' : StopFreeValidZeroRun (2 * extra + 6)
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath restorePath left (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    simpa [restorePath, beforeLeftPath, List.append_assoc] using hshrink
  have hrestore := stopFree_leftPathMap_of
    (.actionPhase .targetRestoreState) (by decide) restorePath
    restoreTargetCell (by
      intro x hx l y r
      simp only [restorePath, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hm : ulogCore stateOne ≠ ulogCore stateMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        have hb : ulogCore stateOne ≠ ulogCore targetBoundary :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        have hp : ulogCore stateOne ≠ ulogCore pcMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        simpa [restoreTargetCell, hm] using
          targetRestoreState_pass (ulogCore stateOne) hm hb hp l y r
      · have hx' : x ∈ finishPath := by simpa using hx
        by_cases hm : x = ulogCore stateMark
        · subst x
          simpa [restoreTargetCell] using targetRestoreState_mark l y r
        · have h := targetFinishPath_restore_safe path done hsafe hx'
          simpa [restoreTargetCell, hm] using
            targetRestoreState_pass x hm h.1 h.2 l y r)
    left (ulogCore targetBoundary)
    (ulogCore stateSep ::
      List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)
  have hmoveStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap restorePath restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have honeMark : ulogCore stateOne ≠ ulogCore stateMark :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have hmap : restorePath.reverse.map restoreTargetCell =
          path ++ List.replicate done (ulogCore stateZero) ++
            [ulogCore stateOne] := by
        simp [restorePath, finishPath, targetFinishPath,
          List.reverse_append, List.map_append,
          restoreTargetCell_path path hsafe, restoreTargetCell, honeMark,
          List.append_assoc]
      rw [show afterLeftPathMap restorePath restoreTargetCell left
            (ulogCore targetBoundary)
            (ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail) =
          ⟨left, ulogCore targetBoundary,
            path ++ List.replicate done (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  tail⟩ by
        simp [afterLeftPathMap, hmap, List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.append_assoc] using
            targetRestoreState_boundary left x
              (xs ++ List.replicate done (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                    tail)
    · simp [afterLeftPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let joined := ((((((hstart.append hscan).append hmark).append hmany).append
    hshrinkStart).append hshrink').append hrestore).append hmoveStart
  refine ⟨
    { steps := 1 + path.length + 1 + (k + 1) + 1 +
        (2 * extra + 6) + restorePath.length + 1
      le_bound := ?_
      run := by
        simpa [joined, finishPath, restorePath] using joined }⟩
  simp [finishPath, restorePath, targetFinishPath, hdoneEq]
  omega

/-! ## Complete target rewrites -/

/-- A non-growing target rewrite has a uniform quadratic physical bound. -/
theorem targetAtMostState_bounded_radius
    (target extra : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ target) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) {R : ℕ}
    (hstate : target + extra ≤ R) (hcorridorLen : corridor.length ≤ R) :
    Nonempty (BoundedStopFreeRun (8 * (R + 1) ^ 2)
      (targetRawStart target (target + extra) corridor left tail)
      (targetRewriteFinished target extra corridor left tail)) := by
  obtain ⟨existing⟩ := targetExistingZeros_bounded target 0 extra corridor
    hsafe left tail
  have hexisting : StopFreeValidZeroRun existing.steps
      (targetRawStart target (target + extra) corridor left tail)
      (targetExistingDone target 0 extra corridor left tail) := by
    cases target with
    | zero => omega
    | succ target =>
        have hrep :
            List.replicate ((target + 1) + extra) (ulogCore stateZero) =
              ulogCore stateZero ::
                List.replicate target (ulogCore stateZero) ++
                  List.replicate extra (ulogCore stateZero) := by
          rw [List.replicate_add, List.replicate_succ]
        simpa [targetRawStart, targetExistingStart, targetScanPath, hrep,
          List.append_assoc] using existing.run
  cases extra with
  | zero =>
      obtain ⟨finish⟩ := targetFinishEqual_bounded corridor hcorridor target
        htarget hsafe.2 (List.replicate target (ulogCore codeZero) ++ left) tail
      have hfinish : StopFreeValidZeroRun finish.steps
          (targetExistingDone target 0 0 corridor left tail)
          (targetRewriteFinished target 0 corridor left tail) := by
        simpa [targetExistingDone, targetRewriteFinished,
          targetFinishPath, List.append_assoc] using finish.run
      refine ⟨
        { steps := existing.steps + finish.steps
          le_bound := ?_
          run := hexisting.append hfinish }⟩
      have he := existing.le_bound
      have hf := finish.le_bound
      nlinarith [sq_nonneg (R : ℤ)]
  | succ extra =>
      obtain ⟨finish⟩ := targetFinishShorter_bounded corridor hcorridor
        target extra htarget hsafe.2
        (List.replicate target (ulogCore codeZero) ++ left) tail
      have hfinish : StopFreeValidZeroRun finish.steps
          (targetExistingDone target 0 (extra + 1) corridor left tail)
          (targetRewriteFinished target (extra + 1) corridor left tail) := by
        simpa [targetExistingDone, targetRewriteFinished, targetFinishPath,
          List.replicate_succ, List.append_assoc] using finish.run
      refine ⟨
        { steps := existing.steps + finish.steps
          le_bound := ?_
          run := hexisting.append hfinish }⟩
      have he := existing.le_bound
      have hf := finish.le_bound
      nlinarith [sq_nonneg (R : ℤ)]

/-- A growing target rewrite has a uniform quadratic physical bound. -/
theorem targetAtLeastState_bounded_radius
    (current growth : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ current + growth)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) {R : ℕ}
    (hstate : current + growth ≤ R)
    (hcorridorLen : corridor.length ≤ R) :
    Nonempty (BoundedStopFreeRun (12 * (R + 1) ^ 2)
      (targetRawStart (current + growth) current corridor left
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))) := by
  obtain ⟨consume⟩ := targetConsumeState_bounded current growth 0 corridor
    hsafe left tail
  have hsource :
      targetRawStart (current + growth) current corridor left
          (List.replicate growth MStarConcreteAlphabet.work ++ tail) =
        targetConsumeStart current growth 0 corridor left tail := by
    cases current with
    | zero =>
        cases growth <;>
          simp [targetRawStart, targetConsumeStart, targetGrowStart,
            targetScanPath, List.replicate_succ, List.append_assoc]
    | succ current =>
        have hsum : current + growth = growth + current := Nat.add_comm _ _
        have htarget' : current + 1 + growth = (growth + current) + 1 := by
          omega
        rw [htarget']
        simp [targetRawStart, targetConsumeStart, targetScanPath,
          List.replicate_succ, hsum, List.append_assoc]
  have hconsume : StopFreeValidZeroRun consume.steps
      (targetRawStart (current + growth) current corridor left
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (targetGrowStart growth current corridor
        (List.replicate current (ulogCore codeZero) ++ left) tail) := by
    rw [hsource]
    simpa [targetConsumeDone] using consume.run
  obtain ⟨grow⟩ := targetGrowZeros_bounded growth current corridor hsafe
    (List.replicate current (ulogCore codeZero) ++ left) tail
  obtain ⟨finish⟩ := targetFinishEqual_bounded corridor hcorridor
    (current + growth) htarget hsafe.2
    (List.replicate growth (ulogCore codeZero) ++
      List.replicate current (ulogCore codeZero) ++ left) tail
  have hfinish : StopFreeValidZeroRun finish.steps
      (targetGrowDone growth current corridor
        (List.replicate current (ulogCore codeZero) ++ left) tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    have hcodes :
        List.replicate growth (ulogCore codeZero) ++
            List.replicate current (ulogCore codeZero) =
          List.replicate (current + growth) (ulogCore codeZero) := by
      rw [← List.replicate_add, Nat.add_comm]
    have hcodesLeft :
        List.replicate growth (ulogCore codeZero) ++
            (List.replicate current (ulogCore codeZero) ++ left) =
          List.replicate (current + growth) (ulogCore codeZero) ++ left := by
      rw [← List.append_assoc, hcodes]
    simpa [targetGrowDone, targetFinishPath, hcodes,
      hcodesLeft, List.append_assoc] using finish.run
  refine ⟨
    { steps := consume.steps + grow.steps + finish.steps
      le_bound := ?_
      run := (hconsume.append grow.run).append hfinish }⟩
  have hc := consume.le_bound
  have hg := grow.le_bound
  have hf := finish.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-! ## Write dispatch and stay tails -/

/-- Explicit write dispatch without the `Classical.choice` used by the
legacy uniform wrapper. -/
theorem actionWriteValid_bounded_radius
    (write : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) {R : ℕ} (hpathLen : path.length ≤ R) :
    Nonempty (BoundedStopFreeRun (2 * R + 5)
      (actionWriteStart write left path oldHead suffix)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
          (writeHeadNat write) suffix))) := by
  interval_cases write
  · let run := stopFree_actionWriteZero oldHead hhead path hpath left suffix
    refine ⟨
      { steps := run.1
        le_bound := ?_
        run := by simpa [run, actionWriteStart, writeHeadNat] using run.2 }⟩
    rw [show run.1 = 2 * path.length + 3 by
      dsimp [run]
      exact actionWriteZero_fuel_eq oldHead hhead path hpath left suffix]
    omega
  · let run := stopFree_actionWriteOne oldHead hhead path hpath left suffix
    refine ⟨
      { steps := run.1
        le_bound := ?_
        run := by
          simpa [run, actionWriteStart, writeHeadNat, List.replicate_succ,
            List.append_assoc] using run.2 }⟩
    rw [show run.1 = 2 * path.length + 4 by
      dsimp [run]
      exact actionWriteOne_fuel_eq oldHead hhead path hpath left suffix]
    omega
  · let run := stopFree_actionWriteBlank oldHead hhead path hpath left suffix
    refine ⟨
      { steps := run.1
        le_bound := ?_
        run := by
          simpa [run, actionWriteStart, writeHeadNat, List.replicate_succ,
            List.append_assoc] using run.2 }⟩
    rw [show run.1 = 2 * path.length + 5 by
      dsimp [run]
      exact actionWriteBlank_fuel_eq oldHead hhead path hpath left suffix]
    omega

/-- Write, target rewrite, and two-bit move dispatch in the non-growing
case, stopping at the geometry-specific `moveSimHead` state. -/
theorem matchedActionAtMost_to_move_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target) (m : OneTapeTableau.Move)
    (movePath runtime : List Tape) (oldHead : Tape)
    (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath).length ≤ R)
    (htargetLen :
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime).length ≤ R)
    (hstate : target + extra ≤ R) :
    Nonempty (BoundedStopFreeRun (12 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail)))) := by
  let writeCorridor := List.replicate target (ulogCore codeZero) ++
    ulogCore codeOne :: moveBits m ++ movePath
  let targetCorridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  obtain ⟨writeRun⟩ := actionWriteValid_bounded_radius write hwrite oldHead
    hhead writeCorridor (by simpa [writeCorridor] using hwritePath) left
    (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
    (by simpa [writeCorridor] using hwriteLen)
  have hwriteRun : StopFreeValidZeroRun writeRun.steps
      (actionWriteStart write left writeCorridor oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart target (target + extra) targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        tail) := by
    cases target <;>
      simpa [targetRawStart, targetCorridor, writeCorridor, moveBits,
        beforeRightPath, List.replicate_succ, List.append_assoc] using
        writeRun.run
  obtain ⟨targetRun⟩ := targetAtMostState_bounded_radius target extra
    targetCorridor (by simp [targetCorridor, moveBits]) htarget
    (by simpa [targetCorridor] using htargetPath)
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail hstate (by simpa [targetCorridor] using htargetLen)
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++
      (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
  have hmove : StopFreeValidZeroRun 2
      (targetRewriteFinished target extra targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        tail)
      (.running (.moveSimHead m)
        (beforeRightPath movePath (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
    cases hpath : movePath with
    | nil =>
        simpa [targetRewriteFinished, targetCorridor, writeCorridor, moveLeft,
          moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove m moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail))
    | cons x xs =>
        simpa [targetRewriteFinished, targetCorridor, writeCorridor, moveLeft,
          moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove m moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate extra MStarConcreteAlphabet.work ++ tail))
  refine ⟨
    { steps := writeRun.steps + targetRun.steps + 2
      le_bound := ?_
      run := by
        simpa [writeCorridor] using (hwriteRun.append targetRun.run).append hmove }⟩
  have hw := writeRun.le_bound
  have ht := targetRun.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- State-growth counterpart of `matchedActionAtMost_to_move_bounded_radius`. -/
theorem matchedActionAtLeast_to_move_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth) (m : OneTapeTableau.Move)
    (movePath runtime : List Tape) (oldHead : Tape)
    (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath).length ≤ R)
    (htargetLen :
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime).length ≤ R)
    (hstate : current + growth ≤ R) :
    Nonempty (BoundedStopFreeRun (16 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write (current + growth) m left)
          (writeHeadNat write)
          (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))) := by
  let target := current + growth
  let writeCorridor := List.replicate target (ulogCore codeZero) ++
    ulogCore codeOne :: moveBits m ++ movePath
  let targetCorridor := moveBits m ++ movePath ++ writeHeadNat write :: runtime
  obtain ⟨writeRun⟩ := actionWriteValid_bounded_radius write hwrite oldHead
    hhead writeCorridor (by simpa [writeCorridor, target] using hwritePath)
    left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ tail)
    (by simpa [writeCorridor, target] using hwriteLen)
  have hwriteRun : StopFreeValidZeroRun writeRun.steps
      (actionWriteStart write left writeCorridor oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (targetRawStart target current targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        (List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    cases htarget' : target <;>
      simpa [targetRawStart, targetCorridor, writeCorridor, target, htarget',
        moveBits, beforeRightPath, List.replicate_succ,
        List.append_assoc] using writeRun.run
  obtain ⟨targetRun⟩ := targetAtLeastState_bounded_radius current growth
    targetCorridor (by simp [targetCorridor, moveBits]) htarget
    (by simpa [targetCorridor] using htargetPath)
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail hstate (by simpa [targetCorridor] using htargetLen)
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++
      (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
  have hmove : StopFreeValidZeroRun 2
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          moveLeft (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.moveSimHead m)
        (beforeRightPath movePath (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    cases hpath : movePath with
    | nil =>
        simpa [targetCorridor, writeCorridor, target, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove m moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))
    | cons x xs =>
        simpa [targetCorridor, writeCorridor, target, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove m moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail))
  refine ⟨
    { steps := writeRun.steps + targetRun.steps + 2
      le_bound := ?_
      run := by
        simpa [writeCorridor, target] using
          (hwriteRun.append targetRun.run).append hmove }⟩
  have hw := writeRun.le_bound
  have ht := targetRun.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- Complete non-growing stay tail, from the actual matched write state to
the next physical cycle boundary. -/
theorem matchedAtMost_stay_tail_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .stay ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .stay ++ scanPath ++ writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write target .stay left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (writeHeadNat write ::
        (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .stay ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .stay ++ scanPath ++ writeHeadNat write :: runtime).length ≤ R)
    (hstate : target + extra ≤ R)
    (hprogramPrefix : programPrefix.length ≤ R)
    (hscanLen : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (16 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .stay ++ scanPath)
        oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          writeHeadNat write,
          runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩)) := by
  let writeCorridor := List.replicate target (ulogCore codeZero) ++
    ulogCore codeOne :: moveBits .stay ++ scanPath
  let targetCorridor := moveBits .stay ++ scanPath ++
    writeHeadNat write :: runtime
  obtain ⟨writeRun⟩ := actionWriteValid_bounded_radius write hwrite
    oldHead hhead writeCorridor (by simpa [writeCorridor] using hwritePath)
    left
    (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    (by simpa [writeCorridor] using hwriteLen)
  have hwriteRun : StopFreeValidZeroRun writeRun.steps
      (actionWriteStart write left writeCorridor oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix))
      (targetRawStart target (target + extra) targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        suffix) := by
    cases target <;>
      simpa [targetRawStart, targetCorridor, writeCorridor, moveBits,
        beforeRightPath, List.replicate_succ, List.append_assoc] using
        writeRun.run
  obtain ⟨targetRun⟩ := targetAtMostState_bounded_radius target extra
    targetCorridor (by simp [targetCorridor, moveBits]) htarget
    (by simpa [targetCorridor] using htargetPath)
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    suffix hstate (by simpa [targetCorridor] using htargetLen)
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++
      (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
  have hmove : StopFreeValidZeroRun 2
      (targetRewriteFinished target extra targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        suffix)
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath (matchedMoveLeft write target .stay left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix))) := by
    cases hpath : scanPath with
    | nil =>
        simpa [targetRewriteFinished, targetCorridor, writeCorridor,
          moveLeft, moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove .stay moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix))
    | cons x xs =>
        simpa [targetRewriteFinished, targetCorridor, writeCorridor,
          moveLeft, moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove .stay moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate extra MStarConcreteAlphabet.work ++ suffix))
  obtain ⟨cleanup⟩ := moveStay_cleanup_bounded_radius programPrefix scanPath
    pcPath terminal outer (writeHeadNat write)
    (runtime ++ List.replicate target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hclock hpc hterminal hprogram
    (by interval_cases write <;> decide)
    hprogramPrefix hscanLen hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath (matchedMoveLeft write target .stay left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          writeHeadNat write,
          runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := writeRun.steps + targetRun.steps + 2 + cleanup.steps
      le_bound := ?_
      run := by
        simpa [writeCorridor] using
          ((hwriteRun.append targetRun.run).append hmove).append hcleanup }⟩
  have hw := writeRun.le_bound
  have ht := targetRun.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- Complete state-growth stay tail. -/
theorem matchedAtLeast_stay_tail_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .stay ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .stay ++ scanPath ++ writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write (current + growth) .stay left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (writeHeadNat write ::
        (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .stay ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .stay ++ scanPath ++ writeHeadNat write :: runtime).length ≤ R)
    (hstate : current + growth ≤ R)
    (hprogramPrefix : programPrefix.length ≤ R)
    (hscanLen : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (20 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .stay ++ scanPath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          writeHeadNat write,
          runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩)) := by
  let target := current + growth
  let writeCorridor := List.replicate target (ulogCore codeZero) ++
    ulogCore codeOne :: moveBits .stay ++ scanPath
  let targetCorridor := moveBits .stay ++ scanPath ++
    writeHeadNat write :: runtime
  obtain ⟨writeRun⟩ := actionWriteValid_bounded_radius write hwrite
    oldHead hhead writeCorridor (by
      simpa [writeCorridor, target] using hwritePath)
    left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)
    (by simpa [writeCorridor, target] using hwriteLen)
  have hwriteRun : StopFreeValidZeroRun writeRun.steps
      (actionWriteStart write left writeCorridor oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (targetRawStart target current targetCorridor
        (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
        (List.replicate growth MStarConcreteAlphabet.work ++ suffix)) := by
    cases htarget' : target <;>
      simpa [targetRawStart, targetCorridor, writeCorridor, target, htarget',
        moveBits, beforeRightPath, List.replicate_succ,
        List.append_assoc] using writeRun.run
  obtain ⟨targetRun⟩ := targetAtLeastState_bounded_radius current growth
    targetCorridor (by simp [targetCorridor, moveBits]) htarget
    (by simpa [targetCorridor] using htargetPath)
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    suffix hstate (by simpa [targetCorridor] using htargetLen)
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++
      (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
  have hmove : StopFreeValidZeroRun 2
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          moveLeft (ulogCore stateOne) (ulogCore stateSep :: suffix)))
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath (matchedMoveLeft write target .stay left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))) := by
    cases hpath : scanPath with
    | nil =>
        simpa [targetCorridor, writeCorridor, target, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove .stay moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix))
    | cons x xs =>
        simpa [targetCorridor, writeCorridor, target, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove .stay moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: suffix))
  obtain ⟨cleanup⟩ := moveStay_cleanup_bounded_radius programPrefix scanPath
    pcPath terminal outer (writeHeadNat write)
    (runtime ++ List.replicate target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan hclock hpc hterminal hprogram
    (by interval_cases write <;> decide)
    hprogramPrefix hscanLen hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath (matchedMoveLeft write target .stay left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          writeHeadNat write,
          runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [show matchedMoveLeft write target .stay left =
        programPrefix.reverse ++ terminal :: pcPath.reverse ++
          ulogCore pcMark :: outer by simpa [target] using hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := writeRun.steps + targetRun.steps + 2 + cleanup.steps
      le_bound := ?_
      run := by
        simpa [writeCorridor, target] using
          ((hwriteRun.append targetRun.run).append hmove).append hcleanup }⟩
  have hw := writeRun.le_bound
  have ht := targetRun.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-! ## Internal-move cleanup -/

theorem moveRightInternal_cleanup_fuel_eq
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head cell : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hhead : choiceHead head = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head])) :
    (stopFree_moveRightInternal_cleanup programPrefix scanPath pcPath terminal
      outer head cell right hscan hhead hcell hclock hpc hterminal hprogram).1 =
      2 * programPrefix.length + 3 * scanPath.length +
        2 * pcPath.length + 9 := by
  simp [stopFree_moveRightInternal_cleanup, stopFree_moveRightInternal,
    restoreCycle_fuel_eq]
  omega

theorem moveLeftInternal_cleanup_fuel_eq
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (cell head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix)) :
    (stopFree_moveLeftInternal_cleanup programPrefix scanPrefix pcPath terminal
      outer cell head right hscan hcell hhead hclock hpc hterminal hprogram).1 =
      2 * programPrefix.length + 3 * scanPrefix.length +
        2 * pcPath.length + 8 := by
  simp [stopFree_moveLeftInternal_cleanup, stopFree_moveLeftInternal,
    restoreCycle_fuel_eq]
  omega

theorem moveRightInternal_cleanup_bounded_radius
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head cell : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath) (hhead : choiceHead head = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head]))
    {R : ℕ} (hp : programPrefix.length ≤ R)
    (hs : scanPath.length ≤ R) (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (7 * R + 9)
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer) head (cell :: right)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape head) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell, right⟩)) := by
  let run := stopFree_moveRightInternal_cleanup programPrefix scanPath pcPath
    terminal outer head cell right hscan hhead hcell hclock hpc hterminal
    hprogram
  refine ⟨{ steps := run.1, le_bound := ?_, run := run.2 }⟩
  rw [show run.1 = 2 * programPrefix.length + 3 * scanPath.length +
      2 * pcPath.length + 9 by
    dsimp [run]
    exact moveRightInternal_cleanup_fuel_eq programPrefix scanPath pcPath
      terminal outer head cell right hscan hhead hcell hclock hpc hterminal
      hprogram]
  omega

theorem moveLeftInternal_cleanup_bounded_radius
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (cell head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix))
    {R : ℕ} (hp : programPrefix.length ≤ R)
    (hs : scanPrefix.length ≤ R) (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (7 * R + 8)
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer) head right))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell, unheadTape head :: right⟩)) := by
  let run := stopFree_moveLeftInternal_cleanup programPrefix scanPrefix pcPath
    terminal outer cell head right hscan hcell hhead hclock hpc hterminal
    hprogram
  refine ⟨{ steps := run.1, le_bound := ?_, run := run.2 }⟩
  rw [show run.1 = 2 * programPrefix.length + 3 * scanPrefix.length +
      2 * pcPath.length + 8 by
    dsimp [run]
    exact moveLeftInternal_cleanup_fuel_eq programPrefix scanPrefix pcPath
      terminal outer cell head right hscan hcell hhead hclock hpc hterminal
      hprogram]
  omega

/-- Non-growing internal-right branch. -/
theorem matchedAtMost_rightInternal_tail_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer runtimeTail suffix : List Tape) (left : List Tape)
    (oldHead cell : Tape) (hhead : choiceHead oldHead = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .right ++ scanPath ++ writeHeadNat write :: cell :: runtimeTail))
    (hdecomp : matchedMoveLeft write target .right left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .right ++ scanPath ++
        writeHeadNat write :: cell :: runtimeTail).length ≤ R)
    (hstate : target + extra ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (16 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .right ++ scanPath)
        oldHead
        ((cell :: runtimeTail) ++
          List.replicate (target + extra) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtimeTail ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtMost_to_move_bounded_radius write
    target extra hwrite htarget .right scanPath (cell :: runtimeTail) oldHead
    hhead hwritePath htargetPath left suffix hwriteLen htargetLen hstate
  obtain ⟨cleanup⟩ := moveRightInternal_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal outer (writeHeadNat write) cell
    (runtimeTail ++ List.replicate target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan (by interval_cases write <;> decide) hcell hclock hpc
    hterminal hprogram hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath (matchedMoveLeft write target .right left)
          (writeHeadNat write)
          ((cell :: runtimeTail) ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtimeTail ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hdecomp]
    simpa [List.cons_append, List.append_assoc] using cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- State-growth internal-right branch. -/
theorem matchedAtLeast_rightInternal_tail_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer runtimeTail suffix : List Tape) (left : List Tape)
    (oldHead cell : Tape) (hhead : choiceHead oldHead = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .right ++ scanPath ++ writeHeadNat write :: cell :: runtimeTail))
    (hdecomp : matchedMoveLeft write (current + growth) .right left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .right ++ scanPath ++
        writeHeadNat write :: cell :: runtimeTail).length ≤ R)
    (hstate : current + growth ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (20 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .right ++ scanPath)
        oldHead
        ((cell :: runtimeTail) ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtimeTail ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtLeast_to_move_bounded_radius write
    current growth hwrite htarget .right scanPath (cell :: runtimeTail)
    oldHead hhead hwritePath htargetPath left suffix hwriteLen htargetLen hstate
  obtain ⟨cleanup⟩ := moveRightInternal_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal outer (writeHeadNat write) cell
    (runtimeTail ++ List.replicate (current + growth) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan (by interval_cases write <;> decide) hcell hclock hpc
    hterminal hprogram hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (matchedMoveLeft write (current + growth) .right left)
          (writeHeadNat write)
          ((cell :: runtimeTail) ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          runtimeTail ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hdecomp]
    simpa [List.cons_append, List.append_assoc] using cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- Non-growing internal-left branch. -/
theorem matchedAtMost_leftInternal_tail_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead cell : Tape) (hhead : choiceHead oldHead = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell]))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .left ++ scanPrefix ++ [cell] ++
        writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write target .left left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix))
    {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell]).length ≤ R)
    (htargetLen :
      (moveBits .left ++ scanPrefix ++ [cell] ++
        writeHeadNat write :: runtime).length ≤ R)
    (hstate : target + extra ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPrefix.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (16 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell])
        oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtMost_to_move_bounded_radius write
    target extra hwrite htarget .left (scanPrefix ++ [cell]) runtime oldHead
    hhead (by simpa [List.append_assoc] using hwritePath)
    (by simpa [List.append_assoc] using htargetPath)
    left suffix (by simpa [List.append_assoc] using hwriteLen)
    (by simpa [List.append_assoc] using htargetLen) hstate
  obtain ⟨cleanup⟩ := moveLeftInternal_cleanup_bounded_radius
    programPrefix scanPrefix pcPath terminal outer cell (writeHeadNat write)
    (runtime ++ List.replicate target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hcell (by interval_cases write <;> decide) hclock hpc
    hterminal hprogram hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (matchedMoveLeft write target .left left) (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-- State-growth internal-left branch. -/
theorem matchedAtLeast_leftInternal_tail_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead cell : Tape) (hhead : choiceHead oldHead = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell]))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .left ++ scanPrefix ++ [cell] ++
        writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write (current + growth) .left left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix))
    {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell]).length ≤ R)
    (htargetLen :
      (moveBits .left ++ scanPrefix ++ [cell] ++
        writeHeadNat write :: runtime).length ≤ R)
    (hstate : current + growth ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPrefix.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (20 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .left ++ scanPrefix ++ [cell])
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtLeast_to_move_bounded_radius write
    current growth hwrite htarget .left (scanPrefix ++ [cell]) runtime oldHead
    hhead (by simpa [List.append_assoc] using hwritePath)
    (by simpa [List.append_assoc] using htargetPath)
    left suffix (by simpa [List.append_assoc] using hwriteLen)
    (by simpa [List.append_assoc] using htargetLen) hstate
  obtain ⟨cleanup⟩ := moveLeftInternal_cleanup_bounded_radius
    programPrefix scanPrefix pcPath terminal outer cell (writeHeadNat write)
    (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan hcell (by interval_cases write <;> decide) hclock hpc
    hterminal hprogram hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (matchedMoveLeft write (current + growth) .left left)
          (writeHeadNat write)
          (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-! ## Boundary-shift fuel -/

theorem restoreCycle_bounded_radius
    (pcPath : List Tape) (terminal : Tape) (programPath : List Tape)
    (outer : List Tape) (head : Tape)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: programPath).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe programPath)
    (hhead : choiceHead head = true) (right : List Tape)
    {R : ℕ} (hpcLen : pcPath.length ≤ R)
    (hprogramLen : programPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (4 * R + 5)
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer, head, right⟩)
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++ ulogCore codeOne ::
            pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          head, right⟩)) := by
  let run := stopFree_restoreCycle pcPath terminal programPath outer head
    hclock hpc hterminal hprogram hhead right
  refine ⟨{ steps := run.1, le_bound := ?_, run := run.2 }⟩
  rw [show run.1 = 2 * pcPath.length + 2 * programPath.length + 5 by
    dsimp [run]
    exact restoreCycle_fuel_eq pcPath terminal programPath outer head hclock
      hpc hterminal hprogram hhead right]
  omega

/-- Literal rightward runtime shift: one step per prefix cell and the two
terminal transitions. -/
theorem shiftRuntimeRight_bounded
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Nonempty (BoundedStopFreeRun (pre.length + 2)
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath (pre.reverse ++ [carry]) left head
          (last :: right)))) := by
  induction pre generalizing carry left head with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work := hsafe last (by simp)
      have hstep : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath [last] (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.right last))
            ⟨carry :: head :: left, MStarConcreteAlphabet.work, right⟩) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeRightPath] using
            shiftRuntimeRight_step carry last hlast (head :: left)
              MStarConcreteAlphabet.work right
        · simp [beforeRightPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      have hend : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right last))
            ⟨carry :: head :: left, MStarConcreteAlphabet.work, right⟩)
          (.running (.actionPhase .returnMovedFromRight)
            (beforeLeftPath [carry] left head (last :: right))) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeLeftPath] using
            shiftRuntimeRight_end last (head :: left) carry right
        · simp [IsConcreteCycleStop, IsConcreteCycleBoundary,
            concreteHalted]
      exact ⟨
        { steps := 2
          le_bound := by simp
          run := by simpa [beforeRightPath, beforeLeftPath] using
            hstep.append hend }⟩
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath ((x :: xs) ++ [last]) (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.right x))
            (beforeRightPath (xs ++ [last]) (carry :: head :: left)
              MStarConcreteAlphabet.work right)) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases xs with
          | nil =>
              simpa [beforeRightPath] using
                shiftRuntimeRight_step carry x hx (head :: left) last
                  (MStarConcreteAlphabet.work :: right)
          | cons z zs =>
              simpa [beforeRightPath, List.append_assoc] using
                shiftRuntimeRight_step carry x hx (head :: left) z
                  (zs ++ last :: MStarConcreteAlphabet.work :: right)
        · simp [beforeRightPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      obtain ⟨rest⟩ := ih x hxs (head :: left) carry
      have hall := hfirst.append rest.run
      refine ⟨
        { steps := 1 + rest.steps
          le_bound := by have hr := rest.le_bound; simp; omega
          run := by
            rw [List.reverse_cons]
            rw [beforeLeftPath_append_singleton (xs.reverse ++ [x]) carry
              (by simp)]
            exact hall }⟩

/-- Leftward symmetric runtime shift. -/
theorem shiftRuntimeLeft_bounded
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Nonempty (BoundedStopFreeRun (pre.length + 2)
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath (pre.reverse ++ [carry]) (last :: left) head
          right))) := by
  induction pre generalizing carry head right with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work := hsafe last (by simp)
      have hstep : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left carry))
            (beforeLeftPath [last] left MStarConcreteAlphabet.work
              (head :: right)))
          (.running (.shiftRuntime (.left last))
            ⟨left, MStarConcreteAlphabet.work, carry :: head :: right⟩) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeLeftPath] using
            shiftRuntimeLeft_step carry last hlast left
              MStarConcreteAlphabet.work (head :: right)
        · simp [beforeLeftPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      have hend : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left last))
            ⟨left, MStarConcreteAlphabet.work, carry :: head :: right⟩)
          (.running (.actionPhase .returnMovedFromLeft)
            (beforeRightPath [carry] (last :: left) head right)) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeRightPath] using
            shiftRuntimeLeft_end last left carry (head :: right)
        · simp [IsConcreteCycleStop, IsConcreteCycleBoundary,
            concreteHalted]
      exact ⟨
        { steps := 2
          le_bound := by simp
          run := by simpa [beforeLeftPath, beforeRightPath] using
            hstep.append hend }⟩
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left carry))
            (beforeLeftPath ((x :: xs) ++ [last]) left
              MStarConcreteAlphabet.work (head :: right)))
          (.running (.shiftRuntime (.left x))
            (beforeLeftPath (xs ++ [last]) left
              MStarConcreteAlphabet.work (carry :: head :: right))) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases xs with
          | nil =>
              simpa [beforeLeftPath] using
                shiftRuntimeLeft_step carry x hx
                  (MStarConcreteAlphabet.work :: left) last (head :: right)
          | cons z zs =>
              simpa [beforeLeftPath, List.append_assoc] using
                shiftRuntimeLeft_step carry x hx
                  (zs ++ last :: MStarConcreteAlphabet.work :: left) z
                  (head :: right)
        · simp [beforeLeftPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      obtain ⟨rest⟩ := ih x hxs carry (head :: right)
      have hall := hfirst.append rest.run
      refine ⟨
        { steps := 1 + rest.steps
          le_bound := by have hr := rest.le_bound; simp; omega
          run := by
            rw [List.reverse_cons]
            rw [beforeRightPath_append_singleton (xs.reverse ++ [x]) carry
              (by simp)]
            exact hall }⟩

theorem shiftRuntimeRight_restored_bounded
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Nonempty (BoundedStopFreeRun (2 * pre.length + 4)
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running .restoreClock
        ⟨left, head, carry :: pre ++ last :: right⟩)) := by
  obtain ⟨shift⟩ := shiftRuntimeRight_bounded carry pre last hshift
    left head right
  let returning := stopFree_returnMovedFromRight (pre.reverse ++ [carry])
    hreturn left head hhead (last :: right)
  have hreturnFuel : returning.1 = pre.length + 2 := by
    simp [returning, stopFree_returnMovedFromRight]
  have hreturnRun : StopFreeValidZeroRun (pre.length + 2)
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath (pre.reverse ++ [carry]) left head (last :: right)))
      (.running .restoreClock ⟨left, head, carry :: pre ++ last :: right⟩) := by
    rw [← hreturnFuel]
    simpa [beforeLeftPath, afterLeftPath, List.reverse_append,
      List.append_assoc] using
      returning.2
  refine ⟨
    { steps := shift.steps + (pre.length + 2)
      le_bound := by have hs := shift.le_bound; omega
      run := shift.run.append hreturnRun }⟩

theorem shiftRuntimeLeft_restored_bounded
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Nonempty (BoundedStopFreeRun (2 * pre.length + 4)
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running .restoreClock
        ⟨carry :: pre ++ last :: left, head, right⟩)) := by
  obtain ⟨shift⟩ := shiftRuntimeLeft_bounded carry pre last hshift
    left head right
  let returning := stopFree_returnMovedFromLeft (pre.reverse ++ [carry])
    hreturn (last :: left) head hhead right
  have hreturnFuel : returning.1 = pre.length + 2 := by
    simp [returning, stopFree_returnMovedFromLeft]
  have hreturnRun : StopFreeValidZeroRun (pre.length + 2)
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath (pre.reverse ++ [carry]) (last :: left) head right))
      (.running .restoreClock ⟨carry :: pre ++ last :: left, head, right⟩) := by
    rw [← hreturnFuel]
    simpa [beforeRightPath, afterRightPath, List.reverse_append,
      List.append_assoc] using
      returning.2
  refine ⟨
    { steps := shift.steps + (pre.length + 2)
      le_bound := by have hs := shift.le_bound; omega
      run := shift.run.append hreturnRun }⟩

theorem moveRightBoundary_bounded
    (path pre : List Tape) (hscan : MoveScanSafe path)
    (boundary last : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Nonempty (BoundedStopFreeRun (path.length + 2 * pre.length + 6)
      (.running (.moveSimHead .right)
        (beforeRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          ulogCore payloadHeadBlank, boundary :: pre ++ last :: right⟩)) := by
  have hscanRun := stopFree_moveScan .right path hscan left head
    (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .right)
        (afterRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        moveSimHead_right head hhead (path.reverse ++ left) boundary
          (pre ++ last :: MStarConcreteAlphabet.work :: right)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩)
      (.running (.shiftRuntime (.right boundary))
        (beforeRightPath (pre ++ [last])
          (ulogCore payloadHeadBlank :: unheadTape head :: path.reverse ++ left)
          MStarConcreteAlphabet.work right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pre with
      | nil =>
          simpa [beforeRightPath] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) last
              (MStarConcreteAlphabet.work :: right)
      | cons x xs =>
          simpa [beforeRightPath, List.append_assoc] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) x
              (xs ++ last :: MStarConcreteAlphabet.work :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨shift⟩ := shiftRuntimeRight_restored_bounded boundary pre last
    hshift hreturn (unheadTape head :: path.reverse ++ left)
    (ulogCore payloadHeadBlank) (by decide) right
  refine ⟨
    { steps := path.length + 2 + shift.steps
      le_bound := by have hs := shift.le_bound; omega
      run := by
        simpa [Nat.add_assoc] using
          ((hscanRun.append hmove).append hplace).append shift.run }⟩

theorem moveLeftBoundary_bounded
    (pre : List Tape) (last boundary : Tape)
    (hscan : MoveScanSafe ((pre ++ [last]).reverse ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Nonempty (BoundedStopFreeRun (3 * pre.length + 9)
      (.running (.moveSimHead .left)
        (beforeRightPath ((pre ++ [last]).reverse ++ [boundary])
          (MStarConcreteAlphabet.work :: left) head right))
      (.running .restoreClock
        ⟨boundary :: pre ++ last :: left, ulogCore payloadHeadBlank,
          unheadTape head :: right⟩)) := by
  let scanPath := (pre ++ [last]).reverse ++ [boundary]
  have hscanRun := stopFree_moveScan .left scanPath hscan
    (MStarConcreteAlphabet.work :: left) head right
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .left)
        (afterRightPath scanPath (MStarConcreteAlphabet.work :: left)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [scanPath, afterRightPath, List.reverse_append,
        List.append_assoc] using
        moveSimHead_left head hhead
          (pre ++ last :: MStarConcreteAlphabet.work :: left) boundary right
    · simp [scanPath, afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pre with
      | nil =>
          simpa [beforeLeftPath] using
            movePlaceLeft_boundary boundary hboundary
              (MStarConcreteAlphabet.work :: left) last
              (unheadTape head :: right)
      | cons x xs =>
          simpa [beforeLeftPath, List.append_assoc] using
            movePlaceLeft_boundary boundary hboundary
              (xs ++ last :: MStarConcreteAlphabet.work :: left) x
              (unheadTape head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨shift⟩ := shiftRuntimeLeft_restored_bounded boundary pre last
    hshift hreturn left (ulogCore payloadHeadBlank) (by native_decide)
    (unheadTape head :: right)
  refine ⟨
    { steps := scanPath.length + 2 + shift.steps
      le_bound := by
        have hs := shift.le_bound
        simp [scanPath]
        omega
      run := by
        simpa [scanPath, Nat.add_assoc] using
          ((hscanRun.append hmove).append hplace).append shift.run }⟩

theorem moveRightBoundary_cleanup_bounded_radius
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head boundary : Tape)
    (shiftPrefix : List Tape) (last : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hhead : choiceHead head = true)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (shiftPrefix ++ [last]))
    (hreturn : ReturnMovedSafe (shiftPrefix.reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head]))
    {R : ℕ} (hp : programPrefix.length ≤ R)
    (hs : scanPath.length ≤ R) (hpcLen : pcPath.length ≤ R)
    (hshiftLen : shiftPrefix.length ≤ R) :
    Nonempty (BoundedStopFreeRun (9 * R + 13)
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape head) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩)) := by
  obtain ⟨move⟩ := moveRightBoundary_bounded scanPath shiftPrefix hscan
    boundary last hboundary hshift hreturn
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  let restore := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [unheadTape head]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
    (by decide) (boundary :: shiftPrefix ++ last :: right)
  have hrestoreFuel : restore.1 =
      2 * pcPath.length +
        2 * (programPrefix ++ scanPath ++ [unheadTape head]).length + 5 := by
    dsimp [restore]
    exact restoreCycle_fuel_eq pcPath terminal
      (programPrefix ++ scanPath ++ [unheadTape head]) outer
      (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
      (by decide) (boundary :: shiftPrefix ++ last :: right)
  have hrestore : StopFreeValidZeroRun restore.1
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [unheadTape head])).reverse ++
              ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩)
      (.running .cycleStart
        ⟨(programPrefix ++ scanPath ++ [unheadTape head]).reverse.map
              restoreProgramCell ++ ulogCore codeOne ::
            pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := restore.2
  have hmove : StopFreeValidZeroRun move.steps
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer) head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [unheadTape head])).reverse ++
              ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
    simpa [List.reverse_append, List.append_assoc] using move.run
  refine ⟨
    { steps := move.steps + restore.1
      le_bound := ?_
      run := by
        simpa [List.reverse_append, List.map_append, List.append_assoc] using
          hmove.append hrestore }⟩
  have hm := move.le_bound
  rw [hrestoreFuel]
  simp only [List.length_append, List.length_singleton]
  omega

theorem moveLeftBoundary_cleanup_bounded_radius
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPath ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe
      (scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse ++ [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse).reverse ++ [boundary]))
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [boundary])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [boundary]))
    {R : ℕ} (hp : programPrefix.length ≤ R)
    (hs : scanPath.length ≤ R) (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (13 * R + 16)
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩)) := by
  let shiftPrefix := scanPath.reverse ++ programPrefix.reverse ++
    terminal :: pcPath.reverse
  have hscanRun := stopFree_moveScan .left (scanPath ++ [boundary]) hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer) head right
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .left)
        (afterRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [shiftPrefix, afterRightPath, List.reverse_append,
        List.append_assoc] using
        moveSimHead_left head hhead
          (shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer) boundary right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (shiftPrefix ++ [ulogCore pcMark]) outer
          MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hprefix : shiftPrefix with
      | nil =>
          simpa [beforeLeftPath, hprefix] using
            movePlaceLeft_boundary boundary hboundary
              (MStarConcreteAlphabet.work :: outer) (ulogCore pcMark)
              (unheadTape head :: right)
      | cons x xs =>
          simpa [beforeLeftPath, hprefix, List.append_assoc] using
            movePlaceLeft_boundary boundary hboundary
              (xs ++ ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
              x (unheadTape head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨shift⟩ := shiftRuntimeLeft_restored_bounded boundary shiftPrefix
    (ulogCore pcMark) (by simpa [shiftPrefix] using hshift)
    (by simpa [shiftPrefix] using hreturn) outer
    (ulogCore payloadHeadBlank) (by decide)
    (unheadTape head :: right)
  have hmoveRestore : StopFreeValidZeroRun
      ((scanPath ++ [boundary]).length + 2 + shift.steps)
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [boundary])).reverse ++
              ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
    have hall := (hscanRun.append hmove).append hplace
    simpa [shiftPrefix, Nat.add_assoc, List.reverse_append,
      List.append_assoc] using hall.append shift.run
  let restore := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [boundary]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
    (by decide) (unheadTape head :: right)
  have hrestoreFuel : restore.1 =
      2 * pcPath.length +
        2 * (programPrefix ++ scanPath ++ [boundary]).length + 5 := by
    dsimp [restore]
    exact restoreCycle_fuel_eq pcPath terminal
      (programPrefix ++ scanPath ++ [boundary]) outer
      (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
      (by decide) (unheadTape head :: right)
  refine ⟨
    { steps := (scanPath ++ [boundary]).length + 2 + shift.steps + restore.1
      le_bound := ?_
      run := by
        simpa [shiftPrefix, List.reverse_append, List.map_append,
          List.append_assoc] using hmoveRestore.append restore.2 }⟩
  have hshiftBound := shift.le_bound
  rw [hrestoreFuel]
  simp [shiftPrefix] at hshiftBound ⊢
  omega

/-! ## Complete boundary tails -/

theorem matchedAtMost_rightBoundary_tail_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .right ++ scanPath ++ writeHeadNat write :: boundary :: runtime))
    (hdecomp : matchedMoveLeft write target .right left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe
      (runtime ++ List.replicate target (ulogCore stateZero) ++
        [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((runtime ++ List.replicate target (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++
            [unheadTape (writeHeadNat write)])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .right ++ scanPath ++
        writeHeadNat write :: boundary :: runtime).length ≤ R)
    (hstate : target + (extra + 1) ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R)
    (hshiftLen :
      (runtime ++ List.replicate target (ulogCore stateZero) ++
        [ulogCore stateOne]).length ≤ R) :
    Nonempty (BoundedStopFreeRun (16 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .right ++ scanPath)
        oldHead
        ((boundary :: runtime) ++
          List.replicate (target + (extra + 1)) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtMost_to_move_bounded_radius write
    target (extra + 1) hwrite htarget .right scanPath (boundary :: runtime)
    oldHead hhead hwritePath htargetPath left suffix hwriteLen htargetLen hstate
  obtain ⟨cleanup⟩ := moveRightBoundary_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal outer (writeHeadNat write) boundary
    (runtime ++ List.replicate target (ulogCore stateZero) ++ [ulogCore stateOne])
    (ulogCore stateSep)
    (List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan (by interval_cases write <;> decide) hboundary
    (by simpa [List.append_assoc] using hshift)
    (by simpa [List.append_assoc] using hreturn)
    hclock hpc hterminal hprogram hp hs hpcLen hshiftLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath (matchedMoveLeft write target .right left)
          (writeHeadNat write)
          ((boundary :: runtime) ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hdecomp]
    simpa [List.replicate_succ, List.cons_append,
      List.append_assoc] using cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.cons_append, List.append_assoc] using
          action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

theorem matchedAtLeast_rightBoundary_tail_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .right ++ scanPath ++ writeHeadNat write :: boundary :: runtime))
    (hdecomp : matchedMoveLeft write (current + growth) .right left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: outer)
    (hscan : MoveScanSafe scanPath)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe
      (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
        [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++
            [unheadTape (writeHeadNat write)])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape (writeHeadNat write)]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .right ++ scanPath).length ≤ R)
    (htargetLen :
      (moveBits .right ++ scanPath ++
        writeHeadNat write :: boundary :: runtime).length ≤ R)
    (hstate : current + growth ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R)
    (hshiftLen :
      (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
        [ulogCore stateOne]).length ≤ R) :
    Nonempty (BoundedStopFreeRun (20 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .right ++ scanPath)
        oldHead
        ((boundary :: runtime) ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work :: suffix))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtLeast_to_move_bounded_radius write
    current growth hwrite htarget .right scanPath (boundary :: runtime)
    oldHead hhead hwritePath htargetPath left
    (MStarConcreteAlphabet.work :: suffix) hwriteLen htargetLen hstate
  obtain ⟨cleanup⟩ := moveRightBoundary_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal outer (writeHeadNat write) boundary
    (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
      [ulogCore stateOne])
    (ulogCore stateSep) suffix hscan
    (by interval_cases write <;> decide) hboundary
    (by simpa [List.append_assoc] using hshift)
    (by simpa [List.append_assoc] using hreturn)
    hclock hpc hterminal hprogram hp hs hpcLen hshiftLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (matchedMoveLeft write (current + growth) .right left)
          (writeHeadNat write)
          ((boundary :: runtime) ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                MStarConcreteAlphabet.work :: suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape (writeHeadNat write)) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hdecomp]
    simpa [List.cons_append, List.append_assoc] using cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.cons_append, List.append_assoc] using
          action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

theorem matchedAtMost_leftBoundary_tail_bounded_radius
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary]))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .left ++ scanPath ++ [boundary] ++
        writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write target .left left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    (hscan : MoveScanSafe (scanPath ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe
      (scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse ++ [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [boundary])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [boundary]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary]).length ≤ R)
    (htargetLen :
      (moveBits .left ++ scanPath ++ [boundary] ++
        writeHeadNat write :: runtime).length ≤ R)
    (hstate : target + (extra + 1) ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (20 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary])
        oldHead
        (runtime ++ List.replicate (target + (extra + 1))
            (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtMost_to_move_bounded_radius write
    target (extra + 1) hwrite htarget .left (scanPath ++ [boundary]) runtime
    oldHead hhead (by simpa [List.append_assoc] using hwritePath)
    (by simpa [List.append_assoc] using htargetPath) left suffix
    (by simpa [List.append_assoc] using hwriteLen)
    (by simpa [List.append_assoc] using htargetLen) hstate
  obtain ⟨cleanup⟩ := moveLeftBoundary_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal boundary outer (writeHeadNat write)
    (runtime ++ List.replicate target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (extra + 1) MStarConcreteAlphabet.work ++ suffix)
    hscan hboundary hshift hreturn
    (by interval_cases write <;> decide) hclock hpc hterminal hprogram
    hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (matchedMoveLeft write target .left left) (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩) := by
    rw [hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

theorem matchedAtLeast_leftBoundary_tail_bounded_radius
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer runtime suffix : List Tape) (left : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary]))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits .left ++ scanPath ++ [boundary] ++
        writeHeadNat write :: runtime))
    (hdecomp : matchedMoveLeft write (current + growth) .left left =
      programPrefix.reverse ++ terminal :: pcPath.reverse ++
        ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    (hscan : MoveScanSafe (scanPath ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe
      (scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse ++ [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [boundary])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [boundary]))
    {R : ℕ}
    (hwriteLen :
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary]).length ≤ R)
    (htargetLen :
      (moveBits .left ++ scanPath ++ [boundary] ++
        writeHeadNat write :: runtime).length ≤ R)
    (hstate : current + growth ≤ R)
    (hp : programPrefix.length ≤ R) (hs : scanPath.length ≤ R)
    (hpcLen : pcPath.length ≤ R) :
    Nonempty (BoundedStopFreeRun (24 * (R + 1) ^ 2)
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits .left ++ scanPath ++ [boundary])
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)) := by
  obtain ⟨action⟩ := matchedActionAtLeast_to_move_bounded_radius write
    current growth hwrite htarget .left (scanPath ++ [boundary]) runtime
    oldHead hhead (by simpa [List.append_assoc] using hwritePath)
    (by simpa [List.append_assoc] using htargetPath) left suffix
    (by simpa [List.append_assoc] using hwriteLen)
    (by simpa [List.append_assoc] using htargetLen) hstate
  obtain ⟨cleanup⟩ := moveLeftBoundary_cleanup_bounded_radius
    programPrefix scanPath pcPath terminal boundary outer (writeHeadNat write)
    (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan hboundary hshift hreturn
    (by interval_cases write <;> decide) hclock hpc hterminal hprogram
    hp hs hpcLen
  have hcleanup : StopFreeValidZeroRun cleanup.steps
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (matchedMoveLeft write (current + growth) .left left)
          (writeHeadNat write)
          (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat write) :: runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hdecomp]
    exact cleanup.run
  refine ⟨
    { steps := action.steps + cleanup.steps
      le_bound := ?_
      run := by
        simpa [List.append_assoc] using action.run.append hcleanup }⟩
  have ha := action.le_bound
  have hc := cleanup.le_bound
  nlinarith [sq_nonneg (R : ℤ)]

/-! ## Uniform ten-branch assembly budget -/

/-- Arithmetic interface shared by all ten branches.  `cursorSteps` is kept
in its sharp mismatch-fold form; using only the coarser cubic common-prefix
corollary would spend the quadratic coefficient twice.  The factor `32` is
literal in `canonicalMismatchBudget`. -/
theorem tenBranch_cyclePolynomial_arithmetic
    {R skip choiceSteps dynamicSteps cursorSteps tailSteps : ℕ}
    (hR : 32 ≤ R)
    (hskip : 32 * skip ≤ R)
    (hchoice : choiceSteps ≤ 4 * R + 3)
    (hdynamic : dynamicSteps ≤ 2 * R + 2)
    (hcursor : cursorSteps ≤
      skip * (6 * R ^ 2 + 17 * R + 18) +
        (6 * R ^ 2 + 11 * R + 13))
    (htail : tailSteps ≤ 24 * (R + 1) ^ 2) :
    choiceSteps + 1 + (dynamicSteps + cursorSteps + tailSteps) ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by
  let P := 6 * R ^ 2 + 17 * R + 18
  have hscaled := Nat.mul_le_mul_right P hskip
  have hR2 : 32 * R ≤ R ^ 2 := by nlinarith
  have hR3 : 32 * R ^ 2 ≤ R ^ 3 := by nlinarith
  dsimp [P] at hscaled
  nlinarith [sq_nonneg (R : ℤ)]

/-- Sharp common cursor prefix.  Unlike the convenience cubic corollary in
`PakULogCycleResourceBound`, this retains the actual number of skipped rules;
that ledger is what leaves room for the nonterminal quadratic tail inside the
same global polynomial. -/
theorem mismatchCertificateList_matchedActionWrite_bounded_sharp
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer tail : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hboundary : (canonicalRuleCursor skip (r :: rs)).boundary =
        sourceBoundary ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryZero ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead))) :
    let R := canonicalMismatchBudget current actual [] skip (r :: rs)
      programToHead runtime
    Nonempty (BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18) +
        (6 * R ^ 2 + 11 * R + 13))
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer tail)
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read
          (canonicalRuleCursor skip (r :: rs)).boundary
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++
            ulogCore pcDone :: (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer))
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail))) := by
  let R := canonicalMismatchBudget current actual [] skip (r :: rs)
    programToHead runtime
  obtain ⟨prefixRun⟩ := mismatchCertificateList_stopFree_atMost_budget slot
    current actual programToHead runtime outer tail certs (by simp) []
  have prefixRun' : BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer tail)
      (ruleCursorResult slot current actual
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        programToHead runtime outer tail) := by
    simpa [R, canonicalRuleCursor_initial] using prefixRun
  let final := canonicalRuleCursor skip (r :: rs)
  have radius := matchedTargetZeroWithin_canonicalBudget current actual [] skip
    r rs programToHead runtime
  obtain ⟨matched⟩ := ruleCursorMatched_actionWrite_bounded_radius
    final.boundary hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime tail hread hwrite hcorridor hreadPath radius.source_le
    radius.source_corridor_le radius.read_corridor_le
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have matched' : StopFreeValidZeroRun matched.steps
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer tail)
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer))
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail)) := by
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      List.append_assoc] using matched.run
  exact ⟨
    { steps := prefixRun'.steps + matched.steps
      le_bound := Nat.add_le_add prefixRun'.le_bound matched.le_bound
      run := by simpa [final] using prefixRun'.run.append matched' }⟩

/-- Final first-hit assembly shared by the ten physical branches.  The three
certificates must meet in one state, so no endpoints from separate runs are
combined. -/
theorem exactCycle_nonterminal_le_of_bounded_parts
    {slot : Bool} {start branch cursorStart actionStart finish : Result}
    (cycle : ExactConcreteCycle slot start finish)
    {R skip : ℕ}
    (hR : 32 ≤ R) (hskip : 32 * skip ≤ R)
    (hchoice : cycle.choicePrefix.steps ≤ 4 * R + 3)
    (dynamic : BoundedStopFreeRun (2 * R + 2) branch cursorStart)
    (hbranch : cycle.branch = branch)
    (cursor : BoundedStopFreeRun
      (skip * (6 * R ^ 2 + 17 * R + 18) +
        (6 * R ^ 2 + 11 * R + 13)) cursorStart actionStart)
    (tail : BoundedStopFreeRun (24 * (R + 1) ^ 2) actionStart finish)
    (hstop : IsConcreteCycleStop finish) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by
  have suffixRun : StopFreeValidZeroRun
      (dynamic.steps + cursor.steps + tail.steps) cycle.branch finish := by
    rw [hbranch]
    exact (dynamic.run.append cursor.run).append tail.run
  have hsuffix : cycle.cycleSuffix.steps ≤
      dynamic.steps + cursor.steps + tail.steps :=
    cycle.cycleSuffix.steps_le (suffixRun.toFirstHit hstop)
  calc
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
        cycle.choicePrefix.steps + 1 +
          (dynamic.steps + cursor.steps + tail.steps) :=
      Nat.add_le_add_left hsuffix _
    _ ≤ 6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 :=
      tenBranch_cyclePolynomial_arithmetic hR hskip hchoice
        dynamic.le_bound cursor.le_bound tail.le_bound

end PakFixedPolyomino.PakULogNonterminalTailFuel
