import PakFixedPolyomino.ULogTernaryGeneratedMarginLoopResources
import PakFixedPolyomino.ULogTernaryGeneratedMarginScanner
import PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts
import PakFixedPolyomino.ULogSourceObliviousAllPrefixGrowth
import PakFixedPolyomino.ULogFiniteTapeBoundedGrowthReadiness
import PakFixedPolyomino.ULogFiniteTapeFreshAcceptingSplit

/-! ALL successful labelled prefixes of the actual whole compact
loader / exhausting Loop / RIGHT highest-state guard / STAY handoff /
fresh LEFT / old ND scanner have allocated growth at most LG 1 and
RG R+1. The central theorem derives AllGrowthBounded internally from
the exact edge ledger. Physical time and the original headline remain
separate. -/

namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPrefixGrowth

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapeGuardedStageComposition
open ULogTernaryGeneratedMarginScanner
open StandardNondeterministicMachine hiding run initial run_append
open ULogSourceObliviousBytecode (boundedProgram)
open ULogFreshEntry (insertConfig)
open FiniteOneTapeSemantics (moveHead)
open ULogFiniteTapeGuardedStageLeafCounts (zipperSlotRun_eq_run)
open ULogFiniteTapeBoundedGrowthReadiness (AllGrowthBounded)

variable {ns nt : Nat}
set_option maxHeartbeats 1000000

theorem tape_edge_eq {ns1 ns2 nα : Nat} (h1 h2 : Int)
    (z1 : BoundedConfig ns1 nα) (z2 : BoundedConfig ns2 nα)
    (hl : z1.leftRev = z2.leftRev) (hr : z1.right = z2.right) (hh : h1 = h2) :
    leftEdge h1 z1 = leftEdge h2 z2 ∧ rightEdge h1 z1 = rightEdge h2 z2 := by
  simp [leftEdge, rightEdge, hl, hr, hh]

theorem leftConfig_edges {ms : Nat} (head : Int) (z : BoundedConfig ns nt) :
    leftEdge head (leftConfig (ms := ms) z) = leftEdge head z ∧
    rightEdge head (leftConfig (ms := ms) z) = rightEdge head z := by
  simp [leftEdge, rightEdge, leftConfig]

theorem rightConfig_edges {ms : Nat} (head : Int) (z : BoundedConfig ms nt) :
    leftEdge head (rightConfig (ns := ns) z) = leftEdge head z ∧
    rightEdge head (rightConfig (ns := ns) z) = rightEdge head z := by
  simp [leftEdge, rightEdge, rightConfig]

theorem insertConfig_edges {k : Nat} (head : Int) (z : BoundedConfig (2 + k) 3) :
    leftEdge head (insertConfig z) = leftEdge head z ∧
    rightEdge head (insertConfig z) = rightEdge head z := by
  simp [leftEdge, rightEdge, insertConfig]

theorem loop_final_right_nonempty (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    (ULogTernaryGeneratedMarginLoop.final M p x).right ≠ [] := by
  have h := (ULogTernaryGeneratedMarginLoop.final_window M p x).2.2.2
  rw [h]; simp

theorem guard_right_same_edges (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
        (guardConfig (ms := scannerStates M) (2 : Fin 3) .right
          (ULogTernaryGeneratedMarginLoop.final M p x)) =
      leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) ∧
    rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
        (guardConfig (ms := scannerStates M) (2 : Fin 3) .right
          (ULogTernaryGeneratedMarginLoop.final M p x)) =
      rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) := by
  have hr := loop_final_right_nonempty M p x
  cases hrt : (ULogTernaryGeneratedMarginLoop.final M p x).right with
  | nil => exact (hr hrt).elim
  | cons y ys =>
      simp [guardConfig, leftConfig, applyBounded, leftEdge, rightEdge, hrt]
      omega

theorem scanner_tape (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    (scannerInitial M p x).leftRev = (ULogTernaryGeneratedMarginLoop.final M p x).leftRev ∧
    (scannerInitial M p x).focus = (ULogTernaryGeneratedMarginLoop.final M p x).focus ∧
    (scannerInitial M p x).right = (ULogTernaryGeneratedMarginLoop.final M p x).right := by
  have hf := ULogTernaryGeneratedMarginLoop.final_window M p x
  simp [scannerInitial, ULogTernaryGeneratedMarginSourceCounts.scannerInitial, suffix,
    hf.2.1, hf.2.2.1, hf.2.2.2, List.append_assoc, List.cons_append]

theorem scanner_initial_edges (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) =
      leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) ∧
    rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) =
      rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) := by
  have t := scanner_tape M p x
  simp [leftEdge, rightEdge, t.1, t.2.2]

theorem boot_initial_same_edges {k : Nat} (z : BoundedConfig (2 + k) 3) (H : Int)
    (hr : z.right ≠ []) :
    leftEdge (H + 1) (ULogFreshEntryExteriorBoot.initial z) = leftEdge H z ∧
    rightEdge (H + 1) (ULogFreshEntryExteriorBoot.initial z) = rightEdge H z := by
  cases hrt : z.right with
  | nil => exact (hr hrt).elim
  | cons y ys =>
      simp [ULogFreshEntryExteriorBoot.initial, applyBounded, leftEdge, rightEdge, hrt]
      omega

theorem fresh_all_split {k : Nat} (q : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (3 + k) 3)
    (hw : run (ULogFreshEntry.program q z.state) 2 w (H + 1)
      (ULogFreshEntryExteriorBoot.initial z) = some (hf, out)) :
    (w = [] ∧ hf = H + 1 ∧ out = ULogFreshEntryExteriorBoot.initial z) ∨
      ∃ rest old, w = false :: rest ∧
        run q 2 rest H z = some (hf, old) ∧ out = insertConfig old := by
  cases w with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | cons slot rest =>
      cases slot with
      | true =>
          cases hz : z.right with
          | nil => exact (hr hz).elim
          | cons a right =>
              simp [run, ULogFreshEntryExteriorBoot.initial, applyBounded, hz,
                boundedHalted, ULogFreshEntry.entryState, ULogFreshEntry.program] at hw
      | false =>
          change run (ULogFreshEntry.program q z.state) 2 ([false] ++ rest) (H + 1)
            (ULogFreshEntryExteriorBoot.initial z) = some (hf, out) at hw
          rw [ULogFiniteTapeZipperRun.run_append,
            ULogFreshEntryExteriorBoot.actual_left_tick q z hr H,
            Option.bind_some] at hw
          have he := ULogFreshEntryRunBridge.zipperSlotRun_insertConfig q z.state rest H z
          rw [zipperSlotRun_eq_run, zipperSlotRun_eq_run, hw] at he
          obtain ⟨⟨hf0, old⟩, hrun, hout⟩ := Option.map_eq_some_iff.mp he.symm
          have hhead := (Prod.mk.inj hout).1
          have hconfig := (Prod.mk.inj hout).2
          change hf0 = hf at hhead
          change insertConfig old = out at hconfig
          subst hf0
          exact Or.inr ⟨rest, old, rfl, hrun, hconfig.symm⟩

theorem old_scanner_zero (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (left suffix : List (Fin 3))
    (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (ULogSourceObliviousBytecode.Active M)) 3)
    (hw : run (boundedProgram M) 2 slots H
      (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix) =
        some (hf, out)) :
    GrowthRun (boundedProgram M) 2 slots H
      (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix)
      hf out 0 0 := by
  have hlarge := ULogTernaryGeneratedMarginSourceCounts.radius_ge_time nt p x
  have hsource : RunsAtMost M x (ULogTernaryGeneratedMarginSourceCounts.radius nt p x) :=
    fun word z hz => (ht word z hz).trans hlarge
  have hw' := hw
  rw [ULogTernaryGeneratedMarginSourceCounts.scanner_initial_eq] at hw'
  simpa [ULogTernaryGeneratedMarginSourceCounts.scanner_initial_eq] using
    ULogSourceObliviousAllPrefixGrowth.all_raw_zero_growth M x
      (ULogTernaryGeneratedMarginSourceCounts.radius nt p x) hsource left suffix
      slots H hf out hw'

theorem second_stage_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (v : List Bool) (hf : Int)
    (zq : BoundedConfig (scannerStates M) 3)
    (hq : run (scannerProgram M) 2 v (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
      (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x)) = some (hf, zq)) :
    leftEdge hf zq =
      leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) ∧
    rightEdge hf zq =
      rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x)
        (ULogTernaryGeneratedMarginLoop.final M p x) := by
  have hr := ULogFreshEntryExteriorBoot.scanner_right_nonempty M p x
    (ULogTernaryGeneratedMarginLoop.under nt p x) (suffix nt p x)
  have hq' := hq
  change run (ULogFreshEntry.program (boundedProgram M) (scannerInitial M p x).state) 2 v
      (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
      (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x)) = some (hf, zq) at hq'
  rcases fresh_all_split (boundedProgram M) (scannerInitial M p x) hr
      (ULogTernaryGeneratedMarginLoop.head nt p x) hf v zq hq' with hnil | hrest
  · rcases hnil with ⟨_, rfl, rfl⟩
    have hb := boot_initial_same_edges (scannerInitial M p x)
      (ULogTernaryGeneratedMarginLoop.head nt p x) hr
    have hs := scanner_initial_edges M p x
    exact ⟨hb.1.trans hs.1, hb.2.trans hs.2⟩
  · obtain ⟨rest, old, _, hold, hcfg⟩ := hrest
    have zg := old_scanner_zero M p x ht (ULogTernaryGeneratedMarginLoop.under nt p x)
      (suffix nt p x) rest (ULogTernaryGeneratedMarginLoop.head nt p x) hf old (by
        simpa [scannerInitial] using hold)
    have led := zg.exact_ledger
    have hs := scanner_initial_edges M p x
    have htape := tape_edge_eq hf hf zq old
      (by simpa [insertConfig] using congrArg BoundedConfig.leftRev hcfg)
      (by simpa [insertConfig] using congrArg BoundedConfig.right hcfg) rfl
    have hL : leftEdge hf zq =
        leftEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) := by
      rw [htape.1, led.1]; simp [scannerInitial]
    have hR : rightEdge hf zq =
        rightEdge (ULogTernaryGeneratedMarginLoop.head nt p x) (scannerInitial M p x) := by
      rw [htape.2, led.2.1]; simp [scannerInitial]
    exact ⟨hL.trans hs.1, hR.trans hs.2⟩

theorem initial_whole_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    leftEdge 0 (initial M p x) = 0 ∧
    rightEdge 0 (initial M p x) =
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source
          (ULogTernaryGeneratedMarginLoop.depth nt p)
          (ULogTernaryGeneratedMarginLoop.seed nt p) x).length : Nat) := by
  simpa only [ULogTernaryGeneratedMarginScanner.initial, leftConfig, leftEdge, rightEdge] using
    ULogTernaryGeneratedMarginLoopResources.initial_edges nt p x

theorem caller_prefix_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    {w : List Bool} {hf : Int}
    {z' : BoundedConfig (ULogTernaryGeneratedMarginLoop.states nt p) 3}
    (hp : run (ULogTernaryGeneratedMarginLoop.program M p) 2 w 0
      (ULogTernaryGeneratedMarginLoop.initial nt p x) = some (hf, z')) :
    -1 ≤ leftEdge hf z' ∧
    rightEdge hf z' ≤
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source
          (ULogTernaryGeneratedMarginLoop.depth nt p)
          (ULogTernaryGeneratedMarginLoop.seed nt p) x).length +
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 : Nat) := by
  obtain ⟨lg, rg, hg, hl, hr⟩ :=
    ULogTernaryGeneratedMarginLoopResources.every_raw_growth M p x hp
  have e := hg.exact_ledger
  have hi := ULogTernaryGeneratedMarginLoopResources.initial_edges nt p x
  have hL : leftEdge hf z' = (0 : Int) - lg := by rw [e.1, hi.1]
  have hR : rightEdge hf z' =
      rightEdge 0 (ULogTernaryGeneratedMarginLoop.initial nt p x) + rg := e.2.1
  constructor
  · rw [hL]; omega
  · rw [hR, hi.2]
    push_cast
    omega

set_option maxHeartbeats 1000000 in
theorem endpoint_edges (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (hf : Int)
    (out : BoundedConfig (states M p) 3)
    (hw : ULogFiniteTapeZipperRun.run (program M p) 2 w 0 (initial M p x) =
      some (hf, out)) :
    -1 ≤ leftEdge hf out ∧
    rightEdge hf out ≤
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
        (ULogTernaryGuardedPumpSentinel.source
          (ULogTernaryGeneratedMarginLoop.depth nt p)
          (ULogTernaryGeneratedMarginLoop.seed nt p) x).length +
        ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 : Nat) := by
  rcases ULogFiniteTapeGuardedStageCompositionRuns.deterministic_first_stage_split
      (ULogTernaryGeneratedMarginLoop.program M p) (scannerProgram M)
      (ULogTernaryGeneratedMarginLoop.states_ge nt p) (scanner_states_ge M) .right
      (2 : Fin 3) (ULogTernaryGeneratedMarginLoop.program_falseOnly M p)
      (ULogTernaryGeneratedMarginLoop.deadline M p x) 0
      (ULogTernaryGeneratedMarginLoop.head nt p x)
      (ULogTernaryGeneratedMarginLoop.initial nt p x)
      (ULogTernaryGeneratedMarginLoop.final M p x)
      (ULogTernaryGeneratedMarginLoop.actual_run M p x)
      (ULogTernaryGeneratedMarginLoop.final_accepts M p x) w hf out hw with
    hfirst | hguard | hsecond
  · obtain ⟨_, z', hp, hout⟩ := hfirst
    have he := caller_prefix_edges M p x hp
    have htape := tape_edge_eq hf hf out z'
      (by simpa [leftConfig] using congrArg BoundedConfig.leftRev hout)
      (by simpa [leftConfig] using congrArg BoundedConfig.right hout) rfl
    rw [htape.1, htape.2]
    exact he
  · obtain ⟨_, hhf, hout⟩ := hguard
    have hs := guard_right_same_edges M p x
    have hfins := ULogTernaryGeneratedMarginLoopResources.final_edges M p x
    have hmove : hf = ULogTernaryGeneratedMarginLoop.head nt p x + 1 := by
      simpa [moveHead] using hhf
    have htape := tape_edge_eq hf (ULogTernaryGeneratedMarginLoop.head nt p x + 1) out
      (guardConfig (ms := scannerStates M) (2 : Fin 3) .right
        (ULogTernaryGeneratedMarginLoop.final M p x))
      (by simpa using congrArg BoundedConfig.leftRev hout)
      (by simpa using congrArg BoundedConfig.right hout) hmove
    rw [htape.1, htape.2, hs.1, hs.2, hfins.1, hfins.2]
    constructor
    · omega
    · rfl
  · obtain ⟨v, zq, _, hq, hout⟩ := hsecond
    have hq' : run (scannerProgram M) 2 v
        (ULogTernaryGeneratedMarginLoop.head nt p x + 1)
        (ULogFreshEntryExteriorBoot.initial (scannerInitial M p x)) = some (hf, zq) := by
      rw [handoff_start] at hq
      simpa [moveHead] using hq
    have hs := second_stage_edges M p x ht v hf zq hq'
    have htape := tape_edge_eq hf hf out zq
      (by simpa [rightConfig] using congrArg BoundedConfig.leftRev hout)
      (by simpa [rightConfig] using congrArg BoundedConfig.right hout) rfl
    have hfins := ULogTernaryGeneratedMarginLoopResources.final_edges M p x
    rw [htape.1, htape.2, hs.1, hs.2, hfins.1, hfins.2]
    constructor
    · omega
    · rfl

theorem every_raw_whole_growth (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (hw : ULogFiniteTapeZipperRun.run (program M p) 2 w 0 (initial M p x) =
      some (hf, out)) :
    ∃ lg rg, GrowthRun (program M p) 2 w 0 (initial M p x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program M p) 2 w 0 hf (initial M p x) out hw
  have e := hg.exact_ledger
  have hi := initial_whole_edges M p x
  have hb := endpoint_edges M p x ht w hf out hw
  have hL : leftEdge hf out = (0 : Int) - lg := by rw [e.1, hi.1]
  have hR : rightEdge hf out = rightEdge 0 (initial M p x) + rg := e.2.1
  have hlg : lg ≤ 1 := by rw [hL] at hb; omega
  have hrg : rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 := by
    rw [hR, hi.2] at hb
    push_cast at hb
    omega
  exact ⟨lg, rg, hg, hlg, hrg⟩

theorem whole_all_prefix_growth (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    AllGrowthBounded (program M p) 0 (initial M p x) 1
      (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) := by
  intro w hf out lg rg hgr
  have hw := hgr.actual_run
  obtain ⟨lg', rg', hg', hl', hr'⟩ := every_raw_whole_growth M p x ht w hf out hw
  have e1 := hgr.exact_ledger
  have e2 := hg'.exact_ledger
  have hlg : lg = lg' := by
    have hL1 := e1.1
    have hL2 := e2.1
    omega
  have hrg : rg = rg' := by
    have hR1 := e2.2.1
    have hR2 := e1.2.1
    omega
  exact ⟨hlg ▸ hl', hrg ▸ hr'⟩

def whole_scanner_all_prefix_growth_spec (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool)
    (_ht : RunsAtMost M x (2 ^ p.eval x.length)) : Prop :=
  (∀ w hf out,
    ULogFiniteTapeZipperRun.run (program M p) 2 w 0 (initial M p x) = some (hf, out) →
      ∃ lg rg, GrowthRun (program M p) 2 w 0 (initial M p x) hf out lg rg ∧
        lg ≤ 1 ∧ rg ≤ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) ∧
  AllGrowthBounded (program M p) 0 (initial M p x) 1
    (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1)

theorem whole_scanner_all_prefix_growth_spec_holds (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    whole_scanner_all_prefix_growth_spec M p x ht :=
  ⟨every_raw_whole_growth M p x ht, whole_all_prefix_growth M p x ht⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPrefixGrowth
