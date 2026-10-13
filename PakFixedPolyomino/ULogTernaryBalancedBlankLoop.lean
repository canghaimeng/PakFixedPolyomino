import PakFixedPolyomino.ULogTernaryReserveThresholdProbe
import PakFixedPolyomino.ULogTernaryBalancedBlankPair
import PakFixedPolyomino.ULogFiniteTapeTestBodyLoop
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter
/-! One finite ternary test/body feedback: frozen58 threshold probe and
frozen119 balanced pair. Program depends only on nt and blank. -/
namespace PakFixedPolyomino.ULogTernaryBalancedBlankLoop
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryOneHotBlockWriter
  (replicate_split replicate_add_run growth_append_le config_ext replicate_concat)
open ULogTernaryRetainedCounterPump (cells)
open FiniteOneTapeSemantics (moveHead)
abbrev K (nt : Nat) : Nat := 2 * (nt + 1)
abbrev ns (nt : Nat) : Nat := K nt + 8
abbrev ms (nt : Nat) : Nat := ULogTernaryBalancedBlankPair.states nt
abbrev loopStates (nt : Nat) : Nat :=
  ULogFiniteTapeTestBodyLoop.stateCount (ns nt) (ms nt)
theorem hK {nt : Nat} (_hnt : 0 < nt) : 0 < K nt := by simp [K]
theorem hns (nt : Nat) : 3 ≤ ns nt := by simp [ns, K]
theorem hms (nt : Nat) : 3 ≤ ms nt := by
  have h := ULogTernaryBalancedBlankPair.append_states_ge nt
  change 3 ≤ ULogFiniteTapeStageComposition.stateCount (ULogTernaryBalancedBlankPair.appendStates nt) 4
  unfold ULogFiniteTapeStageComposition.stateCount; omega
theorem loop_ge (nt : Nat) : 2 < loopStates nt := by
  simp [loopStates, ns, K, ULogFiniteTapeTestBodyLoop.stateCount]
def probe {nt : Nat} (hnt : 0 < nt) : BoundedProgram (ns nt) 3 :=
  ULogTernaryReserveThresholdProbe.program (K nt) (hK hnt)
def pairP {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) : BoundedProgram (ms nt) 3 :=
  ULogTernaryBalancedBlankPair.pairProgram hnt blank
def program {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    BoundedProgram (loopStates nt) 3 :=
  ULogFiniteTapeTestBodyLoop.program (probe hnt) (pairP hnt blank) (hns nt) (hms nt)
def marginBits {nt : Nat} (blank : Fin nt) (source : List Bool) : Nat → List Bool
  | 0 => source
  | m + 1 => ULogTernaryBalancedBlankPair.block blank ++ marginBits blank source m ++ ULogTernaryBalancedBlankPair.block blank
abbrev pool (nt m r : Nat) : Nat := K nt * m + r
def deadline (nt n m r : Nat) : Nat :=
  match m with
  | 0 => 2 * n + 2 * r + 5
  | m + 1 =>
      2 * n + 2 * K nt + 3 + ULogTernaryBalancedBlankPair.deadline nt n + 2 + deadline nt (n + K nt) m r
def initial {nt : Nat} (hnt : 0 < nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) : BoundedConfig (loopStates nt) 3 :=
  ULogFiniteTapeTestBodyLoop.testConfig (ms := ms nt) (ULogTernaryReserveThresholdProbe.initial (K nt) (hK hnt) source under buffer N)
def final {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (m r : Nat) : BoundedConfig (loopStates nt) 3 :=
  ⟨⟨0, by have := loop_ge nt; omega⟩, under, 2,
    ULogTernaryReserveThresholdProbe.srcRight (marginBits blank source m) r buffer⟩
theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    FalseOnly (program hnt blank) :=
  ULogFiniteTapeTestBodyLoop.program_falseOnly _ _ _ _ (ULogTernaryReserveThresholdProbe.program_falseOnly (K nt) (hK hnt))
    (ULogTernaryBalancedBlankPair.program_falseOnly hnt blank)
theorem wrap_length {nt : Nat} (blank : Fin nt) (source : List Bool) :
    (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank).length =
      source.length + K nt := by
  simp [ULogTernaryBalancedBlankPair.block_length, K]; omega
theorem margin_length {nt : Nat} (blank : Fin nt) (source : List Bool) (m : Nat) :
    (marginBits blank source m).length = source.length + K nt * m := by
  induction m with
  | zero => simp [marginBits]
  | succ m ih =>
      simp [marginBits, List.length_append, ULogTernaryBalancedBlankPair.block_length, ih, K, Nat.mul_succ]
      omega
theorem margin_wrap {nt : Nat} (blank : Fin nt) (source : List Bool) (m : Nat) :
    marginBits blank (ULogTernaryBalancedBlankPair.block blank ++ source ++
        ULogTernaryBalancedBlankPair.block blank) m =
      marginBits blank source (m + 1) := by
  induction m with
  | zero => simp [marginBits]
  | succ m ih =>
      change _ ++ marginBits blank (_ ++ source ++ _) m ++ _ =
        _ ++ marginBits blank source (m + 1) ++ _
      rw [ih]
theorem false_cycle (a b : Nat) :
    ((List.replicate a false ++ [false]) ++ (List.replicate b false ++ [false])) =
      List.replicate (a + b + 2) false := by
  rw [← replicate_concat, ← replicate_concat]
  have h : a + 1 + (b + 1) = a + b + 2 := by omega
  rw [← List.replicate_add, h]
theorem pair_initial_tape (nt : Nat) (source : List Bool) (under buffer : List (Fin 3)) :
    (ULogTernaryBalancedBlankPair.initial nt source under buffer).state.val = 2 ∧
    (ULogTernaryBalancedBlankPair.initial nt source under buffer).leftRev = under ∧
    (ULogTernaryBalancedBlankPair.initial nt source under buffer).focus = 2 ∧
    (ULogTernaryBalancedBlankPair.initial nt source under buffer).right =
      cells source ++ 2 :: List.replicate (2 * (nt + 1)) 0 ++ buffer := by
  have hrep : List.replicate (nt + 1) (0 : Fin 3) ++ List.replicate (nt + 1) 0 =
      List.replicate (2 * (nt + 1)) 0 := by
    have : nt + 1 + (nt + 1) = 2 * (nt + 1) := by omega
    simpa [this] using (List.replicate_add (nt + 1) (nt + 1) (0 : Fin 3)).symm
  simp [ULogTernaryBalancedBlankPair.initial, ULogTernaryBalancedBlankPair.appendInitial,
    ULogTernaryBalancedBlankPair.sweepInitial, ULogTernaryBalancedBlankPair.prefixInitial,
    ULogFiniteTapeStageComposition.leftConfig, ULogFiniteTapeStageComposition.leftState,
    ULogFiniteTapeSymbolDispatch.initial]
  rw [← List.append_assoc (List.replicate (nt + 1) (0 : Fin 3)), hrep]
theorem enough_body_start {nt : Nat} (hnt : 0 < nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (hKN : K nt ≤ N) :
    ULogFiniteTapeTestBodyLoop.bodyStart (hms nt)
        (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer N) =
      ULogTernaryBalancedBlankPair.initial nt source under (List.replicate (N - K nt) 0 ++ 2 :: buffer) := by
  have ht := pair_initial_tape nt source under (List.replicate (N - K nt) 0 ++ 2 :: buffer)
  apply config_ext
  · apply Fin.ext; simp [ULogFiniteTapeTestBodyLoop.bodyStart, ULogTernaryReserveThresholdProbe.final, ht.1]
  · simp [ULogFiniteTapeTestBodyLoop.bodyStart, ULogTernaryReserveThresholdProbe.final, ht.2.1]
  · simp [ULogFiniteTapeTestBodyLoop.bodyStart, ULogTernaryReserveThresholdProbe.final, ht.2.2.1]
  · simp [ULogFiniteTapeTestBodyLoop.bodyStart, ULogTernaryReserveThresholdProbe.final,
      ULogTernaryReserveThresholdProbe.srcRight]
    rw [ht.2.2.2, show 2 * (nt + 1) = K nt from rfl]
    have hrepN : List.replicate N (0 : Fin 3) =
        List.replicate (K nt) 0 ++ List.replicate (N - K nt) 0 := by
      conv_lhs => rw [← Nat.add_sub_of_le hKN]
      exact List.replicate_add _ _ _
    rw [hrepN]
    rw [List.append_assoc (List.replicate (K nt) (0 : Fin 3))
      (List.replicate (N - K nt) 0) (2 :: buffer)]
    rw [← List.cons_append, ← List.append_assoc]
theorem pair_test_start {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (remain : Nat) :
    ULogFiniteTapeTestBodyLoop.testStart (hns nt)
        (ULogTernaryBalancedBlankPair.final blank source under (List.replicate remain 0 ++ 2 :: buffer)) =
      ULogTernaryReserveThresholdProbe.initial (K nt) (hK hnt)
        (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank) under buffer remain := by
  have ht := ULogTernaryBalancedBlankPair.final_tape blank source under (List.replicate remain 0 ++ 2 :: buffer)
  apply config_ext
  · apply Fin.ext; simp [ULogFiniteTapeTestBodyLoop.testStart, ULogTernaryReserveThresholdProbe.initial, ULogTernaryReserveThresholdProbe.S]
  · simp [ULogFiniteTapeTestBodyLoop.testStart, ULogTernaryReserveThresholdProbe.initial, ht.1]
  · simp [ULogFiniteTapeTestBodyLoop.testStart, ULogTernaryReserveThresholdProbe.initial, ht.2.1]
  · simp [ULogFiniteTapeTestBodyLoop.testStart, ULogTernaryReserveThresholdProbe.initial, ULogTernaryReserveThresholdProbe.srcRight, ht.2.2, List.append_assoc]
theorem short_final {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (r : Nat) (hr : r < K nt) :
    ULogFiniteTapeTestBodyLoop.testConfig (ms := ms nt)
        (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer r) =
      final hnt blank source under buffer 0 r := by
  have ha : (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer r).state.val = 1 := by
    simp [ULogTernaryReserveThresholdProbe.final, ULogTernaryReserveThresholdProbe.S, show ¬ K nt ≤ r by omega]
  apply config_ext
  · apply Fin.ext
    simpa [final] using ULogFiniteTapeTestBodyLoop.test_stop_accepts (ms := ms nt)
      (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer r) ha
  · simp [ULogFiniteTapeTestBodyLoop.testConfig, ULogTernaryReserveThresholdProbe.final, final]
  · simp [ULogFiniteTapeTestBodyLoop.testConfig, ULogTernaryReserveThresholdProbe.final, final]
  · simp [ULogFiniteTapeTestBodyLoop.testConfig, ULogTernaryReserveThresholdProbe.final, final, marginBits]
theorem probe_short_deadline (nt n r : Nat) (hr : r < K nt) :
    ULogTernaryReserveThresholdProbe.deadline n (K nt) r = 2 * n + 2 * r + 5 := by
  simp [ULogTernaryReserveThresholdProbe.deadline, show ¬ K nt ≤ r by omega]
theorem probe_enough_deadline (nt n N : Nat) (hKN : K nt ≤ N) :
    ULogTernaryReserveThresholdProbe.deadline n (K nt) N = 2 * n + 2 * K nt + 3 := by
  simp [ULogTernaryReserveThresholdProbe.deadline, hKN]
theorem run_short {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (r : Nat) (hr : r < K nt) (H : Int) :
    run (program hnt blank) 2 (List.replicate (deadline nt source.length 0 r) false) H
      (initial hnt source under buffer (pool nt 0 r)) =
      some (H, final hnt blank source under buffer 0 r) := by
  have hp := ULogTernaryReserveThresholdProbe.actual_run (K nt) (hK hnt) source under buffer r H
  have ht := ULogFiniteTapeTestBodyLoop.run_test (probe hnt) (pairP hnt blank) (hns nt) (hms nt) (2 : Fin 3)
    (List.replicate (ULogTernaryReserveThresholdProbe.deadline source.length (K nt) r) false) H H
    (ULogTernaryReserveThresholdProbe.initial (K nt) (hK hnt) source under buffer r)
    (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer r) hp
  rw [probe_short_deadline nt source.length r hr] at ht
  rw [short_final hnt blank source under buffer r hr] at ht
  simpa [program, initial, pool, deadline] using ht
theorem run_cycle {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (m r : Nat) (hr : r < K nt) (H : Int)
    (ih : run (program hnt blank) 2
        (List.replicate (deadline nt (source.length + K nt) m r) false) H
        (initial hnt (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank) under buffer
          (pool nt m r)) =
        some (H, final hnt blank (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank)
          under buffer m r)) :
    run (program hnt blank) 2
      (List.replicate (deadline nt source.length (m + 1) r) false) H
      (initial hnt source under buffer (pool nt (m + 1) r)) =
      some (H, final hnt blank source under buffer (m + 1) r) := by
  have hKN : K nt ≤ pool nt (m + 1) r :=
    le_trans (Nat.le_mul_of_pos_right (K nt) (Nat.succ_pos m)) (Nat.le_add_right _ r)
  have hN : pool nt (m + 1) r - K nt = pool nt m r := by
    change K nt * (m + 1) + r - K nt = K nt * m + r
    rw [Nat.mul_succ, Nat.add_right_comm (K nt * m) (K nt) r, Nat.add_sub_cancel]
  have hu := ULogTernaryReserveThresholdProbe.actual_run (K nt) (hK hnt) source under buffer (pool nt (m + 1) r) H
  have ha : (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer (pool nt (m + 1) r)).state.val = 0 := by
    simp [ULogTernaryReserveThresholdProbe.final, ULogTernaryReserveThresholdProbe.S, hKN]
  have hb := ULogTernaryBalancedBlankPair.final_accepts blank source under
    (List.replicate (pool nt m r) 0 ++ 2 :: buffer)
  have hq := ULogTernaryBalancedBlankPair.actual_run hnt blank source under
    (List.replicate (pool nt m r) 0 ++ 2 :: buffer) H
  have hstart := enough_body_start hnt source under buffer (pool nt (m + 1) r) hKN
  rw [hN] at hstart
  have hq' : run (pairP hnt blank) 2
      (List.replicate (ULogTernaryBalancedBlankPair.deadline nt source.length) false) H
      (ULogFiniteTapeTestBodyLoop.bodyStart (hms nt)
        (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer (pool nt (m + 1) r))) =
      some (H, ULogTernaryBalancedBlankPair.final blank source under
        (List.replicate (pool nt m r) 0 ++ 2 :: buffer)) := by
    rw [hstart]; simpa [pairP] using hq
  have hcycle := ULogFiniteTapeTestBodyLoop.cycle_run (probe hnt) (pairP hnt blank) (hns nt) (hms nt) (2 : Fin 3)
    (List.replicate (ULogTernaryReserveThresholdProbe.deadline source.length (K nt) (pool nt (m + 1) r)) false)
    (List.replicate (ULogTernaryBalancedBlankPair.deadline nt source.length) false) H H H
    (ULogTernaryReserveThresholdProbe.initial (K nt) (hK hnt) source under buffer (pool nt (m + 1) r))
    (ULogTernaryReserveThresholdProbe.final (K nt) (hK hnt) source under buffer (pool nt (m + 1) r))
    (ULogTernaryBalancedBlankPair.final blank source under (List.replicate (pool nt m r) 0 ++ 2 :: buffer))
    hu ha hq' hb
  have hD0 : ULogTernaryReserveThresholdProbe.deadline source.length (K nt) (pool nt (m + 1) r) =
      2 * source.length + 2 * K nt + 3 := probe_enough_deadline _ _ _ hKN
  have hsum : deadline nt source.length (m + 1) r =
      (2 * source.length + 2 * K nt + 3 + ULogTernaryBalancedBlankPair.deadline nt source.length + 2) +
        deadline nt (source.length + K nt) m r := rfl
  have hword := false_cycle (2 * source.length + 2 * K nt + 3)
    (ULogTernaryBalancedBlankPair.deadline nt source.length)
  have hrest : ULogFiniteTapeTestBodyLoop.testConfig (ms := ms nt)
      (ULogFiniteTapeTestBodyLoop.testStart (hns nt)
        (ULogTernaryBalancedBlankPair.final blank source under (List.replicate (pool nt m r) 0 ++ 2 :: buffer))) =
      initial hnt (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank)
        under buffer (pool nt m r) := by
    rw [pair_test_start hnt blank source under buffer (pool nt m r)]; rfl
  have hfin : final hnt blank (ULogTernaryBalancedBlankPair.block blank ++ source ++
        ULogTernaryBalancedBlankPair.block blank) under buffer m r =
      final hnt blank source under buffer (m + 1) r := by
    apply config_ext
    · apply Fin.ext; simp [final]
    · simp [final]
    · simp [final]
    · simp [final]
      rw [← List.append_assoc]
      exact congrArg (fun s => ULogTernaryReserveThresholdProbe.srcRight s r buffer)
        (margin_wrap blank source m)
  have hcycle' : run (program hnt blank) 2
      (List.replicate (2 * source.length + 2 * K nt + 3 + ULogTernaryBalancedBlankPair.deadline nt source.length + 2) false)
      H (initial hnt source under buffer (pool nt (m + 1) r)) =
      some (H, initial hnt (ULogTernaryBalancedBlankPair.block blank ++ source ++
        ULogTernaryBalancedBlankPair.block blank) under buffer (pool nt m r)) := by
    rw [hD0, hword, hrest] at hcycle
    simpa [program, initial] using hcycle
  have hjoin := replicate_add_run (program hnt blank) (2 : Fin 3)
    (2 * source.length + 2 * K nt + 3 + ULogTernaryBalancedBlankPair.deadline nt source.length + 2)
    (deadline nt (source.length + K nt) m r) H
    (initial hnt source under buffer (pool nt (m + 1) r)) hcycle' ih
  rw [hfin] at hjoin
  rw [hsum]
  exact hjoin
theorem actual_run_m {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (m r : Nat) (hr : r < K nt) (H : Int) :
    run (program hnt blank) 2 (List.replicate (deadline nt source.length m r) false) H
      (initial hnt source under buffer (pool nt m r)) =
      some (H, final hnt blank source under buffer m r) := by
  induction m generalizing source with
  | zero => exact run_short hnt blank source under buffer r hr H
  | succ m ih =>
      refine run_cycle hnt blank source under buffer m r hr H ?_
      have hih :=
        ih (ULogTernaryBalancedBlankPair.block blank ++ source ++ ULogTernaryBalancedBlankPair.block blank)
      rw [wrap_length] at hih
      exact hih
theorem actual_run {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    run (program hnt blank) 2
      (List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false) H
      (initial hnt source under buffer N) =
      some (H, final hnt blank source under buffer (N / K nt) (N % K nt)) := by
  have hdiv : N = pool nt (N / K nt) (N % K nt) := (Nat.div_add_mod N (K nt)).symm
  have hr : N % K nt < K nt := Nat.mod_lt _ (hK hnt)
  have h := actual_run_m hnt blank source under buffer (N / K nt) (N % K nt) hr H
  rw [← hdiv] at h
  exact h
theorem final_accepts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (m r : Nat) :
    (final hnt blank source under buffer m r).state.val = 0 := rfl
theorem actual_growth {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    GrowthRun (program hnt blank) 2
      (List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false) H
      (initial hnt source under buffer N) H
      (final hnt blank source under buffer (N / K nt) (N % K nt)) 0 0 := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt blank) 2
    (List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false) H H
    (initial hnt source under buffer N)
    (final hnt blank source under buffer (N / K nt) (N % K nt))
    (actual_run hnt blank source under buffer N H)
  have ⟨hl, hr', hc, _⟩ := hg.exact_ledger
  have hmlen := margin_length blank source (N / K nt)
  have hdiv : N = K nt * (N / K nt) + N % K nt := (Nat.div_add_mod N (K nt)).symm
  simp [leftEdge, rightEdge, cellCount, initial, final,
    ULogFiniteTapeTestBodyLoop.testConfig, ULogTernaryReserveThresholdProbe.initial,
    ULogTernaryReserveThresholdProbe.srcRight, cells, List.length_append, List.length_cons,
    List.length_replicate, List.length_map] at hl hr' hc
  rw [hmlen] at hr' hc
  have hlg : lg = 0 := by omega
  have hrg : rg = 0 := by
    simp [K] at hr' hc hdiv
    omega
  simpa [hlg, hrg] using hg
theorem every_raw {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (loopStates nt) 3}
    (hw : run (program hnt blank) 2 w H (initial hnt source under buffer N) = some (hf, out)) :
    w = List.replicate w.length false ∧
      w.length ≤ deadline nt source.length (N / K nt) (N % K nt) ∧
      cellCount out = cellCount (initial hnt source under buffer N) ∧
      GrowthRun (program hnt blank) 2 w H (initial hnt source under buffer N) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt blank) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length (N / K nt) (N % K nt)) H
    (initial hnt source under buffer N)
    (final hnt blank source under buffer (N / K nt) (N % K nt)) H
    (actual_run hnt blank source under buffer N H)
    (final_accepts hnt blank source under buffer (N / K nt) (N % K nt)) hw
  have hg := actual_growth hnt blank source under buffer N H
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run (program hnt blank) 2 w H hf
    (initial hnt source under buffer N) out hw
  have split : List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false =
      w ++ List.replicate (deadline nt source.length (N / K nt) (N % K nt) - w.length) false := by
    rw [hfalse]; simpa only [List.length_replicate] using replicate_split _ _ hlen
  have le := growth_append_le (by simpa [split] using hg) hg1
  have ⟨hl1, hr1, hc1, _⟩ := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [(by omega : lg1 = 0), (by omega : rg1 = 0)] using hg1⟩
theorem accepting_word {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig (loopStates nt) 3}
    (hw : run (program hnt blank) 2 w H (initial hnt source under buffer N) = some (hf, out))
    (ha : out.state.val = 0) :
    w = List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false ∧ hf = H ∧
      out = final hnt blank source under buffer (N / K nt) (N % K nt) :=
  accepting_zipper_word_eq (2 : Fin 3) _ (program_falseOnly hnt blank)
    (deadline nt source.length (N / K nt) (N % K nt)) H
    (initial hnt source under buffer N)
    (final hnt blank source under buffer (N / K nt) (N % K nt)) H
    (actual_run hnt blank source under buffer N H)
    (final_accepts hnt blank source under buffer (N / K nt) (N % K nt)) hw ha
theorem cutoff_counts {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) (source : List Bool)
    (under buffer : List (Fin 3)) (N : Nat) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial hnt source under buffer N)) =
      if deadline nt source.length (N / K nt) (N % K nt) ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) rfl _ (program_falseOnly hnt blank)
    (deadline nt source.length (N / K nt) (N % K nt)) H
    (initial hnt source under buffer N)
    (final hnt blank source under buffer (N / K nt) (N % K nt)) H
    (actual_run hnt blank source under buffer N H)
    (final_accepts hnt blank source under buffer (N / K nt) (N % K nt)) T
theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) (blank : Fin nt) :
    ∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3 := fun r hr =>
  ⟨(compile_rule_bounded (program hnt blank) hr).2.1,
    (compile_rule_bounded (program hnt blank) hr).2.2.1⟩
theorem balanced_blank_loop_spec {nt : Nat} (hnt : 0 < nt) (blank : Fin nt)
    (source : List Bool) (under buffer : List (Fin 3)) (N : Nat) (H : Int) :
    (run (program hnt blank) 2
      (List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false) H
      (initial hnt source under buffer N) =
      some (H, final hnt blank source under buffer (N / K nt) (N % K nt))) ∧
    (final hnt blank source under buffer (N / K nt) (N % K nt)).state.val = 0 ∧
    (final hnt blank source under buffer (N / K nt) (N % K nt)).leftRev = under ∧
    (final hnt blank source under buffer (N / K nt) (N % K nt)).focus = 2 ∧
    (final hnt blank source under buffer (N / K nt) (N % K nt)).right =
      ULogTernaryReserveThresholdProbe.srcRight (marginBits blank source (N / K nt)) (N % K nt) buffer ∧
    GrowthRun (program hnt blank) 2
      (List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false) H
      (initial hnt source under buffer N) H
      (final hnt blank source under buffer (N / K nt) (N % K nt)) 0 0 ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial hnt source under buffer N) =
      some (hf, out) → w = List.replicate w.length false ∧
      w.length ≤ deadline nt source.length (N / K nt) (N % K nt) ∧
      cellCount out = cellCount (initial hnt source under buffer N) ∧
      GrowthRun (program hnt blank) 2 w H (initial hnt source under buffer N) hf out 0 0) ∧
    (∀ w hf out, run (program hnt blank) 2 w H (initial hnt source under buffer N) =
      some (hf, out) → out.state.val = 0 →
      w = List.replicate (deadline nt source.length (N / K nt) (N % K nt)) false ∧
        hf = H ∧ out = final hnt blank source under buffer (N / K nt) (N % K nt)) ∧
    (∀ r ∈ compile (program hnt blank), r.read < 3 ∧ r.action.write < 3) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program hnt blank) (initial hnt source under buffer N)) =
        if deadline nt source.length (N / K nt) (N % K nt) ≤ T then 1 else 0) :=
  ⟨actual_run hnt blank source under buffer N H, rfl, rfl, rfl, rfl,
    actual_growth hnt blank source under buffer N H,
    fun _ _ _ => every_raw hnt blank source under buffer N H,
    fun _ _ _ => accepting_word hnt blank source under buffer N H,
    compiled_symbols hnt blank, cutoff_counts hnt blank source under buffer N H⟩
end PakFixedPolyomino.ULogTernaryBalancedBlankLoop
