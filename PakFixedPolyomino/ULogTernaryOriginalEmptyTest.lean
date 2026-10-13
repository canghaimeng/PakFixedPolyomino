import PakFixedPolyomino.ULogTernaryBalancedBlankPair

/-! Read the original unary length immediately left of the source delimiter.
This test works even when source blank, zero and one are equal. Accept0 means
originally nonempty; reject1 means empty. Both branches restore the tape/head.
The margin caller has to turn these two outcomes into its actual live branch. -/
namespace PakFixedPolyomino.ULogTernaryOriginalEmptyTest
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger

def program : BoundedProgram 6 3 where
  rule q read slot := if slot then none else
    if q.val = 2 ∧ read.val = 2 then some ⟨2, 3, .left⟩
    else if q.val = 3 ∧ read.val = 1 then some ⟨1, 4, .right⟩
    else if q.val = 3 ∧ read.val = 2 then some ⟨2, 5, .right⟩
    else if q.val = 4 ∧ read.val = 2 then some ⟨2, 0, .stay⟩
    else if q.val = 5 ∧ read.val = 2 then some ⟨2, 1, .stay⟩
    else none

def initial (n : Nat) (under right : List (Fin 3)) : BoundedConfig 6 3 :=
  ⟨2, List.replicate n 1 ++ 2 :: under, 2, right⟩
def final (n : Nat) (under right : List (Fin 3)) : BoundedConfig 6 3 :=
  ⟨if n = 0 then 1 else 0, List.replicate n 1 ++ 2 :: under, 2, right⟩

theorem actual_run (n : Nat) (under right : List (Fin 3)) (H : Int) :
    run program 2 (List.replicate 3 false) H (initial n under right) =
      some (H, final n under right) := by
  cases n with
  | zero => simp [run, program, initial, final, applyBounded, boundedHalted,
      FiniteOneTapeSemantics.moveHead]
  | succ n => simp [run, program, initial, final, applyBounded, boundedHalted,
      FiniteOneTapeSemantics.moveHead, List.replicate_succ]

theorem program_falseOnly : FalseOnly program := by intro q read; simp [program]
theorem final_halted (n : Nat) (under right : List (Fin 3)) :
    boundedHalted (final n under right) = true := by
  by_cases h : n = 0 <;> simp [boundedHalted, final, h]
theorem final_state (n : Nat) (under right : List (Fin 3)) :
    (final n under right).state.val = if n = 0 then 1 else 0 := by
  by_cases h : n = 0 <;> simp [final, h]

theorem terminal_length_le {ns nt : Nat} (blank : Fin nt) (p : BoundedProgram ns nt)
    (hp : FalseOnly p) (L : Nat) (H hf : Int) (z zf : BoundedConfig ns nt)
    (full : run p blank (List.replicate L false) H z = some (hf, zf))
    (halt : boundedHalted zf = true) {w : List Bool} {out : Int × BoundedConfig ns nt}
    (hw : run p blank w H z = some out) : w.length ≤ L := by
  have hfalse := successful_zipper_is_false blank p hp hw
  by_contra hlen
  have hle : L ≤ w.length := by omega
  have split : w = List.replicate L false ++ List.replicate (w.length - L) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using
      ULogTernaryOneHotBlockWriter.replicate_split w.length L hle
  rw [split, run_append, full] at hw
  change run p blank (List.replicate (w.length - L) false) hf zf = some out at hw
  cases hpos : w.length - L with
  | zero => omega
  | succ k =>
      rw [hpos, List.replicate_succ, zipperSlotRun_halted_cons blank p halt] at hw
      cases hw

theorem terminal_word_eq {ns nt : Nat} (blank : Fin nt) (p : BoundedProgram ns nt)
    (hp : FalseOnly p) (L : Nat) (H hf : Int) (z zf : BoundedConfig ns nt)
    (full : run p blank (List.replicate L false) H z = some (hf, zf))
    (halt : boundedHalted zf = true) {w : List Bool} {h' : Int} {out : BoundedConfig ns nt}
    (hw : run p blank w H z = some (h', out)) (ho : boundedHalted out = true) :
    w = List.replicate L false ∧ h' = hf ∧ out = zf := by
  have hfalse := successful_zipper_is_false blank p hp hw
  have hlen := terminal_length_le blank p hp L H hf z zf full halt hw
  have heq : w.length = L := by
    by_contra hne
    have hpos : 0 < L - w.length := by omega
    have split : List.replicate L false = w ++ List.replicate (L - w.length) false := by
      rw [hfalse]
      simpa only [List.length_replicate] using
        ULogTernaryOneHotBlockWriter.replicate_split L w.length hlen
    rw [split, run_append, hw] at full
    change run p blank (List.replicate (L - w.length) false) h' out = some (hf, zf) at full
    cases hrest : L - w.length with
    | zero => omega
    | succ k =>
        rw [hrest, List.replicate_succ, zipperSlotRun_halted_cons blank p ho] at full
        cases full
  have word : w = List.replicate L false := by rw [hfalse, heq]
  refine ⟨word, ?_⟩
  rw [word] at hw
  exact Prod.mk.inj (Option.some.inj (hw.symm.trans full))

theorem rejecting_paths_zero {ns nt : Nat} (blank : Fin nt) (hblank : blank.val = 2)
    (p : BoundedProgram ns nt) (hp : FalseOnly p) (L : Nat) (H hf : Int)
    (z zf : BoundedConfig ns nt)
    (full : run p blank (List.replicate L false) H z = some (hf, zf))
    (reject : zf.state.val = 1) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig p z) = 0 := by
  induction L generalizing H z hf zf T with
  | zero =>
      have he : H = hf ∧ z = zf := by simpa [run] using full
      rcases he with ⟨_, rfl⟩
      have hh : ULogSemantics.halted (liftConfig p z) = true := by
        simp [ULogSemantics.halted, liftConfig, reject]
      have ha : ULogSemantics.accepting (liftConfig p z) = false := by
        simp [ULogSemantics.accepting, liftConfig, reject, ULogSemantics.acceptCode]
      simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine, hh, ha]
  | succ L ih =>
      obtain ⟨hnh, a, hrule, hrest⟩ := zipperSlotRun_replicate_succ blank full
      cases T with
      | zero =>
          have hh : ULogSemantics.halted (liftConfig p z) = false := hnh
          simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine, hh]
      | succ T =>
          have hh : ULogSemantics.halted (liftConfig p z) = false := hnh
          rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt ULogSemantics.machine hh T]
          change (List.map (ULogSemantics.machine.acceptingPaths T) (ULogSemantics.next (liftConfig p z))).sum = 0
          rw [next_false_only blank hblank p hp hnh hrule]
          change ULogSemantics.machine.acceptingPaths T (liftConfig p (applyBounded blank z a)) = 0
          exact ih (FiniteOneTapeSemantics.moveHead a.move H) hf (applyBounded blank z a) zf hrest reject T

theorem cells_unchanged (n : Nat) (under right : List (Fin 3)) :
    cellCount (final n under right) = cellCount (initial n under right) := rfl

theorem every_raw (n : Nat) (under right : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 6 3}
    (hw : run program 2 w H (initial n under right) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ 3 ∧
      cellCount out = cellCount (initial n under right) ∧
      GrowthRun program 2 w H (initial n under right) hf out 0 0 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _ program_falseOnly hw
  have hlen := terminal_length_le (2 : Fin 3) program program_falseOnly 3 H H
    (initial n under right) (final n under right) (actual_run n under right H)
    (final_halted n under right) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run program 2 _ _ _ _ _ (actual_run n under right H)
  have ledger := hg.exact_ledger
  have hc := cells_unchanged n under right
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  obtain ⟨lg1, rg1, hg1⟩ := every_actual_run program 2 w H hf _ out hw
  have split : List.replicate 3 false = w ++ List.replicate (3 - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  rw [split] at hg
  have le := ULogTernaryOneHotBlockWriter.growth_append_le hg hg1
  have hl1 : lg1 = 0 := by omega
  have hr1 : rg1 = 0 := by omega
  have ledger1 := hg1.exact_ledger
  exact ⟨hfalse, hlen, by omega, by simpa only [hl1, hr1] using hg1⟩

theorem every_terminal (n : Nat) (under right : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {out : BoundedConfig 6 3}
    (hw : run program 2 w H (initial n under right) = some (hf, out))
    (ho : boundedHalted out = true) :
    w = List.replicate 3 false ∧ hf = H ∧ out = final n under right :=
  terminal_word_eq (2 : Fin 3) program program_falseOnly 3 H H
    (initial n under right) (final n under right) (actual_run n under right H)
    (final_halted n under right) hw ho

theorem cutoff_counts (n : Nat) (under right : List (Fin 3)) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig program (initial n under right)) =
      if n ≠ 0 ∧ 3 ≤ T then 1 else 0 := by
  by_cases hn : n = 0
  · rw [rejecting_paths_zero (2 : Fin 3) rfl program program_falseOnly 3 H H
      (initial n under right) (final n under right) (actual_run n under right H)
      (by simp [final_state, hn]) T]
    simp [hn]
  · rw [acceptingPaths_threshold (2 : Fin 3) rfl program program_falseOnly 3 H
      (initial n under right) (final n under right) H (actual_run n under right H)
      (by simp [final_state, hn]) T]
    simp [hn]

theorem original_empty_test_spec (n : Nat) (under right : List (Fin 3)) (H : Int) :
    (run program 2 (List.replicate 3 false) H (initial n under right) = some (H, final n under right)) ∧
    (final n under right).state.val = (if n = 0 then 1 else 0) ∧
    (final n under right).leftRev = List.replicate n 1 ++ 2 :: under ∧
    (final n under right).focus = 2 ∧ (final n under right).right = right ∧
    (∀ w hf out, run program 2 w H (initial n under right) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ 3 ∧
        cellCount out = cellCount (initial n under right) ∧
        GrowthRun program 2 w H (initial n under right) hf out 0 0) ∧
    (∀ w hf out, run program 2 w H (initial n under right) = some (hf, out) →
      boundedHalted out = true → w = List.replicate 3 false ∧ hf = H ∧ out = final n under right) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig program (initial n under right)) =
      if n ≠ 0 ∧ 3 ≤ T then 1 else 0) :=
  ⟨actual_run n under right H, final_state n under right, rfl, rfl, rfl,
    fun _ _ _ => every_raw n under right H, fun _ _ _ => every_terminal n under right H,
    cutoff_counts n under right H⟩

end PakFixedPolyomino.ULogTernaryOriginalEmptyTest
