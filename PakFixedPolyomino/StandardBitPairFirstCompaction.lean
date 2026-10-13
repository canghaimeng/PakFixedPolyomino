import PakFixedPolyomino.StandardBitPairFirst
import PakFixedPolyomino.StandardBitMarkedCompactionSpec

/-! Concrete parser, marked compaction and cleanup on every ordinary raw input.
The explicit finite-rule premises of the generic stages are discharged here. -/
namespace PakFixedPolyomino.StandardBitPairFirstCompaction
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitMarkedCompaction (CycleRules)
open StandardBitMarkedCleanup (CleanupRules)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

abbrev machine := StandardBitPairFirst.machine

def firstBits (w : List Bool) : List Bool :=
  match unpairBits w with
  | some (x,_) => x
  | none => []

theorem firstBits_pair (x y : List Bool) : firstBits (pairBits x y) = x := by
  simp [firstBits,unpair_pairBits]

theorem cycle_rules : CycleRules machine := by
  unfold CycleRules
  constructor
  · intro a
    simp [machine,StandardBitPairFirst.machine]
  · constructor
    · intro b a
      cases b <;> simp [StandardBitMarkedCompaction.carry,StandardBitPairCompactionTape.enc,
        machine,StandardBitPairFirst.machine]
    · intro a
      simp [machine,StandardBitPairFirst.machine]

theorem cleanup_rules : CleanupRules machine := by
  unfold CleanupRules
  constructor <;> intro a <;> simp [machine,StandardBitPairFirst.machine]

theorem copy_tape_eq (x y : List Bool) (k : Nat) :
    StandardBitPairFirst.copyTape x y k = StandardBitPairCompactionTape.tape x y k := by
  funext z
  by_cases hz : 0 ≤ z
  · lift z to Nat using hz with i
    have hEnd : (i : Int) = 2*(x.length : Int)+1+(y.length : Int) ↔
        i = 2*x.length+1+y.length := by omega
    simp [StandardBitPairFirst.copyTape,StandardBitPairCompactionTape.tape,
      StandardBitPairCompactionTape.natTape,StandardBitPairFirst.enc,
      StandardBitPairCompactionTape.enc,StandardBitPairFirst.mark,StandardBitPairCompactionTape.mark,hEnd]
  · simp [StandardBitPairFirst.copyTape,StandardBitPairCompactionTape.tape,hz]

theorem copy_config_eq (x y : List Bool) (k : Nat) :
    StandardBitPairFirst.copyConfig x y k = StandardBitMarkedCompaction.copyConfig x y k := by
  unfold StandardBitPairFirst.copyConfig StandardBitMarkedCompaction.copyConfig
  rw [copy_tape_eq]

theorem final_config_eq (x : List Bool) :
    StandardBitMarkedCleanup.finalConfig x = StandardBitPairFirst.finalConfig machine x := rfl

def pairTime (x y : List Bool) : Nat :=
  x.length*x.length+2*x.length+4*(pairBits x y).length+7

theorem pair_run (x y : List Bool) :
    run machine (ticks (pairTime x y)) (initial machine (pairBits x y)) =
      some (StandardBitPairFirst.finalConfig machine x) := by
  have ht : pairTime x y = (2*(pairBits x y).length+5)+
      StandardBitMarkedCompactionSpec.stageTime x y := by
    unfold pairTime StandardBitMarkedCompactionSpec.stageTime
    omega
  rw [ht,ticks_add,run_append,StandardBitPairFirst.setup_run,Option.bind_some,
    copy_config_eq,StandardBitMarkedCompactionSpec.stage_run machine cycle_rules cleanup_rules,
    final_config_eq]

theorem pairTime_le (x y : List Bool) :
    pairTime x y ≤ 64*((pairBits x y).length+1)*((pairBits x y).length+1) := by
  have hn := StandardBitPairCompactionTape.pair_length_gt x y
  unfold pairTime
  nlinarith

theorem first_computes : ComputesWithin machine firstBits (fun n => 64*(n+1)*(n+1)) := by
  intro w
  cases hw : unpairBits w with
  | none =>
    have ho : firstBits w = [] := by simp [firstBits,hw]
    refine ⟨2*w.length+4,StandardBitPairFirst.finalConfig machine [],by nlinarith,
      StandardBitPairFirst.mal_run w hw,?_⟩
    rw [ho]
    exact ⟨rfl,rfl,rfl⟩
  | some xy =>
    rcases xy with ⟨x,y⟩
    have he := StandardBitPairProjection.unpairBits_eq_some.mp hw
    subst w
    refine ⟨pairTime x y,StandardBitPairFirst.finalConfig machine x,pairTime_le x y,
      pair_run x y,?_⟩
    rw [firstBits_pair]
    exact ⟨rfl,rfl,rfl⟩

theorem first_polyBitTime : PolyBitTime firstBits := by
  refine ⟨17,8,machine,Polynomial.C 64 * (Polynomial.X+1) * (Polynomial.X+1),?_⟩
  simpa using first_computes

theorem first_projection_spec (w : List Bool) :
    (∀ x y, unpairBits w = some (x,y) → firstBits w = x) ∧
    (unpairBits w = none → firstBits w = []) ∧
    (∃ n out, n ≤ 64*(w.length+1)*(w.length+1) ∧
      run machine (ticks n) (initial machine w) = some out ∧ Output machine (firstBits w) out) ∧
    RunsAtMost machine w (64*(w.length+1)*(w.length+1)) ∧ PolyBitTime firstBits := by
  refine ⟨?_,?_,first_computes w,(ComputesWithin.actual_bounds machine firstBits _ first_computes w).1,
    first_polyBitTime⟩
  · intro x y hw
    simp [firstBits,hw]
  · intro hw
    simp [firstBits,hw]

end PakFixedPolyomino.StandardBitPairFirstCompaction
