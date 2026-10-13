import PakFixedPolyomino.StandardBitReverseCleanup

/-! The exact swap-loop/cleanup composition. The swap-epoch theorem is an
explicit argument here and must be supplied by the separate epoch module. -/
namespace PakFixedPolyomino.StandardBitReverseIteration
open StandardNondeterministicMachine StandardBitTime StandardBitReverse
open StandardBitReverseCleanup Polynomial

def EpochRuns : Prop := ∀ (x : List Bool) (k : Nat), 2*k < x.length →
  run machine (ticks (epochFuel x.length k)) (epochConfig x k) =
    some (epochConfig x (k+1))

def loopFuel (n m : Nat) : Nat :=
  (List.range m).foldl (fun s k => s + epochFuel n k) 0

theorem loopFuel_succ (n m : Nat) :
    loopFuel n (m+1) = loopFuel n m + epochFuel n m := by
  simp [loopFuel,List.range_succ,List.foldl_append]

theorem loops_run (he : EpochRuns) (x : List Bool) (m : Nat)
    (hm : m ≤ (x.length+1)/2) :
    run machine (ticks (loopFuel x.length m)) (epochConfig x 0) =
      some (epochConfig x m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hk : 2*m < x.length := by omega
    rw [loopFuel_succ,ticks_add,run_append,ih (by omega),Option.bind_some]
    exact he x m hk

theorem reverse_run_of_epoch (he : EpochRuns) (x : List Bool) :
    run machine (ticks (reverseFuel x.length)) (initial machine x) = some (finalConfig x) := by
  have ht : reverseFuel x.length =
      setupFuel x.length + loopFuel x.length ((x.length+1)/2) + cleanupFuel x.length := rfl
  rw [ht,ticks_add,ticks_add,run_append,run_append,setup_run,Option.bind_some,
    loops_run he x ((x.length+1)/2) le_rfl,Option.bind_some]
  exact cleanup_run x ((x.length+1)/2) (by omega)

theorem reverse_computes_of_epoch (he : EpochRuns) :
    ComputesWithin machine List.reverse (fun n => 8*n*n+20*n+20) := by
  intro x
  refine ⟨reverseFuel x.length,finalConfig x,reverseFuel_le x.length,
    reverse_run_of_epoch he x,?_⟩
  exact ⟨rfl,rfl,rfl⟩

theorem reverse_runsAtMost_of_epoch (he : EpochRuns) (x : List Bool) :
    RunsAtMost machine x (reverseFuel x.length) :=
  halting_runsAtMost machine x (reverseFuel x.length) (finalConfig x)
    (reverse_run_of_epoch he x) rfl

noncomputable def boundPoly : Polynomial Nat := C 8 * X^2 + C 20 * X + C 20

theorem boundPoly_eval (n : Nat) : boundPoly.eval n = 8*n*n+20*n+20 := by
  simp [boundPoly,pow_two,Nat.mul_assoc]

theorem reverse_polyBitTime_of_epoch (he : EpochRuns) : PolyBitTime (List.reverse : List Bool → List Bool) := by
  refine ⟨14,8,machine,boundPoly,?_⟩
  simpa only [boundPoly_eval] using reverse_computes_of_epoch he

theorem reverse_exact_of_epoch (he : EpochRuns) :
    (∀ x,run machine (ticks (reverseFuel x.length)) (initial machine x) = some (finalConfig x)) ∧
    (∀ x,RunsAtMost machine x (reverseFuel x.length)) ∧
    PolyBitTime (List.reverse : List Bool → List Bool) :=
  ⟨reverse_run_of_epoch he,reverse_runsAtMost_of_epoch he,reverse_polyBitTime_of_epoch he⟩

end PakFixedPolyomino.StandardBitReverseIteration
