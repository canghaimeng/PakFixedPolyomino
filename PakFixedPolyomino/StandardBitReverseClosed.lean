import PakFixedPolyomino.StandardBitReverseEpoch
import PakFixedPolyomino.StandardBitReverseIteration

/-! Initialized reversal, with the actual swap epoch supplied internally. -/
namespace PakFixedPolyomino.StandardBitReverseClosed
open StandardNondeterministicMachine StandardBitTime StandardBitReverse

theorem epoch_runs : StandardBitReverseIteration.EpochRuns :=
  StandardBitReverseEpoch.epoch_exact

theorem reverse_run (x : List Bool) :
    run machine (ticks (reverseFuel x.length)) (initial machine x) =
      some (finalConfig x) :=
  StandardBitReverseIteration.reverse_run_of_epoch epoch_runs x

theorem reverse_computes :
    ComputesWithin machine List.reverse (fun n => 8*n*n+20*n+20) :=
  StandardBitReverseIteration.reverse_computes_of_epoch epoch_runs

theorem reverse_runsAtMost (x : List Bool) :
    RunsAtMost machine x (reverseFuel x.length) :=
  StandardBitReverseIteration.reverse_runsAtMost_of_epoch epoch_runs x

theorem reverse_output (x : List Bool) : Output machine x.reverse (finalConfig x) :=
  ⟨rfl,rfl,rfl⟩

theorem reverse_polyBitTime : PolyBitTime (List.reverse : List Bool → List Bool) :=
  StandardBitReverseIteration.reverse_polyBitTime_of_epoch epoch_runs

theorem reverse_exact :
    (∀ x,run machine (ticks (reverseFuel x.length)) (initial machine x) =
      some (finalConfig x)) ∧
    (∀ x,Output machine x.reverse (finalConfig x)) ∧
    (∀ x,RunsAtMost machine x (reverseFuel x.length)) ∧
    ComputesWithin machine List.reverse (fun n => 8*n*n+20*n+20) ∧
    PolyBitTime (List.reverse : List Bool → List Bool) :=
  ⟨reverse_run,reverse_output,reverse_runsAtMost,reverse_computes,reverse_polyBitTime⟩

end PakFixedPolyomino.StandardBitReverseClosed
