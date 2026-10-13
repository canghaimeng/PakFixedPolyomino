import PakFixedPolyomino.StandardBitMarkedCleanup

namespace PakFixedPolyomino.StandardBitMarkedCompactionSpec
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitMarkedCompaction StandardBitMarkedCleanup

def stageTime (x y : List Bool) : Nat :=
  x.length*x.length+2*x.length+2*(pairBits x y).length+2

theorem stage_run (M : DeterministicMachine 17 8) (hc : CycleRules M)
    (hr : CleanupRules M) (x y : List Bool) :
    run M (ticks (stageTime x y)) (copyConfig x y 0) = some (finalConfig x) := by
  have hn := StandardBitPairCompactionTape.pair_length_gt x y
  have ht : stageTime x y = (x.length*x.length+3*x.length)+
      (2*(pairBits x y).length-x.length+2) := by
    unfold stageTime
    omega
  rw [ht,ticks_add,run_append,copy_prefix M hc x y x.length le_rfl,
    Option.bind_some,cleanup_run M hc hr x y]

theorem stageTime_le (x y : List Bool) :
    stageTime x y ≤ 64*((pairBits x y).length+1)*((pairBits x y).length+1) := by
  have hn := StandardBitPairCompactionTape.pair_length_gt x y
  unfold stageTime
  nlinarith

end PakFixedPolyomino.StandardBitMarkedCompactionSpec
