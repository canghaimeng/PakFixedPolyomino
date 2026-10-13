import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalFuel
import PakFixedPolyomino.ULogBootstrapAllMicroTimeCounts

/-! Exact physical cutoff counts at the genuine bootstrap hit of the OWN
compact whole-scanner input. Its first hit is constructed internally. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapTimeCounts
open ULogBootstrapExecution ULogProgram ULogConcreteMicroTimeCounts
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open StandardNondeterministicMachine (Machine)
variable {ns nt : Nat}

theorem bootstrap_cutoff_shift (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (capacity : 2 ≤ C) (T : Nat) :
    acceptingMicroPaths ((actual_bootstrap_prefix M p x C capacity).steps + T)
      (bootstrapStart M p x C) =
    acceptingMicroPaths T (frame M p x C (outerTail M p x)).encode :=
  ULogBootstrapAllMicroTimeCounts.cutoff_count_shift (actual_bootstrap_prefix M p x C capacity) rfl T

theorem bootstrap_cutoff_zero_before_hit (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) (capacity : 2 ≤ C) (T : Nat)
    (early : T < (actual_bootstrap_prefix M p x C capacity).steps) :
    acceptingMicroPaths T (bootstrapStart M p x C) = 0 :=
  ULogBootstrapAllMicroTimeCounts.cutoff_count_zero_before_hit
    (actual_bootstrap_prefix M p x C capacity) rfl T early

theorem bootstrap_all_raw_length_transfer (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) (capacity : 2 ≤ C) (B : Nat)
    (bounded : ∀ labels tape,
      ConcreteMicroPath (frame M p x C (outerTail M p x)).encode labels (.accepted tape) →
      labels.length ≤ B) (labels : List (Fin 2)) (tape : MStarParserExecution.Zipper Tape)
    (path : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) :
    labels.length ≤ bootstrapFuel M p x + B :=
  ULogBootstrapAllMicroTimeCounts.all_path_length_transfer (actual_bootstrap_prefix M p x C capacity)
    rfl (bootstrapFuel M p x) B (bootstrap_steps_le M p x C capacity) bounded labels tape path

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapTimeCounts
