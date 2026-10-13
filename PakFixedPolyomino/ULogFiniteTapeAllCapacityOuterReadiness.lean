import PakFixedPolyomino.ULogFiniteTapeNondeterministicResourceBridge
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPrefixGrowth
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCompiledNonempty

/-! ALL-prefix growth supplies the actual left exterior at every logical
resource node, for every capacity. Only the outer-readiness field is taken
from a sufficiently large auxiliary logical ledger; no capacity readiness
or physical execution at the actual smaller capacity is inferred. -/
namespace PakFixedPolyomino.ULogFiniteTapeAllCapacityOuterReadiness
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeBoundedGrowthReadiness
open ULogFiniteTapeNondeterministicResourceBridge ULogBootstrapExecution ULogProgram
open StandardNondeterministicMachine (Machine RunsAtMost)
variable {ns nt : Nat}

def AllReachableOuterReady (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (C : Nat) (outer : List Tape) : Prop :=
  ∀ w hf out Cf outerf, resourceRun p 2 w head z C outer = some (hf, out, Cf, outerf) →
    boundedHalted out = false →
    ∀ slot action, ULogBytecode.lookupRule (compile p) out.state.val out.focus.val slot =
      some action → SemanticOuterReady (liftConfig p out) action outerf

theorem all_outer_ready_of_growth (p : BoundedProgram ns 3) (hp : compile p ≠ [])
    (head : Int) (z : BoundedConfig ns 3) (L R C : Nat) (tail : List Tape)
    (bounds : AllGrowthBounded p head z L R) :
    AllReachableOuterReady p head z C (List.replicate L MStarConcreteAlphabet.work ++ tail) := by
  intro w hf out Cf outerf path halt slot action lookup
  have word := resource_run_forget p w head hf z out C Cf _ outerf path
  obtain ⟨lg, rg, growth⟩ := every_actual_run p 2 w head hf z out word
  have computed := actual_resource_run growth C (List.replicate L MStarConcreteAlphabet.work ++ tail)
  have same := Option.some.inj (path.symm.trans computed)
  have outer := congrArg (fun v : Int × BoundedConfig ns 3 × Nat × List Tape => v.2.2.2) same
  dsimp only at outer
  rw [outer]
  have auxiliary := reachable_nonClock_ready p hp head z L R bounds w hf out lg rg growth halt
    (R + (ns - 1)) tail (Nat.le_refl _)
  exact auxiliary.outer_ready slot action lookup

theorem whole_all_capacity_outer_ready (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape) :
    AllReachableOuterReady (ULogTernaryGeneratedMarginScanner.program M p) 0
      (ULogTernaryGeneratedMarginScanner.initial M p x) C
      (MStarConcreteAlphabet.work :: tail) := by
  simpa only [List.replicate_one, List.cons_append, List.nil_append] using
    all_outer_ready_of_growth (ULogTernaryGeneratedMarginScanner.program M p)
      (ULogTernaryGeneratedMarginScannerCompiledNonempty.compiled_program_nonempty M p) 0
      (ULogTernaryGeneratedMarginScanner.initial M p x) 1
      (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) C tail
      (ULogTernaryGeneratedMarginScannerAllPrefixGrowth.whole_all_prefix_growth M p x ht)

end PakFixedPolyomino.ULogFiniteTapeAllCapacityOuterReadiness
