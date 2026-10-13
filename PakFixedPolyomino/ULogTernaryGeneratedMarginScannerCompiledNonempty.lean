import PakFixedPolyomino.ULogTernaryGeneratedMarginScanner
import PakFixedPolyomino.ULogFiniteTapeCompilerNonempty

/-! The actual loader/guard/fresh-entry word proves the whole compiled
program is nonempty, even when the ordinary source has no accepting path. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCompiledNonempty
open ULogCompiler ULogTernaryGeneratedMarginScanner
open StandardNondeterministicMachine (Machine)
variable {ns nt : Nat}

theorem compiled_program_nonempty (M : Machine ns nt 2) (p : Polynomial Nat) :
    compile (program M p) ≠ [] := by
  apply ULogFiniteTapeCompilerNonempty.compiled_nonempty_of_run (program M p) (2 : Fin 3)
    (List.replicate (bootDeadline M p []) false) 0
    (ULogTernaryGeneratedMarginLoop.head nt p []) (initial M p []) (bootFinal M p [])
  · simp [bootDeadline]
  · exact load_and_boot M p []

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCompiledNonempty
