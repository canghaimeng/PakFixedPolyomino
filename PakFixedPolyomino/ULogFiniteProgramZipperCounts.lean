import PakFixedPolyomino.ULogFiniteProgramZipperRunBridge

/-! Propositional count endpoints for the internally constructed ALL-leaf
equivalence. `Nat.card` also applies before finiteness is established; a
separate source time bound supplies finiteness and acceptingPaths cutoffs. -/

namespace PakFixedPolyomino.ULogFiniteProgramZipperCounts

open ULogCompiler ULogSourceObliviousBytecode StandardNondeterministicMachine
open ULogFiniteProgramZipperRunBridge

theorem finite_leaves_count {ns : Nat} (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3) :
    Nat.card (RawFiniteLeaves p head z) = Nat.card (SemanticLeaves p z) :=
  Nat.card_congr (finiteLeavesEquiv p hterminal head z)

theorem scanner_leaves_count {ns nt : Nat} (M : Machine ns nt 2)
    (head : Int) (z : BoundedConfig (2 + Fintype.card (Active M)) 3) :
    Nat.card (RawFiniteLeaves (boundedProgram M) head z) =
      Nat.card (SemanticLeaves (boundedProgram M) z) :=
  Nat.card_congr (scannerLeavesEquiv M head z)

end PakFixedPolyomino.ULogFiniteProgramZipperCounts
