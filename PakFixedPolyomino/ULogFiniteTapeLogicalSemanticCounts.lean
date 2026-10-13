import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroCounts
import PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts

/-! The same literal Boolean word represents a bounded logical leaf and
a compiled semantic leaf. No terminal-table or chosen-image restriction
is needed for this equivalence. -/
namespace PakFixedPolyomino.ULogFiniteTapeLogicalSemanticCounts
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteTapeNondeterministicMicroCounts (LogicalAcceptingWords)
open ULogFiniteProgramZipperRunBridge (SemanticLeaves)
open ULogFiniteTapeGuardedStageLeafCounts (semantic_of_run run_of_semantic lift_state0)
variable {ns : Nat}

theorem logical_semantic_card_eq (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) :
    Nat.card (LogicalAcceptingWords p head z) = Nat.card (SemanticLeaves p z) := by
  let e : LogicalAcceptingWords p head z ≃ SemanticLeaves p z :=
    { toFun := fun leaf => ⟨leaf.val, by
        obtain ⟨hf, out, path, accepts⟩ := leaf.property
        exact ⟨liftConfig p out, semantic_of_run p leaf.val head hf z out path,
          (lift_state0 p out).2 accepts⟩⟩
      invFun := fun leaf => ⟨leaf.val, by
        obtain ⟨out, path, accepts⟩ := leaf.property
        obtain ⟨hf, out', word, same⟩ := run_of_semantic p leaf.val head z out path
        exact ⟨hf, out', word, (lift_state0 p out').1 (by rw [same]; exact accepts)⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact Nat.card_congr e

end PakFixedPolyomino.ULogFiniteTapeLogicalSemanticCounts
