import PakFixedPolyomino.ULogSourceObliviousInitialZipper
import PakFixedPolyomino.ULogFiniteProgramZipperCounts

/-! The scanner may keep arbitrary finite metadata to its left and unused
allocated cells to its right. The two real delimiters isolate its window.
ALL numerical and semantic accepting leaves retain the ordinary source
count. This describes a loader output, not an expanded metric input. -/
namespace PakFixedPolyomino.ULogSourceObliviousExteriorZipper
open StandardNondeterministicMachine ULogCompiler
open StandardMachineZipperBridge (physical config_ext)
open ULogSourceObliviousWindow ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution (initialWindowConfig)
open ULogSourceObliviousBytecode ULogSourceObliviousBytecodeRunBridge
open StandardMachineWindowBridge (inputWindow)
open ULogFiniteProgramZipperRunBridge ULogFiniteProgramZipperCounts

variable {ns nt : Nat}

theorem physical_front_index {ns : Nat} (q : Fin ns) (left cells suffix : List (Fin 3))
    (i : Nat) (hi : i < (2 :: (cells ++ [2])).length) :
    (physical (2 : Fin 3) 0 (BoundedConfig.mk q left 2 (cells ++ 2 :: suffix))).tape
      (i : Int) = (2 :: (cells ++ [2]))[i] := by
  cases i with
  | zero => simp [physical]
  | succ k =>
      have bound : k ≤ cells.length := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hi
        omega
      have evaluated :
          (physical (2 : Fin 3) 0 (BoundedConfig.mk q left 2 (cells ++ 2 :: suffix))).tape
            ((k + 1 : Nat) : Int) = (cells ++ 2 :: suffix).getD k 2 := by
        have positive : (0 : Int) < (k : Int) + 1 := by omega
        simp [physical, Nat.cast_add, positive.ne', not_lt.mpr positive.le]
      rw [evaluated]
      have index : k < (cells ++ [2]).length := by simp; omega
      change (cells ++ 2 :: suffix).getD k 2 = (cells ++ [2])[k]'index
      rw [← List.getD_eq_getElem (cells ++ [2]) (2 : Fin 3) index]
      by_cases inside : k < cells.length
      · rw [List.getD_append cells (2 :: suffix) 2 k inside,
          List.getD_append cells [2] 2 k inside]
      · rw [List.getD_append_right cells (2 :: suffix) 2 k (by omega),
          List.getD_append_right cells [2] 2 k (by omega)]
        simp [show k - cells.length = 0 by omega]

noncomputable def zipper (M : Machine ns nt 2) (w : LogicalWindow nt)
    (left suffix : List (Fin 3)) : BoundedConfig (2 + Fintype.card (Active M)) 3 :=
  ⟨stateEquiv M (.atLeft M.start), left, 2, w.encode ++ 2 :: suffix⟩

noncomputable def exterior (M : Machine ns nt 2) (w : LogicalWindow nt)
    (left suffix : List (Fin 3)) : Int → Fin 3 :=
  (physical (2 : Fin 3) 0 (zipper M w left suffix)).tape

theorem windowTape_eq_actual (M : Machine ns nt 2) (w : LogicalWindow nt)
    (left suffix : List (Fin 3)) :
    windowTape w (exterior M w left suffix) = exterior M w left suffix := by
  funext p
  unfold windowTape
  by_cases hp : 0 ≤ p
  · by_cases hi : p.toNat < (delimitedCells w).length
    · have cast : p = (p.toNat : Int) := (Int.toNat_of_nonneg hp).symm
      rw [cast, overlayTape_ofNat (delimitedCells w) _ p.toNat hi]
      exact (physical_front_index (stateEquiv M (.atLeft M.start)) left w.encode suffix
        p.toNat hi).symm
    · exact overlayTape_ge (delimitedCells w) _ p hp (by omega)
  · exact overlayTape_neg (delimitedCells w) _ p (by omega)

theorem zipper_physical (M : Machine ns nt 2) (w : LogicalWindow nt)
    (left suffix : List (Fin 3)) :
    physical (2 : Fin 3) 0 (zipper M w left suffix) =
      encodeConfig M (initialWindowConfig M.start w (exterior M w left suffix)) := by
  apply config_ext
  · rfl
  · rfl
  · exact (windowTape_eq_actual M w left suffix).symm

theorem ordinary_leaf_count (M : Machine ns nt 2) (x : List Bool) (bound : Nat)
    (htime : RunsAtMost M x bound) (left suffix : List (Fin 3)) :
    acceptingCount M x bound = Nat.card (RawFiniteLeaves (boundedProgram M) 0
      (zipper M (inputWindow M x bound) left suffix)) := by
  change acceptingCount M x bound = Nat.card {word : List (FiniteOneTapeProgram.Arrow
    (numericalProgram M)) // ∃ out, FiniteOneTapeSemantics.run (numericalProgram M)
      (fun _ => true) word (physical (2 : Fin 3) 0
        (zipper M (inputWindow M x bound) left suffix)) = some out ∧ out.state.val = 0}
  rw [zipper_physical]
  exact ordinary_leaf_count_numerical M x bound htime
    (exterior M (inputWindow M x bound) left suffix)

theorem ordinary_semantic_count (M : Machine ns nt 2) (x : List Bool) (bound : Nat)
    (htime : RunsAtMost M x bound) (left suffix : List (Fin 3)) :
    acceptingCount M x bound = Nat.card (SemanticLeaves (boundedProgram M)
      (zipper M (inputWindow M x bound) left suffix)) := by
  rw [← scanner_leaves_count M 0]
  exact ordinary_leaf_count M x bound htime left suffix

theorem exterior_zipper_count_spec (M : Machine ns nt 2) (x : List Bool) (bound : Nat)
    (htime : RunsAtMost M x bound) (left suffix : List (Fin 3)) :
    (physical (2 : Fin 3) 0 (zipper M (inputWindow M x bound) left suffix) =
      encodeConfig M (initialWindowConfig M.start (inputWindow M x bound)
        (exterior M (inputWindow M x bound) left suffix))) ∧
    acceptingCount M x bound = Nat.card (RawFiniteLeaves (boundedProgram M) 0
      (zipper M (inputWindow M x bound) left suffix)) ∧
    acceptingCount M x bound = Nat.card (SemanticLeaves (boundedProgram M)
      (zipper M (inputWindow M x bound) left suffix)) :=
  ⟨zipper_physical M (inputWindow M x bound) left suffix,
    ordinary_leaf_count M x bound htime left suffix,
    ordinary_semantic_count M x bound htime left suffix⟩

end PakFixedPolyomino.ULogSourceObliviousExteriorZipper
