import PakFixedPolyomino.ULogSourceObliviousBytecodeRunBridge
import PakFixedPolyomino.StandardMachineZipperBridge

/-! The actual materialized scanner window has a finite list-zipper
representation when its exterior is blank2. This states its complete tape
denotation and actual size. It does not compute that exponential window from
compact input or identify its recoded start with universal startCode2. -/

namespace PakFixedPolyomino.ULogSourceObliviousInitialZipper

open StandardNondeterministicMachine ULogCompiler
open StandardMachineZipperBridge (physical config_ext)
open ULogSourceObliviousWindow ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousBytecode ULogSourceObliviousBytecodeRunBridge
open StandardMachineWindowBridge (inputWindow inputWindow_length)

theorem overlay_blank_getD (cells : List (Fin 3)) (blank : Fin 3) (p : Int) :
    overlayTape cells (fun _ => blank) p =
      if 0 ≤ p then cells.getD p.toNat blank else blank := by
  unfold overlayTape
  by_cases hp : 0 ≤ p
  · rw [dif_pos hp, if_pos hp]
    by_cases hi : p.toNat < cells.length
    · rw [dif_pos hi, List.getD_eq_getElem cells blank hi]
    · rw [dif_neg hi]
      symm
      apply List.getD_eq_default
      omega
  · rw [dif_neg hp, if_neg hp]

theorem physical_cons_overlay {ns : Nat} (q : Fin ns)
    (focus blank : Fin 3) (right : List (Fin 3)) :
    physical blank 0 (BoundedConfig.mk q [] focus right) =
      { state := q, head := 0,
        tape := overlayTape (focus :: right) (fun _ => blank) } := by
  apply config_ext
  · rfl
  · rfl
  · funext p
    change (physical blank 0 (BoundedConfig.mk q [] focus right)).tape p =
      overlayTape (focus :: right) (fun _ => blank) p
    rw [overlay_blank_getD]
    by_cases hp : p = 0
    · subst p
      simp [physical]
    · by_cases hn : p < 0
      · have hnn : ¬0 ≤ p := by omega
        simp [physical, hp, hn, hnn]
      · have hpos : 0 < p := by omega
        have hnn : 0 ≤ p := by omega
        have hnat : 0 < p.toNat := by omega
        obtain ⟨k, hk⟩ : ∃ k, p.toNat = k + 1 := ⟨p.toNat - 1, by omega⟩
        simp [physical, hp, hn, hnn, hk]

noncomputable def initialZipper {ns nt : Nat} (M : Machine ns nt 2)
    (w : LogicalWindow nt) : BoundedConfig (2 + Fintype.card (Active M)) 3 :=
  ⟨stateEquiv M (.atLeft M.start), [], physBlank,
    w.encode ++ [physBlank]⟩

theorem initialZipper_physical {ns nt : Nat} (M : Machine ns nt 2)
    (w : LogicalWindow nt) :
    physical (2 : Fin 3) 0 (initialZipper M w) =
      encodeConfig M (initialWindowConfig M.start w (fun _ => physBlank)) := by
  exact physical_cons_overlay (stateEquiv M (.atLeft M.start)) physBlank
    (2 : Fin 3) (w.encode ++ [physBlank])

theorem initialZipper_cells {ns nt : Nat} (M : Machine ns nt 2)
    (w : LogicalWindow nt) :
    (initialZipper M w).leftRev.length + 1 +
      (initialZipper M w).right.length = windowWidth w + 2 := by
  simp [initialZipper, windowWidth]
  omega

theorem initialZipper_input_cells {ns nt : Nat} (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) :
    (initialZipper M (inputWindow M x bound)).leftRev.length + 1 +
      (initialZipper M (inputWindow M x bound)).right.length =
        (x.length + 2 * bound + 3) * (nt + 1) + 2 := by
  rw [initialZipper_cells, windowWidth_eq, inputWindow_length]

/-- Ordinary ALL accepting leaves are counted on the actual finite zipper
denotation, with no arrow-image or stopping-length restriction. -/
theorem ordinary_leaf_count_initialZipper {ns nt : Nat} (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound) :
    acceptingCount M x bound =
      Nat.card {word : List (FiniteOneTapeProgram.Arrow (numericalProgram M)) //
        ∃ out, FiniteOneTapeSemantics.run (numericalProgram M) (fun _ => true)
          word (physical (2 : Fin 3) 0
            (initialZipper M (inputWindow M x bound))) = some out ∧
          out.state.val = 0} := by
  rw [initialZipper_physical]
  exact ordinary_leaf_count_numerical M x bound htime (fun _ => physBlank)

end PakFixedPolyomino.ULogSourceObliviousInitialZipper
