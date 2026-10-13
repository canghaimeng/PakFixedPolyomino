import PakFixedPolyomino.StandardMachineWindowInitialLayout
import PakFixedPolyomino.ULogTernaryPreparedHeadedSourceExpansion

/-! Literal marked-list alignment after balanced margins and the internal
nonempty-only extra right blank. This is a layout identity, not a supplied
execution certificate or an exponentially materialized metric input. -/
namespace PakFixedPolyomino.ULogTernaryMarginMarkedLayout
open StandardNondeterministicMachine StandardMachineWindowBridge
open StandardMachineWindowInitialLayout
open ULogSourceObliviousWindow
open ULogTernaryRetainedCounterPump (cell)

variable {ns nt : Nat}
def codes (M : Machine ns nt 2) (a : Fin 3) : Fin nt :=
  if a.val = 0 then M.zero else if a.val = 1 then M.one else M.blank
theorem codes_bit (M : Machine ns nt 2) (b : Bool) :
    codes M (cell b) = if b then M.one else M.zero := by cases b <;> rfl
theorem codes_blank (M : Machine ns nt 2) : codes M 2 = M.blank := rfl

def blankCell (M : Machine ns nt 2) : MarkedCell nt := ⟨M.blank, false⟩
def extra (M : Machine ns nt 2) : List Bool → List (MarkedCell nt)
  | [] => []
  | _ :: _ => [blankCell M]
def marked (M : Machine ns nt 2) (x : List Bool) (B : Nat) : List (MarkedCell nt) :=
  List.replicate (B + 1) (blankCell M) ++
    ULogTernaryPreparedHeadedSourceExpansion.markedSource (codes M) x ++
    extra M x ++ List.replicate (B + 1) (blankCell M)

theorem symbols (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (marked M x B).map MarkedCell.symbol = paddedCells M x B := by
  cases x with
  | nil => simp [marked, extra, blankCell, paddedCells, sourceSymbols,
      ULogTernaryPreparedHeadedSourceExpansion.markedSource,
      ULogTernaryPreparedHeadedSourceExpansion.first,
      ULogTernaryPreparedHeadedSourceExpansion.tail, codes_blank, List.replicate_succ]
  | cons b xs => simp [marked, extra, blankCell, paddedCells, sourceSymbols,
      ULogTernaryPreparedHeadedSourceExpansion.markedSource,
      ULogTernaryPreparedHeadedSourceExpansion.first,
      ULogTernaryPreparedHeadedSourceExpansion.tail, codes_bit, List.map_map,
      Function.comp_def, List.replicate_succ, List.append_assoc]

theorem flags (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (marked M x B).map MarkedCell.head =
      List.replicate (B + 1) false ++ true :: List.replicate (x.length + B + 1) false := by
  cases x with
  | nil => simp [marked, extra, blankCell,
      ULogTernaryPreparedHeadedSourceExpansion.markedSource_unique,
      ULogTernaryPreparedHeadedSourceExpansion.tail, List.append_assoc]
  | cons b xs =>
      simp [marked, extra, blankCell,
        ULogTernaryPreparedHeadedSourceExpansion.markedSource_unique,
        ULogTernaryPreparedHeadedSourceExpansion.tail, List.append_assoc,
        List.replicate_add, Nat.add_assoc, -List.replicate_append_replicate]

theorem marked_length (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (marked M x B).length = x.length + 2 * B + 3 := by
  have h := congrArg List.length (symbols M x B)
  simpa only [List.length_map, padded_length] using h

theorem flag_get (pre post i : Nat) (hi : i < pre + 1 + post) :
    (List.replicate pre false ++ true :: List.replicate post false)[i]'(by simp; omega) =
      decide (i = pre) := by
  by_cases hl : i < pre
  · have hn : i ≠ pre := by omega
    simp [List.getElem_append, hl, hn]
  · by_cases he : i = pre
    · subst i; simp [List.getElem_append]
    · have hn : i - pre ≠ 0 := by omega
      simp [List.getElem_append, hl, he, List.getElem_cons, hn]

theorem fields_injective {xs ys : List (MarkedCell nt)}
    (hs : xs.map MarkedCell.symbol = ys.map MarkedCell.symbol)
    (hh : xs.map MarkedCell.head = ys.map MarkedCell.head) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
      cases ys with
      | nil => simp at hs
      | cons b ys =>
          obtain ⟨hab, hst⟩ := List.cons.inj hs
          obtain ⟨hah, hht⟩ := List.cons.inj hh
          have he : a = b := by cases a; cases b; simp_all
          rw [he, ih hst hht]

theorem window_symbols (w : LogicalWindow nt) : w.markedCells.map MarkedCell.symbol = w.cells := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [LogicalWindow.markedCells]

theorem window_flags (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (inputWindow M x B).markedCells.map MarkedCell.head =
      List.replicate (B + 1) false ++ true :: List.replicate (x.length + B + 1) false := by
  apply List.ext_getElem
  · simp [inputWindow_length]; omega
  · intro i hi hj
    have bound : i < (B + 1) + 1 + (x.length + B + 1) := by
      simp only [List.length_append, List.length_replicate, List.length_cons] at hj
      omega
    rw [flag_get (B + 1) (x.length + B + 1) i bound]
    simp [LogicalWindow.markedCells, Fin.ext_iff, initial_head_index]

theorem marked_eq_window (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    marked M x B = (inputWindow M x B).markedCells := by
  apply fields_injective
  · rw [symbols, window_symbols, initial_cells]
  · rw [flags, window_flags]

theorem margin_marked_layout_spec (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    marked M x B = (inputWindow M x B).markedCells ∧
    encodeWindow (marked M x B) = (inputWindow M x B).encode ∧
    (marked M x B).length = x.length + 2 * B + 3 ∧
    (marked M x B).map MarkedCell.head =
      List.replicate (B + 1) false ++ true :: List.replicate (x.length + B + 1) false :=
  ⟨marked_eq_window M x B, congrArg encodeWindow (marked_eq_window M x B),
    marked_length M x B, flags M x B⟩

end PakFixedPolyomino.ULogTernaryMarginMarkedLayout
