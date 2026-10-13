import PakFixedPolyomino.ULogTernaryGeneratedMarginEntry
import PakFixedPolyomino.ULogTernaryMarginMarkedLayout

/-! Exact encoding alignment for repeated blank blocks around the actual
counter-corrected source. Execution is supplied by the separate real loop. -/
namespace PakFixedPolyomino.ULogTernaryBalancedMarginEncoding
open StandardNondeterministicMachine StandardMachineWindowBridge
open ULogSourceObliviousWindow
open ULogTernaryRetainedCounterPump (cell cells)
open ULogTernaryBalancedBlankPair (block)
open ULogTernaryMarginMarkedLayout (codes blankCell marked extra)
variable {ns nt : Nat}

def copies (blank : Fin nt) (m : Nat) : List Bool :=
  (List.replicate m (block blank)).flatten
def marginBits (M : Machine ns nt 2) (x : List Bool) (m : Nat) : List Bool :=
  copies M.blank m ++ ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x ++
    copies M.blank m

theorem copies_succ (blank : Fin nt) (m : Nat) :
    copies blank (m + 1) = block blank ++ copies blank m := by
  simp [copies, List.replicate_succ]

theorem copies_length (blank : Fin nt) (m : Nat) :
    (copies blank m).length = m * (nt + 1) := by
  induction m with
  | zero => simp [copies]
  | succ m ih =>
      rw [copies_succ, List.length_append, ULogTernaryBalancedBlankPair.block_length, ih]
      ring

theorem cells_block (M : Machine ns nt 2) :
    cells (block M.blank) = encodeMarkedCell (blankCell M) := by
  simp [cells, block, encodeMarkedCell, blankCell,
    ULogTernaryPreparedHeadedSourceExpansion.cell_tapeOfBit]

theorem cells_append (xs ys : List Bool) : cells (xs ++ ys) = cells xs ++ cells ys := by
  simp [cells]

theorem copies_encoding (M : Machine ns nt 2) (m : Nat) :
    cells (copies M.blank m) = encodeWindow (List.replicate m (blankCell M)) := by
  induction m with
  | zero => simp [copies, cells, encodeWindow]
  | succ m ih =>
      rw [copies_succ, cells_append, cells_block, ih]
      simp only [List.replicate_succ, encodeWindow, List.flatMap_cons]

theorem corrected_encoding (M : Machine ns nt 2) (x : List Bool) :
    cells (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x) =
      encodeWindow (ULogTernaryPreparedHeadedSourceExpansion.markedSource (codes M) x ++ extra M x) := by
  cases x with
  | nil =>
      simp [ULogTernaryGeneratedMarginEntry.correctedBits, extra,
        ULogTernaryGeneratedHeadedSourceReturn.source_encoding]
  | cons b rest =>
      simp only [ULogTernaryGeneratedMarginEntry.correctedBits, List.length_cons,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, extra]
      rw [cells_append, ULogTernaryGeneratedHeadedSourceReturn.source_encoding, cells_block]
      simp [encodeWindow, List.flatMap_append]

theorem encoded_marked (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    cells (marginBits M x (B + 1)) = encodeWindow (marked M x B) := by
  simp only [marginBits, cells, List.map_append]
  change cells (copies M.blank (B + 1)) ++
    cells (ULogTernaryGeneratedMarginEntry.correctedBits (codes M) M.blank x) ++
    cells (copies M.blank (B + 1)) = _
  rw [copies_encoding, corrected_encoding]
  simp [marked, encodeWindow, List.flatMap_append, List.append_assoc]

theorem exact_input_window (M : Machine ns nt 2) (x : List Bool) (m : Nat) (hm : 0 < m) :
    cells (marginBits M x m) = (inputWindow M x (m - 1)).encode := by
  have h : m - 1 + 1 = m := by omega
  have he := encoded_marked M x (m - 1)
  rw [h, ULogTernaryMarginMarkedLayout.marked_eq_window] at he
  exact he

theorem balanced_margin_encoding_spec (M : Machine ns nt 2) (x : List Bool)
    (m : Nat) (hm : 0 < m) :
    cells (marginBits M x m) = (inputWindow M x (m - 1)).encode ∧
      (marginBits M x m).length = (x.length + 2 * (m - 1) + 3) * (nt + 1) := by
  refine ⟨exact_input_window M x m hm, ?_⟩
  have he := congrArg List.length (exact_input_window M x m hm)
  simpa only [cells, List.length_map, LogicalWindow.encode, encodeWindow_length,
    LogicalWindow.markedCells_length, inputWindow_length] using he

end PakFixedPolyomino.ULogTernaryBalancedMarginEncoding
