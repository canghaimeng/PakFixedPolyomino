import PakFixedPolyomino.StandardMachineWindowBridge

/-! Literal blank padding of the ordinary input window, including empty input.
This is a target-layout equality. Actual compact loading remains a separate
execution proof and this materialized list is never the metric input. -/

namespace PakFixedPolyomino.StandardMachineWindowInitialLayout

open StandardNondeterministicMachine StandardMachineWindowBridge

variable {ns nt : Nat}

def sourceSymbols (M : Machine ns nt 2) (x : List Bool) : List (Fin nt) :=
  x.map (fun b => if b then M.one else M.zero)

def paddedCells (M : Machine ns nt 2) (x : List Bool) (B : Nat) : List (Fin nt) :=
  List.replicate (B + 1) M.blank ++ sourceSymbols M x ++ List.replicate (B + 2) M.blank

theorem padded_length (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (paddedCells M x B).length = x.length + 2 * B + 3 := by
  simp [paddedCells, sourceSymbols]; omega

theorem initial_head_index (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (inputWindow M x B).head.val = B + 1 := by
  simp [inputWindow, window, initial, inputOrigin]
  omega

theorem initial_cells (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (inputWindow M x B).cells = paddedCells M x B := by
  apply List.ext_getElem
  · rw [inputWindow_length, padded_length]
  · intro i hi hj
    simp only [inputWindow, window, List.getElem_ofFn]
    change (initial M x).tape (inputOrigin B + (i : Int)) = (paddedCells M x B)[i]
    change inputTape M x (inputOrigin B + (i : Int)) = _
    by_cases hleft : i < B + 1
    · rw [inputTape_neg M x _ (by unfold inputOrigin; omega)]
      simp [paddedCells, List.getElem_append, hleft]
    · by_cases hmid : i < B + 1 + x.length
      · have hpos : inputOrigin B + (i : Int) = ((i - (B + 1) : Nat) : Int) := by
          unfold inputOrigin; omega
        rw [hpos, inputTape_ofNat M x _ (by omega)]
        simp [paddedCells, sourceSymbols, List.getElem_append, hleft,
          (by omega : i - (B + 1) < x.length)]
      · rw [inputTape_ge M x _ (by unfold inputOrigin; omega)]
        simp [paddedCells, sourceSymbols, List.getElem_append, hleft,
          (by omega : ¬i - (B + 1) < x.length)]
        intro h
        have hn : ¬i - (B + 1) < x.length := by omega
        exact (hn h).elim

theorem initial_head_symbol (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (inputWindow M x B).cells.get (inputWindow M x B).head =
      match x with
      | [] => M.blank
      | b :: _ => if b then M.one else M.zero := by
  have h := window_read (inputOrigin B) (inputSize x B) (initial M x) (initial_headIn M x B)
  change (inputWindow M x B).cells.get (inputWindow M x B).head = _ at h
  rw [h]
  cases x <;> simp [initial, inputTape]

theorem initial_marked_head (M : Machine ns nt 2) (x : List Bool) (B : Nat)
    (i : Fin (inputWindow M x B).cells.length) :
    ((inputWindow M x B).markedCells.get ⟨i.val, by simp⟩).head = decide (i.val = B + 1) := by
  rw [ULogSourceObliviousWindow.LogicalWindow.markedCells_get_head, initial_head_index]

theorem initial_layout_spec (M : Machine ns nt 2) (x : List Bool) (B : Nat) :
    (inputWindow M x B).cells =
      List.replicate (B + 1) M.blank ++ sourceSymbols M x ++ List.replicate (B + 2) M.blank ∧
    (inputWindow M x B).head.val = B + 1 ∧
    (inputWindow M x B).cells.length = x.length + 2 * B + 3 :=
  ⟨initial_cells M x B, initial_head_index M x B, inputWindow_length M x B⟩

end PakFixedPolyomino.StandardMachineWindowInitialLayout
