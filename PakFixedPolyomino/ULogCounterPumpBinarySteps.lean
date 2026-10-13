import PakFixedPolyomino.ULogCounterPumpCounterSteps
import PakFixedPolyomino.ULogCounterPumpPotential

/-! The pump's actual carry/return stages on binary counter patterns.
The generated zero suffix and delimiter are part of the literal tape and
are preserved by these transitions. These are carry3 stages; the separate
append5 sweep is not assumed or claimed here. -/

namespace PakFixedPolyomino.ULogCounterPumpBinarySteps

open ULogCompiler ULogFiniteTapeZipperRun ULogCounterPump
open ULogBinaryCounterValue

def cell (b : Bool) : Fin 4 := if b then 1 else 0

def cells (bs : List Bool) : List (Fin 4) := bs.map cell

@[simp] theorem cells_length (bs : List Bool) : (cells bs).length = bs.length := by
  simp [cells]

theorem cells_no_blank (bs : List Bool) : ∀ a ∈ cells bs, a ≠ (2 : Fin 4) := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  cases b <;> decide

theorem cells_append (xs ys : List Bool) : cells (xs ++ ys) = cells xs ++ cells ys := by
  simp [cells]

theorem cells_replicate (k : Nat) (b : Bool) :
    cells (List.replicate k b) = List.replicate k (cell b) := by
  simp [cells]

def data (bs : List Bool) (m : Nat) : List (Fin 4) :=
  cells bs ++ 3 :: List.replicate m 0

@[simp] theorem data_length (bs : List Bool) (m : Nat) :
    (data bs m).length = bs.length + m + 1 := by
  simp [data]; omega

theorem data_no_blank (bs : List Bool) (m : Nat) : ∀ a ∈ data bs m, a ≠ (2 : Fin 4) := by
  intro a ha
  simp only [data, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | ha | ha
  · exact cells_no_blank bs a ha
  · subst a; decide
  · have hzero : a = 0 := (List.mem_replicate.mp ha).2
    subst a; decide

theorem data_append_zero (bs : List Bool) (m : Nat) :
    data bs m ++ [0] = data bs (m + 1) := by
  simp [data, List.replicate_add, List.append_assoc]

theorem increment_run {bs next : List Bool} {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail) (head : Int) (m : Nat) :
    run program 2 (List.replicate (2 * n + 2) false) head (fromCells 3 [2] (data bs m)) =
      some (head, fromCells 5 [2] (data next m)) := by
  simpa [hb, hn, data, cells, cell, List.append_assoc] using
    ULogCounterPumpCounterSteps.increment_return n head (data tail m)

theorem overflow_run {bs : List Bool} (hi : increment bs = none) (head : Int) (m : Nat) :
    run program 2 (List.replicate (bs.length + 1) false) head (fromCells 3 [2] (data bs m)) =
      some (head + bs.length, fromCells 0 (List.replicate bs.length 0 ++ [2])
        (3 :: List.replicate m 0)) := by
  have hc : cells bs = List.replicate bs.length (1 : Fin 4) := by
    have h := congrArg cells (increment_none_bits hi)
    simpa [cells_replicate, cell] using h
  rw [data, hc]
  exact ULogCounterPumpCounterSteps.overflow_accept bs.length head _

end PakFixedPolyomino.ULogCounterPumpBinarySteps
