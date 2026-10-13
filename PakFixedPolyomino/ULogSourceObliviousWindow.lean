import PakFixedPolyomino.ULogSourceOneHotBlocks
import PakFixedPolyomino.ULogSourceOneHotReader
import Mathlib.Tactic

/-! # Fixed-window tape cells and an oblivious round-trip schedule

This is the spatial front end needed by an exact-resource source compiler.
The simulated head is data in a fixed-width cell, while the physical head
performs the same complete round trip for every source branch.
-/

namespace PakFixedPolyomino.ULogSourceObliviousWindow

open ULogSourceOneHotBlocks ULogSourceOneHotReader

abbrev PhysicalTape := Fin 3

/-- One logical tape symbol together with the unique simulated-head bit. -/
structure MarkedCell (nt : ℕ) where
  symbol : Fin nt
  head : Bool
  deriving DecidableEq, Fintype, Repr

/-- `head` is stored first, followed by the fixed-width one-hot symbol. -/
def encodeMarkedCell {nt : ℕ} (c : MarkedCell nt) : List PhysicalTape :=
  tapeOfBit c.head :: (encodeOneHot c.symbol).map tapeOfBit

@[simp] theorem encodeMarkedCell_length {nt : ℕ} (c : MarkedCell nt) :
    (encodeMarkedCell c).length = nt + 1 := by
  simp [encodeMarkedCell]

theorem tapeOfBit_injective : Function.Injective tapeOfBit := by
  intro a b h
  cases a <;> cases b <;> simp [tapeOfBit, zero, one] at h ⊢

theorem map_tapeOfBit_injective :
    Function.Injective (List.map tapeOfBit) :=
  List.map_injective_iff.mpr tapeOfBit_injective

theorem encodeMarkedCell_injective {nt : ℕ} :
    Function.Injective (encodeMarkedCell (nt := nt)) := by
  intro a b h
  have hhead := congrArg List.head? h
  have htail := congrArg List.tail h
  have hhead' : a.head = b.head := by
    simp [encodeMarkedCell] at hhead
    exact tapeOfBit_injective hhead
  have hsymbolMap :
      (encodeOneHot a.symbol).map tapeOfBit =
        (encodeOneHot b.symbol).map tapeOfBit := by
    simpa [encodeMarkedCell] using htail
  have hsymbolBits : encodeOneHot a.symbol = encodeOneHot b.symbol :=
    map_tapeOfBit_injective hsymbolMap
  have hsymbol : a.symbol = b.symbol := encodeOneHot_injective hsymbolBits
  cases a
  cases b
  simp_all

/-- Concatenation of equal-width marked cells. -/
def encodeWindow {nt : ℕ} (cells : List (MarkedCell nt)) :
    List PhysicalTape := cells.flatMap encodeMarkedCell

@[simp] theorem encodeWindow_length {nt : ℕ}
    (cells : List (MarkedCell nt)) :
    (encodeWindow cells).length = cells.length * (nt + 1) := by
  induction cells with
  | nil => simp [encodeWindow]
  | cons c cells ih =>
      simp [encodeWindow, ih]
      rw [Nat.add_mul]
      omega

theorem encodeWindow_injective {nt : ℕ} :
    Function.Injective (encodeWindow (nt := nt)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length h
          simp [encodeWindow] at hlen
          omega
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hlen := congrArg List.length h
          simp [encodeWindow] at hlen
      | cons y ys =>
          have hfirst := congrArg (List.take (nt + 1)) h
          have hrest := congrArg (List.drop (nt + 1)) h
          have hxy : x = y := by
            apply encodeMarkedCell_injective
            simpa [encodeWindow] using hfirst
          subst y
          have htail : xs = ys := by
            apply ih
            simpa [encodeWindow] using hrest
          subst ys
          rfl

/-- A finite logical tape window with the simulated head stored as an index,
not as the position of the physical scanner. -/
structure LogicalWindow (nt : ℕ) where
  cells : List (Fin nt)
  head : Fin cells.length
  deriving DecidableEq, Repr

def moveIndex {n : ℕ} (move : OneTapeTableau.Move) (i : Fin n) :
    Option (Fin n) :=
  match move with
  | .stay => some i
  | .right => if h : i.1 + 1 < n then some ⟨i.1 + 1, h⟩ else none
  | .left => if h : 0 < i.1 then some ⟨i.1 - 1, by omega⟩ else none

@[simp] theorem moveIndex_stay {n : ℕ} (i : Fin n) :
    moveIndex .stay i = some i := rfl

theorem moveIndex_right {n : ℕ} (i : Fin n) (h : i.1 + 1 < n) :
    moveIndex .right i = some ⟨i.1 + 1, h⟩ := by
  simp [moveIndex, h]

theorem moveIndex_left {n : ℕ} (i : Fin n) (h : 0 < i.1) :
    moveIndex .left i = some ⟨i.1 - 1, by omega⟩ := by
  simp [moveIndex, h]

/-- Pure logical effect computed by an oblivious window sweep.  Failure means
that the simulated head attempted to leave the preallocated window. -/
def LogicalWindow.applyAction? {ns nt : ℕ} (w : LogicalWindow nt)
    (a : ULogCompiler.BoundedAction ns nt) : Option (LogicalWindow nt) := do
  let nextHead ← moveIndex a.move w.head
  let nextCells := w.cells.set w.head a.write
  have hlength : nextCells.length = w.cells.length := by simp [nextCells]
  pure {
    cells := nextCells
    head := ⟨nextHead.1, by simpa [hlength] using nextHead.2⟩ }

@[simp] theorem LogicalWindow.applyAction_stay {ns nt : ℕ}
    (w : LogicalWindow nt) (a : ULogCompiler.BoundedAction ns nt)
    (hmove : a.move = .stay) :
    w.applyAction? a = some {
      cells := w.cells.set w.head a.write
      head := ⟨w.head.1, by simp⟩ } := by
  rcases a with ⟨write, target, move⟩
  simp only at hmove
  subst move
  simp [LogicalWindow.applyAction?, moveIndex]

theorem LogicalWindow.applyAction_preserves_width {ns nt : ℕ}
    (w next : LogicalWindow nt) (a : ULogCompiler.BoundedAction ns nt)
    (h : w.applyAction? a = some next) :
    next.cells.length = w.cells.length := by
  unfold LogicalWindow.applyAction? at h
  cases hm : moveIndex a.move w.head with
  | none => simp [hm] at h
  | some nextHead =>
      simp [hm] at h
      subst next
      simp

/-- Place a finite-list source configuration in a symmetric logical window.
The two radius blocks are genuine logical blanks reserved for future head
moves; the simulated head is the distinguished middle occurrence. -/
def boundedWindowCells {ns nt : ℕ} (blank : Fin nt) (radius : ℕ)
    (c : ULogCompiler.BoundedConfig ns nt) : List (Fin nt) :=
  List.replicate radius blank ++ c.leftRev.reverse ++
    c.focus :: (c.right ++ List.replicate radius blank)

def boundedWindow {ns nt : ℕ} (blank : Fin nt) (radius : ℕ)
    (c : ULogCompiler.BoundedConfig ns nt) : LogicalWindow nt where
  cells := boundedWindowCells blank radius c
  head := ⟨radius + c.leftRev.length, by
    simp [boundedWindowCells]⟩

@[simp] theorem boundedWindow_cells_length {ns nt : ℕ}
    (blank : Fin nt) (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (boundedWindow blank radius c).cells.length =
      2 * radius + c.leftRev.length + c.right.length + 1 := by
  simp [boundedWindow, boundedWindowCells]
  omega

@[simp] theorem boundedWindow_head_val {ns nt : ℕ}
    (blank : Fin nt) (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (boundedWindow blank radius c).head.1 = radius + c.leftRev.length := rfl

@[simp] theorem boundedWindow_head_symbol {ns nt : ℕ}
    (blank : Fin nt) (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (boundedWindow blank radius c).cells.get
      (boundedWindow blank radius c).head = c.focus := by
  simp [boundedWindow, boundedWindowCells]

/-- Materialize the motion reserve as ordinary source blanks.  Unlike an
external proof-only margin, these cells remain part of the fixed logical
window throughout the simulated run. -/
def padBoundedConfig {ns nt : ℕ} (blank : Fin nt) (radius : ℕ)
    (c : ULogCompiler.BoundedConfig ns nt) : ULogCompiler.BoundedConfig ns nt :=
  { state := c.state
    leftRev := c.leftRev ++ List.replicate radius blank
    focus := c.focus
    right := c.right ++ List.replicate radius blank }

@[simp] theorem padBoundedConfig_state {ns nt : ℕ} (blank : Fin nt)
    (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (padBoundedConfig blank radius c).state = c.state := rfl

@[simp] theorem padBoundedConfig_focus {ns nt : ℕ} (blank : Fin nt)
    (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (padBoundedConfig blank radius c).focus = c.focus := rfl

@[simp] theorem padBoundedConfig_tape_length {ns nt : ℕ} (blank : Fin nt)
    (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (padBoundedConfig blank radius c).leftRev.length + 1 +
      (padBoundedConfig blank radius c).right.length =
      c.leftRev.length + 1 + c.right.length + 2 * radius := by
  simp [padBoundedConfig]
  omega

/-- The fully materialized window used by the oblivious compiler. -/
def materializedWindow {ns nt : ℕ} (blank : Fin nt) (radius : ℕ)
    (c : ULogCompiler.BoundedConfig ns nt) : LogicalWindow nt :=
  boundedWindow blank 0 (padBoundedConfig blank radius c)

@[simp] theorem materializedWindow_cells_length {ns nt : ℕ}
    (blank : Fin nt) (radius : ℕ) (c : ULogCompiler.BoundedConfig ns nt) :
    (materializedWindow blank radius c).cells.length =
      c.leftRev.length + c.right.length + 1 + 2 * radius := by
  simp [materializedWindow, padBoundedConfig]
  omega

def LogicalWindow.markedCells {nt : ℕ} (w : LogicalWindow nt) :
    List (MarkedCell nt) :=
  List.ofFn fun i : Fin w.cells.length =>
    ⟨w.cells.get i, decide (i = w.head)⟩

@[simp] theorem LogicalWindow.markedCells_length {nt : ℕ}
    (w : LogicalWindow nt) : w.markedCells.length = w.cells.length := by
  simp [LogicalWindow.markedCells]

@[simp] theorem LogicalWindow.markedCells_get_symbol {nt : ℕ}
    (w : LogicalWindow nt) (i : Fin w.cells.length) :
    (w.markedCells.get ⟨i.1, by simpa using i.2⟩).symbol =
      w.cells.get i := by
  simp [LogicalWindow.markedCells]

@[simp] theorem LogicalWindow.markedCells_get_head {nt : ℕ}
    (w : LogicalWindow nt) (i : Fin w.cells.length) :
    (w.markedCells.get ⟨i.1, by simpa using i.2⟩).head =
      decide (i.1 = w.head.1) := by
  simp [LogicalWindow.markedCells, Fin.ext_iff]

theorem LogicalWindow.unique_marked_head {nt : ℕ}
    (w : LogicalWindow nt) :
    ∃! i : Fin w.markedCells.length, (w.markedCells.get i).head = true := by
  let h : Fin w.markedCells.length := ⟨w.head.1, by simpa using w.head.2⟩
  refine ⟨h, ?_, ?_⟩
  · have hh := LogicalWindow.markedCells_get_head w w.head
    simpa [h] using hh
  · intro i hi
    let j : Fin w.cells.length := ⟨i.1, by simpa using i.2⟩
    have hj := LogicalWindow.markedCells_get_head w j
    have hi' :
        (w.markedCells.get ⟨j.1, by simpa using j.2⟩).head = true := by
      simpa [j] using hi
    have : i.1 = w.head.1 := by
      rw [hj] at hi'
      simpa [j] using hi'
    apply Fin.ext
    simpa [h] using this

def LogicalWindow.encode {nt : ℕ} (w : LogicalWindow nt) :
    List PhysicalTape := encodeWindow w.markedCells

@[simp] theorem LogicalWindow.encode_length {nt : ℕ}
    (w : LogicalWindow nt) :
    w.encode.length = w.cells.length * (nt + 1) := by
  simp [LogicalWindow.encode]

/-- Physical positions in one complete left-to-right and right-to-left scan.
The duplicated far endpoint is intentional: it gives every phase a literal
fixed length and makes concatenation of scan rounds definitionally simple. -/
def roundTripSweep (width : ℕ) : List (Fin width) :=
  List.finRange width ++ (List.finRange width).reverse

@[simp] theorem roundTripSweep_length (width : ℕ) :
    (roundTripSweep width).length = 2 * width := by
  simp [roundTripSweep, Nat.mul_comm]
  omega

theorem mem_roundTripSweep {width : ℕ} (i : Fin width) :
    i ∈ roundTripSweep width := by
  simp [roundTripSweep]

theorem roundTripSweep_head {width : ℕ} (hwidth : 0 < width) :
    (roundTripSweep width).head? = some ⟨0, hwidth⟩ := by
  cases width with
  | zero => cases hwidth
  | succ width =>
      simp only [roundTripSweep, List.head?_append]
      simp [List.finRange]

theorem roundTripSweep_last {width : ℕ} (hwidth : 0 < width) :
    (roundTripSweep width).getLast? = some ⟨0, hwidth⟩ := by
  cases width with
  | zero => cases hwidth
  | succ width =>
      simp only [roundTripSweep, List.getLast?_append,
        List.getLast?_reverse]
      simp [List.finRange]

/-- Repeating the round trip `steps` times gives a branch-independent
physical schedule with a literal closed-form length. -/
def repeatedSweep (width steps : ℕ) : List (Fin width) :=
  List.replicate steps (roundTripSweep width) |>.flatten

@[simp] theorem repeatedSweep_length (width steps : ℕ) :
    (repeatedSweep width steps).length = steps * (2 * width) := by
  simp [repeatedSweep]

theorem mem_repeatedSweep_of_pos {width steps : ℕ}
    (hsteps : 0 < steps) (i : Fin width) :
    i ∈ repeatedSweep width steps := by
  cases steps with
  | zero => cases hsteps
  | succ steps =>
      simp [repeatedSweep, mem_roundTripSweep]

/-- The physical scanner schedule for one logical transition.  It depends
only on the allocated window width, never on a branch or head move. -/
def LogicalWindow.oneStepSchedule {nt : ℕ} (w : LogicalWindow nt) :
    List (Fin w.encode.length) := roundTripSweep w.encode.length

@[simp] theorem LogicalWindow.oneStepSchedule_length {nt : ℕ}
    (w : LogicalWindow nt) :
    w.oneStepSchedule.length = 2 * (w.cells.length * (nt + 1)) := by
  simp [LogicalWindow.oneStepSchedule]

end PakFixedPolyomino.ULogSourceObliviousWindow
