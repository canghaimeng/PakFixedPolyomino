import PakFixedPolyomino.ConcretePakScanner
import Mathlib.Tactic

/-!
# Generated five-track coupling predicates

This module implements the five literal same-cell predicates `(K-W)`,
`(K-E)`, `(K-S)`, `(K-N)`, and `(K-nE)` from the paper.  It deliberately
separates their finite, executable logic from the still missing byte-level
description of the fixed source machine `M_star`.

Instantiating `MachineBoundaryData` with that machine's actual start and
accepting states and four distinguished tape letters produces the complete
five Boolean lookup tables.  No semantic theorem about `M_star` is assumed
here.
-/

namespace PakFixedPolyomino.PakCouplingGenerated

open ConcretePakScanner

variable {MachineState Tape Arrow : Type*}
variable [Fintype MachineState] [Fintype Tape] [Fintype Arrow]
variable [DecidableEq MachineState] [DecidableEq Tape] [DecidableEq Arrow]

/-- The only source-machine constants used by the five local coupling
predicates.  The parser and universal simulation do not enter this interface;
they are properties of the transition inventory supplied later. -/
structure MachineBoundaryData (MachineState Tape : Type*) where
  start : MachineState
  accept : MachineState
  hash : Tape
  zero : Tape
  one : Tape
  work : Tape
  rightEnd : Tape

variable (B : MachineBoundaryData MachineState Tape)
variable (M : TableauMachineData MachineState Tape Arrow)
variable (Q : ℕ) [NeZero Q]

abbrev Tracks :=
  ConcreteWProd.Tracks M Q ConcretePakScanner.State

def amp (u : Tracks M Q) : SharedQAmpTile Q := u.1.1.1

def ripple (u : Tracks M Q) : RippleTile := u.1.1.2

def tableau (u : Tracks M Q) :
    HigherBlockTableauTile MachineState Tape Arrow M := u.1.2

def scan (u : Tracks M Q) : ConcretePakScanner.Tile := u.2

/-- Scanner-buffer letters embedded into the actual source-machine cells. -/
def bufferCell : ConcretePakScanner.Buffer → TableauCell MachineState Tape
  | .hash => .plain B.hash
  | .zero => .plain B.zero
  | .one => .plain B.one
  | .work => .plain B.work
  | .rightEnd => .plain B.rightEnd
  | .headZero => .head B.start B.zero
  | .headOne => .head B.start B.one

/-- The radius-one tableau window emitted by one marked scanner tile. -/
def emittedWindow (s t : ConcretePakScanner.State) :
    CellTriple (TableauCell MachineState Tape) :=
  { minus := bufferCell B s.left
    center := bufferCell B s.centre
    plus := bufferCell B t.centre }

def emittedMatches
    (X : CellTriple (TableauCell MachineState Tape))
    (s t : ConcretePakScanner.State) : Prop :=
  X.minus = bufferCell B s.left ∧
    X.center = bufferCell B s.centre ∧
    X.plus = bufferCell B t.centre

theorem emittedMatches_iff_eq
    (X : CellTriple (TableauCell MachineState Tape))
    (s t : ConcretePakScanner.State) :
    emittedMatches B X s t ↔ X = emittedWindow B s t := by
  constructor
  · rintro ⟨hm, hc, hp⟩
    apply CellTriple.ext <;> assumption
  · intro h
    subst X
    exact ⟨rfl, rfl, rfl⟩

def cellAccepting : TableauCell MachineState Tape → Prop
  | .plain _ => True
  | .head q _ => q = B.accept

/-- A west window is accepting when every head visible in it has the accepting
state.  The column order-bit theorem supplies the unique physical head. -/
def acceptingWindow (X : CellTriple (TableauCell MachineState Tape)) : Prop :=
  cellAccepting B X.minus ∧ cellAccepting B X.center ∧ cellAccepting B X.plus

/-- Literal south sentinel colour `S_hash`. -/
def southSentinel (u : HigherBlockTableauTile MachineState Tape Arrow M) : Prop :=
  u.1.old.minus = .plain B.hash ∧
  u.1.old.center = .plain B.hash ∧
  u.1.new.minus = .plain B.hash ∧
  u.1.new.center = .plain B.hash ∧
  u.1.oldMinusBit = false ∧ u.1.newMinusBit = false ∧
  u.1.southToken = none

/-- Literal north sentinel colour `N_hash`. -/
def northSentinel (u : HigherBlockTableauTile MachineState Tape Arrow M) : Prop :=
  u.1.old.center = .plain B.hash ∧
  u.1.old.plus = .plain B.hash ∧
  u.1.new.center = .plain B.hash ∧
  u.1.new.plus = .plain B.hash ∧
  u.1.oldPlusBit = true ∧ u.1.newPlusBit = true ∧
  u.1.northToken = none

def scannerBottom : ConcretePakScanner.State :=
  { phase := .bot, left := .hash, centre := .hash,
    lookahead := .lh0, mode := .binary }

def scannerTopSouth (s : ConcretePakScanner.State) : Prop :=
  s.phase = .top ∧ s.centre = .hash ∧
    s.lookahead = .lh1 ∧ s.mode = .high

/-- `(K-W)`. -/
def West (u : Tracks M Q) : Prop :=
  (amp M Q u).1.westActive = true →
    (ripple M Q u).1 = false ∧
    acceptingWindow B (tableau M Q u).1.new ∧
    scan M Q u = none

/-- `(K-E)`, including `(K-phase)` and `(K-lh)` through
`ActivityCoupledStep`. -/
def East (u : Tracks M Q) : Prop :=
  (amp M Q u).1.eastActive = true →
    ActivityCoupledStep
      (amp M Q u).1.southActive
      (amp M Q u).1.northActive
      (scan M Q u)
      (xor (ripple M Q u).1 (ripple M Q u).2) ∧
    ∃ s t : ConcretePakScanner.State,
      scan M Q u = some (s, t) ∧
      emittedMatches B (tableau M Q u).1.old s t

/-- `(K-S)`. -/
def South (u : Tracks M Q) : Prop :=
  (amp M Q u).1.southActive = true →
    (ripple M Q u).2 = true ∧
    southSentinel B M (tableau M Q u) ∧
    ((amp M Q u).1.eastActive = true →
      ∃ t : ConcretePakScanner.State,
        scan M Q u = some (scannerBottom, t))

/-- `(K-N)`. -/
def North (u : Tracks M Q) : Prop :=
  (amp M Q u).1.northActive = true →
    ((ripple M Q u).1 && (ripple M Q u).2) = false ∧
    northSentinel B M (tableau M Q u) ∧
    ((amp M Q u).1.eastActive = true →
      ∃ s t : ConcretePakScanner.State,
        scan M Q u = some (s, t) ∧ scannerTopSouth s)

/-- `(K-nE)`. -/
def NonEast (u : Tracks M Q) : Prop :=
  (amp M Q u).1.eastActive = false → scan M Q u = none

instance (u : Tracks M Q) : Decidable (West B M Q u) := by
  unfold West acceptingWindow
  cases (tableau M Q u).1.new.minus <;>
    cases (tableau M Q u).1.new.center <;>
    cases (tableau M Q u).1.new.plus <;>
    simp only [cellAccepting] <;> infer_instance

instance (u : Tracks M Q) : Decidable (East B M Q u) := by
  unfold East emittedMatches
  infer_instance

instance (u : Tracks M Q) : Decidable (South B M Q u) := by
  unfold South southSentinel
  infer_instance

instance (u : Tracks M Q) : Decidable (North B M Q u) := by
  unfold North northSentinel scannerTopSouth
  infer_instance

instance (u : Tracks M Q) : Decidable (NonEast M Q u) := by
  unfold NonEast
  infer_instance

/-- The five finite Boolean lookup tables generated from the machine boundary
constants.  These are executable after the finite machine types are supplied. -/
def fiveCouplings : ConcreteWProd.FiveCouplingTable M Q ConcretePakScanner.State where
  west u := decide (West B M Q u)
  east u := decide (East B M Q u)
  south u := decide (South B M Q u)
  north u := decide (North B M Q u)
  nonEast u := decide (NonEast M Q u)

theorem fiveCouplings_accepts_iff (u : Tracks M Q) :
    ConcreteWProd.FiveCouplingTable.accepts M Q (fiveCouplings B M Q) u ↔
      West B M Q u ∧ East B M Q u ∧ South B M Q u ∧
        North B M Q u ∧ NonEast M Q u := by
  simp [ConcreteWProd.FiveCouplingTable.accepts, fiveCouplings]

theorem coupled_nonEast_idle {u : Tracks M Q}
    (h : ConcreteWProd.FiveCouplingTable.accepts M Q (fiveCouplings B M Q) u)
    (hne : (amp M Q u).1.eastActive = false) :
    scan M Q u = none := by
  exact ((fiveCouplings_accepts_iff B M Q u).mp h).2.2.2.2 hne

theorem coupled_east_marked {u : Tracks M Q}
    (h : ConcreteWProd.FiveCouplingTable.accepts M Q (fiveCouplings B M Q) u)
    (he : (amp M Q u).1.eastActive = true) :
    ∃ s t : ConcretePakScanner.State,
      scan M Q u = some (s, t) ∧
      (tableau M Q u).1.old = emittedWindow B s t := by
  rcases (((fiveCouplings_accepts_iff B M Q u).mp h).2.1 he).2 with
    ⟨s, t, hscan, hwindow⟩
  exact ⟨s, t, hscan, (emittedMatches_iff_eq B _ _ _).mp hwindow⟩

theorem coupled_no_double_vertical_activity {u : Tracks M Q}
    (h : ConcreteWProd.FiveCouplingTable.accepts M Q (fiveCouplings B M Q) u)
    (he : (amp M Q u).1.eastActive = true) :
    ¬ ((amp M Q u).1.southActive = true ∧
       (amp M Q u).1.northActive = true) := by
  intro hboth
  have hstep := (((fiveCouplings_accepts_iff B M Q u).mp h).2.1 he).1
  rcases hboth with ⟨hs, hn⟩
  rw [hs, hn] at hstep
  exact activityCoupled_no_double_end (scan M Q u)
    (xor (ripple M Q u).1 (ripple M Q u).2) hstep

end PakFixedPolyomino.PakCouplingGenerated
