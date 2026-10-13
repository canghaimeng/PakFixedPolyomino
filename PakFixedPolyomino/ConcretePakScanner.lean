import PakFixedPolyomino.WProdRegisterConcrete
import Mathlib.Tactic

/-!
# The literal repaired Pak scanner table

This file is the first machine-level component of the headline closure.  The
four finite coordinates and the four `LegalScan` clauses are the literal
`bot/mid/preTop/top/cap/lookahead/high-zero` table in the JACM construction.
They do not depend on the still-unformalized source machine or on `Q`.
-/

namespace PakFixedPolyomino.ConcretePakScanner

inductive Buffer where
  | hash | zero | one | work | rightEnd | headZero | headOne
  deriving DecidableEq, Repr

instance : Fintype Buffer := Fintype.ofList
  [.hash, .zero, .one, .work, .rightEnd, .headZero, .headOne] (by
    intro x
    cases x <;> simp)

inductive Phase where
  | bot | mid | top | cap
  deriving DecidableEq, Repr

instance : Fintype Phase := Fintype.ofList [.bot, .mid, .top, .cap] (by
  intro x
  cases x <;> simp)

inductive Lookahead where
  | lh0 | lh1
  deriving DecidableEq, Repr

instance : Fintype Lookahead := Fintype.ofList [.lh0, .lh1] (by
  intro x
  cases x <;> simp)

inductive Mode where
  | high | binary | tail
  deriving DecidableEq, Repr

instance : Fintype Mode := Fintype.ofList [.high, .binary, .tail] (by
  intro x
  cases x <;> simp)

@[ext] structure State where
  phase : Phase
  left : Buffer
  centre : Buffer
  lookahead : Lookahead
  mode : Mode
  deriving DecidableEq, Fintype, Repr

inductive Clause where
  | bot | mid | terminal | tail | preTop | top
  deriving DecidableEq, Repr

instance : Fintype Clause := Fintype.ofList
  [.bot, .mid, .terminal, .tail, .preTop, .top] (by
  intro x
  cases x <;> simp)

def headBuffer : Bool → Buffer
  | false => .headZero
  | true => .headOne

/-- `NewMid(b,m')` from the paper. -/
def newMid : Bool → Mode → Buffer
  | _, .tail => .hash
  | true, _ => .one
  | false, .high => .work
  | false, .binary => .zero

/-- North-to-south high-zero mode update `ModeOut(b,m')`. -/
def modeOut : Bool → Mode → Mode
  | false, .high => .high
  | true, .high => .binary
  | _, .binary => .binary
  | _, .tail => .high

def topNorth : State :=
  { phase := .cap, left := .hash, centre := .hash,
    lookahead := .lh0, mode := .high }

/-- The common buffer-overlap equation `u' = v`. -/
def Shift (s t : State) : Prop := t.left = s.centre

/-- One labelled clause of the exact finite scanner relation. -/
def LegalClause : Clause → State → State → Bool → Prop
  | .bot, s, t, b =>
      Shift s t ∧
      s.phase = .bot ∧ s.lookahead = .lh0 ∧
      s.left = .hash ∧ s.centre = .hash ∧
      t.phase = .mid ∧ t.lookahead = .lh0 ∧
      s.mode = .binary ∧ t.centre = headBuffer b
  | .mid, s, t, b =>
      Shift s t ∧
      s.phase = .mid ∧ t.phase = .mid ∧
      s.lookahead = .lh0 ∧ t.lookahead = .lh0 ∧
      t.centre = newMid b t.mode ∧ s.mode = modeOut b t.mode
  | .terminal, s, t, b =>
      Shift s t ∧
      s.phase = .mid ∧ t.phase = .mid ∧
      s.lookahead = .lh0 ∧ t.lookahead = .lh0 ∧
      (s.mode = .high ∨ s.mode = .binary) ∧ t.mode = .tail ∧
      t.centre = .rightEnd ∧ b = false
  | .tail, s, t, b =>
      Shift s t ∧
      s.phase = .mid ∧ t.phase = .mid ∧
      s.lookahead = .lh0 ∧ t.lookahead = .lh0 ∧
      s.mode = .tail ∧ t.mode = .tail ∧
      t.centre = .hash ∧ b = false
  | .preTop, s, t, b =>
      Shift s t ∧
      s.phase = .mid ∧ t.phase = .top ∧
      s.lookahead = .lh0 ∧ t.lookahead = .lh1 ∧
      t.centre = .hash ∧ (s.mode = .high ∨ s.mode = .tail) ∧
      t.mode = .high ∧
      b = false
  | .top, s, t, _ =>
      Shift s t ∧
      s.phase = .top ∧ t.phase = .cap ∧
      s.lookahead = .lh1 ∧ t.lookahead = .lh0 ∧
      s.mode = .high ∧ t.mode = .high ∧
      s.centre = .hash ∧ t.centre = .hash ∧ t.left = .hash

instance (c : Clause) (s t : State) (b : Bool) :
    Decidable (LegalClause c s t b) := by
  cases c <;> unfold LegalClause Shift <;> infer_instance

def LegalScan (s t : State) (b : Bool) : Prop :=
  ∃ c : Clause, LegalClause c s t b

instance (s t : State) (b : Bool) : Decidable (LegalScan s t b) := by
  unfold LegalScan
  infer_instance

def emit (s t : State) : Buffer × Buffer × Buffer :=
  (s.left, s.centre, t.centre)

@[simp] theorem card_buffer : Fintype.card Buffer = 7 := by native_decide
@[simp] theorem card_phase : Fintype.card Phase = 4 := by native_decide
@[simp] theorem card_lookahead : Fintype.card Lookahead = 2 := by native_decide
@[simp] theorem card_mode : Fintype.card Mode = 3 := by native_decide
@[simp] theorem card_state : Fintype.card State = 1176 := by native_decide

/-- The formula tables are total on their declared finite inputs. -/
theorem newMid_total (b : Bool) (m : Mode) : ∃ x, newMid b m = x :=
  ⟨newMid b m, rfl⟩

theorem modeOut_total (b : Bool) (m : Mode) : ∃ x, modeOut b m = x :=
  ⟨modeOut b m, rfl⟩

/-- The finite clauses are disjoint; a legal edge has one unambiguous role. -/
theorem legalClause_unique :
    ∀ (c d : Clause) (s t : State) (b : Bool),
      LegalClause c s t b → LegalClause d s t b → c = d := by
  intro c d s t b hc hd
  cases c <;> cases d <;>
    simp_all [LegalClause, Shift, newMid, modeOut] <;>
      all_goals
        cases t with
        | mk tp tl tc lk tm =>
          cases tm <;> cases b <;>
            simp_all [newMid, modeOut]

theorem legalScan_shift {s t : State} {b : Bool} (h : LegalScan s t b) :
    Shift s t := by
  rcases h with ⟨c, hc⟩
  cases c <;> exact hc.1

/-- No legal scanner tile can start below a `cap` state. -/
theorem no_clause_from_cap :
    ∀ (s t : State) (b : Bool), s.phase = .cap → ¬ LegalScan s t b := by
  native_decide

/-- No legal scanner tile exposes `bot` on its north side. -/
theorem no_clause_to_bot :
    ∀ (s t : State) (b : Bool), t.phase = .bot → ¬ LegalScan s t b := by
  native_decide

theorem preTop_reads_zero {s t : State} {b : Bool}
    (h : LegalClause .preTop s t b) : b = false := h.2.2.2.2.2.2.2.2

theorem top_forces_cap {s t : State} {b : Bool}
    (h : LegalClause .top s t b) : t = topNorth := by
  rcases h with ⟨_hshift, _hsphase, htphase, _hslook, htlook,
    _hsmode, htmode, _hscentre, htcentre, htleft⟩
  apply State.ext
  · exact htphase
  · exact htleft
  · exact htcentre
  · exact htlook
  · exact htmode

/-- Local nondeterminism is bounded and completely visible.  In particular,
the global uniqueness argument must use the north-to-south mode boundary; it
must not silently claim that `LegalScan` is a partial function. -/
theorem legal_successors_at_most_four :
    ∀ (s : State) (b : Bool),
      Fintype.card {t : State // LegalScan s t b} ≤ 4 := by
  native_decide

/-- The concrete marked east-diode tile inventory used by `W_prod`. -/
abbrev Tile := ScannerTile State

def wangTile : Tile → WangTile Bool (Option State) := scannerTile

/-- `(K-phase)`: south activity marks `bot`, north activity marks `top`, and
ordinary east-boundary cells carry `mid`.  Both activities at one cell are
rejected; that thin-square case is outside the `n ≥ 5` full-frame theorem. -/
def PhaseCoupled (southActive northActive : Bool) (p : Phase) : Prop :=
  match southActive, northActive with
  | true, false => p = .bot
  | false, true => p = .top
  | false, false => p = .mid
  | true, true => False

instance (s n : Bool) (p : Phase) : Decidable (PhaseCoupled s n p) := by
  cases s <;> cases n <;> unfold PhaseCoupled <;> infer_instance

/-- `(K-lh)`: the lookahead bit is literally the current cell's north-side
activity bit, not a `Q`-valued amplifier colour. -/
def LookaheadCoupled (northActive : Bool) (l : Lookahead) : Prop :=
  l = if northActive then .lh1 else .lh0

instance (n : Bool) (l : Lookahead) : Decidable (LookaheadCoupled n l) := by
  unfold LookaheadCoupled
  infer_instance

/-- The complete scanner part of an east-active same-cell coupling. -/
def ActivityCoupledStep
    (southActive northActive : Bool) (scan : Tile) (bit : Bool) : Prop :=
  ∃ s t : State,
    scan = some (s, t) ∧ LegalScan s t bit ∧
    PhaseCoupled southActive northActive s.phase ∧
    LookaheadCoupled northActive s.lookahead

instance (s n : Bool) (scan : Tile) (b : Bool) :
    Decidable (ActivityCoupledStep s n scan b) := by
  unfold ActivityCoupledStep
  infer_instance

theorem activityCoupled_no_double_end :
    ∀ (scan : Tile) (b : Bool), ¬ ActivityCoupledStep true true scan b := by
  rintro scan b ⟨s, t, _, _, hphase, _⟩
  exact hphase

theorem activityCoupled_bottom_phase :
    ∀ (scan : Tile) (b : Bool) (s t : State),
      scan = some (s, t) → ActivityCoupledStep true false scan b →
      s.phase = .bot ∧ s.lookahead = .lh0 := by
  rintro scan b s t rfl ⟨s', t', heq, _, hp, hl⟩
  have hpair : (s, t) = (s', t') := Option.some.inj heq
  have hs : s = s' := by simpa using congrArg Prod.fst hpair
  have ht : t = t' := by simpa using congrArg Prod.snd hpair
  subst s'
  subst t'
  exact ⟨hp, hl⟩

theorem activityCoupled_middle_phase :
    ∀ (scan : Tile) (b : Bool) (s t : State),
      scan = some (s, t) → ActivityCoupledStep false false scan b →
      s.phase = .mid ∧ s.lookahead = .lh0 := by
  rintro scan b s t rfl ⟨s', t', heq, _, hp, hl⟩
  have hpair : (s, t) = (s', t') := Option.some.inj heq
  have hs : s = s' := by simpa using congrArg Prod.fst hpair
  have ht : t = t' := by simpa using congrArg Prod.snd hpair
  subst s'
  subst t'
  exact ⟨hp, hl⟩

theorem activityCoupled_top_phase :
    ∀ (scan : Tile) (b : Bool) (s t : State),
      scan = some (s, t) → ActivityCoupledStep false true scan b →
      s.phase = .top ∧ s.lookahead = .lh1 := by
  rintro scan b s t rfl ⟨s', t', heq, _, hp, hl⟩
  have hpair : (s, t) = (s', t') := Option.some.inj heq
  have hs : s = s' := by simpa using congrArg Prod.fst hpair
  have ht : t = t' := by simpa using congrArg Prod.snd hpair
  subst s'
  subst t'
  exact ⟨hp, hl⟩

/-- This finite check is the local cap/lookahead repair: a top-coupled cell
has exactly the repaired `Top` role and exposes `topNorth`; an early top chain
cannot continue because `cap` has no outgoing clause. -/
theorem activityCoupled_top_forces_cap :
    ∀ (scan : Tile) (b : Bool) (s t : State),
      scan = some (s, t) → ActivityCoupledStep false true scan b →
      LegalClause .top s t b ∧ t = topNorth := by
  rintro scan b s t rfl ⟨s', t', heq, ⟨c, hc⟩, hp, _⟩
  have hpair : (s, t) = (s', t') := Option.some.inj heq
  have hs : s = s' := by simpa using congrArg Prod.fst hpair
  have ht : t = t' := by simpa using congrArg Prod.snd hpair
  subst s'
  subst t'
  have hsphase : s.phase = .top := hp
  have htop : LegalClause .top s t b := by
    cases c with
    | bot => simp [LegalClause, hsphase] at hc
    | mid => simp [LegalClause, hsphase] at hc
    | terminal => simp [LegalClause, hsphase] at hc
    | tail => simp [LegalClause, hsphase] at hc
    | preTop => simp [LegalClause, hsphase] at hc
    | top => exact hc
  exact ⟨htop, top_forces_cap htop⟩

end PakFixedPolyomino.ConcretePakScanner
