import PakFixedPolyomino.ULogConcreteMachine
import PakFixedPolyomino.ULogAutomaticSemanticHalt
import PakFixedPolyomino.ULogScheduledContinuation
import PakFixedPolyomino.ULogMultiCycleRefinement

/-!
# First-hit concrete traces

`BranchedReaches` is deliberately convenient for forward simulation, but its
unlabelled prefix and suffix are arbitrary `Reaches` witnesses.  In
particular, a slot-zero cycle can be absorbed into the prefix and a later
`chooseSlot` state can be presented as the choice belonging to the current
label.  That relation is therefore too permissive for a converse or a path
count.

This file records the stricter concrete notion needed by such a converse.  A
cycle consists of the *first* valid slot-zero run to `chooseSlot`, one genuine
successor of `concreteMachine` with the advertised slot, and the *first* valid
slot-zero run to either the next `cycleStart` boundary or a halted result.
The first-hit decomposition is deterministic and hence unique.  The
definitions below are entirely concrete: their codomain is not restricted by
semantic membership.
-/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

/-- A concrete configuration at which the binary slot is selected. -/
def IsConcreteChoice : Result → Prop
  | .running .chooseSlot _ => True
  | _ => False

/-- The distinguished boundary between two simulated semantic cycles. -/
def IsConcreteCycleBoundary : Result → Prop
  | .running .cycleStart _ => True
  | _ => False

/-- A cycle ends at the next cycle boundary or at its first concrete terminal. -/
def IsConcreteCycleStop (r : Result) : Prop :=
  IsConcreteCycleBoundary r ∨ concreteHalted r = true

/-- A run of exactly `n` genuine slot-zero edges of `concreteMachine`.

Unlike `Reaches`, a missing transition is not silently replaced by the
absorbing auxiliary result `.stuck`: every edge is witnessed by
`validStepAt`. -/
inductive ValidZeroRun : ℕ → Result → Result → Prop
  | nil (r : Result) : ValidZeroRun 0 r r
  | cons (r next finish : Result) (n : ℕ)
      (head : validStepAt 0 r = some next)
      (tail : ValidZeroRun n next finish) :
      ValidZeroRun (n + 1) r finish

theorem validStepAt_zero_some_eq_oneStep
    {r next : Result} (h : validStepAt 0 r = some next) :
    oneStep r = next := by
  rw [oneStep_eq_slot_zero]
  exact validStepAt_some_eq_oneStepAt h

theorem ValidZeroRun.eq_run
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) : run n start = finish := by
  induction h with
  | nil r => rfl
  | cons r next finish n hhead htail ih =>
      simp only [run]
      rw [validStepAt_zero_some_eq_oneStep hhead]
      exact ih

theorem ValidZeroRun.toReaches
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) : Reaches start finish :=
  ⟨n, h.eq_run⟩

theorem ValidZeroRun.finish_unique
    {n : ℕ} {start finish₁ finish₂ : Result}
    (h₁ : ValidZeroRun n start finish₁)
    (h₂ : ValidZeroRun n start finish₂) : finish₁ = finish₂ := by
  rw [← h₁.eq_run, ← h₂.eq_run]

/-- Every initial segment of a genuine zero-run is itself genuine. -/
theorem ValidZeroRun.prefix
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) {k : ℕ} (hk : k ≤ n) :
    ValidZeroRun k start (run k start) := by
  induction h generalizing k with
  | nil r =>
      have hkzero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact .nil r
  | cons r next finish n hhead htail ih =>
      cases k with
      | zero => exact .nil r
      | succ k =>
          have hk' : k ≤ n := by omega
          have hprefix := ih hk'
          have hrun : run (k + 1) r = run k next := by
            simp only [run]
            rw [validStepAt_zero_some_eq_oneStep hhead]
          rw [hrun]
          exact .cons r next (run k next) k hhead hprefix

theorem ValidZeroRun.append
    {a b : ℕ} {start middle finish : Result}
    (h₁ : ValidZeroRun a start middle)
    (h₂ : ValidZeroRun b middle finish) :
    ValidZeroRun (a + b) start finish := by
  induction h₁ with
  | nil => simpa using h₂
  | cons r next middle n hhead htail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ValidZeroRun.cons r next finish (n + b) hhead (ih h₂))

/-- A first hit of `stop` along genuine slot-zero machine edges. -/
structure FirstValidZeroHit (stop : Result → Prop)
    (start finish : Result) : Type where
  steps : ℕ
  valid : ValidZeroRun steps start finish
  hit : stop finish
  before : ∀ m, m < steps → ¬ stop (run m start)

/-- A compositional prefix certificate used to assemble program phases before
the first choice. -/
structure ChoiceFreeValidZeroRun (n : ℕ)
    (start finish : Result) : Type where
  valid : ValidZeroRun n start finish
  choice_free : ∀ m, m < n → ¬ IsConcreteChoice (run m start)

def ChoiceFreeValidZeroRun.toFirstHit
    {n : ℕ} {start finish : Result}
    (h : ChoiceFreeValidZeroRun n start finish)
    (hfinish : IsConcreteChoice finish) :
    FirstValidZeroHit IsConcreteChoice start finish where
  steps := n
  valid := h.valid
  hit := hfinish
  before := h.choice_free

def ChoiceFreeValidZeroRun.one
    {start finish : Result}
    (hstep : validStepAt 0 start = some finish)
    (hstart : ¬ IsConcreteChoice start) :
    ChoiceFreeValidZeroRun 1 start finish where
  valid := .cons start finish finish 0 hstep (.nil finish)
  choice_free := by
    intro m hm
    have hmzero : m = 0 := by omega
    subst m
    simpa only [run] using hstart

def ChoiceFreeValidZeroRun.append
    {a b : ℕ} {start middle finish : Result}
    (h₁ : ChoiceFreeValidZeroRun a start middle)
    (h₂ : ChoiceFreeValidZeroRun b middle finish) :
    ChoiceFreeValidZeroRun (a + b) start finish where
  valid := h₁.valid.append h₂.valid
  choice_free := by
    intro m hm
    by_cases hma : m < a
    · exact h₁.choice_free m hma
    · have ham : a ≤ m := Nat.le_of_not_gt hma
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ham
      have hkb : k < b := by omega
      rw [run_add, h₁.valid.eq_run]
      exact h₂.choice_free k hkb

/-- A genuine deterministic segment with no earlier cycle boundary or
terminal. -/
structure StopFreeValidZeroRun (n : ℕ)
    (start finish : Result) : Type where
  valid : ValidZeroRun n start finish
  stop_free : ∀ m, m < n → ¬ IsConcreteCycleStop (run m start)

def StopFreeValidZeroRun.toFirstHit
    {n : ℕ} {start finish : Result}
    (h : StopFreeValidZeroRun n start finish)
    (hfinish : IsConcreteCycleStop finish) :
    FirstValidZeroHit IsConcreteCycleStop start finish where
  steps := n
  valid := h.valid
  hit := hfinish
  before := h.stop_free

def StopFreeValidZeroRun.one
    {start finish : Result}
    (hstep : validStepAt 0 start = some finish)
    (hstart : ¬ IsConcreteCycleStop start) :
    StopFreeValidZeroRun 1 start finish where
  valid := .cons start finish finish 0 hstep (.nil finish)
  stop_free := by
    intro m hm
    have hmzero : m = 0 := by omega
    subst m
    simpa only [run] using hstart

def StopFreeValidZeroRun.append
    {a b : ℕ} {start middle finish : Result}
    (h₁ : StopFreeValidZeroRun a start middle)
    (h₂ : StopFreeValidZeroRun b middle finish) :
    StopFreeValidZeroRun (a + b) start finish where
  valid := h₁.valid.append h₂.valid
  stop_free := by
    intro m hm
    by_cases hma : m < a
    · exact h₁.stop_free m hma
    · have ham : a ≤ m := Nat.le_of_not_gt hma
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ham
      have hkb : k < b := by omega
      rw [run_add, h₁.valid.eq_run]
      exact h₂.stop_free k hkb

/-- A genuine finite run ending in `stop` has a canonical earliest stopped
prefix.  This is the existence companion to first-hit uniqueness. -/
noncomputable def ValidZeroRun.firstHit
    {stop : Result → Prop} [DecidablePred stop]
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) (hstop : stop finish) :
    FirstValidZeroHit stop start (run (Nat.find
      (show ∃ m, stop (run m start) from
        ⟨n, by rw [h.eq_run]; exact hstop⟩)) start) := by
  classical
  let hex : ∃ m, stop (run m start) :=
    ⟨n, by rw [h.eq_run]; exact hstop⟩
  let k := Nat.find hex
  have hk : k ≤ n := Nat.find_min' hex (by
    rw [h.eq_run]
    exact hstop)
  exact
    { steps := k
      valid := h.prefix hk
      hit := Nat.find_spec hex
      before := fun m hm => Nat.find_min hex hm }

theorem FirstValidZeroHit.exists_of_validZeroRun
    {stop : Result → Prop} [DecidablePred stop]
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) (hstop : stop finish) :
    Nonempty (Σ first, FirstValidZeroHit stop start first) := by
  classical
  exact ⟨⟨run (Nat.find
    (show ∃ m, stop (run m start) from
      ⟨n, by rw [h.eq_run]; exact hstop⟩)) start,
    h.firstHit hstop⟩⟩

theorem FirstValidZeroHit.toReaches
    {stop : Result → Prop} {start finish : Result}
    (h : FirstValidZeroHit stop start finish) : Reaches start finish :=
  h.valid.toReaches

theorem FirstValidZeroHit.steps_le
    {stop : Result → Prop} {start finish₁ finish₂ : Result}
    (h₁ : FirstValidZeroHit stop start finish₁)
    (h₂ : FirstValidZeroHit stop start finish₂) :
    h₁.steps ≤ h₂.steps := by
  by_contra hnot
  have hlt : h₂.steps < h₁.steps := Nat.lt_of_not_ge hnot
  exact h₁.before h₂.steps hlt (by
    rw [h₂.valid.eq_run]
    exact h₂.hit)

/-- A deterministic run has at most one first hit of a predicate. -/
theorem FirstValidZeroHit.steps_eq
    {stop : Result → Prop} {start finish₁ finish₂ : Result}
    (h₁ : FirstValidZeroHit stop start finish₁)
    (h₂ : FirstValidZeroHit stop start finish₂) :
    h₁.steps = h₂.steps :=
  Nat.le_antisymm (h₁.steps_le h₂) (h₂.steps_le h₁)

theorem FirstValidZeroHit.finish_unique
    {stop : Result → Prop} {start finish₁ finish₂ : Result}
    (h₁ : FirstValidZeroHit stop start finish₁)
    (h₂ : FirstValidZeroHit stop start finish₂) :
    finish₁ = finish₂ := by
  have hn := h₁.steps_eq h₂
  rw [← h₁.valid.eq_run, ← h₂.valid.eq_run, hn]

@[simp] theorem run_accepted (n : ℕ) (z : Zipper Tape) :
    run n (.accepted z) = .accepted z := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, oneStep] using ih

@[simp] theorem run_rejected (n : ℕ) : run n .rejected = .rejected := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, oneStep] using ih

@[simp] theorem run_stuck (n : ℕ) : run n .stuck = .stuck := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, oneStep] using ih

/-- If a deterministic step remains running, it is necessarily a genuine
slot-zero edge of `concreteMachine`. -/
theorem validStepAt_zero_of_oneStep_running
    {start : Result} {q : State} {z : Zipper Tape}
    (h : oneStep start = .running q z) :
    validStepAt 0 start = some (.running q z) := by
  cases start with
  | running q₀ z₀ =>
      cases hrule : program.rule q₀ z₀.focus 0 with
      | none => simp [oneStep, hrule] at h
      | some action =>
          have hvalid : validStepAt 0 (.running q₀ z₀) =
              some (oneStepAt 0 (.running q₀ z₀)) := by
            simp [validStepAt, hrule]
          rw [hvalid, ← oneStep_eq_slot_zero, h]
  | accepted z₀ => simp [oneStep] at h
  | rejected => simp [oneStep] at h
  | stuck => simp [oneStep] at h

theorem validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
    {start : Result} (hhalt : concreteHalted start = false)
    (hnext : oneStep start ≠ .stuck) :
    validStepAt 0 start = some (oneStep start) := by
  cases start with
  | running q z =>
      cases hrule : program.rule q z.focus 0 with
      | none =>
          exfalso
          apply hnext
          simp [oneStep, hrule]
      | some action =>
          have hvalid : validStepAt 0 (.running q z) =
              some (oneStepAt 0 (.running q z)) := by
            simp [validStepAt, hrule]
          simpa only [oneStep_eq_slot_zero] using hvalid
  | accepted z => simp [concreteHalted] at hhalt
  | rejected => simp [concreteHalted] at hhalt
  | stuck => simp [concreteHalted] at hhalt

/-- Before a non-stuck endpoint, a run with no earlier halted state is a path
of genuine machine edges.  This removes padded terminal iterations from the
legacy `Reaches` representation. -/
theorem validZeroRun_of_run_eq_of_not_halted_before
    {n : ℕ} {start finish : Result}
    (hend : run n start = finish) (hfinish : finish ≠ .stuck)
    (hbefore : ∀ m, m < n → concreteHalted (run m start) = false) :
    ValidZeroRun n start finish := by
  induction n generalizing start with
  | zero =>
      simp only [run] at hend
      subst finish
      exact .nil start
  | succ n ih =>
      have hstart : concreteHalted start = false := by
        simpa only [run] using hbefore 0 (by omega)
      have htail : run n (oneStep start) = finish := by
        simpa only [run] using hend
      have hnext : oneStep start ≠ .stuck := by
        intro hstuck
        rw [hstuck, run_stuck] at htail
        exact hfinish htail.symm
      have hvalid :=
        validStepAt_zero_of_not_halted_of_oneStep_ne_stuck hstart hnext
      have hbeforeTail : ∀ m, m < n →
          concreteHalted (run m (oneStep start)) = false := by
        intro m hm
        have horiginal := hbefore (m + 1) (by omega)
        simpa only [run] using horiginal
      exact .cons start (oneStep start) finish n hvalid
        (ih htail hbeforeTail)

def StopFreeValidZeroRun.oneOfStep
    {start finish : Result}
    (hstep : oneStep start = finish)
    (hhalt : concreteHalted start = false)
    (hfinish : finish ≠ .stuck)
    (hstart : ¬ IsConcreteCycleStop start) :
    StopFreeValidZeroRun 1 start finish := by
  apply StopFreeValidZeroRun.one
  · have hv := validStepAt_zero_of_not_halted_of_oneStep_ne_stuck hhalt
      (by rw [hstep]; exact hfinish)
    exact hv.trans (congrArg some hstep)
  · exact hstart

/-! One-step choice-free certificates for every phase of the clock prefix.
They are the compositional atoms for the arbitrary payload/zero-count proof. -/

def choiceFree_cycleStart_head_step
    (head : Tape) (hhead : choiceHead head = true)
    (left : List Tape) (next : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .cycleStart ⟨left, head, next :: right⟩)
      (.running .clockSeek ⟨head :: left, next, right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (cycleStart_head_step head hhead left next right))
    (by simp [IsConcreteChoice])

def choiceFree_clockSeek_payloadCell_step
    (cell : Tape) (hcell : PayloadCell cell)
    (left : List Tape) (next : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockSeek ⟨left, cell, next :: right⟩)
      (.running .clockSeek ⟨cell :: left, next, right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockSeek_payloadCell_step cell hcell left next right))
    (by simp [IsConcreteChoice])

def choiceFree_clockSeek_zero_step
    (left : List Tape) (next : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockSeek ⟨left, ulogCore clockZero, next :: right⟩)
      (.running .clockConsume
        ⟨ulogCore clockOne :: left, next, right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockSeek_zero_step left next right))
    (by simp [IsConcreteChoice])

def choiceFree_clockSeek_one_step
    (left : List Tape) (head : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockSeek ⟨head :: left, ulogCore clockOne, right⟩)
      (.running .clockReturn
        ⟨left, head, ulogCore clockZero :: right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockSeek_one_step left head right))
    (by simp [IsConcreteChoice])

def choiceFree_clockConsume_zero_step
    (left : List Tape) (next : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockConsume
        ⟨left, ulogCore clockZero, next :: right⟩)
      (.running .clockConsume
        ⟨ulogCore clockOne :: left, next, right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockConsume_zero_step left next right))
    (by simp [IsConcreteChoice])

def choiceFree_clockConsume_one_step
    (left : List Tape) (head : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockConsume
        ⟨head :: left, ulogCore clockOne, right⟩)
      (.running .clockReturn
        ⟨left, head, ulogCore clockZero :: right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockConsume_one_step left head right))
    (by simp [IsConcreteChoice])

def choiceFree_clockReturn_payloadCell_step
    (cell : Tape) (hcell : PayloadCell cell)
    (left : List Tape) (head : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockReturn ⟨head :: left, cell, right⟩)
      (.running .clockReturn ⟨left, head, cell :: right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockReturn_payloadCell_step cell hcell left head right))
    (by simp [IsConcreteChoice])

def choiceFree_clockReturn_head_step
    (head : Tape) (hhead : choiceHead head = true)
    (left right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockReturn ⟨left, head, right⟩)
      (.running .chooseSlot ⟨left, head, right⟩) :=
  ChoiceFreeValidZeroRun.one
    (validStepAt_zero_of_oneStep_running
      (clockReturn_head_step head hhead left right))
    (by simp [IsConcreteChoice])

/-- An arbitrary safe payload scan stays in `clockSeek`, hence is
choice-free. -/
def choiceFree_clockSeek_payloadPath
    (path : List Tape) (hsafe : PayloadPathSafe path)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun path.length
      (.running .clockSeek (beforeRightPath path left terminal right))
      (.running .clockSeek (afterRightPath path left terminal right)) := by
  induction path generalizing left with
  | nil =>
      exact
        { valid := .nil _
          choice_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx : PayloadCell x := hsafe x (by simp)
      have hxs : PayloadPathSafe xs := by
        intro cell hcell
        exact hsafe cell (by simp [hcell])
      cases xs with
      | nil =>
          simpa [beforeRightPath, afterRightPath] using
            choiceFree_clockSeek_payloadCell_step x hx left terminal right
      | cons y ys =>
          have hfirst := choiceFree_clockSeek_payloadCell_step x hx left y
            (ys ++ terminal :: right)
          have hrest := ih hxs (x :: left)
          have hall := hfirst.append hrest
          simpa [beforeRightPath, afterRightPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- The matching safe return scan stays in `clockReturn`, hence is
choice-free. -/
def choiceFree_clockReturn_payloadPath
    (path : List Tape) (hsafe : PayloadPathSafe path)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun path.length
      (.running .clockReturn (beforeLeftPath path left terminal right))
      (.running .clockReturn (afterLeftPath path left terminal right)) := by
  induction path generalizing right with
  | nil =>
      exact
        { valid := .nil _
          choice_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx : PayloadCell x := hsafe x (by simp)
      have hxs : PayloadPathSafe xs := by
        intro cell hcell
        exact hsafe cell (by simp [hcell])
      cases xs with
      | nil =>
          simpa [beforeLeftPath, afterLeftPath] using
            choiceFree_clockReturn_payloadCell_step x hx left terminal right
      | cons y ys =>
          have hfirst := choiceFree_clockReturn_payloadCell_step x hx
            (ys ++ terminal :: left) y right
          have hrest := ih hxs (x :: right)
          have hall := hfirst.append hrest
          simpa [beforeLeftPath, afterLeftPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- The unary carry portion of clock consumption contains only non-choice
control states. -/
def choiceFree_clockConsume_zeros
    (n : ℕ) (left suffix : List Tape) :
    ChoiceFreeValidZeroRun n
      (.running .clockConsume (beforeConsumeZeros n left suffix))
      (.running .clockConsume (afterConsumeZeros n left suffix)) := by
  induction n generalizing left with
  | zero =>
      exact
        { valid := .nil _
          choice_free := by intro m hm; simp at hm }
  | succ n ih =>
      have hfirst : ChoiceFreeValidZeroRun 1
          (.running .clockConsume (beforeConsumeZeros (n + 1) left suffix))
          (.running .clockConsume
            (beforeConsumeZeros n (ulogCore clockOne :: left) suffix)) := by
        cases n with
        | zero =>
          simpa [beforeConsumeZeros] using
            choiceFree_clockConsume_zero_step left (ulogCore clockOne)
              suffix
        | succ n =>
          simpa [beforeConsumeZeros, List.replicate_succ,
            List.append_assoc] using
            choiceFree_clockConsume_zero_step left (ulogCore clockZero)
              (List.replicate n (ulogCore clockZero) ++
                ulogCore clockOne :: suffix)
      have hrest := ih (ulogCore clockOne :: left)
      have hall := hfirst.append hrest
      simpa [afterConsumeZeros, List.replicate_succ', List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def ClockReturnCell (cell : Tape) : Prop :=
  cell = ulogCore clockOne ∨ PayloadCell cell

def ClockReturnPathSafe (path : List Tape) : Prop :=
  ∀ cell ∈ path, ClockReturnCell cell

theorem choiceFree_clockReturnCell_step_nonempty
    (cell : Tape) (hcell : ClockReturnCell cell)
    (left : List Tape) (head : Tape) (right : List Tape) :
    Nonempty (ChoiceFreeValidZeroRun 1
      (.running .clockReturn ⟨head :: left, cell, right⟩)
      (.running .clockReturn ⟨left, head, cell :: right⟩)) := by
  rcases hcell with rfl | hpayload
  · exact ⟨ChoiceFreeValidZeroRun.one
      (validStepAt_zero_of_oneStep_running
        (clockReturn_clock_step true left head right))
      (by simp [IsConcreteChoice])⟩
  · exact ⟨choiceFree_clockReturn_payloadCell_step cell hpayload
      left head right⟩

noncomputable def choiceFree_clockReturnCell_step
    (cell : Tape) (hcell : ClockReturnCell cell)
    (left : List Tape) (head : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun 1
      (.running .clockReturn ⟨head :: left, cell, right⟩)
      (.running .clockReturn ⟨left, head, cell :: right⟩) :=
  Classical.choice
    (choiceFree_clockReturnCell_step_nonempty cell hcell left head right)

noncomputable def choiceFree_clockReturnPath
    (path : List Tape) (hsafe : ClockReturnPathSafe path)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    ChoiceFreeValidZeroRun path.length
      (.running .clockReturn (beforeLeftPath path left terminal right))
      (.running .clockReturn (afterLeftPath path left terminal right)) := by
  induction path generalizing right with
  | nil =>
      exact
        { valid := .nil _
          choice_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx : ClockReturnCell x := hsafe x (by simp)
      have hxs : ClockReturnPathSafe xs := by
        intro cell hcell
        exact hsafe cell (by simp [hcell])
      cases xs with
      | nil =>
          simpa [beforeLeftPath, afterLeftPath] using
            choiceFree_clockReturnCell_step x hx left terminal right
      | cons y ys =>
          have hfirst := choiceFree_clockReturnCell_step x hx
            (ys ++ terminal :: left) y right
          have hrest := ih hxs (x :: right)
          have hall := hfirst.append hrest
          simpa [beforeLeftPath, afterLeftPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem runtimeClockReturnPath_safe
    (k : ℕ) (payloadPath : List Tape)
    (hsafe : PayloadPathSafe payloadPath) :
    ClockReturnPathSafe (runtimeClockReturnPath k payloadPath) := by
  intro cell hcell
  simp only [runtimeClockReturnPath, List.mem_append, List.mem_replicate,
    List.mem_reverse] at hcell
  rcases hcell with hclock | hpayload
  · exact Or.inl hclock.2
  · exact Or.inr (hsafe cell hpayload)

/-- Any `Reaches` witness whose endpoint is still running consists entirely
of genuine slot-zero machine edges; an absorbing terminal cannot occur in its
prefix. -/
theorem validZeroRun_of_run_eq_running
    {n : ℕ} {start : Result} {q : State} {z : Zipper Tape}
    (h : run n start = .running q z) :
    ValidZeroRun n start (.running q z) := by
  induction n generalizing start with
  | zero =>
      simp only [run] at h
      subst start
      exact .nil _
  | succ n ih =>
      have htail : run n (oneStep start) = .running q z := by
        simpa only [run] using h
      cases hnext : oneStep start with
      | running q₁ z₁ =>
          have hvalid : validStepAt 0 start = some (.running q₁ z₁) :=
            validStepAt_zero_of_oneStep_running hnext
          have hrest : ValidZeroRun n (.running q₁ z₁)
              (.running q z) := ih (by simpa [hnext] using htail)
          exact .cons start (.running q₁ z₁) (.running q z) n
            hvalid hrest
      | accepted z₁ => simp [hnext] at htail
      | rejected => simp [hnext] at htail
      | stuck => simp [hnext] at htail

/-- A reachability proof to `chooseSlot`, together with the genuinely missing
control-flow fact that no earlier iterate is a choice, supplies first-hit
data. -/
theorem firstChoice_of_reaches
    {start : Result} {z : Zipper Tape}
    (h : Reaches start (.running .chooseSlot z))
    (hbefore : ∀ n, run n start = .running .chooseSlot z →
      ∀ m, m < n → ¬ IsConcreteChoice (run m start)) :
    Nonempty (FirstValidZeroHit IsConcreteChoice start
      (.running .chooseSlot z)) := by
  rcases h with ⟨n, hn⟩
  exact ⟨
    { steps := n
      valid := validZeroRun_of_run_eq_running hn
      hit := by simp [IsConcreteChoice]
      before := hbefore n hn }⟩

/-- A non-stuck cycle endpoint with no earlier boundary or terminal yields the
corresponding first-stop certificate. -/
theorem firstCycleStop_of_reaches
    {start finish : Result} (h : Reaches start finish)
    (hstop : IsConcreteCycleStop finish) (hfinish : finish ≠ .stuck)
    (hbefore : ∀ n, run n start = finish →
      ∀ m, m < n → ¬ IsConcreteCycleStop (run m start)) :
    Nonempty (FirstValidZeroHit IsConcreteCycleStop start finish) := by
  rcases h with ⟨n, hn⟩
  have hnotHalted : ∀ m, m < n →
      concreteHalted (run m start) = false := by
    intro m hm
    have hnot := hbefore n hn m hm
    cases hvalue : concreteHalted (run m start) with
    | false => rfl
    | true => exact (hnot (Or.inr hvalue)).elim
  exact ⟨
    { steps := n
      valid := validZeroRun_of_run_eq_of_not_halted_before hn hfinish hnotHalted
      hit := hstop
      before := hbefore n hn }⟩

/-- A label-preserving path of genuine edges of the explicit concrete
machine. -/
inductive ConcreteMicroPath : Result → List (Fin 2) → Result → Prop
  | nil (r : Result) : ConcreteMicroPath r [] r
  | cons (start next finish : Result) (slot : Fin 2)
      (slots : List (Fin 2))
      (head : validStepAt slot start = some next)
      (tail : ConcreteMicroPath next slots finish) :
      ConcreteMicroPath start (slot :: slots) finish

theorem validStepAt_some_mem_concreteNext
    {slot : Fin 2} {start next : Result}
    (h : validStepAt slot start = some next) :
    next ∈ concreteNext start := by
  fin_cases slot
  · change validStepAt 0 start = some next at h
    cases hother : validStepAt 1 start <;> simp [concreteNext, h, hother]
  · change validStepAt 1 start = some next at h
    cases hother : validStepAt 0 start <;> simp [concreteNext, h, hother]

/-- The ordinary edge-path relation obtained from `concreteMachine.next`. -/
inductive ConcreteMachinePath : Result → List Result → Result → Prop
  | nil (r : Result) : ConcreteMachinePath r [] r
  | cons (start next finish : Result) (states : List Result)
      (head : next ∈ concreteNext start)
      (tail : ConcreteMachinePath next states finish) :
      ConcreteMachinePath start (next :: states) finish

theorem ConcreteMicroPath.toMachinePath
    {start finish : Result} {slots : List (Fin 2)}
    (h : ConcreteMicroPath start slots finish) :
    ∃ states, ConcreteMachinePath start states finish ∧
      states.length = slots.length := by
  induction h with
  | nil r => exact ⟨[], .nil r, rfl⟩
  | cons start next finish slot slots hhead htail ih =>
      obtain ⟨states, hstates, hlength⟩ := ih
      exact ⟨next :: states,
        .cons start next finish states
          (validStepAt_some_mem_concreteNext hhead) hstates,
        by simp [hlength]⟩

theorem ConcreteMicroPath.append
    {a b c : Result} {xs ys : List (Fin 2)}
    (h₁ : ConcreteMicroPath a xs b)
    (h₂ : ConcreteMicroPath b ys c) :
    ConcreteMicroPath a (xs ++ ys) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons start next finish slot slots hhead htail ih =>
      exact .cons start next c slot (slots ++ ys) hhead (ih h₂)

theorem ConcreteMachinePath.append
    {a b c : Result} {xs ys : List Result}
    (h₁ : ConcreteMachinePath a xs b)
    (h₂ : ConcreteMachinePath b ys c) :
    ConcreteMachinePath a (xs ++ ys) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons start next finish states hhead htail ih =>
      exact .cons start next c (states ++ ys) hhead (ih h₂)

theorem ValidZeroRun.toMicroPath
    {n : ℕ} {start finish : Result}
    (h : ValidZeroRun n start finish) :
    ConcreteMicroPath start (List.replicate n (0 : Fin 2)) finish := by
  induction h with
  | nil r => exact .nil r
  | cons r next finish n hhead htail ih =>
      rw [List.replicate_succ]
      exact .cons r next finish 0 (List.replicate n 0) hhead ih

/-- One exact, first-hit simulated cycle.  The advertised branch is an actual
edge of `concreteMachine`, not merely an application of `oneStepAt`. -/
structure ExactConcreteCycle (slot : Bool) (start finish : Result) : Type where
  choice : Result
  branch : Result
  choicePrefix : FirstValidZeroHit IsConcreteChoice start choice
  selected : validStepAt (ULogBytecode.slotIndex slot) choice = some branch
  cycleSuffix : FirstValidZeroHit IsConcreteCycleStop branch finish

theorem ExactConcreteCycle.prefix_no_hidden_choice
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish)
    {m : ℕ} (hm : m < h.choicePrefix.steps) :
    ¬ IsConcreteChoice (run m start) :=
  h.choicePrefix.before m hm

theorem ExactConcreteCycle.suffix_no_hidden_boundary_or_terminal
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish)
    {m : ℕ} (hm : m < h.cycleSuffix.steps) :
    ¬ IsConcreteCycleStop (run m h.branch) :=
  h.cycleSuffix.before m hm

theorem ExactConcreteCycle.toBranchedReaches
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish) :
    BranchedReaches slot start finish :=
  ⟨h.choice, h.branch, h.choicePrefix.toReaches,
    validStepAt_some_eq_oneStepAt h.selected, h.cycleSuffix.toReaches⟩

theorem ExactConcreteCycle.toMicroPath
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish) :
    ConcreteMicroPath start
      (List.replicate h.choicePrefix.steps (0 : Fin 2) ++
        ULogBytecode.slotIndex slot ::
          List.replicate h.cycleSuffix.steps (0 : Fin 2)) finish := by
  exact h.choicePrefix.valid.toMicroPath.append
    (.cons h.choice h.branch finish (ULogBytecode.slotIndex slot)
      (List.replicate h.cycleSuffix.steps 0) h.selected
      h.cycleSuffix.valid.toMicroPath)

theorem ExactConcreteCycle.toMachinePath
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish) :
    ∃ states, ConcreteMachinePath start states finish := by
  obtain ⟨states, hstates, _⟩ := h.toMicroPath.toMachinePath
  exact ⟨states, hstates⟩

/-- At the well-formed choice head used by semantic frames, the selected edge
required by an exact cycle is supplied directly by `validStepAt_chooseSlot`. -/
def exactConcreteCycleOfChoiceHead
    {slot : Bool} {start finish : Result}
    (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true)
    (choicePrefix : FirstValidZeroHit IsConcreteChoice start
      (.running .chooseSlot ⟨left, head, right⟩))
    (cycleSuffix : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨left, head, right⟩)) finish) :
    ExactConcreteCycle slot start finish where
  choice := .running .chooseSlot ⟨left, head, right⟩
  branch := oneStepAt (ULogBytecode.slotIndex slot)
    (.running .chooseSlot ⟨left, head, right⟩)
  choicePrefix := choicePrefix
  selected := validStepAt_chooseSlot slot left head right hhead
  cycleSuffix := cycleSuffix

/-- Assemble an exact cycle directly from a first choice and a concrete
stop-free suffix.  This deliberately does not pass through `Reaches`: the
suffix's validity and no-earlier-stop proof are retained in the resulting
first-hit certificate. -/
def exactConcreteCycleOfChoiceHeadStopFree
    {slot : Bool} {start finish : Result}
    (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true)
    (choicePrefix : FirstValidZeroHit IsConcreteChoice start
      (.running .chooseSlot ⟨left, head, right⟩))
    {n : ℕ}
    (suffix : StopFreeValidZeroRun n
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨left, head, right⟩)) finish)
    (hfinish : IsConcreteCycleStop finish) :
    ExactConcreteCycle slot start finish :=
  exactConcreteCycleOfChoiceHead left head right hhead choicePrefix
    (suffix.toFirstHit hfinish)

/-- Concatenate the three deterministic suffix pieces occurring after a
choice edge: dynamic cursor return, certified mismatch-prefix scan, and the
matched-rule continuation.  Keeping this as a stop-free run is what prevents
the legacy `BranchedReaches` prefix/suffix loophole from reappearing in the
resource-indexed construction. -/
def exactConcreteCycleOfCursorSuffix
    {slot : Bool} {start finish branch cursorStart matchedStart : Result}
    (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true)
    (choicePrefix : FirstValidZeroHit IsConcreteChoice start
      (.running .chooseSlot ⟨left, head, right⟩))
    (hbranch : oneStepAt (ULogBytecode.slotIndex slot)
      (.running .chooseSlot ⟨left, head, right⟩) = branch)
    {a b d : ℕ}
    (dynamic : StopFreeValidZeroRun a branch cursorStart)
    (mismatches : StopFreeValidZeroRun b cursorStart matchedStart)
    (matchedSuffix : StopFreeValidZeroRun d matchedStart finish)
    (hfinish : IsConcreteCycleStop finish) :
    ExactConcreteCycle slot start finish := by
  have htail : StopFreeValidZeroRun (a + b + d) branch finish := by
    exact (dynamic.append mismatches).append matchedSuffix
  rw [← hbranch] at htail
  exact exactConcreteCycleOfChoiceHeadStopFree left head right hhead
    choicePrefix htail hfinish

/-- Upgrade the canonical pieces used in the existing cycle proofs.  The two
`before` premises are program-specific control-flow obligations; all other
parts, including validity of the selected nondeterministic edge, are derived
here. -/
theorem exactConcreteCycle_of_canonical_parts
    {slot : Bool} {start branch finish : Result}
    (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true)
    (hprefix : Reaches start
      (.running .chooseSlot ⟨left, head, right⟩))
    (hprefixBefore : ∀ n,
      run n start = .running .chooseSlot ⟨left, head, right⟩ →
        ∀ m, m < n → ¬ IsConcreteChoice (run m start))
    (hbranch : oneStepAt (ULogBytecode.slotIndex slot)
      (.running .chooseSlot ⟨left, head, right⟩) = branch)
    (hsuffix : Reaches branch finish)
    (hstop : IsConcreteCycleStop finish) (hfinish : finish ≠ .stuck)
    (hsuffixBefore : ∀ n, run n branch = finish →
      ∀ m, m < n → ¬ IsConcreteCycleStop (run m branch)) :
    Nonempty (ExactConcreteCycle slot start finish) := by
  obtain ⟨choicePrefix⟩ :=
    firstChoice_of_reaches hprefix hprefixBefore
  obtain ⟨cycleSuffix⟩ :=
    firstCycleStop_of_reaches hsuffix hstop hfinish hsuffixBefore
  have cycleSuffix' : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨left, head, right⟩)) finish := by
    simpa [hbranch] using cycleSuffix
  exact ⟨exactConcreteCycleOfChoiceHead left head right hhead
    choicePrefix cycleSuffix'⟩

theorem exactConcreteAcceptingCycle_of_canonical_parts
    {slot : Bool} {start branch : Result} (acceptedTape : Zipper Tape)
    (left : List Tape) (head : Tape) (right : List Tape)
    (hhead : choiceHead head = true)
    (hprefix : Reaches start
      (.running .chooseSlot ⟨left, head, right⟩))
    (hprefixBefore : ∀ n,
      run n start = .running .chooseSlot ⟨left, head, right⟩ →
        ∀ m, m < n → ¬ IsConcreteChoice (run m start))
    (hbranch : oneStepAt (ULogBytecode.slotIndex slot)
      (.running .chooseSlot ⟨left, head, right⟩) = branch)
    (hsuffix : Reaches branch (.accepted acceptedTape))
    (hsuffixBefore : ∀ n, run n branch = .accepted acceptedTape →
      ∀ m, m < n → ¬ IsConcreteCycleStop (run m branch)) :
    Nonempty (ExactConcreteCycle slot start (.accepted acceptedTape)) := by
  apply exactConcreteCycle_of_canonical_parts left head right hhead hprefix
    hprefixBefore hbranch hsuffix
  · exact Or.inr rfl
  · intro h
    cases h
  · exact hsuffixBefore

/-- The first choice, selected branch, and first cycle stop are determined by
the starting configuration and the Boolean label. -/
theorem ExactConcreteCycle.decomposition_unique
    {slot : Bool} {start finish₁ finish₂ : Result}
    (h₁ : ExactConcreteCycle slot start finish₁)
    (h₂ : ExactConcreteCycle slot start finish₂) :
    h₁.choice = h₂.choice ∧ h₁.branch = h₂.branch ∧
      finish₁ = finish₂ := by
  have hchoice : h₁.choice = h₂.choice :=
    h₁.choicePrefix.finish_unique h₂.choicePrefix
  have hbranch : h₁.branch = h₂.branch := by
    apply Option.some.inj
    rw [← h₁.selected, ← h₂.selected, hchoice]
  have hfinish : finish₁ = finish₂ := by
    have hsuffix₁ : FirstValidZeroHit IsConcreteCycleStop
        h₂.branch finish₁ := by
      simpa [hbranch] using h₁.cycleSuffix
    exact hsuffix₁.finish_unique h₂.cycleSuffix
  exact ⟨hchoice, hbranch, hfinish⟩

theorem ExactConcreteCycle.finish_unique
    {slot : Bool} {start finish₁ finish₂ : Result}
    (h₁ : ExactConcreteCycle slot start finish₁)
    (h₂ : ExactConcreteCycle slot start finish₂) :
    finish₁ = finish₂ :=
  (h₁.decomposition_unique h₂).2.2

/-- A halted result cannot begin another exact cycle.  Its deterministic run
is constant, whereas the first phase of an exact cycle must genuinely hit a
`chooseSlot` configuration. -/
theorem ExactConcreteCycle.false_of_concreteHalted_start
    {slot : Bool} {start finish : Result}
    (h : ExactConcreteCycle slot start finish)
    (hstart : concreteHalted start = true) : False := by
  have hchoice : h.choice = start := by
    rw [← h.choicePrefix.valid.eq_run]
    cases start with
    | running q z => simp [concreteHalted] at hstart
    | accepted z => simp
    | rejected => simp
    | stuck => simp
  have hhit : IsConcreteChoice start := by
    rw [← hchoice]
    exact h.choicePrefix.hit
  cases start with
  | running q z => simp [concreteHalted] at hstart
  | accepted z => simp [IsConcreteChoice] at hhit
  | rejected => simp [IsConcreteChoice] at hhit
  | stuck => simp [IsConcreteChoice] at hhit

/-- Honest strengthening of the legacy relation.  The additional arguments
are exactly the two first-hit facts and the genuine selected machine edge
that `BranchedReaches` itself forgets. -/
theorem BranchedReaches.toExactConcreteCycle
    {slot : Bool} {start finish choice branch : Result}
    (_legacy : BranchedReaches slot start finish)
    (choicePrefix : FirstValidZeroHit IsConcreteChoice start choice)
    (selected : validStepAt (ULogBytecode.slotIndex slot) choice = some branch)
    (cycleSuffix : FirstValidZeroHit IsConcreteCycleStop branch finish) :
    Nonempty (ExactConcreteCycle slot start finish) :=
  ⟨
    { choice := choice
      branch := branch
      choicePrefix := choicePrefix
      selected := selected
      cycleSuffix := cycleSuffix }⟩

/-- First-hit strengthening of the concrete clock-decrement prefix.  The
remaining hypothesis is deliberately stated as a control-state exclusion;
unlike terminal exclusion, it does not follow from reachability alone. -/
theorem reaches_clockDecrementCells_firstChoice
    (head : Tape) (hhead : choiceHead head = true)
    (k : ℕ) (payloadPath : List Tape) (hsafe : PayloadPathSafe payloadPath)
    (left suffix : List Tape)
    (hbefore : ∀ n,
      run n (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩) =
        .running .chooseSlot
          ⟨left, head,
            payloadPath ++ List.replicate k (ulogCore clockOne) ++
              ulogCore clockZero :: suffix⟩ →
      ∀ m, m < n →
        ¬ IsConcreteChoice
          (run m (.running .cycleStart
            ⟨left, head,
              payloadPath ++ List.replicate k (ulogCore clockZero) ++
                ulogCore clockOne :: suffix⟩))) :
    Nonempty (FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockOne) ++
            ulogCore clockZero :: suffix⟩)) := by
  apply firstChoice_of_reaches
  · exact reaches_clockDecrementCells head hhead k payloadPath hsafe left suffix
  · exact hbefore

/-- Base case of the concrete clock prefix, proved with its exact three
machine edges.  This is the first program-specific discharge of the
no-earlier-choice obligation (empty payload path and a zero-free binary
clock). -/
def clockDecrementCells_empty_zero_firstChoice
    (head : Tape) (hhead : choiceHead head = true)
    (left suffix : List Tape) :
    FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨left, head, ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head, ulogCore clockZero :: suffix⟩) := by
  let start : Result := .running .cycleStart
    ⟨left, head, ulogCore clockOne :: suffix⟩
  let seek : Result := .running .clockSeek
    ⟨head :: left, ulogCore clockOne, suffix⟩
  let returning : Result := .running .clockReturn
    ⟨left, head, ulogCore clockZero :: suffix⟩
  let choice : Result := .running .chooseSlot
    ⟨left, head, ulogCore clockZero :: suffix⟩
  have h₀ : oneStep start = seek := by
    simpa [start, seek] using
      cycleStart_head_step head hhead left (ulogCore clockOne) suffix
  have h₁ : oneStep seek = returning := by
    simpa [seek, returning] using clockSeek_one_step left head suffix
  have h₂ : oneStep returning = choice := by
    simpa [returning, choice] using
      clockReturn_head_step head hhead left (ulogCore clockZero :: suffix)
  have v₀ : validStepAt 0 start = some seek :=
    validStepAt_zero_of_oneStep_running h₀
  have v₁ : validStepAt 0 seek = some returning :=
    validStepAt_zero_of_oneStep_running h₁
  have v₂ : validStepAt 0 returning = some choice :=
    validStepAt_zero_of_oneStep_running h₂
  change FirstValidZeroHit IsConcreteChoice start choice
  exact
    { steps := 3
      valid := .cons start seek choice 2 v₀
        (.cons seek returning choice 1 v₁
          (.cons returning choice choice 0 v₂ (.nil choice)))
      hit := by simp [choice, IsConcreteChoice]
      before := by
        intro m hm
        interval_cases m <;>
          simp [run, h₀, h₁, start, seek, returning,
            IsConcreteChoice] }

/-- Full first-hit clock prefix for a zero-free binary clock and an arbitrary
safe payload path.  Both scans are assembled from genuine machine edges, so
the resulting choice is provably the first one. -/
def clockDecrementCells_zero_firstChoice
    (head : Tape) (hhead : choiceHead head = true)
    (payloadPath : List Tape) (hsafe : PayloadPathSafe payloadPath)
    (left suffix : List Tape) :
    FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨left, head, payloadPath ++ ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head, payloadPath ++ ulogCore clockZero :: suffix⟩) := by
  have hcycle : ChoiceFreeValidZeroRun 1
      (.running .cycleStart
        ⟨left, head, payloadPath ++ ulogCore clockOne :: suffix⟩)
      (.running .clockSeek
        (beforeRightPath payloadPath (head :: left)
          (ulogCore clockOne) suffix)) := by
    cases payloadPath with
    | nil =>
        simpa [beforeRightPath] using
          choiceFree_cycleStart_head_step head hhead left
            (ulogCore clockOne) suffix
    | cons x xs =>
        simpa [beforeRightPath, List.append_assoc] using
          choiceFree_cycleStart_head_step head hhead left x
            (xs ++ ulogCore clockOne :: suffix)
  have hscan := choiceFree_clockSeek_payloadPath payloadPath hsafe
    (head :: left) (ulogCore clockOne) suffix
  have hseekOne : ChoiceFreeValidZeroRun 1
      (.running .clockSeek
        (afterRightPath payloadPath (head :: left)
          (ulogCore clockOne) suffix))
      (.running .clockReturn
        (beforeLeftPath payloadPath.reverse left head
          (ulogCore clockZero :: suffix))) := by
    apply ChoiceFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        clockSeek_one_over_path payloadPath.reverse left head suffix
    · simp [afterRightPath, IsConcreteChoice]
  have hsafeReverse : PayloadPathSafe payloadPath.reverse := by
    intro cell hcell
    exact hsafe cell (by simpa using hcell)
  have hreturn := choiceFree_clockReturn_payloadPath payloadPath.reverse
    hsafeReverse left head (ulogCore clockZero :: suffix)
  have hheadStep : ChoiceFreeValidZeroRun 1
      (.running .clockReturn
        (afterLeftPath payloadPath.reverse left head
          (ulogCore clockZero :: suffix)))
      (.running .chooseSlot
        ⟨left, head, payloadPath ++ ulogCore clockZero :: suffix⟩) := by
    simpa [afterLeftPath, List.append_assoc] using
      choiceFree_clockReturn_head_step head hhead left
        (payloadPath ++ ulogCore clockZero :: suffix)
  have hall := (((hcycle.append hscan).append hseekOne).append hreturn).append
    hheadStep
  exact hall.toFirstHit (by simp [IsConcreteChoice])

/-- Program-specific first-hit strengthening of
`reaches_clockDecrementCells`, for every safe payload path and every unary
zero prefix of the binary clock. -/
noncomputable def clockDecrementCells_firstChoice
    (head : Tape) (hhead : choiceHead head = true)
    (k : ℕ) (payloadPath : List Tape) (hsafe : PayloadPathSafe payloadPath)
    (left suffix : List Tape) :
    FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockOne) ++
            ulogCore clockZero :: suffix⟩) := by
  cases k with
  | zero =>
      simpa using clockDecrementCells_zero_firstChoice head hhead payloadPath
        hsafe left suffix
  | succ n =>
      have hcycle : ChoiceFreeValidZeroRun 1
          (.running .cycleStart
            ⟨left, head,
              payloadPath ++ List.replicate (n + 1) (ulogCore clockZero) ++
                ulogCore clockOne :: suffix⟩)
          (.running .clockSeek
            (beforeRightPath payloadPath (head :: left)
              (ulogCore clockZero)
              (List.replicate n (ulogCore clockZero) ++
                ulogCore clockOne :: suffix))) := by
        cases payloadPath with
        | nil =>
            simpa [beforeRightPath, List.replicate_succ,
              List.append_assoc] using
              choiceFree_cycleStart_head_step head hhead left
                (ulogCore clockZero)
                (List.replicate n (ulogCore clockZero) ++
                  ulogCore clockOne :: suffix)
        | cons x xs =>
            simpa [beforeRightPath, List.replicate_succ,
              List.append_assoc] using
              choiceFree_cycleStart_head_step head hhead left x
                (xs ++ ulogCore clockZero ::
                  List.replicate n (ulogCore clockZero) ++
                    ulogCore clockOne :: suffix)
      have hscan := choiceFree_clockSeek_payloadPath payloadPath hsafe
        (head :: left) (ulogCore clockZero)
        (List.replicate n (ulogCore clockZero) ++
          ulogCore clockOne :: suffix)
      have hseekZero : ChoiceFreeValidZeroRun 1
          (.running .clockSeek
            (afterRightPath payloadPath (head :: left)
              (ulogCore clockZero)
              (List.replicate n (ulogCore clockZero) ++
                ulogCore clockOne :: suffix)))
          (.running .clockConsume
            (beforeConsumeZeros n
              (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
              suffix)) := by
        apply ChoiceFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases n with
          | zero =>
              simpa [afterRightPath, beforeConsumeZeros,
                List.append_assoc] using
                clockSeek_zero_step
                  (payloadPath.reverse ++ head :: left)
                  (ulogCore clockOne) suffix
          | succ n =>
              simpa [afterRightPath, beforeConsumeZeros,
                List.replicate_succ, List.append_assoc] using
                clockSeek_zero_step
                  (payloadPath.reverse ++ head :: left)
                  (ulogCore clockZero)
                  (List.replicate n (ulogCore clockZero) ++
                    ulogCore clockOne :: suffix)
        · simp [afterRightPath, IsConcreteChoice]
      have hconsume := choiceFree_clockConsume_zeros n
        (ulogCore clockOne :: payloadPath.reverse ++ head :: left) suffix
      have hconsumeOne : ChoiceFreeValidZeroRun 1
          (.running .clockConsume
            (afterConsumeZeros n
              (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
              suffix))
          (.running .clockReturn
            (beforeLeftPath (runtimeClockReturnPath (n + 1) payloadPath)
              left head (ulogCore clockZero :: suffix))) := by
        apply ChoiceFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [afterConsumeZeros, runtimeClockReturnPath,
            List.replicate_succ', List.append_assoc] using
            clockConsume_one_over_path
              (runtimeClockReturnPath (n + 1) payloadPath) left head suffix
        · simp [afterConsumeZeros, IsConcreteChoice]
      have hreturn := choiceFree_clockReturnPath
        (runtimeClockReturnPath (n + 1) payloadPath)
        (runtimeClockReturnPath_safe (n + 1) payloadPath hsafe)
        left head (ulogCore clockZero :: suffix)
      have hheadStep : ChoiceFreeValidZeroRun 1
          (.running .clockReturn
            (afterLeftPath (runtimeClockReturnPath (n + 1) payloadPath)
              left head (ulogCore clockZero :: suffix)))
          (.running .chooseSlot
            ⟨left, head,
              payloadPath ++ List.replicate (n + 1) (ulogCore clockOne) ++
                ulogCore clockZero :: suffix⟩) := by
        simpa [afterLeftPath, runtimeClockReturnPath_reverse,
          List.append_assoc] using
          choiceFree_clockReturn_head_step head hhead left
            (payloadPath ++ List.replicate (n + 1) (ulogCore clockOne) ++
              ulogCore clockZero :: suffix)
      have hall := (((((hcycle.append hscan).append hseekZero).append
        hconsume).append hconsumeOne).append hreturn).append hheadStep
      exact hall.toFirstHit (by simp [IsConcreteChoice])

/-- A safe target-finish corridor is traversed without reaching a cycle
boundary or any terminal. -/
def stopFree_targetFinishSeek_path
    (path : List Tape) (hsafe : TargetFinishCorridorSafe path)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path left terminal right))
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path left terminal right)) := by
  induction path generalizing left with
  | nil =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx := hsafe x (by simp)
      have hxs : TargetFinishCorridorSafe xs := by
        intro cell hcell
        exact hsafe cell (by simp [hcell])
      cases xs with
      | nil =>
          apply StopFreeValidZeroRun.one
          · apply validStepAt_zero_of_oneStep_running
            simpa [beforeRightPath, afterRightPath] using
              targetFinishSeek_pass x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
                left terminal right
          · simp [beforeRightPath, IsConcreteCycleStop,
              IsConcreteCycleBoundary, concreteHalted]
      | cons y ys =>
          have hfirst : StopFreeValidZeroRun 1
              (.running (.actionPhase .targetFinishSeek)
                (beforeRightPath (x :: y :: ys) left terminal right))
              (.running (.actionPhase .targetFinishSeek)
                (beforeRightPath (y :: ys) (x :: left) terminal right)) := by
            apply StopFreeValidZeroRun.one
            · apply validStepAt_zero_of_oneStep_running
              simpa [beforeRightPath, List.append_assoc] using
                targetFinishSeek_pass x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
                  left y (ys ++ terminal :: right)
            · simp [beforeRightPath, IsConcreteCycleStop,
                IsConcreteCycleBoundary, concreteHalted]
          have hrest := ih hxs (x :: left)
          have hall := hfirst.append hrest
          simpa [beforeRightPath, afterRightPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Exact first stop of the final target-zero rewrite: after one setup step
and a safe scan, the first stopped configuration is the accepting result. -/
def actionTargetFinishSeek_firstStop
    (path : List Tape) (hsafe : TargetFinishCorridorSafe path)
    (left : List Tape) (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (.running .actionTarget
        ⟨left, ulogCore codeOne, path ++ terminal :: right⟩)
      (.accepted
        (afterRightPath path (ulogCore targetBoundary :: left)
          terminal right)) := by
  have hsetup : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne, path ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path (ulogCore targetBoundary :: left)
          terminal right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) terminal right
  have hhaltStep : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path (ulogCore targetBoundary :: left)
          terminal right))
      (.accepted
        (afterRightPath path (ulogCore targetBoundary :: left)
          terminal right)) := by
    have hone : oneStep
        (.running (.actionPhase .targetFinishSeek)
          (afterRightPath path (ulogCore targetBoundary :: left)
            terminal right)) =
        .accepted
          (afterRightPath path (ulogCore targetBoundary :: left)
            terminal right) := by
      rcases hterminal with rfl | rfl
      · simpa [afterRightPath, List.append_assoc] using
          targetFinishSeek_shorter
            (path.reverse ++ ulogCore targetBoundary :: left) right
      · simpa [afterRightPath, List.append_assoc] using
          targetFinishSeek_one_any
            (path.reverse ++ ulogCore targetBoundary :: left) right
    apply StopFreeValidZeroRun.one
    · have hv := validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
          (start := .running (.actionPhase .targetFinishSeek)
            (afterRightPath path (ulogCore targetBoundary :: left)
              terminal right))
          (by rfl) (by rw [hone]; intro h; cases h)
      exact hv.trans (congrArg Option.some hone)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact ((hsetup.append hscan).append hhaltStep).toFirstHit (Or.inr rfl)

def targetRawZero_firstStop
    (current : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ z, FirstValidZeroHit IsConcreteCycleStop
      (targetRawStart 0 current corridor left tail) (.accepted z) := by
  cases current with
  | zero =>
      exact ⟨afterRightPath corridor (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail),
        by
          simpa [targetRawStart, List.append_assoc] using
            actionTargetFinishSeek_firstStop corridor hsafe.2 left
              (ulogCore stateOne) (Or.inr rfl) (ulogCore stateSep :: tail)⟩
  | succ current =>
      exact ⟨afterRightPath corridor (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail),
        by
          simpa [targetRawStart, List.replicate_succ,
            List.append_assoc] using
            actionTargetFinishSeek_firstStop corridor hsafe.2 left
              (ulogCore stateZero) (Or.inl rfl)
              (List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)⟩

/-- Exact first rejecting stop after a target-one rewrite has placed its
single state mark.  All setup and scan states remain nonterminal; rejection
is the first cycle stop. -/
def actionTargetFinishOneMark_firstStop
    (path : List Tape) (hsafe : TargetFinishCorridorSafe path)
    (left : List Tape) (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          path ++ ulogCore stateMark :: terminal :: right⟩)
      .rejected := by
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          path ++ ulogCore stateMark :: terminal :: right⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) (ulogCore stateMark) (terminal :: right)
  have hmark : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        (afterRightPath path (ulogCore targetBoundary :: left)
          (ulogCore stateMark) (terminal :: right)))
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left,
          terminal, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        (targetFinishSeek_mark
          (path.reverse ++ ulogCore targetBoundary :: left) terminal right)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hreject : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left,
          terminal, right⟩)
      .rejected := by
    have hone : oneStep
        (.running (.actionPhase .targetFinishSeenOne)
          ⟨ulogCore stateMark :: path.reverse ++
              ulogCore targetBoundary :: left,
            terminal, right⟩) = .rejected := by
      rcases hterminal with rfl | rfl
      · exact targetFinishSeenOne_zero_reject_core _ _
      · exact targetFinishSeenOne_one_reject_core _ _
    apply StopFreeValidZeroRun.one
    · have hv := validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
          (start := .running (.actionPhase .targetFinishSeenOne)
            ⟨ulogCore stateMark :: path.reverse ++
                ulogCore targetBoundary :: left,
              terminal, right⟩)
          (by rfl) (by rw [hone]; intro h; cases h)
      exact hv.trans (congrArg Option.some hone)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact (((hstart.append hscan).append hmark).append hreject).toFirstHit
    (Or.inr rfl)

/-- Generic stop-free right scan in a fixed non-boundary control state. -/
def stopFree_rightPath_of
    (q : State) (hq : q ≠ .cycleStart) (path : List Tape)
    (hstep : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running q ⟨left, x, y :: right⟩) =
        .running q ⟨x :: left, y, right⟩)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running q (beforeRightPath path left terminal right))
      (.running q (afterRightPath path left terminal right)) := by
  induction path generalizing left with
  | nil =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx := hstep x (by simp)
      have hxs : ∀ z, z ∈ xs → ∀ left y right,
          oneStep (.running q ⟨left, z, y :: right⟩) =
            .running q ⟨z :: left, y, right⟩ := by
        intro z hz
        exact hstep z (by simp [hz])
      cases xs with
      | nil =>
          apply StopFreeValidZeroRun.one
          · apply validStepAt_zero_of_oneStep_running
            simpa [beforeRightPath, afterRightPath] using
              hx left terminal right
          · simp [beforeRightPath, IsConcreteCycleStop,
              IsConcreteCycleBoundary, concreteHalted, hq]
      | cons y ys =>
          have hfirst : StopFreeValidZeroRun 1
              (.running q (beforeRightPath (x :: y :: ys) left terminal right))
              (.running q
                (beforeRightPath (y :: ys) (x :: left) terminal right)) := by
            apply StopFreeValidZeroRun.one
            · apply validStepAt_zero_of_oneStep_running
              simpa [beforeRightPath, List.append_assoc] using
                hx left y (ys ++ terminal :: right)
            · simp [beforeRightPath, IsConcreteCycleStop,
                IsConcreteCycleBoundary, concreteHalted, hq]
          have hrest := ih hxs (x :: left)
          have hall := hfirst.append hrest
          simpa [beforeRightPath, afterRightPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Generic stop-free left scan in a fixed non-boundary control state. -/
def stopFree_leftPath_of
    (q : State) (hq : q ≠ .cycleStart) (path : List Tape)
    (hstep : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running q ⟨y :: left, x, right⟩) =
        .running q ⟨left, y, x :: right⟩)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running q (beforeLeftPath path left terminal right))
      (.running q (afterLeftPath path left terminal right)) := by
  induction path generalizing right with
  | nil =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx := hstep x (by simp)
      have hxs : ∀ z, z ∈ xs → ∀ left y right,
          oneStep (.running q ⟨y :: left, z, right⟩) =
            .running q ⟨left, y, z :: right⟩ := by
        intro z hz
        exact hstep z (by simp [hz])
      cases xs with
      | nil =>
          apply StopFreeValidZeroRun.one
          · apply validStepAt_zero_of_oneStep_running
            simpa [beforeLeftPath, afterLeftPath] using
              hx left terminal right
          · simp [beforeLeftPath, IsConcreteCycleStop,
              IsConcreteCycleBoundary, concreteHalted, hq]
      | cons y ys =>
          have hfirst : StopFreeValidZeroRun 1
              (.running q (beforeLeftPath (x :: y :: ys) left terminal right))
              (.running q
                (beforeLeftPath (y :: ys) left terminal (x :: right))) := by
            apply StopFreeValidZeroRun.one
            · apply validStepAt_zero_of_oneStep_running
              simpa [beforeLeftPath, List.append_assoc] using
                hx (ys ++ terminal :: left) y right
            · simp [beforeLeftPath, IsConcreteCycleStop,
                IsConcreteCycleBoundary, concreteHalted, hq]
          have hrest := ih hxs (x :: right)
          have hall := hfirst.append hrest
          simpa [beforeLeftPath, afterLeftPath, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def stopFree_leftPathMap_of
    (q : State) (hq : q ≠ .cycleStart) (path : List Tape)
    (f : Tape → Tape)
    (hstep : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running q ⟨y :: left, x, right⟩) =
        .running q ⟨left, y, f x :: right⟩)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running q (beforeLeftPath path left terminal right))
      (.running q (afterLeftPathMap path f left terminal right)) := by
  induction path generalizing right with
  | nil =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx := hstep x (by simp)
      have hxs : ∀ z, z ∈ xs → ∀ left y right,
          oneStep (.running q ⟨y :: left, z, right⟩) =
            .running q ⟨left, y, f z :: right⟩ := by
        intro z hz
        exact hstep z (by simp [hz])
      cases xs with
      | nil =>
          apply StopFreeValidZeroRun.one
          · apply validStepAt_zero_of_oneStep_running
            simpa [beforeLeftPath, afterLeftPathMap] using
              hx left terminal right
          · cases q <;>
              simp_all [beforeLeftPath, IsConcreteCycleStop,
                IsConcreteCycleBoundary, concreteHalted]
      | cons y ys =>
          have hfirst : StopFreeValidZeroRun 1
              (.running q (beforeLeftPath (x :: y :: ys) left terminal right))
              (.running q
                (beforeLeftPath (y :: ys) left terminal (f x :: right))) := by
            apply StopFreeValidZeroRun.one
            · apply validStepAt_zero_of_oneStep_running
              simpa [beforeLeftPath, List.append_assoc] using
                hx (ys ++ terminal :: left) y right
            · cases q <;>
                simp_all [beforeLeftPath, IsConcreteCycleStop,
                  IsConcreteCycleBoundary, concreteHalted]
          have hrest := ih hxs (f x :: right)
          have hall := hfirst.append hrest
          simpa [beforeLeftPath, afterLeftPathMap, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Generic stop-free right scan which also rewrites each traversed cell.
This is the exact-path counterpart of the `restorePc`/`restoreHead` cleanup
loops: the map is part of the endpoint, while every microstep remains an
ordinary slot-zero machine edge. -/
def stopFree_rightPathMap_of
    (q : State) (hq : q ≠ .cycleStart) (path : List Tape)
    (f : Tape → Tape)
    (hstep : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running q ⟨left, x, y :: right⟩) =
        .running q ⟨f x :: left, y, right⟩)
    (left : List Tape) (terminal : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running q (beforeRightPath path left terminal right))
      (.running q (afterRightPathMap path f left terminal right)) := by
  induction path generalizing left with
  | nil =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | cons x xs ih =>
      have hx := hstep x (by simp)
      have hxs : ∀ z, z ∈ xs → ∀ left y right,
          oneStep (.running q ⟨left, z, y :: right⟩) =
            .running q ⟨f z :: left, y, right⟩ := by
        intro z hz
        exact hstep z (by simp [hz])
      cases xs with
      | nil =>
          apply StopFreeValidZeroRun.one
          · apply validStepAt_zero_of_oneStep_running
            simpa [beforeRightPath, afterRightPathMap] using
              hx left terminal right
          · cases q <;>
              simp_all [beforeRightPath, IsConcreteCycleStop,
                IsConcreteCycleBoundary, concreteHalted]
      | cons y ys =>
          have hfirst : StopFreeValidZeroRun 1
              (.running q (beforeRightPath (x :: y :: ys) left terminal right))
              (.running q
                (beforeRightPath (y :: ys) (f x :: left) terminal right)) := by
            apply StopFreeValidZeroRun.one
            · apply validStepAt_zero_of_oneStep_running
              simpa [beforeRightPath, List.append_assoc] using
                hx left y (ys ++ terminal :: right)
            · cases q <;>
                simp_all [beforeRightPath, IsConcreteCycleStop,
                  IsConcreteCycleBoundary, concreteHalted]
          have hrest := ih hxs (f x :: left)
          have hall := hfirst.append hrest
          simpa [beforeRightPath, afterRightPathMap, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- Stop-free strengthening of the common seek/write/return action-head
routine. -/
def stopFree_actionWriteHead_of
    (seekState : State) (hseek : seekState ≠ .cycleStart)
    (oldHead newHead : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hwrite : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, oldHead, right⟩) =
        .running (.actionPhase .writeReturning)
          ⟨left, y, newHead :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore actionBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running seekState
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left) newHead suffix)) := by
  have hscan := stopFree_rightPath_of seekState hseek path hpass
    (ulogCore actionBoundary :: left) oldHead suffix
  have hwriteStep : StopFreeValidZeroRun 1
      (.running seekState
        (afterRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running (.actionPhase .writeReturning)
        (beforeLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : path.reverse with
      | nil =>
          simpa [afterRightPath, beforeLeftPath, hr] using
            hwrite left (ulogCore actionBoundary) suffix
      | cons x xs =>
          simpa [afterRightPath, beforeLeftPath, hr,
            List.append_assoc] using
            hwrite (xs ++ ulogCore actionBoundary :: left) x suffix
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted, hseek]
  have hreturnStep := stopFree_leftPath_of
    (.actionPhase .writeReturning) (by decide) path.reverse (by
      intro x hx l y r
      have hx' : x ∈ path := by simpa using hx
      have h := hreturn x hx'
      exact actionWriteReturn_pass x h.1 h.2 l y r)
    left (ulogCore actionBoundary) (newHead :: suffix)
  have hboundary : StopFreeValidZeroRun 1
      (.running (.actionPhase .writeReturning)
        (afterLeftPath path.reverse left (ulogCore actionBoundary)
          (newHead :: suffix)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left) newHead suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path with
      | nil =>
          simpa [afterLeftPath, beforeRightPath] using
            actionWriteReturn_boundary left newHead suffix
      | cons x xs =>
          simpa [afterLeftPath, beforeRightPath,
            List.append_assoc] using
            actionWriteReturn_boundary left x (xs ++ newHead :: suffix)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let hall := ((hscan.append hwriteStep).append hreturnStep).append hboundary
  exact ⟨_, hall⟩

def stopFree_actionWriteZero_head
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .seekWriteZero)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) :=
  stopFree_actionWriteHead_of (.actionPhase .seekWriteZero) (by decide)
    oldHead (ulogCore payloadHeadZero) path
    (fun x hx l y r =>
      actionSeekWriteZero_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteZero_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

def stopFree_actionWriteOne_head
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .seekWriteOne)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadOne) suffix)) :=
  stopFree_actionWriteHead_of (.actionPhase .seekWriteOne) (by decide)
    oldHead (ulogCore payloadHeadOne) path
    (fun x hx l y r =>
      actionSeekWriteOne_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteOne_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

def stopFree_actionWriteBlank_head
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .seekWriteBlank)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadBlank) suffix)) :=
  stopFree_actionWriteHead_of (.actionPhase .seekWriteBlank) (by decide)
    oldHead (ulogCore payloadHeadBlank) path
    (fun x hx l y r =>
      actionSeekWriteBlank_pass x (hpath x hx).1 (hpath x hx).2.1 l y r)
    (actionSeekWriteBlank_head oldHead hhead)
    (fun x hx => ⟨(hpath x hx).2.2.1, (hpath x hx).2.2.2⟩)
    left suffix

def stopFree_actionWriteZero
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionWrite
        ⟨left, ulogCore codeOne, path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  have hstart : StopFreeValidZeroRun 1
      (.running .actionWrite
        ⟨left, ulogCore codeOne, path ++ oldHead :: suffix⟩)
      (.running (.actionPhase .seekWriteZero)
        (beforeRightPath path (ulogCore actionBoundary :: left)
          oldHead suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [beforeRightPath, actionWrite_zero, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hheadRun⟩ :=
    stopFree_actionWriteZero_head oldHead hhead path hpath left suffix
  exact ⟨1 + n, hstart.append hheadRun⟩

def stopFree_actionWriteOne
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  let counted : Result := .running (.actionPhase .writeCountOne)
    ⟨ulogCore codeZero :: left, ulogCore codeOne,
      path ++ oldHead :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: path ++ oldHead :: suffix⟩) counted := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [counted] using actionWrite_more left (ulogCore codeOne)
        (path ++ oldHead :: suffix)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 counted
      (.running (.actionPhase .seekWriteOne)
        (beforeRightPath path
          (ulogCore actionBoundary :: ulogCore codeZero :: left)
          oldHead suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [counted, beforeRightPath, actionWriteOne_done,
          List.append_assoc]
    · simp [counted, IsConcreteCycleStop, IsConcreteCycleBoundary,
        concreteHalted]
  obtain ⟨n, hheadRun⟩ := stopFree_actionWriteOne_head oldHead hhead
    path hpath (ulogCore codeZero :: left) suffix
  exact ⟨2 + n, (h₀.append h₁).append hheadRun⟩

def stopFree_actionWriteBlank
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ oldHead :: suffix⟩)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  let countedOne : Result := .running (.actionPhase .writeCountOne)
    ⟨ulogCore codeZero :: left, ulogCore codeZero,
      ulogCore codeOne :: path ++ oldHead :: suffix⟩
  let countedTwo : Result := .running (.actionPhase .writeCountTwo)
    ⟨ulogCore codeZero :: ulogCore codeZero :: left,
      ulogCore codeOne, path ++ oldHead :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running .actionWrite
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne ::
            path ++ oldHead :: suffix⟩) countedOne := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne] using actionWrite_more left (ulogCore codeZero)
        (ulogCore codeOne :: path ++ oldHead :: suffix)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 countedOne countedTwo := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne, countedTwo] using
        actionWriteOne_more (ulogCore codeZero :: left) (ulogCore codeOne)
          (path ++ oldHead :: suffix)
    · simp [countedOne, IsConcreteCycleStop, IsConcreteCycleBoundary,
        concreteHalted]
  have h₂ : StopFreeValidZeroRun 1 countedTwo
      (.running (.actionPhase .seekWriteBlank)
        (beforeRightPath path
          (ulogCore actionBoundary :: ulogCore codeZero ::
            ulogCore codeZero :: left) oldHead suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [countedTwo, beforeRightPath, actionWriteTwo_done,
          List.append_assoc]
    · simp [countedTwo, IsConcreteCycleStop, IsConcreteCycleBoundary,
        concreteHalted]
  obtain ⟨n, hheadRun⟩ := stopFree_actionWriteBlank_head oldHead hhead
    path hpath (ulogCore codeZero :: ulogCore codeZero :: left) suffix
  exact ⟨3 + n, ((h₀.append h₁).append h₂).append hheadRun⟩

theorem stopFree_actionWriteValid_nonempty
    (write : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (actionWriteStart write left path oldHead suffix)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne ::
            List.replicate write (ulogCore codeZero) ++ left)
          (writeHeadNat write) suffix))) := by
  interval_cases write
  · exact ⟨by
      simpa [actionWriteStart, writeHeadNat] using
        stopFree_actionWriteZero oldHead hhead path hpath left suffix⟩
  · exact ⟨by
      simpa [actionWriteStart, writeHeadNat, List.replicate_succ,
        List.append_assoc] using
        stopFree_actionWriteOne oldHead hhead path hpath left suffix⟩
  · exact ⟨by
      simpa [actionWriteStart, writeHeadNat, List.replicate_succ,
        List.append_assoc] using
        stopFree_actionWriteBlank oldHead hhead path hpath left suffix⟩

noncomputable def stopFree_actionWriteValid
    (write : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (actionWriteStart write left path oldHead suffix)
      (.running .actionTarget
        (beforeRightPath path
          (ulogCore codeOne ::
            List.replicate write (ulogCore codeZero) ++ left)
          (writeHeadNat write) suffix)) :=
  Classical.choice (stopFree_actionWriteValid_nonempty write hwrite oldHead
    hhead path hpath left suffix)

/-- All three supported writes, followed by the exact target-zero accepting
suffix. -/
noncomputable def actionWriteTargetZero_firstStop
    (write current : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (corridor runtime : List Tape)
    (hwritePath : ActionWriteCorridorSafe (ulogCore codeOne :: corridor))
    (htargetPath : TargetRewriteCorridorSafe
      (corridor ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Σ z, FirstValidZeroHit IsConcreteCycleStop
      (actionWriteStart write left (ulogCore codeOne :: corridor) oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.accepted z) := by
  obtain ⟨n, hwriteRun⟩ := stopFree_actionWriteValid write hwrite
    oldHead hhead (ulogCore codeOne :: corridor) hwritePath left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨z, htarget⟩ := targetRawZero_firstStop current
    (corridor ++ writeHeadNat write :: runtime) htargetPath
    (ulogCore codeOne ::
      List.replicate write (ulogCore codeZero) ++ left) tail
  have hwriteRun' : StopFreeValidZeroRun n
      (actionWriteStart write left (ulogCore codeOne :: corridor) oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart 0 current (corridor ++ writeHeadNat write :: runtime)
        (ulogCore codeOne ::
          List.replicate write (ulogCore codeZero) ++ left) tail) := by
    simpa [targetRawStart, beforeRightPath, List.append_assoc] using hwriteRun
  exact ⟨z,
    (hwriteRun'.append
      { valid := htarget.valid
        stop_free := htarget.before }).toFirstHit htarget.hit⟩

/-- Stop-free strengthening of the deterministic rule-return/count prefix
immediately following the selected branch. -/
def stopFree_dynamicRuleSourceStarted
    (slot : Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath leftTape rules input) outer
          (ulogCore pcMark) (head :: right)))
      (dynamicRuleSourceStarted slot leftTape rules input outer head right) := by
  let path := dynamicRuleReturnPath leftTape rules input
  have hscan := stopFree_leftPath_of (.ruleSeekChoice slot)
    (by intro h; cases h) path
    (by
      intro x hx l y r
      exact dynamicRuleReturnPath_pass slot leftTape hleft rules input x
        (by simpa [path] using hx) l y r)
    outer (ulogCore pcMark) (head :: right)
  have hmark : StopFreeValidZeroRun 1
      (.running (.ruleSeekChoice slot)
        (afterLeftPath path outer (ulogCore pcMark) (head :: right)))
      (.running (.ruleCountSeek slot)
        (beforeRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: outer) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases rules with
      | nil => exact (hrules rfl).elim
      | cons r rs =>
          simp [path, afterLeftPath, beforeRightPath,
            dynamicRuleReturnPath_reverse, ruleSeekChoice_mark,
            codeTape, List.replicate_succ, List.append_assoc]
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hcount := stopFree_rightPath_of (.ruleCountSeek slot)
    (by intro h; cases h)
    (List.replicate rules.length (ulogCore pcDone)) (by
      intro x hx l y r
      have hm : rules.length ≠ 0 ∧ x = ulogCore pcDone := by
        simpa only [List.mem_replicate] using hx
      rw [hm.2]
      exact ruleCountSeek_done slot l y r)
    (ulogCore pcMark :: outer) (ulogCore codeOne)
    ((ULogBytecode.encodeRules rules).map codeTape ++
      (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
        head :: right)
  have henc : ULogBytecode.encodeRules rules ≠ [] := encodeRules_ne_nil hrules
  have hend : StopFreeValidZeroRun 1
      (.running (.ruleCountSeek slot)
        (afterRightPath
          (List.replicate rules.length (ulogCore pcDone))
          (ulogCore pcMark :: outer) (ulogCore codeOne)
          ((ULogBytecode.encodeRules rules).map codeTape ++
            (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
              head :: right)))
      (dynamicRuleSourceStarted slot leftTape rules input outer head right) := by
    apply StopFreeValidZeroRun.one
    · have hrun : oneStep
          (.running (.ruleCountSeek slot)
            (afterRightPath
              (List.replicate rules.length (ulogCore pcDone))
              (ulogCore pcMark :: outer) (ulogCore codeOne)
              ((ULogBytecode.encodeRules rules).map codeTape ++
                (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
                  head :: right))) =
          dynamicRuleSourceStarted slot leftTape rules input outer head right := by
        cases he : ULogBytecode.encodeRules rules with
        | nil => exact (henc he).elim
        | cons b bs =>
            simpa [dynamicRuleSourceStarted, afterRightPath, he,
              List.replicate_succ', List.append_assoc] using
              ruleCountSeek_end slot
                (List.replicate rules.length (ulogCore pcDone) ++
                  ulogCore pcMark :: outer)
                (codeTape b)
                (bs.map codeTape ++ (payloadProgramPrefix input).reverse ++
                  leftTape.reverse ++ head :: right)
      have hne : dynamicRuleSourceStarted slot leftTape rules input outer head
          right ≠ .stuck := by
        cases he : ULogBytecode.encodeRules rules with
        | nil => exact (henc he).elim
        | cons b bs =>
            simp [dynamicRuleSourceStarted, he]
      have hv := validStepAt_zero_of_not_halted_of_oneStep_ne_stuck
        (start := .running (.ruleCountSeek slot)
          (afterRightPath
            (List.replicate rules.length (ulogCore pcDone))
            (ulogCore pcMark :: outer) (ulogCore codeOne)
            ((ULogBytecode.encodeRules rules).map codeTape ++
              (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
                head :: right)))
        (by rfl) (by rw [hrun]; exact hne)
      exact hv.trans (congrArg some hrun)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let hall := ((hscan.append hmark).append hcount).append hend
  exact ⟨_, hall⟩

/-- Stop-free unary-field scan shared by matched-source/read decoding. -/
def stopFree_unaryState_zeros_of
    (q : State) (hq : q ≠ .cycleStart) (n : ℕ)
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    StopFreeValidZeroRun n (beforeUnaryState q n left y right)
      (afterUnaryState q n left y right) := by
  induction n generalizing left with
  | zero =>
      exact
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
  | succ n ih =>
      have hfirst : StopFreeValidZeroRun 1
          (beforeUnaryState q (n + 1) left y right)
          (beforeUnaryState q n (ulogCore codeZero :: left) y right) := by
        apply StopFreeValidZeroRun.one
        · cases n with
          | zero =>
              have hone := hzero left (ulogCore codeOne) (y :: right)
              simpa [beforeUnaryState] using
                (validStepAt_zero_of_oneStep_running hone)
          | succ n =>
              have hone := hzero left (ulogCore codeZero)
                (List.replicate n (ulogCore codeZero) ++
                  ulogCore codeOne :: y :: right)
              simpa [beforeUnaryState, List.replicate_succ,
                List.append_assoc] using
                (validStepAt_zero_of_oneStep_running hone)
        · simp [beforeUnaryState, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted, hq]
      have hrest := ih (ulogCore codeZero :: left)
      have hall := hfirst.append hrest
      simpa [afterUnaryState, List.replicate_succ', List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def stopFree_unaryState_of
    (q qnext : State) (hq : q ≠ .cycleStart) (n : ℕ)
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (hone : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeOne, y :: right⟩) =
        .running qnext ⟨ulogCore codeOne :: left, y, right⟩)
    (left : List Tape) (y : Tape) (right : List Tape) :
    StopFreeValidZeroRun (n + 1) (beforeUnaryState q n left y right)
      (.running qnext
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
  have hzeros := stopFree_unaryState_zeros_of q hq n hzero left y right
  have honeStep : StopFreeValidZeroRun 1 (afterUnaryState q n left y right)
      (.running qnext
        ⟨ulogCore codeOne ::
            (List.replicate n (ulogCore codeZero) ++ left),
          y, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterUnaryState] using
        hone (List.replicate n (ulogCore codeZero) ++ left) y right
    · simp [afterUnaryState, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted, hq]
  exact hzeros.append honeStep

/-- The matched-source unary read selector is stop-free for every source
value. -/
def stopFree_sourceFieldRestoredAt_read
    (slot : Bool) (q : ℕ) (boundary : ULogLetter) (b : Bool)
    (base corridor suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceFieldRestoredAt slot q boundary base (codeTape b :: corridor)
        suffix)
      (sourceReadStartedAt slot q boundary b base corridor suffix) := by
  have hrun := stopFree_unaryState_of
    (.fieldCompare .matchedSource slot) (.fieldCompare .read slot)
    (by intro h; cases h) q (matchedSourceSeek_zero slot)
    (matchedSourceSeek_one slot) (ulogCore boundary :: base) (codeTape b)
    (corridor ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact ⟨q + 1, by
    cases q <;>
      simpa [sourceFieldRestoredAt, sourceReadStartedAt, beforeUnaryState,
        List.replicate_succ, List.append_assoc] using hrun⟩

/-- Stop-free strengthening of the common read-head match routine. -/
def stopFree_readHeadMatch_of
    (slot : Bool) (seekState : State) (hseek : seekState ≠ .cycleStart)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hmatch : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, head, right⟩) =
        .running (.readPhase .returning slot) ⟨left, y, head :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore readBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left) head suffix)) := by
  have hscan := stopFree_rightPath_of seekState hseek path hpass
    (ulogCore readBoundary :: left) head suffix
  have hmatchStep : StopFreeValidZeroRun 1
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.readPhase .returning slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : path.reverse with
      | nil => simpa [afterRightPath, beforeLeftPath, hr] using
          hmatch left (ulogCore readBoundary) suffix
      | cons x xs => simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (hmatch (xs ++ ulogCore readBoundary :: left) x suffix)
    · cases seekState <;>
        simp_all [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hreturnScan := stopFree_leftPath_of (.readPhase .returning slot)
    (by intro h; cases h) path.reverse (by
      intro x hx l y r
      have hx' : x ∈ path := by simpa using hx
      have hp := hreturn x hx'
      exact readReturn_pass slot x hp.1 hp.2 l y r)
    left (ulogCore readBoundary) (head :: suffix)
  have hboundary : StopFreeValidZeroRun 1
      (.running (.readPhase .returning slot)
        (afterLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix)))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left) head suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path with
      | nil => simpa [afterLeftPath, beforeRightPath] using
          readReturn_boundary slot left head suffix
      | cons x xs => simpa [afterLeftPath, beforeRightPath,
          List.append_assoc] using
          readReturn_boundary slot left x (xs ++ head :: suffix)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  let hall := ((hscan.append hmatchStep).append hreturnScan).append hboundary
  exact ⟨_, hall⟩

def stopFree_readZero_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadZero) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) :=
  stopFree_readHeadMatch_of slot (.readPhase .seekZero slot)
    (by intro h; cases h) (ulogCore payloadHeadZero) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekZero_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekZero_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩) left suffix

def stopFree_readOne_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadOne) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadOne) suffix)) :=
  stopFree_readHeadMatch_of slot (.readPhase .seekOne slot)
    (by intro h; cases h) (ulogCore payloadHeadOne) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekOne_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekOne_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩) left suffix

def stopFree_readBlank_head (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe path) (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path (ulogCore readBoundary :: left)
          (ulogCore payloadHeadBlank) suffix))
      (.running (.fieldCompare .slot slot)
        (beforeRightPath path (ulogCore codeOne :: left)
          (ulogCore payloadHeadBlank) suffix)) :=
  stopFree_readHeadMatch_of slot (.readPhase .seekBlank slot)
    (by intro h; cases h) (ulogCore payloadHeadBlank) path
    (fun x hx l y r =>
      let h := hpath x hx
      readSeekBlank_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (readSeekBlank_match slot)
    (fun x hx => ⟨(hpath x hx).2.2.2.2.1,
      (hpath x hx).2.2.2.2.2⟩) left suffix

def stopFree_slotMatch (slot : Bool) (path : List Tape)
    (left : List Tape) (head : Tape) (suffix : List Tape) :
    StopFreeValidZeroRun 1
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape slot :: path)
          left head suffix))
      (.running .actionWrite
        (beforeRightPath path (codeTape slot :: left) head suffix)) := by
  apply StopFreeValidZeroRun.one
  · apply validStepAt_zero_of_oneStep_running
    cases path <;>
      simp [beforeRightPath, fieldCompare_slot_match, List.append_assoc]
  · simp [beforeRightPath, IsConcreteCycleStop,
      IsConcreteCycleBoundary, concreteHalted]

def stopFree_slotMismatchRaw (slot : Bool) (path : List Tape)
    (left : List Tape) (saved : Tape) (head : Tape)
    (suffix : List Tape) :
    StopFreeValidZeroRun 1
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: path)
          (saved :: left) head suffix))
      (.running (.restoreRule slot)
        ⟨left, saved, codeTape (!slot) :: path ++ head :: suffix⟩) := by
  apply StopFreeValidZeroRun.one
  · apply validStepAt_zero_of_oneStep_running
    cases path <;>
      simp [beforeRightPath, fieldCompare_slot_mismatch,
        List.append_assoc]
  · cases slot <;>
      simp [beforeRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]

def stopFree_readZero_toSlot (slot : Bool) (slotCell : Tape)
    (path : List Tape)
    (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          slotCell :: path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore codeOne :: left) (ulogCore payloadHeadZero) suffix)) := by
  have hstart : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          slotCell :: path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore readBoundary :: left)
          (ulogCore payloadHeadZero) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [beforeRightPath, fieldCompare_read_zero, List.append_assoc]
    · cases slot <;>
        simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readZero_head slot
    (slotCell :: path) hpath left suffix
  exact ⟨1 + n, hstart.append hhead⟩

def stopFree_sourceReadAtSlotMismatchZero_boundary
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst 0) base
        ((ULogBytecode.encodeNatField 0).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat 0 :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source 0)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat 0 :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  let readBase := ulogCore codeOne ::
    List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base
  obtain ⟨a, hread⟩ := stopFree_readZero_toSlot slot (codeTape (!slot))
    actionPath hsafe readBase
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hmismatch := stopFree_slotMismatchRaw slot actionPath
    readBase
    (ulogCore codeOne) (ulogCore payloadHeadZero)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hall := hread.append hmismatch
  have hendEq :
      ⟨readBase, ulogCore codeOne,
        codeTape (!slot) :: actionPath ++ ulogCore payloadHeadZero ::
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)⟩ =
      beforeLeftPath (slotMismatchRestorePath source 0) base
        (ulogCore boundary)
        (codeTape (!slot) :: actionPath ++ readHeadNat 0 :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
    rw [← slotMismatch_beforeLeft_eq source 0 boundary base]
    simp [readBase, readMismatchBaseAt, readHeadNat, List.append_assoc]
  have hendResultEq := congrArg (Result.running (.restoreRule slot)) hendEq
  rw [hendResultEq] at hall
  exact ⟨a + 1, by
    simpa [sourceReadStartedAt, unaryFieldFirst,
      ULogBytecode.encodeNatField, readHeadNat, readBase, codeTape,
      List.append_assoc] using hall⟩

def stopFree_readOne_toSlot (slot : Bool) (slotCell : Tape)
    (path : List Tape) (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: slotCell :: path ++
            ulogCore payloadHeadOne :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore codeOne :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  let counted : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: left, ulogCore codeOne,
      slotCell :: path ++ ulogCore payloadHeadOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: slotCell :: path ++
            ulogCore payloadHeadOne :: suffix⟩) counted := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [counted] using fieldCompare_read_more slot left
        (ulogCore codeOne)
        (slotCell :: path ++ ulogCore payloadHeadOne :: suffix)
    · cases slot <;>
        simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 counted
      (.running (.readPhase .seekOne slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore readBoundary :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [counted, beforeRightPath, readCountOne_done,
          List.append_assoc]
    · cases slot <;>
        simp [counted, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readOne_head slot
    (slotCell :: path) hpath (ulogCore codeZero :: left) suffix
  exact ⟨2 + n, (h₀.append h₁).append hhead⟩

def stopFree_readBlank_toSlot (slot : Bool) (slotCell : Tape)
    (path : List Tape) (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne :: slotCell :: path ++
            ulogCore payloadHeadBlank :: suffix⟩)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  let countedOne : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: left, ulogCore codeZero,
      ulogCore codeOne :: slotCell :: path ++
        ulogCore payloadHeadBlank :: suffix⟩
  let countedTwo : Result := .running (.readPhase .countTwo slot)
    ⟨ulogCore codeZero :: ulogCore codeZero :: left,
      ulogCore codeOne,
      slotCell :: path ++ ulogCore payloadHeadBlank :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne :: slotCell :: path ++
            ulogCore payloadHeadBlank :: suffix⟩) countedOne := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne] using fieldCompare_read_more slot left
        (ulogCore codeZero)
        (ulogCore codeOne :: slotCell :: path ++
          ulogCore payloadHeadBlank :: suffix)
    · cases slot <;>
        simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 countedOne countedTwo := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne, countedTwo] using
        readCountOne_more slot (ulogCore codeZero :: left)
          (ulogCore codeOne)
          (slotCell :: path ++ ulogCore payloadHeadBlank :: suffix)
    · cases slot <;>
        simp [countedOne, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have h₂ : StopFreeValidZeroRun 1 countedTwo
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath (slotCell :: path)
          (ulogCore readBoundary :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [countedTwo, beforeRightPath, readCountTwo_done,
          List.append_assoc]
    · cases slot <;>
        simp [countedTwo, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readBlank_head slot
    (slotCell :: path) hpath
    (ulogCore codeZero :: ulogCore codeZero :: left) suffix
  exact ⟨3 + n, ((h₀.append h₁).append h₂).append hhead⟩

def stopFree_sourceReadAtSlotMismatchOne_boundary
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst 1) base
        ((ULogBytecode.encodeNatField 1).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat 1 :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source 1)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat 1 :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  let sourceBase := ulogCore codeOne ::
    List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base
  let readBase := ulogCore codeZero :: sourceBase
  obtain ⟨a, hread⟩ := stopFree_readOne_toSlot slot (codeTape (!slot))
    actionPath hsafe sourceBase
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hmismatch := stopFree_slotMismatchRaw slot actionPath readBase
    (ulogCore codeOne) (ulogCore payloadHeadOne)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hall := hread.append hmismatch
  have hendEq :
      ⟨readBase, ulogCore codeOne,
        codeTape (!slot) :: actionPath ++ ulogCore payloadHeadOne ::
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)⟩ =
      beforeLeftPath (slotMismatchRestorePath source 1) base
        (ulogCore boundary)
        (codeTape (!slot) :: actionPath ++ readHeadNat 1 :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
    rw [← slotMismatch_beforeLeft_eq source 1 boundary base]
    simp [readBase, sourceBase, readMismatchBaseAt, readHeadNat,
      List.append_assoc]
  rw [congrArg (Result.running (.restoreRule slot)) hendEq] at hall
  exact ⟨a + 1, by
    simpa [sourceReadStartedAt, unaryFieldFirst,
      ULogBytecode.encodeNatField, readHeadNat, sourceBase, readBase,
      codeTape, List.append_assoc] using hall⟩

def stopFree_sourceReadAtSlotMismatchBlank_boundary
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst 2) base
        ((ULogBytecode.encodeNatField 2).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat 2 :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source 2)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat 2 :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  let sourceBase := ulogCore codeOne ::
    List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base
  let readBase := ulogCore codeZero :: ulogCore codeZero :: sourceBase
  obtain ⟨a, hread⟩ := stopFree_readBlank_toSlot slot (codeTape (!slot))
    actionPath hsafe sourceBase
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hmismatch := stopFree_slotMismatchRaw slot actionPath readBase
    (ulogCore codeOne) (ulogCore payloadHeadBlank)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hall := hread.append hmismatch
  have hendEq :
      ⟨readBase, ulogCore codeOne,
        codeTape (!slot) :: actionPath ++ ulogCore payloadHeadBlank ::
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)⟩ =
      beforeLeftPath (slotMismatchRestorePath source 2) base
        (ulogCore boundary)
        (codeTape (!slot) :: actionPath ++ readHeadNat 2 :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
    rw [← slotMismatch_beforeLeft_eq source 2 boundary base]
    simp [readBase, sourceBase, readMismatchBaseAt, readHeadNat,
      List.append_assoc]
  rw [congrArg (Result.running (.restoreRule slot)) hendEq] at hall
  exact ⟨a + 1, by
    simpa [sourceReadStartedAt, unaryFieldFirst,
      ULogBytecode.encodeNatField, readHeadNat, sourceBase, readBase,
      codeTape, List.append_assoc] using hall⟩

theorem stopFree_sourceReadAtSlotMismatch_boundary_nonempty
    (slot : Bool) (source read : ℕ) (hread : read < 3)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source read)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  interval_cases read
  · exact ⟨stopFree_sourceReadAtSlotMismatchZero_boundary slot source
      boundary base actionPath runtime suffix hsafe⟩
  · exact ⟨stopFree_sourceReadAtSlotMismatchOne_boundary slot source
      boundary base actionPath runtime suffix hsafe⟩
  · exact ⟨stopFree_sourceReadAtSlotMismatchBlank_boundary slot source
      boundary base actionPath runtime suffix hsafe⟩

noncomputable def stopFree_sourceReadAtSlotMismatch_boundary
    (slot : Bool) (source read : ℕ) (hread : read < 3)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source read)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) :=
  Classical.choice (stopFree_sourceReadAtSlotMismatch_boundary_nonempty slot
    source read hread boundary base actionPath runtime suffix hsafe)

def stopFree_restoreRule_boundary
    (slot : Bool) (path : List Tape) (hpath : MismatchRestorePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (outer : List Tape) (pcSide : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.restoreRule slot)
        (beforeLeftPath path (pcSide :: outer) (ulogCore boundary) right))
      (.running (.mismatchReturnToPc slot)
        ⟨outer, pcSide,
          ulogCore boundary :: path.reverse.map restoreMismatchCell ++ right⟩) := by
  have hscan := stopFree_leftPathMap_of (.restoreRule slot)
    (by intro h; cases h) path restoreMismatchCell (by
      intro x hx l y r
      have h := hpath x hx
      exact restoreRule_step slot x h.1 h.2.1 h.2.2.1 h.2.2.2 l y r)
    (pcSide :: outer) (ulogCore boundary) right
  have hend : StopFreeValidZeroRun 1
      (.running (.restoreRule slot)
        (afterLeftPathMap path restoreMismatchCell (pcSide :: outer)
          (ulogCore boundary) right))
      (.running (.mismatchReturnToPc slot)
        ⟨outer, pcSide,
          ulogCore boundary :: path.reverse.map restoreMismatchCell ++ right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterLeftPathMap] using
        restoreRule_boundary slot boundary hboundary outer pcSide
          (path.reverse.map restoreMismatchCell ++ right)
    · cases slot <;>
        simp [afterLeftPathMap, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

def stopFree_mismatchReturnToPc
    (slot : Bool) (path : List Tape)
    (hpath : ∀ x ∈ path, x ≠ ulogCore pcMark)
    (outer : List Tape) (y : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchReturnToPc slot)
        (beforeLeftPath path outer (ulogCore pcMark) (y :: right)))
      (.running (.mismatchCount slot)
        (beforeRightPath path.reverse (ulogCore pcMark :: outer) y right)) := by
  have hscan := stopFree_leftPath_of (.mismatchReturnToPc slot)
    (by intro h; cases h) path (by
      intro x hx l z r
      exact mismatchReturnToPc_pass slot x (hpath x hx) l z r)
    outer (ulogCore pcMark) (y :: right)
  have hend : StopFreeValidZeroRun 1
      (.running (.mismatchReturnToPc slot)
        (afterLeftPath path outer (ulogCore pcMark) (y :: right)))
      (.running (.mismatchCount slot)
        (beforeRightPath path.reverse (ulogCore pcMark :: outer) y right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : path.reverse with
      | nil => simpa [afterLeftPath, beforeRightPath, hr] using
          mismatchReturnToPc_mark slot outer y right
      | cons x xs => simpa [afterLeftPath, beforeRightPath, hr,
          List.append_assoc] using
          mismatchReturnToPc_mark slot outer x (xs ++ y :: right)
    · cases slot <;>
        simp [afterLeftPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

def stopFree_mismatchCount_fresh
    (slot : Bool) (done : ℕ) (left : List Tape)
    (y : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchCount slot)
        (beforeRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right)))
      (.running (.mismatchSeekBoundary slot)
        ⟨ulogCore codeZero ::
            (List.replicate done (ulogCore codeZero) ++ left), y, right⟩) := by
  have hscan := stopFree_rightPath_of (.mismatchCount slot)
    (by intro h; cases h) (List.replicate done (ulogCore codeZero)) (by
      intro x hx l z r
      have hm : done ≠ 0 ∧ x = ulogCore codeZero := by
        simpa only [List.mem_replicate] using hx
      rw [hm.2]
      exact mismatchCount_consumed slot l z r)
    left (ulogCore pcDone) (y :: right)
  have hend : StopFreeValidZeroRun 1
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (y :: right)))
      (.running (.mismatchSeekBoundary slot)
        ⟨ulogCore codeZero ::
            (List.replicate done (ulogCore codeZero) ++ left), y, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using mismatchCount_fresh slot
        (List.replicate done (ulogCore codeZero) ++ left) y right
    · cases slot <;>
        simp [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  exact ⟨done + 1, by simpa using hscan.append hend⟩

def stopFree_mismatchCount_prefix_fresh
    (slot : Bool) (done : ℕ) (path left : List Tape)
    (boundary : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchCount slot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path) left boundary right))
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path
          (ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++ left)
          boundary right)) := by
  cases path with
  | nil =>
      cases done with
      | zero => simpa [beforeRightPath] using
          (stopFree_mismatchCount_fresh slot 0 left boundary right)
      | succ n => simpa [beforeRightPath, List.replicate_succ,
          List.append_assoc] using
          (stopFree_mismatchCount_fresh slot (n + 1) left boundary right)
  | cons x xs =>
      cases done with
      | zero => simpa [beforeRightPath, List.append_assoc] using
          (stopFree_mismatchCount_fresh slot 0 left x
            (xs ++ boundary :: right))
      | succ n => simpa [beforeRightPath, List.replicate_succ,
          List.append_assoc] using
          (stopFree_mismatchCount_fresh slot (n + 1) left x
            (xs ++ boundary :: right))

def stopFree_mismatchSeekBoundary
    (slot : Bool) (path : List Tape) (hpath : MismatchBoundaryFree path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (left : List Tape) (y : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary) (y :: right)))
      (.running (.mismatchSkipSource slot)
        ⟨(if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ left, y, right⟩) := by
  have hscan := stopFree_rightPath_of (.mismatchSeekBoundary slot)
    (by intro h; cases h) path (by
      intro x hx l z r
      have h := hpath x hx
      exact mismatchSeekBoundary_pass slot x h.1 h.2.1 h.2.2 l z r)
    left (ulogCore boundary) (y :: right)
  have hend : StopFreeValidZeroRun 1
      (.running (.mismatchSeekBoundary slot)
        (afterRightPath path left (ulogCore boundary) (y :: right)))
      (.running (.mismatchSkipSource slot)
        ⟨(if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ left, y, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        mismatchSeekBoundary_boundary slot boundary hboundary
          (path.reverse ++ left) y right
    · cases slot <;>
        simp [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

def stopFree_unaryState_prefix_of
    (q qnext : State) (hq : q ≠ .cycleStart) (n : ℕ)
    (tail : List Bool) (htail : tail ≠ [])
    (hzero : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeZero, y :: right⟩) =
        .running q ⟨ulogCore codeZero :: left, y, right⟩)
    (hone : ∀ left y right,
      oneStep (.running q ⟨left, ulogCore codeOne, y :: right⟩) =
        .running qnext ⟨ulogCore codeOne :: left, y, right⟩)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Σ steps, StopFreeValidZeroRun steps
      (atBits q (ULogBytecode.encodeNatField n ++ tail) left after right)
      (atBits qnext tail
        ((ULogBytecode.encodeNatField n).reverse.map codeTape ++ left)
        after right) := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons b bs =>
      cases n with
      | zero =>
          exact ⟨1, by
            simpa [atBits, beforeUnaryState, codeTape,
              ULogBytecode.encodeNatField, List.map_append,
              List.reverse_append, List.append_assoc] using
              stopFree_unaryState_of q qnext hq 0 hzero hone left
                (codeTape b) (bs.map codeTape ++ after :: right)⟩
      | succ n =>
          exact ⟨n + 2, by
            simpa [atBits, beforeUnaryState, codeTape,
              ULogBytecode.encodeNatField, List.map_append,
              List.reverse_append, List.replicate_succ,
              List.append_assoc, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using
              stopFree_unaryState_of q qnext hq (n + 1) hzero hone left
                (codeTape b) (bs.map codeTape ++ after :: right)⟩

def stopFree_mismatchSkipRule
    (lookupSlot : Bool) (r : ULogBytecode.RuleCode)
    (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r ++ next) left after right)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++ left) after right) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [moveFirst move, moveSecond move]
  let lS := sBits.reverse.map codeTape ++ left
  let lR := rBits.reverse.map codeTape ++ lS
  let lSlot := codeTape ruleSlot :: lR
  let lW := wBits.reverse.map codeTape ++ lSlot
  let lT := tBits.reverse.map codeTape ++ lW
  let lM₁ := codeTape (moveFirst move) :: lT
  let lM₂ := mismatchBoundaryTape (moveSecond move) :: lM₁
  obtain ⟨nS, hS⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipSource lookupSlot) (.mismatchSkipRead lookupSlot)
    (by intro h; cases h) source
    (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
    (by simp [rBits, ULogBytecode.encodeNatField])
    (mismatchSkipSource_zero lookupSlot) (mismatchSkipSource_one lookupSlot)
    left after right
  obtain ⟨nR, hR⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipRead lookupSlot) (.mismatchSkipSlot lookupSlot)
    (by intro h; cases h) read
    ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) (by simp)
    (mismatchSkipRead_zero lookupSlot) (mismatchSkipRead_one lookupSlot)
    lS after right
  have hSlotEq := atBits_mismatchSlot lookupSlot ruleSlot
    (wBits ++ tBits ++ mBits ++ next) lR after right
  have hSlot : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right)
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [lSlot, List.append_assoc] using hSlotEq
    · cases lookupSlot <;> cases ruleSlot <;> rfl
    · cases write <;>
        simp [atBits, wBits, ULogBytecode.encodeNatField,
          List.replicate_succ]
    · cases lookupSlot <;> cases ruleSlot <;>
        simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  obtain ⟨nW, hW⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipWrite lookupSlot) (.mismatchSkipTarget lookupSlot)
    (by intro h; cases h) write (tBits ++ mBits ++ next)
    (by simp [tBits, ULogBytecode.encodeNatField])
    (mismatchSkipWrite_zero lookupSlot) (mismatchSkipWrite_one lookupSlot)
    lSlot after right
  obtain ⟨nT, hT⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipTarget lookupSlot) (.mismatchSkipMoveFirst lookupSlot)
    (by intro h; cases h) target (mBits ++ next) (by simp [mBits])
    (mismatchSkipTarget_zero lookupSlot) (mismatchSkipTarget_one lookupSlot)
    lW after right
  have hM₁Eq := atBits_mismatchMoveFirst lookupSlot (moveFirst move)
    (moveSecond move :: next) lT after right
  have hM₁ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveFirst lookupSlot) (mBits ++ next)
        lT after right)
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [mBits, lM₁, List.append_assoc] using hM₁Eq
    · cases lookupSlot <;> cases move <;> rfl
    · cases lookupSlot <;> cases move <;> simp [atBits]
    · cases lookupSlot <;> cases move <;>
        simp [atBits, mBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  have hM₂ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right)
      (atBits (.fieldCompare .source lookupSlot) next lM₂ after right) := by
    cases next with
    | nil => exact (hnext rfl).elim
    | cons b bs =>
        apply StopFreeValidZeroRun.oneOfStep
        · simpa [lM₂] using atBits_mismatchMoveSecond lookupSlot
            (moveSecond move) (b :: bs) lM₁ after right
        · cases lookupSlot <;> cases move <;> rfl
        · cases lookupSlot <;> cases move <;> simp [atBits]
        · cases lookupSlot <;> cases move <;>
            simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
              concreteHalted]
  dsimp [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
    lT, lM₁, lM₂] at hS hR hSlot hW hT hM₁ hM₂
  simp only [List.append_assoc] at hS hR hSlot hW hT hM₁ hM₂
  have hall := (((((hS.append hR).append hSlot).append hW).append hT).append
    hM₁).append hM₂
  exact ⟨_, by
    simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
      lT, lM₁, lM₂, mismatchRulePrefix,
      ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      List.reverse_append, List.map_append, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall⟩

def stopFree_mismatchSeekBoundary_rule
    (slot : Bool) (path : List Tape) (hpath : MismatchBoundaryFree path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.mismatchSkipSource slot)
        (ULogBytecode.encodeRule r ++ next)
        ((if boundary = sourceBoundaryZero then ulogCore codeZero
          else ulogCore codeOne) :: path.reverse ++ left) after right) := by
  have henc : ULogBytecode.encodeRule r ≠ [] := by
    rcases r with ⟨source, read, ruleSlot, action⟩
    cases source <;> simp [ULogBytecode.encodeRule,
      ULogBytecode.encodeNatField, List.replicate_succ]
  cases he : ULogBytecode.encodeRule r ++ next with
  | nil =>
      have hfalse : False := by simpa [henc] using he
      exact hfalse.elim
  | cons b bs =>
      obtain ⟨n, h⟩ := stopFree_mismatchSeekBoundary slot path hpath
        boundary hboundary left (codeTape b)
        (bs.map codeTape ++ after :: right)
      exact ⟨n, by
        simpa [atBits, he, List.map_append, List.append_assoc] using h⟩

def stopFree_mismatchCount_skipRule
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchBoundaryFree path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path) left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ ulogCore codeZero ::
              List.replicate done (ulogCore codeZero) ++ left)
        after right) := by
  let countLeft := ulogCore codeZero ::
    List.replicate done (ulogCore codeZero) ++ left
  let restoredLeft :=
    (if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: path.reverse ++ countLeft
  obtain ⟨a, hcount⟩ := stopFree_mismatchCount_prefix_fresh lookupSlot done
    path left (ulogCore boundary)
    ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
  obtain ⟨b, hseek⟩ := stopFree_mismatchSeekBoundary_rule lookupSlot path
    hpath boundary hboundary r next countLeft after right
  obtain ⟨c, hskip⟩ := stopFree_mismatchSkipRule lookupSlot r next hnext
    restoredLeft after right
  have hall := (hcount.append hseek).append hskip
  exact ⟨a + b + c, by
    simpa [countLeft, restoredLeft, mismatchRulePrefix,
      List.append_assoc, Nat.add_assoc] using hall⟩

def stopFree_mismatchAdvanceRule
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (outer : List Tape) (after : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.mismatchReturnToPc lookupSlot)
        (beforeLeftPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse outer (ulogCore pcMark)
          (ulogCore boundary ::
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right)))
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ ulogCore codeZero ::
              List.replicate done (ulogCore codeZero) ++
                ulogCore pcMark :: outer) after right) := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturnSafe : ∀ x ∈ returnPath, x ≠ ulogCore pcMark := by
    intro x hx
    have hx' : x ∈ path ∨ x = ulogCore pcDone ∨
        (done ≠ 0 ∧ x = ulogCore codeZero) := by
      simpa [returnPath] using hx
    rcases hx' with hp | hd | hz
    · exact hpath.2 x hp
    · rw [hd]; decide
    · rw [hz.2]; decide
  obtain ⟨a, hreturn⟩ := stopFree_mismatchReturnToPc lookupSlot returnPath
    hreturnSafe outer (ulogCore boundary)
    ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
  obtain ⟨b, hcount⟩ := stopFree_mismatchCount_skipRule lookupSlot done
    path hpath.1 boundary hboundary r next hnext (ulogCore pcMark :: outer)
    after right
  have hreturn' : StopFreeValidZeroRun a
      (.running (.mismatchReturnToPc lookupSlot)
        (beforeLeftPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse outer (ulogCore pcMark)
          (ulogCore boundary ::
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right)))
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path) (ulogCore pcMark :: outer)
          (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right))) := by
    simpa [returnPath] using hreturn
  exact ⟨a + b, hreturn'.append hcount⟩

def stopFree_restoreMismatchAdvanceRule
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (restorePath : List Tape) (hrestoreSafe : MismatchRestorePathSafe restorePath)
    (mismatchRight : List Tape) (r : ULogBytecode.RuleCode)
    (next : List Bool) (hnext : next ≠ [])
    (outer : List Tape) (after : Tape) (right : List Tape)
    (hrestored : restorePath.reverse.map restoreMismatchCell ++ mismatchRight =
      (ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right) :
    Σ n, StopFreeValidZeroRun n
      (restoreAdvanceStarted lookupSlot restorePath
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse outer boundary mismatchRight)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ ulogCore codeZero ::
              List.replicate done (ulogCore codeZero) ++
                ulogCore pcMark :: outer) after right) := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      obtain ⟨a, hrestore⟩ := stopFree_restoreRule_boundary lookupSlot
        restorePath hrestoreSafe boundary hboundary
        (xs ++ ulogCore pcMark :: outer) x mismatchRight
      have hrestored' :
          (restorePath.map restoreMismatchCell).reverse ++ mismatchRight =
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right := by
        simpa only [List.map_reverse] using hrestored
      have hrestore' : StopFreeValidZeroRun a
          (restoreAdvanceStarted lookupSlot restorePath returnPath
            outer boundary mismatchRight)
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right))) := by
        simpa [restoreAdvanceStarted, returnPath, he, beforeLeftPath,
          hrestored', List.append_assoc] using hrestore
      obtain ⟨b, hadvance⟩ := stopFree_mismatchAdvanceRule lookupSlot done
        path hpath boundary hboundary r next hnext outer after right
      have hadvance' : StopFreeValidZeroRun b
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right)))
          (atBits (.fieldCompare .source lookupSlot) next
            (mismatchRulePrefix r ++
              (if boundary = sourceBoundaryZero then ulogCore codeZero
                else ulogCore codeOne) :: path.reverse ++
                  ulogCore codeZero ::
                    List.replicate done (ulogCore codeZero) ++
                      ulogCore pcMark :: outer) after right) := by
        simpa [returnPath] using hadvance
      exact ⟨a + b, hrestore'.append hadvance'⟩

def stopFree_readZero_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          codeTape slot :: path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: left)
          (ulogCore payloadHeadZero) suffix)) := by
  have hstart : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeOne,
          codeTape slot :: path ++ ulogCore payloadHeadZero :: suffix⟩)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore readBoundary :: left)
          (ulogCore payloadHeadZero) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [beforeRightPath, fieldCompare_read_zero, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readZero_head slot
    (codeTape slot :: path) hpath left suffix
  have hslot := stopFree_slotMatch slot path (ulogCore codeOne :: left)
    (ulogCore payloadHeadZero) suffix
  exact ⟨1 + n + 1, (hstart.append hhead).append hslot⟩

def stopFree_readOne_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadOne :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
  let counted : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: left, ulogCore codeOne,
      codeTape slot :: path ++ ulogCore payloadHeadOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadOne :: suffix⟩) counted := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [counted] using fieldCompare_read_more slot left
        (ulogCore codeOne)
        (codeTape slot :: path ++ ulogCore payloadHeadOne :: suffix)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 counted
      (.running (.readPhase .seekOne slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore readBoundary :: ulogCore codeZero :: left)
          (ulogCore payloadHeadOne) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [counted, beforeRightPath, readCountOne_done,
          List.append_assoc]
    · simp [counted, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readOne_head slot
    (codeTape slot :: path) hpath (ulogCore codeZero :: left) suffix
  have hslot := stopFree_slotMatch slot path
    (ulogCore codeOne :: ulogCore codeZero :: left)
    (ulogCore payloadHeadOne) suffix
  exact ⟨2 + n + 1, ((h₀.append h₁).append hhead).append hslot⟩

def stopFree_readBlank_slotMatch (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadBlank :: suffix⟩)
      (.running .actionWrite
        (beforeRightPath path
          (codeTape slot :: ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
  let countedOne : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: left, ulogCore codeZero,
      ulogCore codeOne :: codeTape slot ::
        path ++ ulogCore payloadHeadBlank :: suffix⟩
  let countedTwo : Result := .running (.readPhase .countTwo slot)
    ⟨ulogCore codeZero :: ulogCore codeZero :: left,
      ulogCore codeOne,
      codeTape slot :: path ++ ulogCore payloadHeadBlank :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running (.fieldCompare .read slot)
        ⟨left, ulogCore codeZero,
          ulogCore codeZero :: ulogCore codeOne :: codeTape slot ::
            path ++ ulogCore payloadHeadBlank :: suffix⟩) countedOne := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne] using fieldCompare_read_more slot left
        (ulogCore codeZero)
        (ulogCore codeOne :: codeTape slot ::
          path ++ ulogCore payloadHeadBlank :: suffix)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 countedOne countedTwo := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [countedOne, countedTwo] using
        readCountOne_more slot (ulogCore codeZero :: left)
          (ulogCore codeOne)
          (codeTape slot :: path ++ ulogCore payloadHeadBlank :: suffix)
    · simp [countedOne, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have h₂ : StopFreeValidZeroRun 1 countedTwo
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath (codeTape slot :: path)
          (ulogCore readBoundary :: ulogCore codeZero ::
            ulogCore codeZero :: left)
          (ulogCore payloadHeadBlank) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;>
        simp [countedTwo, beforeRightPath, readCountTwo_done,
          List.append_assoc]
    · simp [countedTwo, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨n, hhead⟩ := stopFree_readBlank_head slot
    (codeTape slot :: path) hpath
    (ulogCore codeZero :: ulogCore codeZero :: left) suffix
  have hslot := stopFree_slotMatch slot path
    (ulogCore codeOne :: ulogCore codeZero :: ulogCore codeZero :: left)
    (ulogCore payloadHeadBlank) suffix
  exact ⟨3 + n + 1,
    (((h₀.append h₁).append h₂).append hhead).append hslot⟩

theorem stopFree_sourceReadAtValid_actionWrite_nonempty
    (slot : Bool) (source read write target : ℕ)
    (boundary : ULogLetter) (m : OneTapeTableau.Move)
    (hread : read < 3) (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath)) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime) suffix)
      (actionWriteStart write
        (matchedReadLeftAt slot source read boundary base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))) := by
  cases slot <;> interval_cases read
  · exact ⟨by
      have h := stopFree_readZero_slotMatch false
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩
  · exact ⟨by
      have h := stopFree_readOne_slotMatch false
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩
  · exact ⟨by
      have h := stopFree_readBlank_slotMatch false
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩
  · exact ⟨by
      have h := stopFree_readZero_slotMatch true
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩
  · exact ⟨by
      have h := stopFree_readOne_slotMatch true
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩
  · exact ⟨by
      have h := stopFree_readBlank_slotMatch true
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      cases write <;> simpa [sourceReadStartedAt, matchedReadLeftAt,
        encodedActionPath, ULogBytecode.encodeNatField, actionWriteStart,
        unaryFieldFirst, readHeadNat, beforeRightPath, List.map_append,
        List.replicate_succ, List.append_assoc, codeTape] using h⟩

noncomputable def stopFree_sourceReadAtValid_actionWrite
    (slot : Bool) (source read write target : ℕ)
    (boundary : ULogLetter) (m : OneTapeTableau.Move)
    (hread : read < 3) (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath)) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime) suffix)
      (actionWriteStart write
        (matchedReadLeftAt slot source read boundary base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) :=
  Classical.choice (stopFree_sourceReadAtValid_actionWrite_nonempty slot
    source read write target boundary m hread base movePath runtime suffix hsafe)

/-- One complete matched source-comparison round, with all five phases
certified stop-free. -/
def stopFree_sourceCompareRound
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hseek : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
        x ≠ MStarConcreteAlphabet.work)
    (hreturn : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore sourceMark ∧ x ≠ ulogCore pcMark)
    (left stateRest : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.fieldCompare .source slot)
        ⟨left, ulogCore codeZero,
          sourceCompareScanPath remaining corridor done ++
            ulogCore stateZero :: stateRest⟩)
      (.running (.fieldCompare .source slot)
        (beforeRightPath (sourceCompareScanPath remaining corridor done)
          (ulogCore sourceMark :: left) (ulogCore stateMark) stateRest)) := by
  let path := sourceCompareScanPath remaining corridor done
  have hp : path ≠ [] := sourceCompareScanPath_ne_nil remaining corridor done
  have hstart : StopFreeValidZeroRun 1
      (.running (.fieldCompare .source slot)
        ⟨left, ulogCore codeZero, path ++ ulogCore stateZero :: stateRest⟩)
      (.running (.compareSeekState slot)
        (beforeRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases he : path with
      | nil => exact (hp he).elim
      | cons x xs => simpa [beforeRightPath, he] using
          (fieldCompare_source_zero slot left x
            (xs ++ ulogCore stateZero :: stateRest))
    · cases slot <;>
        simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hseekRun := stopFree_rightPath_of (.compareSeekState slot)
    (by intro h; cases h) path (by
      intro x hx l y r
      have h := hseek x (by simpa [path] using hx)
      exact compareSeekState_pass slot x h.1 h.2.1 h.2.2 l y r)
    (ulogCore sourceMark :: left) (ulogCore stateZero) stateRest
  have hturn : StopFreeValidZeroRun 1
      (.running (.compareSeekState slot)
        (afterRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.compareReturnSource slot)
        (beforeLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hpr : path.reverse ≠ [] := by simpa using hp
      cases he : path.reverse with
      | nil => exact (hpr he).elim
      | cons x xs => simpa [afterRightPath, beforeLeftPath, he,
          List.append_assoc] using
          (compareSeekState_zero slot (xs ++ ulogCore sourceMark :: left)
            x stateRest)
    · cases slot <;>
        simp [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hreturnRun := stopFree_leftPath_of (.compareReturnSource slot)
    (by intro h; cases h) path.reverse (by
      intro x hx l y r
      have hx' : x ∈ path := by simpa using hx
      have h := hreturn x (by simpa [path] using hx')
      exact compareReturnSource_pass slot x h.1 h.2 l y r)
    left (ulogCore sourceMark) (ulogCore stateMark :: stateRest)
  have hend : StopFreeValidZeroRun 1
      (.running (.compareReturnSource slot)
        (afterLeftPath path.reverse left (ulogCore sourceMark)
          (ulogCore stateMark :: stateRest)))
      (.running (.fieldCompare .source slot)
        (beforeRightPath path (ulogCore sourceMark :: left)
          (ulogCore stateMark) stateRest)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases he : path with
      | nil => exact (hp he).elim
      | cons x xs => simpa [afterLeftPath, beforeRightPath, he,
          List.append_assoc] using
          (compareReturnSource_mark slot left x
            (xs ++ ulogCore stateMark :: stateRest))
    · cases slot <;>
        simp [afterLeftPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  let hall := (((hstart.append hseekRun).append hturn).append
    hreturnRun).append hend
  exact ⟨_, hall⟩

def stopFree_sourceCompareZeros
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceCompareStart slot remaining done corridor left suffix)
      (sourceCompareAllMarked slot remaining done corridor left suffix) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨0,
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }⟩
  | succ remaining ih =>
      obtain ⟨a, hround⟩ := stopFree_sourceCompareRound slot remaining done
        corridor (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
        (fun x hx => sourceCompareScanPath_return_safe hcorridor hx) left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      obtain ⟨b, htail⟩ := ih (done + 1) (ulogCore sourceMark :: left)
      have htail' : StopFreeValidZeroRun b
          (.running (.fieldCompare .source slot)
            (beforeRightPath (sourceCompareScanPath remaining corridor done)
              (ulogCore sourceMark :: left) (ulogCore stateMark)
              (List.replicate remaining (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)))
          (sourceCompareAllMarked slot remaining (done + 1) corridor
            (ulogCore sourceMark :: left) suffix) := by
        cases remaining <;>
          simpa [sourceCompareStart, sourceCompareScanPath, beforeRightPath,
            List.replicate_succ, List.replicate_succ',
            List.append_assoc] using htail
      have hall := hround.append htail'
      exact ⟨a + b, by
        simpa [sourceCompareStart, sourceCompareAllMarked,
          sourceCompareScanPath, List.replicate_succ,
          List.replicate_succ', List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hall⟩

theorem stopFree_sourceMatchRestoredAt_nonempty
    (slot : Bool) (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (base suffix : List Tape) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceCompareStart slot q 0 corridor (ulogCore boundary :: base) suffix)
      (sourceFieldRestoredAt slot q boundary base corridor suffix)) := by
  obtain ⟨a, hzeros⟩ := stopFree_sourceCompareZeros slot q 0 corridor
    hcorridor (ulogCore boundary :: base) suffix
  let finishPath := sourceFinishPath q corridor
  let restorePath := sourceRestorePath q corridor
  have hstart : StopFreeValidZeroRun 1
      (sourceCompareAllMarked slot q 0 corridor
        (ulogCore boundary :: base) suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      rw [show sourceCompareAllMarked slot q 0 corridor
            (ulogCore boundary :: base) suffix =
          .running (.fieldCompare .source slot)
            ⟨List.replicate q (ulogCore sourceMark) ++
                ulogCore boundary :: base,
              ulogCore codeOne, finishPath ++ ulogCore stateOne :: suffix⟩ by
        simp [sourceCompareAllMarked, finishPath, sourceFinishPath]]
      cases he : finishPath with
      | nil => simpa [beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base) (ulogCore stateOne) suffix)
      | cons x xs => simpa [beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base) x
            (xs ++ ulogCore stateOne :: suffix))
    · cases slot <;>
        simp [sourceCompareAllMarked, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hfinishScan := stopFree_rightPath_of (.compareFinishSource slot)
    (by intro h; cases h) finishPath (by
      intro x hx l y r
      unfold finishPath sourceFinishPath at hx
      rcases List.mem_append.mp hx with hc | hs
      · have h := hcorridor x hc
        exact compareFinishSource_pass slot x h.2.2.2.2.2.1 h.1
          h.2.1 h.2.2.1 l y r
      · have heq : x = ulogCore stateMark :=
          (by simpa only [List.mem_replicate] using hs :
            q ≠ 0 ∧ x = ulogCore stateMark).2
        rw [heq]
        exact compareFinishSource_mark slot l y r)
    (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
      ulogCore boundary :: base) (ulogCore stateOne) suffix
  have hturn : StopFreeValidZeroRun 1
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base) (ulogCore stateOne) suffix))
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore boundary)
          (ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [finishPath, restorePath, sourceRestorePath, afterRightPath,
        List.append_assoc] using
        compareFinishSource_one_over_path slot restorePath base
          (ulogCore boundary) suffix
    · cases slot <;>
        simp [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hrestore := stopFree_leftPathMap_of (.compareRestoreSource slot)
    (by intro h; cases h) restorePath restoreSourceCell (by
      intro x hx l y r
      have hsafe := sourceRestorePath_safe q corridor hcorridor
        (by simpa [restorePath] using hx)
      exact compareRestoreSource_step slot x hsafe.1 hsafe.2.1
        hsafe.2.2.1 hsafe.2.2.2 l y r)
    base (ulogCore boundary) (ulogCore stateOne :: suffix)
  have hend : StopFreeValidZeroRun 1
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix)))
      (sourceFieldRestoredAt slot q boundary base corridor suffix) := by
    have hmap : restorePath.reverse.map restoreSourceCell =
        List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
          corridor ++ List.replicate q (ulogCore stateZero) := by
      simpa [restorePath] using sourceRestorePath_map q corridor hcorridor
    rw [show afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix) =
        ⟨base, ulogCore boundary,
          List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
            corridor ++ List.replicate q (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    apply StopFreeValidZeroRun.one
    · rcases hboundary with rfl | rfl | rfl <;> cases q <;>
        apply validStepAt_zero_of_oneStep_running <;>
        simp [sourceFieldRestoredAt, restoredSourceBoundaryTape,
          List.replicate_succ, List.append_assoc,
          compareRestoreSource_boundary, compareRestoreSource_boundaryZero,
          compareRestoreSource_boundaryOne]
    · cases slot <;> cases q <;>
        simp [sourceFieldRestoredAt, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hall := ((((hzeros.append hstart).append hfinishScan).append
    hturn).append hrestore).append hend
  exact ⟨_, hall⟩

noncomputable def stopFree_sourceMatchRestoredAt
    (slot : Bool) (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (base suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceCompareStart slot q 0 corridor (ulogCore boundary :: base) suffix)
      (sourceFieldRestoredAt slot q boundary base corridor suffix) :=
  Classical.choice (stopFree_sourceMatchRestoredAt_nonempty slot q corridor
    hcorridor boundary hboundary base suffix)

noncomputable def stopFree_ruleCursorSourceMatch_read
    (slot : Bool) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base : List Tape) (head : Tape)
    (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead head runtime)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ head :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++ head :: runtime)
        suffix) := by
  rw [atBitsTail_encodeRules_cons_source]
  have hstart : sourceCompareStartAgainst slot r.source r.source 0
        (ruleContinuationCorridor r rs (programToHead ++ head :: runtime))
        (ulogCore boundary :: base) suffix =
      sourceCompareStart slot r.source 0
        (cursorRuleCorridor r rs programToHead head runtime)
        (ulogCore boundary :: base) suffix := by
    cases r.source <;> simp [sourceCompareStartAgainst, sourceCompareStart,
      cursorRuleCorridor, List.append_assoc]
  rw [hstart]
  obtain ⟨a, hmatch⟩ := stopFree_sourceMatchRestoredAt slot r.source
    (cursorRuleCorridor r rs programToHead head runtime) hcorridor boundary
    hboundary base suffix
  have hcorridorEq : cursorRuleCorridor r rs programToHead head runtime =
      codeTape (unaryFieldFirst r.read) ::
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++ head :: runtime) := by
    rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
    cases read <;> simp [cursorRuleCorridor, ruleContinuationCorridor,
      cursorMatchedMovePath, encodedActionPath,
      ULogBytecode.encodeNatField, ULogBytecode.encodeAction,
      encodeMove_eq, moveBits, unaryFieldFirst, List.replicate_succ,
      List.map_append, codeTape, List.append_assoc]
  obtain ⟨b, hread⟩ := stopFree_sourceFieldRestoredAt_read slot r.source
    boundary (unaryFieldFirst r.read) base
    ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
      codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead) ++ head :: runtime)
    suffix
  have hread' := hread
  rw [← hcorridorEq] at hread'
  exact ⟨a + b, hmatch.append hread'⟩

/-- A matched cursor whose target is zero reaches its first concrete stop,
which is accepting. -/
noncomputable def ruleCursorMatchedTargetZero_firstStop
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) (tail : List Tape) :
    Σ z, FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.accepted z) := by
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read r.slot
    boundary hboundary r rs programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: tail) hcorridor
  obtain ⟨b, hreadRun⟩ := stopFree_sourceReadAtValid_actionWrite r.slot
    r.source r.read r.action.write r.action.target boundary r.action.move
    hread base (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: tail) hreadPath
  have hwritePath' : ActionWriteCorridorSafe
      (ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead) := by
    simpa [htarget] using hwritePath
  obtain ⟨z, haction⟩ := actionWriteTargetZero_firstStop r.action.write
    r.source hwrite (readHeadNat r.read)
    (by interval_cases r.read <;> decide)
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) runtime
    hwritePath' (by simpa [List.append_assoc] using htargetPath)
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  have hreadRun' : StopFreeValidZeroRun b
      (sourceReadStartedAt r.slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [htarget] using hreadRun
  have hall := (hsource.append hreadRun').append
    { valid := haction.valid, stop_free := haction.before }
  exact ⟨z, hall.toFirstHit haction.hit⟩

noncomputable def stopFree_ruleCursorMatched_actionWrite
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (hread : r.read < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail)) := by
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read r.slot
    boundary hboundary r rs programToHead base (readHeadNat r.read) runtime
    tail hcorridor
  obtain ⟨b, hreadRun⟩ := stopFree_sourceReadAtValid_actionWrite r.slot
    r.source r.read r.action.write r.action.target boundary r.action.move
    hread base (cursorMatchedMovePath rs programToHead) runtime tail hreadPath
  exact ⟨a + b, hsource.append hreadRun⟩

/-- Exact deterministic content required of one certified mismatch cursor
advance. -/
noncomputable def stopFree_ruleCursorSlotMismatch_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (rs : List ULogBytecode.RuleCode) (hrs : rs ≠ [])
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hrestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read slot boundary
    hboundary r rs programToHead pcBase (readHeadNat r.read) runtime suffix
    hsourceCorridor
  obtain ⟨b, hslotMismatch⟩ := stopFree_sourceReadAtSlotMismatch_boundary
    slot r.source r.read hread boundary pcBase
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead)) runtime suffix hreadScan
  have hsource' := hsource
  rw [hslot] at hsource'
  have hrestore := hsource'.append hslotMismatch
  have htail : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorSlotMismatch_restored slot r hslot rs
        programToHead runtime suffix
      have hrestored' :
          (slotMismatchRestorePath r.source r.read).reverse.map
                restoreMismatchCell ++ codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix =
            (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++
                ULogBytecode.encodeRules rs).map codeTape ++
              (programToHead ++ readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨c, hadvance⟩ := stopFree_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (slotMismatchRestorePath r.source r.read) hrestoreSafe
        (codeTape (!slot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath rs programToHead) ++
          readHeadNat r.read :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
      have hrestoreHe := hrestore
      rw [he] at hrestoreHe
      have hreturn : (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
      have hrestore' : StopFreeValidZeroRun (a + b)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (slotMismatchRestorePath r.source r.read)
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)) := by
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hrestoreHe
      have hall := hrestore'.append hadvance
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hall
      exact ⟨a + b + c, by
        simpa [atBitsTail, he, pcBase, List.reverse_append,
          List.append_assoc] using hall⟩

def stopFree_readHeadMismatch_of
    (slot : Bool) (seekState : State) (hseek : seekState ≠ .cycleStart)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      oneStep (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hmismatch : ∀ left y right,
      oneStep (.running seekState ⟨y :: left, head, right⟩) =
        .running (.restoreRule slot) ⟨left, y, head :: right⟩)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running seekState
        (beforeRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
  have hscan := stopFree_rightPath_of seekState hseek path hpass
    (ulogCore readBoundary :: left) head suffix
  have hend : StopFreeValidZeroRun 1
      (.running seekState
        (afterRightPath path (ulogCore readBoundary :: left) head suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse left (ulogCore readBoundary)
          (head :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : path.reverse with
      | nil => simpa [afterRightPath, beforeLeftPath, hr] using
          (hmismatch left (ulogCore readBoundary) suffix)
      | cons x xs => simpa [afterRightPath, beforeLeftPath, hr,
          List.append_assoc] using
          (hmismatch (xs ++ ulogCore readBoundary :: left) x suffix)
    · cases seekState <;>
        simp_all [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

theorem stopFree_sourceReadAtZero_mismatch_nonempty
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadOne ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 0 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  have hstart : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 0 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [sourceReadStartedAt, readMismatchBaseAt,
        beforeRightPath, fieldCompare_read_zero, codeTape,
        List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      oneStep (.running (.readPhase .seekZero slot)
        ⟨y :: left, actualHead, right⟩) =
      .running (.restoreRule slot) ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekZero_one_mismatch slot l y rr
    · exact readSeekZero_blank_mismatch slot l y rr
  obtain ⟨n, htail⟩ := stopFree_readHeadMismatch_of slot
    (.readPhase .seekZero slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekZero_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 0 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact ⟨⟨1 + n, hstart.append htail⟩⟩

theorem stopFree_sourceReadAtOne_mismatch_nonempty
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 1 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  let counted : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base,
      ulogCore codeOne, path ++ actualHead :: runtime ++
        List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      counted := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [sourceReadStartedAt, counted, fieldCompare_read_more,
        codeTape, List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 counted
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 1 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [counted, readMismatchBaseAt, beforeRightPath,
        readCountOne_done, List.append_assoc]
    · cases slot <;> simp [counted, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      oneStep (.running (.readPhase .seekOne slot)
        ⟨y :: left, actualHead, right⟩) =
      .running (.restoreRule slot) ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekOne_zero_mismatch slot l y rr
    · exact readSeekOne_blank_mismatch slot l y rr
  obtain ⟨n, htail⟩ := stopFree_readHeadMismatch_of slot
    (.readPhase .seekOne slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekOne_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 1 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact ⟨⟨2 + n, (h₀.append h₁).append htail⟩⟩

theorem stopFree_sourceReadAtBlank_mismatch_nonempty
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadOne)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne ::
          path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 2 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  let countedOne : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base,
      ulogCore codeZero, ulogCore codeOne :: path ++ actualHead :: runtime ++
        List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix⟩
  let countedTwo : Result := .running (.readPhase .countTwo slot)
    ⟨ulogCore codeZero :: ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base,
      ulogCore codeOne, path ++ actualHead :: runtime ++
        List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne ::
          path ++ actualHead :: runtime) suffix) countedOne := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [sourceReadStartedAt, countedOne, fieldCompare_read_more,
        codeTape, List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 countedOne countedTwo := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [countedOne, countedTwo, readCountOne_more, List.append_assoc]
    · cases slot <;> simp [countedOne, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have h₂ : StopFreeValidZeroRun 1 countedTwo
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 2 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [countedTwo, readMismatchBaseAt, beforeRightPath,
        readCountTwo_done, List.append_assoc]
    · cases slot <;> simp [countedTwo, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      oneStep (.running (.readPhase .seekBlank slot)
        ⟨y :: left, actualHead, right⟩) =
      .running (.restoreRule slot) ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekBlank_zero_mismatch slot l y rr
    · exact readSeekBlank_one_mismatch slot l y rr
  obtain ⟨n, htail⟩ := stopFree_readHeadMismatch_of slot
    (.readPhase .seekBlank slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekBlank_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 2 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact ⟨⟨3 + n, ((h₀.append h₁).append h₂).append htail⟩⟩

theorem stopFree_sourceReadAtMismatch_boundary_nonempty
    (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          path ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (readMismatchRestorePath source read path)
          base (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  interval_cases read <;> interval_cases actual
  all_goals try omega
  · obtain ⟨h⟩ := stopFree_sourceReadAtZero_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadOne) (Or.inl rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩
  · obtain ⟨h⟩ := stopFree_sourceReadAtZero_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩
  · obtain ⟨h⟩ := stopFree_sourceReadAtOne_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩
  · obtain ⟨h⟩ := stopFree_sourceReadAtOne_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩
  · obtain ⟨h⟩ := stopFree_sourceReadAtBlank_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩
  · obtain ⟨h⟩ := stopFree_sourceReadAtBlank_mismatch_nonempty slot source
      boundary base path runtime suffix (ulogCore payloadHeadOne) (Or.inr rfl) hsafe
    rw [readMismatch_beforeLeft_eq] at h
    exact ⟨by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
      readHeadNat, codeTape, List.append_assoc] using h⟩

noncomputable def stopFree_sourceReadAtMismatch_boundary
    (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe path) :
    Σ n, StopFreeValidZeroRun n
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          path ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (readMismatchRestorePath source read path)
          base (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) :=
  Classical.choice (stopFree_sourceReadAtMismatch_boundary_nonempty slot source
    read actual hread hactual hne boundary base path runtime suffix hsafe)

noncomputable def stopFree_ruleCursorReadMismatch_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programToHead : List Tape) (actual : ℕ)
    (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r rs programToHead))
    (hrestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read slot boundary
    hboundary r rs programToHead pcBase (readHeadNat actual) runtime suffix
    hsourceCorridor
  obtain ⟨b, hreadMismatch⟩ := stopFree_sourceReadAtMismatch_boundary
    slot r.source r.read actual hread hactual hreadNe boundary pcBase
    (cursorReadScanPath r rs programToHead) runtime suffix hreadScan
  have hrestore := hsource.append hreadMismatch
  have htail : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorReadMismatch_restored r rs programToHead
        runtime suffix actual hrestoreIdentity
      have hrestored' :
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r rs programToHead)).reverse.map
              restoreMismatchCell ++
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix) =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++
                ULogBytecode.encodeRules rs).map codeTape ++
              (programToHead ++ readHeadNat actual :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨c, hadvance⟩ := stopFree_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (readMismatchRestorePath r.source r.read
          (cursorReadScanPath r rs programToHead)) hrestoreSafe
        (readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
      have hreturn : (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
      have hrestoreHe := hrestore
      rw [he] at hrestoreHe
      have hrestore' : StopFreeValidZeroRun (a + b)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (readMismatchRestorePath r.source r.read
              (cursorReadScanPath r rs programToHead))
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)) := by
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hrestoreHe
      have hall := hrestore'.append hadvance
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hall
      exact ⟨a + b + c, by
        simpa [atBitsTail, he, pcBase, List.reverse_append,
          List.append_assoc] using hall⟩

def stopFree_sourceCompareCommon
    (slot : Bool) (source current done : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceCompareStartAgainst slot source current done corridor left suffix)
      (sourceCompareStartAgainst slot (source - current) (current - source)
        (done + min source current) corridor
        (List.replicate (min source current) (ulogCore sourceMark) ++ left)
        suffix) := by
  induction source generalizing current done left with
  | zero =>
      have h : StopFreeValidZeroRun 0
          (sourceCompareStartAgainst slot 0 current done corridor left suffix)
          (sourceCompareStartAgainst slot 0 current done corridor left suffix) :=
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }
      exact ⟨0, by simpa using h⟩
  | succ source ih =>
      cases current with
      | zero =>
          have h : StopFreeValidZeroRun 0
              (sourceCompareStartAgainst slot (source + 1) 0 done corridor
                left suffix)
              (sourceCompareStartAgainst slot (source + 1) 0 done corridor
                left suffix) :=
            { valid := .nil _
              stop_free := by intro m hm; simp at hm }
          exact ⟨0, by simpa using h⟩
      | succ current =>
          obtain ⟨a, hround⟩ := stopFree_sourceCompareRound slot source done
            corridor (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
            (fun x hx => sourceCompareScanPath_return_safe hcorridor hx) left
            (List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
          obtain ⟨b, htail⟩ := ih current (done + 1)
            (ulogCore sourceMark :: left)
          have hround' : StopFreeValidZeroRun a
              (sourceCompareStartAgainst slot (source + 1) (current + 1)
                done corridor left suffix)
              (sourceCompareStartAgainst slot source current (done + 1)
                corridor (ulogCore sourceMark :: left) suffix) := by
            cases source <;> cases current <;>
              simpa [sourceCompareStartAgainst, sourceCompareScanPath,
                beforeRightPath, List.replicate_succ,
                List.replicate_succ', Nat.add_comm, Nat.add_left_comm,
                List.append_assoc] using hround
          have hall := hround'.append htail
          exact ⟨a + b, by
            simpa [Nat.succ_sub_succ_eq_sub, List.replicate_succ,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              List.append_assoc] using hall⟩

def stopFree_sourceShortMismatch_restore
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceCompareStartAgainst slot 0 (extra + 1) done corridor
        (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceShortRestorePath done corridor)
          pcBase boundary
          (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  let finishPath := sourceShortFinishPath done corridor
  have hstart : StopFreeValidZeroRun 1
      (sourceCompareStartAgainst slot 0 (extra + 1) done corridor
        (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
        suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne :: List.replicate done (ulogCore sourceMark) ++
            boundary :: pcBase) (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      unfold sourceCompareStartAgainst
      rw [show corridor ++ List.replicate done (ulogCore stateMark) =
        finishPath by rfl, List.replicate_succ]
      cases he : finishPath with
      | nil => simpa [beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
            (ulogCore stateZero)
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
      | cons x xs => simpa [beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
            x (xs ++ ulogCore stateZero ::
              List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))
    · cases slot <;> simp [sourceCompareStartAgainst,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan := stopFree_rightPath_of (.compareFinishSource slot)
    (by intro h; cases h) finishPath (by
      intro x hx l y r
      exact sourceShortFinishPath_pass slot done corridor hcorridor x
        (by simpa [finishPath] using hx) l y r)
    (ulogCore codeOne :: List.replicate done (ulogCore sourceMark) ++
      boundary :: pcBase) (ulogCore stateZero)
    (List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hend : StopFreeValidZeroRun 1
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne :: List.replicate done (ulogCore sourceMark) ++
            boundary :: pcBase) (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceShortRestorePath done corridor)
          pcBase boundary
          (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : finishPath.reverse with
      | nil => simpa [afterRightPath, beforeLeftPath,
          sourceShortRestorePath, finishPath, hr, List.append_assoc] using
          (compareFinishSource_zero_mismatch slot
            (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
            (ulogCore codeOne)
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
      | cons x xs => simpa [afterRightPath, beforeLeftPath,
          sourceShortRestorePath, finishPath, hr, List.append_assoc] using
          (compareFinishSource_zero_mismatch slot
            (xs ++ ulogCore codeOne ::
              List.replicate done (ulogCore sourceMark) ++
                boundary :: pcBase) x
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
    · cases slot <;> simp [afterRightPath,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact ⟨_, (hstart.append hscan).append hend⟩

def stopFree_sourceLongMismatch_restore
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (sourceCompareStartAgainst slot extra.succ 0 done corridor
        (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceLongRestorePath extra done corridor)
          pcBase boundary (ulogCore stateOne :: suffix))) := by
  let seekPath := sourceLongSeekPath extra done corridor
  have hstart : StopFreeValidZeroRun 1
      (sourceCompareStartAgainst slot extra.succ 0 done corridor
        (List.replicate done (ulogCore sourceMark) ++ boundary :: pcBase)
        suffix)
      (.running (.compareSeekState slot)
        (beforeRightPath seekPath
          (ulogCore sourceMark :: List.replicate done (ulogCore sourceMark) ++
            boundary :: pcBase) (ulogCore stateOne) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      unfold sourceCompareStartAgainst
      cases he : seekPath with
      | nil =>
          have hne : seekPath ≠ [] := by
            simp [seekPath, sourceLongSeekPath, sourceCompareScanPath]
          exact (hne he).elim
      | cons x xs =>
          have hseekEq : sourceCompareScanPath extra corridor done = x :: xs := by
            simpa [seekPath, sourceLongSeekPath] using he
          simp only [sourceCompareStartAgainst]
          rw [hseekEq]
          simpa [beforeRightPath, List.append_assoc] using
            (fieldCompare_source_zero slot
              (List.replicate done (ulogCore sourceMark) ++
                boundary :: pcBase) x (xs ++ ulogCore stateOne :: suffix))
    · cases slot <;> simp [sourceCompareStartAgainst,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan := stopFree_rightPath_of (.compareSeekState slot)
    (by intro h; cases h) seekPath (by
      intro x hx l y r
      have hs := sourceCompareScanPath_seek_safe hcorridor
        (by simpa [seekPath, sourceLongSeekPath] using hx)
      exact compareSeekState_pass slot x hs.1 hs.2.1 hs.2.2 l y r)
    (ulogCore sourceMark :: List.replicate done (ulogCore sourceMark) ++
      boundary :: pcBase) (ulogCore stateOne) suffix
  have hend : StopFreeValidZeroRun 1
      (.running (.compareSeekState slot)
        (afterRightPath seekPath
          (ulogCore sourceMark :: List.replicate done (ulogCore sourceMark) ++
            boundary :: pcBase) (ulogCore stateOne) suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceLongRestorePath extra done corridor)
          pcBase boundary (ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hne : seekPath ≠ [] := by
        simp [seekPath, sourceLongSeekPath, sourceCompareScanPath]
      cases hr : seekPath.reverse with
      | nil =>
          have he : seekPath = [] := by simpa using congrArg List.reverse hr
          exact (hne he).elim
      | cons x xs =>
          have hrevEq : (sourceCompareScanPath extra corridor done).reverse =
              x :: xs := by simpa [seekPath, sourceLongSeekPath] using hr
          simp only [afterRightPath]
          rw [hr]
          unfold sourceLongRestorePath sourceLongSeekPath
          rw [hrevEq]
          simpa [beforeLeftPath, List.append_assoc] using
            (compareSeekState_one_mismatch slot
              (xs ++ ulogCore sourceMark ::
                List.replicate done (ulogCore sourceMark) ++
                  boundary :: pcBase) x suffix)
    · cases slot <;> simp [afterRightPath,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact ⟨_, (hstart.append hscan).append hend⟩

noncomputable def stopFree_atBitsSourceShort_restore
    (slot : Bool) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programPath : List Tape)
    (extra : ℕ) (boundary : ULogLetter) (pcBase suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary)
          (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  rw [atBitsTail_encodeRules_cons_source]
  obtain ⟨a, hcommon⟩ := stopFree_sourceCompareCommon slot r.source
    (r.source + extra + 1) 0 (ruleContinuationCorridor r rs programPath)
    hcorridor (ulogCore boundary :: pcBase) suffix
  have hcommon' : StopFreeValidZeroRun a
      (sourceCompareStartAgainst slot r.source (r.source + extra + 1) 0
        (ruleContinuationCorridor r rs programPath)
        (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (ruleContinuationCorridor r rs programPath)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa [Nat.min_eq_left, Nat.add_assoc] using hcommon
  obtain ⟨b, hmismatch⟩ := stopFree_sourceShortMismatch_restore slot
    r.source extra (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary) pcBase suffix
  have hmismatch' : StopFreeValidZeroRun b
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source
        (ruleContinuationCorridor r rs programPath)
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary)
          (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    simpa [List.append_assoc] using hmismatch
  exact ⟨a + b, hcommon'.append hmismatch'⟩

noncomputable def stopFree_atBitsSourceLong_restore
    (slot : Bool) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programPath : List Tape)
    (current extra : ℕ) (hsource : r.source = current + extra + 1)
    (boundary : ULogLetter) (pcBase suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
  rw [atBitsTail_encodeRules_cons_source]
  obtain ⟨a, hcommon⟩ := stopFree_sourceCompareCommon slot r.source current
    0 (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary :: pcBase) suffix
  have hcommon' : StopFreeValidZeroRun a
      (sourceCompareStartAgainst slot r.source current 0
        (ruleContinuationCorridor r rs programPath)
        (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (ruleContinuationCorridor r rs programPath)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa [hsource, Nat.min_eq_right, Nat.add_assoc] using hcommon
  obtain ⟨b, hmismatch⟩ := stopFree_sourceLongMismatch_restore slot
    current extra (ruleContinuationCorridor r rs programPath) hcorridor
    (ulogCore boundary) pcBase suffix
  have hmismatch' : StopFreeValidZeroRun b
      (sourceCompareStartAgainst slot (extra + 1) 0 current
        (ruleContinuationCorridor r rs programPath)
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r rs programPath))
          pcBase (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
    simpa [Nat.succ_eq_add_one, List.append_assoc] using hmismatch
  exact ⟨a + b, hcommon'.append hmismatch'⟩

noncomputable def stopFree_ruleCursorSourceShort_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)) := by
  let pcBase := (List.replicate done (ulogCore codeZero) ++
    ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
      ulogCore pcMark :: outer
  obtain ⟨a, hrestore⟩ := stopFree_atBitsSourceShort_restore slot r rs
    programPath extra boundary pcBase suffix hcorridor
  have htail : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := ruleSourceShort_restored r rs programPath suffix extra
        hcorridor hreadBoundary
      have hrestored' :
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r rs programPath)).reverse.map
              restoreMismatchCell ++
            (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have hafter' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ (programPath ++
                List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using hafter'
      obtain ⟨b, hadvance⟩ := stopFree_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (sourceShortRestorePath r.source
          (ruleContinuationCorridor r rs programPath))
        (sourceShortRestorePath_safe r.source
          (ruleContinuationCorridor r rs programPath) hcorridor)
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
      have hrestoreHe := hrestore
      rw [he] at hrestoreHe
      have hreturn : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
      have hrestore' : StopFreeValidZeroRun a
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (sourceShortRestorePath r.source
              (ruleContinuationCorridor r rs programPath))
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)) := by
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs => simpa [pcBase, restoreAdvanceStarted, hret,
            beforeLeftPath, List.append_assoc] using hrestoreHe
      have hall := hrestore'.append hadvance
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hall
      exact ⟨a + b, by
        simpa [atBitsTail, he, pcBase, List.reverse_append,
          List.append_assoc] using hall⟩

noncomputable def stopFree_ruleCursorSourceLong_step
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  let pcBase := (List.replicate done (ulogCore codeZero) ++
    ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
      ulogCore pcMark :: outer
  obtain ⟨a, hrestore⟩ := stopFree_atBitsSourceLong_restore slot r rs
    programPath current extra hsource boundary pcBase suffix hcorridor
  have htail : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := ruleSourceLong_restored r rs programPath suffix
        current extra hsource hcorridor hreadBoundary
      have hrestored' :
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r rs programPath)).reverse.map
              restoreMismatchCell ++ ulogCore stateOne :: suffix =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have hafter' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ (programPath ++
                List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using hafter'
      obtain ⟨b, hadvance⟩ := stopFree_restoreMismatchAdvanceRule slot done
        (ulogCore pcDone :: path) hpath boundary hboundary
        (sourceLongRestorePath extra current
          (ruleContinuationCorridor r rs programPath))
        (sourceLongRestorePath_safe extra current
          (ruleContinuationCorridor r rs programPath) hcorridor)
        (ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
      have hrestoreHe := hrestore
      rw [he] at hrestoreHe
      have hreturn : (List.replicate done (ulogCore codeZero) ++
        ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
      have hrestore' : StopFreeValidZeroRun a
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (sourceLongRestorePath extra current
              (ruleContinuationCorridor r rs programPath))
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary (ulogCore stateOne :: suffix)) := by
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs => simpa [pcBase, restoreAdvanceStarted, hret,
            beforeLeftPath, List.append_assoc] using hrestoreHe
      have hall := hrestore'.append hadvance
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      rw [hleft] at hall
      exact ⟨a + b, by
        simpa [atBitsTail, he, pcBase, List.reverse_append,
          List.append_assoc] using hall⟩

def CursorMismatchStopFreeStep : Prop :=
  ∀ (slot : Bool) (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape)
    (ready : CursorMismatchReady slot current actual c r rs
      programToHead runtime),
    Nonempty (Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual c (r :: rs)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual
        (advanceRuleCursor c r ready.tail) rs
        programToHead runtime outer suffix))

/-- All four concrete mismatch cases discharge the local stop-free cursor
advance obligation. -/
theorem cursorMismatchStopFreeStep : CursorMismatchStopFreeStep := by
  intro slot current actual c r rs programToHead runtime outer suffix ready
  by_cases hsource : r.source = current
  · by_cases hread : r.read = actual
    · have hslotNe : r.slot ≠ slot := by
        intro hs
        exact ready.mismatch ⟨hsource, hread, hs⟩
      have hslot : r.slot = !slot := by
        cases hr : r.slot <;> cases hs : slot <;> simp_all
      let h := stopFree_ruleCursorSlotMismatch_step slot c.done ready.tail
        ready.path_safe c.boundary ready.boundary_valid r hslot rs
        ready.remaining_ne programToHead ready.read_valid runtime outer suffix
        (by simpa [hread] using ready.source_corridor)
        (by simpa [hslot] using ready.slot_scan)
        (by simpa [hsource, hread] using ready.slot_restore)
      exact ⟨by
        simpa [ruleCursorResult, ruleCursorBase, advanceRuleCursor,
          ready.path_eq, hsource, hread, List.append_assoc] using h⟩
    · let h := stopFree_ruleCursorReadMismatch_step slot c.done ready.tail
        ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne programToHead actual ready.read_valid
        ready.actual_valid hread runtime outer suffix ready.source_corridor
        ready.read_scan ready.read_restore ready.program_restore
      exact ⟨by
        simpa [ruleCursorResult, ruleCursorBase, advanceRuleCursor,
          ready.path_eq, hsource, List.append_assoc] using h⟩
  · by_cases hlt : r.source < current
    · obtain ⟨extra, hcurrent⟩ : ∃ extra,
          current = r.source + extra + 1 :=
        ⟨current - r.source - 1, by omega⟩
      let h := stopFree_ruleCursorSourceShort_step slot c.done ready.tail
        ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne (programToHead ++ readHeadNat actual :: runtime)
        extra outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.source_corridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.read_boundary_free)
      exact ⟨by
        simpa [ruleCursorResult, ruleCursorBase, advanceRuleCursor,
          ready.path_eq, hcurrent, List.append_assoc] using h⟩
    · have hcurLt : current < r.source := by omega
      obtain ⟨extra, hrsource⟩ : ∃ extra,
          r.source = current + extra + 1 :=
        ⟨r.source - current - 1, by omega⟩
      let h := stopFree_ruleCursorSourceLong_step slot c.done ready.tail
        ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne (programToHead ++ readHeadNat actual :: runtime)
        current extra hrsource outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.source_corridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.read_boundary_free)
      exact ⟨by
        simpa [ruleCursorResult, ruleCursorBase, advanceRuleCursor,
          ready.path_eq, List.append_assoc] using h⟩

/-- Once the four mismatch cases discharge the preceding local interface,
an arbitrary certified mismatch prefix folds to one stop-free run. -/
theorem stopFree_mismatchPrefix_nonempty
    (stepExact : CursorMismatchStopFreeStep)
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final) :
    Nonempty (Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix)) := by
  induction trace with
  | nil c rest =>
      exact ⟨⟨0,
        { valid := .nil _
          stop_free := by intro m hm; simp at hm }⟩⟩
  | cons c r skip rest final ready next ih =>
      obtain ⟨⟨a, hstep⟩⟩ := stepExact slot current actual c r
        (skip ++ rest) programToHead runtime outer suffix ready
      obtain ⟨⟨b, htail⟩⟩ := ih
      exact ⟨⟨a + b, hstep.append htail⟩⟩

noncomputable def stopFree_mismatchPrefix
    (stepExact : CursorMismatchStopFreeStep)
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix) :=
  Classical.choice (stopFree_mismatchPrefix_nonempty stepExact slot current
    actual programToHead runtime outer suffix trace)

theorem branchedCycle_semanticTargetZero_exact_nonempty
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 0)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) :
    Nonempty (Σ z, ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) (.accepted z)) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> decide
  let choiceLeft := dynamicRuleReturnPath (c.leftRev.map payloadNat)
    (skip ++ r :: rs) input ++ ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix
  have hchoice := clockDecrementCells_firstChoice (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    choiceLeft
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) := by
    simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
      clockCellsAfter, heq, choiceLeft, choiceRight,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot
    (c.leftRev.map payloadNat) (payloadNatList_safe c.leftRev)
    (skip ++ r :: rs) (by simp) input outer (readHeadNat c.focus) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
            input) outer (ulogCore pcMark) (readHeadNat c.focus :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil (c.leftRev.map payloadNat)
      (skip ++ r :: rs) input
    cases hePath : dynamicRuleReturnPath (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input with
    | nil => exact (hpne hePath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  obtain ⟨b, hmismatch⟩ := stopFree_mismatchPrefix
    cursorMismatchStopFreeStep slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix))
    trace
  have hmismatch' := hmismatch
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot c.state c.focus
    (c.leftRev.map payloadNat) input skip r rs
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix))] at hmismatch'
  have hmismatch'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight)
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) := by
    simpa [choiceRight, List.append_assoc] using hmismatch'
  obtain ⟨z, hmatched⟩ := ruleCursorMatchedTargetZero_firstStop
    (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
        (ulogCore codeZero) ++
      ulogCore pcDone :: (canonicalRuleCursor skip (r :: rs)).path).reverse ++
        ulogCore pcMark :: outer)
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    htarget rscan.read_valid hwrite
    (by simpa [hmatch.2.1] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by simpa [htarget] using
      (matchedWritePath_safe r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hmatched' : FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) (.accepted z) := by
    simpa [ruleCursorResult, ruleCursorBase, hmatch.1, hmatch.2.1,
      hmatch.2.2, List.append_assoc] using hmatched
  have hsuffix := (hdynamic'.append hmismatch'').append
    ({ valid := hmatched'.valid
       stop_free := hmatched'.before } : StopFreeValidZeroRun
        hmatched'.steps _ (.accepted z))
  have hsuffix' : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      (.accepted z) := by
    exact hsuffix.toFirstHit hmatched'.hit
  exact ⟨⟨z, exactConcreteCycleOfChoiceHead choiceLeft
    (readHeadNat c.focus) choiceRight hhead hchoice' hsuffix'⟩⟩

/-- Write-zero specialization composed all the way through the target-zero
accepting terminal. -/
def actionWriteZero_targetZero_firstStop
    (current : ℕ) (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (corridor : List Tape) (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeOne :: corridor))
    (htargetPath : TargetRewriteCorridorSafe
      (corridor ++ [ulogCore payloadHeadZero]))
    (left tail : List Tape) :
    Σ z, FirstValidZeroHit IsConcreteCycleStop
      (.running .actionWrite
        ⟨left, ulogCore codeOne,
          ulogCore codeOne :: corridor ++ oldHead ::
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.accepted z) := by
  let suffix := oldHead :: List.replicate current (ulogCore stateZero) ++
    ulogCore stateOne :: ulogCore stateSep :: tail
  obtain ⟨n, hwrite⟩ := stopFree_actionWriteZero oldHead hhead
    (ulogCore codeOne :: corridor) hwritePath left
    (List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  obtain ⟨z, htarget⟩ := targetRawZero_firstStop current
    (corridor ++ [ulogCore payloadHeadZero]) htargetPath
    (ulogCore codeOne :: left) tail
  have hwrite' : StopFreeValidZeroRun n
      (.running .actionWrite
        ⟨left, ulogCore codeOne,
          ulogCore codeOne :: corridor ++ oldHead ::
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (targetRawStart 0 current (corridor ++ [ulogCore payloadHeadZero])
        (ulogCore codeOne :: left) tail) := by
    simpa [targetRawStart, beforeRightPath, List.append_assoc] using hwrite
  exact ⟨z,
    (hwrite'.append
      { valid := htarget.valid
        stop_free := htarget.before }).toFirstHit htarget.hit⟩

/-- A concrete word-indexed run whose every simulated cycle uses the exact
first-hit decomposition. -/
inductive ExactConcreteSlotRun : Result → List Bool → Result → Prop
  | nil (r : Result) : ExactConcreteSlotRun r [] r
  | cons (start next finish : Result) (slot : Bool) (slots : List Bool)
      (cycle : ExactConcreteCycle slot start next)
      (tail : ExactConcreteSlotRun next slots finish) :
      ExactConcreteSlotRun start (slot :: slots) finish

/-- A slot run starting at any concrete terminal has no labelled cycles.
Consequently an accepting-cycle endpoint cannot carry a hidden tail, and a
rejecting endpoint cannot later recover into an accepting result. -/
theorem ExactConcreteSlotRun.eq_nil_of_concreteHalted_start
    {start finish : Result} {slots : List Bool}
    (h : ExactConcreteSlotRun start slots finish)
    (hstart : concreteHalted start = true) :
    slots = [] ∧ finish = start := by
  cases h with
  | nil r => exact ⟨rfl, rfl⟩
  | cons start next finish slot slots cycle tail =>
      exact (cycle.false_of_concreteHalted_start hstart).elim

theorem ExactConcreteSlotRun.finish_unique
    {start finish₁ finish₂ : Result} {slots : List Bool}
    (h₁ : ExactConcreteSlotRun start slots finish₁)
    (h₂ : ExactConcreteSlotRun start slots finish₂) :
    finish₁ = finish₂ := by
  induction h₁ generalizing finish₂ with
  | nil r =>
      cases h₂
      rfl
  | cons start next finish slot slots hcycle htail ih =>
      cases h₂ with
      | cons _ next₂ finish₂ _ _ hcycle₂ htail₂ =>
          have hnext : next = next₂ := hcycle.finish_unique hcycle₂
          subst next₂
          exact ih htail₂

/-- Forgetting the cycle labels yields an ordinary path through
`concreteMachine.next`. -/
theorem ExactConcreteSlotRun.toMachinePath
    {start finish : Result} {slots : List Bool}
    (h : ExactConcreteSlotRun start slots finish) :
    ∃ states, ConcreteMachinePath start states finish := by
  induction h with
  | nil r => exact ⟨[], .nil r⟩
  | cons start next finish slot slots hcycle htail ih =>
      obtain ⟨cycleStates, hcycleStates⟩ := hcycle.toMachinePath
      obtain ⟨tailStates, htailStates⟩ := ih
      exact ⟨cycleStates ++ tailStates,
        hcycleStates.append htailStates⟩

/-- Actual accepting first-hit executions, with no semantic membership baked
into the definition. -/
def ExactConcreteAcceptingSlotTrace
    (start : Result) (slots : List Bool) : Prop :=
  ∃ finish, ExactConcreteSlotRun start slots finish ∧
    concreteAccepting finish = true

/-- Concrete accepting words with a cycle-label budget.  This subtype is
genuinely concrete: it mentions neither semantic configurations nor semantic
accepting-word membership. -/
def ExactConcreteAcceptingWords
    (t : ℕ) (start : Result) : Type :=
  { slots : List Bool // slots.length ≤ t ∧
    ExactConcreteAcceptingSlotTrace start slots }

/-- For a fixed word, a first-hit concrete execution has a unique terminal
configuration. -/
theorem exactConcreteAcceptingSlotTrace_terminal_unique
    {start : Result} {slots : List Bool} {finish₁ finish₂ : Result}
    (h₁ : ExactConcreteSlotRun start slots finish₁)
    (h₂ : ExactConcreteSlotRun start slots finish₂)
    (_ : concreteAccepting finish₁ = true)
    (_ : concreteAccepting finish₂ = true) : finish₁ = finish₂ :=
  h₁.finish_unique h₂

/-- `BranchedReaches` really can hide a completed slot-zero cycle in the
prefix of a later labelled cycle.  This closure property is exactly why it
cannot serve as the path type of the converse counting argument. -/
theorem branchedReaches_false_to_reaches
    {start finish : Result} (h : BranchedReaches false start finish) :
    Reaches start finish := by
  rcases h with ⟨choice, branch, hprefix, hselected, hsuffix⟩
  have hstep : Reaches choice branch := reaches_step (by
    rw [oneStep_eq_slot_zero]
    simpa [ULogBytecode.slotIndex] using hselected)
  exact reaches_trans hprefix (reaches_trans hstep hsuffix)

theorem branchedReaches_can_hide_prior_zero_cycle
    {start middle finish : Result} {slot : Bool}
    (hprior : BranchedReaches false start middle)
    (hlater : BranchedReaches slot middle finish) :
    BranchedReaches slot start finish := by
  rcases hlater with ⟨choice, branch, hprefix, hselected, hsuffix⟩
  exact ⟨choice, branch,
    reaches_trans (branchedReaches_false_to_reaches hprior) hprefix,
    hselected, hsuffix⟩

/-! ## Exact resource refinement

The following two local interfaces are the precise obligations needed to
upgrade the existing forward simulation to a converse-safe one.  They demand
an `ExactConcreteCycle`, so neither can be discharged by handing back an
unrestricted `BranchedReaches` witness.
-/

/-- The data produced by an exact realization of a nonhalting semantic
successor. -/
structure ExactContinuationWitness
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (c' : ULogSemantics.Config) : Type where
  action : ULogBytecode.ActionCode
  action_eq : ULogSemantics.applyAction frame.config action = c'
  reframe : ClockReframe
    ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
    (clockCellsAfter
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime)
  next_ready : FrameReady (frame.reframeNext action reframe)
  exact_cycle : ExactConcreteCycle slot frame.encode
    (frame.reframeNext action reframe).encode

/-- Exact realization of a nonhalting semantic successor, including the next
resource frame.  This is data-valued because its first-hit certificate carries
the concrete choice, branch, and stopping times. -/
def ExactResourceContinuationRefinement
    {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (ready : FrameReady frame) (c' : ULogSemantics.Config),
    ULogSemantics.stepSlot slot frame.config = some c' →
      ULogSemantics.accepting c' = false →
      ULogSemantics.halted c' = false →
        ExactContinuationWitness frame slot c'

/-- The data produced by an exact accepting cycle. -/
structure ExactAcceptingWitness
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool) : Type where
  tape : Zipper Tape
  exact_cycle : ExactConcreteCycle slot frame.encode (.accepted tape)

/-- Exact realization of a semantic step whose successor accepts. -/
def ExactAcceptingCycleRefinement
    {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (ready : FrameReady frame) (c' : ULogSemantics.Config),
    ULogSemantics.stepSlot slot frame.config = some c' →
      ULogSemantics.accepting c' = true →
        ExactAcceptingWitness frame slot

theorem exactAcceptingCycleWitness_nonempty
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame) (c' : ULogSemantics.Config)
    (hstep : ULogSemantics.stepSlot slot frame.config = some c')
    (haccept : ULogSemantics.accepting c' = true) :
    Nonempty (ExactAcceptingWitness frame slot) := by
  obtain ⟨_, action, hlookup, haction⟩ :=
    ULogSemantics.stepSlot_some_rule hstep
  have hacceptAction : ULogSemantics.accepting
      (ULogSemantics.applyAction frame.config action) = true := by
    simpa [haction] using haccept
  have htarget : action.target = 0 :=
    (accepting_applyAction_iff_target_zero frame.config action).mp hacceptAction
  obtain ⟨⟨z, hcycle⟩⟩ := branchedCycle_semanticTargetZero_exact_nonempty
    frame.config slot action hlookup htarget input frame.clockZeros
    frame.capacity frame.runtime frame.outer suffix ready.runtime_passive
    ready.focus_lt_three ready.reads_lt_three ready.writes_lt_three
    ready.state_le_capacity
  exact ⟨
    { tape := z
      exact_cycle := by
        simpa [SemanticCycleFrame.encode] using hcycle }⟩

/-- Fully concrete accepting-cycle refinement; no continuation or semantic
membership oracle remains. -/
noncomputable def exactAcceptingCycleRefinement
    {input : List Bool} {suffix : List Tape} :
    ExactAcceptingCycleRefinement (input := input) (suffix := suffix) :=
  fun frame slot ready c' hstep haccept =>
    Classical.choice
      (exactAcceptingCycleWitness_nonempty frame slot ready c' hstep haccept)

/-- First converse ingredient: semantic acceptance determines the outcome of
every exact concrete cycle with the same frame and label, not only the
canonical witness constructed above. -/
theorem exactConcreteCycle_finish_eq_accepting_of_semantic
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame) (c' : ULogSemantics.Config)
    (hstep : ULogSemantics.stepSlot slot frame.config = some c')
    (haccept : ULogSemantics.accepting c' = true)
    {finish : Result} (runExact : ExactConcreteCycle slot frame.encode finish) :
    finish = .accepted
      (exactAcceptingCycleRefinement frame slot ready c' hstep haccept).tape := by
  exact runExact.finish_unique
    (exactAcceptingCycleRefinement frame slot ready c' hstep haccept).exact_cycle

theorem exactConcreteCycle_accepting_of_semantic
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (ready : FrameReady frame) (c' : ULogSemantics.Config)
    (hstep : ULogSemantics.stepSlot slot frame.config = some c')
    (haccept : ULogSemantics.accepting c' = true)
    {finish : Result} (runExact : ExactConcreteCycle slot frame.encode finish) :
    concreteAccepting finish = true := by
  rw [exactConcreteCycle_finish_eq_accepting_of_semantic frame slot ready c'
    hstep haccept runExact]
  rfl

def stopFree_actionMove
    (m : OneTapeTableau.Move) (left : List Tape)
    (y : Tape) (right : List Tape) :
    StopFreeValidZeroRun 2
      (.running (.actionPhase .moveStart)
        ⟨left, codeTape (moveFirst m), codeTape (moveSecond m) :: y :: right⟩)
      (.running (.moveSimHead m)
        ⟨codeTape (moveSecond m) :: codeTape (moveFirst m) :: left,
          y, right⟩) := by
  let middle : Result := .running
    (if moveFirst m then .actionPhase .moveAfterOne
      else .actionPhase .moveAfterZero)
    ⟨codeTape (moveFirst m) :: left, codeTape (moveSecond m), y :: right⟩
  have h₀ : StopFreeValidZeroRun 1
      (.running (.actionPhase .moveStart)
        ⟨left, codeTape (moveFirst m), codeTape (moveSecond m) :: y :: right⟩)
      middle := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [middle] using actionMoveStart_bit (moveFirst m) left
        (codeTape (moveSecond m)) (y :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 middle
      (.running (.moveSimHead m)
        ⟨codeTape (moveSecond m) :: codeTape (moveFirst m) :: left,
          y, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [middle] using actionMoveSecond m
        (codeTape (moveFirst m) :: left) y right
    · cases m <;> simp [middle, moveFirst, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  exact h₀.append h₁

def stopFree_moveScan
    (m : OneTapeTableau.Move) (path : List Tape)
    (hsafe : MoveScanSafe path) (left : List Tape)
    (head : Tape) (right : List Tape) :
    StopFreeValidZeroRun path.length
      (.running (.moveSimHead m) (beforeRightPath path left head right))
      (.running (.moveSimHead m) (afterRightPath path left head right)) :=
  stopFree_rightPath_of (.moveSimHead m) (by intro h; cases h) path
    (fun x hx l y r =>
      moveSimHead_pass m x (hsafe x hx).1 (hsafe x hx).2 l y r)
    left head right

def stopFree_moveStay
    (path : List Tape) (hsafe : MoveScanSafe path)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .stay) (beforeRightPath path left head right))
      (.running .restoreClock ⟨path.reverse ++ left, head, right⟩) := by
  have hscan := stopFree_moveScan .stay path hsafe left head right
  have hend : StopFreeValidZeroRun 1
      (.running (.moveSimHead .stay) (afterRightPath path left head right))
      (.running .restoreClock ⟨path.reverse ++ left, head, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        moveSimHead_stay head hhead (path.reverse ++ left) right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

def stopFree_moveRightInternal
    (path : List Tape) (hsafe : MoveScanSafe path)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (cell : Tape) (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .right)
        (beforeRightPath path left head (cell :: right)))
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          headTapeOfCell cell, right⟩) := by
  have hscan := stopFree_moveScan .right path hsafe left head (cell :: right)
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .right)
        (afterRightPath path left head (cell :: right)))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, cell, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        moveSimHead_right head hhead (path.reverse ++ left) cell right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, cell, right⟩)
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          headTapeOfCell cell, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact movePlaceRight_cell cell hcell
        (unheadTape head :: path.reverse ++ left) right
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 2, by
    simpa [Nat.add_assoc] using (hscan.append hmove).append hplace⟩

def stopFree_moveLeftInternal
    (pre : List Tape) (cell : Tape) (hsafe : MoveScanSafe (pre ++ [cell]))
    (hcell : cell = payloadTape false ∨ cell = payloadTape true ∨
      cell = ulogCore payloadBlank)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .left)
        (beforeRightPath (pre ++ [cell]) left head right))
      (.running .restoreClock
        ⟨pre.reverse ++ left, headTapeOfCell cell,
          unheadTape head :: right⟩) := by
  have hscan := stopFree_moveScan .left (pre ++ [cell]) hsafe left head right
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .left)
        (afterRightPath (pre ++ [cell]) left head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre.reverse ++ left, cell, unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.reverse_append,
        List.append_assoc] using
        moveSimHead_left head hhead (pre.reverse ++ left) cell right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre.reverse ++ left, cell, unheadTape head :: right⟩)
      (.running .restoreClock
        ⟨pre.reverse ++ left, headTapeOfCell cell,
          unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact movePlaceLeft_cell cell hcell (pre.reverse ++ left)
        (unheadTape head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  exact ⟨(pre ++ [cell]).length + 2, by
    simpa [Nat.add_assoc] using (hscan.append hmove).append hplace⟩

def stopFree_returnMovedFromRight
    (path : List Tape) (hsafe : ReturnMovedSafe path)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath path left head right))
      (.running .restoreClock (afterLeftPath path left head right)) := by
  have hscan := stopFree_leftPath_of (.actionPhase .returnMovedFromRight)
    (by intro h; cases h) path (by
      intro x hx l y r
      exact returnMovedFromRight_pass x (hsafe x hx) l y r)
    left head right
  have hend : StopFreeValidZeroRun 1
      (.running (.actionPhase .returnMovedFromRight)
        (afterLeftPath path left head right))
      (.running .restoreClock (afterLeftPath path left head right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterLeftPath] using
        returnMovedFromRight_head head hhead left (path.reverse ++ right)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

def stopFree_returnMovedFromLeft
    (path : List Tape) (hsafe : ReturnMovedSafe path)
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath path left head right))
      (.running .restoreClock (afterRightPath path left head right)) := by
  have hscan := stopFree_rightPath_of (.actionPhase .returnMovedFromLeft)
    (by intro h; cases h) path (by
      intro x hx l y r
      exact returnMovedFromLeft_pass x (hsafe x hx) l y r)
    left head right
  have hend : StopFreeValidZeroRun 1
      (.running (.actionPhase .returnMovedFromLeft)
        (afterRightPath path left head right))
      (.running .restoreClock (afterRightPath path left head right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        returnMovedFromLeft_head head hhead (path.reverse ++ left) right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  exact ⟨path.length + 1, hscan.append hend⟩

/-- Exact stop-free transport of the right workspace shift.  The workspace
sentinel is consumed only at the final step, so this segment cannot conceal a
cycle boundary or a terminal. -/
def stopFree_shiftRuntimeRight
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running (.actionPhase .returnMovedFromRight)
        (beforeLeftPath (pre.reverse ++ [carry]) left head
          (last :: right))) := by
  induction pre generalizing carry left head with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work := hsafe last (by simp)
      have hstep : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath [last] (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.right last))
            ⟨carry :: head :: left, MStarConcreteAlphabet.work, right⟩) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeRightPath] using
            shiftRuntimeRight_step carry last hlast (head :: left)
              MStarConcreteAlphabet.work right
        · simp [beforeRightPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      have hend : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right last))
            ⟨carry :: head :: left, MStarConcreteAlphabet.work, right⟩)
          (.running (.actionPhase .returnMovedFromRight)
            (beforeLeftPath [carry] left head (last :: right))) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeLeftPath] using
            shiftRuntimeRight_end last (head :: left) carry right
        · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
      exact ⟨2, by simpa [beforeRightPath, beforeLeftPath] using hstep.append hend⟩
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath ((x :: xs) ++ [last]) (head :: left)
              MStarConcreteAlphabet.work right))
          (.running (.shiftRuntime (.right x))
            (beforeRightPath (xs ++ [last]) (carry :: head :: left)
              MStarConcreteAlphabet.work right)) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases xs with
          | nil =>
              simpa [beforeRightPath] using
                shiftRuntimeRight_step carry x hx (head :: left) last
                  (MStarConcreteAlphabet.work :: right)
          | cons z zs =>
              simpa [beforeRightPath, List.append_assoc] using
                shiftRuntimeRight_step carry x hx (head :: left) z
                  (zs ++ last :: MStarConcreteAlphabet.work :: right)
        · simp [beforeRightPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      obtain ⟨n, hrest⟩ := ih x hxs (head :: left) carry
      have hall := hfirst.append hrest
      refine ⟨1 + n, ?_⟩
      rw [List.reverse_cons]
      rw [beforeLeftPath_append_singleton (xs.reverse ++ [x]) carry
        (by simp)]
      exact hall

def stopFree_shiftRuntimeRight_restored
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right))
      (.running .restoreClock
        ⟨left, head, carry :: pre ++ last :: right⟩) := by
  obtain ⟨a, hshiftRun⟩ :=
    stopFree_shiftRuntimeRight carry pre last hshift left head right
  obtain ⟨b, hreturnRun⟩ :=
    stopFree_returnMovedFromRight (pre.reverse ++ [carry]) hreturn
      left head hhead (last :: right)
  exact ⟨a + b, by
    simpa [afterLeftPath, List.reverse_append, List.append_assoc] using
      hshiftRun.append hreturnRun⟩

/-- The right boundary case first creates a blank head, shifts the finite
workspace one cell, and then restores the clock.  All four pieces are exact
slot-zero runs. -/
def stopFree_moveRightBoundary
    (path pre : List Tape) (hscan : MoveScanSafe path) (boundary last : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .right)
        (beforeRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨unheadTape head :: path.reverse ++ left,
          ulogCore payloadHeadBlank, boundary :: pre ++ last :: right⟩) := by
  have hscanRun := stopFree_moveScan .right path hscan left head
    (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .right)
        (afterRightPath path left head
          (boundary :: pre ++ last :: MStarConcreteAlphabet.work :: right)))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        moveSimHead_right head hhead (path.reverse ++ left) boundary
          (pre ++ last :: MStarConcreteAlphabet.work :: right)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ last :: MStarConcreteAlphabet.work :: right⟩)
      (.running (.shiftRuntime (.right boundary))
        (beforeRightPath (pre ++ [last])
          (ulogCore payloadHeadBlank :: unheadTape head ::
            path.reverse ++ left) MStarConcreteAlphabet.work right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pre with
      | nil =>
          simpa [beforeRightPath] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) last
              (MStarConcreteAlphabet.work :: right)
      | cons x xs =>
          simpa [beforeRightPath, List.append_assoc] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) x
              (xs ++ last :: MStarConcreteAlphabet.work :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨a, hshiftRun⟩ := stopFree_shiftRuntimeRight_restored boundary pre
    last hshift hreturn (unheadTape head :: path.reverse ++ left)
    (ulogCore payloadHeadBlank) (by decide) right
  have hprefix := (hscanRun.append hmove).append hplace
  exact ⟨path.length + 2 + a, by
    simpa [Nat.add_assoc] using hprefix.append hshiftRun⟩

/-- Exact stop-free transport of the left workspace shift. -/
def stopFree_shiftRuntimeLeft
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (head : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running (.actionPhase .returnMovedFromLeft)
        (beforeRightPath (pre.reverse ++ [carry]) (last :: left) head right)) := by
  induction pre generalizing carry head right with
  | nil =>
      have hlast : last ≠ MStarConcreteAlphabet.work := hsafe last (by simp)
      have hstep : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left carry))
            (beforeLeftPath [last] left MStarConcreteAlphabet.work
              (head :: right)))
          (.running (.shiftRuntime (.left last))
            ⟨left, MStarConcreteAlphabet.work, carry :: head :: right⟩) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeLeftPath] using
            shiftRuntimeLeft_step carry last hlast left
              MStarConcreteAlphabet.work (head :: right)
        · simp [beforeLeftPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      have hend : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left last))
            ⟨left, MStarConcreteAlphabet.work, carry :: head :: right⟩)
          (.running (.actionPhase .returnMovedFromLeft)
            (beforeRightPath [carry] (last :: left) head right)) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [beforeRightPath] using
            shiftRuntimeLeft_end last left carry (head :: right)
        · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
      exact ⟨2, by simpa [beforeLeftPath, beforeRightPath] using hstep.append hend⟩
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.left carry))
            (beforeLeftPath ((x :: xs) ++ [last]) left
              MStarConcreteAlphabet.work (head :: right)))
          (.running (.shiftRuntime (.left x))
            (beforeLeftPath (xs ++ [last]) left
              MStarConcreteAlphabet.work (carry :: head :: right))) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases xs with
          | nil =>
              simpa [beforeLeftPath] using
                shiftRuntimeLeft_step carry x hx
                  (MStarConcreteAlphabet.work :: left) last (head :: right)
          | cons z zs =>
              simpa [beforeLeftPath, List.append_assoc] using
                shiftRuntimeLeft_step carry x hx
                  (zs ++ last :: MStarConcreteAlphabet.work :: left) z
                  (head :: right)
        · simp [beforeLeftPath, IsConcreteCycleStop,
            IsConcreteCycleBoundary, concreteHalted]
      obtain ⟨n, hrest⟩ := ih x hxs carry (head :: right)
      have hall := hfirst.append hrest
      refine ⟨1 + n, ?_⟩
      rw [List.reverse_cons]
      rw [beforeRightPath_append_singleton (xs.reverse ++ [x]) carry
        (by simp)]
      exact hall

def stopFree_shiftRuntimeLeft_restored
    (carry : Tape) (pre : List Tape) (last : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [carry]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.shiftRuntime (.left carry))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (head :: right)))
      (.running .restoreClock
        ⟨carry :: pre ++ last :: left, head, right⟩) := by
  obtain ⟨a, hshiftRun⟩ :=
    stopFree_shiftRuntimeLeft carry pre last hshift left head right
  obtain ⟨b, hreturnRun⟩ :=
    stopFree_returnMovedFromLeft (pre.reverse ++ [carry]) hreturn
      (last :: left) head hhead right
  exact ⟨a + b, by
    simpa [afterRightPath, List.reverse_append, List.append_assoc] using
      hshiftRun.append hreturnRun⟩

/-- Exact stop-free left-boundary extension. -/
def stopFree_moveLeftBoundary
    (pre : List Tape) (last boundary : Tape)
    (hscan : MoveScanSafe ((pre ++ [last]).reverse ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ReturnMovedSafe (pre.reverse ++ [boundary]))
    (left : List Tape) (head : Tape) (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .left)
        (beforeRightPath ((pre ++ [last]).reverse ++ [boundary])
          (MStarConcreteAlphabet.work :: left) head right))
      (.running .restoreClock
        ⟨boundary :: pre ++ last :: left, ulogCore payloadHeadBlank,
          unheadTape head :: right⟩) := by
  let scanPath := (pre ++ [last]).reverse ++ [boundary]
  have hscanRun := stopFree_moveScan .left scanPath hscan
    (MStarConcreteAlphabet.work :: left) head right
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .left)
        (afterRightPath scanPath (MStarConcreteAlphabet.work :: left)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [scanPath, afterRightPath, List.reverse_append,
        List.append_assoc] using
        moveSimHead_left head hhead
          (pre ++ last :: MStarConcreteAlphabet.work :: left) boundary right
    · simp [scanPath, afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceLeft)
        ⟨pre ++ last :: MStarConcreteAlphabet.work :: left, boundary,
          unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (pre ++ [last]) left MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pre with
      | nil =>
          simpa [beforeLeftPath] using
            movePlaceLeft_boundary boundary hboundary
              (MStarConcreteAlphabet.work :: left) last
              (unheadTape head :: right)
      | cons x xs =>
          simpa [beforeLeftPath, List.append_assoc] using
            movePlaceLeft_boundary boundary hboundary
              (xs ++ last :: MStarConcreteAlphabet.work :: left) x
              (unheadTape head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨a, hshiftRun⟩ := stopFree_shiftRuntimeLeft_restored boundary pre
    last hshift hreturn left (ulogCore payloadHeadBlank) (by native_decide)
    (unheadTape head :: right)
  have hprefix := (hscanRun.append hmove).append hplace
  exact ⟨scanPath.length + 2 + a, by
    simpa [scanPath, Nat.add_assoc] using hprefix.append hshiftRun⟩

/-- Exact first-stop strengthening of the clock/program/head cleanup.  The
only stop produced by this cleanup is its final `cycleStart` boundary. -/
def stopFree_restoreCycle
    (pcPath : List Tape) (terminal : Tape)
    (programPath : List Tape) (outer : List Tape) (head : Tape)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: programPath).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe programPath)
    (hhead : choiceHead head = true)
    (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩)
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++
                ulogCore pcMark :: outer,
          head, right⟩) := by
  let clockPath := head :: (pcPath ++ terminal :: programPath).reverse
  have hclockRun := stopFree_leftPath_of .restoreClock (by decide) clockPath
    (by
      intro x hx l y r
      exact restoreClock_pass x (hclock x hx).1 (hclock x hx).2 l y r)
    outer (ulogCore pcMark) right
  have hpcStart : StopFreeValidZeroRun 1
      (.running .restoreClock
        (afterLeftPath clockPath outer (ulogCore pcMark) right))
      (.running .restorePc
        (beforeRightPath pcPath (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pcPath with
      | nil =>
          simpa [clockPath, afterLeftPath, beforeRightPath,
            List.reverse_append, List.append_assoc] using
            restoreClock_pc outer terminal (programPath ++ head :: right)
      | cons x xs =>
          simpa [clockPath, afterLeftPath, beforeRightPath,
            List.reverse_append, List.append_assoc] using
            restoreClock_pc outer x
              (xs ++ terminal :: programPath ++ head :: right)
    · simp [clockPath, afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hpcRun := stopFree_rightPathMap_of .restorePc (by decide) pcPath
    restorePcCell (by
      intro x hx l y r
      exact restorePc_path_step x (hpc x hx) l y r)
    (ulogCore pcMark :: outer) terminal (programPath ++ head :: right)
  have hheadStart : StopFreeValidZeroRun 1
      (.running .restorePc
        (afterRightPathMap pcPath restorePcCell
          (ulogCore pcMark :: outer) terminal
          (programPath ++ head :: right)))
      (.running .restoreHead
        (beforeRightPath programPath
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      rcases hterminal with rfl | rfl
      · cases programPath with
        | nil =>
            simpa [afterRightPathMap, beforeRightPath] using
              restorePc_end
                (pcPath.reverse.map restorePcCell ++
                  ulogCore pcMark :: outer) head right
        | cons x xs =>
            simpa [afterRightPathMap, beforeRightPath,
              List.append_assoc] using
              restorePc_end
                (pcPath.reverse.map restorePcCell ++
                  ulogCore pcMark :: outer) x (xs ++ head :: right)
      · cases programPath with
        | nil =>
            simpa [afterRightPathMap, beforeRightPath] using
              restorePc_boundary
                (pcPath.reverse.map restorePcCell ++
                  ulogCore pcMark :: outer) head right
        | cons x xs =>
            simpa [afterRightPathMap, beforeRightPath,
              List.append_assoc] using
              restorePc_boundary
                (pcPath.reverse.map restorePcCell ++
                  ulogCore pcMark :: outer) x (xs ++ head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hheadRun := stopFree_rightPathMap_of .restoreHead (by decide)
    programPath restoreProgramCell (by
      intro x hx l y r
      exact restoreHead_pass x (hprogram x hx).1 (hprogram x hx).2 l y r)
    (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
      ulogCore pcMark :: outer) head right
  have hfinish : StopFreeValidZeroRun 1
      (.running .restoreHead
        (afterRightPathMap programPath restoreProgramCell
          (ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
            ulogCore pcMark :: outer) head right))
      (.running .cycleStart
        ⟨programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
              ulogCore pcMark :: outer, head, right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPathMap, List.append_assoc] using
        restoreHead_head head hhead
          (programPath.reverse.map restoreProgramCell ++
            ulogCore codeOne :: pcPath.reverse.map restorePcCell ++
              ulogCore pcMark :: outer) right
    · simp [afterRightPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hclockRun' : StopFreeValidZeroRun clockPath.length
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: programPath).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩)
      (.running .restoreClock
        (afterLeftPath clockPath outer (ulogCore pcMark) right)) := by
    simpa [clockPath, beforeLeftPath, List.append_assoc] using hclockRun
  have hprefix := ((hclockRun'.append hpcStart).append hpcRun).append hheadStart
  have hcleanup := hprefix.append hheadRun
  exact ⟨clockPath.length + 1 + pcPath.length + 1 + programPath.length + 1,
    by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hcleanup.append hfinish⟩

/-- Exact cleanup after a staying simulated-head move.  This is the
stop-free version of `reaches_moveStay_cleanup`; its only cycle stop is the
final restored `cycleStart` configuration. -/
def stopFree_moveStay_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    (hhead : choiceHead head = true) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .cycleStart
        ⟨scanPath.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          head, right⟩) := by
  obtain ⟨a, hmove⟩ := stopFree_moveStay scanPath hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  obtain ⟨b, hcleanup⟩ := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath) outer head hclock hpc hterminal hprogram
    hhead right
  have hmove' : StopFreeValidZeroRun a
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse ++
            ulogCore pcMark :: outer,
          head, right⟩) := by
    simpa [List.reverse_append, List.append_assoc] using hmove
  exact ⟨a + b, by
    simpa [List.reverse_append, List.map_append, List.append_assoc] using
      hmove'.append hcleanup⟩

/-- Exact cleanup after an internal right move. -/
def stopFree_moveRightInternal_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head cell : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hhead : choiceHead head = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head])) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head (cell :: right)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape head) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell, right⟩) := by
  obtain ⟨a, hmove⟩ := stopFree_moveRightInternal scanPath hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead cell hcell right
  have hnewHead : choiceHead (headTapeOfCell cell) = true := by
    rcases hcell with rfl | rfl | rfl <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [unheadTape head]) outer
    (headTapeOfCell cell) hclock hpc hterminal hprogram hnewHead right
  have hmove' : StopFreeValidZeroRun a
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head (cell :: right)))
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [unheadTape head])).reverse ++
              ulogCore pcMark :: outer,
          headTapeOfCell cell, right⟩) := by
    simpa [List.reverse_append, List.append_assoc] using hmove
  exact ⟨a + b, by
    simpa [List.reverse_append, List.map_append, List.append_assoc] using
      hmove'.append hcleanup⟩

/-- Exact cleanup after an internal left move. -/
def stopFree_moveLeftInternal_cleanup
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (cell head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix)) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .cycleStart
        ⟨scanPrefix.reverse.map restoreProgramCell ++
            programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
              pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          headTapeOfCell cell, unheadTape head :: right⟩) := by
  obtain ⟨a, hmove⟩ := stopFree_moveLeftInternal scanPrefix cell hscan hcell
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  have hnewHead : choiceHead (headTapeOfCell cell) = true := by
    rcases hcell with rfl | rfl | rfl <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPrefix) outer (headTapeOfCell cell)
    hclock hpc hterminal hprogram hnewHead (unheadTape head :: right)
  have hmove' : StopFreeValidZeroRun a
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .restoreClock
        ⟨(pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell, unheadTape head :: right⟩) := by
    simpa [List.reverse_append, List.append_assoc] using hmove
  exact ⟨a + b, by
    simpa [List.reverse_append, List.map_append, List.append_assoc] using
      hmove'.append hcleanup⟩

/-- Exact cleanup after a right-boundary extension.  The workspace shift is
part of the stop-free prefix, and the only stop is the restored cycle
boundary. -/
def stopFree_moveRightBoundary_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head boundary : Tape)
    (shiftPrefix : List Tape) (last : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (shiftPrefix ++ [last]))
    (hreturn : ReturnMovedSafe (shiftPrefix.reverse ++ [boundary]))
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head])) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .cycleStart
        ⟨restoreProgramCell (unheadTape head) ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
  obtain ⟨a, hmove⟩ := stopFree_moveRightBoundary scanPath shiftPrefix hscan
    boundary last hboundary hshift hreturn
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  obtain ⟨b, hcleanup⟩ := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [unheadTape head]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
    (by native_decide) (boundary :: shiftPrefix ++ last :: right)
  have hmove' : StopFreeValidZeroRun a
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [unheadTape head])).reverse ++
              ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
    simpa [List.reverse_append, List.append_assoc] using hmove
  exact ⟨a + b, by
    simpa [List.reverse_append, List.map_append, List.append_assoc] using
      hmove'.append hcleanup⟩

/-- Exact cleanup after a left-boundary extension.  Unlike the internal left
case, the shift crosses the program-counter marker and consumes the reserved
outer workspace cell before the ordinary restore pass. -/
def stopFree_moveLeftBoundary_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPath ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe
      (scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse ++ [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((scanPath.reverse ++ programPrefix.reverse ++ terminal ::
        pcPath.reverse).reverse ++ [boundary]))
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [boundary])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [boundary])) :
    Σ n, StopFreeValidZeroRun n
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .cycleStart
        ⟨restoreProgramCell boundary ::
            scanPath.reverse.map restoreProgramCell ++
              programPrefix.reverse.map restoreProgramCell ++ ulogCore codeOne ::
                pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
  let shiftPrefix := scanPath.reverse ++ programPrefix.reverse ++
    terminal :: pcPath.reverse
  have hscanRun := stopFree_moveScan .left (scanPath ++ [boundary]) hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    head right
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .left)
        (afterRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [shiftPrefix, afterRightPath, List.reverse_append,
        List.append_assoc] using
        moveSimHead_left head hhead
          (shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer)
          boundary right
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (shiftPrefix ++ [ulogCore pcMark]) outer
          MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hprefix : shiftPrefix with
      | nil =>
          simpa [beforeLeftPath, hprefix] using
            movePlaceLeft_boundary boundary hboundary
              (MStarConcreteAlphabet.work :: outer) (ulogCore pcMark)
              (unheadTape head :: right)
      | cons x xs =>
          simpa [beforeLeftPath, hprefix, List.append_assoc] using
            movePlaceLeft_boundary boundary hboundary
              (xs ++ ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
              x (unheadTape head :: right)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨a, hshiftRun⟩ := stopFree_shiftRuntimeLeft_restored boundary
    shiftPrefix (ulogCore pcMark) (by simpa [shiftPrefix] using hshift)
    (by simpa [shiftPrefix] using hreturn) outer
    (ulogCore payloadHeadBlank) (by native_decide) (unheadTape head :: right)
  have hmoveRestore : StopFreeValidZeroRun
      ((scanPath ++ [boundary]).length + 2 + a)
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .restoreClock
        ⟨boundary :: shiftPrefix ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
    have hall := (hscanRun.append hmove).append hplace
    simpa [shiftPrefix, Nat.add_assoc, List.reverse_append,
      List.append_assoc] using hall.append hshiftRun
  obtain ⟨b, hcleanup⟩ := stopFree_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [boundary]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
    (by native_decide) (unheadTape head :: right)
  have hmoveRestore' : StopFreeValidZeroRun
      ((scanPath ++ [boundary]).length + 2 + a)
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .restoreClock
        ⟨(pcPath ++ terminal ::
            (programPrefix ++ scanPath ++ [boundary])).reverse ++
              ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
    simpa [shiftPrefix, List.reverse_append, List.append_assoc] using
      hmoveRestore
  exact ⟨(scanPath ++ [boundary]).length + 2 + a + b, by
    simpa [shiftPrefix, List.reverse_append, List.map_append,
      List.append_assoc] using hmoveRestore'.append hcleanup⟩

/-- One marked-state target-rewrite round, with every microstep certified as
an actual slot-zero edge.  This is the inductive atom for the existing-state
(`target ≤ current`) rewrite, rather than a conversion of its legacy
`Reaches` proof. -/
def stopFree_targetRoundExisting
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hsafe : TargetRoundCorridorSafe path)
    (left stateRest : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          targetScanPath path done ++ ulogCore stateZero :: stateRest⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++ stateRest))) := by
  let scanPath := targetScanPath path done
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateZero :: stateRest⟩)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases scanPath <;>
        simp [beforeRightPath, actionTarget_zero, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hseek := stopFree_rightPath_of (.actionPhase .targetSeekState)
    (by decide) scanPath (by
      intro x hx l y r
      by_cases hm : x = ulogCore stateMark
      · subst x
        exact targetSeekState_mark l y r
      · have h := targetScanPath_seek_safe path done hsafe hx
        exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
    (ulogCore targetMark :: left) (ulogCore stateZero) stateRest
  have hzero : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateZero) stateRest))
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : scanPath.reverse with
      | nil =>
          simpa [afterRightPath, beforeLeftPath, hr] using
            targetSeekState_zero left (ulogCore targetMark) stateRest
      | cons x xs =>
          simpa [afterRightPath, beforeLeftPath, hr,
            List.append_assoc] using
            targetSeekState_zero (xs ++ ulogCore targetMark :: left)
              x stateRest
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hreturn := stopFree_leftPath_of (.actionPhase .targetReturning)
    (by decide) scanPath.reverse (by
      intro x hx l y r
      have hx' : x ∈ scanPath := by simpa using hx
      have h := targetScanPath_return_safe path done hsafe hx'
      exact targetReturning_pass x h.1 h.2 l y r)
    left (ulogCore targetMark) (ulogCore stateMark :: stateRest)
  have hdone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetReturning)
        (afterLeftPath scanPath.reverse left (ulogCore targetMark)
          (ulogCore stateMark :: stateRest)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++ stateRest))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hscan : scanPath.reverse.reverse =
          path ++ List.replicate done (ulogCore stateMark) := by
        simp [scanPath, targetScanPath]
      rw [show afterLeftPath scanPath.reverse left (ulogCore targetMark)
            (ulogCore stateMark :: stateRest) =
          ⟨left, ulogCore targetMark,
            path ++ List.replicate (done + 1) (ulogCore stateMark) ++
              stateRest⟩ by
          simp [afterLeftPath, hscan, List.replicate_succ',
            List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.replicate_succ,
            List.append_assoc] using
            targetReturning_mark left x
              (xs ++ List.replicate (done + 1) (ulogCore stateMark) ++
                stateRest)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hprefix := ((hstart.append hseek).append hzero).append hreturn
  exact ⟨_, hprefix.append hdone⟩

/-- One target-rewrite round which consumes one workspace cell and creates a
new marked state.  It is the exact inductive atom for the growing branch. -/
def stopFree_targetRoundGrow
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hsafe : TargetRoundCorridorSafe path)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          targetScanPath path done ++ ulogCore stateOne ::
            ulogCore stateSep :: MStarConcreteAlphabet.work :: tail⟩)
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  let scanPath := targetScanPath path done
  let returnPath := targetGrowReturnPath scanPath
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeZero,
          scanPath ++ ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetSeekState)
        (beforeRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases scanPath <;>
        simp [beforeRightPath, actionTarget_zero, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hseek := stopFree_rightPath_of (.actionPhase .targetSeekState)
    (by decide) scanPath (by
      intro x hx l y r
      by_cases hm : x = ulogCore stateMark
      · subst x
        exact targetSeekState_mark l y r
      · have h := targetScanPath_seek_safe path done hsafe hx
        exact targetSeekState_pass x hm h.1 h.2.1 h.2.2 l y r)
    (ulogCore targetMark :: left) (ulogCore stateOne)
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)
  have hone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetSeekState)
        (afterRightPath scanPath (ulogCore targetMark :: left)
          (ulogCore stateOne)
          (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetGrowSep)
        ⟨ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          ulogCore stateSep, MStarConcreteAlphabet.work :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        targetSeekState_one
          (scanPath.reverse ++ ulogCore targetMark :: left)
          (ulogCore stateSep) (MStarConcreteAlphabet.work :: tail)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hsep : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetGrowSep)
        ⟨ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          ulogCore stateSep, MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetGrowPlaceSep)
        ⟨ulogCore stateOne :: ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          MStarConcreteAlphabet.work, tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetGrowSep_step
        (ulogCore stateMark :: scanPath.reverse ++
          ulogCore targetMark :: left)
        MStarConcreteAlphabet.work tail
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetGrowPlaceSep)
        ⟨ulogCore stateOne :: ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left,
          MStarConcreteAlphabet.work, tail⟩)
      (.running (.actionPhase .targetReturning)
        (beforeLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [returnPath, targetGrowReturnPath, beforeLeftPath,
        List.append_assoc] using
        targetGrowPlaceSep_step
          (ulogCore stateMark :: scanPath.reverse ++
            ulogCore targetMark :: left)
          (ulogCore stateOne) tail
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hreturn := stopFree_leftPath_of (.actionPhase .targetReturning)
    (by decide) returnPath (by
      intro x hx l y r
      have h := targetGrowReturnPath_safe path done hsafe (by
        simpa [returnPath, scanPath] using hx)
      exact targetReturning_pass x h.1 h.2 l y r)
    left (ulogCore targetMark) (ulogCore stateSep :: tail)
  have hdone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetReturning)
        (afterLeftPath returnPath left (ulogCore targetMark)
          (ulogCore stateSep :: tail)))
      (.running .actionTarget
        (beforeRightPath path (ulogCore codeZero :: left)
          (ulogCore stateMark)
          (List.replicate done (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hreturn : returnPath.reverse =
          path ++ List.replicate (done + 1) (ulogCore stateMark) ++
            [ulogCore stateOne] := by
        simp [returnPath, targetGrowReturnPath, scanPath, targetScanPath,
          List.reverse_append, List.replicate_succ', List.append_assoc]
      rw [show afterLeftPath returnPath left (ulogCore targetMark)
            (ulogCore stateSep :: tail) =
          ⟨left, ulogCore targetMark,
            path ++ List.replicate (done + 1) (ulogCore stateMark) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
          simp [afterLeftPath, hreturn, List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.replicate_succ,
            List.append_assoc] using
            targetReturning_mark left x
              (xs ++ List.replicate (done + 1) (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hprefix := (((hstart.append hseek).append hone).append hsep).append hplace
  exact ⟨_, (hprefix.append hreturn).append hdone⟩

/-- Fold the exact existing-state target rounds. -/
def stopFree_targetExistingZeros
    (remaining done extra : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetExistingStart remaining done extra corridor left tail)
      (targetExistingDone remaining done extra corridor left tail) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨0, by
        simpa [targetExistingStart, targetExistingDone] using
          ({ valid := ValidZeroRun.nil _
             stop_free := by intro m hm; simp at hm } :
            StopFreeValidZeroRun 0
              (targetExistingStart 0 done extra corridor left tail)
              (targetExistingStart 0 done extra corridor left tail))⟩
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      obtain ⟨a, hround⟩ := stopFree_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining (ulogCore stateZero) ++
          List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      obtain ⟨b, htail⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have htail' : StopFreeValidZeroRun b
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                List.replicate remaining (ulogCore stateZero) ++
                  List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail)))
          (targetExistingDone remaining (done + 1) extra corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetExistingStart, path, beforeRightPath,
            targetScanPath, List.replicate_succ, List.replicate_succ',
            List.append_assoc, Nat.add_assoc] using htail
      have htailJoin : StopFreeValidZeroRun b
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                (List.replicate remaining (ulogCore stateZero) ++
                  List.replicate extra (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail))))
          (targetExistingDone remaining (done + 1) extra corridor
            (ulogCore codeZero :: left) tail) := by
        simpa only [List.append_assoc] using htail'
      have hall := hround.append htailJoin
      exact ⟨a + b, by
        simpa [targetExistingStart, targetExistingDone, path,
          targetScanPath, List.replicate_succ, List.replicate_succ',
          List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hall⟩

/-- Fold the exact growing target rounds. -/
def stopFree_targetGrowZeros
    (remaining done : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetGrowStart remaining done corridor left tail)
      (targetGrowDone remaining done corridor left tail) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨0, by
        simpa [targetGrowStart, targetGrowDone] using
          ({ valid := ValidZeroRun.nil _
             stop_free := by intro m hm; simp at hm } :
            StopFreeValidZeroRun 0
              (targetGrowStart 0 done corridor left tail)
              (targetGrowStart 0 done corridor left tail))⟩
  | succ remaining ih =>
      let path := List.replicate remaining (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      obtain ⟨a, hround⟩ := stopFree_targetRoundGrow path hpath done
        (targetCodeCorridor_round_safe remaining corridor hsafe) left
        (List.replicate remaining MStarConcreteAlphabet.work ++ tail)
      obtain ⟨b, htail⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have htail' : StopFreeValidZeroRun b
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate remaining MStarConcreteAlphabet.work ++
                    tail)))
          (targetGrowDone remaining (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        cases remaining <;>
          simpa [targetGrowStart, path, beforeRightPath, targetScanPath,
            List.replicate_succ, List.replicate_succ', List.append_assoc,
            Nat.add_assoc] using htail
      have htailJoin : StopFreeValidZeroRun b
          (.running .actionTarget
            (beforeRightPath path (ulogCore codeZero :: left)
              (ulogCore stateMark)
              (List.replicate done (ulogCore stateMark) ++
                (ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate remaining MStarConcreteAlphabet.work ++
                    tail))))
          (targetGrowDone remaining (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        simpa only [List.append_assoc] using htail'
      have hall := hround.append htailJoin
      exact ⟨a + b, by
        simpa [targetGrowStart, targetGrowDone, path, targetScanPath,
          List.replicate_succ, List.replicate_succ', List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall⟩

/-- Exact target-one rejection when the current state is zero.  The required
workspace cell is first consumed by the certified growing round, after which
the target-finish controller reaches rejection as its first stop. -/
def targetRawOneZero_firstStop
    (corridor : List Tape) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (targetRawStart 1 0 corridor left
        (MStarConcreteAlphabet.work :: tail)) .rejected := by
  obtain ⟨n, hwork⟩ := stopFree_targetGrowZeros 1 0 corridor hsafe left tail
  have hwork' : StopFreeValidZeroRun n
      (targetRawStart 1 0 corridor left
        (MStarConcreteAlphabet.work :: tail))
      (targetGrowDone 1 0 corridor left tail) := by
    simpa [targetRawStart, targetGrowStart, targetScanPath,
      List.append_assoc] using hwork
  have hhalt := actionTargetFinishOneMark_firstStop corridor hsafe.2
    (ulogCore codeZero :: left) (ulogCore stateOne) (Or.inr rfl)
    (ulogCore stateSep :: tail)
  have hhalt' : FirstValidZeroHit IsConcreteCycleStop
      (targetGrowDone 1 0 corridor left tail) .rejected := by
    simpa [targetGrowDone, List.replicate_succ,
      List.append_assoc] using hhalt
  exact (hwork'.append
    { valid := hhalt'.valid
      stop_free := hhalt'.before }).toFirstHit hhalt'.hit

/-- Exact target-one rejection when at least one current state cell exists. -/
def targetRawOnePositive_firstStop
    (extra : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (targetRawStart 1 (extra + 1) corridor left tail) .rejected := by
  obtain ⟨n, hwork⟩ := stopFree_targetExistingZeros 1 0 extra corridor
    hsafe left tail
  have hwork' : StopFreeValidZeroRun n
      (targetRawStart 1 (extra + 1) corridor left tail)
      (targetExistingDone 1 0 extra corridor left tail) := by
    simpa [targetRawStart, targetExistingStart, targetScanPath,
      List.replicate_succ, List.append_assoc] using hwork
  cases extra with
  | zero =>
      have hhalt := actionTargetFinishOneMark_firstStop corridor hsafe.2
        (ulogCore codeZero :: left) (ulogCore stateOne) (Or.inr rfl)
        (ulogCore stateSep :: tail)
      have hhalt' : FirstValidZeroHit IsConcreteCycleStop
          (targetExistingDone 1 0 0 corridor left tail) .rejected := by
        simpa [targetExistingDone, List.replicate_succ,
          List.append_assoc] using hhalt
      exact (hwork'.append
        { valid := hhalt'.valid
          stop_free := hhalt'.before }).toFirstHit hhalt'.hit
  | succ extra =>
      have hhalt := actionTargetFinishOneMark_firstStop corridor hsafe.2
        (ulogCore codeZero :: left) (ulogCore stateZero) (Or.inl rfl)
        (List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      have hhalt' : FirstValidZeroHit IsConcreteCycleStop
          (targetExistingDone 1 0 (extra + 1) corridor left tail)
          .rejected := by
        simpa [targetExistingDone, List.replicate_succ,
          List.append_assoc] using hhalt
      exact (hwork'.append
        { valid := hhalt'.valid
          stop_free := hhalt'.before }).toFirstHit hhalt'.hit

/-- The common action-write prefix followed by the exact target-one
rejection when the current state is zero.  The trailing workspace cell is
consumed by the target rewrite, so it is part of the concrete first-stop
statement rather than an implicit resource assumption. -/
noncomputable def actionWriteTargetOneZero_firstStop
    (write : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (corridor runtime : List Tape)
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: corridor))
    (htargetPath : TargetRewriteCorridorSafe
      (corridor ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: corridor) oldHead
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail)) .rejected := by
  obtain ⟨n, hwriteRun⟩ := stopFree_actionWriteValid write hwrite oldHead
    hhead (ulogCore codeZero :: ulogCore codeOne :: corridor) hwritePath left
    (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
      MStarConcreteAlphabet.work :: tail)
  have hwriteRun' : StopFreeValidZeroRun n
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: corridor) oldHead
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail))
      (targetRawStart 1 0 (corridor ++ writeHeadNat write :: runtime)
        (ulogCore codeOne ::
          List.replicate write (ulogCore codeZero) ++ left)
        (MStarConcreteAlphabet.work :: tail)) := by
    simpa [targetRawStart, beforeRightPath, List.append_assoc] using hwriteRun
  have htarget := targetRawOneZero_firstStop
    (corridor ++ writeHeadNat write :: runtime) htargetPath
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail
  exact (hwriteRun'.append
    { valid := htarget.valid, stop_free := htarget.before }).toFirstHit
      htarget.hit

/-- The common action-write prefix followed by the exact target-one
rejection when a positive current state is already represented. -/
noncomputable def actionWriteTargetOnePositive_firstStop
    (write extra : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (corridor runtime : List Tape)
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: corridor))
    (htargetPath : TargetRewriteCorridorSafe
      (corridor ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: corridor) oldHead
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) .rejected := by
  obtain ⟨n, hwriteRun⟩ := stopFree_actionWriteValid write hwrite oldHead
    hhead (ulogCore codeZero :: ulogCore codeOne :: corridor) hwritePath left
    (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hwriteRun' : StopFreeValidZeroRun n
      (actionWriteStart write left
        (ulogCore codeZero :: ulogCore codeOne :: corridor) oldHead
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart 1 (extra + 1)
        (corridor ++ writeHeadNat write :: runtime)
        (ulogCore codeOne ::
          List.replicate write (ulogCore codeZero) ++ left) tail) := by
    simpa [targetRawStart, beforeRightPath, List.replicate_succ,
      List.append_assoc] using hwriteRun
  have htarget := targetRawOnePositive_firstStop extra
    (corridor ++ writeHeadNat write :: runtime) htargetPath
    (ulogCore codeOne :: List.replicate write (ulogCore codeZero) ++ left)
    tail
  exact (hwriteRun'.append
    { valid := htarget.valid, stop_free := htarget.before }).toFirstHit
      htarget.hit

/-- A matched rule with target one rejects at its first concrete cycle stop
when the semantic source state is zero. -/
noncomputable def ruleCursorMatchedTargetOneZero_firstStop
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape)
    (hsource : r.source = 0) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) (tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail)) .rejected := by
  obtain ⟨a, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    boundary hboundary r rs programToHead base runtime hread hcorridor
    hreadPath (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)
  have hmatched' : StopFreeValidZeroRun a
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne ::
          moveBits r.action.move ++ cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail)) := by
    simpa [hsource, htarget] using hmatched
  have hreject := actionWriteTargetOneZero_firstStop r.action.write hwrite
    (readHeadNat r.read) (by interval_cases r.read <;> native_decide)
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) runtime
    hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  exact (hmatched'.append
    { valid := hreject.valid, stop_free := hreject.before }).toFirstHit
      hreject.hit

/-- A matched rule with target one rejects at its first concrete cycle stop
when the semantic source state is positive. -/
noncomputable def ruleCursorMatchedTargetOnePositive_firstStop
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (extra : ℕ)
    (hsource : r.source = extra + 1) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) (tail : List Tape) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate (extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)) .rejected := by
  obtain ⟨a, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    boundary hboundary r rs programToHead base runtime hread hcorridor
    hreadPath (ulogCore stateSep :: tail)
  have hmatched' : StopFreeValidZeroRun a
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate (extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne ::
          moveBits r.action.move ++ cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [hsource, htarget] using hmatched
  have hreject := actionWriteTargetOnePositive_firstStop r.action.write extra
    hwrite (readHeadNat r.read)
    (by interval_cases r.read <;> native_decide)
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) runtime
    hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  exact (hmatched'.append
    { valid := hreject.valid, stop_free := hreject.before }).toFirstHit
      hreject.hit

/-- Semantic lookup of a target-one action has a canonical genuine
first-hit concrete rejecting cycle.  This is the exact counterpart of the
older `BranchedReaches` dispatch: both source-state cases retain the
stop-free proof all the way to `.rejected`. -/
theorem branchedCycle_semanticTargetOne_exact_nonempty
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) .rejected) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  let choiceLeft := dynamicRuleReturnPath (c.leftRev.map payloadNat)
    (skip ++ r :: rs) input ++ ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix
  have hchoice := clockDecrementCells_firstChoice (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    choiceLeft
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) := by
    simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
      clockCellsAfter, heq, choiceLeft, choiceRight,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot
    (c.leftRev.map payloadNat) (payloadNatList_safe c.leftRev)
    (skip ++ r :: rs) (by simp) input outer (readHeadNat c.focus) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
            input) outer (ulogCore pcMark) (readHeadNat c.focus :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil (c.leftRev.map payloadNat)
      (skip ++ r :: rs) input
    cases hePath : dynamicRuleReturnPath (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input with
    | nil => exact (hpne hePath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hePath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat c.focus) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  obtain ⟨b, hmismatch⟩ := stopFree_mismatchPrefix
    cursorMismatchStopFreeStep slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix))
    trace
  have hmismatch' := hmismatch
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot c.state c.focus
    (c.leftRev.map payloadNat) input skip r rs
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (ulogCore stateSep ::
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix))] at hmismatch'
  have hmismatch'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus) choiceRight)
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) := by
    simpa [choiceRight, List.append_assoc] using hmismatch'
  have hmatched : FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot c.state c.focus
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix))) .rejected := by
    cases hstate : c.state with
    | zero =>
        let remaining := capacity - 1
        have hcapacityEq : capacity = remaining + 1 := by
          dsimp [remaining]
          omega
        have h := ruleCursorMatchedTargetOneZero_firstStop
          (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++ ulogCore pcDone ::
            (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer)
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          (by simpa [hstate] using hmatch.1) htarget rscan.read_valid hwrite
          (by simpa [hstate, hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (by simpa [htarget] using
            (matchedWritePath_safe r rs
              (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
          (List.replicate remaining MStarConcreteAlphabet.work ++ suffix)
        simpa [ruleCursorResult, ruleCursorBase, hstate, hcapacityEq,
          hmatch.2.1, hmatch.2.2, List.replicate_succ,
          List.append_assoc] using h
    | succ extra =>
        have h := ruleCursorMatchedTargetOnePositive_firstStop
          (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++ ulogCore pcDone ::
            (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer)
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          extra (by simpa [hstate] using hmatch.1) htarget
          rscan.read_valid hwrite
          (by simpa [hstate, hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (by simpa [htarget] using
            (matchedWritePath_safe r rs
              (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
          (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
            suffix)
        simpa [ruleCursorResult, ruleCursorBase, hstate, hmatch.2.1,
          hmatch.2.2, List.append_assoc] using h
  have hsuffix := (hdynamic'.append hmismatch'').append
    ({ valid := hmatched.valid
       stop_free := hmatched.before } : StopFreeValidZeroRun
        hmatched.steps _ .rejected)
  have hsuffix' : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      .rejected :=
    hsuffix.toFirstHit hmatched.hit
  exact ⟨exactConcreteCycleOfChoiceHead choiceLeft (readHeadNat c.focus)
    choiceRight hhead hchoice' hsuffix'⟩

/-- The canonical target-one rejecting cycle pins down the endpoint of every
raw exact cycle from the same semantic encoding.  First-hit uniqueness is
the only determinism principle used here; no semantic subtype is imposed on
the raw endpoint. -/
theorem exactConcreteCycle_semanticTargetOne_finish_eq_rejected
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity)
    {finish : Result}
    (raw : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) finish) :
    finish = .rejected := by
  obtain ⟨canonical⟩ := branchedCycle_semanticTargetOne_exact_nonempty
    c slot action hlookup htarget input clockZeros capacity runtime outer
      suffix hruntime hfocus hreads hwrites hstateCapacity honeCapacity
  exact raw.finish_unique canonical

/-- A target-one exact cycle cannot supply the accepting endpoint required by
an accepting slot-run tail. -/
theorem exactConcreteCycle_semanticTargetOne_not_accepted
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity)
    {z : Zipper Tape}
    (raw : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) (.accepted z)) : False := by
  have hfinish := exactConcreteCycle_semanticTargetOne_finish_eq_rejected
    c slot action hlookup htarget input clockZeros capacity runtime outer
      suffix hruntime hfocus hreads hwrites hstateCapacity honeCapacity raw
  cases hfinish

/-- Fold the exact rounds which consume existing state cells before the
subsequent growing phase. -/
def stopFree_targetConsumeState
    (remaining growth done : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetConsumeStart remaining growth done corridor left tail)
      (targetConsumeDone remaining growth done corridor left tail) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨0, by
        simpa [targetConsumeStart, targetConsumeDone] using
          ({ valid := ValidZeroRun.nil _
             stop_free := by intro m hm; simp at hm } :
            StopFreeValidZeroRun 0
              (targetConsumeStart 0 growth done corridor left tail)
              (targetConsumeStart 0 growth done corridor left tail))⟩
  | succ remaining ih =>
      let path := List.replicate (growth + remaining) (ulogCore codeZero) ++
        ulogCore codeOne :: corridor
      have hpath : path ≠ [] := by simp [path]
      obtain ⟨a, hround⟩ := stopFree_targetRoundExisting path hpath done
        (targetCodeCorridor_round_safe (growth + remaining) corridor hsafe)
        left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail)
      obtain ⟨b, htail⟩ := ih (done + 1) (ulogCore codeZero :: left)
      have hround' : StopFreeValidZeroRun a
          (targetConsumeStart (remaining + 1) growth done corridor left tail)
          (targetConsumeStart remaining growth (done + 1) corridor
            (ulogCore codeZero :: left) tail) := by
        dsimp [path] at hround
        cases remaining with
        | zero =>
            cases growth <;>
              simpa [targetConsumeStart, path, targetGrowStart,
                beforeRightPath, targetScanPath, List.replicate_succ,
                List.replicate_succ', List.cons_append, List.append_assoc,
                Nat.add_assoc] using hround
        | succ remaining =>
            have hcount : growth + (remaining + 1) =
                (growth + remaining) + 1 := by omega
            have hrepl :
                List.replicate (growth + (remaining + 1))
                    (ulogCore codeZero) =
                  ulogCore codeZero ::
                    List.replicate (growth + remaining)
                      (ulogCore codeZero) := by
              rw [hcount, List.replicate_succ]
            simpa [targetConsumeStart, path, targetGrowStart,
              beforeRightPath, targetScanPath, List.replicate_succ,
              List.replicate_succ', List.cons_append, List.append_assoc,
              Nat.add_assoc, hrepl] using hround
      have hall := hround'.append htail
      exact ⟨a + b, by
        simpa [targetConsumeStart, targetConsumeDone, path,
          targetScanPath, List.replicate_succ, List.replicate_succ',
          List.cons_append, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hall⟩

/-- The finite `SeenOne` mark sweep in the target-finish controller. -/
def stopFree_targetFinishSeenOne_many_core
    (done : ℕ) (left : List Tape) (terminal : Tape) (right : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨left, ulogCore stateMark,
          List.replicate done (ulogCore stateMark) ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishMany)
        ⟨List.replicate (done + 1) (ulogCore stateMark) ++ left,
          terminal, right⟩) := by
  have hstart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨left, ulogCore stateMark,
          List.replicate done (ulogCore stateMark) ++ terminal :: right⟩)
      (.running (.actionPhase .targetFinishMany)
        (beforeRightPath (List.replicate done (ulogCore stateMark))
          (ulogCore stateMark :: left) terminal right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases done <;>
        simp [beforeRightPath, targetFinishSeenOne_mark_core,
          List.replicate_succ]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hsweep := stopFree_rightPath_of (.actionPhase .targetFinishMany)
    (by decide) (List.replicate done (ulogCore stateMark)) (by
      intro x hx l y r
      have hx' : x = ulogCore stateMark :=
        (by simpa only [List.mem_replicate] using hx :
          done ≠ 0 ∧ x = ulogCore stateMark).2
      rw [hx']
      exact targetFinishMany_mark_core l y r)
    (ulogCore stateMark :: left) terminal right
  exact ⟨1 + done, by
    simpa [afterRightPath, List.replicate_succ, List.append_assoc] using
      hstart.append hsweep⟩

/-- Exact target-finish path for equal state/target counts. -/
def stopFree_targetFinishEqual
    (path : List Tape) (hpath : path ≠ []) (done : ℕ)
    (hdone : 2 ≤ done) (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateOne ::
            ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
  have hex : ∃ k, done = k + 2 := ⟨done - 2, by omega⟩
  let k := Nat.find hex
  have hdoneEq : done = k + 2 := Nat.find_spec hex
  rw [hdoneEq]
  let finishPath := targetFinishPath path (k + 2)
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases finishPath <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan0 := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) (ulogCore stateMark)
    (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hscan : StopFreeValidZeroRun path.length
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [finishPath, targetFinishPath, beforeRightPath,
          afterRightPath, hp, List.replicate_succ,
          List.append_assoc] using hscan0
  have hmark : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetFinishSeek_mark
        (path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateMark)
        (List.replicate k (ulogCore stateMark) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨a, hmany0⟩ := stopFree_targetFinishSeenOne_many_core k
    (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
    (ulogCore stateOne) (ulogCore stateSep :: tail)
  have hleftEq :
      List.replicate (k + 1) (ulogCore stateMark) ++
          (ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left) =
        ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark) ++
            (path.reverse ++ ulogCore targetBoundary :: left) := by
    simp [List.replicate_succ, List.append_assoc]
  have hmany : StopFreeValidZeroRun a
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    rw [hleftEq] at hmany0
    have hmarks : List.replicate (k + 2) (ulogCore stateMark) =
        ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark) := by
      have hk : k + 2 = Nat.succ (Nat.succ k) := by omega
      rw [hk, List.replicate_succ, List.replicate_succ]
    have hfinishLeft :
        (ulogCore stateMark :: ulogCore stateMark ::
            List.replicate k (ulogCore stateMark)) ++
          (path.reverse ++ ulogCore targetBoundary :: left) =
          finishPath.reverse ++ ulogCore targetBoundary :: left := by
      simp [finishPath, targetFinishPath, List.reverse_append, hmarks,
        List.append_assoc]
    rw [hfinishLeft] at hmany0
    simpa [afterRightPath] using hmany0
  have hrestoreStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath finishPath.reverse left (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases hr : finishPath.reverse with
      | nil =>
          simpa [afterRightPath, beforeLeftPath, hr] using
            targetFinishMany_one_core left (ulogCore targetBoundary)
              (ulogCore stateSep :: tail)
      | cons x xs =>
          simpa [afterRightPath, beforeLeftPath, hr,
            List.append_assoc] using
            targetFinishMany_one_core
              (xs ++ ulogCore targetBoundary :: left) x
              (ulogCore stateSep :: tail)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hrestore := stopFree_leftPathMap_of (.actionPhase .targetRestoreState)
    (by decide) finishPath.reverse restoreTargetCell (by
      intro x hx l y r
      have hx' : x ∈ finishPath := by simpa using hx
      by_cases hm : x = ulogCore stateMark
      · subst x
        simpa [restoreTargetCell] using targetRestoreState_mark l y r
      · have h := targetFinishPath_restore_safe path (k + 2) hsafe hx'
        simpa [restoreTargetCell, hm] using
          targetRestoreState_pass x hm h.1 h.2 l y r)
    left (ulogCore targetBoundary)
    (ulogCore stateOne :: ulogCore stateSep :: tail)
  have hmoveStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap finishPath.reverse restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate (k + 2) (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have hmap : finishPath.map restoreTargetCell =
          path ++ List.replicate (k + 2) (ulogCore stateZero) := by
        simp [finishPath, targetFinishPath, List.map_append,
          restoreTargetCell_path path hsafe, restoreTargetCell]
      rw [show afterLeftPathMap finishPath.reverse restoreTargetCell left
            (ulogCore targetBoundary)
            (ulogCore stateOne :: ulogCore stateSep :: tail) =
          ⟨left, ulogCore targetBoundary,
            path ++ List.replicate (k + 2) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩ by
          simp [afterLeftPathMap, hmap, List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.append_assoc] using
            targetRestoreState_boundary left x
              (xs ++ List.replicate (k + 2) (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [afterLeftPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have htarget := ((hstart.append hscan).append hmark).append hmany
  have hcleanup := (htarget.append hrestoreStart).append hrestore
  exact ⟨_, hcleanup.append hmoveStart⟩

/-- Exact erase-and-return path used when the requested target state is
shorter than the current workspace block. -/
def stopFree_targetShrink
    (extra : ℕ) (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running (.actionPhase .targetShrink)
        ⟨left, ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        ⟨left, ulogCore stateOne,
          ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
  have hstart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetShrink)
        ⟨left, ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetShrinkErase)
        (beforeRightPath (List.replicate extra (ulogCore stateZero))
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases extra <;>
        simp [beforeRightPath, targetShrink_start,
          List.replicate_succ, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have herase := stopFree_rightPathMap_of (.actionPhase .targetShrinkErase)
    (by decide) (List.replicate extra (ulogCore stateZero))
    (fun _ => MStarConcreteAlphabet.work) (by
      intro x hx l y r
      have hx' : x = ulogCore stateZero :=
        (by simpa only [List.mem_replicate] using hx :
          extra ≠ 0 ∧ x = ulogCore stateZero).2
      rw [hx']
      exact targetShrinkErase_zero l y r)
    (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
    (ulogCore stateSep :: tail)
  have hone : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetShrinkErase)
        (afterRightPathMap (List.replicate extra (ulogCore stateZero))
          (fun _ => MStarConcreteAlphabet.work)
          (ulogCore stateShrinkBoundary :: left) (ulogCore stateOne)
          (ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrinkEraseOne)
        ⟨MStarConcreteAlphabet.work ::
            List.replicate extra MStarConcreteAlphabet.work ++
              ulogCore stateShrinkBoundary :: left,
          ulogCore stateSep, tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPathMap, List.append_assoc] using
        targetShrinkErase_one
          (List.replicate extra MStarConcreteAlphabet.work ++
            ulogCore stateShrinkBoundary :: left)
          (ulogCore stateSep) tail
    · simp [afterRightPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hsep : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetShrinkEraseOne)
        ⟨MStarConcreteAlphabet.work ::
            List.replicate extra MStarConcreteAlphabet.work ++
              ulogCore stateShrinkBoundary :: left,
          ulogCore stateSep, tail⟩)
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (beforeLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [beforeLeftPath, List.replicate_succ,
        List.append_assoc] using
        targetShrinkEraseOne_sep
          (List.replicate extra MStarConcreteAlphabet.work ++
            ulogCore stateShrinkBoundary :: left)
          MStarConcreteAlphabet.work tail
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hreturn := stopFree_leftPath_of
    (.actionPhase .targetShrinkReturnBoundary) (by decide)
    (List.replicate (extra + 1) MStarConcreteAlphabet.work) (by
      intro x hx l y r
      have hx' : x = MStarConcreteAlphabet.work :=
        (by simpa only [List.mem_replicate] using hx :
          extra + 1 ≠ 0 ∧ x = MStarConcreteAlphabet.work).2
      rw [hx']
      exact targetShrinkReturn_work l y r)
    left (ulogCore stateShrinkBoundary)
    (MStarConcreteAlphabet.work :: tail)
  have hboundary : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetShrinkReturnBoundary)
        (afterLeftPath
          (List.replicate (extra + 1) MStarConcreteAlphabet.work)
          left (ulogCore stateShrinkBoundary)
          (MStarConcreteAlphabet.work :: tail)))
      (.running (.actionPhase .targetShrinkPlaceSep)
        ⟨ulogCore stateOne :: left, MStarConcreteAlphabet.work,
          List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterLeftPath, List.replicate_succ,
        List.append_assoc] using
        targetShrinkReturn_boundary left MStarConcreteAlphabet.work
          (List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail)
    · simp [afterLeftPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetShrinkPlaceSep)
        ⟨ulogCore stateOne :: left, MStarConcreteAlphabet.work,
          List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        ⟨left, ulogCore stateOne,
          ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [List.replicate_succ, List.append_assoc] using
        targetShrinkPlaceSep_step left (ulogCore stateOne)
          (List.replicate extra MStarConcreteAlphabet.work ++
            MStarConcreteAlphabet.work :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hprefix := (((hstart.append herase).append hone).append hsep).append hreturn
  exact ⟨_, (hprefix.append hboundary).append hplace⟩

/-- Exact target-finish path for the strictly shorter state/target case. -/
def stopFree_targetFinishShorter
    (path : List Tape) (hpath : path ≠ []) (done extra : ℕ)
    (hdone : 2 ≤ done) (hsafe : TargetFinishCorridorSafe path)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          targetFinishPath path done ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate done (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
  have hex : ∃ k, done = k + 2 := ⟨done - 2, by omega⟩
  let k := Nat.find hex
  have hdoneEq : done = k + 2 := Nat.find_spec hex
  rw [hdoneEq]
  let finishPath := targetFinishPath path (k + 2)
  have hstart : StopFreeValidZeroRun 1
      (.running .actionTarget
        ⟨left, ulogCore codeOne,
          finishPath ++ ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases finishPath <;>
        simp [beforeRightPath, actionTarget_done, List.append_assoc]
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hscan0 := stopFree_targetFinishSeek_path path hsafe
    (ulogCore targetBoundary :: left) (ulogCore stateMark)
    (ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
      ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: tail)
  have hscan : StopFreeValidZeroRun path.length
      (.running (.actionPhase .targetFinishSeek)
        (beforeRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    cases hp : path with
    | nil => exact (hpath hp).elim
    | cons x xs =>
        simpa [finishPath, targetFinishPath, beforeRightPath,
          afterRightPath, hp, List.replicate_succ,
          List.append_assoc] using hscan0
  have hmark : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishSeek)
        ⟨path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          ulogCore stateMark :: List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      exact targetFinishSeek_mark
        (path.reverse ++ ulogCore targetBoundary :: left)
        (ulogCore stateMark)
        (List.replicate k (ulogCore stateMark) ++
          ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨a, hmany0⟩ := stopFree_targetFinishSeenOne_many_core k
    (ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left)
    (ulogCore stateZero)
    (List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hleftEq :
      List.replicate (k + 1) (ulogCore stateMark) ++
          (ulogCore stateMark :: path.reverse ++
            ulogCore targetBoundary :: left) =
        ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark) ++
            (path.reverse ++ ulogCore targetBoundary :: left) := by
    simp [List.replicate_succ, List.append_assoc]
  have hmarks : List.replicate (k + 2) (ulogCore stateMark) =
      ulogCore stateMark :: ulogCore stateMark ::
        List.replicate k (ulogCore stateMark) := by
    have hk : k + 2 = Nat.succ (Nat.succ k) := by omega
    rw [hk, List.replicate_succ, List.replicate_succ]
  have hfinishLeft :
      (ulogCore stateMark :: ulogCore stateMark ::
          List.replicate k (ulogCore stateMark)) ++
        (path.reverse ++ ulogCore targetBoundary :: left) =
      finishPath.reverse ++ ulogCore targetBoundary :: left := by
    simp [finishPath, targetFinishPath, List.reverse_append, hmarks,
      List.append_assoc]
  have hmany : StopFreeValidZeroRun a
      (.running (.actionPhase .targetFinishSeenOne)
        ⟨ulogCore stateMark :: path.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateMark,
          List.replicate k (ulogCore stateMark) ++
            ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    rw [hleftEq, hfinishLeft] at hmany0
    simpa [afterRightPath] using hmany0
  have hshrinkStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetFinishMany)
        (afterRightPath finishPath (ulogCore targetBoundary :: left)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)))
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath] using
        targetFinishMany_zero_core
          (finishPath.reverse ++ ulogCore targetBoundary :: left)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail)
    · simp [afterRightPath, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  obtain ⟨b, hshrink0⟩ := stopFree_targetShrink extra
    (finishPath.reverse ++ ulogCore targetBoundary :: left) tail
  let restorePath := ulogCore stateOne :: finishPath.reverse
  have hshrink : StopFreeValidZeroRun b
      (.running (.actionPhase .targetShrink)
        ⟨finishPath.reverse ++ ulogCore targetBoundary :: left,
          ulogCore stateZero,
          List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail⟩)
      (.running (.actionPhase .targetRestoreState)
        (beforeLeftPath restorePath left (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    simpa [restorePath, beforeLeftPath, List.append_assoc] using hshrink0
  have hrestore := stopFree_leftPathMap_of (.actionPhase .targetRestoreState)
    (by decide) restorePath restoreTargetCell (by
      intro x hx l y r
      simp only [restorePath, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hm : ulogCore stateOne ≠ ulogCore stateMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        have hb : ulogCore stateOne ≠ ulogCore targetBoundary :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        have hp : ulogCore stateOne ≠ ulogCore pcMark :=
          ULogTapeDecoding.ulog_symbol_ne (by decide)
        simpa [restoreTargetCell, hm] using
          targetRestoreState_pass (ulogCore stateOne) hm hb hp l y r
      · have hx' : x ∈ finishPath := by simpa using hx
        by_cases hm : x = ulogCore stateMark
        · subst x
          simpa [restoreTargetCell] using targetRestoreState_mark l y r
        · have h := targetFinishPath_restore_safe path (k + 2) hsafe hx'
          simpa [restoreTargetCell, hm] using
            targetRestoreState_pass x hm h.1 h.2 l y r)
    left (ulogCore targetBoundary)
    (ulogCore stateSep ::
      List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)
  have hmoveStart : StopFreeValidZeroRun 1
      (.running (.actionPhase .targetRestoreState)
        (afterLeftPathMap restorePath restoreTargetCell left
          (ulogCore targetBoundary)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (path ++ List.replicate (k + 2) (ulogCore stateZero))
          (ulogCore codeOne :: left) (ulogCore stateOne)
          (ulogCore stateSep ::
            List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      have honeMark : ulogCore stateOne ≠ ulogCore stateMark :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have hmap : restorePath.reverse.map restoreTargetCell =
          path ++ List.replicate (k + 2) (ulogCore stateZero) ++
            [ulogCore stateOne] := by
        simp [restorePath, finishPath, targetFinishPath,
          List.reverse_append, List.map_append,
          restoreTargetCell_path path hsafe, restoreTargetCell, honeMark,
          List.append_assoc]
      rw [show afterLeftPathMap restorePath restoreTargetCell left
            (ulogCore targetBoundary)
            (ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail) =
          ⟨left, ulogCore targetBoundary,
            path ++ List.replicate (k + 2) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail⟩ by
          simp [afterLeftPathMap, hmap, List.append_assoc]]
      cases hp : path with
      | nil => exact (hpath hp).elim
      | cons x xs =>
          simpa [beforeRightPath, hp, List.append_assoc] using
            targetRestoreState_boundary left x
              (xs ++ List.replicate (k + 2) (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate (extra + 1) MStarConcreteAlphabet.work ++ tail)
    · simp [afterLeftPathMap, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have htarget := ((hstart.append hscan).append hmark).append hmany
  have htoRestore := ((htarget.append hshrinkStart).append hshrink).append hrestore
  exact ⟨_, htoRestore.append hmoveStart⟩

/-- Existing-state rounds followed by the exact target-finish controller. -/
def stopFree_targetExistingFinished
    (target extra : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ target) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetExistingStart target 0 extra corridor left tail)
      (targetRewriteFinished target extra corridor left tail) := by
  obtain ⟨a, hexisting⟩ := stopFree_targetExistingZeros target 0 extra
    corridor hsafe left tail
  cases extra with
  | zero =>
      obtain ⟨b, hfinish⟩ := stopFree_targetFinishEqual corridor hcorridor
        target htarget hsafe.2 (List.replicate target (ulogCore codeZero) ++ left)
        tail
      have hfinish' : StopFreeValidZeroRun b
          (targetExistingDone target 0 0 corridor left tail)
          (targetRewriteFinished target 0 corridor left tail) := by
        simpa [targetExistingDone, targetRewriteFinished,
          targetFinishPath, List.append_assoc] using hfinish
      exact ⟨a + b, hexisting.append hfinish'⟩
  | succ extra =>
      obtain ⟨b, hfinish⟩ := stopFree_targetFinishShorter corridor hcorridor
        target extra htarget hsafe.2
        (List.replicate target (ulogCore codeZero) ++ left) tail
      have hfinish' : StopFreeValidZeroRun b
          (targetExistingDone target 0 (extra + 1) corridor left tail)
          (targetRewriteFinished target (extra + 1) corridor left tail) := by
        simpa [targetExistingDone, targetRewriteFinished,
          targetFinishPath, List.replicate_succ, List.append_assoc] using hfinish
      exact ⟨a + b, hexisting.append hfinish'⟩

/-- Growing rounds followed by the equal finish controller. -/
def stopFree_targetGrowFinished
    (growth done : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (hdone : 2 ≤ done + growth) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetGrowStart growth done corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (done + growth) (ulogCore stateZero))
          (ulogCore codeOne :: List.replicate growth (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
  obtain ⟨a, hgrow⟩ := stopFree_targetGrowZeros growth done corridor hsafe
    left tail
  obtain ⟨b, hfinish⟩ := stopFree_targetFinishEqual corridor hcorridor
    (done + growth) (by simpa [Nat.add_comm] using hdone) hsafe.2
    (List.replicate growth (ulogCore codeZero) ++ left) tail
  have hfinish' : StopFreeValidZeroRun b
      (targetGrowDone growth done corridor left tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (done + growth) (ulogCore stateZero))
          (ulogCore codeOne :: List.replicate growth (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa [targetGrowDone, targetFinishPath, List.append_assoc] using hfinish
  exact ⟨a + b, hgrow.append hfinish'⟩

/-- The target rewrite when the requested target is no larger than the
current state block. -/
def stopFree_targetAtMostState
    (target extra : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ target) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetRawStart target (target + extra) corridor left tail)
      (targetRewriteFinished target extra corridor left tail) := by
  obtain ⟨n, h⟩ := stopFree_targetExistingFinished target extra corridor
    hcorridor htarget hsafe left tail
  cases target with
  | zero => omega
  | succ target =>
      have hrep :
          List.replicate ((target + 1) + extra) (ulogCore stateZero) =
            ulogCore stateZero ::
              List.replicate target (ulogCore stateZero) ++
                List.replicate extra (ulogCore stateZero) := by
        rw [List.replicate_add, List.replicate_succ]
      exact ⟨n, by
        simpa [targetRawStart, targetExistingStart, targetScanPath,
          hrep, List.append_assoc] using h⟩

/-- The target rewrite when current state cells must first be consumed and
then new workspace cells grown. -/
def stopFree_targetAtLeastState
    (current growth : ℕ) (corridor : List Tape) (hcorridor : corridor ≠ [])
    (htarget : 2 ≤ current + growth) (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (targetRawStart (current + growth) current corridor left
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
  obtain ⟨a, hconsume⟩ := stopFree_targetConsumeState current growth 0
    corridor hsafe left tail
  obtain ⟨b, hgrow⟩ := stopFree_targetGrowFinished growth current corridor
    hcorridor (by simpa [Nat.add_comm] using htarget) hsafe
    (List.replicate current (ulogCore codeZero) ++ left) tail
  have hsource :
      targetRawStart (current + growth) current corridor left
          (List.replicate growth MStarConcreteAlphabet.work ++ tail) =
        targetConsumeStart current growth 0 corridor left tail := by
    cases current with
    | zero =>
        cases growth <;>
          simp [targetRawStart, targetConsumeStart, targetGrowStart,
            targetScanPath, List.replicate_succ, List.append_assoc]
    | succ current =>
        have hsum : current + growth = growth + current := Nat.add_comm _ _
        have htarget' : current + 1 + growth = (growth + current) + 1 := by
          omega
        rw [htarget']
        simp [targetRawStart, targetConsumeStart, targetScanPath,
          List.replicate_succ, hsum, List.append_assoc]
  rw [← hsource] at hconsume
  have hconsume' : StopFreeValidZeroRun a
      (targetRawStart (current + growth) current corridor left
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (targetGrowStart growth current corridor
        (List.replicate current (ulogCore codeZero) ++ left) tail) := by
    simpa [targetConsumeDone] using hconsume
  have hcodes :
      List.replicate growth (ulogCore codeZero) ++
          List.replicate current (ulogCore codeZero) =
        List.replicate (current + growth) (ulogCore codeZero) := by
    rw [← List.replicate_add, Nat.add_comm]
  have hleft :
      ulogCore codeOne :: List.replicate growth (ulogCore codeZero) ++
          (List.replicate current (ulogCore codeZero) ++ left) =
        ulogCore codeOne ::
          List.replicate (current + growth) (ulogCore codeZero) ++ left := by
    simp only [List.cons_append]
    congr 1
    rw [← List.append_assoc, hcodes]
  have hgrow' : StopFreeValidZeroRun b
      (targetGrowStart growth current corridor
        (List.replicate current (ulogCore codeZero) ++ left) tail)
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (corridor ++ List.replicate (current + growth) (ulogCore stateZero))
          (ulogCore codeOne ::
            List.replicate (current + growth) (ulogCore codeZero) ++ left)
          (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa only [hleft] using hgrow
  exact ⟨a + b, hconsume'.append hgrow'⟩

/-- The nonhalting matched-action corridor in the case where the requested
state block is no larger than the current one.  This is the exact counterpart
of `reaches_matchedActionAtMostState`: in particular, the target rewrite and
the two move-bit steps are still ordinary slot-zero edges, with no hidden
`Reaches` conversion. -/
noncomputable def stopFree_matchedActionAtMostState
    (write target extra : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++
          List.replicate (target + extra) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left)
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  let targetCorridor :=
    moveBits m ++ movePath ++ writeHeadNat write :: runtime
  let actionLeft := ulogCore codeOne ::
    List.replicate write (ulogCore codeZero) ++ left
  obtain ⟨a, hwriteRun⟩ := stopFree_actionWriteValid write hwrite oldHead
    hhead
    (List.replicate target (ulogCore codeZero) ++
      ulogCore codeOne :: moveBits m ++ movePath) hwritePath left
    (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: tail)
  have hwriteRun' : StopFreeValidZeroRun a
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (targetRawStart target (target + extra) targetCorridor actionLeft tail) := by
    cases target <;>
      simpa [targetRawStart, targetCorridor, actionLeft, moveBits,
        beforeRightPath, List.replicate_succ, List.append_assoc] using hwriteRun
  obtain ⟨b, htargetRun⟩ := stopFree_targetAtMostState target extra
    targetCorridor (by simp [targetCorridor, moveBits]) htarget htargetPath
    actionLeft tail
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++ actionLeft
  have hmove : StopFreeValidZeroRun 2
      (targetRewriteFinished target extra targetCorridor actionLeft tail)
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left) (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
    cases hpath : movePath with
    | nil =>
        simpa [targetRewriteFinished, targetCorridor, actionLeft, moveLeft,
          moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove m moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail))
    | cons x xs =>
        simpa [targetRewriteFinished, targetCorridor, actionLeft, moveLeft,
          moveBits, matchedMoveLeft, beforeRightPath, hpath,
          List.append_assoc] using
          (stopFree_actionMove m moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate extra MStarConcreteAlphabet.work ++ tail))
  exact ⟨a + b + 2, (hwriteRun'.append htargetRun).append hmove⟩

/-- The nonhalting matched-action corridor in the state-growth case.  The
workspace consumption, growth, equal-finish sweep, and the move-bit decoder
are all retained as one stop-free concrete zero-run. -/
noncomputable def stopFree_matchedActionAtLeastState
    (write current growth : ℕ) (hwrite : write < 3)
    (htarget : 2 ≤ current + growth)
    (m : OneTapeTableau.Move) (movePath runtime : List Tape)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (left tail : List Tape) :
    Σ n, StopFreeValidZeroRun n
      (actionWriteStart write left
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write (current + growth) m left)
          (writeHeadNat write)
          (runtime ++ List.replicate (current + growth) (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  let target := current + growth
  let targetCorridor :=
    moveBits m ++ movePath ++ writeHeadNat write :: runtime
  let actionLeft := ulogCore codeOne ::
    List.replicate write (ulogCore codeZero) ++ left
  obtain ⟨a, hwriteRun⟩ := stopFree_actionWriteValid write hwrite oldHead
    hhead
    (List.replicate target (ulogCore codeZero) ++
      ulogCore codeOne :: moveBits m ++ movePath) (by
        simpa [target] using hwritePath) left
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ tail)
  have hwriteRun' : StopFreeValidZeroRun a
      (actionWriteStart write left
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        oldHead
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (targetRawStart target current targetCorridor actionLeft
        (List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    cases htarget' : target <;>
      simpa [targetRawStart, target, htarget', targetCorridor, actionLeft,
        moveBits, beforeRightPath, List.replicate_succ,
        List.append_assoc] using hwriteRun
  obtain ⟨b, htargetRun⟩ := stopFree_targetAtLeastState current growth
    targetCorridor (by simp [targetCorridor, moveBits]) (by simpa [target]
      using htarget) htargetPath actionLeft tail
  let moveLeft := ulogCore codeOne ::
    List.replicate target (ulogCore codeZero) ++ actionLeft
  have htargetRun' : StopFreeValidZeroRun b
      (targetRawStart target current targetCorridor actionLeft
        (List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          moveLeft (ulogCore stateOne) (ulogCore stateSep :: tail))) := by
    simpa [target, moveLeft, List.append_assoc] using htargetRun
  have hmove : StopFreeValidZeroRun 2
      (.running (.actionPhase .moveStart)
        (beforeRightPath
          (targetCorridor ++ List.replicate target (ulogCore stateZero))
          moveLeft (ulogCore stateOne) (ulogCore stateSep :: tail)))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m left) (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    cases hpath : movePath with
    | nil =>
        simpa [targetCorridor, actionLeft, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove m moveLeft (writeHeadNat write)
            (runtime ++ List.replicate target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))
    | cons x xs =>
        simpa [targetCorridor, actionLeft, moveLeft, moveBits,
          matchedMoveLeft, beforeRightPath, hpath, List.append_assoc] using
          (stopFree_actionMove m moveLeft x
            (xs ++ writeHeadNat write :: runtime ++
              List.replicate target (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: tail))
  exact ⟨a + b + 2, (hwriteRun'.append htargetRun').append hmove⟩

/-- Fold a certified mismatch prefix and then execute the matching rule in
the shrinking/equal target case, retaining the complete deterministic suffix
as a genuine stop-free zero-run. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (start final : RuleCursorData) (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual start (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix))) := by
  obtain ⟨a, hprefix⟩ := stopFree_mismatchPrefix cursorMismatchStopFreeStep
    slot current actual programToHead runtime outer
    (ulogCore stateSep :: suffix) trace
  obtain ⟨b, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    final.boundary hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime hread hcorridor hreadPath (ulogCore stateSep :: suffix)
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> decide
  obtain ⟨d, haction⟩ := stopFree_matchedActionAtMostState
    r.action.write r.action.target extra hwrite htargetLower r.action.move
    (cursorMatchedMovePath rs programToHead) runtime (readHeadNat r.read)
    hhead hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read final.boundary
      ((List.replicate final.done (ulogCore codeZero) ++
        ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer))
    suffix
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have hmatched' : StopFreeValidZeroRun b
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++
              ulogCore pcMark :: outer))
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate (r.action.target + extra)
          (ulogCore stateZero) ++ ulogCore stateOne ::
            ulogCore stateSep :: suffix)) := by
    have hcurrent : current = r.action.target + extra :=
      hsource.symm.trans htarget
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      hcurrent, List.append_assoc] using hmatched
  exact ⟨a + b + d, (hprefix.append hmatched').append haction⟩

/-- Fold a certified mismatch prefix and then execute the matching rule in
the state-growth case, again without converting any part of the suffix to an
unlabelled reachability witness. -/
noncomputable def stopFree_mismatchPrefix_matchedAtLeast
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (start final : RuleCursorData) (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual start (skip ++ r :: rs)
        programToHead runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))) := by
  obtain ⟨a, hprefix⟩ := stopFree_mismatchPrefix cursorMismatchStopFreeStep
    slot current actual programToHead runtime outer
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ suffix) trace
  obtain ⟨b, hmatched⟩ := stopFree_ruleCursorMatched_actionWrite
    final.boundary hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime hread hcorridor hreadPath
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> decide
  have htargetEq : r.action.target = current + growth := by
    rw [htarget, hmatch.1]
  have htargetLower' : 2 ≤ current + growth := by
    rw [← htargetEq]
    exact htargetLower
  have hwritePath' : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead) := by
    simpa [htargetEq] using hwritePath
  obtain ⟨d, haction⟩ := stopFree_matchedActionAtLeastState
    r.action.write current growth hwrite htargetLower' r.action.move
    (cursorMatchedMovePath rs programToHead) runtime (readHeadNat r.read)
    hhead hwritePath' htargetPath
    (matchedReadLeftAt r.slot r.source r.read final.boundary
      ((List.replicate final.done (ulogCore codeZero) ++
        ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer))
    suffix
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have hmatched' : StopFreeValidZeroRun b
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++
              ulogCore pcMark :: outer))
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix)) := by
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      htargetEq, List.append_assoc] using hmatched
  have haction' : StopFreeValidZeroRun d
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++
              ulogCore pcMark :: outer))
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))) := by
    simpa [htargetEq] using haction
  exact ⟨a + b + d, (hprefix.append hmatched').append haction'⟩

/-- Exact successful internal-left cycle after a certified mismatch prefix
in the state-growth case.  The physical left endpoint is removed from the
program scan and becomes the new simulated head; the written old head is
placed at the front of the concrete right tape. -/
noncomputable def stopFree_mismatchPrefix_matchedAtLeast_leftInternal_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (cell : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (programToHead ++ [cell]) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (programToHead ++ [cell])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (programToHead ++ [cell]))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (programToHead ++ [cell])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (programToHead ++ [cell]) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (programToHead ++ [cell])))
    (hcell : PayloadCell cell)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (programToHead ++ [cell]) runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtLeast
    slot current actual (programToHead ++ [cell]) runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (programToHead ++ [cell]) runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  have hscan' : MoveScanSafe
      (cursorMatchedMovePath rs programToHead ++ [cell]) := by
    simpa [cursorMatchedMovePath, List.append_assoc] using hscan
  obtain ⟨b, hcleanup⟩ := stopFree_moveLeftInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer cell (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan' hcell hhead hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (programToHead ++ [cell]))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cursorMatchedMovePath, cleanedCycleLeft, List.append_assoc] using
      hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- First-hit strengthening of the certified internal-left cycle in the
state-growth case. -/
noncomputable def exactCycle_certifiedFirstMatchAtLeast_leftInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input (cell :: leftTape))
      (clockCellsAfter rightTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input (cell :: leftTape))
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape)))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape))))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input (cell :: leftTape)) ++
        writeHeadNat r.action.write ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input (cell :: leftTape))))
    (hrestoreClock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input (cell :: leftTape)
  let tailProgramToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft :=
    dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
      ulogCore pcMark :: outer
  let choiceRight := clockCellsAfter rightTape clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros rightTape hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot
    (cell :: leftTape) hleft (skip ++ r :: rs) (by simp) input outer
    (readHeadNat actual) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil
      (cell :: leftTape) (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath
        (cell :: leftTape) (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
        input outer (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hpath : programToHead = tailProgramToHead ++ [cell] := by
    simp [programToHead, tailProgramToHead, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (clockCellsAfter rightTape clockZeros runtime) certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtLeast_leftInternal_cycle
      slot current actual tailProgramToHead cell
      (clockCellsAfter rightTape clockZeros runtime) outer suffix
      skip r rs (canonicalRuleCursor skip (r :: rs))
      (by simpa [hpath] using trace) hmatch growth htarget hread hwrite
      htargetLower hmove hboundary
      (by simpa [programToHead, hpath] using hcorridor)
      (by simpa [programToHead, hpath] using hreadPath)
      (by simpa [programToHead, hpath] using hwritePath)
      (by simpa [programToHead, hpath] using htargetPath)
      (by simpa [programToHead, hpath] using hscan)
      (hleft cell (by simp)) hrestoreClock hprogram
  have hfull' := hfull
  have hstartEq :
      ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          (tailProgramToHead ++ [cell])
          (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix) =
        dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
          input outer (readHeadNat actual)
          (clockCellsAfter rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne ::
                (ulogCore stateSep ::
                  List.replicate growth MStarConcreteAlphabet.work ++
                    suffix)) := by
    calc
      _ = ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          programToHead (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix) := by
              rw [hpath]
      _ = _ := by
        change ruleCursorResult slot current actual
            (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
            (cursorDynamicProgramToHead input (cell :: leftTape))
            (clockCellsAfter rightTape clockZeros runtime) outer
            (ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ suffix) = _
        exact (dynamicRuleSourceStarted_eq_cursorResult slot current actual
          (cell :: leftTape) input skip r rs
          (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix)).symm
  rw [hstartEq] at hfull'
  have hleftTail : PayloadPathSafe leftTape := by
    intro x hx
    exact hleft x (by simp [hx])
  have hprogramRestored : tailProgramToHead.map restoreProgramCell =
      tailProgramToHead :=
    cursorDynamicProgramToHead_restored input leftTape hleftTail
  have hclean := cleanedCursorCycleLeft_eq skip r rs tailProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
        input outer (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    simpa [choiceRight, programToHead, tailProgramToHead, clockCellsAfter,
      List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Exact successful internal-left cycle after a certified mismatch prefix
in the shrinking/equal target case.  The physical left endpoint is moved
under the head, the written old head is retained on the right, and released
state cells remain in the fixed-capacity workspace. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost_leftInternal_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (cell : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (programToHead ++ [cell]) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (programToHead ++ [cell])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (programToHead ++ [cell]))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (programToHead ++ [cell])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (programToHead ++ [cell]) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (programToHead ++ [cell])))
    (hcell : PayloadCell cell)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (programToHead ++ [cell]) runtime outer
          (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtMost
    slot current actual (programToHead ++ [cell]) runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch extra
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (programToHead ++ [cell]) runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  have hscan' : MoveScanSafe
      (cursorMatchedMovePath rs programToHead ++ [cell]) := by
    simpa [cursorMatchedMovePath, List.append_assoc] using hscan
  obtain ⟨b, hcleanup⟩ := stopFree_moveLeftInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer cell (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan' hcell hhead hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (programToHead ++ [cell]))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cursorMatchedMovePath, cleanedCycleLeft, List.append_assoc] using
      hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- First-hit strengthening of the certified internal-left cycle in the
shrinking/equal target case. -/
noncomputable def exactCycle_certifiedFirstMatchAtMost_leftInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (cell : Tape) (leftTape : List Tape)
    (hleft : PayloadPathSafe (cell :: leftTape))
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input (cell :: leftTape))
      (clockCellsAfter rightTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input (cell :: leftTape))
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape)))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input (cell :: leftTape))))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input (cell :: leftTape)) ++
        writeHeadNat r.action.write ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input (cell :: leftTape))))
    (hrestoreClock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input (cell :: leftTape)
  let tailProgramToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft :=
    dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
      ulogCore pcMark :: outer
  let choiceRight := clockCellsAfter rightTape clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> native_decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros rightTape hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot
    (cell :: leftTape) hleft (skip ++ r :: rs) (by simp) input outer
    (readHeadNat actual) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (cell :: leftTape) (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil
      (cell :: leftTape) (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath
        (cell :: leftTape) (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
        input outer (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hpath : programToHead = tailProgramToHead ++ [cell] := by
    simp [programToHead, tailProgramToHead, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (clockCellsAfter rightTape clockZeros runtime) certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtMost_leftInternal_cycle
      slot current actual tailProgramToHead cell
      (clockCellsAfter rightTape clockZeros runtime) outer suffix
      skip r rs (canonicalRuleCursor skip (r :: rs))
      (by simpa [hpath] using trace) hmatch extra htarget hread hwrite
      htargetLower hmove hboundary
      (by simpa [programToHead, hpath] using hcorridor)
      (by simpa [programToHead, hpath] using hreadPath)
      (by simpa [programToHead, hpath] using hwritePath)
      (by simpa [programToHead, hpath] using htargetPath)
      (by simpa [programToHead, hpath] using hscan)
      (hleft cell (by simp)) hrestoreClock hprogram
  have hfull' := hfull
  have hstartEq :
      ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          (tailProgramToHead ++ [cell])
          (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep :: suffix) =
        dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
          input outer (readHeadNat actual)
          (clockCellsAfter rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix) := by
    calc
      _ = ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          programToHead (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep :: suffix) := by rw [hpath]
      _ = _ := by
        change ruleCursorResult slot current actual
            (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
            (cursorDynamicProgramToHead input (cell :: leftTape))
            (clockCellsAfter rightTape clockZeros runtime) outer
            (ulogCore stateSep :: suffix) = _
        exact (dynamicRuleSourceStarted_eq_cursorResult slot current actual
          (cell :: leftTape) input skip r rs
          (clockCellsAfter rightTape clockZeros runtime) outer
          (ulogCore stateSep :: suffix)).symm
  rw [hstartEq] at hfull'
  have hleftTail : PayloadPathSafe leftTape := by
    intro x hx
    exact hleft x (by simp [hx])
  have hprogramRestored : tailProgramToHead.map restoreProgramCell =
      tailProgramToHead :=
    cursorDynamicProgramToHead_restored input leftTape hleftTail
  have hclean := cleanedCursorCycleLeft_eq skip r rs tailProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot (cell :: leftTape) (skip ++ r :: rs)
        input outer (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    simpa [choiceRight, programToHead, tailProgramToHead, clockCellsAfter,
      List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Exact successful internal-right cycle after a certified mismatch prefix
in the shrinking/equal target case.  The action fold leaves the released
state cells as workspace, and the complete move/restore cleanup remains in
the same stop-free run. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost_rightInternal_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (cell : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead
      (cell :: runtime) (initialRuleCursor (skip ++ r :: rs))
      skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) (cell :: runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: cell :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hcell : PayloadCell cell)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead (cell :: runtime) outer (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtMost
    slot current actual programToHead (cell :: runtime) outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch extra
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead (cell :: runtime) skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveRightInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write) cell
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hhead hcell hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (cell :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cleanedCycleLeft, List.append_assoc] using hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- Exact successful internal-right cycle after a certified mismatch prefix
in the state-growth case.  The action fold and the complete move/restore
cleanup remain one stop-free run, so the advertised `cycleStart` is the first
cycle boundary reached after the selected slot edge. -/
noncomputable def stopFree_mismatchPrefix_matchedAtLeast_rightInternal_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (cell : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead
      (cell :: runtime) (initialRuleCursor (skip ++ r :: rs))
      skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) (cell :: runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: cell :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hcell : PayloadCell cell)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead (cell :: runtime) outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtLeast
    slot current actual programToHead (cell :: runtime) outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead (cell :: runtime) skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveRightInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write) cell
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan hhead hcell hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (cell :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cleanedCycleLeft, List.append_assoc] using hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- First-hit strengthening of the certified internal-right cycle in the
shrinking/equal target case. -/
noncomputable def exactCycle_certifiedFirstMatchAtMost_rightInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (cell : Tape) (rightTape : List Tape)
    (hright : PayloadPathSafe (cell :: rightTape))
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter (cell :: rightTape) clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (cell :: clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write :: cell ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hrestoreClock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape) ++
                  [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
            [unheadTape (writeHeadNat r.action.write)])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore (cell :: rightTape) clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter rightTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (cell :: rightTape) clockZeros runtime ++
      List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros (cell :: rightTape) hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore (cell :: rightTape) clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hclockEq : clockCellsAfter (cell :: rightTape) clockZeros runtime =
      cell :: clockCellsAfter rightTape clockZeros runtime := by
    simp [clockCellsAfter, List.append_assoc]
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (cell :: clockCellsAfter rightTape clockZeros runtime)
    (by simpa [hclockEq] using certs) (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtMost_rightInternal_cycle
      slot current actual programToHead cell
      (clockCellsAfter rightTape clockZeros runtime) outer suffix
      skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch extra
      htarget hread hwrite htargetLower hmove hboundary
      (by simpa [programToHead] using hcorridor)
      (by simpa [programToHead] using hreadPath)
      (by simpa [programToHead] using hwritePath)
      (by simpa [programToHead] using htargetPath)
      (by simpa [programToHead] using hscan) (hright cell (by simp))
      hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (cell :: clockCellsAfter rightTape clockZeros runtime) outer
    (ulogCore stateSep :: suffix)] at hfull'
  let newLeft := unheadTape (writeHeadNat r.action.write) :: leftTape
  let newProgramToHead := cursorDynamicProgramToHead input newLeft
  have hnewLeftSafe : PayloadPathSafe newLeft := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact unheadTape_payloadCell _ (by
        interval_cases r.action.write <;> decide)
    · exact hleft x hx
  have hmovePath : cursorMatchedMovePath rs programToHead ++
        [unheadTape (writeHeadNat r.action.write)] =
      cursorMatchedMovePath rs newProgramToHead := by
    simp [programToHead, newProgramToHead, newLeft,
      cursorMatchedMovePath, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have hprogramPath : cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)] =
      cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs newProgramToHead := by
    calc
      cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)] =
          cursorCleanupProgramPrefix skip r ++
            (cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) :=
        List.append_assoc _ _ _
      _ = cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs newProgramToHead := by rw [hmovePath]
  rw [hprogramPath] at hfull'
  have hprogramRestored : newProgramToHead.map restoreProgramCell =
      newProgramToHead :=
    cursorDynamicProgramToHead_restored input newLeft hnewLeftSafe
  have hclean := cleanedCursorCycleLeft_eq skip r rs newProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath newLeft (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter rightTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    simpa [choiceRight, programToHead, newLeft, List.append_assoc, hclockEq]
      using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- First-hit strengthening of the certified internal-right cycle in the
state-growth case. -/
noncomputable def exactCycle_certifiedFirstMatchAtLeast_rightInternal
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (cell : Tape) (rightTape : List Tape)
    (hright : PayloadPathSafe (cell :: rightTape))
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter (cell :: rightTape) clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (cell :: clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write :: cell ::
          clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hrestoreClock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape) ++
                  [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
            [unheadTape (writeHeadNat r.action.write)])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore (cell :: rightTape) clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter rightTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (cell :: rightTape) clockZeros runtime ++
      List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros (cell :: rightTape) hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore (cell :: rightTape) clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hclockEq : clockCellsAfter (cell :: rightTape) clockZeros runtime =
      cell :: clockCellsAfter rightTape clockZeros runtime := by
    simp [clockCellsAfter, List.append_assoc]
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (cell :: clockCellsAfter rightTape clockZeros runtime)
    (by simpa [hclockEq] using certs) (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtLeast_rightInternal_cycle
      slot current actual programToHead cell
      (clockCellsAfter rightTape clockZeros runtime) outer suffix
      skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch growth
      htarget hread hwrite htargetLower hmove hboundary
      (by simpa [programToHead] using hcorridor)
      (by simpa [programToHead] using hreadPath)
      (by simpa [programToHead] using hwritePath)
      (by simpa [programToHead] using htargetPath)
      (by simpa [programToHead] using hscan) (hright cell (by simp))
      hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (cell :: clockCellsAfter rightTape clockZeros runtime) outer
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hfull'
  let newLeft := unheadTape (writeHeadNat r.action.write) :: leftTape
  let newProgramToHead := cursorDynamicProgramToHead input newLeft
  have hnewLeftSafe : PayloadPathSafe newLeft := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact unheadTape_payloadCell _ (by
        interval_cases r.action.write <;> decide)
    · exact hleft x hx
  have hmovePath : cursorMatchedMovePath rs programToHead ++
        [unheadTape (writeHeadNat r.action.write)] =
      cursorMatchedMovePath rs newProgramToHead := by
    simp [programToHead, newProgramToHead, newLeft,
      cursorMatchedMovePath, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have hprogramPath : cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)] =
      cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs newProgramToHead := by
    calc
      cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)] =
          cursorCleanupProgramPrefix skip r ++
            (cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) :=
        List.append_assoc _ _ _
      _ = cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs newProgramToHead := by rw [hmovePath]
  rw [hprogramPath] at hfull'
  have hprogramRestored : newProgramToHead.map restoreProgramCell =
      newProgramToHead :=
    cursorDynamicProgramToHead_restored input newLeft hnewLeftSafe
  have hclean := cleanedCursorCycleLeft_eq skip r rs newProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath newLeft (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          headTapeOfCell cell,
          clockCellsAfter rightTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    simpa [choiceRight, programToHead, newLeft, List.append_assoc, hclockEq]
      using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-! ### State-growth left-boundary exact cycle -/

/-- Exact successful left-boundary cycle after a certified mismatch prefix in
the strictly shrinking case.  The boundary shift consumes the distinguished
outer `work` cell, while all released state cells remain in the fixed-capacity
state workspace. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost_leftBoundary_cycle
    (slot : Bool) (current actual : ℕ) (input : List Bool)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input []) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + (extra + 1))
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead input [])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead input []) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs
          (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [leftBoundaryMarker input]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
                [leftBoundaryMarker input])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
          [leftBoundaryMarker input])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (cursorDynamicProgramToHead input []) runtime
        (MStarConcreteAlphabet.work :: outer) (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtMost
    slot current actual (cursorDynamicProgramToHead input []) runtime
    (MStarConcreteAlphabet.work :: outer) suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch
    (extra + 1) htarget hread hwrite htargetLower hcursorBoundary hcorridor
    hreadPath hwritePath htargetPath
  have hp := cursorDynamicProgramToHead_emptyLeft_split input
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (cursorDynamicProgramToHead input []) runtime skip r rs trace
    (MStarConcreteAlphabet.work :: outer)
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hp, cursorMatchedMovePath, List.append_assoc]
  obtain ⟨b, hcleanup⟩ := stopFree_moveLeftBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs (leftBoundaryScanPrefix input))
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) (leftBoundaryMarker input) outer
    (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (extra + 1) MStarConcreteAlphabet.work ++ suffix)
    (by simpa [hmoveSplit] using hscan) (leftBoundaryMarker_valid input)
    hshift hreturn hhead hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))
            outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [hmoveSplit, cleanedCycleLeft, List.reverse_append,
      List.map_append, List.append_assoc] using hcleanup
  have hall := haction.append hcleanup'
  have hprogramRestored :
      (cursorDynamicProgramToHead input []).map restoreProgramCell =
        cursorDynamicProgramToHead input [] :=
    cursorDynamicProgramToHead_restored input [] (by simp [PayloadPathSafe])
  have hclean := cleanedCursorCycleLeft_eq skip r rs
    (cursorDynamicProgramToHead input []) outer hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hall
  exact ⟨a + b, hall⟩

/-- First-hit strengthening of the certified left-boundary cycle in the
strictly shrinking case. -/
noncomputable def exactCycle_certifiedFirstMatchAtMost_leftBoundary
    (slot : Bool) (current actual : ℕ) (input : List Bool)
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input [])
      (clockCellsAfter rightTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + (extra + 1))
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead input [])
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead input []) ++
          writeHeadNat r.action.write ::
            clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs
          (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [leftBoundaryMarker input]))
    (hrestoreClock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
                [leftBoundaryMarker input])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
          [leftBoundaryMarker input])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩) := by
  let choiceLeft := dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
    ulogCore pcMark :: MStarConcreteAlphabet.work :: outer
  let choiceRight := clockCellsAfter rightTape clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros rightTape hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .chooseSlot
        ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot []
    (by simp [PayloadPathSafe]) (skip ++ r :: rs) (by simp) input
    (MStarConcreteAlphabet.work :: outer) (readHeadNat actual) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath [] (skip ++ r :: rs) input)
          (MStarConcreteAlphabet.work :: outer) (ulogCore pcMark)
          (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil [] (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath [] (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark ::
                  MStarConcreteAlphabet.work :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark ::
                  MStarConcreteAlphabet.work :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) input
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have trace := mismatchCertificateList_initial_trace slot current actual
    (cursorDynamicProgramToHead input [])
    (clockCellsAfter rightTape clockZeros runtime) certs (by simp)
  have hcursorBoundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtMost_leftBoundary_cycle
      slot current actual input (clockCellsAfter rightTape clockZeros runtime)
      outer suffix skip r rs (canonicalRuleCursor skip (r :: rs)) trace
      hmatch extra htarget hread hwrite htargetLower hmove hcursorBoundary
      hcorridor hreadPath hwritePath htargetPath hscan hshift hreturn
      hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    [] input skip r rs (clockCellsAfter rightTape clockZeros runtime)
    (MStarConcreteAlphabet.work :: outer) (ulogCore stateSep :: suffix)] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) input
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix⟩) := by
    simpa [choiceRight, clockCellsAfter, List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Exact successful left-boundary cycle after a certified mismatch prefix in
the state-growth case.  The boundary shift consumes the distinguished outer
`work` cell, while the state workspace (and hence its capacity) is unchanged.
-/
noncomputable def stopFree_mismatchPrefix_matchedAtLeast_leftBoundary_cycle
    (slot : Bool) (current actual : ℕ) (input : List Bool)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (cursorDynamicProgramToHead input []) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead input [])
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead input []) ++
          writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs
          (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [leftBoundaryMarker input]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
                [leftBoundaryMarker input])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
          [leftBoundaryMarker input])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (cursorDynamicProgramToHead input []) runtime
        (MStarConcreteAlphabet.work :: outer)
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtLeast
    slot current actual (cursorDynamicProgramToHead input []) runtime
    (MStarConcreteAlphabet.work :: outer) suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hcursorBoundary hcorridor hreadPath
    hwritePath htargetPath
  have hp := cursorDynamicProgramToHead_emptyLeft_split input
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (cursorDynamicProgramToHead input []) runtime skip r rs trace
    (MStarConcreteAlphabet.work :: outer)
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hp, cursorMatchedMovePath, List.append_assoc]
  obtain ⟨b, hcleanup⟩ := stopFree_moveLeftBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs (leftBoundaryScanPrefix input))
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) (leftBoundaryMarker input) outer
    (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    (by simpa [hmoveSplit] using hscan) (leftBoundaryMarker_valid input)
    hshift hreturn hhead hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))
            outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [hmoveSplit, cleanedCycleLeft, List.reverse_append,
      List.map_append, List.append_assoc] using hcleanup
  have hall := haction.append hcleanup'
  have hprogramRestored :
      (cursorDynamicProgramToHead input []).map restoreProgramCell =
        cursorDynamicProgramToHead input [] :=
    cursorDynamicProgramToHead_restored input [] (by simp [PayloadPathSafe])
  have hclean := cleanedCursorCycleLeft_eq skip r rs
    (cursorDynamicProgramToHead input []) outer hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hall
  exact ⟨a + b, hall⟩

/-- First-hit strengthening of the certified left-boundary cycle in the
state-growth case.  The clock prefix reaches the selected `chooseSlot` for the
first time, and the selected suffix is stop-free through outer-cell
consumption and the restored `cycleStart`. -/
noncomputable def exactCycle_certifiedFirstMatchAtLeast_leftBoundary
    (slot : Bool) (current actual : ℕ) (input : List Bool)
    (rightTape : List Tape) (hright : PayloadPathSafe rightTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input [])
      (clockCellsAfter rightTape clockZeros runtime) skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .left)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs (cursorDynamicProgramToHead input [])
        (readHeadNat r.read)
        (clockCellsAfter rightTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs (cursorDynamicProgramToHead input []))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs (cursorDynamicProgramToHead input []) ++
          writeHeadNat r.action.write ::
            clockCellsAfter rightTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (cursorDynamicProgramToHead input [])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs
          (leftBoundaryScanPrefix input)).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [leftBoundaryMarker input]))
    (hrestoreClock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
                [leftBoundaryMarker input])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
          [leftBoundaryMarker input])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  let choiceLeft := dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
    ulogCore pcMark :: MStarConcreteAlphabet.work :: outer
  let choiceRight := clockCellsAfter rightTape clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> native_decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros rightTape hright choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer,
          readHeadNat actual,
          clockCellsBefore rightTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .chooseSlot
        ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot []
    (by simp [PayloadPathSafe]) (skip ++ r :: rs) (by simp) input
    (MStarConcreteAlphabet.work :: outer) (readHeadNat actual) choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath [] (skip ++ r :: rs) input)
          (MStarConcreteAlphabet.work :: outer) (ulogCore pcMark)
          (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil [] (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath [] (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark ::
                  MStarConcreteAlphabet.work :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark ::
                  MStarConcreteAlphabet.work :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) input
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have trace := mismatchCertificateList_initial_trace slot current actual
    (cursorDynamicProgramToHead input [])
    (clockCellsAfter rightTape clockZeros runtime) certs (by simp)
  have hcursorBoundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtLeast_leftBoundary_cycle
      slot current actual input (clockCellsAfter rightTape clockZeros runtime)
      outer suffix skip r rs (canonicalRuleCursor skip (r :: rs)) trace
      hmatch growth htarget hread hwrite htargetLower hmove hcursorBoundary
      hcorridor hreadPath hwritePath htargetPath hscan hshift hreturn
      hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    [] input skip r rs (clockCellsAfter rightTape clockZeros runtime)
    (MStarConcreteAlphabet.work :: outer)
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot [] (skip ++ r :: rs) input
        (MStarConcreteAlphabet.work :: outer) (readHeadNat actual)
        choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath [] (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter
              (unheadTape (writeHeadNat r.action.write) :: rightTape)
              clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    simpa [choiceRight, clockCellsAfter, List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Exact successful right-boundary cycle after a certified mismatch prefix
in the shrinking-target case.  One of the released state cells is consumed
by the boundary extension, while the remaining `extra` cells stay available
as workspace. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost_rightBoundary_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (boundary : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead
      (boundary :: runtime) (initialRuleCursor (skip ++ r :: rs))
      skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + (extra + 1))
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) (boundary :: runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: boundary :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe
      (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
        [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead (boundary :: runtime) outer
          (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtMost
    slot current actual programToHead (boundary :: runtime) outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch
    (extra + 1) htarget hread hwrite htargetLower hcursorBoundary hcorridor
    hreadPath hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead (boundary :: runtime) skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveRightBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write) boundary
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      [ulogCore stateOne])
    (ulogCore stateSep)
    (List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hboundary
    (by simpa [List.append_assoc] using hshift)
    (by simpa [List.append_assoc] using hreturn) hhead hclock
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate (extra + 1) MStarConcreteAlphabet.work ++
                  suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [List.replicate_succ, cleanedCycleLeft, List.append_assoc] using
      hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

noncomputable def stopFree_mismatchPrefix_matchedAtLeast_rightBoundary_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead : List Tape) (boundary : Tape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead
      (boundary :: runtime) (initialRuleCursor (skip ++ r :: rs))
      skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcursorBoundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) (boundary :: runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: boundary :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe
      (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
        [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)])) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead (boundary :: runtime) outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtLeast
    slot current actual programToHead (boundary :: runtime) outer
    (MStarConcreteAlphabet.work :: suffix)
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hcursorBoundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead (boundary :: runtime) skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveRightBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write) boundary
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      [ulogCore stateOne])
    (ulogCore stateSep) suffix hscan hboundary
    (by simpa [List.append_assoc] using hshift)
    (by simpa [List.append_assoc] using hreturn) hhead hclock
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                MStarConcreteAlphabet.work :: suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cleanedCycleLeft, List.append_assoc] using hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- First-hit strengthening of the certified right-boundary cycle in the
shrinking-target case. -/
noncomputable def exactCycle_certifiedFirstMatchAtMost_rightBoundary
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + (extra + 1))
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write :: clockBoundaryAfter clockZeros ::
          clockTailAfter clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hshift : ShiftRuntimeSafe
      (clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne]).reverse ++ [clockBoundaryAfter clockZeros]))
    (hrestoreClock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape) ++
                  [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
            [unheadTape (writeHeadNat r.action.write)])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore [] clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight := clockCellsAfter [] clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros [] (by simp [PayloadPathSafe]) choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore [] clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead
    (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
    certs (by simp)
  have hcursorBoundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtMost_rightBoundary_cycle
      slot current actual programToHead (clockBoundaryAfter clockZeros)
      (clockTailAfter clockZeros runtime) outer suffix skip r rs
      (canonicalRuleCursor skip (r :: rs)) trace hmatch extra htarget
      hread hwrite htargetLower hmove hcursorBoundary
      (by simpa [programToHead] using hcorridor)
      (by simpa [programToHead] using hreadPath)
      (by simpa [programToHead] using hwritePath)
      (by simpa [programToHead] using htargetPath)
      (by simpa [programToHead] using hscan)
      (clockBoundaryAfter_valid clockZeros) hshift hreturn hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime) outer
    (ulogCore stateSep :: suffix)] at hfull'
  let newLeft := unheadTape (writeHeadNat r.action.write) :: leftTape
  let newProgramToHead := cursorDynamicProgramToHead input newLeft
  have hnewLeftSafe : PayloadPathSafe newLeft := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact unheadTape_payloadCell _ (by
        interval_cases r.action.write <;> decide)
    · exact hleft x hx
  have hmovePath : cursorMatchedMovePath rs programToHead ++
        [unheadTape (writeHeadNat r.action.write)] =
      cursorMatchedMovePath rs newProgramToHead := by
    simp [programToHead, newProgramToHead, newLeft,
      cursorMatchedMovePath, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have hprogramPath : cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)] =
      cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs newProgramToHead := by
    calc
      cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)] =
          cursorCleanupProgramPrefix skip r ++
            (cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) :=
        List.append_assoc _ _ _
      _ = cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs newProgramToHead := by rw [hmovePath]
  rw [hprogramPath] at hfull'
  have hprogramRestored : newProgramToHead.map restoreProgramCell =
      newProgramToHead :=
    cursorDynamicProgramToHead_restored input newLeft hnewLeftSafe
  have hclean := cleanedCursorCycleLeft_eq skip r rs newProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath newLeft (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    simpa [choiceRight, programToHead, newLeft, hdecomp,
      List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- First-hit strengthening of the certified right-boundary cycle in the
state-growth case.  The clock prefix reaches the selected `chooseSlot` for the
first time, and the selected suffix is stop-free through the boundary shift
and restored `cycleStart`. -/
noncomputable def exactCycle_certifiedFirstMatchAtLeast_rightBoundary
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .right)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write :: clockBoundaryAfter clockZeros ::
          clockTailAfter clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hshift : ShiftRuntimeSafe
      (clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne, ulogCore stateSep]))
    (hreturn : ReturnMovedSafe
      ((clockTailAfter clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          [ulogCore stateOne]).reverse ++ [clockBoundaryAfter clockZeros]))
    (hrestoreClock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape) ++
                  [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
            [unheadTape (writeHeadNat r.action.write)])) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore [] clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++
                  MStarConcreteAlphabet.work :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (unheadTape (writeHeadNat r.action.write) :: leftTape)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight := clockCellsAfter [] clockZeros runtime ++
    List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++
          MStarConcreteAlphabet.work :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros [] (by simp [PayloadPathSafe]) choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++
          MStarConcreteAlphabet.work :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore [] clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++
                  MStarConcreteAlphabet.work :: suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead
    (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime)
    certs (by simp)
  have hcursorBoundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ :=
    stopFree_mismatchPrefix_matchedAtLeast_rightBoundary_cycle
      slot current actual programToHead (clockBoundaryAfter clockZeros)
      (clockTailAfter clockZeros runtime) outer suffix skip r rs
      (canonicalRuleCursor skip (r :: rs)) trace hmatch growth htarget
      hread hwrite htargetLower hmove hcursorBoundary
      (by simpa [programToHead] using hcorridor)
      (by simpa [programToHead] using hreadPath)
      (by simpa [programToHead] using hwritePath)
      (by simpa [programToHead] using htargetPath)
      (by simpa [programToHead] using hscan)
      (clockBoundaryAfter_valid clockZeros) hshift hreturn hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (clockBoundaryAfter clockZeros :: clockTailAfter clockZeros runtime) outer
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++
        MStarConcreteAlphabet.work :: suffix)] at hfull'
  let newLeft := unheadTape (writeHeadNat r.action.write) :: leftTape
  let newProgramToHead := cursorDynamicProgramToHead input newLeft
  have hnewLeftSafe : PayloadPathSafe newLeft := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact unheadTape_payloadCell _ (by
        interval_cases r.action.write <;> decide)
    · exact hleft x hx
  have hmovePath : cursorMatchedMovePath rs programToHead ++
        [unheadTape (writeHeadNat r.action.write)] =
      cursorMatchedMovePath rs newProgramToHead := by
    simp [programToHead, newProgramToHead, newLeft,
      cursorMatchedMovePath, cursorDynamicProgramToHead,
      List.reverse_cons, List.append_assoc]
  have hprogramPath : cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)] =
      cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs newProgramToHead := by
    calc
      cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)] =
          cursorCleanupProgramPrefix skip r ++
            (cursorMatchedMovePath rs programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) :=
        List.append_assoc _ _ _
      _ = cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs newProgramToHead := by rw [hmovePath]
  rw [hprogramPath] at hfull'
  have hprogramRestored : newProgramToHead.map restoreProgramCell =
      newProgramToHead :=
    cursorDynamicProgramToHead_restored input newLeft hnewLeftSafe
  have hclean := cleanedCursorCycleLeft_eq skip r rs newProgramToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath newLeft (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    simpa [choiceRight, programToHead, newLeft, hdecomp,
      List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Automatic exact realization of a right-boundary, shrinking-target
branch.  The state drop supplies the workspace cell consumed by the boundary
extension, hence the semantic capacity decreases by one. -/
noncomputable def exactCycle_semanticLookupSome_rightBoundaryAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hright : c.right = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + (extra + 1))
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input (clockCellsBefore [] clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input (clockCellsAfter [] clockZeros runtime)
        (capacity - 1) outer suffix
          (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclockPath := clockCellsAfter_passive ([] : List ℕ) clockZeros
    runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter [] clockZeros runtime)
      hp hclockPath c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + (extra + 1) :=
    hmatch.1.trans hstate
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have htailSafe := clockTailAfter_passive clockZeros runtime hruntime
  let hcycle := exactCycle_certifiedFirstMatchAtMost_rightBoundary
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hdecomp] using certs) hmatch extra htarget
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hmatch.2.1, hdecomp] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter [] clockZeros runtime) hp hclockPath
      simpa [hdecomp] using ht)
    (passivePath_move (cursorMatchedMovePath_passive rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedRightBoundary_shift_safe (clockTailAfter clockZeros runtime)
      htailSafe r.action.target)
    (matchedRightBoundary_return_safe (clockBoundaryAfter clockZeros)
      (clockBoundaryAfter_valid clockZeros)
      (clockTailAfter clockZeros runtime) htailSafe r.action.target)
    (by
      have hc := matchedCleanupClock_rightInternal_safe skip r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank] using hc)
    (matchedCleanupProgram_appendUnhead_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + (capacity - c.state) =
      (capacity - 1) - r.action.target := by omega
  have hwork : List.replicate extra MStarConcreteAlphabet.work ++
      (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix) =
    List.replicate ((capacity - 1) - r.action.target)
      MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  rw [unhead_writeHeadNat] at hcycle
  have hrightOut := congrArg
    (fun ws => clockCellsAfter [] clockZeros runtime ++
      List.replicate r.action.target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
        (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix) =
      clockCellsAfter [] clockZeros runtime ++
        stateWorkspace (capacity - 1) r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [hrightOut'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hright, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
      hsourceState, List.append_assoc] using hcycle⟩

/-- Automatic exact realization of a right-boundary, state-growth branch.
The boundary extension consumes one reserved workspace cell, so the literal
post-cycle encoding has capacity `capacity - 1`. -/
noncomputable def exactCycle_semanticLookupSome_rightBoundaryAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hright : c.right = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target < capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input (clockCellsBefore [] clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input (clockCellsAfter [] clockZeros runtime)
        (capacity - 1) outer suffix
          (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclockPath := clockCellsAfter_passive ([] : List ℕ) clockZeros
    runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter [] clockZeros runtime)
      hp hclockPath c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  have hdecomp := clockCellsAfter_nil_decompose clockZeros runtime
  have htailSafe := clockTailAfter_passive clockZeros runtime hruntime
  let hcycle := exactCycle_certifiedFirstMatchAtLeast_rightBoundary
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) clockZeros runtime outer
    (List.replicate ((capacity - 1) - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hdecomp] using certs) hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hmatch.2.1, hdecomp] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter [] clockZeros runtime) hp hclockPath
      simpa [hdecomp] using ht)
    (passivePath_move (cursorMatchedMovePath_passive rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedRightBoundary_shift_safe (clockTailAfter clockZeros runtime)
      htailSafe r.action.target)
    (matchedRightBoundary_return_safe (clockBoundaryAfter clockZeros)
      (clockBoundaryAfter_valid clockZeros)
      (clockTailAfter clockZeros runtime) htailSafe r.action.target)
    (by
      have hc := matchedCleanupClock_rightInternal_safe skip r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp 2
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank] using hc)
    (matchedCleanupProgram_appendUnhead_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + 1 + ((capacity - 1) - r.action.target) := by omega
  have hwork : List.replicate growth MStarConcreteAlphabet.work ++
        MStarConcreteAlphabet.work ::
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
      List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix := by
    rw [show MStarConcreteAlphabet.work ::
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate 1 MStarConcreteAlphabet.work ++
          (List.replicate ((capacity - 1) - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) by simp]
    rw [← List.append_assoc, ← List.replicate_add]
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws => clockCellsBefore [] clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightStart :
      clockCellsBefore [] clockZeros runtime ++
            List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            (List.replicate growth MStarConcreteAlphabet.work ++
              MStarConcreteAlphabet.work ::
                (List.replicate ((capacity - 1) - r.action.target)
                  MStarConcreteAlphabet.work ++ suffix)) =
        clockCellsBefore [] clockZeros runtime ++
          stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  have hrightFinish :
      clockCellsAfter [] clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            (List.replicate ((capacity - 1) - r.action.target)
              MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter [] clockZeros runtime ++
          stateWorkspace (capacity - 1) r.action.target suffix := by
    simp only [stateWorkspace, List.cons_append, List.append_assoc]
  rw [unhead_writeHeadNat] at hcycle
  have hcycleNorm : ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
              input ++ ulogCore pcMark :: outer,
          readHeadNat c.focus,
          clockCellsBefore [] clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              (List.replicate growth MStarConcreteAlphabet.work ++
                MStarConcreteAlphabet.work ::
                  (List.replicate ((capacity - 1) - r.action.target)
                    MStarConcreteAlphabet.work ++ suffix))⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath
              (payloadNat r.action.write :: c.leftRev.map payloadNat)
              (skip ++ r :: rs) input ++ ulogCore pcMark :: outer,
          ulogCore payloadHeadBlank,
          clockCellsAfter [] clockZeros runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              (List.replicate ((capacity - 1) - r.action.target)
                MStarConcreteAlphabet.work ++ suffix)⟩) := by
    simpa only [List.cons_append, List.append_assoc] using hcycle
  have hcycle' := hcycleNorm
  rw [hrightStart, hrightFinish] at hcycle'
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hright, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
      hsourceState, List.append_assoc] using hcycle'⟩

/-- Automatic exact realization of a left-boundary, state-growth branch.
The physical extension consumes the leading outer `work` cell, while the
semantic state workspace keeps the same capacity. -/
noncomputable def exactCycle_semanticLookupSome_leftBoundaryAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hleft : c.leftRev = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity (MStarConcreteAlphabet.work :: outer) suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpEmpty : PassivePath (cursorDynamicProgramToHead input []) := by
    simpa [hleft] using hp
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  have hsplit := cursorDynamicProgramToHead_emptyLeft_split input
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hsplit, cursorMatchedMovePath, List.append_assoc]
  have hcleanupClock := matchedCleanupClock_leftInternal_safe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty 2
  have hcleanupProgram := cursorCleanupProgramPath_restoreHeadSafe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty
  rw [hmoveSplit] at hcleanupClock hcleanupProgram
  have hcycle := exactCycle_certifiedFirstMatchAtLeast_leftBoundary
    slot c.state c.focus input (c.right.map payloadNat)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by simpa [hleft] using (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (by simpa [hleft] using (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hleft] using ht)
    (by simpa [hleft] using (passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)))
    (matchedLeftBoundary_shift_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input))
    (matchedLeftBoundary_return_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input)
      (leftBoundaryMarker input) (leftBoundaryMarker_passive input))
    (by
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank, List.append_assoc] using hcleanupClock)
    (by simpa [List.append_assoc] using hcleanupProgram)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hwork : List.replicate growth MStarConcreteAlphabet.work ++
        (List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix) =
      List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
        suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws => clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightIn' :
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  rw [unhead_writeHeadNat, hrightIn'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hleft, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
      hsourceState, List.append_assoc] using hcycle⟩

/-- Automatic exact realization of a left-boundary, strictly shrinking
branch.  The leading outer `work` cell is consumed by the boundary shift;
released state cells remain in the unchanged-capacity workspace. -/
noncomputable def exactCycle_semanticLookupSome_leftBoundaryAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (hleft : c.leftRev = []) (input : List Bool)
    (clockZeros capacity : ℕ) (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime) (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + (extra + 1))
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity (MStarConcreteAlphabet.work :: outer) suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpEmpty : PassivePath (cursorDynamicProgramToHead input []) := by
    simpa [hleft] using hp
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + (extra + 1) :=
    hmatch.1.trans hstate
  have hsplit := cursorDynamicProgramToHead_emptyLeft_split input
  have hmoveSplit : cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input []) =
      cursorMatchedMovePath rs (leftBoundaryScanPrefix input) ++
        [leftBoundaryMarker input] := by
    simp [hsplit, cursorMatchedMovePath, List.append_assoc]
  have hcleanupClock := matchedCleanupClock_leftInternal_safe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty 2
  have hcleanupProgram := cursorCleanupProgramPath_restoreHeadSafe skip r rs
    (cursorDynamicProgramToHead input []) hpEmpty
  rw [hmoveSplit] at hcleanupClock hcleanupProgram
  have hcycle := exactCycle_certifiedFirstMatchAtMost_leftBoundary
    slot c.state c.focus input (c.right.map payloadNat)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (List.replicate (capacity - c.state)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch extra htarget
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by simpa [hleft] using (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (by simpa [hleft] using (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hleft] using ht)
    (by simpa [hleft] using (passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)))
    (matchedLeftBoundary_shift_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input))
    (matchedLeftBoundary_return_safe_general skip r rs
      (leftBoundaryScanPrefix input) (leftBoundaryScanPrefix_passive input)
      (leftBoundaryMarker input) (leftBoundaryMarker_passive input))
    (by
      have hblank : headTapeOfCell (payloadNat 2) =
          ulogCore payloadHeadBlank := by decide
      simpa [hblank, List.append_assoc] using hcleanupClock)
    (by simpa [List.append_assoc] using hcleanupProgram)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + 1 + (capacity - c.state) =
      capacity - r.action.target := by omega
  have hwork :
      List.replicate (extra + 1) MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightOut := congrArg
    (fun ws =>
      clockCellsAfter
          (payloadNat r.action.write :: c.right.map payloadNat)
          clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter
              (payloadNat r.action.write :: c.right.map payloadNat)
              clockZeros runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (extra + 1) MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter
            (payloadNat r.action.write :: c.right.map payloadNat)
            clockZeros runtime ++
          stateWorkspace capacity r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [unhead_writeHeadNat, hrightOut'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hleft, hmove,
      ULogSemantics.applyAction, ULogSemantics.blankCode, readHeadNat,
      hsourceState, List.append_assoc] using hcycle⟩

/-- Exact successful stay cycle after a certified mismatch prefix in the
target-at-most case. -/
noncomputable def stopFree_mismatchPrefix_matchedAtMost_stay_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtMost
    slot current actual programToHead runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch extra
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveStay_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram hhead
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cleanedCycleLeft] using hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- Exact successful stay cycle after a certified mismatch prefix in the
state-growth case. -/
noncomputable def stopFree_mismatchPrefix_matchedAtLeast_stay_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead)) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  obtain ⟨a, haction⟩ := stopFree_mismatchPrefix_matchedAtLeast
    slot current actual programToHead runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch growth
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath
    hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> decide
  obtain ⟨b, hcleanup⟩ := stopFree_moveStay_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
    hscan hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram hhead
  have hcleanup' : StopFreeValidZeroRun b
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    simpa [cleanedCycleLeft] using hcleanup
  exact ⟨a + b, haction.append hcleanup'⟩

/-- First-hit strengthening of the certified successful stay cycle when the
requested state does not grow.  The choice prefix, rule cursor, target
rewrite, move, and cleanup are all explicit exact pieces. -/
noncomputable def exactCycle_certifiedFirstMatchAtMost_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape clockTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hclockTape : PayloadPathSafe clockTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter clockTape clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockCellsAfter clockTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write ::
          clockCellsAfter clockTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          clockCellsAfter clockTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter clockTape clockZeros runtime ++
      List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros clockTape hclockTape choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (clockCellsAfter clockTape clockZeros runtime) certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ := stopFree_mismatchPrefix_matchedAtMost_stay_cycle
    slot current actual programToHead
    (clockCellsAfter clockTape clockZeros runtime) outer suffix
    skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch extra htarget
    hread hwrite htargetLower hmove hboundary
    (by simpa [programToHead] using hcorridor)
    (by simpa [programToHead] using hreadPath)
    (by simpa [programToHead] using hwritePath)
    (by simpa [programToHead] using htargetPath)
    (by simpa [programToHead] using hscan) hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (clockCellsAfter clockTape clockZeros runtime) outer
    (ulogCore stateSep :: suffix)] at hfull'
  have hprogramRestored : programToHead.map restoreProgramCell = programToHead :=
    cursorDynamicProgramToHead_restored input leftTape hleft
  have hclean := cleanedCursorCycleLeft_eq skip r rs programToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          clockCellsAfter clockTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    simpa [choiceRight, programToHead, List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- First-hit strengthening of the certified successful stay cycle in the
state-growth case. -/
noncomputable def exactCycle_certifiedFirstMatchAtLeast_stay
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape clockTape : List Tape)
    (hleft : PayloadPathSafe leftTape)
    (hclockTape : PayloadPathSafe clockTape)
    (clockZeros : ℕ) (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual
      (cursorDynamicProgramToHead input leftTape)
      (clockCellsAfter clockTape clockZeros runtime)
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs
        (cursorDynamicProgramToHead input leftTape)
        (readHeadNat r.read)
        (clockCellsAfter clockTape clockZeros runtime)))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape))))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs
            (cursorDynamicProgramToHead input leftTape)))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape) ++
        writeHeadNat r.action.write ::
          clockCellsAfter clockTape clockZeros runtime))
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs
        (cursorDynamicProgramToHead input leftTape)))
    (hrestoreClock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs
                (cursorDynamicProgramToHead input leftTape))).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs
          (cursorDynamicProgramToHead input leftTape))) :
    ExactConcreteCycle slot
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          clockCellsAfter clockTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
  let programToHead := cursorDynamicProgramToHead input leftTape
  let choiceLeft := dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
    ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter clockTape clockZeros runtime ++
      List.replicate current (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ suffix
  have hhead : choiceHead (readHeadNat actual) = true := by
    rw [← hmatch.2.1]
    interval_cases r.read <;> native_decide
  have hchoice := clockDecrementCells_firstChoice (readHeadNat actual) hhead
    clockZeros clockTape hclockTape choiceLeft
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          clockCellsBefore clockTape clockZeros runtime ++
            List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate growth MStarConcreteAlphabet.work ++ suffix⟩)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) := by
    simpa [choiceLeft, choiceRight, clockCellsBefore, clockCellsAfter,
      List.append_assoc] using hchoice
  obtain ⟨a, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ r :: rs) (by simp) input outer (readHeadNat actual)
    choiceRight
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ r :: rs) input)
          outer (ulogCore pcMark) (readHeadNat actual :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ r :: rs) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ r :: rs) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x choiceRight
  have hdynamic' : StopFreeValidZeroRun a
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot ⟨choiceLeft, readHeadNat actual, choiceRight⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight) := by
    rw [hselectedStart]
    exact hdynamic
  have trace := mismatchCertificateList_initial_trace slot current actual
    programToHead (clockCellsAfter clockTape clockZeros runtime) certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  obtain ⟨b, hfull⟩ := stopFree_mismatchPrefix_matchedAtLeast_stay_cycle
    slot current actual programToHead
    (clockCellsAfter clockTape clockZeros runtime) outer suffix
    skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch growth htarget
    hread hwrite htargetLower hmove hboundary
    (by simpa [programToHead] using hcorridor)
    (by simpa [programToHead] using hreadPath)
    (by simpa [programToHead] using hwritePath)
    (by simpa [programToHead] using htargetPath)
    (by simpa [programToHead] using hscan) hrestoreClock hprogram
  have hfull' := hfull
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual
    leftTape input skip r rs
    (clockCellsAfter clockTape clockZeros runtime) outer
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ suffix)] at hfull'
  have hprogramRestored : programToHead.map restoreProgramCell = programToHead :=
    cursorDynamicProgramToHead_restored input leftTape hleft
  have hclean := cleanedCursorCycleLeft_eq skip r rs programToHead outer
    hprogramRestored
  rw [hclean, canonicalCursorCycleLeft_dynamic] at hfull'
  have hfull'' : StopFreeValidZeroRun b
      (dynamicRuleSourceStarted slot leftTape (skip ++ r :: rs) input outer
        (readHeadNat actual) choiceRight)
      (.running .cycleStart
        ⟨dynamicRuleReturnPath leftTape (skip ++ r :: rs) input ++
            ulogCore pcMark :: outer,
          writeHeadNat r.action.write,
          clockCellsAfter clockTape clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: suffix⟩) := by
    simpa [choiceRight, programToHead, List.append_assoc] using hfull'
  exact exactConcreteCycleOfChoiceHeadStopFree choiceLeft (readHeadNat actual)
    choiceRight hhead hchoice' (hdynamic'.append hfull'')
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary])

/-- Automatic exact realization of the nonhalting stay branch when the target
state block does not grow.  This is the first semantic-level discharge of
`ExactPositiveCycleCore`; unlike the legacy theorem it returns the actual
first-hit cycle. -/
noncomputable def exactCycle_semanticLookupSome_stayAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .stay) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra :=
    hmatch.1.trans hstate
  have hcycle := exactCycle_certifiedFirstMatchAtMost_stay
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (c.right.map payloadNat) (payloadNatList_safe c.leftRev)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs certs hmatch extra htarget rscan.read_valid hwrite htargetLower
    hmove
    (by simpa [hmatch.2.1] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
    (passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp hwrite)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hworkspace := stateWorkspace_atMost capacity r.source
    r.action.target extra htarget (by omega) suffix
  have hout :
      List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix =
        stateWorkspace capacity r.action.target suffix := by
    rw [hsourceState] at hworkspace
    simpa [List.append_assoc] using hworkspace
  have hright := congrArg
    (fun xs => clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      xs) hout
  have hright' :
      clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate extra MStarConcreteAlphabet.work ++
              (List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity r.action.target suffix := by
    simpa only [List.append_assoc] using hright
  rw [hright'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hsourceState, List.append_assoc] using hcycle⟩

/-- Automatic exact realization of the nonhalting stay branch when the target
state block grows. -/
noncomputable def exactCycle_semanticLookupSome_stayAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .stay) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  have hcycle := exactCycle_certifiedFirstMatchAtLeast_stay
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (c.right.map payloadNat) (payloadNatList_safe c.leftRev)
    (payloadNatList_safe c.right) clockZeros runtime outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs certs hmatch growth htarget' rscan.read_valid hwrite
    htargetLower hmove
    (by simpa [hmatch.2.1] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
    (passivePath_move
      (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp hwrite)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hright' :
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
        stateWorkspace capacity c.state suffix =
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++
            (List.replicate (capacity - r.action.target)
              MStarConcreteAlphabet.work ++ suffix) := by
    simp only [stateWorkspace]
    rw [hsum, List.replicate_add]
    simp only [List.cons_append, List.append_assoc]
  rw [← hright'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hsourceState, List.append_assoc] using hcycle⟩

/-- Automatic exact realization of an internal-left, state-growth branch.
The physical left endpoint becomes the successor focus and the written old
focus is retained at the front of the successor right tape. -/
noncomputable def exactCycle_semanticLookupSome_leftInternalAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (leftTail : List ℕ) (hleft : c.leftRev = next :: leftTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpTail := cursorDynamicProgramToHead_passive input leftTail
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  have hcycle := exactCycle_certifiedFirstMatchAtLeast_leftInternal
    slot c.state c.focus input (payloadNat next) (leftTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: leftTail) x hx)
    (c.right.map payloadNat) (payloadNatList_safe c.right)
    clockZeros runtime outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by
      simpa [hleft] using matchedReadPath_safe r.slot r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      simpa [hleft] using matchedWritePath_safe r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hleft] using ht)
    (by
      simpa [hleft] using passivePath_move (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_leftInternal_safe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail next)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hwork :
      List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - c.state)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws =>
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightIn' :
      clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsBefore (c.right.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  rw [unhead_writeHeadNat, hrightIn'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hleft, hsourceState,
      List.append_assoc] using hcycle⟩

/-- Automatic exact realization of an internal-left, shrinking/equal target
branch.  The released state cells remain in the fixed-capacity workspace as
the physical left endpoint becomes the successor focus. -/
noncomputable def exactCycle_semanticLookupSome_leftInternalAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (leftTail : List ℕ) (hleft : c.leftRev = next :: leftTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .left) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hpTail := cursorDynamicProgramToHead_passive input leftTail
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra :=
    hmatch.1.trans hstate
  have hcycle := exactCycle_certifiedFirstMatchAtMost_leftInternal
    slot c.state c.focus input (payloadNat next) (leftTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: leftTail) x hx)
    (c.right.map payloadNat) (payloadNatList_safe c.right)
    clockZeros runtime outer
    (List.replicate (capacity - c.state)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs (by simpa [hleft] using certs) hmatch extra htarget
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hleft, hmatch.2.1] using rscan.source_corridor)
    (by
      simpa [hleft] using matchedReadPath_safe r.slot r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      simpa [hleft] using matchedWritePath_safe r rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hleft] using ht)
    (by
      simpa [hleft] using passivePath_move (cursorMatchedMovePath_passive rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_leftInternal_safe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail next)
    (cursorCleanupProgramPath_restoreHeadSafe skip r rs
      (cursorDynamicProgramToHead input (leftTail.map payloadNat)) hpTail)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + (capacity - c.state) =
      capacity - r.action.target := by omega
  have hwork :
      List.replicate extra MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightOut := congrArg
    (fun ws =>
      clockCellsAfter
          (payloadNat r.action.write :: c.right.map payloadNat)
          clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter
              (payloadNat r.action.write :: c.right.map payloadNat)
              clockZeros runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter
            (payloadNat r.action.write :: c.right.map payloadNat)
            clockZeros runtime ++
          stateWorkspace capacity r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [unhead_writeHeadNat, hrightOut'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hleft, hsourceState,
      List.append_assoc] using hcycle⟩

/-- Automatic exact realization of an internal-right, shrinking/equal target
branch.  The released state cells remain in the fixed-capacity workspace. -/
noncomputable def exactCycle_semanticLookupSome_rightInternalAtMost
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (rightTail : List ℕ) (hright : c.right = next :: rightTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (extra : ℕ) (hstate : c.state = action.target + extra)
    (hcapacity : c.state ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget : r.source = r.action.target + extra :=
    hmatch.1.trans hstate
  have hclockEq : clockCellsAfter (c.right.map payloadNat) clockZeros runtime =
      payloadNat next ::
        clockCellsAfter (rightTail.map payloadNat) clockZeros runtime := by
    simp [hright, clockCellsAfter, List.append_assoc]
  have hcycle := exactCycle_certifiedFirstMatchAtMost_rightInternal
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) (payloadNat next)
    (rightTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: rightTail) x hx)
    clockZeros runtime outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs
    (by simpa [hright, clockCellsAfter, List.append_assoc] using certs)
    hmatch extra htarget rscan.read_valid hwrite htargetLower hmove
    (by simpa [hmatch.2.1, hclockEq] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hclockEq] using ht)
    (passivePath_move (cursorMatchedMovePath_passive rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_rightInternal_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp next)
    (matchedCleanupProgram_appendUnhead_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : extra + (capacity - c.state) =
      capacity - r.action.target := by omega
  have hwork :
      List.replicate extra MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightOut := congrArg
    (fun ws =>
      clockCellsAfter (rightTail.map payloadNat) clockZeros runtime ++
        List.replicate r.action.target (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightOut' :
      clockCellsAfter (rightTail.map payloadNat) clockZeros runtime ++
              List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix) =
        clockCellsAfter (rightTail.map payloadNat) clockZeros runtime ++
          stateWorkspace capacity r.action.target suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightOut
  rw [unhead_writeHeadNat, hrightOut'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hright, hsourceState,
      List.append_assoc] using hcycle⟩

/-- Automatic exact realization of an internal-right, state-growth branch.
The result ends at the literal post-cycle clock layout; a supplied
`ClockReframe` below identifies that layout with the next semantic frame. -/
noncomputable def exactCycle_semanticLookupSome_rightInternalAtLeast
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (next : ℕ) (rightTail : List ℕ) (hright : c.right = next :: rightTail)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (growth : ℕ) (htarget : action.target = c.state + growth)
    (hcapacity : action.target ≤ capacity) (htargetLower : 2 ≤ action.target)
    (hmove : action.move = .right) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        capacity outer suffix (ULogSemantics.applyAction c action))) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have htarget' : r.action.target = r.source + growth := by
    rw [hmatch.1]
    exact htarget
  have hclockEq : clockCellsAfter (c.right.map payloadNat) clockZeros runtime =
      payloadNat next ::
        clockCellsAfter (rightTail.map payloadNat) clockZeros runtime := by
    simp [hright, clockCellsAfter, List.append_assoc]
  have hcycle := exactCycle_certifiedFirstMatchAtLeast_rightInternal
    slot c.state c.focus input (c.leftRev.map payloadNat)
    (payloadNatList_safe c.leftRev) (payloadNat next)
    (rightTail.map payloadNat)
    (by intro x hx; exact payloadNatList_safe (next :: rightTail) x hx)
    clockZeros runtime outer
    (List.replicate (capacity - r.action.target)
      MStarConcreteAlphabet.work ++ suffix)
    skip r rs
    (by simpa [hright, clockCellsAfter, List.append_assoc] using certs)
    hmatch growth htarget'
    rscan.read_valid hwrite htargetLower hmove
    (by simpa [hmatch.2.1, hclockEq] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (by
      have ht := matchedTargetPath_safe r hwrite rs
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock
      simpa [hclockEq] using ht)
    (passivePath_move (cursorMatchedMovePath_passive rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp))
    (matchedCleanupClock_rightInternal_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp next)
    (matchedCleanupProgram_appendUnhead_safe skip r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
  have hsourceState : r.source = c.state := hmatch.1
  have hsum : capacity - c.state =
      growth + (capacity - r.action.target) := by omega
  have hwork :
      List.replicate growth MStarConcreteAlphabet.work ++
          (List.replicate (capacity - r.action.target)
            MStarConcreteAlphabet.work ++ suffix) =
        List.replicate (capacity - c.state)
          MStarConcreteAlphabet.work ++ suffix := by
    rw [← List.append_assoc, ← List.replicate_add, hsum]
  have hrightIn := congrArg
    (fun ws =>
      clockCellsBefore (payloadNat next :: rightTail.map payloadNat)
          clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: ws) hwork
  have hrightIn' :
      clockCellsBefore (payloadNat next :: rightTail.map payloadNat)
              clockZeros runtime ++
            List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++
        (List.replicate (capacity - r.action.target)
          MStarConcreteAlphabet.work ++ suffix) =
      clockCellsBefore (payloadNat next :: rightTail.map payloadNat)
          clockZeros runtime ++ stateWorkspace capacity c.state suffix := by
    simpa only [stateWorkspace, List.cons_append, List.append_assoc] using
      hrightIn
  rw [unhead_writeHeadNat, hrightIn'] at hcycle
  exact ⟨by
    simpa [semanticCycleEncoding, stateWorkspace, heq, hmove,
      ULogSemantics.applyAction, hright, hsourceState,
      List.append_assoc] using hcycle⟩

/-! ## Resource- and clock-indexed exact continuation

The old `ExactResourceContinuationRefinement` quantified over arbitrary
`FrameReady` frames.  That is too broad: a passive runtime need not contain a
next `clockOne`, so it does not in general support a `ClockReframe`.  Exact
continuations are therefore consumed only together with a decoded positive
clock budget and a step-indexed frame reserve.
-/

/-- One nonterminal exact cycle together with the positive-clock reframing
needed for the following frame.  The certificate is indexed by the remaining
decoded budget, rather than asserting a reframe for an arbitrary passive
runtime. -/
structure ExactPositiveResourceContinuation
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (remaining : ℕ) : Type where
  action : ULogBytecode.ActionCode
  reframe : ClockReframe
    ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
    (clockCellsAfter
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime)
  lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
    frame.config.focus slot = some action
  action_eq : ULogSemantics.applyAction frame.config action = next
  clock_decoded : decodeBinaryClock
    (List.replicate reframe.zeros (ulogCore clockZero) ++
      ulogCore clockOne :: reframe.runtime) = some remaining
  exact_cycle : ExactConcreteCycle slot frame.encode
    (frame.reframeNext action reframe).encode

/-- A source-level exact continuation constructor.  Its domain makes all
resource and clock assumptions explicit: it is intentionally not an
unconditional oracle over `FrameReady`. -/
def ExactPositiveResourceSchedule
    {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (next : ULogSemantics.Config) (steps budget : ℕ),
    FrameResourceInvariant frame (steps + 1) →
    PassivePath frame.runtime →
    decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget →
    1 < budget →
    ULogSemantics.stepSlot slot frame.config = some next →
    ULogSemantics.accepting next = false →
    ULogSemantics.halted next = false →
      ExactPositiveResourceContinuation frame slot next (budget - 1)

/-- The remaining machine-specific obligation, separated from clock and
resource bookkeeping.  Its result is an exact first-hit cycle for a chosen
valid positive-clock reframe; the theorem below turns it into the schedule
consumed by the trace recursion. -/
def ExactPositiveCycleCore
    {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (next : ULogSemantics.Config) (steps : ℕ)
      (resources : FrameResourceInvariant frame (steps + 1))
      (hruntime : PassivePath frame.runtime)
      (action : ULogBytecode.ActionCode)
      (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
        frame.config.focus slot = some action)
      (haction : ULogSemantics.applyAction frame.config action = next)
      (hhalt : ULogSemantics.halted next = false)
      (reframe : ClockReframe
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        (clockCellsAfter
          ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
          frame.clockZeros frame.runtime)),
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode

/-- The non-growing stay branch of the positive exact-cycle core.  Since the
head does not move, the semantic capacity and outer reserve are unchanged;
the supplied clock reframe is the only physical layout identification needed
at the next boundary. -/
noncomputable def exactPositiveCycleCore_stayAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .stay)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_stayAtMost
      frame.config slot action hlookup input frame.clockZeros frame.capacity
      frame.runtime frame.outer suffix hruntime resources.tape_bounded.focus
      resources.reads_lt_three resources.writes_lt_three extra hstate
      resources.state_le_capacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
    using hcycle

/-- The state-growth stay branch of the positive exact-cycle core. -/
noncomputable def exactPositiveCycleCore_stayAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .stay)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    (resources.frameReady hruntime).capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_stayAtLeast
      frame.config slot action hlookup input frame.clockZeros frame.capacity
      frame.runtime frame.outer suffix hruntime resources.tape_bounded.focus
      resources.reads_lt_three resources.writes_lt_three growth htarget
      hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
    using hcycle

/-- The state-growth/internal-left branch of the positive exact-cycle core.
The nonempty left tape supplies the physical endpoint moved under the head;
the provided positive-clock reframe identifies the literal post-cycle clock
with the next resource frame. -/
noncomputable def exactPositiveCycleCore_leftInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (leftTail : List ℕ)
    (hleft : frame.config.leftRev = next :: leftTail)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    (resources.frameReady hruntime).capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hleft] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftInternalAtLeast
      frame.config slot action hlookup next leftTail hleft input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, hreframe]
    using hcycle

/-- The shrinking/equal-target internal-left branch of the positive exact
cycle core.  Moving the physical left endpoint under the head preserves the
capacity, and released state cells remain available as workspace. -/
noncomputable def exactPositiveCycleCore_leftInternalAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (leftTail : List ℕ)
    (hleft : frame.config.leftRev = next :: leftTail)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftInternalAtMost
      frame.config slot action hlookup next leftTail hleft input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three extra hstate resources.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, hreframe]
    using hcycle

/-- The shrinking/equal-target internal-right branch of the positive exact
cycle core.  The nonempty right tape supplies the cell moved under the head,
while the released state cells stay inside the unchanged capacity. -/
noncomputable def exactPositiveCycleCore_rightInternalAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (rightTail : List ℕ)
    (hright : frame.config.right = next :: rightTail)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightInternalAtMost
      frame.config slot action hlookup next rightTail hright input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three extra hstate resources.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hright, hreframe]
    using hcycle

/-- The state-growth/internal-right branch of the positive exact-cycle core.
It consumes the current passive runtime explicitly and uses nonhalting of the
semantic successor to exclude the concrete target-zero/target-one terminal
dispatches. -/
noncomputable def exactPositiveCycleCore_rightInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (rightTail : List ℕ)
    (hright : frame.config.right = next :: rightTail)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    (resources.frameReady hruntime).capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightInternalAtLeast
      frame.config slot action hlookup next rightTail hright input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hright, hreframe]
    using hcycle

/-- The strictly shrinking/right-boundary branch of the positive exact-cycle
core.  One released state cell is consumed by the boundary extension, so the
semantic capacity drops by one. -/
noncomputable def exactPositiveCycleCore_rightBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hright : frame.config.right = [])
    (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    (resources.frameReady hruntime).capacity_ready slot action hlookup
  have hcapacity : action.target < frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightBoundaryAtMost
      frame.config slot action hlookup hright input frame.clockZeros
      frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three extra hstate resources.state_le_capacity
      htargetLower hmove)
  have hreframeNil :
      clockCellsBefore [] reframe.zeros reframe.runtime =
        clockCellsAfter [] frame.clockZeros frame.runtime := by
    simpa [ULogSemantics.applyAction, hmove, hright] using reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, ULogSemantics.applyAction,
    hmove, hright, hreframeNil]
    using hcycle

/-- The state-growth/right-boundary branch of the positive exact-cycle core.
The resource invariant supplies the strict target bound needed after the
boundary shift consumes one capacity cell, and the supplied clock reframe
identifies the literal post-cycle clock with the next semantic frame. -/
noncomputable def exactPositiveCycleCore_rightBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hright : frame.config.right = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    (resources.frameReady hruntime).capacity_ready slot action hlookup
  have hcapacity : action.target < frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightBoundaryAtLeast
      frame.config slot action hlookup hright input frame.clockZeros
      frame.capacity frame.runtime frame.outer suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframeNil :
      clockCellsBefore [] reframe.zeros reframe.runtime =
        clockCellsAfter [] frame.clockZeros frame.runtime := by
    simpa [ULogSemantics.applyAction, hmove, hright] using reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, ULogSemantics.applyAction,
    hmove, hright, hreframeNil]
    using hcycle

/-- The strictly shrinking/left-boundary branch of the positive exact-cycle
core.  `SemanticOuterReady` supplies the physical leading `work` cell consumed
by the boundary extension, while released state cells keep the semantic
capacity unchanged. -/
noncomputable def exactPositiveCycleCore_leftBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hleft : frame.config.leftRev = [])
    (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have ready := resources.frameReady hruntime
  have houterReady := ready.outer_ready slot action hlookup
  have hex : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let outerTail := Classical.choose hex
  have houter : frame.outer = MStarConcreteAlphabet.work :: outerTail :=
    Classical.choose_spec hex
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftBoundaryAtMost
      frame.config slot action hlookup hleft input frame.clockZeros
      frame.capacity frame.runtime outerTail suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three extra hstate resources.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter, hreframe]
    using hcycle

/-- The state-growth/left-boundary branch of the positive exact-cycle core.
`SemanticOuterReady` supplies the physical leading `work` cell consumed by
the boundary extension; unlike a right-boundary extension, the semantic
capacity is unchanged. -/
noncomputable def exactPositiveCycleCore_leftBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hleft : frame.config.leftRev = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have ready := resources.frameReady hruntime
  have hcapacityReady := ready.capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove] using hcapacityReady
  have houterReady := ready.outer_ready slot action hlookup
  have hex : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let outerTail := Classical.choose hex
  have houter : frame.outer = MStarConcreteAlphabet.work :: outerTail :=
    Classical.choose_spec hex
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftBoundaryAtLeast
      frame.config slot action hlookup hleft input frame.clockZeros
      frame.capacity frame.runtime outerTail suffix hruntime
      resources.tape_bounded.focus resources.reads_lt_three
      resources.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter, hreframe]
    using hcycle

/-- Total concrete dispatch for a positive nonhalting semantic cycle.  A
strictly smaller target uses the corresponding `AtMost` realization, while
an equal or larger target uses `AtLeast`; moving branches are further split
according to whether the tape in the direction of travel is empty. -/
noncomputable def concreteExactPositiveCycleCore
    {input : List Bool} {suffix : List Tape} :
    ExactPositiveCycleCore (input := input) (suffix := suffix) := by
  intro frame slot nextConfig steps resources hruntime action hlookup haction
    hhalt reframe
  cases hmove : action.move with
  | stay =>
      by_cases htarget : action.target < frame.config.state
      · let extra := frame.config.state - action.target - 1
        have hstate :
            frame.config.state = action.target + (extra + 1) := by
          dsimp [extra]
          omega
        exact exactPositiveCycleCore_stayAtMost frame slot nextConfig steps
          resources hruntime action hlookup haction hhalt (extra + 1) hstate
          hmove reframe
      · let growth := action.target - frame.config.state
        have htargetEq :
            action.target = frame.config.state + growth := by
          dsimp [growth]
          omega
        exact exactPositiveCycleCore_stayAtLeast frame slot nextConfig steps
          resources hruntime action hlookup haction hhalt growth htargetEq
          hmove reframe
  | right =>
      cases hright : frame.config.right with
      | nil =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_rightBoundaryAtMost frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              hright extra hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_rightBoundaryAtLeast frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              hright growth htargetEq hmove reframe
      | cons next rightTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_rightInternalAtMost frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              next rightTail hright (extra + 1) hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_rightInternalAtLeast frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              next rightTail hright growth htargetEq hmove reframe
  | left =>
      cases hleft : frame.config.leftRev with
      | nil =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_leftBoundaryAtMost frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              hleft extra hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_leftBoundaryAtLeast frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              hleft growth htargetEq hmove reframe
      | cons next leftTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_leftInternalAtMost frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              next leftTail hleft (extra + 1) hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_leftInternalAtLeast frame slot
              nextConfig steps resources hruntime action hlookup haction hhalt
              next leftTail hleft growth htargetEq hmove reframe

/-- Clock arithmetic and `FrameResourceInvariant` turn an exact
machine-cycle core into the correctly indexed continuation schedule.  In
particular this construction is unavailable at a zero post-clock, which is
why no unconditional `FrameReady` continuation is asserted. -/
noncomputable def exactPositiveResourceSchedule_of_core
    {input : List Bool} {suffix : List Tape}
    (core : ExactPositiveCycleCore (input := input) (suffix := suffix)) :
    ExactPositiveResourceSchedule (input := input) (suffix := suffix) := by
  intro frame slot next steps budget resources hruntime hclock hbudget hstep _ hhalt
  let actionWitness := Classical.indefiniteDescription _
    (ULogSemantics.stepSlot_some_rule hstep).2
  let action := actionWitness.1
  have hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action := actionWitness.2.1
  have haction : ULogSemantics.applyAction frame.config action = next :=
    actionWitness.2.2
  have hafter := decodeBinaryClock_after_eq_pred frame.clockZeros
    frame.runtime budget hclock
  let reframeWitness := Classical.indefiniteDescription _
    (exists_clockReframe_of_positive_binaryClock
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime hruntime
      (budget - 1) hafter (by omega))
  let reframe := reframeWitness.1
  have hnextClock : decodeBinaryClock
      (List.replicate reframe.zeros (ulogCore clockZero) ++
        ulogCore clockOne :: reframe.runtime) = some (budget - 1) :=
    reframeWitness.2
  exact
    { action := action
      reframe := reframe
      lookup := hlookup
      action_eq := haction
      clock_decoded := hnextClock
      exact_cycle := core frame slot next steps resources hruntime action hlookup
        haction hhalt reframe }

/-- Resource- and clock-indexed identification of an arbitrary raw positive
cycle.  The schedule constructs one canonical first-hit cycle for the
semantic successor; `ExactConcreteCycle.finish_unique` then forces every raw
cycle with the same frame and slot to stop at that very same reframed
boundary.  In particular, the conclusion does not assume that the raw finish
already has semantic shape. -/
theorem exactConcreteCycle_identify_positive_outcome
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (steps budget : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hruntime : PassivePath frame.runtime)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = false)
    (hhalt : ULogSemantics.halted next = false)
    {finish : Result} (raw : ExactConcreteCycle slot frame.encode finish) :
    ∃ continuation : ExactPositiveResourceContinuation
        frame slot next (budget - 1),
      finish = (frame.reframeNext continuation.action
        continuation.reframe).encode := by
  let continuation :=
    (exactPositiveResourceSchedule_of_core
      (concreteExactPositiveCycleCore
        (input := input) (suffix := suffix)))
      frame slot next steps budget resources hruntime hclock hbudget hstep
        haccept hhalt
  exact ⟨continuation, raw.finish_unique continuation.exact_cycle⟩

/-- A semantic accepting trace with a decoded clock budget is realized by an
actual first-hit concrete accepting execution.  In the continuing branch the
next reserve is derived by `FrameResourceInvariant.next`; no general
`FrameReady → ClockReframe` assertion is used. -/
theorem acceptingSlotTrace_has_boundedResource_exact_trace
    {input : List Bool} {suffix : List Tape}
    (schedule : ExactPositiveResourceSchedule
      (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ExactConcreteAcceptingSlotTrace frame.encode word := by
  induction t generalizing frame word budget with
  | zero => simp [AcceptingSlotTrace, hstart] at trace
  | succ t ih =>
      have ready := resources.frameReady hruntime
      rcases trace with terminal |
        ⟨slot, next, rest, rfl, _, hstep, tailTrace⟩
      · simp [hstart] at terminal
      · by_cases haccept : ULogSemantics.accepting next = true
        · have hrest : rest = [] :=
            tailTrace.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hcycle⟩ :=
            exactAcceptingCycleRefinement frame slot ready next hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hcycle
              (.nil _),
            rfl⟩
        · have hacceptFalse : ULogSemantics.accepting next = false := by
            cases h : ULogSemantics.accepting next <;> simp_all
          by_cases hhalt : ULogSemantics.halted next = true
          · exact (tailTrace.false_of_halted_not_accepting hhalt
              hacceptFalse).elim
          · have hhaltFalse : ULogSemantics.halted next = false := by
              cases h : ULogSemantics.halted next <;> simp_all
            have hrestPositive : 0 < rest.length :=
              tailTrace.length_pos_of_not_halted hhaltFalse
            have hbudget : 1 < budget := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨action, reframe, hlookup, haction, hnextClock,
                hcycle⟩ :=
              schedule frame slot next t budget resources hruntime hclock hbudget
                hstep hacceptFalse hhaltFalse
            have nextResources : FrameResourceInvariant
                (frame.reframeNext action reframe) t :=
              resources.next frame slot action t hlookup reframe
            have tailTrace' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact tailTrace
            have hnextStart : ULogSemantics.halted
                (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            have hrestBudget : rest.length ≤ budget - 1 := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨finish, hrun, hfinish⟩ :=
              ih nextResources reframe.runtime_passive hnextStart
                tailTrace' (budget - 1) hnextClock hrestBudget
            exact ⟨finish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                finish slot rest hcycle hrun,
              hfinish⟩

/-- The trace layer consumes the machine-specific exact core directly; the
positive-clock schedule is compiled internally and is no longer an exposed
continuation parameter. -/
theorem acceptingSlotTrace_has_boundedResource_exact_trace_of_core
    {input : List Bool} {suffix : List Tape}
    (core : ExactPositiveCycleCore (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ExactConcreteAcceptingSlotTrace frame.encode word :=
  acceptingSlotTrace_has_boundedResource_exact_trace
    (exactPositiveResourceSchedule_of_core core) resources hruntime hstart
    trace budget hclock hwordBudget

/-- Every resource-certified, clock-bounded semantic accepting trace has its
concrete first-hit realization; the machine-cycle core is discharged by the
total concrete dispatch above. -/
theorem acceptingSlotTrace_has_boundedResource_concrete_exact_trace
    {input : List Bool} {suffix : List Tape}
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ExactConcreteAcceptingSlotTrace frame.encode word :=
  acceptingSlotTrace_has_boundedResource_exact_trace_of_core
    (concreteExactPositiveCycleCore (input := input) (suffix := suffix))
    resources hruntime hstart trace budget hclock hwordBudget

/-- Under exact local cycle certificates, every semantic accepting trace from
a nonhalting frame is an actual first-hit concrete accepting execution. -/
theorem acceptingSlotTrace_has_exact_concrete_accepting_trace
    {input : List Bool} {suffix : List Tape}
    (continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := suffix))
    (acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word) :
    ExactConcreteAcceptingSlotTrace frame.encode word := by
  induction t generalizing frame word with
  | zero =>
      rcases trace with ⟨_, hhalt, _⟩
      simp [hstart] at hhalt
  | succ t ih =>
      rcases trace with hterminal |
        ⟨slot, c', rest, hword, hnotHalted, hstep, htail⟩
      · rcases hterminal with ⟨_, hhalt, _⟩
        simp [hstart] at hhalt
      · subst word
        by_cases haccept : ULogSemantics.accepting c' = true
        · have hrest : rest = [] :=
            htail.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hcycle⟩ := acceptExact frame slot ready c' hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hcycle
              (.nil _),
            rfl⟩
        · have hacceptFalse : ULogSemantics.accepting c' = false := by
            cases hvalue : ULogSemantics.accepting c' <;> simp_all
          by_cases hhalt : ULogSemantics.halted c' = true
          · exact (htail.false_of_halted_not_accepting hhalt hacceptFalse).elim
          · have hhaltFalse : ULogSemantics.halted c' = false := by
              cases hvalue : ULogSemantics.halted c' <;> simp_all
            obtain ⟨action, haction, reframe, hnextReady, hcycle⟩ :=
              continueExact frame slot ready c' hstep hacceptFalse hhaltFalse
            have htail' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact htail
            have hnextStart : ULogSemantics.halted
                (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            obtain ⟨finish, hrun, hfinish⟩ :=
              ih hnextReady hnextStart htail'
            exact ⟨finish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                finish slot rest hcycle hrun,
              hfinish⟩

/-- The exact concrete image map lands in a subtype defined only by genuine
machine execution. -/
def semanticToExactConcreteAccepting
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := suffix))
    (acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false) :
    SemanticAcceptingWords t frame.config →
      ExactConcreteAcceptingWords t frame.encode :=
  fun word =>
    let trace := (mem_acceptingSlotWords_iff t frame.config word.1).mp word.2
    ⟨word.1, trace.length_le_budget,
      acceptingSlotTrace_has_exact_concrete_accepting_trace continueExact
        acceptExact ready hstart trace⟩

theorem semanticToExactConcreteAccepting_apply_val
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := suffix))
    (acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (word : SemanticAcceptingWords t frame.config) :
    (semanticToExactConcreteAccepting t frame continueExact acceptExact ready
      hstart word).1 = word.1 := rfl

/-- Semantic accepting words inject into genuinely concrete exact accepting
words once the two local first-hit cycle obligations are discharged. -/
theorem semanticToExactConcreteAccepting_injective
    {input : List Bool} {suffix : List Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := suffix))
    (acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false) :
    Function.Injective
      (semanticToExactConcreteAccepting t frame continueExact acceptExact ready
        hstart) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun q : ExactConcreteAcceptingWords t frame.encode => q.1) hxy

/-- Resource-certified bootstrap specialization of the genuine concrete
injection.  No semantic membership occurs in the codomain. -/
theorem FrameResourceInvariant.bootstrap_semantic_exact_injective
    {rules : List ULogBytecode.RuleCode} {input padding : List Bool}
    {capacity t : ℕ} {outerTail : List Tape}
    (resources : FrameResourceInvariant
      (bootstrapSemanticFrame rules input padding capacity outerTail) t)
    (runtimePassive : PassivePath
      (bootstrapSemanticFrame rules input padding capacity outerTail).runtime)
    (continueExact : ExactResourceContinuationRefinement
      (input := input) (suffix := ([] : List Tape)))
    (acceptExact : ExactAcceptingCycleRefinement
      (input := input) (suffix := ([] : List Tape))) :
    Function.Injective
      (semanticToExactConcreteAccepting t
        (bootstrapSemanticFrame rules input padding capacity outerTail)
        continueExact acceptExact (resources.frameReady runtimePassive)
        (by
          simp [bootstrapSemanticFrame, ULogSemantics.startFrom,
            ULogSemantics.halted, ULogSemantics.startCode])) :=
  semanticToExactConcreteAccepting_injective t
    (bootstrapSemanticFrame rules input padding capacity outerTail)
    continueExact acceptExact (resources.frameReady runtimePassive)
    (by
      simp [bootstrapSemanticFrame, ULogSemantics.startFrom,
        ULogSemantics.halted, ULogSemantics.startCode])

/-- The uniqueness result applies in particular to every resource-certified
bootstrap encoding.  The resource invariant is used by the forward
existence theorem; uniqueness itself is stronger and follows solely from the
explicit machine transition function and the first-hit discipline. -/
theorem FrameResourceInvariant.bootstrap_exact_run_finish_unique
    {rules : List ULogBytecode.RuleCode} {input padding : List Bool}
    {capacity steps : ℕ} {outerTail : List Tape}
    (resources : FrameResourceInvariant
      (bootstrapSemanticFrame rules input padding capacity outerTail) steps)
    {slots : List Bool} {finish₁ finish₂ : Result}
    (h₁ : ExactConcreteSlotRun
      (bootstrapSemanticFrame rules input padding capacity outerTail).encode
      slots finish₁)
    (h₂ : ExactConcreteSlotRun
      (bootstrapSemanticFrame rules input padding capacity outerTail).encode
      slots finish₂) : finish₁ = finish₂ := by
  have _ := resources
  exact h₁.finish_unique h₂

/-- Two concrete terminal endpoints of the deterministic legacy zero-slot
execution from the same start must coincide. -/
theorem reaches_endpoint_unique_of_concreteHalted
    {start finish₁ finish₂ : Result}
    (h₁ : Reaches start finish₁) (h₂ : Reaches start finish₂)
    (hhalt₁ : concreteHalted finish₁ = true)
    (hhalt₂ : concreteHalted finish₂ = true) :
    finish₁ = finish₂ := by
  have hfreeze₁ : ∀ n, run n finish₁ = finish₁ := by
    intro n
    cases finish₁ with
    | running q z => simp [concreteHalted] at hhalt₁
    | accepted z =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
    | rejected =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
    | stuck =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
  have hfreeze₂ : ∀ n, run n finish₂ = finish₂ := by
    intro n
    cases finish₂ with
    | running q z => simp [concreteHalted] at hhalt₂
    | accepted z =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
    | rejected =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
    | stuck =>
        induction n with
        | zero => rfl
        | succ n ih => simpa [run, oneStep] using ih
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn⟩
  have hmn : run (m + n) start = finish₁ := by
    rw [run_add, hm]
    exact hfreeze₁ n
  have hnm : run (n + m) start = finish₂ := by
    rw [run_add, hn]
    exact hfreeze₂ m
  calc
    finish₁ = run (m + n) start := hmn.symm
    _ = run (n + m) start := by rw [Nat.add_comm]
    _ = finish₂ := hnm

/-- In particular, the deterministic legacy execution cannot both reject
and accept from one start. -/
theorem reaches_rejected_not_accepted
    {start : Result} {z : Zipper Tape}
    (hreject : Reaches start .rejected)
    (haccept : Reaches start (.accepted z)) : False := by
  have hterminal := reaches_endpoint_unique_of_concreteHalted hreject haccept
    (by simp [concreteHalted]) (by simp [concreteHalted])
  cases hterminal

/-- The canonical legacy (slot-zero) execution of a semantic no-rule frame
reaches rejection.  This is intentionally only a legacy `Reaches` statement;
the raw subtype below still contains no semantic membership predicate. -/
theorem semanticNoRule_reaches_rejected
    (c : ULogSemantics.Config)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape)
    (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus false =
      none) :
    Reaches
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      .rejected :=
  branchedReaches_false_to_reaches
    (branchedCycle_semanticNoRule c false input clockZeros capacity runtime
      outer suffix hruntime hfocus hrules hreads hlookup)

/-- The already exact target-one rejection result has the same whole-tail
consequence: it cannot be followed by an accepting raw slot run. -/
theorem exactConcreteCycle_semanticTargetOne_not_accepting_tail
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action) (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity)
    {next : Result} {slots : List Bool} {z : Zipper Tape}
    (cycle : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) next)
    (tail : ExactConcreteSlotRun next slots (.accepted z)) : False := by
  have hnext := exactConcreteCycle_semanticTargetOne_finish_eq_rejected
    c slot action hlookup htarget input clockZeros capacity runtime outer
      suffix hruntime hfocus hreads hwrites hstateCapacity honeCapacity cycle
  subst next
  obtain ⟨-, hfinish⟩ := tail.eq_nil_of_concreteHalted_start (by
    simp [concreteHalted])
  cases hfinish

/-- If an exact raw accepting trace starts at a nonaccepting configuration,
its slot word is nonempty.  This is the base-case exclusion needed by the
forthcoming converse recursion. -/
theorem ExactConcreteAcceptingSlotTrace.slots_ne_nil_of_not_accepting_start
    {start : Result} {slots : List Bool}
    (trace : ExactConcreteAcceptingSlotTrace start slots)
    (hstart : concreteAccepting start = false) : slots ≠ [] := by
  intro hslots
  subst slots
  rcases trace with ⟨finish, run, hfinish⟩
  cases run
  simp [hstart] at hfinish

/-- Numeric form of the nonempty-word fact, suitable for decreasing a
natural slot budget in the converse recursion. -/
theorem ExactConcreteAcceptingSlotTrace.length_pos_of_not_accepting_start
    {start : Result} {slots : List Bool}
    (trace : ExactConcreteAcceptingSlotTrace start slots)
    (hstart : concreteAccepting start = false) : 0 < slots.length := by
  cases slots with
  | nil => exact (trace.slots_ne_nil_of_not_accepting_start hstart rfl).elim
  | cons slot slots => simp

/-- A deterministic legacy rejection has a genuine earliest concrete cycle
stop.  The endpoint is intentionally left outcome-valued: an unrestricted
legacy path may cross a cycle boundary before its eventual rejection, so this
lemma does not falsely identify that first stop with `.rejected`. -/
noncomputable def firstCycleStop_of_reaches_rejected
    {start : Result} (hreject : Reaches start .rejected) :
    Σ finish, FirstValidZeroHit IsConcreteCycleStop start finish := by
  classical
  let bound := Classical.choose hreject
  have hbound : run bound start = .rejected :=
    Classical.choose_spec hreject
  let hex : ∃ n, run n start = .rejected := ⟨bound, hbound⟩
  let n := Nat.find hex
  have hn : run n start = .rejected := Nat.find_spec hex
  have hbefore : ∀ m, m < n → concreteHalted (run m start) = false := by
    intro m hm
    have hle : m ≤ n := Nat.le_of_lt hm
    obtain ⟨k, hnk⟩ := Nat.exists_eq_add_of_le hle
    cases hmid : run m start with
    | running q z => simp [hmid, concreteHalted]
    | accepted z =>
        exfalso
        have hterminal : (.accepted z : Result) = .rejected := by
          calc
            (.accepted z : Result) = run n start := by
              rw [hnk, run_add, hmid, run_accepted]
            _ = .rejected := hn
        cases hterminal
    | rejected =>
        exact (Nat.find_min hex hm hmid).elim
    | stuck =>
        exfalso
        have hterminal : (.stuck : Result) = .rejected := by
          calc
            (.stuck : Result) = run n start := by
              rw [hnk, run_add, hmid, run_stuck]
            _ = .rejected := hn
        cases hterminal
  have hvalid : ValidZeroRun n start .rejected :=
    validZeroRun_of_run_eq_of_not_halted_before hn (by simp) hbefore
  exact ⟨_, hvalid.firstHit (Or.inr rfl)⟩

/-- The common terminal leaf of all four last-rule mismatch branches is a
genuine one-edge zero-slot run.  This is the first exactification point for
the no-match route: unlike the older `Reaches` theorem, it retains both edge
validity and the absence of an earlier cycle stop. -/
def stopFree_fieldCompare_source_invalid_reject
    (slot : Bool) (left : List Tape) (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    StopFreeValidZeroRun 1
      (.running (.fieldCompare .source slot) ⟨left, after, right⟩)
      .rejected :=
  StopFreeValidZeroRun.oneOfStep
    (fieldCompare_source_invalid_reject slot left after right hzero hone)
    (by simp [concreteHalted])
    (by simp)
    (by simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted])

/-- The exact common terminal leaf is the first concrete cycle stop, not
merely a later rejecting endpoint of an unrestricted legacy execution. -/
def fieldCompare_source_invalid_firstStop_reject
    (slot : Bool) (left : List Tape) (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (.running (.fieldCompare .source slot) ⟨left, after, right⟩)
      .rejected :=
  (stopFree_fieldCompare_source_invalid_reject slot left after right hzero
    hone).toFirstHit (Or.inr rfl)

/-- Compose a stop-free deterministic prefix with an already exact first
stop.  This is the composition rule needed to replace the restore/count
`Reaches` links in a last-mismatch proof without losing the first-stop
invariant. -/
def StopFreeValidZeroRun.appendFirstHit
    {a : ℕ} {start middle finish : Result}
    (hprefix : StopFreeValidZeroRun a start middle)
    (tail : FirstValidZeroHit IsConcreteCycleStop middle finish) :
    FirstValidZeroHit IsConcreteCycleStop start finish where
  steps := a + tail.steps
  valid := hprefix.valid.append tail.valid
  hit := tail.hit
  before := by
    intro m hm
    by_cases hma : m < a
    · exact hprefix.stop_free m hma
    · have ham : a ≤ m := Nat.le_of_not_gt hma
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ham
      have hkb : k < tail.steps := by omega
      rw [run_add, hprefix.valid.eq_run]
      exact tail.before k hkb

/-- Any future stop-free exactification of a last-mismatch restore/count
prefix can be closed at the common invalid-source leaf by this one rule.  It
is polymorphic in the prefix start, so it applies uniformly to source,
read, slot, and length mismatch exits once their existing legacy prefixes
are upgraded. -/
def lastMismatch_firstStop_reject_of_stopFreePrefix
    {n : ℕ} {start : Result}
    (slot : Bool) (left : List Tape) (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true)
    (hprefix : StopFreeValidZeroRun n start
      (.running (.fieldCompare .source slot) ⟨left, after, right⟩)) :
    FirstValidZeroHit IsConcreteCycleStop start .rejected :=
  hprefix.appendFirstHit
    (fieldCompare_source_invalid_firstStop_reject slot left after right hzero
      hone)

/-- The certified mismatching rules before the final rule already support a
single genuine stop-free prefix.  This is an actual no-match exactifier (not
an abstract connector): the four mismatch cases are discharged by
`cursorMismatchStopFreeStep`, while the final rule is deliberately left as
the remaining exactification boundary. -/
noncomputable def stopFree_certifiedNoMatch_prefix
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual programToHead runtime
      skip last) :
    Σ n, StopFreeValidZeroRun n
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ [last])) (skip ++ [last])
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual
        (canonicalRuleCursor skip [last]) [last]
        programToHead runtime outer suffix) := by
  let trace := mismatchCertificateList_initial_trace slot current actual
    programToHead runtime cert.mismatches (by simp)
  exact stopFree_mismatchPrefix cursorMismatchStopFreeStep slot current actual
    programToHead runtime outer suffix trace

/-- Re-express the certified stop-free mismatch prefix at the dynamic source
entry used by a concrete semantic cycle.  This is the concrete bridge from
the selected branch's rule-source scan to the remaining final-rule boundary. -/
noncomputable def stopFree_dynamicCertifiedNoMatch_prefix
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last) :
    Σ n, StopFreeValidZeroRun n
      (dynamicRuleSourceStarted slot leftTape (skip ++ [last]) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (ruleCursorResult slot current actual
        (canonicalRuleCursor skip [last]) [last]
        (cursorDynamicProgramToHead input leftTape) runtime outer suffix) := by
  obtain ⟨n, hprefix⟩ := stopFree_certifiedNoMatch_prefix slot current actual
    (cursorDynamicProgramToHead input leftTape) runtime outer suffix skip
    last cert
  refine ⟨n, ?_⟩
  rw [dynamicRuleSourceStarted_eq_cursorResult slot current actual leftTape
    input skip last [] runtime outer suffix]
  exact hprefix

/-- Full certified no-match rejection, upgraded from its legacy path to the
actual first concrete cycle stop.  Its endpoint remains outcome-valued for
the same reason as `firstCycleStop_of_reaches_rejected`: proving that this
first stop is specifically rejection requires the remaining final-last-rule
control-flow exclusion, rather than mere reachability. -/
noncomputable def firstCycleStop_certifiedNoMatch
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual programToHead runtime
      skip last)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Σ finish, FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ [last])) (skip ++ [last])
        programToHead runtime outer suffix)
      finish :=
  firstCycleStop_of_reaches_rejected
    (reaches_certifiedNoMatch_reject slot current actual programToHead runtime
      outer suffix skip last cert after right hafter hzero hone)

/-- Exact final-rule slot-mismatch prefix.  Unlike the older last-rule
reachability proof, this retains the genuine zero edges up to the restore
controller; the subsequent restore/count rejection tail is kept separate. -/
noncomputable def stopFree_lastRuleSlotMismatch_restorePrefix
    (slot : Bool) (done : ℕ) (path : List Tape)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath [] programToHead))) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath r.source r.read)
          ((List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
          (ulogCore boundary)
          (codeTape (!slot) ::
            encodedActionPath r.action.write r.action.target r.action.move
              (cursorMatchedMovePath [] programToHead) ++
            readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read slot boundary
    hboundary r [] programToHead pcBase (readHeadNat r.read) runtime suffix
    hsourceCorridor
  obtain ⟨b, hmismatch⟩ := stopFree_sourceReadAtSlotMismatch_boundary
    slot r.source r.read hread boundary pcBase
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath [] programToHead)) runtime suffix hreadScan
  rw [hslot] at hsource
  exact ⟨a + b, by simpa [pcBase, List.append_assoc] using
    (hsource.append hmismatch)⟩

/-- Exact final-rule read-mismatch prefix, parallel to the slot-mismatch
prefix above and likewise ending at the restore controller. -/
noncomputable def stopFree_lastRuleReadMismatch_restorePrefix
    (slot : Bool) (done : ℕ) (path : List Tape)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programToHead : List Tape)
    (actual : ℕ) (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead
        (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r [] programToHead)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r [] programToHead))
          ((List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
          (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  obtain ⟨a, hsource⟩ := stopFree_ruleCursorSourceMatch_read slot boundary
    hboundary r [] programToHead pcBase (readHeadNat actual) runtime suffix
    hsourceCorridor
  obtain ⟨b, hmismatch⟩ := stopFree_sourceReadAtMismatch_boundary
    slot r.source r.read actual hread hactual hreadNe boundary pcBase
    (cursorReadScanPath r [] programToHead) runtime suffix hreadScan
  exact ⟨a + b, by simpa [pcBase, List.append_assoc] using
    (hsource.append hmismatch)⟩

/-- Exact final-rule source-short mismatch prefix through its restore
controller. -/
noncomputable def stopFree_lastRuleSourceShort_restorePrefix
    (slot : Bool) (done : ℕ) (path : List Tape)
    (boundary : ULogLetter)
    (r : ULogBytecode.RuleCode) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceShortRestorePath r.source
            (ruleContinuationCorridor r [] programPath))
          ((List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
          (ulogCore boundary)
          (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  obtain ⟨n, hrestore⟩ := stopFree_atBitsSourceShort_restore slot r []
    programPath extra boundary pcBase suffix hcorridor
  exact ⟨n, by simpa [pcBase] using hrestore⟩

/-- Exact final-rule source-long mismatch prefix through its restore
controller. -/
noncomputable def stopFree_lastRuleSourceLong_restorePrefix
    (slot : Bool) (done : ℕ) (path : List Tape)
    (boundary : ULogLetter)
    (r : ULogBytecode.RuleCode) (programPath : List Tape)
    (current extra : ℕ) (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath)) :
    Σ n, StopFreeValidZeroRun n
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (sourceLongRestorePath extra current
            (ruleContinuationCorridor r [] programPath))
          ((List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
          (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer
  obtain ⟨n, hrestore⟩ := stopFree_atBitsSourceLong_restore slot r []
    programPath current extra hsource boundary pcBase suffix hcorridor
  exact ⟨n, by simpa [pcBase] using hrestore⟩

/-- The empty-rule-list terminal case of mismatch skipping.  The ordinary
skip helper deliberately requires a nonempty continuation; here its final
move-second edge lands at the invalid-source field comparison and is closed
by the genuine rejecting first stop. -/
noncomputable def firstStop_mismatchSkipRule_last
    (lookupSlot : Bool) (r : ULogBytecode.RuleCode)
    (left : List Tape) (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r) left after right)
      .rejected := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [moveFirst move, moveSecond move]
  let lS := sBits.reverse.map codeTape ++ left
  let lR := rBits.reverse.map codeTape ++ lS
  let lSlot := codeTape ruleSlot :: lR
  let lW := wBits.reverse.map codeTape ++ lSlot
  let lT := tBits.reverse.map codeTape ++ lW
  let lM₁ := codeTape (moveFirst move) :: lT
  let lM₂ := mismatchBoundaryTape (moveSecond move) :: lM₁
  obtain ⟨nS, hS⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipSource lookupSlot) (.mismatchSkipRead lookupSlot)
    (by intro h; cases h) source
    (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits)
    (by simp [rBits, ULogBytecode.encodeNatField])
    (mismatchSkipSource_zero lookupSlot) (mismatchSkipSource_one lookupSlot)
    left after right
  obtain ⟨nR, hR⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipRead lookupSlot) (.mismatchSkipSlot lookupSlot)
    (by intro h; cases h) read
    ([ruleSlot] ++ wBits ++ tBits ++ mBits) (by simp)
    (mismatchSkipRead_zero lookupSlot) (mismatchSkipRead_one lookupSlot)
    lS after right
  have hSlot : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits) lR after right)
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits) lSlot after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [lSlot, List.append_assoc] using
        atBits_mismatchSlot lookupSlot ruleSlot (wBits ++ tBits ++ mBits)
          lR after right
    · cases lookupSlot <;> cases ruleSlot <;> rfl
    · cases write <;> simp [atBits, wBits, ULogBytecode.encodeNatField,
        List.replicate_succ]
    · cases lookupSlot <;> cases ruleSlot <;>
        simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  obtain ⟨nW, hW⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipWrite lookupSlot) (.mismatchSkipTarget lookupSlot)
    (by intro h; cases h) write (tBits ++ mBits)
    (by simp [tBits, ULogBytecode.encodeNatField])
    (mismatchSkipWrite_zero lookupSlot) (mismatchSkipWrite_one lookupSlot)
    lSlot after right
  obtain ⟨nT, hT⟩ := stopFree_unaryState_prefix_of
    (.mismatchSkipTarget lookupSlot) (.mismatchSkipMoveFirst lookupSlot)
    (by intro h; cases h) target mBits (by simp [mBits])
    (mismatchSkipTarget_zero lookupSlot) (mismatchSkipTarget_one lookupSlot)
    lW after right
  have hM₁ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveFirst lookupSlot) mBits lT after right)
      (atBits (.mismatchSkipMoveSecond lookupSlot) [moveSecond move]
        lM₁ after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [mBits, lM₁, List.append_assoc] using
        atBits_mismatchMoveFirst lookupSlot (moveFirst move)
          [moveSecond move] lT after right
    · cases lookupSlot <;> cases move <;> rfl
    · cases lookupSlot <;> cases move <;> simp [atBits]
    · cases lookupSlot <;> cases move <;>
        simp [atBits, mBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  have hM₂ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveSecond lookupSlot) [moveSecond move]
        lM₁ after right)
      (atBits (.fieldCompare .source lookupSlot) [] lM₂ after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [lM₂] using atBits_mismatchMoveSecond lookupSlot
        (moveSecond move) [] lM₁ after right
    · cases lookupSlot <;> cases move <;> rfl
    · cases lookupSlot <;> cases move <;> simp [atBits]
    · cases lookupSlot <;> cases move <;>
        simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  dsimp [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW, lT, lM₁,
    lM₂] at hS hR hSlot hW hT hM₁ hM₂
  simp only [List.append_assoc] at hS hR hSlot hW hT hM₁ hM₂
  have hprefix := (((((hS.append hR).append hSlot).append hW).append hT).append
    hM₁).append hM₂
  have hterminal : FirstValidZeroHit IsConcreteCycleStop
      (atBits (.fieldCompare .source lookupSlot) [] lM₂ after right)
      .rejected := by
    simpa [atBits] using
      fieldCompare_source_invalid_firstStop_reject lookupSlot lM₂ after right
        hzero hone
  simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW, lT, lM₁,
    lM₂, ULogBytecode.encodeRule, ULogBytecode.encodeAction,
    List.reverse_append, List.map_append, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hprefix.appendFirstHit hterminal

/-- Shared exact count/skip tail for the final mismatching rule. -/
noncomputable def firstStop_mismatchCount_lastRule_reject
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (left : List Tape)
    (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          left (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      .rejected := by
  let countLeft := ulogCore codeZero ::
    List.replicate done (ulogCore codeZero) ++ left
  obtain ⟨a, hcount⟩ := stopFree_mismatchCount_prefix_fresh lookupSlot done
    path left (ulogCore boundary)
    ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)
  obtain ⟨b, hseek⟩ := stopFree_mismatchSeekBoundary_rule lookupSlot path
    hpath.1 boundary hboundary r [] countLeft after right
  have hcount' : StopFreeValidZeroRun a
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          left (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      (.running (.mismatchSeekBoundary lookupSlot)
        (beforeRightPath path countLeft (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right))) := by
    simpa [countLeft, List.append_assoc] using hcount
  have hskip := firstStop_mismatchSkipRule_last lookupSlot r
    ((if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: path.reverse ++ countLeft)
    after right hzero hone
  have hseek' : StopFreeValidZeroRun b
      (.running (.mismatchSeekBoundary lookupSlot)
        (beforeRightPath path countLeft (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r)
        ((if boundary = sourceBoundaryZero then ulogCore codeZero
          else ulogCore codeOne) :: path.reverse ++ countLeft)
        after right) := by
    simpa only [List.append_nil] using hseek
  have ht := hseek'.appendFirstHit hskip
  have ht' : FirstValidZeroHit IsConcreteCycleStop
      (.running (.mismatchSeekBoundary lookupSlot)
        (beforeRightPath path countLeft (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      .rejected := by
    simpa only [List.append_nil] using ht
  exact hcount'.appendFirstHit ht'

/-- Shared exact restore/count tail of a final mismatching rule. -/
noncomputable def firstStop_restoreMismatchLastRule_reject
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (restorePath : List Tape) (hrestoreSafe : MismatchRestorePathSafe restorePath)
    (mismatchRight : List Tape) (r : ULogBytecode.RuleCode)
    (outer : List Tape) (after : Tape) (right : List Tape)
    (hrestored : restorePath.reverse.map restoreMismatchCell ++ mismatchRight =
      (ULogBytecode.encodeRule r).map codeTape ++ after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (.running (.restoreRule lookupSlot)
        (beforeLeftPath restorePath
          ((List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
          (ulogCore boundary) mismatchRight))
      .rejected := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      obtain ⟨a, hrestore⟩ := stopFree_restoreRule_boundary lookupSlot
        restorePath hrestoreSafe boundary hboundary
        (xs ++ ulogCore pcMark :: outer) x mismatchRight
      have hrestored' :
          (restorePath.map restoreMismatchCell).reverse ++ mismatchRight =
            (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
        simpa only [List.map_reverse] using hrestored
      have hrestore' : StopFreeValidZeroRun a
          (.running (.restoreRule lookupSlot)
            (beforeLeftPath restorePath
              (returnPath ++ ulogCore pcMark :: outer)
              (ulogCore boundary) mismatchRight))
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r).map codeTape ++ after :: right))) := by
        simpa [returnPath, he, beforeLeftPath,
          hrestored', List.append_assoc] using hrestore
      have hreturnSafe : ∀ y ∈ returnPath, y ≠ ulogCore pcMark := by
        intro y hy
        have hy' : y ∈ path ∨ y = ulogCore pcDone ∨
            (done ≠ 0 ∧ y = ulogCore codeZero) := by
          simpa [returnPath] using hy
        rcases hy' with hp | hd | hz
        · exact hpath.2 y hp
        · rw [hd]; native_decide
        · rw [hz.2]; native_decide
      obtain ⟨b, hreturnRun⟩ := stopFree_mismatchReturnToPc lookupSlot
        returnPath hreturnSafe outer (ulogCore boundary)
        ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)
      have hreturn' : StopFreeValidZeroRun b
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
          (.running (.mismatchCount lookupSlot)
            (beforeRightPath
              (List.replicate done (ulogCore codeZero) ++
                ulogCore pcDone :: path)
              (ulogCore pcMark :: outer) (ulogCore boundary)
              ((ULogBytecode.encodeRule r).map codeTape ++ after :: right))) := by
        simpa [returnPath] using hreturnRun
      have hcount := firstStop_mismatchCount_lastRule_reject lookupSlot done
        path hpath boundary hboundary r (ulogCore pcMark :: outer) after right
        hzero hone
      exact hrestore'.appendFirstHit (hreturn'.appendFirstHit hcount)

/-- Complete exact first-stop rejection for the final slot-mismatch branch. -/
noncomputable def firstStop_lastRuleSlotMismatch_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath [] programToHead)))
    (hrestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat r.read :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  obtain ⟨n, hpref⟩ := stopFree_lastRuleSlotMismatch_restorePrefix slot done
    path boundary hboundary r hslot programToHead hread runtime outer suffix
    hsourceCorridor hreadScan
  have hrestored := cursorSlotMismatch_restored slot r hslot [] programToHead
    runtime suffix
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (slotMismatchRestorePath r.source r.read).reverse.map
          restoreMismatchCell ++
        (codeTape (!slot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath [] programToHead) ++
          readHeadNat r.read :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) =
        (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programToHead ++ readHeadNat r.read :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) := by
            simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have htail := firstStop_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary (slotMismatchRestorePath r.source r.read) hrestoreSafe
    (codeTape (!slot) ::
      encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath [] programToHead) ++ readHeadNat r.read ::
          runtime ++ List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
    r outer after right hrestored' hzero hone
  exact hpref.appendFirstHit htail

/-- Complete exact first-stop rejection for the final read-mismatch branch. -/
noncomputable def firstStop_lastRuleReadMismatch_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programToHead : List Tape)
    (actual : ℕ) (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r [] programToHead))
    (hrestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  obtain ⟨n, hpref⟩ := stopFree_lastRuleReadMismatch_restorePrefix slot done
    path boundary hboundary r programToHead actual hread hactual hreadNe
    runtime outer suffix hsourceCorridor hreadScan
  have hrestored := cursorReadMismatch_restored r [] programToHead runtime
    suffix actual hrestoreIdentity
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)).reverse.map
          restoreMismatchCell ++
        (readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) =
        (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programToHead ++ readHeadNat actual :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) := by
            simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have htail := firstStop_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary
    (readMismatchRestorePath r.source r.read
      (cursorReadScanPath r [] programToHead)) hrestoreSafe
    (readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix)
    r outer after right hrestored' hzero hone
  exact hpref.appendFirstHit htail

/-- Complete exact first-stop rejection for final source-short mismatch. -/
noncomputable def firstStop_lastRuleSourceShort_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨ boundary = sourceBoundaryZero ∨
      boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r [] programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++
        List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source slot) (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++ ulogCore pcDone :: path).reverse ++
            ulogCore pcMark :: outer)
        (programPath ++ List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) .rejected := by
  obtain ⟨n, hpref⟩ := stopFree_lastRuleSourceShort_restorePrefix slot done
    path boundary r programPath extra outer suffix hcorridor
  have hrestored := ruleSourceShort_restored r [] programPath suffix extra
    hcorridor hreadBoundary
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (sourceShortRestorePath r.source
        (ruleContinuationCorridor r [] programPath)).reverse.map
          restoreMismatchCell ++
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
        (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programPath ++ List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
            simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have htail := firstStop_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary
    (sourceShortRestorePath r.source (ruleContinuationCorridor r [] programPath))
    (sourceShortRestorePath_safe r.source
      (ruleContinuationCorridor r [] programPath) hcorridor)
    (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
    r outer after right hrestored' hzero hone
  exact hpref.appendFirstHit htail

/-- Complete exact first-stop rejection for final source-long mismatch. -/
noncomputable def firstStop_lastRuleSourceLong_reject
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨ boundary = sourceBoundaryZero ∨
      boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (programPath : List Tape)
    (current extra : ℕ) (hsource : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r [] programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r [] programPath,
      x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source slot) (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++ ulogCore pcDone :: path).reverse ++
            ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) .rejected := by
  obtain ⟨n, hpref⟩ := stopFree_lastRuleSourceLong_restorePrefix slot done
    path boundary r programPath current extra hsource outer suffix hcorridor
  have hrestored := ruleSourceLong_restored r [] programPath suffix current
    extra hsource hcorridor hreadBoundary
  have hafter' := congrArg
    (fun xs => (ULogBytecode.encodeRule r).map codeTape ++ xs) hafter
  have hrestored' :
      (sourceLongRestorePath extra current
        (ruleContinuationCorridor r [] programPath)).reverse.map
          restoreMismatchCell ++ ulogCore stateOne :: suffix =
        (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
    calc
      _ = (ULogBytecode.encodeRule r).map codeTape ++
          (programPath ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix) := by
            simpa [ULogBytecode.encodeRules, List.append_assoc] using hrestored
      _ = _ := by simpa [List.append_assoc] using hafter'
  have htail := firstStop_restoreMismatchLastRule_reject slot done path hpath
    boundary hboundary
    (sourceLongRestorePath extra current (ruleContinuationCorridor r [] programPath))
    (sourceLongRestorePath_safe extra current
      (ruleContinuationCorridor r [] programPath) hcorridor)
    (ulogCore stateOne :: suffix) r outer after right hrestored' hzero hone
  exact hpref.appendFirstHit htail

/-- Exact unified rejection of the final rule in a certified no-match scan.
This is the first-hit counterpart of the legacy unified `Reaches` theorem;
each mismatch case is discharged by its already exact branch above. -/
noncomputable def firstStop_lastRuleMismatch_reject
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (done : ℕ) (path : List Tape) (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode)
    (hmismatch : ¬ RuleMatchesCursor slot current actual r)
    (hreadCode : r.read < 3)
    (programToHead runtime outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r [] programToHead (readHeadNat actual) runtime))
    (hreadBoundary : ∀ x ∈
      cursorRuleCorridor r [] programToHead (readHeadNat actual) runtime,
        x ≠ ulogCore readBoundary)
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r [] programToHead))
    (hreadRestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r [] programToHead)))
    (hslotScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath [] programToHead)))
    (hslotRestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules [r])
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse ++ ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      .rejected := by
  by_cases hsource : r.source = current
  · by_cases hread : r.read = actual
    · have hslotNe : r.slot ≠ slot := by
        intro hslot
        exact hmismatch ⟨hsource, hread, hslot⟩
      have hslot : r.slot = !slot := by
        cases hrslot : r.slot <;> cases hsslot : slot <;> simp_all
      have h := firstStop_lastRuleSlotMismatch_reject slot done path hpath
        boundary hboundary r hslot programToHead hreadCode runtime outer suffix
        (by simpa [hread] using hcorridor)
        (by simpa [hslot] using hslotScan)
        (by simpa [hsource, hread] using hslotRestoreSafe)
        after right (by simpa [hsource, hread] using hafter) hzero hone
      simpa [hsource, hread, List.append_assoc] using h
    · have h := firstStop_lastRuleReadMismatch_reject slot done path hpath
        boundary hboundary r programToHead actual hreadCode hactual hread
        runtime outer suffix hcorridor hreadScan hreadRestoreSafe
        hrestoreIdentity after right (by simpa [hsource] using hafter)
        hzero hone
      simpa [hsource, List.append_assoc] using h
  · by_cases hlt : r.source < current
    · let extra := current - r.source - 1
      have hcurrent : current = r.source + extra + 1 := by
        dsimp [extra]
        omega
      have h := firstStop_lastRuleSourceShort_reject slot done path hpath
        boundary hboundary r (programToHead ++ readHeadNat actual :: runtime)
        extra outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
        after right (by simpa [hcurrent, List.append_assoc] using hafter)
        hzero hone
      simpa [hcurrent, List.append_assoc] using h
    · have hcurLt : current < r.source := by omega
      let extra := r.source - current - 1
      have hrsource : r.source = current + extra + 1 := by
        dsimp [extra]
        omega
      have h := firstStop_lastRuleSourceLong_reject slot done path hpath
        boundary hboundary r (programToHead ++ readHeadNat actual :: runtime)
        current extra hrsource outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using hcorridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using hreadBoundary)
        after right (by simpa [List.append_assoc] using hafter) hzero hone
      simpa [List.append_assoc] using h

 /-- A certified no-match scan reaches the rejecting terminal at its genuine
first concrete cycle stop.  The stop-free prefix discharges all rules before
the final one, and the unified final-rule theorem discharges that remaining
rule without reverting to an unrestricted `Reaches` witness. -/
noncomputable def firstStop_certifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual programToHead runtime
      skip last)
    (after : Tape) (right : List Tape)
    (hafter : programToHead ++ readHeadNat actual :: runtime ++
        List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ [last])) (skip ++ [last])
        programToHead runtime outer suffix)
      .rejected := by
  obtain ⟨n, hprefix⟩ := stopFree_certifiedNoMatch_prefix slot current actual
    programToHead runtime outer suffix skip last cert
  have hboundary :
      (canonicalRuleCursor skip [last]).boundary = sourceBoundary ∨
        (canonicalRuleCursor skip [last]).boundary = sourceBoundaryZero ∨
          (canonicalRuleCursor skip [last]).boundary = sourceBoundaryOne :=
    boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hlast := firstStop_lastRuleMismatch_reject slot current actual
    cert.lastMismatch.actual_valid (canonicalRuleCursor skip [last]).done
    (canonicalRuleCursor skip [last]).path
    (canonicalRuleCursor_path_safe skip [last])
    (canonicalRuleCursor skip [last]).boundary hboundary last
    cert.lastMismatch.mismatch cert.lastMismatch.read_valid
    programToHead runtime outer suffix cert.lastMismatch.source_corridor
    cert.lastMismatch.read_boundary_free cert.lastMismatch.read_scan
    cert.lastMismatch.read_restore cert.lastMismatch.slot_scan
    cert.lastMismatch.slot_restore cert.lastMismatch.program_restore
    after right hafter hzero hone
  exact hprefix.appendFirstHit hlast

/-- The dynamic rule-source entry inherits the exact first-stop rejection of
the normalized certified cursor scan. -/
noncomputable def firstStop_dynamicCertifiedNoMatch_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last)
    (after : Tape) (right : List Tape)
    (hafter : cursorDynamicProgramToHead input leftTape ++
        readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    FirstValidZeroHit IsConcreteCycleStop
      (dynamicRuleSourceStarted slot leftTape (skip ++ [last]) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      .rejected := by
  have hfull := firstStop_certifiedNoMatch_reject slot current actual
    (cursorDynamicProgramToHead input leftTape) runtime outer suffix skip
    last cert after right hafter hzero hone
  rw [← dynamicRuleSourceStarted_eq_cursorResult slot current actual leftTape
    input skip last [] runtime outer suffix] at hfull
  exact hfull

/-- The chosen slot enters the dynamic no-match scan through its actual
one-step branch, and that branch has a first-hit rejecting suffix. -/
structure ExactNoMatchBranchWitness (slot : Bool) (choice : Result) : Type where
  branchStart : Result
  branch_eq : oneStepAt (ULogBytecode.slotIndex slot) choice = branchStart
  first_hit : FirstValidZeroHit IsConcreteCycleStop branchStart .rejected

noncomputable def chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
    (slot : Bool) (current actual : ℕ)
    (input : List Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode) (last : ULogBytecode.RuleCode)
    (cert : NoMatchCertificate slot current actual
      (cursorDynamicProgramToHead input leftTape) runtime skip last)
    (after : Tape) (right : List Tape)
    (hafter : cursorDynamicProgramToHead input leftTape ++
        readHeadNat actual :: runtime ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix = after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    ExactNoMatchBranchWitness slot
      (.running .chooseSlot
        ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
            ulogCore pcMark :: outer,
          readHeadNat actual,
          runtime ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩) := by
  have hhead : choiceHead (readHeadNat actual) = true := by
    have hactual := cert.lastMismatch.actual_valid
    interval_cases actual <;> native_decide
  have htail := firstStop_dynamicCertifiedNoMatch_reject slot current actual
    input leftTape runtime outer suffix skip last cert after right hafter
    hzero hone
  obtain ⟨n, hdynamic⟩ := stopFree_dynamicRuleSourceStarted slot leftTape
    hleft (skip ++ [last]) (by simp) input outer (readHeadNat actual)
    (runtime ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have hbranch :
      oneStepAt (ULogBytecode.slotIndex slot)
          (.running .chooseSlot
            ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
                ulogCore pcMark :: outer,
              readHeadNat actual,
              runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) =
        .running (.ruleSeekChoice slot)
          (beforeLeftPath
            (dynamicRuleReturnPath leftTape (skip ++ [last]) input) outer
            (ulogCore pcMark)
            (readHeadNat actual ::
              (runtime ++ List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))) := by
    have hpne := dynamicRuleReturnPath_ne_nil leftTape (skip ++ [last]) input
    cases hpath : dynamicRuleReturnPath leftTape (skip ++ [last]) input with
    | nil => exact (hpne hpath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x
                (runtime ++ List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)
        | true =>
            simpa [beforeLeftPath, hpath, ULogBytecode.slotIndex,
              List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat actual) hhead
                (xs ++ ulogCore pcMark :: outer) x
                (runtime ++ List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)
  have hdynamic' : StopFreeValidZeroRun n
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨dynamicRuleReturnPath leftTape (skip ++ [last]) input ++
              ulogCore pcMark :: outer,
            readHeadNat actual,
            runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩))
      (dynamicRuleSourceStarted slot leftTape (skip ++ [last]) input outer
        (readHeadNat actual)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
    rw [hbranch]
    exact hdynamic
  exact
    { branchStart := .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath leftTape (skip ++ [last]) input) outer
          (ulogCore pcMark)
          (readHeadNat actual ::
            (runtime ++ List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))
      branch_eq := hbranch
      first_hit := by
        rw [← hbranch]
        exact hdynamic'.appendFirstHit htail }

/-- A semantic no-rule lookup has a canonical exact concrete rejecting cycle
for either selected slot.  Its construction follows the target-one exact
cycle discipline: clock decrement to the first choice, one selected branch,
then a stop-free scan ending at the first rejecting stop. -/
theorem branchedCycle_semanticNoRule_exact_nonempty
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none) :
    Nonempty (ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) .rejected) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, last, heq, cert⟩ := automatic_lookup_none
    slot c.state c.focus hfocus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    hp hclock c.program hrules hreads hlookup
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  let choiceLeft := dynamicRuleReturnPath (c.leftRev.map payloadNat)
    (skip ++ [last]) input ++ ulogCore pcMark :: outer
  let choiceRight :=
    clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
      List.replicate c.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix
  have hchoice := clockDecrementCells_firstChoice (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    choiceLeft
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
  have hchoice' : FirstValidZeroHit IsConcreteChoice
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.running .chooseSlot ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) := by
    simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
      clockCellsAfter, heq, choiceLeft, choiceRight,
      List.append_assoc] using hchoice
  have hselected : FirstValidZeroHit IsConcreteCycleStop
      (oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩))
      .rejected := by
    cases hinput : input with
    | nil =>
        obtain ⟨branchStart, hbranch, hreject⟩ :=
          chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
            slot c.state c.focus [] (c.leftRev.map payloadNat)
            (payloadNatList_safe c.leftRev)
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            outer (ulogCore stateSep ::
              List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
                suffix)
            skip last (by simpa [hinput] using cert)
            (ulogCore payloadStartOne)
            ((c.leftRev.map payloadNat).reverse ++ readHeadNat c.focus ::
              clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
              List.replicate c.state (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep ::
                  List.replicate (capacity - c.state)
                    MStarConcreteAlphabet.work ++ suffix)
            (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
              List.append_assoc]) (by native_decide) (by native_decide)
        have hbranch' :
            oneStepAt (ULogBytecode.slotIndex slot)
                (.running .chooseSlot
                  ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
              branchStart := by
          simpa [choiceLeft, choiceRight, hinput, List.append_assoc] using
            hbranch
        rw [hbranch']
        exact hreject
    | cons b bs =>
        obtain ⟨branchStart, hbranch, hreject⟩ :=
          chooseSlot_dynamicCertifiedNoMatch_firstHit_reject
            slot c.state c.focus (b :: bs) (c.leftRev.map payloadNat)
            (payloadNatList_safe c.leftRev)
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            outer (ulogCore stateSep ::
              List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
                suffix)
            skip last (by simpa [hinput] using cert)
            (ulogCore payloadStartDone)
            (List.replicate bs.length (ulogCore payloadDone) ++
              ulogCore payloadEnd :: (c.leftRev.map payloadNat).reverse ++
                readHeadNat c.focus ::
                  clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
                List.replicate c.state (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep ::
                    List.replicate (capacity - c.state)
                      MStarConcreteAlphabet.work ++ suffix)
            (by simp [cursorDynamicProgramToHead, payloadProgramPrefix,
              List.reverse_append, List.append_assoc])
            (by native_decide) (by native_decide)
        have hbranch' :
            oneStepAt (ULogBytecode.slotIndex slot)
                (.running .chooseSlot
                  ⟨choiceLeft, readHeadNat c.focus, choiceRight⟩) =
              branchStart := by
          simpa [choiceLeft, choiceRight, hinput, List.append_assoc] using
            hbranch
        rw [hbranch']
        exact hreject
  exact ⟨exactConcreteCycleOfChoiceHead choiceLeft (readHeadNat c.focus)
    choiceRight hhead hchoice' hselected⟩

/-- First-hit cycle uniqueness forces every raw exact no-rule cycle from the
same semantic encoding to end in rejection. -/
theorem exactConcreteCycle_semanticNoRule_finish_eq_rejected
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none)
    {finish : Result}
    (raw : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) finish) :
    finish = .rejected := by
  obtain ⟨canonical⟩ := branchedCycle_semanticNoRule_exact_nonempty c slot
    input clockZeros capacity runtime outer suffix hruntime hfocus hrules
    hreads hlookup
  exact raw.finish_unique canonical

/-- A no-rule exact cycle cannot be followed by an accepting raw slot run. -/
theorem exactConcreteCycle_semanticNoRule_not_accepting_tail
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      none)
    {next : Result} {slots : List Bool} {z : Zipper Tape}
    (cycle : ExactConcreteCycle slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c) next)
    (tail : ExactConcreteSlotRun next slots (.accepted z)) : False := by
  have hnext := exactConcreteCycle_semanticNoRule_finish_eq_rejected c slot
    input clockZeros capacity runtime outer suffix hruntime hfocus hrules
    hreads hlookup cycle
  subst next
  obtain ⟨-, hfinish⟩ := tail.eq_nil_of_concreteHalted_start (by
    simp [concreteHalted])
  cases hfinish

end PakFixedPolyomino.ULogBootstrapExecution
