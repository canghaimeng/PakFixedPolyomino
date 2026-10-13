import PakFixedPolyomino.FiniteOneTapeSemantics
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Standard finite nondeterministic one-tape machine semantics

The branching degree and finite alphabet/state counts belong to a machine,
not to its input. Input is written as binary letters starting at coordinate
zero, with blanks everywhere else. Each transition writes one tape cell and
moves by at most one cell. There is no arbitrary configuration initializer,
normalization certificate, preallocated window, or spatial restriction.

An accepting branch is a finite sequence of literal transition labels ending
in the halting accept state. Different labels remain different branches even
when their actions coincide. Variable halting lengths are counted separately;
no unproved exact-deadline padding is built into the source definition.
-/

namespace PakFixedPolyomino.StandardNondeterministicMachine

open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (Config moveHead writtenTape)

/-- Ordinary finite machine data, with any finite branching degree. Missing
transitions are dead rejecting branches. Accept/reject have no transitions. -/
structure Machine (ns nt branching : ℕ) where
  rule : Fin ns → Fin nt → Fin branching → Option (Action (Fin ns) (Fin nt))
  start : Fin ns
  accept : Fin ns
  reject : Fin ns
  accept_ne_reject : accept ≠ reject
  blank : Fin nt
  zero : Fin nt
  one : Fin nt
  blank_ne_zero : blank ≠ zero
  blank_ne_one : blank ≠ one
  zero_ne_one : zero ≠ one
  accept_terminal : ∀ x slot, rule accept x slot = none
  reject_terminal : ∀ x slot, rule reject x slot = none

abbrev Configuration (ns nt : ℕ) := Config (Fin ns) (Fin nt)

variable {ns nt branching : ℕ}

def inputTape (M : Machine ns nt branching) (x : List Bool) (z : Int) : Fin nt :=
  if hz : 0 ≤ z then
    if hi : z.toNat < x.length then
      if x[z.toNat] then M.one else M.zero
    else M.blank
  else M.blank

def initial (M : Machine ns nt branching) (x : List Bool) : Configuration ns nt :=
  { state := M.start, head := 0, tape := inputTape M x }

theorem inputTape_ofNat (M : Machine ns nt branching) (x : List Bool)
    (i : ℕ) (hi : i < x.length) :
    inputTape M x (i : Int) = if x[i] then M.one else M.zero := by
  simp [inputTape, hi]

theorem inputTape_neg (M : Machine ns nt branching) (x : List Bool)
    (z : Int) (hz : z < 0) : inputTape M x z = M.blank := by
  have : ¬0 ≤ z := by omega
  simp [inputTape, this]

theorem inputTape_ge (M : Machine ns nt branching) (x : List Bool)
    (z : Int) (hz : (x.length : Int) ≤ z) : inputTape M x z = M.blank := by
  have hnonneg : 0 ≤ z := by omega
  have hlength : x.length ≤ z.toNat := (Int.le_toNat hnonneg).mpr hz
  simp [inputTape, hnonneg, Nat.not_lt.mpr hlength]

/-- One genuine tape transition. An unused label has no successor. -/
def step (M : Machine ns nt branching) (slot : Fin branching)
    (c : Configuration ns nt) : Option (Configuration ns nt) :=
  (M.rule c.state (c.tape c.head) slot).map fun a =>
    { state := a.target
      head := moveHead a.move c.head
      tape := writtenTape c a.write }

def run (M : Machine ns nt branching) :
    List (Fin branching) → Configuration ns nt → Option (Configuration ns nt)
  | [], c => some c
  | slot :: slots, c => (step M slot c).bind (run M slots)

@[simp] theorem run_nil (M : Machine ns nt branching) (c : Configuration ns nt) :
    run M [] c = some c := rfl

@[simp] theorem run_cons (M : Machine ns nt branching) (slot : Fin branching)
    (slots : List (Fin branching)) (c : Configuration ns nt) :
    run M (slot :: slots) c = (step M slot c).bind (run M slots) := rfl

theorem run_append (M : Machine ns nt branching) (pre tail : List (Fin branching))
    (c : Configuration ns nt) :
    run M (pre ++ tail) c = (run M pre c).bind (run M tail) := by
  induction pre generalizing c with
  | nil => rfl
  | cons slot pre ih =>
      simp only [List.cons_append, run_cons, ih, Option.bind_assoc]

theorem run_append_some_iff (M : Machine ns nt branching)
    (pre tail : List (Fin branching)) (c out : Configuration ns nt) :
    run M (pre ++ tail) c = some out ↔
      ∃ middle, run M pre c = some middle ∧ run M tail middle = some out := by
  cases hpre : run M pre c with
  | none => simp [run_append, hpre]
  | some middle => simp [run_append, hpre]

theorem step_accept_none (M : Machine ns nt branching) (slot : Fin branching)
    (c : Configuration ns nt) (hstate : c.state = M.accept) : step M slot c = none := by
  simp [step, hstate, M.accept_terminal]

theorem step_reject_none (M : Machine ns nt branching) (slot : Fin branching)
    (c : Configuration ns nt) (hstate : c.state = M.reject) : step M slot c = none := by
  simp [step, hstate, M.reject_terminal]

theorem run_accept_nonempty_none (M : Machine ns nt branching)
    (c : Configuration ns nt) (hstate : c.state = M.accept)
    (slots : List (Fin branching)) (hne : slots ≠ []) : run M slots c = none := by
  cases slots with
  | nil => contradiction
  | cons slot slots => simp [run_cons, step_accept_none M slot c hstate]

/-- An accepting leaf, expressed by its ordinary executed final state. -/
def Accepted (M : Machine ns nt branching) (x : List Bool)
    (slots : List (Fin branching)) : Prop :=
  (run M slots (initial M x)).map (fun c => c.state) = some M.accept

instance (M : Machine ns nt branching) (x : List Bool)
    (slots : List (Fin branching)) : Decidable (Accepted M x slots) :=
  inferInstanceAs (Decidable (_ = _))

theorem accepted_iff (M : Machine ns nt branching) (x : List Bool)
    (slots : List (Fin branching)) :
    Accepted M x slots ↔ ∃ out, run M slots (initial M x) = some out ∧
      out.state = M.accept := by
  cases hr : run M slots (initial M x) with
  | none => simp [Accepted, hr]
  | some out => simp [Accepted, hr]

/-- Every successful prefix has length at most the time bound. Dead branches
and halting branches have no further transition. This is actual tape time. -/
def RunsAtMost (M : Machine ns nt branching) (x : List Bool) (bound : ℕ) : Prop :=
  ∀ slots out, run M slots (initial M x) = some out → slots.length ≤ bound

/-- A literal configuration with no successful outgoing transition. This
includes a dead rejecting state as well as explicit accept/reject. -/
def Blocked (M : Machine ns nt branching) (c : Configuration ns nt) : Prop :=
  ∀ slot, step M slot c = none

theorem RunsAtMost.blocked_at_bound (M : Machine ns nt branching)
    (x : List Bool) (bound : ℕ) (htime : RunsAtMost M x bound)
    (slots : List (Fin branching)) (out : Configuration ns nt)
    (hlen : slots.length = bound) (hrun : run M slots (initial M x) = some out) :
    Blocked M out := by
  intro slot
  cases hnext : step M slot out with
  | none => rfl
  | some next =>
      have hfull : run M (slots ++ [slot]) (initial M x) = some next := by
        rw [run_append, hrun, Option.bind_some, run_cons, hnext,
          Option.bind_some, run_nil]
      have hbad := htime (slots ++ [slot]) next hfull
      simp only [List.length_append, List.length_singleton, hlen] at hbad
      omega

theorem runsAtMost_iff_blocked_at_bound (M : Machine ns nt branching)
    (x : List Bool) (bound : ℕ) :
    RunsAtMost M x bound ↔
      ∀ slots out, slots.length = bound →
        run M slots (initial M x) = some out → Blocked M out := by
  constructor
  · exact fun htime => RunsAtMost.blocked_at_bound M x bound htime
  · intro hblocked slots out hrun
    by_contra hlong
    have hlt : bound < slots.length := by omega
    have hlen : (slots.take bound).length = bound := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
    have hfull : run M (slots.take bound ++ slots.drop bound) (initial M x) =
        some out := by simpa using hrun
    obtain ⟨middle, hpre, htail⟩ :=
      (run_append_some_iff M _ _ _ _).mp hfull
    have hstop := hblocked (slots.take bound) middle hlen hpre
    cases hdrop : slots.drop bound with
    | nil =>
        have hzero : slots.length - bound = 0 := by
          have hl := congrArg List.length hdrop
          simpa using hl
        omega
    | cons slot tail =>
        simp [hdrop, run_cons, hstop slot] at htail

/-- Finitely many literal label sequences of all lengths at most bound. -/
abbrev WordCode (branching bound : ℕ) :=
  (n : Fin (bound + 1)) × (Fin n.val → Fin branching)

def WordCode.toList {bound : ℕ} (code : WordCode branching bound) :
    List (Fin branching) := List.ofFn code.2

@[simp] theorem WordCode.toList_length {bound : ℕ} (code : WordCode branching bound) :
    code.toList.length = code.1.val := by simp [WordCode.toList]

theorem WordCode.toList_injective {bound : ℕ} :
    Function.Injective (WordCode.toList : WordCode branching bound → List (Fin branching)) := by
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  have hnm : n = m := Fin.ext (by
    have hlen := congrArg List.length h
    simpa [WordCode.toList] using hlen)
  subst m
  congr 1
  exact List.ofFn_injective h

def WordCode.ofList {bound : ℕ} (slots : List (Fin branching))
    (hbound : slots.length ≤ bound) : WordCode branching bound :=
  ⟨⟨slots.length, by omega⟩, slots.get⟩

@[simp] theorem WordCode.toList_ofList {bound : ℕ} (slots : List (Fin branching))
    (hbound : slots.length ≤ bound) : (WordCode.ofList slots hbound).toList = slots := by
  exact List.ofFn_get slots

abbrev AcceptingCode (M : Machine ns nt branching) (x : List Bool) (bound : ℕ) :=
  {code : WordCode branching bound // Accepted M x code.toList}

/-- All literal accepting leaves, with no cutoff or chosen-image condition. -/
abbrev AcceptingLeaf (M : Machine ns nt branching) (x : List Bool) :=
  {slots : List (Fin branching) // Accepted M x slots}

def acceptingCount (M : Machine ns nt branching) (x : List Bool) (bound : ℕ) : ℕ :=
  Fintype.card (AcceptingCode M x bound)

theorem accepting_length_le (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (slots : List (Fin branching))
    (haccept : Accepted M x slots) : slots.length ≤ bound := by
  obtain ⟨out, hrun, _⟩ := (accepted_iff M x slots).mp haccept
  exact htime slots out hrun

/-- The finite code count covers every genuine accepting leaf when its
cutoff bounds actual machine time. -/
def acceptingLeavesEquiv (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    AcceptingCode M x bound ≃ AcceptingLeaf M x where
  toFun code := ⟨code.val.toList, code.property⟩
  invFun leaf := ⟨WordCode.ofList leaf.val
    (accepting_length_le M x bound htime leaf.val leaf.property), by
      simpa using leaf.property⟩
  left_inv code := by
    apply Subtype.ext
    apply WordCode.toList_injective
    simp
  right_inv leaf := by apply Subtype.ext; simp

theorem accepted_append_iff_empty (M : Machine ns nt branching) (x : List Bool)
    (pre tail : List (Fin branching)) (hpre : Accepted M x pre) :
    Accepted M x (pre ++ tail) ↔ tail = [] := by
  obtain ⟨out, hrun, hstate⟩ := (accepted_iff M x pre).mp hpre
  constructor
  · intro hfull
    by_contra hne
    have htail := run_accept_nonempty_none M out hstate tail hne
    have hnone : run M (pre ++ tail) (initial M x) = none := by
      rw [run_append, hrun, Option.bind_some, htail]
    simp [Accepted, hnone] at hfull
  · intro heq
    subst tail
    simpa using hpre

/-- Changing a cutoff above actual machine time changes neither labels nor
leaf lengths. This is not an exact-deadline normalization theorem. -/
def acceptingCodeEquiv (M : Machine ns nt branching) (x : List Bool)
    (time bound₁ bound₂ : ℕ) (htime : RunsAtMost M x time)
    (h₁ : time ≤ bound₁) (h₂ : time ≤ bound₂) :
    AcceptingCode M x bound₁ ≃ AcceptingCode M x bound₂ where
  toFun code := ⟨⟨⟨code.val.1.val, by
      have ht := accepting_length_le M x time htime code.val.toList code.property
      simp only [WordCode.toList_length] at ht
      omega⟩, code.val.2⟩, code.property⟩
  invFun code := ⟨⟨⟨code.val.1.val, by
      have ht := accepting_length_le M x time htime code.val.toList code.property
      simp only [WordCode.toList_length] at ht
      omega⟩, code.val.2⟩, code.property⟩
  left_inv code := by rcases code with ⟨⟨⟨n, hn⟩, labels⟩, ha⟩; rfl
  right_inv code := by rcases code with ⟨⟨⟨n, hn⟩, labels⟩, ha⟩; rfl

theorem acceptingCount_eq_of_bounds (M : Machine ns nt branching) (x : List Bool)
    (time bound₁ bound₂ : ℕ) (htime : RunsAtMost M x time)
    (h₁ : time ≤ bound₁) (h₂ : time ≤ bound₂) :
    acceptingCount M x bound₁ = acceptingCount M x bound₂ :=
  Fintype.card_congr (acceptingCodeEquiv M x time bound₁ bound₂ htime h₁ h₂)

/-- Standard machine counting with an exponential polynomial time bound.
The finite machine is fixed for the function. The witness contains genuine
operational time and accepting-leaf counts, not a compiler/hardness interface. -/
def SharpEXP (f : List Bool → ℕ) : Prop :=
  ∃ ns nt branching, ∃ M : Machine ns nt branching, ∃ exponent : Polynomial ℕ,
    ∀ x : List Bool,
      RunsAtMost M x (2 ^ exponent.eval x.length) ∧
      f x = acceptingCount M x (2 ^ exponent.eval x.length)

end PakFixedPolyomino.StandardNondeterministicMachine
