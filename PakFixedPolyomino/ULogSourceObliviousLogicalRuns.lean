import PakFixedPolyomino.ULogSourceObliviousCycleTraces
import PakFixedPolyomino.StandardNondeterministicMachine

/-! # Literal logical runs and all-raw scanner multi-cycle counts

Each logical transition reads its actual head cell, uses the literal Fin2
slot of the finite program, writes and moves by applyAction?. Successful
slot words are equivalent to the logical traces, hence to ALL completed raw
scanner histories of the matching physical length. No trace/image predicate
is imposed on either raw domain.

This is finite-window semantics. A physical source compiler must still prove
that every ordinary source run fits the materialized window, and construct
source halt/clock/loading and capacity-count invariants.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLogicalRuns

open ULogCompiler ULogSourceObliviousWindow
open ULogSourceObliviousCycleTraces ULogSourceObliviousCycleInverse
open ULogSourceOneHotMacroEquiv (SourceChoice)
open ULogSourceObliviousUpdateExecution

variable {ns nt : ℕ}

abbrev Configuration (ns nt : ℕ) := Fin ns × LogicalWindow nt

def step (p : BoundedProgram ns nt) (slot : Fin 2)
    (c : Configuration ns nt) : Option (Configuration ns nt) :=
  (p.rule c.1 (c.2.cells.get c.2.head) (slot = 1)).bind fun a =>
    (c.2.applyAction? a).map fun next => (a.target, next)

def run (p : BoundedProgram ns nt) :
    List (Fin 2) → Configuration ns nt → Option (Configuration ns nt)
  | [], c => some c
  | slot :: slots, c => (step p slot c).bind (run p slots)

def slots (p : BoundedProgram ns nt) :
    (n : ℕ) → (q : Fin ns) → (w : LogicalWindow nt) → Trace p n q w → List (Fin 2)
  | 0, _, _, _ => []
  | n + 1, q, w, ⟨s, tail⟩ => s.1.slot ::
      slots p n s.1.action.target (safeNext p q w s) tail

@[simp] theorem slots_length (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) (t : Trace p n q w) :
    (slots p n q w t).length = n := by
  induction n generalizing q w with
  | zero => rfl
  | succ n ih => rcases t with ⟨s, tail⟩; simp only [slots, List.length_cons, ih]

theorem step_choice (p : BoundedProgram ns nt) (q : Fin ns) (w : LogicalWindow nt)
    (s : SafeSourceChoice p q w) :
    step p s.1.slot (q, w) = some (s.1.action.target, safeNext p q w s) := by
  simp only [step, s.1.occupied, Option.bind_some, safeNext_spec, Option.map_some]

theorem slots_run (p : BoundedProgram ns nt) (n : ℕ) (q : Fin ns)
    (w : LogicalWindow nt) (t : Trace p n q w) :
    run p (slots p n q w t) (q, w) = some (endpoint p n q w t) := by
  induction n generalizing q w with
  | zero => rfl
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      simp only [slots, run, step_choice, Option.bind_some, endpoint]
      exact ih s.1.action.target (safeNext p q w s) tail

theorem slots_injective (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) : Function.Injective (slots p n q w) := by
  induction n generalizing q w with
  | zero =>
      intro a b _
      change PUnit at a b
      exact Subsingleton.elim a b
  | succ n ih =>
      rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ heq
      have he : s₁.1.slot = s₂.1.slot ∧
          slots p n s₁.1.action.target (safeNext p q w s₁) t₁ =
          slots p n s₂.1.action.target (safeNext p q w s₂) t₂ :=
        List.cons.inj heq
      have hs : s₁ = s₂ := Subtype.ext (SourceChoice.ext he.1)
      subst s₂
      have ht := ih s₁.1.action.target (safeNext p q w s₁) he.2
      subst t₂
      rfl

theorem logical_trace_inverse (p : BoundedProgram ns nt) (word : List (Fin 2))
    (q : Fin ns) (w : LogicalWindow nt) (out : Configuration ns nt)
    (hrun : run p word (q, w) = some out) :
    ∃ t : Trace p word.length q w, word = slots p word.length q w t ∧
      out = endpoint p word.length q w t := by
  induction word generalizing q w with
  | nil => exact ⟨PUnit.unit, rfl, (Option.some.inj hrun).symm⟩
  | cons slot word ih =>
      cases hrule : p.rule q (w.cells.get w.head) (slot = 1) with
      | none =>
          simp only [run, step, hrule, Option.bind_none] at hrun
          cases hrun
      | some a =>
          cases hact : w.applyAction? a with
          | none =>
              simp only [run, step, hrule, Option.bind_some, hact,
                Option.map_none, Option.bind_none] at hrun
              cases hrun
          | some next =>
              have htail : run p word (a.target, next) = some out := by
                simpa only [run, step, hrule, Option.bind_some, hact,
                  Option.map_some] using hrun
              let choice : SourceChoice p q (w.cells.get w.head) := ⟨slot, a, hrule⟩
              cases hs : (w.applyAction? a).isSome with
              | false => simp [hact] at hs
              | true =>
                  let s : SafeSourceChoice p q w := ⟨choice, hs⟩
                  have hn : next = safeNext p q w s :=
                    Option.some.inj (hact.symm.trans (safeNext_spec p q w s))
                  subst next
                  obtain ⟨t, hslots, hout⟩ :=
                    ih a.target (safeNext p q w s) htail
                  exact ⟨⟨s, t⟩, by
                    simp only [List.length_cons, slots, s, choice, hslots], hout⟩

def LogicalWords (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) :=
  {word : List (Fin 2) // word.length = n ∧ ∃ out, run p word (q, w) = some out}

def toLogical (p : BoundedProgram ns nt) (n : ℕ) (q : Fin ns)
    (w : LogicalWindow nt) (t : Trace p n q w) : LogicalWords p n q w :=
  ⟨slots p n q w t, slots_length p n q w t, endpoint p n q w t, slots_run p n q w t⟩

noncomputable def logicalEquiv (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) : Trace p n q w ≃ LogicalWords p n q w :=
  Equiv.ofBijective (toLogical p n q w) (by
    constructor
    · intro a b heq
      exact slots_injective p n q w (congrArg Subtype.val heq)
    · rintro ⟨word, hlen, out, hrun⟩
      subst n
      obtain ⟨t, hword, _⟩ := logical_trace_inverse p word q w out hrun
      exact ⟨t, Subtype.ext hword.symm⟩)

noncomputable def logicalRawEquiv (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (exterior : Int → Phys) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) :
    LogicalWords p n q w ≃ RawCycles p hnt blank exterior n q w :=
  (logicalEquiv p n q w).symm.trans (traceEquiv p hnt blank exterior n q w)

instance logicalWords_finite (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) : Finite (LogicalWords p n q w) := by
  apply Finite.of_injective (fun word : LogicalWords p n q w =>
    StandardNondeterministicMachine.WordCode.ofList (bound := n) word.1
      (Nat.le_of_eq word.2.1))
  intro a b heq
  have hlist := congrArg StandardNondeterministicMachine.WordCode.toList heq
  apply Subtype.ext
  simpa using hlist

instance trace_finite (p : BoundedProgram ns nt) (n : ℕ) (q : Fin ns)
    (w : LogicalWindow nt) : Finite (Trace p n q w) :=
  Finite.of_injective (toLogical p n q w) (fun a b h =>
    slots_injective p n q w (congrArg Subtype.val h))

instance rawCycles_finite (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    Finite (RawCycles p hnt blank exterior n q w) :=
  Finite.of_injective (traceEquiv p hnt blank exterior n q w).symm
    (traceEquiv p hnt blank exterior n q w).symm.injective

/-- The full raw physical count equals the full successful logical label-word
count at every finite horizon. There is no canonical-image count premise. -/
theorem raw_count_eq_logical_count (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q : Fin ns)
    (w : LogicalWindow nt) :
    Nat.card (RawCycles p hnt blank exterior n q w) = Nat.card (LogicalWords p n q w) :=
  Nat.card_congr (logicalRawEquiv p hnt blank exterior n q w).symm

end PakFixedPolyomino.ULogSourceObliviousLogicalRuns
