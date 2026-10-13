import PakFixedPolyomino.ULogSourceObliviousCompletedCyclePrefix

/-! # All raw fixed-length multi-cycle scanner histories

Logical traces retain each literal occupied source slot and execute its actual
window action. Their expansion is in bijection with ALL successful raw scanner
words of the corresponding length ending atLeft. The raw domain stores no
logical trace, safety, intermediate endpoint or canonical-image condition.

Window width is preserved by actual actions, hence every transition takes the
same physical time. Source halt wrappers, clock normalization, capacity slack
and arbitrary lengths remain separate obligations.
-/

namespace PakFixedPolyomino.ULogSourceObliviousCycleTraces

open FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousCycleInverse ULogSourceObliviousCompletedCyclePrefix
open ULogSourceObliviousWindowFootprint

variable {ns nt : ℕ}

def Trace (p : BoundedProgram ns nt) : ℕ → Fin ns → LogicalWindow nt → Type
  | 0, _, _ => PUnit
  | n + 1, q, w => (s : SafeSourceChoice p q w) ×
      Trace p n s.1.action.target (safeNext p q w s)

def endpoint (p : BoundedProgram ns nt) :
    (n : ℕ) → (q : Fin ns) → (w : LogicalWindow nt) →
      Trace p n q w → Fin ns × LogicalWindow nt
  | 0, q, w, _ => (q, w)
  | n + 1, q, w, ⟨s, tail⟩ => endpoint p n s.1.action.target (safeNext p q w s) tail

def arrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) : (n : ℕ) → (q : Fin ns) → (w : LogicalWindow nt) →
      Trace p n q w → List (ScanArrow p hnt blank)
  | 0, _, _, _ => []
  | n + 1, q, w, ⟨s, tail⟩ => safeCycleArrows p hnt blank q w s exterior ++
      arrows p hnt blank exterior n s.1.action.target (safeNext p q w s) tail

theorem safeNext_width (p : BoundedProgram ns nt) (q : Fin ns)
    (w : LogicalWindow nt) (s : SafeSourceChoice p q w) :
    windowWidth (safeNext p q w s) = windowWidth w := by
  have hl := LogicalWindow.applyAction_preserves_width w (safeNext p q w s)
    s.1.action (safeNext_spec p q w s)
  simp only [windowWidth, LogicalWindow.encode_length, hl]

@[simp] theorem safeCycle_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (q : Fin ns)
    (w : LogicalWindow nt) (s : SafeSourceChoice p q w) :
    (safeCycleArrows p hnt blank q w s exterior).length = 4 * windowWidth w + 6 := by
  simp [safeCycleArrows]

theorem arrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (t : Trace p n q w) :
    (arrows p hnt blank exterior n q w t).length = n * (4 * windowWidth w + 6) := by
  induction n generalizing q w with
  | zero => simp [arrows]
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      simp only [arrows, List.length_append, safeCycle_length, ih, safeNext_width]
      rw [Nat.succ_mul n (4 * windowWidth w + 6)]
      omega

theorem endpoint_width (p : BoundedProgram ns nt) (n : ℕ)
    (q : Fin ns) (w : LogicalWindow nt) (t : Trace p n q w) :
    windowWidth (endpoint p n q w t).2 = windowWidth w := by
  induction n generalizing q w with
  | zero => rfl
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      exact (ih s.1.action.target (safeNext p q w s) tail).trans (safeNext_width p q w s)

theorem arrows_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (t : Trace p n q w) :
    run (program p hnt blank) (fun _ => true) (arrows p hnt blank exterior n q w t)
      (initialWindowConfig q w exterior) =
      some (initialWindowConfig (endpoint p n q w t).1 (endpoint p n q w t).2 exterior) := by
  induction n generalizing q w with
  | zero => rfl
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      rw [arrows, run_append p hnt blank]
      have hcycle := cycle_run p hnt blank q w s.1 (safeNext p q w s)
        (safeNext_spec p q w s) exterior
      change run (program p hnt blank) (fun _ => true)
        (safeCycleArrows p hnt blank q w s exterior) (initialWindowConfig q w exterior) =
        some (initialWindowConfig s.1.action.target (safeNext p q w s) exterior) at hcycle
      rw [hcycle, Option.bind_some]
      exact ih s.1.action.target (safeNext p q w s) tail

theorem arrows_footprint (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (t : Trace p n q w) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (arrows p hnt blank exterior n q w t) (initialWindowConfig q w exterior) := by
  induction n generalizing q w with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by simpa [arrows] using hk
      subst k
      exact ⟨initialWindowConfig q w exterior, rfl, by rfl,
        by change 0 ≤ (windowWidth w : Int) + 1; omega⟩
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      apply prefixInInterval_append p hnt blank _ _ _ _ _
        (initialWindowConfig s.1.action.target (safeNext p q w s) exterior)
      · exact cycle_footprint p hnt blank q w s.1 (safeNext p q w s)
          (safeNext_spec p q w s) exterior
      · exact cycle_run p hnt blank q w s.1 (safeNext p q w s)
          (safeNext_spec p q w s) exterior
      · simpa only [safeNext_width] using
          ih s.1.action.target (safeNext p q w s) tail

theorem arrows_injective (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    Function.Injective (arrows p hnt blank exterior n q w) := by
  induction n generalizing q w with
  | zero =>
      intro a b _
      change PUnit at a b
      exact Subsingleton.elim a b
  | succ n ih =>
      rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ heq
      change safeCycleArrows p hnt blank q w s₁ exterior ++
        arrows p hnt blank exterior n s₁.1.action.target (safeNext p q w s₁) t₁ =
        safeCycleArrows p hnt blank q w s₂ exterior ++
        arrows p hnt blank exterior n s₂.1.action.target (safeNext p q w s₂) t₂ at heq
      obtain ⟨hfirst, htail⟩ := List.append_inj heq (by simp)
      have hs : s₁ = s₂ := Subtype.ext (cycleArrows_source_inj p hnt blank q w exterior
        s₁.1 s₂.1 (safeNext p q w s₁) (safeNext p q w s₂)
        (safeNext_spec p q w s₁) (safeNext_spec p q w s₂) hfirst)
      subst s₂
      have ht := ih s₁.1.action.target (safeNext p q w s₁) htail
      subst t₂
      rfl

/-- Arbitrary raw execution is reconstructed without supplying a trace or
any intermediate endpoint. The zero-cycle case includes the empty history. -/
theorem raw_trace_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : raw.length = n * (4 * windowWidth w + 6))
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ t : Trace p n q w,
      raw = arrows p hnt blank exterior n q w t ∧
        out = initialWindowConfig (endpoint p n q w t).1 (endpoint p n q w t).2 exterior := by
  induction n generalizing q w raw out with
  | zero =>
      have hnil : raw = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst raw
      exact ⟨PUnit.unit, rfl, (Option.some.inj hrun).symm⟩
  | succ n ih =>
      have hfirst : 4 * windowWidth w + 6 ≤ raw.length := by
        rw [hlen, Nat.succ_mul n (4 * windowWidth w + 6)]
        omega
      obtain ⟨choice, next, hsafe, tail, hraw, htail⟩ :=
        raw_completed_cycle_prefix p hnt blank q w exterior raw out hrun hfirst hleft
      cases hs : (w.applyAction? choice.action).isSome with
      | false => simp [hsafe] at hs
      | true =>
          let s : SafeSourceChoice p q w := ⟨choice, hs⟩
          have hn : next = safeNext p q w s :=
            Option.some.inj (hsafe.symm.trans (safeNext_spec p q w s))
          subst next
          have htlen : tail.length = n * (4 * windowWidth (safeNext p q w s) + 6) := by
            have hh := congrArg List.length hraw
            simp only [List.length_append, cycleArrows_length] at hh
            rw [safeNext_width]
            rw [Nat.succ_mul n (4 * windowWidth w + 6)] at hlen
            omega
          obtain ⟨t, hword, hout⟩ := ih s.1.action.target (safeNext p q w s) tail out
            htail htlen hleft
          refine ⟨⟨s, t⟩, ?_, hout⟩
          simpa only [arrows, safeCycleArrows, s, hword] using hraw

def RawCycles (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :=
  {raw : List (ScanArrow p hnt blank) //
    raw.length = n * (4 * windowWidth w + 6) ∧
      ∃ out, run (program p hnt blank) (fun _ => true) raw
        (initialWindowConfig q w exterior) = some out ∧ ∃ r, out.state = State.atLeft r}

def toRaw (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (t : Trace p n q w) : RawCycles p hnt blank exterior n q w :=
  ⟨arrows p hnt blank exterior n q w t, arrows_length p hnt blank exterior n q w t,
    initialWindowConfig (endpoint p n q w t).1 (endpoint p n q w t).2 exterior,
    arrows_run p hnt blank exterior n q w t, (endpoint p n q w t).1, rfl⟩

noncomputable def traceEquiv (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    Trace p n q w ≃ RawCycles p hnt blank exterior n q w :=
  Equiv.ofBijective (toRaw p hnt blank exterior n q w) (by
    constructor
    · intro t₁ t₂ heq
      exact arrows_injective p hnt blank exterior n q w (congrArg Subtype.val heq)
    · intro raw
      obtain ⟨out, hrun, hleft⟩ := raw.property.2
      obtain ⟨t, hword, _⟩ := raw_trace_inverse p hnt blank exterior n q w raw.val out
        hrun raw.property.1 hleft
      exact ⟨t, Subtype.ext hword.symm⟩)

end PakFixedPolyomino.ULogSourceObliviousCycleTraces
