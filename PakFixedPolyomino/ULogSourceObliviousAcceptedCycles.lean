import PakFixedPolyomino.ULogSourceObliviousLogicalRuns

/-! # Exact accepting counts for all raw completed scanner cycles

Acceptance checks the actual endpoint state. The physical domain includes
every raw successful word of the displayed whole-cycle length ending at the
chosen atLeft state; it contains no image or intermediate-safety condition.
The scanner still needs a genuine halting wrapper before this endpoint count
can be used as a standard accepting-leaf count.
-/

namespace PakFixedPolyomino.ULogSourceObliviousAcceptedCycles

open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousUpdateExecution
open ULogSourceObliviousCycleTraces ULogSourceObliviousLogicalRuns

variable {ns nt : ℕ}

theorem logicalRawEquiv_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q : Fin ns)
    (w : LogicalWindow nt) (word : LogicalWords p n q w)
    (out : Configuration ns nt) (hrun : run p word.1 (q, w) = some out) :
    FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
      (logicalRawEquiv p hnt blank exterior n q w word).1
      (initialWindowConfig q w exterior) =
        some (initialWindowConfig out.1 out.2 exterior) := by
  let t := (logicalEquiv p n q w).symm word
  have hword : slots p n q w t = word.1 :=
    congrArg Subtype.val ((logicalEquiv p n q w).apply_symm_apply word)
  have hout : endpoint p n q w t = out := by
    exact Option.some.inj ((slots_run p n q w t).symm.trans (hword ▸ hrun))
  change FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
    (arrows p hnt blank exterior n q w t) (initialWindowConfig q w exterior) = _
  rw [arrows_run, hout]

def LogicalAccepts (p : BoundedProgram ns nt) (n : ℕ) (q accept : Fin ns)
    (w : LogicalWindow nt) (word : LogicalWords p n q w) : Prop :=
  ∃ out, run p word.1 (q, w) = some out ∧ out.1 = accept

def RawAccepts (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns) (w : LogicalWindow nt)
    (raw : RawCycles p hnt blank exterior n q w) : Prop :=
  ∃ out, FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) raw.1
    (initialWindowConfig q w exterior) = some out ∧ out.state = State.atLeft accept

theorem acceptance_iff (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns)
    (w : LogicalWindow nt) (word : LogicalWords p n q w) :
    LogicalAccepts p n q accept w word ↔
      RawAccepts p hnt blank exterior n q accept w
        (logicalRawEquiv p hnt blank exterior n q w word) := by
  obtain ⟨logicalOut, hlogical⟩ := word.2.2
  have hphysical := logicalRawEquiv_run p hnt blank exterior n q w word
    logicalOut hlogical
  constructor
  · rintro ⟨out, hrun, haccept⟩
    have heq : logicalOut = out := Option.some.inj (hlogical.symm.trans hrun)
    subst out
    exact ⟨initialWindowConfig logicalOut.1 logicalOut.2 exterior, hphysical,
      by change State.atLeft logicalOut.1 = State.atLeft accept; rw [haccept]⟩
  · rintro ⟨out, hrun, haccept⟩
    have heq : initialWindowConfig logicalOut.1 logicalOut.2 exterior = out :=
      Option.some.inj (hphysical.symm.trans hrun)
    subst out
    exact ⟨logicalOut, hlogical, State.atLeft.inj haccept⟩

abbrev AcceptedLogicalWords (p : BoundedProgram ns nt) (n : ℕ)
    (q accept : Fin ns) (w : LogicalWindow nt) :=
  {word : LogicalWords p n q w // LogicalAccepts p n q accept w word}

abbrev AcceptedRawCycles (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns)
    (w : LogicalWindow nt) :=
  {raw : RawCycles p hnt blank exterior n q w //
    RawAccepts p hnt blank exterior n q accept w raw}

noncomputable def acceptedEquiv (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns)
    (w : LogicalWindow nt) :
    AcceptedLogicalWords p n q accept w ≃
      AcceptedRawCycles p hnt blank exterior n q accept w :=
  (logicalRawEquiv p hnt blank exterior n q w).subtypeEquiv
    (acceptance_iff p hnt blank exterior n q accept w)

theorem accepting_count_eq (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns)
    (w : LogicalWindow nt) :
    Nat.card (AcceptedRawCycles p hnt blank exterior n q accept w) =
      Nat.card (AcceptedLogicalWords p n q accept w) :=
  Nat.card_congr (acceptedEquiv p hnt blank exterior n q accept w).symm

end PakFixedPolyomino.ULogSourceObliviousAcceptedCycles
