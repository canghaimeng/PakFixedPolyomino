import PakFixedPolyomino.ULogSourceObliviousOverflowExecution
import Mathlib.Tactic

/-! # Unrestricted completed-cycle inverse

Any successful raw history of length 4W+6 from atLeft/head 0 whose actual
final state is atLeft recovers an occupied source slot, an actual
`applyAction?` successor, the constructed cycle word, and the logical
endpoint. Boundary overflow is excluded operationally: unsafe right cannot
complete a 3W+4 suffix, and unsafe left ends in `reject`.
-/

namespace PakFixedPolyomino.ULogSourceObliviousCycleInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousInitialWindowInverse
open ULogSourceObliviousSafeSuffix
open ULogSourceObliviousCycleExecution
open ULogSourceObliviousOverflowExecution
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

theorem unrestricted_cycle_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : raw.length = 4 * windowWidth w + 6)
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ (choice : SourceChoice p q (w.cells.get w.head))
      (next : LogicalWindow nt)
      (hsafe : w.applyAction? choice.action = some next),
      raw = cycleArrows p hnt blank q w choice next hsafe exterior ∧
        out = initialWindowConfig choice.action.target next exterior := by
  have hscanLen : windowWidth w + 2 ≤ raw.length := by
    rw [hlen]
    have := windowWidth_pos w
    omega
  obtain ⟨choice, tail, hraw, htail⟩ :=
    raw_scan_prefix p hnt blank q w exterior raw out hrun hscanLen
  have htlen : tail.length = 3 * windowWidth w + 4 := by
    have he := congrArg List.length hraw
    simp only [List.length_append, sourceScanArrows_length] at he
    omega
  cases hact : w.applyAction? choice.action with
  | none =>
      have hover := (applyAction?_eq_none_iff w choice.action).mp hact
      rcases hover with ⟨hmove, hover⟩ | ⟨hmove, hhd⟩
      · exact (unsafe_right_no_suffix_run p hnt blank q choice.action w
          hmove hover exterior tail out htail htlen).elim
      · have hrej := unsafe_left_suffix_reject p hnt blank q choice.action w
          hmove hhd exterior tail out htail htlen
        obtain ⟨r, hr⟩ := hleft
        exact (reject_ne_atLeft (hrej.symm.trans hr)).elim
  | some next =>
      have ⟨hsuf, hout⟩ :=
        safe_suffix_raw_unique p hnt blank q choice.action w next hact
          exterior tail out htail htlen
      refine ⟨choice, next, hact, ?_, ?_⟩
      · rw [cycleArrows, hraw, hsuf]
      · simpa [initialWindowConfig] using hout

theorem unrestricted_cycle_inverse_safe (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : raw.length = 4 * windowWidth w + 6)
    (hleft : ∃ r, out.state = State.atLeft r) :
    ∃ choice : SourceChoice p q (w.cells.get w.head),
      (w.applyAction? choice.action).isSome = true ∧
        ∃ (next : LogicalWindow nt)
          (hsafe : w.applyAction? choice.action = some next),
          raw = cycleArrows p hnt blank q w choice next hsafe exterior ∧
            out = initialWindowConfig choice.action.target next exterior := by
  obtain ⟨choice, next, hsafe, hr, ho⟩ :=
    unrestricted_cycle_inverse p hnt blank q w exterior raw out hrun hlen hleft
  refine ⟨choice, ?_, next, hsafe, hr, ho⟩
  simp [hsafe]

def SafeSourceChoice (p : BoundedProgram ns nt) (q : Fin ns)
    (w : LogicalWindow nt) :=
  {choice : SourceChoice p q (w.cells.get w.head) //
    (w.applyAction? choice.action).isSome = true}

def RawCompletedCycle (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (exterior : Int → Phys) :=
  {raw : List (ScanArrow p hnt blank) //
    raw.length = 4 * windowWidth w + 6 ∧
      ∃ out, run (program p hnt blank) (fun _ => true) raw
          (initialWindowConfig q w exterior) = some out ∧
        ∃ r, out.state = State.atLeft r}

def safeNext (p : BoundedProgram ns nt) (q : Fin ns) (w : LogicalWindow nt)
    (s : SafeSourceChoice p q w) : LogicalWindow nt :=
  (w.applyAction? s.1.action).get (by simpa using s.2)

theorem safeNext_spec (p : BoundedProgram ns nt) (q : Fin ns)
    (w : LogicalWindow nt) (s : SafeSourceChoice p q w) :
    w.applyAction? s.1.action = some (safeNext p q w s) := by
  cases h : w.applyAction? s.1.action with
  | none =>
      have : (none : Option (LogicalWindow nt)).isSome = true := by
        simpa [h] using s.2
      simp at this
  | some next =>
      simp [safeNext, h]

def safeCycleArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (s : SafeSourceChoice p q w)
    (exterior : Int → Phys) : List (ScanArrow p hnt blank) :=
  cycleArrows p hnt blank q w s.1 (safeNext p q w s) (safeNext_spec p q w s)
    exterior

theorem cycleArrows_source_inj (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (c₁ c₂ : SourceChoice p q (w.cells.get w.head))
    (n₁ n₂ : LogicalWindow nt)
    (hs₁ : w.applyAction? c₁.action = some n₁)
    (hs₂ : w.applyAction? c₂.action = some n₂)
    (h : cycleArrows p hnt blank q w c₁ n₁ hs₁ exterior =
      cycleArrows p hnt blank q w c₂ n₂ hs₂ exterior) :
    c₁ = c₂ := by
  unfold cycleArrows at h
  have hinj := List.append_inj h (by simp [sourceScanArrows_length])
  exact sourceScanArrows_injective p hnt blank q w exterior hinj.1

noncomputable def recoverCompleted (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : RawCompletedCycle p hnt blank q w exterior) :
    SafeSourceChoice p q w :=
  let h := unrestricted_cycle_inverse_safe p hnt blank q w exterior raw.val
      (Classical.choose raw.property.2)
      (Classical.choose_spec raw.property.2).1
      raw.property.1
      (Classical.choose_spec raw.property.2).2
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem recoverCompleted_eq (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : RawCompletedCycle p hnt blank q w exterior) :
    raw.val = safeCycleArrows p hnt blank q w
      (recoverCompleted p hnt blank q w exterior raw) exterior := by
  let h := unrestricted_cycle_inverse_safe p hnt blank q w exterior raw.val
      (Classical.choose raw.property.2)
      (Classical.choose_spec raw.property.2).1
      raw.property.1
      (Classical.choose_spec raw.property.2).2
  obtain ⟨next, hsafe, heq, _⟩ := (Classical.choose_spec h).2
  have hch :
      (recoverCompleted p hnt blank q w exterior raw).1 = Classical.choose h :=
    rfl
  have hn : next = safeNext p q w
      (recoverCompleted p hnt blank q w exterior raw) := by
    have hs := safeNext_spec p q w
      (recoverCompleted p hnt blank q w exterior raw)
    simpa [hch] using Option.some.inj (hsafe.symm.trans hs)
  subst hn
  simpa [safeCycleArrows, hch] using heq

noncomputable def completedCycleEquiv (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (exterior : Int → Phys) :
    SafeSourceChoice p q w ≃ RawCompletedCycle p hnt blank q w exterior where
  toFun s :=
    ⟨safeCycleArrows p hnt blank q w s exterior,
      by simpa [safeCycleArrows] using
        cycleArrows_length p hnt blank q w s.1 (safeNext p q w s)
          (safeNext_spec p q w s) exterior,
      initialWindowConfig s.1.action.target (safeNext p q w s) exterior,
      by simpa [safeCycleArrows] using
        cycle_run p hnt blank q w s.1 (safeNext p q w s)
          (safeNext_spec p q w s) exterior,
      s.1.action.target, rfl⟩
  invFun := recoverCompleted p hnt blank q w exterior
  left_inv s := by
    apply Subtype.ext
    apply cycleArrows_source_inj p hnt blank q w exterior
      (recoverCompleted p hnt blank q w exterior
        ⟨safeCycleArrows p hnt blank q w s exterior,
          by simpa [safeCycleArrows] using
            cycleArrows_length p hnt blank q w s.1 (safeNext p q w s)
              (safeNext_spec p q w s) exterior,
          initialWindowConfig s.1.action.target (safeNext p q w s) exterior,
          by simpa [safeCycleArrows] using
            cycle_run p hnt blank q w s.1 (safeNext p q w s)
              (safeNext_spec p q w s) exterior,
          s.1.action.target, rfl⟩).1
      s.1 (safeNext p q w _) (safeNext p q w s)
      (safeNext_spec p q w _) (safeNext_spec p q w s)
    simpa [safeCycleArrows] using
      (recoverCompleted_eq p hnt blank q w exterior _).symm
  right_inv raw := by
    apply Subtype.ext
    exact (recoverCompleted_eq p hnt blank q w exterior raw).symm

end PakFixedPolyomino.ULogSourceObliviousCycleInverse
