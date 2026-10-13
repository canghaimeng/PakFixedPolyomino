import PakFixedPolyomino.ULogSourceObliviousScanExecution
import PakFixedPolyomino.FiniteOneTapeRunSlots

/-! # Raw one-step inversion of the fixed-window scanner

These inverse laws apply to the actual labelled-arrow semantics. The raw
branch domain stores an occupied arrow and its successful execution, and
does not store the selected source action. The full window-cycle converse
will additionally need the scan/update phase grammar and endpoint laws.
-/

namespace PakFixedPolyomino.ULogSourceObliviousScanInverse

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution

variable {ns nt : ℕ}

theorem branch_success_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt)
    (tape : Int → Fin 3) (head : Int)
    (arrow : Arrow (program p hnt blank)) (out : ScanConfig)
    (hstep : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
      ({ state := .branch q read, head := head, tape := tape } : ScanConfig)
      arrow = some out) :
    ∃ choice : ULogSourceOneHotMacroEquiv.SourceChoice p q read,
      arrow = branchArrow p hnt blank q read (tape head)
        choice.slot choice.action choice.occupied ∧
      out = { state := .flag q (some choice.action), head := head, tape := tape } := by
  have hsource := step_some_forces_source (program p hnt blank)
    (fun _ => true) _ out arrow hstep
  rcases hsource with ⟨hstate, hread⟩
  rcases arrow with ⟨⟨⟨source, x⟩, slot⟩, hoccupied⟩
  change State.branch q read = source at hstate
  change tape head = x at hread
  subst source
  subst x
  cases hrule : p.rule q read (slot = 1) with
  | none =>
      rw [branch_rule, hrule] at hoccupied
      simp at hoccupied
  | some a =>
      let choice : ULogSourceOneHotMacroEquiv.SourceChoice p q read :=
        ⟨slot, a, hrule⟩
      have harrow :
          (⟨((State.branch q read, tape head), slot), hoccupied⟩ :
            Arrow (program p hnt blank)) =
          branchArrow p hnt blank q read (tape head)
            choice.slot choice.action choice.occupied := by rfl
      refine ⟨choice, harrow, ?_⟩
      have hbranch := ULogSourceObliviousScanExecution.branchArrow_step
        p hnt blank q read
        ({ state := .branch q read, head := head, tape := tape } : ScanConfig)
        choice rfl
      rw [harrow, hbranch] at hstep
      exact Option.some.inj hstep.symm

/-- An arbitrary successful nonbranch arrow is the unique deterministic
slot-zero action, including its literal physical head and tape update. -/
theorem nonbranch_success_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c out : ScanConfig)
    (hs : ∀ q read, c.state ≠ State.branch q read)
    (arrow : Arrow (program p hnt blank))
    (hstep : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
      c arrow = some out) :
    arrow.1.2 = 0 ∧
      ∃ (act : Action (State ns nt) (Fin 3))
        (hact : deterministicAction p hnt blank c.state (c.tape c.head) = some act),
        arrow = deterministicArrow p hnt blank c.state (c.tape c.head) act hact ∧
        out = { state := act.target, head := moveHead act.move c.head, tape := writtenTape c act.write } := by
  have hsource := step_some_forces_source (program p hnt blank)
    (fun _ => true) c out arrow hstep
  rcases hsource with ⟨hstate, hread⟩
  rcases arrow with ⟨⟨⟨source, x⟩, slot⟩, hoccupied⟩
  change c.state = source at hstate
  change c.tape c.head = x at hread
  subst source
  subst x
  have hslot : slot = 0 := by
    fin_cases slot
    · rfl
    · exact False.elim (hoccupied
        (nonbranch_slot_one_empty p hnt blank c.state (c.tape c.head) hs))
  subst slot
  have hdet : (program p hnt blank).rule c.state (c.tape c.head) 0 =
      deterministicAction p hnt blank c.state (c.tape c.head) := by
    generalize heq : c.state = s at *
    cases s <;> try rfl
    exact False.elim (hs _ _ rfl)
  obtain ⟨act, hact⟩ : ∃ act,
      deterministicAction p hnt blank c.state (c.tape c.head) = some act := by
    cases h : deterministicAction p hnt blank c.state (c.tape c.head) with
    | none => exact False.elim (hoccupied (hdet.trans h))
    | some act => exact ⟨act, rfl⟩
  have harrow :
      (⟨((c.state, c.tape c.head), 0), hoccupied⟩ :
        Arrow (program p hnt blank)) =
      deterministicArrow p hnt blank c.state (c.tape c.head) act hact := by rfl
  refine ⟨rfl, act, hact, harrow, ?_⟩
  have hdetstep := deterministicArrow_step p hnt blank c
    c.state (c.tape c.head) act rfl rfl hact
  rw [harrow, hdetstep] at hstep
  exact Option.some.inj hstep.symm

abbrev RawBranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt)
    (tape : Int → Fin 3) (head : Int) :=
  {arrow : Arrow (program p hnt blank) // ∃ out,
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
      ({ state := .branch q read, head := head, tape := tape } : ScanConfig)
      arrow = some out}

/-- A choice-free raw branch is equivalent to one original occupied slot.
Coincident source actions remain distinct through their arrow slot labels. -/
noncomputable def sourceChoiceRawBranchEquiv
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt)
    (tape : Int → Fin 3) (head : Int) :
    ULogSourceOneHotMacroEquiv.SourceChoice p q read ≃
      RawBranch p hnt blank q read tape head where
  toFun choice := ⟨branchArrow p hnt blank q read (tape head)
    choice.slot choice.action choice.occupied,
    ⟨_, ULogSourceObliviousScanExecution.branchArrow_step p hnt blank q read
      ({ state := .branch q read, head := head, tape := tape } : ScanConfig)
      choice rfl⟩⟩
  invFun raw := Classical.choose (branch_success_inverse p hnt blank q read
    tape head raw.1 (Classical.choose raw.2) (Classical.choose_spec raw.2))
  left_inv choice := by
    apply ULogSourceOneHotMacroEquiv.SourceChoice.ext
    let raw : RawBranch p hnt blank q read tape head :=
      ⟨branchArrow p hnt blank q read (tape head)
        choice.slot choice.action choice.occupied,
        ⟨_, ULogSourceObliviousScanExecution.branchArrow_step p hnt blank q read
          ({ state := .branch q read, head := head, tape := tape } : ScanConfig)
          choice rfl⟩⟩
    have h := (Classical.choose_spec (branch_success_inverse p hnt blank q read
      tape head raw.1 (Classical.choose raw.2) (Classical.choose_spec raw.2))).1
    simpa only [raw, branchArrow] using
      (congrArg (fun a : Arrow (program p hnt blank) => a.1.2) h).symm
  right_inv raw := by
    apply Subtype.ext
    exact (Classical.choose_spec (branch_success_inverse p hnt blank q read
      tape head raw.1 (Classical.choose raw.2) (Classical.choose_spec raw.2))).1.symm

/-- Proposition form for the public kernel gateway. -/
theorem sourceChoice_rawBranch_equiv
    (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (read : Fin nt)
    (tape : Int → Fin 3) (head : Int) :
    Nonempty (ULogSourceOneHotMacroEquiv.SourceChoice p q read ≃
      RawBranch p hnt blank q read tape head) :=
  ⟨sourceChoiceRawBranchEquiv p hnt blank q read tape head⟩

end PakFixedPolyomino.ULogSourceObliviousScanInverse
