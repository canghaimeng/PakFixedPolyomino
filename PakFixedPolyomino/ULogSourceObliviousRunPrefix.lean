import PakFixedPolyomino.FiniteOneTapeRunPrefix
import PakFixedPolyomino.ULogSourceObliviousScanInverse

/-! # Local deterministic-phase converse for the oblivious scanner -/

namespace PakFixedPolyomino.ULogSourceObliviousRunPrefix

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousScanInverse

variable {ns nt : ℕ}

theorem nonbranch_success_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c d e : ScanConfig)
    (hs : ∀ q read, c.state ≠ State.branch q read)
    (a b : Arrow (program p hnt blank))
    (ha : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c a = some d)
    (hb : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c b = some e) :
    a = b := by
  have hslotA := (nonbranch_success_inverse p hnt blank c d hs a ha).1
  have hslotB := (nonbranch_success_inverse p hnt blank c e hs b hb).1
  exact successful_arrows_eq_of_slot_eq (program p hnt blank) (fun _ => true)
    c d e a b ha hb (hslotA.trans hslotB.symm)

def NonbranchPrefix (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) :
    List (Arrow (program p hnt blank)) → ScanConfig (ns := ns) (nt := nt) → Prop
  | [], _ => True
  | a :: as, c =>
      (∀ q read, c.state ≠ State.branch q read) ∧
      ∃ d, FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c a = some d ∧
        NonbranchPrefix p hnt blank as d

theorem nonbranchPrefix_forced (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (as : List (Arrow (program p hnt blank))) (c : ScanConfig)
    (h : NonbranchPrefix p hnt blank as c) :
    ForcedPrefix (program p hnt blank) (fun _ => true) as c := by
  induction as generalizing c with
  | nil => trivial
  | cons a as ih =>
      rcases h with ⟨hs, d, hstep, htail⟩
      refine ⟨d, hstep, ?_, ih d htail⟩
      intro b e hb
      exact nonbranch_success_unique p hnt blank c e d hs b a hb hstep

/-- Deterministic scanner phases add no raw-run multiplicity. This is a
pre converse, and does not assume the raw run belongs to a forward image. -/
theorem nonbranchPrefix_split_successful_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (pre raw : List (Arrow (program p hnt blank))) (c out : ScanConfig)
    (hprefix : NonbranchPrefix p hnt blank pre c)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlength : pre.length ≤ raw.length) :
    ∃ tail boundary,
      raw = pre ++ tail ∧
      run (program p hnt blank) (fun _ => true) pre c = some boundary ∧
      run (program p hnt blank) (fun _ => true) tail boundary = some out :=
  forcedPrefix_split_successful_run (program p hnt blank) (fun _ => true)
    pre raw c out (nonbranchPrefix_forced p hnt blank pre c hprefix) hrun hlength

end PakFixedPolyomino.ULogSourceObliviousRunPrefix
