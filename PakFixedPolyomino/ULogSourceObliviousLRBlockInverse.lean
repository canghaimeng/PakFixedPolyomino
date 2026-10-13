import PakFixedPolyomino.ULogSourceObliviousLRBlockExecution
import PakFixedPolyomino.ULogSourceObliviousRunPrefix

/-! # Arbitrary successful raw runs of a literal skipLR block

The prefix states are derived from the engineer's actual run, rather than
stored as a condition on the compared raw history. No image restriction or
source-choice certificate is imposed on the raw list.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLRBlockInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix
open ULogSourceObliviousLRBlockExecution

variable {ns nt : ℕ}

/-- A successful operational list whose proper-prefix states are nonbranch
is a locally forced scanner prefix. -/
theorem nonbranchPrefix_of_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (as : List (ScanArrow p hnt blank)) (c out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) as c = some out)
    (hstates : ∀ k < as.length, ∀ mid : ScanCfg ns nt,
      run (program p hnt blank) (fun _ => true) (as.take k) c = some mid →
      ∀ q read, mid.state ≠ State.branch q read) :
    NonbranchPrefix p hnt blank as c := by
  induction as generalizing c with
  | nil => trivial
  | cons a as ih =>
      cases hstep : FiniteOneTapeSemantics.step
          (program p hnt blank) (fun _ => true) c a with
      | none => simp [run, hstep] at hrun
      | some d =>
          refine ⟨hstates 0 (by simp) c rfl, d, hstep, ?_⟩
          apply ih d (by simpa [run, hstep] using hrun)
          intro k hk mid hmid
          apply hstates (k + 1) (by simpa using hk) mid
          simpa [List.take, run, hstep] using hmid

theorem skipLR_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (c : ScanCfg ns nt) (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    NonbranchPrefix p hnt blank
      (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid) c := by
  apply nonbranchPrefix_of_run p hnt blank _ c _
    (skipLR_run p hnt blank a armed rewrite bits hbits hvalid c hstate head hhead hread)
  intro k hk mid hmid q read
  have hkn : k < nt := by simpa using hk
  have hcanonical := skipLR_take_lt p hnt blank a armed rewrite bits hbits hvalid
    c hstate head hhead hread k hkn
  have heq : mid = skipLRMid a armed rewrite bits c head k hkn :=
    Option.some.inj (hmid.symm.trans hcanonical)
  simp [heq, skipLRMid]

/-- A raw successful run of the exact block length is the literal occupied
arrow list and has the actual full tape/head/control endpoint. -/
theorem skipLR_raw_unique
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (c : ScanCfg ns nt) (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlength : raw.length = nt) :
    raw = skipLRArrows p hnt blank a armed rewrite bits hbits hvalid ∧
      out = { state := .updateLRFlag a armed
              head := head + nt
              tape := writeBlock c.tape head (outputBits a rewrite bits) } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (skipLR_nonbranchPrefix p hnt blank a armed rewrite bits hbits hvalid
      c hstate head hhead hread)
  obtain ⟨heq, hout⟩ := forcedPrefix_unique_successful_run
    (program p hnt blank) (fun _ => true) _ raw c out hforced hrun
    (by simpa using hlength.symm)
  refine ⟨heq, ?_⟩
  exact Option.some.inj (hout.symm.trans
    (skipLR_run p hnt blank a armed rewrite bits hbits hvalid c hstate head hhead hread))

/-- Every sufficiently long successful raw run begins with this same
literal block at its actual operational endpoint. -/
theorem skipLR_raw_prefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (c : ScanCfg ns nt) (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlength : nt ≤ raw.length) :
    ∃ tail,
      raw = skipLRArrows p hnt blank a armed rewrite bits hbits hvalid ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        { state := .updateLRFlag a armed
          head := head + nt
          tape := writeBlock c.tape head (outputBits a rewrite bits) } = some out := by
  obtain ⟨tail, mid, heq, hpre, htail⟩ :=
    nonbranchPrefix_split_successful_run p hnt blank _ raw c out
      (skipLR_nonbranchPrefix p hnt blank a armed rewrite bits hbits hvalid
        c hstate head hhead hread) hrun (by simpa using hlength)
  have heqmid := Option.some.inj (hpre.symm.trans
    (skipLR_run p hnt blank a armed rewrite bits hbits hvalid c hstate head hhead hread))
  exact ⟨tail, heq, heqmid ▸ htail⟩

end PakFixedPolyomino.ULogSourceObliviousLRBlockInverse
