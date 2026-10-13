import PakFixedPolyomino.ULogSourceObliviousLRBlockInverse
import PakFixedPolyomino.ULogSourceObliviousReturnInverse

/-! # Literal flag step followed by one LR symbol block

The only flag premise is the value of the explicit finite `updateLR`
function. No later tape occupancy or tape-update identity is assumed.
Whole-window induction must derive this value from its unique head flag.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLRCellExecution

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix
open ULogSourceObliviousLRBlockExecution ULogSourceObliviousLRBlockInverse
open ULogSourceObliviousReturnInverse (nonbranchPrefix_append)

variable {ns nt : ℕ}

theorem updateLRFlagInteriorArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed'))
    (c : ScanCfg ns nt) (hstate : c.state = .updateLRFlag a armed)
    (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c
      (updateLRFlagInteriorArrow p hnt blank a armed x hne write armed' hupd) =
      some { state := .skipLR a armed' (x = ULogSourceOneHotReader.one) ⟨0, hnt⟩
             head := c.head + 1
             tape := Function.update c.tape c.head write } := by
  have hact : deterministicAction p hnt blank (.updateLRFlag a armed) x =
      some ⟨write, .skipLR a armed' (x = ULogSourceOneHotReader.one) ⟨0, hnt⟩,
        .right⟩ := by
    simp [deterministicAction, hne, hupd]
  have hstep := deterministicArrow_step p hnt blank c (.updateLRFlag a armed) x
    ⟨write, .skipLR a armed' (x = ULogSourceOneHotReader.one) ⟨0, hnt⟩, .right⟩
    hstate hread hact
  simpa [updateLRFlagInteriorArrow, writtenTape, moveHead] using hstep

def cellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true) : List (ScanArrow p hnt blank) :=
  updateLRFlagInteriorArrow p hnt blank a armed x hne write armed' hupd ::
    skipLRArrows p hnt blank a armed' (x = ULogSourceOneHotReader.one) bits hbits hvalid

@[simp] theorem cellArrows_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true) :
    (cellArrows p hnt blank a armed x write armed' hne hupd bits hbits hvalid).length =
      nt + 1 := by simp [cellArrows]

def cellMiddle (a : BoundedAction ns nt) (hnt : 0 < nt)
    (x write : Phys) (armed' : Bool) (c : ScanCfg ns nt) : ScanCfg ns nt :=
  { state := .skipLR a armed' (x = ULogSourceOneHotReader.one) ⟨0, hnt⟩
    head := c.head + 1
    tape := Function.update c.tape c.head write }

theorem cellMiddle_read
    (a : BoundedAction ns nt) (hnt : 0 < nt)
    (x write : Phys) (armed' : Bool) (c : ScanCfg ns nt)
    (bits : List Phys) (hbits : bits.length = nt)
    (hread : ∀ i : Fin nt, c.tape (c.head + 1 + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    ∀ i : Fin nt, (cellMiddle a hnt x write armed' c).tape
      (c.head + 1 + (i.val : Int)) = bits.get ⟨i.val, by omega⟩ := by
  intro i
  have hne : c.head + 1 + (i.val : Int) ≠ c.head := by omega
  simpa [cellMiddle, Function.update, hne] using hread i

theorem cell_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (c : ScanCfg ns nt) (hstate : c.state = .updateLRFlag a armed)
    (hflag : c.tape c.head = x)
    (hread : ∀ i : Fin nt, c.tape (c.head + 1 + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    run (program p hnt blank) (fun _ => true)
      (cellArrows p hnt blank a armed x write armed' hne hupd bits hbits hvalid) c =
      some { state := .updateLRFlag a armed'
             head := c.head + 1 + nt
             tape := writeBlock (Function.update c.tape c.head write) (c.head + 1)
               (outputBits a (x = ULogSourceOneHotReader.one) bits) } := by
  have hstep := updateLRFlagInteriorArrow_step p hnt blank a armed x write armed'
    hne hupd c hstate hflag
  rw [cellArrows, run_cons, hstep, Option.bind_some]
  exact skipLR_run p hnt blank a armed' (x = ULogSourceOneHotReader.one) bits hbits
    hvalid (cellMiddle a hnt x write armed' c) rfl (c.head + 1) rfl
    (cellMiddle_read a hnt x write armed' c bits hbits hread)

theorem cell_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (c : ScanCfg ns nt) (hstate : c.state = .updateLRFlag a armed)
    (hflag : c.tape c.head = x)
    (hread : ∀ i : Fin nt, c.tape (c.head + 1 + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    NonbranchPrefix p hnt blank
      (cellArrows p hnt blank a armed x write armed' hne hupd bits hbits hvalid) c := by
  refine ⟨?_, cellMiddle a hnt x write armed' c,
    updateLRFlagInteriorArrow_step p hnt blank a armed x write armed' hne hupd c
      hstate hflag, ?_⟩
  · intro q read
    simp [hstate]
  · exact skipLR_nonbranchPrefix p hnt blank a armed'
      (x = ULogSourceOneHotReader.one) bits hbits hvalid
      (cellMiddle a hnt x write armed' c) rfl (c.head + 1) rfl
      (cellMiddle_read a hnt x write armed' c bits hbits hread)

end PakFixedPolyomino.ULogSourceObliviousLRCellExecution
