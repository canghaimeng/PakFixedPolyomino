import PakFixedPolyomino.ULogSourceObliviousRLBlockInverse
import PakFixedPolyomino.ULogSourceObliviousReturnInverse

/-! # Literal reverse symbol block followed by its flag step

All symbol bits are physically traversed without modifying the tape. The
displayed finite updateRL value then supplies the flag write. A complete
window proof must derive that value from its single marked head.
-/

namespace PakFixedPolyomino.ULogSourceObliviousRLCellExecution

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix
open ULogSourceObliviousRLBlockExecution ULogSourceObliviousRLBlockInverse
open ULogSourceObliviousReturnInverse (nonbranchPrefix_append)

variable {ns nt : ℕ}

theorem updateRLFlagArrow_step
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed'))
    (c : ScanCfg ns nt) (hstate : c.state = .updateRLFlag a armed)
    (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c
      (updateRLFlagArrow p hnt blank a armed x write armed' hupd) =
      some { state := .skipRL a armed' ⟨nt - 1, by omega⟩
             head := c.head - 1
             tape := Function.update c.tape c.head write } := by
  have hact : deterministicAction p hnt blank (.updateRLFlag a armed) x =
      some ⟨write, .skipRL a armed' ⟨nt - 1, by omega⟩, .left⟩ := by
    simp [deterministicAction, hupd]
  have hstep := deterministicArrow_step p hnt blank c (.updateRLFlag a armed) x
    ⟨write, .skipRL a armed' ⟨nt - 1, by omega⟩, .left⟩ hstate hread hact
  simpa [updateRLFlagArrow, writtenTape, moveHead] using hstep

def cellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (hneBits : ∀ y ∈ bits, y ≠ ULogSourceOneHotReader.blank) :
    List (ScanArrow p hnt blank) :=
  skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits ++
    [updateRLFlagArrow p hnt blank a armed x write armed' hupd]

@[simp] theorem cellArrows_length
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (hneBits : ∀ y ∈ bits, y ≠ ULogSourceOneHotReader.blank) :
    (cellArrows p hnt blank a armed x write armed' hupd bits hbits hvalid hneBits).length =
      nt + 1 := by simp [cellArrows]

def cellMiddle (a : BoundedAction ns nt) (armed : Bool)
    (c : ScanCfg ns nt) (base : Int) : ScanCfg ns nt :=
  { state := .updateRLFlag a armed, head := base - 1, tape := c.tape }

theorem cell_run
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (hneBits : ∀ y ∈ bits, y ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (hflag : c.tape (base - 1) = x) :
    run (program p hnt blank) (fun _ => true)
      (cellArrows p hnt blank a armed x write armed' hupd bits hbits hvalid hneBits) c =
      some { state := .skipRL a armed' ⟨nt - 1, by omega⟩
             head := base - 2
             tape := Function.update c.tape (base - 1) write } := by
  rw [cellArrows, run_append p hnt blank,
    skipRL_run p hnt blank a armed bits hbits hvalid hneBits c hstate base hhead hread,
    Option.bind_some, run_cons]
  have hstep := updateRLFlagArrow_step p hnt blank a armed x write armed' hupd
    (cellMiddle a armed c base) rfl hflag
  simp only [cellMiddle] at hstep
  rw [hstep, Option.bind_some, run_nil]
  congr 1
  apply cfg_ext
  · rfl
  · change base - 1 - 1 = base - 2
    omega
  · rfl

theorem cell_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed'))
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ y ∈ bits, validBit y = true)
    (hneBits : ∀ y ∈ bits, y ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (hflag : c.tape (base - 1) = x) :
    NonbranchPrefix p hnt blank
      (cellArrows p hnt blank a armed x write armed' hupd bits hbits hvalid hneBits) c := by
  apply nonbranchPrefix_append p hnt blank _ _ c (cellMiddle a armed c base)
    (skipRL_nonbranchPrefix p hnt blank a armed bits hbits hvalid hneBits
      c hstate base hhead hread)
    (skipRL_run p hnt blank a armed bits hbits hvalid hneBits
      c hstate base hhead hread)
  refine ⟨?_, _, updateRLFlagArrow_step p hnt blank a armed x write armed' hupd
    (cellMiddle a armed c base) rfl hflag, trivial⟩
  intro q read
  simp [cellMiddle]

end PakFixedPolyomino.ULogSourceObliviousRLCellExecution
