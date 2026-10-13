import PakFixedPolyomino.ULogSourceObliviousRLBlockExecution
import PakFixedPolyomino.ULogSourceObliviousLRBlockInverse

/-! # Exact reverse-block prefixes and unrestricted raw converse -/

namespace PakFixedPolyomino.ULogSourceObliviousRLBlockInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousRunPrefix
open ULogSourceObliviousRLBlockExecution
open ULogSourceObliviousLRBlockInverse (nonbranchPrefix_of_run)

variable {ns nt : ℕ}

theorem skipRL_nonbranchPrefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    NonbranchPrefix p hnt blank
      (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) c := by
  apply nonbranchPrefix_of_run p hnt blank _ c _
    (skipRL_run p hnt blank a armed bits hbits hvalid hneBits c hstate base hhead hread)
  intro k hk mid hmid q read
  have hkn : k < nt := by simpa using hk
  have hcanonical := skipRL_take_lt p hnt blank a armed bits hbits hvalid hneBits
    c hstate base hhead hread k hkn
  have heq : mid = skipRLMid a armed c base k hkn :=
    Option.some.inj (hmid.symm.trans hcanonical)
  simp [heq, skipRLMid]

theorem skipRL_raw_unique
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlength : raw.length = nt) :
    raw = skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits ∧
      out = { state := .updateRLFlag a armed, head := base - 1, tape := c.tape } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (skipRL_nonbranchPrefix p hnt blank a armed bits hbits hvalid hneBits
      c hstate base hhead hread)
  obtain ⟨heq, hout⟩ := forcedPrefix_unique_successful_run
    (program p hnt blank) (fun _ => true) _ raw c out hforced hrun
    (by simpa using hlength.symm)
  exact ⟨heq, Option.some.inj (hout.symm.trans
    (skipRL_run p hnt blank a armed bits hbits hvalid hneBits c hstate base hhead hread))⟩

theorem skipRL_raw_prefix
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlength : nt ≤ raw.length) :
    ∃ tail,
      raw = skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        { state := .updateRLFlag a armed, head := base - 1, tape := c.tape } = some out := by
  obtain ⟨tail, mid, heq, hpre, htail⟩ :=
    nonbranchPrefix_split_successful_run p hnt blank _ raw c out
      (skipRL_nonbranchPrefix p hnt blank a armed bits hbits hvalid hneBits
        c hstate base hhead hread) hrun (by simpa using hlength)
  have heqmid := Option.some.inj (hpre.symm.trans
    (skipRL_run p hnt blank a armed bits hbits hvalid hneBits c hstate base hhead hread))
  exact ⟨tail, heq, heqmid ▸ htail⟩

/-- Complete literal run, exact fuel, and actual operational head at every
prefix, including the full block. This is stronger than endpoint bounds. -/
theorem skipRL_exact_block
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    run (program p hnt blank) (fun _ => true)
      (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) c =
        some { state := .updateRLFlag a armed, head := base - 1, tape := c.tape } ∧
    (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).length = nt ∧
    ∀ k ≤ nt, ∃ mid : ScanCfg ns nt,
      run (program p hnt blank) (fun _ => true)
        ((skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take k) c =
          some mid ∧
      mid.tape = c.tape ∧ mid.head = base + (nt : Int) - 1 - k ∧
      base - 1 ≤ mid.head ∧ mid.head ≤ base + (nt : Int) - 1 := by
  refine ⟨skipRL_run p hnt blank a armed bits hbits hvalid hneBits c hstate base
    hhead hread, by simp, ?_⟩
  intro k hk
  by_cases hlt : k < nt
  · refine ⟨skipRLMid a armed c base k hlt,
      skipRL_take_lt p hnt blank a armed bits hbits hvalid hneBits c hstate base
        hhead hread k hlt, rfl, rfl, ?_, ?_⟩
    all_goals simp [skipRLMid]; omega
  · have heq : k = nt := by omega
    subst k
    refine ⟨{ state := .updateRLFlag a armed, head := base - 1, tape := c.tape },
      ?_, rfl, ?_, le_rfl, ?_⟩
    · have htake :
          (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take nt =
            skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits := by simp
      rw [htake]
      exact skipRL_run p hnt blank a armed bits hbits hvalid hneBits c
        hstate base hhead hread
    · change base - 1 = base + (nt : Int) - 1 - nt
      omega
    · simp

end PakFixedPolyomino.ULogSourceObliviousRLBlockInverse
