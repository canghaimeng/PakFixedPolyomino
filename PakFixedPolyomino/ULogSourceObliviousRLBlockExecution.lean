import PakFixedPolyomino.ULogSourceObliviousUpdateExecution
import Mathlib.Tactic

/-!
# Literal nt-arrow skipRL block on a valid nonblank bit window

From `.skipRL a armed ⟨nt-1⟩` at `base + nt - 1`, with `bits` occupying
`[base, base+nt)`, the existing reverse `skipRLBitArrows` list of length
`nt` runs to `.updateRLFlag a armed` at `base - 1` and leaves the tape
unchanged.

This is one reverse logical-symbol block, not a full window walk.
-/

namespace PakFixedPolyomino.ULogSourceObliviousRLBlockExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler
open ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution

variable {ns nt : ℕ}

theorem cfg_ext (c₁ c₂ : ScanCfg ns nt)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

theorem take_succ_getElem {α : Type*} (l : List α) (k : ℕ)
    (h : k < l.length) : l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k =>
          have h' : k < xs.length := by simp at h; omega
          simpa using ih k h'

/-! ## Single skipRL arrow steps (identity write, move left) -/

theorem skipRLArrow_step_not_first (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hne : x ≠ ULogSourceOneHotReader.blank) (hfirst : i.val ≠ 0)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed i) (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (skipRLArrow p hnt blank a armed i x hvalid hne) = some {
        state := .skipRL a armed ⟨i.val - 1, by omega⟩
        head := c.head - 1
        tape := c.tape } := by
  have hact := skipRL_not_first p hnt blank a armed i x hvalid hne hfirst
  have harrow :
      skipRLArrow p hnt blank a armed i x hvalid hne =
        deterministicArrow p hnt blank (.skipRL a armed i) x
          ⟨x, .skipRL a armed ⟨i.val - 1, by omega⟩, .left⟩ hact := by
    unfold skipRLArrow
    rw [dif_neg hfirst]
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c x = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c (.skipRL a armed i) x
    ⟨x, .skipRL a armed ⟨i.val - 1, by omega⟩, .left⟩ hstate hread hact
  simpa [htape, moveHead] using hs

theorem skipRLArrow_step_first (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hne : x ≠ ULogSourceOneHotReader.blank) (hfirst : i.val = 0)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed i) (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (skipRLArrow p hnt blank a armed i x hvalid hne) = some {
        state := .updateRLFlag a armed
        head := c.head - 1
        tape := c.tape } := by
  have hact := skipRL_first p hnt blank a armed i x hvalid hne hfirst
  have harrow :
      skipRLArrow p hnt blank a armed i x hvalid hne =
        deterministicArrow p hnt blank (.skipRL a armed i) x
          ⟨x, .updateRLFlag a armed, .left⟩ hact := by
    unfold skipRLArrow
    rw [dif_pos hfirst]
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c x = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c (.skipRL a armed i) x
    ⟨x, .updateRLFlag a armed, .left⟩ hstate hread hact
  simpa [htape, moveHead] using hs

theorem skipRLBitArrows_get (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hne : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (k : Fin nt) :
    (skipRLBitArrows p hnt blank a armed bits hbits hvalid hne)[k.val]'(by simp) =
      skipRLArrow p hnt blank a armed ⟨nt - 1 - k.val, by omega⟩
        (bits.get ⟨nt - 1 - k.val, by omega⟩)
        (hvalid _ (List.get_mem _ _)) (hne _ (List.get_mem _ _)) := by
  simp [skipRLBitArrows, List.getElem_ofFn]

/-! ## Prefix configurations of the reverse block -/

def skipRLMid (a : BoundedAction ns nt) (armed : Bool)
    (c : ScanCfg ns nt) (base : Int) (k : ℕ) (hk : k < nt) : ScanCfg ns nt :=
  { state := .skipRL a armed ⟨nt - 1 - k, by omega⟩
    head := base + (nt : Int) - 1 - k
    tape := c.tape }

theorem skipRLMid_read (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (c : ScanCfg ns nt) (base : Int)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    (skipRLMid a armed c base k hk).tape (skipRLMid a armed c base k hk).head =
      bits.get ⟨nt - 1 - k, by omega⟩ := by
  have hidx : base + (nt : Int) - 1 - k = base + ((nt - 1 - k : ℕ) : Int) := by
    omega
  simp only [skipRLMid]
  rw [hidx]
  exact hread ⟨nt - 1 - k, by omega⟩

theorem skipRLMid_zero (a : BoundedAction ns nt) (armed : Bool)
    (hnt : 0 < nt) (c : ScanCfg ns nt) (base : Int)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (hhead : c.head = base + (nt : Int) - 1) :
    skipRLMid a armed c base 0 hnt = c := by
  apply cfg_ext <;> simp [skipRLMid, hstate, hhead]

theorem skipRL_take_lt (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      ((skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take k) c =
      some (skipRLMid a armed c base k hk) := by
  induction k with
  | zero =>
      simp [FiniteOneTapeSemantics.run_nil]
      exact (skipRLMid_zero a armed hnt c base hstate hhead).symm
  | succ k ih =>
      have hk' : k < nt := Nat.lt_of_succ_lt hk
      have hsplit :=
        take_succ_getElem
          (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) k
          (by simp; omega)
      let i : Fin nt := ⟨nt - 1 - k, by omega⟩
      have hxvalid :
          ULogSourceObliviousScanProgram.validBit
            (bits.get ⟨i.val, by omega⟩) = true :=
        hvalid _ (List.get_mem _ _)
      have hxne : bits.get ⟨i.val, by omega⟩ ≠ ULogSourceOneHotReader.blank :=
        hneBits _ (List.get_mem _ _)
      have hnotfirst : i.val ≠ 0 := by
        simp [i]; omega
      have hst : (skipRLMid a armed c base k hk').state = .skipRL a armed i := by
        simp [skipRLMid, i]
      have hrd :
          (skipRLMid a armed c base k hk').tape
            (skipRLMid a armed c base k hk').head =
            bits.get ⟨i.val, by omega⟩ := by
        simpa [i] using skipRLMid_read a armed bits hbits c base hread k hk'
      rw [hsplit, run_append p hnt blank, ih hk']
      simp only [Option.bind_some, FiniteOneTapeSemantics.run_cons,
        FiniteOneTapeSemantics.run_nil]
      have hget := skipRLBitArrows_get p hnt blank a armed bits hbits hvalid
        hneBits ⟨k, hk'⟩
      have hstep :=
        skipRLArrow_step_not_first p hnt blank a armed i
          (bits.get ⟨i.val, by omega⟩) hxvalid hxne hnotfirst
          (skipRLMid a armed c base k hk') hst hrd
      rw [hget, hstep]
      simp only [Option.bind_some, FiniteOneTapeSemantics.run_nil]
      apply congrArg some
      apply cfg_ext
      · simp [skipRLMid, i]; omega
      · simp [skipRLMid]; omega
      · rfl

theorem skipRL_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) c =
      some {
        state := .updateRLFlag a armed
        head := base - 1
        tape := c.tape } := by
  have hlenA :
      (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).length = nt := by
    simp
  have hntpred : nt - 1 < nt := Nat.sub_one_lt_of_lt hnt
  have hsucc : nt - 1 + 1 = nt := Nat.sub_add_cancel hnt
  have hsplit :
      skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits =
        (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take (nt - 1) ++
          [(skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits)[nt - 1]'(by omega)] := by
    have h :=
      take_succ_getElem
        (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) (nt - 1)
        (by omega)
    have htake :
        (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take nt =
          skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits := by
      simp [hlenA]
    rw [hsucc] at h
    exact htake.symm.trans h
  rw [hsplit, run_append p hnt blank]
  have hpre :=
    skipRL_take_lt p hnt blank a armed bits hbits hvalid hneBits c hstate base
      hhead hread (nt - 1) hntpred
  rw [hpre, Option.bind_some]
  simp only [FiniteOneTapeSemantics.run_cons, FiniteOneTapeSemantics.run_nil]
  let i : Fin nt := ⟨nt - 1 - (nt - 1), by omega⟩
  have hxvalid :
      ULogSourceObliviousScanProgram.validBit
        (bits.get ⟨i.val, by omega⟩) = true :=
    hvalid _ (List.get_mem _ _)
  have hxne : bits.get ⟨i.val, by omega⟩ ≠ ULogSourceOneHotReader.blank :=
    hneBits _ (List.get_mem _ _)
  have hfirst : i.val = 0 := by simp [i]
  have hst :
      (skipRLMid a armed c base (nt - 1) hntpred).state = .skipRL a armed i := by
    simp [skipRLMid, i]
  have hrd :
      (skipRLMid a armed c base (nt - 1) hntpred).tape
        (skipRLMid a armed c base (nt - 1) hntpred).head =
        bits.get ⟨i.val, by omega⟩ := by
    simpa [i] using
      skipRLMid_read a armed bits hbits c base hread (nt - 1) hntpred
  have hget := skipRLBitArrows_get p hnt blank a armed bits hbits hvalid hneBits
    ⟨nt - 1, hntpred⟩
  have hstep :=
    skipRLArrow_step_first p hnt blank a armed i
      (bits.get ⟨i.val, by omega⟩) hxvalid hxne hfirst
      (skipRLMid a armed c base (nt - 1) hntpred) hst hrd
  rw [hget, hstep]
  simp only [Option.bind_some, FiniteOneTapeSemantics.run_nil]
  apply congrArg some
  apply cfg_ext
  · rfl
  · simp [skipRLMid]; omega
  · rfl

theorem skipRL_run_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank) :
    (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).length = nt := by
  simp

theorem skipRL_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        ((skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take k) c =
          some c' ∧
      c'.state = .skipRL a armed ⟨nt - 1 - k, by omega⟩ ∧
      c'.head = base + (nt : Int) - 1 - k ∧
      c'.tape = c.tape ∧
      base - 1 ≤ c'.head ∧ c'.head ≤ base + (nt : Int) - 1 := by
  refine ⟨skipRLMid a armed c base k hk, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · exact skipRL_take_lt p hnt blank a armed bits hbits hvalid hneBits c
      hstate base hhead hread k hk
  · simp [skipRLMid]; omega
  · simp [skipRLMid]; omega

theorem skipRL_head_bound (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k ≤ nt) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        ((skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take k) c =
          some c' ∧
      c'.tape = c.tape ∧
      base - 1 ≤ c'.head ∧ c'.head ≤ base + (nt : Int) - 1 := by
  by_cases hlt : k < nt
  · rcases skipRL_prefix_head p hnt blank a armed bits hbits hvalid hneBits c
      hstate base hhead hread k hlt with ⟨c', hrun, _, _, htape, hlo, hhi⟩
    exact ⟨c', hrun, htape, hlo, hhi⟩
  · have hknt : k = nt := by omega
    subst k
    have htake :
        (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).take nt =
          skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits := by
      simp
    refine ⟨{ state := .updateRLFlag a armed, head := base - 1, tape := c.tape },
      ?_, rfl, le_rfl, ?_⟩
    · rw [htake]
      exact skipRL_run p hnt blank a armed bits hbits hvalid hneBits c
        hstate base hhead hread
    · simp

theorem skipRL_block (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hneBits : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a armed ⟨nt - 1, by omega⟩)
    (base : Int) (hhead : c.head = base + (nt : Int) - 1)
    (hread : ∀ i : Fin nt, c.tape (base + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits) c = some c' ∧
      c'.state = .updateRLFlag a armed ∧
      c'.head = base - 1 ∧
      c'.tape = c.tape ∧
      (skipRLBitArrows p hnt blank a armed bits hbits hvalid hneBits).length = nt ∧
      base - 1 ≤ c'.head ∧ c'.head ≤ base + (nt : Int) - 1 := by
  refine ⟨{ state := .updateRLFlag a armed, head := base - 1, tape := c.tape },
    ?_, rfl, rfl, rfl, by simp, le_rfl, ?_⟩
  · exact skipRL_run p hnt blank a armed bits hbits hvalid hneBits c
      hstate base hhead hread
  · simp

end PakFixedPolyomino.ULogSourceObliviousRLBlockExecution
