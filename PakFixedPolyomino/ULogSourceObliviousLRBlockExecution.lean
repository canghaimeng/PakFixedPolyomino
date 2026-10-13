import PakFixedPolyomino.ULogSourceObliviousUpdateExecution
import Mathlib.Tactic

/-!
# Literal nt-arrow skipLR block on a valid physical bit window

Given a source configuration in `.skipLR a armed rewrite ⟨0, hnt⟩` whose
next `nt` cells are the valid bits `bits`, the existing chronological
`skipLRArrows` list of length `nt` runs to `.updateLRFlag a armed` at
`head + nt`, overlaying `outputBits a rewrite bits` on `[head, head+nt)`
and leaving the exterior unchanged.

This is one logical-symbol LR block, not a full window walk.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLRBlockExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler
open ULogSourceOneHotReader (tapeOfBit)
open ULogSourceOneHotBlocks
open ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution

variable {ns nt : ℕ}

theorem cfg_ext (c₁ c₂ : ScanCfg ns nt)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-! ## Finite-block tape overlay -/

def writeBlock (tape : Int → Phys) (head : Int) (outBits : List Phys)
    (z : Int) : Phys :=
  if hz : head ≤ z then
    if hn : (z - head).toNat < outBits.length then outBits[(z - head).toNat]
    else tape z
  else
    tape z

def outputBits (a : BoundedAction ns nt) (rewrite : Bool) (bits : List Phys) :
    List Phys :=
  if rewrite then (encodeOneHot a.write).map tapeOfBit else bits

@[simp] theorem outputBits_length (a : BoundedAction ns nt) (rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt) :
    (outputBits a rewrite bits).length = nt := by
  cases rewrite <;> simp [outputBits, encodeOneHot_length, hbits]

theorem writeBlock_nil (tape : Int → Phys) (head : Int) :
    writeBlock tape head [] = tape := by
  funext z
  unfold writeBlock
  simp

theorem writeBlock_ofNat (tape : Int → Phys) (head : Int) (outBits : List Phys)
    (i : ℕ) (hi : i < outBits.length) :
    writeBlock tape head outBits (head + i) = outBits[i] := by
  have hdiff : (head + (i : Int)) - head = (i : Int) := by omega
  have hnn : head ≤ head + (i : Int) := by omega
  have hto : ((head + (i : Int)) - head).toNat = i := by
    rw [hdiff, Int.toNat_natCast]
  unfold writeBlock
  simp [hnn, hi]

theorem writeBlock_lt (tape : Int → Phys) (head : Int) (outBits : List Phys)
    (z : Int) (hz : z < head) : writeBlock tape head outBits z = tape z := by
  unfold writeBlock
  have : ¬ head ≤ z := by omega
  simp [this]

theorem writeBlock_ge (tape : Int → Phys) (head : Int) (outBits : List Phys)
    (z : Int) (hz : (head + outBits.length : Int) ≤ z) :
    writeBlock tape head outBits z = tape z := by
  unfold writeBlock
  have hnn : head ≤ z := by omega
  have hge : ¬ (z - head).toNat < outBits.length := by
    have hnn' : 0 ≤ z - head := Int.sub_nonneg_of_le hnn
    have hlen : (outBits.length : Int) ≤ z - head := by omega
    have : outBits.length ≤ (z - head).toNat :=
      (Int.le_toNat (n := outBits.length) hnn').mpr hlen
    omega
  simp [hnn, hge]

theorem writeBlock_at_length (tape : Int → Phys) (head : Int)
    (outBits : List Phys) :
    writeBlock tape head outBits (head + outBits.length) =
      tape (head + outBits.length) := by
  apply writeBlock_ge
  omega

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

theorem writeBlock_snoc (tape : Int → Phys) (head : Int)
    (xs : List Phys) (x : Phys) :
    Function.update (writeBlock tape head xs) (head + xs.length) x =
      writeBlock tape head (xs ++ [x]) := by
  funext z
  by_cases heq : z = head + (xs.length : Int)
  · subst z
    have hnn : head ≤ head + (xs.length : Int) := by omega
    have hdiff : (head + (xs.length : Int)) - head = (xs.length : Int) := by omega
    have hto : ((head + (xs.length : Int)) - head).toNat = xs.length := by
      rw [hdiff, Int.toNat_natCast]
    have hlt : xs.length < (xs ++ [x]).length := by simp
    unfold Function.update writeBlock
    simp [hnn, hlt]
  · have hL :
        Function.update (writeBlock tape head xs) (head + xs.length) x z =
          writeBlock tape head xs z := by
      unfold Function.update
      simp [heq]
    rw [hL]
    by_cases hnn : head ≤ z
    · have hne : (z - head).toNat ≠ xs.length := by
        intro h
        apply heq
        have hnn' : 0 ≤ z - head := Int.sub_nonneg_of_le hnn
        have hz' : z - head = ((z - head).toNat : Int) :=
          (Int.toNat_of_nonneg hnn').symm
        have : z - head = (xs.length : Int) := by simpa [h] using hz'
        omega
      by_cases hlt : (z - head).toNat < xs.length
      · have hlt' : (z - head).toNat < (xs ++ [x]).length := by simp; omega
        have hLv : writeBlock tape head xs z = xs[(z - head).toNat] := by
          unfold writeBlock
          rw [dif_pos hnn, dif_pos hlt]
        have hRv : writeBlock tape head (xs ++ [x]) z =
            (xs ++ [x])[(z - head).toNat] := by
          unfold writeBlock
          rw [dif_pos hnn, dif_pos hlt']
        rw [hLv, hRv]
        exact (List.getElem_append_left (bs := [x]) hlt).symm
      · have hLv : writeBlock tape head xs z = tape z := by
          unfold writeBlock
          rw [dif_pos hnn, dif_neg hlt]
        have hge : ¬ (z - head).toNat < (xs ++ [x]).length := by
          simp; omega
        have hRv : writeBlock tape head (xs ++ [x]) z = tape z := by
          unfold writeBlock
          rw [dif_pos hnn, dif_neg hge]
        rw [hLv, hRv]
    · have hLv : writeBlock tape head xs z = tape z := by
        unfold writeBlock
        rw [dif_neg hnn]
      have hRv : writeBlock tape head (xs ++ [x]) z = tape z := by
        unfold writeBlock
        rw [dif_neg hnn]
      rw [hLv, hRv]

theorem writeBlock_take_succ (tape : Int → Phys) (head : Int)
    (outBits : List Phys) (k : ℕ) (hk : k < outBits.length) :
    Function.update (writeBlock tape head (outBits.take k)) (head + k)
      outBits[k] = writeBlock tape head (outBits.take (k + 1)) := by
  have htake : (outBits.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hsplit := take_succ_getElem outBits k hk
  rw [hsplit, ← writeBlock_snoc, htake]

theorem skipLRWrite_eq_outputBits (a : BoundedAction ns nt) (rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt) (i : Fin nt) :
    skipLRWrite a rewrite i (bits[i.val]'(by omega)) =
      (outputBits a rewrite bits)[i.val]'(by
        simp [outputBits_length a rewrite bits hbits]) := by
  cases rewrite
  · simp [skipLRWrite, outputBits]
  · simp [skipLRWrite, outputBits, List.getElem_map]

/-! ## Single skipLR arrow steps -/

theorem skipLRArrow_step_not_last (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hlast : i.val + 1 ≠ nt) (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite i)
    (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (skipLRArrow p hnt blank a armed rewrite i x hvalid) = some {
        state := .skipLR a armed rewrite ⟨i.val + 1, by omega⟩
        head := c.head + 1
        tape := Function.update c.tape c.head (skipLRWrite a rewrite i x) } := by
  have hact := skipLR_not_last p hnt blank a armed rewrite i x hvalid hlast
  have harrow :
      skipLRArrow p hnt blank a armed rewrite i x hvalid =
        deterministicArrow p hnt blank (.skipLR a armed rewrite i) x
          ⟨skipLRWrite a rewrite i x,
            .skipLR a armed rewrite ⟨i.val + 1, by omega⟩, .right⟩ hact := by
    unfold skipLRArrow
    rw [dif_neg hlast]
  rw [harrow]
  have hs := deterministicArrow_step p hnt blank c
    (.skipLR a armed rewrite i) x
    ⟨skipLRWrite a rewrite i x,
      .skipLR a armed rewrite ⟨i.val + 1, by omega⟩, .right⟩
    hstate hread hact
  simpa [FiniteOneTapeSemantics.writtenTape, moveHead] using hs

theorem skipLRArrow_step_last (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hlast : i.val + 1 = nt) (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite i)
    (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (skipLRArrow p hnt blank a armed rewrite i x hvalid) = some {
        state := .updateLRFlag a armed
        head := c.head + 1
        tape := Function.update c.tape c.head (skipLRWrite a rewrite i x) } := by
  have hact := skipLR_last p hnt blank a armed rewrite i x hvalid hlast
  have harrow :
      skipLRArrow p hnt blank a armed rewrite i x hvalid =
        deterministicArrow p hnt blank (.skipLR a armed rewrite i) x
          ⟨skipLRWrite a rewrite i x, .updateLRFlag a armed, .right⟩ hact := by
    unfold skipLRArrow
    rw [dif_pos hlast]
  rw [harrow]
  have hs := deterministicArrow_step p hnt blank c
    (.skipLR a armed rewrite i) x
    ⟨skipLRWrite a rewrite i x, .updateLRFlag a armed, .right⟩
    hstate hread hact
  simpa [FiniteOneTapeSemantics.writtenTape, moveHead] using hs

theorem skipLRArrows_get (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (i : Fin nt) :
    (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid)[i.val]'(by
      simp) =
      skipLRArrow p hnt blank a armed rewrite i
        (bits.get ⟨i.val, by omega⟩)
        (hvalid _ (List.get_mem _ _)) := by
  simp [skipLRArrows, List.getElem_ofFn]

/-! ## Prefix configurations of the nt-arrow block -/

def skipLRMid (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (c : ScanCfg ns nt) (head : Int)
    (k : ℕ) (hk : k < nt) : ScanCfg ns nt :=
  { state := .skipLR a armed rewrite ⟨k, hk⟩
    head := head + k
    tape := writeBlock c.tape head ((outputBits a rewrite bits).take k) }

def skipLREnd (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (c : ScanCfg ns nt) (head : Int) : ScanCfg ns nt :=
  { state := .updateLRFlag a armed
    head := head + nt
    tape := writeBlock c.tape head (outputBits a rewrite bits) }

theorem skipLRMid_read (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (c : ScanCfg ns nt) (head : Int)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    (skipLRMid a armed rewrite bits c head k hk).tape
      (skipLRMid a armed rewrite bits c head k hk).head =
      bits.get ⟨k, by omega⟩ := by
  have hlen : ((outputBits a rewrite bits).take k).length = k := by
    simp [List.length_take, outputBits_length a rewrite bits hbits,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  have hge : writeBlock c.tape head ((outputBits a rewrite bits).take k)
      (head + k) = c.tape (head + k) := by
    simpa [hlen] using
      writeBlock_at_length c.tape head ((outputBits a rewrite bits).take k)
  simpa [skipLRMid, hge] using hread ⟨k, hk⟩

theorem skipLRMid_zero (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hnt : 0 < nt) (c : ScanCfg ns nt) (head : Int)
    (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (hhead : c.head = head) :
    skipLRMid a armed rewrite bits c head 0 hnt = c := by
  apply cfg_ext
  · simpa [skipLRMid] using hstate.symm
  · simp [skipLRMid, hhead]
  · simp [skipLRMid, writeBlock_nil]

theorem skipLR_take_lt (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      ((skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).take k) c =
      some (skipLRMid a armed rewrite bits c head k hk) := by
  induction k with
  | zero =>
      simp [FiniteOneTapeSemantics.run_nil]
      exact (skipLRMid_zero a armed rewrite bits hnt c head hstate hhead).symm
  | succ k ih =>
      have hk' : k < nt := Nat.lt_of_succ_lt hk
      have hlenA :
          (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).length = nt := by
        simp
      have hsplit :=
        take_succ_getElem
          (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid) k (by omega)
      have hxvalid :
          ULogSourceObliviousScanProgram.validBit
            (bits.get ⟨k, by omega⟩) = true :=
        hvalid _ (List.get_mem _ _)
      have hnotlast : k + 1 ≠ nt := by omega
      rw [hsplit, run_append p hnt blank, ih hk']
      simp only [Option.bind_some, FiniteOneTapeSemantics.run_cons,
        FiniteOneTapeSemantics.run_nil]
      have hget := skipLRArrows_get p hnt blank a armed rewrite bits hbits hvalid
        ⟨k, hk'⟩
      have hstep :=
        skipLRArrow_step_not_last p hnt blank a armed rewrite ⟨k, hk'⟩
          (bits.get ⟨k, by omega⟩) hxvalid hnotlast
          (skipLRMid a armed rewrite bits c head k hk')
          rfl (skipLRMid_read a armed rewrite bits hbits c head hread k hk')
      rw [hget, hstep]
      simp only [Option.bind_some, FiniteOneTapeSemantics.run_nil]
      apply congrArg some
      apply cfg_ext
      · apply congrArg (State.skipLR a armed rewrite)
        apply Fin.ext
        simp
      · simp [skipLRMid]; omega
      · have houtlen : k < (outputBits a rewrite bits).length := by
          simp [outputBits_length a rewrite bits hbits]; exact hk'
        have hwrite :
            skipLRWrite a rewrite ⟨k, hk'⟩ (bits[k]'(by omega)) =
              (outputBits a rewrite bits)[k]'(by exact houtlen) :=
          skipLRWrite_eq_outputBits a rewrite bits hbits ⟨k, hk'⟩
        simp [skipLRMid]
        rw [hwrite]
        exact writeBlock_take_succ c.tape head (outputBits a rewrite bits) k houtlen

theorem skipLR_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid) c =
      some {
        state := .updateLRFlag a armed
        head := head + nt
        tape := writeBlock c.tape head (outputBits a rewrite bits) } := by
  have hlenA :
      (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).length = nt := by
    simp
  have hntpred : nt - 1 < nt := Nat.sub_one_lt_of_lt hnt
  have hsucc : nt - 1 + 1 = nt := Nat.sub_add_cancel hnt
  have hsplit :
      skipLRArrows p hnt blank a armed rewrite bits hbits hvalid =
        (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).take (nt - 1) ++
          [(skipLRArrows p hnt blank a armed rewrite bits hbits hvalid)[nt - 1]'(by omega)] := by
    have h :=
      take_succ_getElem
        (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid) (nt - 1)
        (by omega)
    have htake :
        (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).take nt =
          skipLRArrows p hnt blank a armed rewrite bits hbits hvalid := by
      simp [hlenA]
    rw [hsucc] at h
    exact htake.symm.trans h
  rw [hsplit, run_append p hnt blank]
  have hpre :=
    skipLR_take_lt p hnt blank a armed rewrite bits hbits hvalid c hstate head
      hhead hread (nt - 1) hntpred
  rw [hpre, Option.bind_some]
  simp only [FiniteOneTapeSemantics.run_cons, FiniteOneTapeSemantics.run_nil]
  have hxvalid :
      ULogSourceObliviousScanProgram.validBit
        (bits.get ⟨nt - 1, by omega⟩) = true :=
    hvalid _ (List.get_mem _ _)
  have hget := skipLRArrows_get p hnt blank a armed rewrite bits hbits hvalid
    ⟨nt - 1, hntpred⟩
  have hstep :=
    skipLRArrow_step_last p hnt blank a armed rewrite ⟨nt - 1, hntpred⟩
      (bits.get ⟨nt - 1, by omega⟩) hxvalid (by omega)
      (skipLRMid a armed rewrite bits c head (nt - 1) hntpred)
      rfl (skipLRMid_read a armed rewrite bits hbits c head hread (nt - 1) hntpred)
  rw [hget, hstep]
  simp only [Option.bind_some, FiniteOneTapeSemantics.run_nil]
  apply congrArg some
  apply cfg_ext
  · rfl
  · simp [skipLRMid]; omega
  · have houtlen : nt - 1 < (outputBits a rewrite bits).length := by
      simp [outputBits_length a rewrite bits hbits]; omega
    have hwrite :
        skipLRWrite a rewrite ⟨nt - 1, hntpred⟩
          (bits[nt - 1]'(by omega)) =
          (outputBits a rewrite bits)[nt - 1]'(by exact houtlen) :=
      skipLRWrite_eq_outputBits a rewrite bits hbits ⟨nt - 1, hntpred⟩
    have htakeAll :
        (outputBits a rewrite bits).take ((nt - 1) + 1) =
          outputBits a rewrite bits := by
      simp [hsucc, outputBits_length a rewrite bits hbits]
    simp [skipLRMid]
    rw [hwrite]
    rw [writeBlock_take_succ c.tape head (outputBits a rewrite bits) (nt - 1) houtlen,
      htakeAll]

theorem skipLR_run_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true) :
    (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).length = nt := by
  simp

theorem skipLR_exterior (a : BoundedAction ns nt) (rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (tape : Int → Phys) (head z : Int)
    (hz : z < head ∨ (head + (nt : Int)) ≤ z) :
    writeBlock tape head (outputBits a rewrite bits) z = tape z := by
  rcases hz with hz | hz
  · exact writeBlock_lt tape head _ z hz
  · apply writeBlock_ge
    simp [outputBits_length a rewrite bits hbits]
    exact hz

theorem skipLR_block (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid) c = some c' ∧
      c'.state = .updateLRFlag a armed ∧
      c'.head = head + nt ∧
      c'.tape = writeBlock c.tape head (outputBits a rewrite bits) ∧
      (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).length = nt ∧
      (∀ z, z < head ∨ (head + (nt : Int)) ≤ z → c'.tape z = c.tape z) := by
  refine ⟨{ state := .updateLRFlag a armed
            head := head + nt
            tape := writeBlock c.tape head (outputBits a rewrite bits) },
    ?_, rfl, rfl, rfl, by simp, ?_⟩
  · exact skipLR_run p hnt blank a armed rewrite bits hbits hvalid c
      hstate head hhead hread
  · intro z hz
    exact skipLR_exterior a rewrite bits hbits c.tape head z hz

theorem skipLR_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipLR a armed rewrite ⟨0, hnt⟩)
    (head : Int) (hhead : c.head = head)
    (hread : ∀ i : Fin nt, c.tape (head + (i.val : Int)) =
      bits.get ⟨i.val, by omega⟩)
    (k : ℕ) (hk : k < nt) :
    ∃ c' : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        ((skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).take k) c =
          some c' ∧
      c'.state = .skipLR a armed rewrite ⟨k, hk⟩ ∧
      c'.head = head + k := by
  refine ⟨skipLRMid a armed rewrite bits c head k hk, ?_, rfl, rfl⟩
  exact skipLR_take_lt p hnt blank a armed rewrite bits hbits hvalid c
    hstate head hhead hread k hk

end PakFixedPolyomino.ULogSourceObliviousLRBlockExecution
