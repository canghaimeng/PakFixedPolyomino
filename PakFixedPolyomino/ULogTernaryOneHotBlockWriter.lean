import PakFixedPolyomino.ULogSourceOneHotBlocks
import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogFiniteTapeZipperRun
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Literal finite ternary one-hot block writer. One program per alphabet
size `nt > 0`, independent of the represented symbol `a`. Writes
`encodeOneHot a` into already allocated zeros and returns to the start
cell. Loader composition and the original headline remain separate. -/

namespace PakFixedPolyomino.ULogTernaryOneHotBlockWriter

open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter
  (fromCells fromCells_eq bind_run fromCells_state)
open ULogTernaryRetainedCounterPump (cell cells)
open ULogSourceOneHotBlocks
  (encodeOneHot encodeOneHot_length encodeOneHot_getElem)
open FiniteOneTapeSemantics (moveHead)

def stateCount (nt : Nat) : Nat := nt * nt + nt + 2

instance (nt : Nat) : NeZero (stateCount nt) :=
  ⟨Nat.pos_iff_ne_zero.mp (by unfold stateCount; omega)⟩

def writeQ {nt : Nat} (_hnt : 0 < nt) (a i : Fin nt) : Fin (stateCount nt) :=
  ⟨2 + a.val * nt + i.val, by
    have ha := a.isLt; have hi := i.isLt
    have hlt : a.val * nt + i.val < nt * nt := by
      have : a.val * nt + i.val < a.val * nt + nt := Nat.add_lt_add_left hi _
      have : a.val * nt + nt = (a.val + 1) * nt := by ring
      have : (a.val + 1) * nt ≤ nt * nt :=
        Nat.mul_le_mul_right nt (Nat.succ_le_of_lt ha)
      omega
    unfold stateCount; omega⟩

def returnQ {nt : Nat} (_hnt : 0 < nt) (j : Nat) (hj : j < nt - 1) :
    Fin (stateCount nt) :=
  ⟨2 + nt * nt + j, by unfold stateCount; omega⟩

def entry {nt : Nat} (hnt : 0 < nt) (a : Fin nt) : Fin (stateCount nt) :=
  writeQ hnt a ⟨0, hnt⟩

def program (nt : Nat) (hnt : 0 < nt) : BoundedProgram (stateCount nt) 3 where
  rule q read slot :=
    if slot then none
    else if hHalt : q.val < 2 then none
    else if hW : q.val < 2 + nt * nt then
      if hNext : (q.val - 2) % nt + 1 < nt then
        some ⟨if (q.val - 2) % nt = (q.val - 2) / nt then 1 else 0,
          ⟨q.val + 1, by unfold stateCount at hW ⊢; omega⟩, .right⟩
      else if hBig : 1 < nt then
        some ⟨if (q.val - 2) % nt = (q.val - 2) / nt then 1 else 0,
          ⟨2 + nt * nt + (nt - 2), by unfold stateCount; omega⟩, .stay⟩
      else
        some ⟨if (q.val - 2) % nt = (q.val - 2) / nt then 1 else 0,
          ⟨0, by unfold stateCount; omega⟩, .stay⟩
    else if hR : q.val < 2 + nt * nt + (nt - 1) then
      some ⟨read,
        if hJ : q.val = 2 + nt * nt then
          ⟨0, by unfold stateCount; omega⟩
        else
          ⟨q.val - 1, by unfold stateCount at hR ⊢; omega⟩, .left⟩
    else none

def initial {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ULogTernaryCountedSourceDelimiter.fromCells (entry hnt a) left
    (List.replicate nt 0 ++ suffix)

def final {nt : Nat} (a : Fin nt) (left suffix : List (Fin 3)) :
    BoundedConfig (stateCount nt) 3 :=
  ULogTernaryCountedSourceDelimiter.fromCells 0 left
    (ULogTernaryRetainedCounterPump.cells
      (ULogSourceOneHotBlocks.encodeOneHot a) ++ suffix)

def deadline (nt : Nat) : Nat := 2 * nt - 1

def bits {nt : Nat} (a : Fin nt) : List (Fin 3) := cells (encodeOneHot a)

def occupied (nt : Nat) (left suffix : List (Fin 3)) : Nat :=
  left.length + nt + suffix.length

def writeCfg {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (k : Nat) (hk : k < nt)
    (left suffix : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ⟨writeQ hnt a ⟨k, hk⟩, (List.take k (bits a)).reverse ++ left, 0,
    List.replicate (nt - k - 1) 0 ++ suffix⟩

def returnCfg {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (d : Nat) (hd : d < nt)
    (left suffix : List (Fin 3)) : BoundedConfig (stateCount nt) 3 :=
  ⟨if h : d = nt - 1 then ⟨0, by unfold stateCount; omega⟩
    else returnQ hnt (nt - 2 - d) (by omega),
    (List.take (nt - 1 - d) (bits a)).reverse ++ left,
    (bits a)[nt - 1 - d]'(by simp [bits, cells, encodeOneHot_length]; omega),
    (bits a).drop (nt - d) ++ suffix⟩

theorem entry_val {nt : Nat} (hnt : 0 < nt) (a : Fin nt) :
    (entry hnt a).val = 2 + a.val * nt := by
  simp [entry, writeQ]

theorem writeQ_bound {nt : Nat} (hnt : 0 < nt) (a i : Fin nt) :
    ¬ (writeQ hnt a i).val < 2 ∧ (writeQ hnt a i).val < 2 + nt * nt := by
  have ha := a.isLt; have hi := i.isLt
  have hlt : a.val * nt + i.val < nt * nt := by
    have : a.val * nt + i.val < a.val * nt + nt := Nat.add_lt_add_left hi _
    have : a.val * nt + nt = (a.val + 1) * nt := by ring
    have : (a.val + 1) * nt ≤ nt * nt :=
      Nat.mul_le_mul_right nt (Nat.succ_le_of_lt ha)
    omega
  simp [writeQ]; omega

theorem decode_div {nt : Nat} (hnt : 0 < nt) (a i : Fin nt) :
    (a.val * nt + i.val) / nt = a.val := by
  rw [Nat.add_comm, Nat.add_mul_div_right i.val a.val hnt,
    Nat.div_eq_of_lt i.isLt, Nat.zero_add]

theorem decode_mod {nt : Nat} (hnt : 0 < nt) (a i : Fin nt) :
    (a.val * nt + i.val) % nt = i.val := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

theorem decode_write {nt : Nat} (hnt : 0 < nt) (a i : Fin nt) :
    ((writeQ hnt a i).val - 2) / nt = a.val ∧
      ((writeQ hnt a i).val - 2) % nt = i.val := by
  have hsub : 2 + a.val * nt + i.val - 2 = a.val * nt + i.val := by omega
  simp [writeQ, hsub, decode_div hnt a i, decode_mod hnt a i]

theorem bits_length {nt : Nat} (a : Fin nt) : (bits a).length = nt := by
  simp [bits, cells, encodeOneHot_length]

theorem bits_get {nt : Nat} (a : Fin nt) (i : Nat) (hi : i < nt) :
    (bits a)[i]'(by simp [bits_length, hi]) =
      if i = a.val then (1 : Fin 3) else 0 := by
  have h := encodeOneHot_getElem a i hi
  simp [List.get_eq_getElem] at h
  simp [bits, cells, List.getElem_map, h, cell]
  by_cases hia : i = a.val <;> simp [hia]

theorem take_succ_getElem {α} (l : List α) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => cases hk
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k =>
          simpa [List.take] using ih k (Nat.lt_of_succ_lt_succ (by simpa using hk))

theorem bits_take_succ {nt : Nat} (a : Fin nt) (k : Nat) (hk : k < nt) :
    (bits a).take (k + 1) =
      (bits a).take k ++ [(bits a)[k]'(by simp [bits_length, hk])] :=
  take_succ_getElem _ k (by simp [bits_length, hk])

theorem deadline_split {nt : Nat} (hnt : 0 < nt) :
    deadline nt = nt + (nt - 1) := by
  simp [deadline]; omega

theorem replicate_concat (n : Nat) :
    List.replicate (n + 1) false = List.replicate n false ++ [false] := by
  simpa using List.replicate_add n 1 false

theorem config_ext {ns nα : Nat} {c₁ c₂ : BoundedConfig ns nα}
    (h1 : c₁.state = c₂.state) (h2 : c₁.leftRev = c₂.leftRev)
    (h3 : c₁.focus = c₂.focus) (h4 : c₁.right = c₂.right) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

theorem rule_true {nt : Nat} (hnt : 0 < nt) (q : Fin (stateCount nt))
    (read : Fin 3) : (program nt hnt).rule q read true = none := by
  simp [program]

theorem program_falseOnly {nt : Nat} (hnt : 0 < nt) :
    FalseOnly (program nt hnt) :=
  fun q read => rule_true hnt q read

theorem rule_write_mid {nt : Nat} (hnt : 0 < nt) (a i : Fin nt)
    (hnext : i.val + 1 < nt) (read : Fin 3) :
    (program nt hnt).rule (writeQ hnt a i) read false =
      some ⟨if i.val = a.val then 1 else 0,
        writeQ hnt a ⟨i.val + 1, hnext⟩, .right⟩ := by
  have ⟨hge, hlt⟩ := writeQ_bound hnt a i
  have ⟨hdiv, hmod⟩ := decode_write hnt a i
  have htg : (writeQ hnt a i).val + 1 =
      (writeQ hnt a ⟨i.val + 1, hnext⟩).val := by simp [writeQ]; omega
  have hN : ((writeQ hnt a i).val - 2) % nt + 1 < nt := by rw [hmod]; exact hnext
  dsimp [program]
  rw [dif_neg hge, dif_pos hlt, if_pos hN]
  simp [hdiv, hmod, htg]

theorem rule_write_last {nt : Nat} (hnt : 0 < nt) (a i : Fin nt)
    (hlast : ¬ i.val + 1 < nt) (read : Fin 3) :
    (program nt hnt).rule (writeQ hnt a i) read false =
      some ⟨if i.val = a.val then 1 else 0,
        if hBig : 1 < nt then returnQ hnt (nt - 2) (by omega)
        else ⟨0, by unfold stateCount; omega⟩, .stay⟩ := by
  have ⟨hge, hlt⟩ := writeQ_bound hnt a i
  have ⟨hdiv, hmod⟩ := decode_write hnt a i
  have hN : ¬ ((writeQ hnt a i).val - 2) % nt + 1 < nt := by rw [hmod]; exact hlast
  dsimp [program]
  rw [dif_neg hge, dif_pos hlt, if_neg hN]
  simp [hdiv, hmod]
  by_cases hBig : 1 < nt <;> simp [hBig, returnQ]

theorem returnQ_bound {nt : Nat} (hnt : 0 < nt) (j : Nat) (hj : j < nt - 1) :
    ¬ (returnQ hnt j hj).val < 2 ∧
      ¬ (returnQ hnt j hj).val < 2 + nt * nt ∧
      (returnQ hnt j hj).val < 2 + nt * nt + (nt - 1) := by
  simp [returnQ]; omega

theorem rule_return {nt : Nat} (hnt : 0 < nt) (j : Nat) (hj : j < nt - 1)
    (read : Fin 3) :
    (program nt hnt).rule (returnQ hnt j hj) read false =
      some ⟨read,
        if h0 : j = 0 then ⟨0, by unfold stateCount; omega⟩
        else returnQ hnt (j - 1) (by omega), .left⟩ := by
  have ⟨hge, hnW, hR⟩ := returnQ_bound hnt j hj
  dsimp [program]
  rw [dif_neg hge, dif_neg hnW, dif_pos hR]
  by_cases hJ : (returnQ hnt j hj).val = 2 + nt * nt
  · have hj0 : j = 0 := by simp [returnQ] at hJ; omega
    rw [dif_pos hJ]
    simp [hj0]
  · have hj0 : j ≠ 0 := by intro h; simp [returnQ, h] at hJ
    rw [dif_neg hJ]
    simp [hj0]
    exact Fin.ext (by simp [returnQ]; omega)

theorem writeCfg_not_halt {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (k : Nat)
    (hk : k < nt) (left suffix : List (Fin 3)) :
    boundedHalted (writeCfg hnt a k hk left suffix) = false := by
  have ⟨hge, _⟩ := writeQ_bound hnt a ⟨k, hk⟩
  simp [writeCfg, boundedHalted]; omega

theorem returnCfg_not_halt {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (d : Nat)
    (hd : d < nt) (hd0 : d ≠ nt - 1) (left suffix : List (Fin 3)) :
    boundedHalted (returnCfg hnt a d hd left suffix) = false := by
  simp [returnCfg, hd0, boundedHalted, returnQ]; omega

theorem initial_eq_writeCfg {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) :
    initial hnt a left suffix = writeCfg hnt a 0 hnt left suffix := by
  have hrep : List.replicate nt (0 : Fin 3) ++ suffix =
      0 :: (List.replicate (nt - 1) 0 ++ suffix) := by
    have : nt = nt - 1 + 1 := by omega
    rw [this, List.replicate_succ, List.cons_append, Nat.add_sub_cancel]
  unfold initial writeCfg entry
  rw [hrep]
  simp [fromCells, List.take_zero, List.reverse_nil]

theorem returnCfg_final {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) :
    returnCfg hnt a (nt - 1) (by omega) left suffix = final a left suffix := by
  have hfin : final a left suffix = fromCells 0 left (bits a ++ suffix) := rfl
  cases hb : bits a with
  | nil =>
      have := bits_length a; simp [hb] at this; omega
  | cons x xs =>
      unfold returnCfg
      rw [dif_pos rfl]
      have h0 : nt - 1 - (nt - 1) = 0 := by omega
      have h1 : nt - (nt - 1) = 1 := by omega
      simp [hfin, fromCells, hb, h0, h1, List.take_zero, List.reverse_nil]

theorem step_write_mid {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (k : Nat)
    (hk : k + 1 < nt) (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 [false] H
      (writeCfg hnt a k (by omega) left suffix) =
      some (H + 1, writeCfg hnt a (k + 1) (by omega) left suffix) := by
  have hk0 : k < nt := by omega
  have hh := writeCfg_not_halt hnt a k hk0 left suffix
  have hr := rule_write_mid hnt a ⟨k, hk0⟩ hk (0 : Fin 3)
  have heq : nt - k - 1 = nt - (k + 1) := Nat.sub_sub _ _ _
  have hpos : 0 < nt - k - 1 := by rw [heq]; exact Nat.sub_pos_of_lt hk
  have hsucc : List.replicate (nt - k - 1) (0 : Fin 3) =
      0 :: List.replicate (nt - (k + 1) - 1) 0 := by
    have h1 : nt - k - 1 = Nat.succ (nt - k - 1 - 1) :=
      (Nat.succ_pred_eq_of_pos hpos).symm
    have h2 : nt - k - 1 - 1 = nt - (k + 1) - 1 := by rw [heq]
    rw [h1, h2, List.replicate_succ]
  have hsrc : writeCfg hnt a k (by omega) left suffix =
      writeCfg hnt a k hk0 left suffix := by
    apply config_ext <;> simp [writeCfg, writeQ]
  have hdst : writeCfg hnt a (k + 1) (by omega) left suffix =
      writeCfg hnt a (k + 1) hk left suffix := by
    apply config_ext <;> simp [writeCfg, writeQ]
  rw [hsrc, hdst]
  dsimp [run]
  rw [hh]
  rw [show (writeCfg hnt a k hk0 left suffix).state = writeQ hnt a ⟨k, hk0⟩ from rfl]
  rw [show (writeCfg hnt a k hk0 left suffix).focus = (0 : Fin 3) from rfl]
  rw [hr]
  simp [writeCfg, applyBounded, moveHead, hsucc]
  have ht := bits_take_succ a k hk0
  rw [ht, List.reverse_append]
  simp [bits_get a k hk0]

theorem step_write_last {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 [false] H
      (writeCfg hnt a (nt - 1) (by omega) left suffix) =
      some (H, returnCfg hnt a 0 hnt left suffix) := by
  have hk : nt - 1 < nt := by omega
  have hh := writeCfg_not_halt hnt a (nt - 1) hk left suffix
  have hval : (⟨nt - 1, hk⟩ : Fin nt).val = nt - 1 := rfl
  have hr := rule_write_last hnt a ⟨nt - 1, hk⟩ (by simp [hval]; omega) (0 : Fin 3)
  have hz : nt - (nt - 1) - 1 = 0 := by omega
  have hsrc : writeCfg hnt a (nt - 1) (by omega) left suffix =
      writeCfg hnt a (nt - 1) hk left suffix := by
    apply config_ext <;> simp [writeCfg, writeQ]
  rw [hsrc]
  dsimp [run]
  rw [hh]
  rw [show (writeCfg hnt a (nt - 1) hk left suffix).state =
      writeQ hnt a ⟨nt - 1, hk⟩ from rfl]
  rw [show (writeCfg hnt a (nt - 1) hk left suffix).focus = (0 : Fin 3) from rfl]
  rw [hr]
  simp [applyBounded, moveHead]
  apply config_ext
  · simp [returnCfg]
    split_ifs <;> first | omega | simp [returnQ]
  · simp [writeCfg, returnCfg]
  · simp [writeCfg, returnCfg]
    exact (bits_get a (nt - 1) hk).symm
  · have hdrop : (bits a).drop nt = [] := by simp [bits_length]
    simp [writeCfg, returnCfg, hz, hdrop]

theorem write_prefix {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (k : Nat)
    (hk : k < nt) (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 (List.replicate k false) H
      (initial hnt a left suffix) =
      some (H + k, writeCfg hnt a k hk left suffix) := by
  induction k with
  | zero =>
      simp [run, initial_eq_writeCfg]
  | succ k ih =>
      have hk0 : k < nt := by omega
      rw [replicate_concat, run_append, ih hk0, bind_run,
        step_write_mid hnt a k (by omega)]
      exact congrArg some (Prod.ext (by omega) rfl)

theorem write_run {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 (List.replicate nt false) H
      (initial hnt a left suffix) =
      some (H + ((nt - 1 : Nat) : Int), returnCfg hnt a 0 hnt left suffix) := by
  have hw : List.replicate nt false =
      List.replicate (nt - 1) false ++ [false] := by
    have h := replicate_concat (nt - 1)
    rwa [Nat.sub_add_cancel hnt] at h
  rw [hw, run_append, write_prefix hnt a (nt - 1) (by omega), bind_run,
    step_write_last]

theorem step_return {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (d : Nat)
    (hd : d + 1 < nt) (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 [false] H
      (returnCfg hnt a d (by omega) left suffix) =
      some (H - 1, returnCfg hnt a (d + 1) (by omega) left suffix) := by
  have hdlt : d < nt := by omega
  have hd0 : d ≠ nt - 1 := by omega
  have hj : nt - 2 - d < nt - 1 := by omega
  have hi : nt - 1 - d < (bits a).length := by simp [bits_length]; omega
  have hr := rule_return hnt (nt - 2 - d) hj ((bits a)[nt - 1 - d]'hi)
  have hrev :
      (List.take (nt - 1 - d) (bits a)).reverse =
        (bits a)[nt - 2 - d]'(by simp [bits_length]; omega) ::
          (List.take (nt - 2 - d) (bits a)).reverse := by
    have : nt - 1 - d = (nt - 2 - d) + 1 := by omega
    rw [this, bits_take_succ a (nt - 2 - d) (by omega), List.reverse_append]
    rfl
  have hsrc : returnCfg hnt a d (by omega) left suffix =
      ⟨returnQ hnt (nt - 2 - d) hj,
        (List.take (nt - 1 - d) (bits a)).reverse ++ left,
        (bits a)[nt - 1 - d]'hi, (bits a).drop (nt - d) ++ suffix⟩ := by
    unfold returnCfg
    rw [dif_neg hd0]
  rw [hsrc]
  dsimp [run]
  have hh' : boundedHalted
      ⟨returnQ hnt (nt - 2 - d) hj,
        (List.take (nt - 1 - d) (bits a)).reverse ++ left,
        (bits a)[nt - 1 - d]'hi, (bits a).drop (nt - d) ++ suffix⟩ = false := by
    simp [boundedHalted, returnQ]; omega
  rw [hh', hr, hrev]
  simp [applyBounded, moveHead]
  apply config_ext
  · simp [returnCfg]
    by_cases hlast : d + 1 = nt - 1
    · have : nt - 2 - d = 0 := by omega
      simp [hlast, this]
    · have : nt - 2 - d ≠ 0 := by omega
      simp [hlast, this]
      exact Fin.ext (by simp [returnQ]; omega)
  · simp [returnCfg]; congr 1; omega
  · have hidx : nt - 2 - d = nt - 1 - (d + 1) := by omega
    simp [returnCfg, hidx]
  · simp [returnCfg]
    have hdrop :
        (bits a)[nt - 1 - d]'hi :: (bits a).drop (nt - d) =
          (bits a).drop (nt - (d + 1)) := by
      have h1 : nt - (d + 1) = nt - 1 - d := by omega
      have h2 : nt - d = (nt - 1 - d) + 1 := by omega
      rw [h1, List.drop_eq_getElem_cons (i := nt - 1 - d) hi, h2]
    exact congrArg (fun l => l ++ suffix) hdrop

theorem return_prefix {nt : Nat} (hnt : 0 < nt) (a : Fin nt) (d : Nat)
    (hd : d < nt) (H : Int) (left suffix : List (Fin 3)) :
    run (program nt hnt) 2 (List.replicate d false) H
      (returnCfg hnt a 0 hnt left suffix) =
      some (H - d, returnCfg hnt a d hd left suffix) := by
  induction d with
  | zero => simp [run]
  | succ d ih =>
      rw [replicate_concat, run_append, ih (by omega), bind_run,
        step_return hnt a d (by omega)]
      exact congrArg some (Prod.ext (by omega) rfl)

theorem writer_run {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (H : Int) :
    run (program nt hnt) 2 (List.replicate (deadline nt) false) H
      (initial hnt a left suffix) =
      some (H, final a left suffix) := by
  have hw : List.replicate (deadline nt) false =
      List.replicate nt false ++ List.replicate (nt - 1) false := by
    rw [deadline_split hnt, List.replicate_add]
  rw [hw, run_append, write_run, bind_run, return_prefix hnt a (nt - 1) (by omega)]
  refine congrArg some (Prod.ext ?_ (returnCfg_final hnt a left suffix))
  omega

theorem replicate_split (n t : Nat) (ht : t ≤ n) :
    List.replicate n false =
      List.replicate t false ++ List.replicate (n - t) false := by
  conv_lhs => rw [← Nat.add_sub_of_le ht]
  exact List.replicate_add t (n - t) false

theorem replicate_add_run {ns nα : Nat} (p : BoundedProgram ns nα)
    (blank : Fin nα) (n m : Nat) (head : Int) (z : BoundedConfig ns nα)
    {hf : Int} {zf : BoundedConfig ns nα} {hf' : Int}
    {zf' : BoundedConfig ns nα}
    (h1 : run p blank (List.replicate n false) head z = some (hf, zf))
    (h2 : run p blank (List.replicate m false) hf zf = some (hf', zf')) :
    run p blank (List.replicate (n + m) false) head z =
      some (hf', zf') := by
  have hw : List.replicate (n + m) false =
      List.replicate n false ++ List.replicate m false :=
    List.replicate_add n m false
  rw [hw, run_append, h1, bind_run, h2]

theorem growth_append_le {ns nα : Nat} {p : BoundedProgram ns nα}
    {blank : Fin nα} {w1 w2 : List Bool} {h0 hf hm : Int}
    {z0 zf zm : BoundedConfig ns nα} {lg rg lg1 rg1 : Nat}
    (hfull : GrowthRun p blank (w1 ++ w2) h0 z0 hf zf lg rg)
    (hpre : GrowthRun p blank w1 h0 z0 hm zm lg1 rg1) :
    lg1 ≤ lg ∧ rg1 ≤ rg := by
  induction w1 generalizing h0 z0 hm zm lg rg lg1 rg1 hf zf with
  | nil =>
      cases hpre
      omega
  | cons slot rest ih =>
      cases hpre with
      | cons halt rule tail =>
          have hcons :
              GrowthRun p blank (slot :: (rest ++ w2)) h0 z0 hf zf lg rg := by
            simpa [List.cons_append] using hfull
          cases hcons with
          | cons halt' rule' tail' =>
              have ha := Option.some.inj (rule.symm.trans rule')
              subst ha
              have ⟨hL, hR⟩ := ih tail' tail
              constructor <;> omega

theorem cellCount_of_cells {ns : Nat} (q : Fin ns)
    (left tape : List (Fin 3)) (hne : tape ≠ []) :
    cellCount (fromCells q left tape) = left.length + tape.length := by
  cases tape with
  | nil => exact (hne rfl).elim
  | cons _ rest =>
      simp [cellCount, fromCells]; omega

theorem occupied_initial {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) :
    cellCount (initial hnt a left suffix) = occupied nt left suffix := by
  have hne : List.replicate nt (0 : Fin 3) ++ suffix ≠ [] :=
    List.ne_nil_of_length_pos (by simp; omega)
  rw [initial, cellCount_of_cells _ _ _ hne]
  simp [occupied, Nat.add_assoc]

theorem occupied_final {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) :
    cellCount (final a left suffix) = occupied nt left suffix := by
  have hne : cells (encodeOneHot a) ++ suffix ≠ [] :=
    List.ne_nil_of_length_pos (by simp [cells, encodeOneHot_length]; omega)
  rw [final, cellCount_of_cells _ _ _ hne]
  simp [occupied, cells, encodeOneHot_length, Nat.add_assoc]

theorem prefix_head {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (H : Int) (t : Nat)
    (ht : t ≤ deadline nt) :
    ∃ zf,
      run (program nt hnt) 2 (List.replicate t false) H
        (initial hnt a left suffix) = some
          (if t ≤ nt - 1 then H + t
            else H + ((nt - 1 : Nat) : Int) - ((t - nt : Nat) : Int), zf) ∧
        H ≤ (if t ≤ nt - 1 then H + t
          else H + ((nt - 1 : Nat) : Int) - ((t - nt : Nat) : Int)) ∧
        (if t ≤ nt - 1 then H + t
          else H + ((nt - 1 : Nat) : Int) - ((t - nt : Nat) : Int)) ≤
          H + ((nt - 1 : Nat) : Int) := by
  by_cases h1 : t ≤ nt - 1
  · have hk : t < nt := by omega
    refine ⟨writeCfg hnt a t hk left suffix, ?_, ?_, ?_⟩
    · simpa [h1] using write_prefix hnt a t hk H left suffix
    · simp [h1]
    · simp [h1]
  · have hntle : nt ≤ t := by
      have : nt - 1 < t := Nat.not_le.mp h1
      omega
    have hd : t - nt < nt := by
      have : t ≤ 2 * nt - 1 := by simpa [deadline] using ht
      omega
    have hlen : nt + (t - nt) = t := by omega
    have hrun := replicate_add_run (program nt hnt) 2 nt (t - nt) H
      (initial hnt a left suffix) (write_run hnt a H left suffix)
      (return_prefix hnt a (t - nt) hd (H + ((nt - 1 : Nat) : Int)) left suffix)
    refine ⟨returnCfg hnt a (t - nt) hd left suffix, ?_, ?_, ?_⟩
    · simpa [h1, hlen] using hrun
    · simp [h1]; try omega
    · simp [h1]; try omega

theorem final_state {nt : Nat} (a : Fin nt) (left suffix : List (Fin 3)) :
    (final a left suffix).state.val = 0 := by
  simp [final, fromCells_state]

theorem every_raw {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program nt hnt) 2 w H (initial hnt a left suffix) =
      some (hf, zf)) :
    w = List.replicate w.length false ∧
      w.length ≤ deadline nt ∧
      H ≤ hf ∧ hf ≤ H + ((nt - 1 : Nat) : Int) ∧
      cellCount zf = occupied nt left suffix := by
  have hwfalse :=
    successful_zipper_is_false (2 : Fin 3) (program nt hnt)
      (program_falseOnly hnt) hw
  have hlen :=
    successful_zipper_length_le (2 : Fin 3) (program nt hnt)
      (program_falseOnly hnt) (deadline nt) H (initial hnt a left suffix)
      (final a left suffix) H (writer_run hnt a left suffix H)
      (final_state a left suffix) hw
  refine ⟨hwfalse, hlen, ?_⟩
  obtain ⟨zf', hpre, hlo, hhi⟩ := prefix_head hnt a left suffix H w.length hlen
  have hw' : run (program nt hnt) 2 (List.replicate w.length false) H
      (initial hnt a left suffix) = some (hf, zf) := by
    rwa [← hwfalse]
  have heq := hw'.symm.trans hpre
  obtain ⟨hf_eq, zf_eq⟩ := Prod.mk.inj (Option.some.inj heq)
  subst zf
  rw [← hf_eq] at hlo hhi
  refine ⟨hlo, hhi, ?_⟩
  obtain ⟨lg, rg, hG⟩ :=
    every_actual_run (program nt hnt) 2 (List.replicate (deadline nt) false)
      H H (initial hnt a left suffix) (final a left suffix)
      (writer_run hnt a left suffix H)
  have hF := hG.exact_ledger
  have hcnt :
      cellCount (final a left suffix) = cellCount (initial hnt a left suffix) := by
    rw [occupied_final hnt a left suffix, occupied_initial hnt a left suffix]
  have h0 : lg = 0 ∧ rg = 0 := by omega
  have hsplit := replicate_split (deadline nt) w.length hlen
  have hGfull : GrowthRun (program nt hnt) 2
      (List.replicate w.length false ++
        List.replicate (deadline nt - w.length) false)
      H (initial hnt a left suffix) H (final a left suffix) lg rg := by
    simpa [hsplit] using hG
  obtain ⟨lg1, rg1, hG1⟩ :=
    every_actual_run (program nt hnt) 2 (List.replicate w.length false) H hf
      (initial hnt a left suffix) zf' hw'
  have ⟨hleL, hleR⟩ := growth_append_le hGfull hG1
  have hP := hG1.exact_ledger
  have hocc := occupied_initial hnt a left suffix
  omega

theorem every_raw_no_growth {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program nt hnt) 2 w H (initial hnt a left suffix) =
      some (hf, zf)) :
    GrowthRun (program nt hnt) 2 w H (initial hnt a left suffix) hf zf 0 0 := by
  obtain ⟨lg, rg, hg⟩ :=
    every_actual_run (program nt hnt) 2 w H hf (initial hnt a left suffix) zf hw
  have hraw := every_raw hnt a left suffix H hw
  have he := hg.exact_ledger
  have h0 := occupied_initial hnt a left suffix
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg

theorem accepting_word {nt : Nat} (hnt : 0 < nt) (a : Fin nt)
    (left suffix : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig (stateCount nt) 3}
    (hw : run (program nt hnt) 2 w H (initial hnt a left suffix) =
      some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline nt) false ∧ hf = H ∧
      zf = final a left suffix :=
  accepting_zipper_word_eq (2 : Fin 3) (program nt hnt)
    (program_falseOnly hnt) (deadline nt) H (initial hnt a left suffix)
    (final a left suffix) H (writer_run hnt a left suffix H)
    (final_state a left suffix) hw ha

theorem compiled_symbols {nt : Nat} (hnt : 0 < nt) :
    ∀ r ∈ compile (program nt hnt), r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded (program nt hnt) hr
  exact ⟨hb.2.1, hb.2.2.1⟩

theorem writer_spec {nt : Nat} (hnt : 0 < nt) :
    (∀ (a : Fin nt) (left suffix : List (Fin 3)) (H : Int),
      run (program nt hnt) 2 (List.replicate (deadline nt) false) H
        (initial hnt a left suffix) =
      some (H, final a left suffix)) ∧
    (∀ (a : Fin nt) (left suffix : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig (stateCount nt) 3),
      run (program nt hnt) 2 w H (initial hnt a left suffix) = some (hf, zf) →
      w = List.replicate w.length false ∧
        w.length ≤ deadline nt ∧
        H ≤ hf ∧ hf ≤ H + ((nt - 1 : Nat) : Int) ∧
        cellCount zf = occupied nt left suffix ∧
        GrowthRun (program nt hnt) 2 w H (initial hnt a left suffix) hf zf 0 0) ∧
    (∀ (a : Fin nt) (left suffix : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig (stateCount nt) 3),
      run (program nt hnt) 2 w H (initial hnt a left suffix) = some (hf, zf) →
      zf.state.val = 0 →
      w = List.replicate (deadline nt) false ∧ hf = H ∧
        zf = final a left suffix) ∧
    (∀ r ∈ compile (program nt hnt), r.read < 3 ∧ r.action.write < 3) := by
  refine ⟨writer_run hnt, ?_, ?_, compiled_symbols hnt⟩
  · intro a left suffix H w hf zf hw
    have h := every_raw hnt a left suffix H hw
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      every_raw_no_growth hnt a left suffix H hw⟩
  · intro a left suffix H w hf zf hw ha
    exact accepting_word hnt a left suffix H hw ha

end PakFixedPolyomino.ULogTernaryOneHotBlockWriter
