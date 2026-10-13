import PakFixedPolyomino.StandardMachineAlphabetRelabel
import PakFixedPolyomino.StandardMachineDeterministicBranchEmbedding

/-! A common physical alphabet for an arbitrary ND phase and a deterministic
continuation. The deterministic view supplies only letter-code data to the
existing injective alphabet maps. The actual ND machine retains EVERY slot. -/
namespace PakFixedPolyomino.StandardMachineNondeterministicCommonAlphabet
open StandardNondeterministicMachine StandardBitTime
open StandardMachineAlphabetRelabel (AlphabetMap config)
variable {nsA nsB ntA ntB nb : Nat}

def codeView (M : Machine nsA ntA nb) (hnb : 0<nb) : DeterministicMachine nsA ntA where
  rule q a _ := M.rule q a (StandardMachineDeterministicBranchEmbedding.zeroSlot hnb)
  start := M.start
  accept := M.accept
  reject := M.reject
  accept_ne_reject := M.accept_ne_reject
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal a _ := M.accept_terminal a _
  reject_terminal a _ := M.reject_terminal a _

def leftMap (M : Machine nsA ntA nb) (hnb : 0<nb) : AlphabetMap ntA (ntA+ntB+3) :=
  StandardMachineAlphabetRelabel.mapA (codeView M hnb)
def left (M : Machine nsA ntA nb) (hnb : 0<nb) : Machine nsA (ntA+ntB+3) nb :=
  StandardMachineAlphabetRelabel.machine M (leftMap M hnb)
def right (N : DeterministicMachine nsB ntB) : DeterministicMachine nsB (ntA+ntB+3) :=
  StandardMachineAlphabetRelabel.machine N (StandardMachineAlphabetRelabel.mapB N)

theorem left_codes (M : Machine nsA ntA nb) (hnb : 0<nb) :
    (left (ntB:=ntB) M hnb).blank=2 ∧ (left (ntB:=ntB) M hnb).zero=0 ∧
      (left (ntB:=ntB) M hnb).one=1 := by
  exact StandardMachineAlphabetRelabel.codes_A (ntB:=ntB) (codeView M hnb)

theorem same_codes (M : Machine nsA ntA nb) (N : DeterministicMachine nsB ntB) (hnb : 0<nb) :
    (left (ntB:=ntB) M hnb).blank=(right (ntA:=ntA) N).blank ∧
    (left (ntB:=ntB) M hnb).zero=(right (ntA:=ntA) N).zero ∧
    (left (ntB:=ntB) M hnb).one=(right (ntA:=ntA) N).one := by
  obtain ⟨ab,az,ao⟩ := left_codes (ntB:=ntB) M hnb
  obtain ⟨bb,bz,bo⟩ := StandardMachineAlphabetRelabel.codes_B (ntA:=ntA) N
  exact ⟨ab.trans bb.symm,az.trans bz.symm,ao.trans bo.symm⟩

theorem left_all_raw_inverse (M : Machine nsA ntA nb) (hnb : 0<nb)
    (raw : List Bool) (slots : List (Fin nb)) (out : Configuration nsA (ntA+ntB+3)) :
    run (left M hnb) slots (initial (left M hnb) raw)=some out ↔
      ∃ source,run M slots (initial M raw)=some source ∧ out=config (leftMap M hnb) source :=
  StandardMachineAlphabetRelabel.all_raw_run_inverse M (leftMap M hnb) raw slots out

theorem left_accepted_iff (M : Machine nsA ntA nb) (hnb : 0<nb)
    (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (left (ntB:=ntB) M hnb) raw slots ↔ Accepted M raw slots :=
  StandardMachineAlphabetRelabel.accepted_iff M (leftMap M hnb) raw slots

theorem left_prefix_bound (M : Machine nsA ntA nb) (hnb : 0<nb)
    (raw : List Bool) (bound : Nat) (h : RunsAtMost M raw bound) :
    RunsAtMost (left (ntB:=ntB) M hnb) raw bound := by
  intro slots out hr
  obtain ⟨source,hs,_⟩ := (left_all_raw_inverse M hnb raw slots out).mp hr
  exact h slots source hs

theorem right_computes (N : DeterministicMachine nsB ntB) (f : List Bool → List Bool)
    (p : Nat → Nat) (h : ComputesWithin N f p) :
    ComputesWithin (right (ntA:=ntA) N) f p :=
  StandardMachineAlphabetRelabel.computes N (StandardMachineAlphabetRelabel.mapB N) f p h

theorem left_clean (M : Machine nsA ntA nb) (hnb : 0<nb) (y : List Bool) :
    config (leftMap (ntB:=ntB) M hnb) ⟨M.accept,0,inputTape M y⟩=
      ⟨(left (ntB:=ntB) M hnb).accept,0,inputTape (left (ntB:=ntB) M hnb) y⟩ := by
  apply StandardBitMachineComposition.config_ext
  · rfl
  · rfl
  · funext z
    simp only [config,inputTape,left,StandardMachineAlphabetRelabel.machine]
    split_ifs <;> rfl

theorem nondeterministic_common_alphabet_spec (M : Machine nsA ntA nb)
    (N : DeterministicMachine nsB ntB) (hnb : 0<nb) :
    (left (ntB:=ntB) M hnb).blank=(right (ntA:=ntA) N).blank ∧
    (left (ntB:=ntB) M hnb).zero=(right (ntA:=ntA) N).zero ∧
    (left (ntB:=ntB) M hnb).one=(right (ntA:=ntA) N).one ∧
    (∀ raw slots,Accepted (left (ntB:=ntB) M hnb) raw slots ↔ Accepted M raw slots) := by
  obtain ⟨hb,hz,ho⟩ := same_codes M N hnb
  exact ⟨hb,hz,ho,left_accepted_iff M hnb⟩

end PakFixedPolyomino.StandardMachineNondeterministicCommonAlphabet
