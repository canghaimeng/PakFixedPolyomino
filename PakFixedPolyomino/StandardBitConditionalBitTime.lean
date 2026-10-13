import PakFixedPolyomino.StandardBitProtectedConditional
import PakFixedPolyomino.StandardMachineAlphabetRelabel

/-! Polynomial ordinary tape-time closure under Boolean conditional control.
The three source alphabets are internally relabeled to common literal codes;
the compiler physically restores the original input before the chosen core. -/
namespace PakFixedPolyomino.StandardBitConditionalBitTime
open StandardNondeterministicMachine StandardBitTime
open StandardBitProtectedConditional (conditional SameCodes conditional_bit_spec)

theorem conditional_polyBitTime (b : List Bool → Bool) (f g : List Bool → List Bool)
    (hb : PolyBitTime (fun x => [b x])) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (conditional b f g) := by
  obtain ⟨nsP,ntP,P,p,hP⟩ := hb
  obtain ⟨nsF,ntF,F,q,hF⟩ := hf
  obtain ⟨nsT,ntT,T,r,hT⟩ := hg
  let F0 := StandardMachineAlphabetRelabel.machine F
    (StandardMachineAlphabetRelabel.mapA (ntB:=ntT) F)
  let T0 := StandardMachineAlphabetRelabel.machine T
    (StandardMachineAlphabetRelabel.mapB (ntA:=ntF) T)
  let P1 := StandardMachineAlphabetRelabel.machine P
    (StandardMachineAlphabetRelabel.mapA (ntB:=ntF+ntT+3) P)
  let F1 := StandardMachineAlphabetRelabel.machine F0
    (StandardMachineAlphabetRelabel.mapB (ntA:=ntP) F0)
  let T1 := StandardMachineAlphabetRelabel.machine T0
    (StandardMachineAlphabetRelabel.mapB (ntA:=ntP) T0)
  have hP1 : ComputesWithin P1 (fun x => [b x]) (fun k => p.eval k) :=
    StandardMachineAlphabetRelabel.computes P _ _ _ hP
  have hF0 : ComputesWithin F0 f (fun k => q.eval k) :=
    StandardMachineAlphabetRelabel.computes F _ _ _ hF
  have hT0 : ComputesWithin T0 g (fun k => r.eval k) :=
    StandardMachineAlphabetRelabel.computes T _ _ _ hT
  have hF1 : ComputesWithin F1 f (fun k => q.eval k) :=
    StandardMachineAlphabetRelabel.computes F0 _ _ _ hF0
  have hT1 : ComputesWithin T1 g (fun k => r.eval k) :=
    StandardMachineAlphabetRelabel.computes T0 _ _ _ hT0
  have cp := StandardMachineAlphabetRelabel.codes_A (ntB:=ntF+ntT+3) P
  have cf := StandardMachineAlphabetRelabel.codes_B (ntA:=ntP) F0
  have ct := StandardMachineAlphabetRelabel.codes_B (ntA:=ntP) T0
  have hcf : SameCodes P1 F1 :=
    ⟨cp.1.trans cf.1.symm,cp.2.1.trans cf.2.1.symm,cp.2.2.trans cf.2.2.symm⟩
  have hct : SameCodes P1 T1 :=
    ⟨cp.1.trans ct.1.symm,cp.2.1.trans ct.2.1.symm,cp.2.2.trans ct.2.2.symm⟩
  exact (conditional_bit_spec P1 F1 T1 hcf hct b f g p q r hP1 hF1 hT1).1

end PakFixedPolyomino.StandardBitConditionalBitTime
