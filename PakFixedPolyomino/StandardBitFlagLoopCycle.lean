import PakFixedPolyomino.StandardBitFlagLoopControl
import PakFixedPolyomino.StandardMachineAlphabetRelabel
import PakFixedPolyomino.StandardBitHalve

/-! An ordinary physical loop cycle. The source body emits flag :: payload;
the existing halving machine removes the flag. All alphabets, stripping,
control handoffs and clean next-input configurations are internal. -/
namespace PakFixedPolyomino.StandardBitFlagLoopCycle
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition (config_ext)
variable {ns nt : Nat}

def source (M : DeterministicMachine ns nt) : DeterministicMachine ns (nt+7) :=
  StandardMachineAlphabetRelabel.machine M (StandardMachineAlphabetRelabel.mapA (ntB:=4) M)

def strip (M : DeterministicMachine ns nt) : DeterministicMachine 10 (nt+7) :=
  StandardMachineAlphabetRelabel.machine StandardBitHalve.machine
    (StandardMachineAlphabetRelabel.mapB (ntA:=nt) StandardBitHalve.machine)

def machine (M : DeterministicMachine ns nt) : DeterministicMachine (ns+25) (nt+7) :=
  StandardBitFlagLoopControl.machine (source M) (strip M)

def startConfig (M : DeterministicMachine ns nt) (x : List Bool) : Configuration (ns+25) (nt+7) :=
  StandardBitFlagLoopControl.bodyConfig (nh:=10) (initial (source M) x)

def finalConfig (M : DeterministicMachine ns nt) (y : List Bool) : Configuration (ns+25) (nt+7) :=
  ⟨0,0,inputTape (machine M) y⟩

theorem initial_eq (M : DeterministicMachine ns nt) (x : List Bool) :
    initial (machine M) x=startConfig M x := rfl

theorem input_source (M : DeterministicMachine ns nt) (x : List Bool) :
    inputTape (machine M) x=inputTape (source M) x := rfl

theorem input_same (M : DeterministicMachine ns nt) (x : List Bool) :
    inputTape (source M) x=inputTape (strip M) x := by
  have hc := StandardMachineAlphabetRelabel.codes_A (ntB:=4) M
  have hh := StandardMachineAlphabetRelabel.codes_B (ntA:=nt) StandardBitHalve.machine
  funext z
  simp only [inputTape,source,strip,hc.1,hc.2.1,hc.2.2,hh.1,hh.2.1,hh.2.2]

theorem source_computes (M : DeterministicMachine ns nt)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p) :
    ComputesWithin (source M) f p := StandardMachineAlphabetRelabel.computes M _ f p hf

theorem strip_computes (M : DeterministicMachine ns nt) :
    ComputesWithin (strip M) (fun x : List Bool => x.tail) (fun n => 4*n+4) :=
  StandardMachineAlphabetRelabel.computes StandardBitHalve.machine _ _ _ StandardBitHalve.halve_computes

theorem flag_read (M : DeterministicMachine ns nt) (w : List Bool) :
    inputTape (source M) w 0=(source M).one ↔ w.headD false=true := by
  cases w with
  | nil => simp [inputTape,(source M).blank_ne_one]
  | cons b w => cases b <;> simp [inputTape,(source M).zero_ne_one]

theorem next_eq (M : DeterministicMachine ns nt) (y : List Bool)
    (out : Configuration 10 (nt+7)) (ho : Output (strip M) y out) :
    StandardBitFlagLoopControl.bodyConfig (nh:=10) ⟨(source M).start,out.head,out.tape⟩=
      startConfig M y := by
  apply config_ext
  · rfl
  · exact ho.2.1
  · exact ho.2.2.trans (input_same M y).symm

theorem final_eq (M : DeterministicMachine ns nt) (y : List Bool)
    (out : Configuration 10 (nt+7)) (ho : Output (strip M) y out) :
    (⟨0,out.head,out.tape⟩ : Configuration (ns+25) (nt+7))=finalConfig M y := by
  apply config_ext
  · rfl
  · exact ho.2.1
  · change out.tape = inputTape (machine M) y
    rw [input_source]
    exact ho.2.2.trans (input_same M y).symm

theorem final_output (M : DeterministicMachine ns nt) (y : List Bool) :
    Output (machine M) y (finalConfig M y) := ⟨rfl,rfl,rfl⟩

theorem cycle_run (M : DeterministicMachine ns nt)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) :
    ∃ t, t≤5*p x.length+4*x.length+11 ∧
      run (machine M) (ticks t) (startConfig M x)=some
        (if (f x).headD false then startConfig M (f x).tail else finalConfig M (f x).tail) := by
  obtain ⟨n,c,hn,hr,ho⟩ := source_computes M f p hf x
  obtain ⟨m,out,hm,hs,hout⟩ := strip_computes M (f x)
  have hlen := ComputesWithin.output_length M f p hf x
  change m ≤ 4*(f x).length+4 at hm
  have hstart : (⟨(strip M).start,c.head,c.tape⟩ : Configuration 10 (nt+7))=
      initial (strip M) (f x) := by
    apply config_ext
    · rfl
    · exact ho.2.1
    · exact ho.2.2.trans (input_same M (f x))
  have hstrip : run (strip M) (ticks m) ⟨(strip M).start,c.head,c.tape⟩=some out := by
    rw [hstart]
    exact hs
  refine ⟨n+m+3,by omega,?_⟩
  cases hb : (f x).headD false with
  | false =>
    have hp : c.tape c.head≠(source M).one := by
      rw [ho.2.1,ho.2.2]
      intro he
      have he' := (flag_read M (f x)).mp he
      rw [hb] at he'
      cases he'
    have h := StandardBitFlagLoopControl.cycle_false (source M) (strip M)
      (initial (source M) x) c out n m hr ho.1 hp hstrip hout.1
    rw [final_eq M (f x).tail out hout] at h
    simpa only [machine,startConfig,hb,Bool.false_eq_true,if_false] using h
  | true =>
    have hp : c.tape c.head=(source M).one := by
      rw [ho.2.1,ho.2.2,flag_read]
      exact hb
    have h := StandardBitFlagLoopControl.cycle_true (source M) (strip M)
      (initial (source M) x) c out n m hr ho.1 hp hstrip hout.1
    rw [next_eq M (f x).tail out hout] at h
    simpa only [machine,startConfig,hb,ite_true] using h

end PakFixedPolyomino.StandardBitFlagLoopCycle
