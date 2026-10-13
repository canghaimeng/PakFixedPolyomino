import PakFixedPolyomino.PakFixedShapeNondeterministicRound
import PakFixedPolyomino.PakFixedShapeFlaggedPreparation
import PakFixedPolyomino.StandardBitHalve

/-! Actual preparation, nondeterministic choice/check and physical flag strip
on one common finite alphabet. Every cost and clean tape theorem is supplied
internally; the generic feedback compiler is an independently owned module. -/
namespace PakFixedPolyomino.PakFixedShapeNondeterministicPhases
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeNondeterministicRound (Implementation)
open PakFixedShapeFiniteLabelRound (L checkedRound labelAt)
open PakFixedShapeFlaggedPreparation (prepare)

theorem exists_preparation : ∃ d : Implementation,
    ComputesWithin d.machine prepare (fun n => d.polynomial.eval n) := by
  obtain ⟨ns,nt,P,p,h⟩ := PakFixedShapeFlaggedPreparation.prepare_polyBitTime
  exact ⟨⟨ns,nt,P,p⟩,h⟩
def preparation : Implementation := Classical.choose exists_preparation
theorem preparation_computes : ComputesWithin preparation.machine prepare
    (fun n => preparation.polynomial.eval n) := Classical.choose_spec exists_preparation

def prepareBase := StandardMachineAlphabetRelabel.machine preparation.machine
  (StandardMachineAlphabetRelabel.mapA (ntB:=4) preparation.machine)
def stripBase := StandardMachineAlphabetRelabel.machine StandardBitHalve.machine
  (StandardMachineAlphabetRelabel.mapB (ntA:=preparation.alphabet) StandardBitHalve.machine)
def extraAlphabet := preparation.alphabet+4+3
def roundAlphabet := 3+PakFixedShapeNondeterministicRound.implementation.alphabet+3
def commonMap := StandardMachineAlphabetRelabel.mapB (ntA:=roundAlphabet) prepareBase
def prepareMachine := StandardMachineAlphabetRelabel.machine prepareBase commonMap
def stripMachine := StandardMachineAlphabetRelabel.machine stripBase commonMap
def roundMachine := StandardMachineNondeterministicCommonAlphabet.left (ntB:=extraAlphabet)
  PakFixedShapeNondeterministicRound.machine (StandardBitFiniteChoiceContinuation.positive L)
def roundMap := StandardMachineNondeterministicCommonAlphabet.leftMap (ntB:=extraAlphabet)
  PakFixedShapeNondeterministicRound.machine (StandardBitFiniteChoiceContinuation.positive L)

theorem prepare_computes : ComputesWithin prepareMachine prepare
    (fun n => preparation.polynomial.eval n) := by
  apply StandardMachineAlphabetRelabel.computes
  exact StandardMachineAlphabetRelabel.computes preparation.machine _ _ _ preparation_computes

theorem strip_computes : ComputesWithin stripMachine (fun raw : List Bool => raw.tail) (fun n => 4*n+4) := by
  apply StandardMachineAlphabetRelabel.computes
  exact StandardMachineAlphabetRelabel.computes StandardBitHalve.machine _ _ _ StandardBitHalve.halve_computes

theorem base_codes : stripBase.blank=prepareBase.blank ∧ stripBase.zero=prepareBase.zero ∧
    stripBase.one=prepareBase.one := by
  obtain ⟨pb,pz,po⟩ := StandardMachineAlphabetRelabel.codes_A (ntB:=4) preparation.machine
  obtain ⟨hb,hz,ho⟩ := StandardMachineAlphabetRelabel.codes_B (ntA:=preparation.alphabet) StandardBitHalve.machine
  exact ⟨hb.trans pb.symm,hz.trans pz.symm,ho.trans po.symm⟩

theorem codes :
    roundMachine.blank=prepareMachine.blank ∧ roundMachine.zero=prepareMachine.zero ∧
    roundMachine.one=prepareMachine.one ∧ stripMachine.blank=prepareMachine.blank ∧
    stripMachine.zero=prepareMachine.zero ∧ stripMachine.one=prepareMachine.one := by
  obtain ⟨hb,hz,ho⟩ := StandardMachineNondeterministicCommonAlphabet.same_codes
    PakFixedShapeNondeterministicRound.machine prepareBase (StandardBitFiniteChoiceContinuation.positive L)
  obtain ⟨sb,sz,so⟩ := base_codes
  exact ⟨hb,hz,ho,congrArg commonMap.encode sb,congrArg commonMap.encode sz,congrArg commonMap.encode so⟩

theorem round_prefix_bound (raw : List Bool) : RunsAtMost roundMachine raw
    (PakFixedShapeNondeterministicRound.polynomial.eval raw.length) :=
  StandardMachineNondeterministicCommonAlphabet.left_prefix_bound
    PakFixedShapeNondeterministicRound.machine (StandardBitFiniteChoiceContinuation.positive L) raw _
    (PakFixedShapeNondeterministicRound.all_prefix_bound raw)

theorem round_accepted_iff (raw : List Bool) (slots : List (Fin (L+1))) :
    Accepted roundMachine raw slots ↔ ∃ i : Fin L,slots=PakFixedShapeNondeterministicRound.path raw i := by
  unfold roundMachine
  rw [StandardMachineNondeterministicCommonAlphabet.left_accepted_iff]
  exact PakFixedShapeNondeterministicRound.accepted_iff_path raw slots

theorem relabel_clean {ns nt mt nb : Nat} (M : Machine ns nt nb)
    (E : StandardMachineAlphabetRelabel.AlphabetMap nt mt) (y : List Bool) (c : Configuration ns nt)
    (hh : c.head=0) (ht : c.tape=inputTape M y) :
    (StandardMachineAlphabetRelabel.config E c).head=0 ∧
      (StandardMachineAlphabetRelabel.config E c).tape=inputTape (StandardMachineAlphabetRelabel.machine M E) y := by
  refine ⟨hh,?_⟩
  funext z
  simp only [StandardMachineAlphabetRelabel.config,ht,inputTape,StandardMachineAlphabetRelabel.machine]
  split_ifs <;> rfl

theorem round_path_run (raw : List Bool) (i : Fin L) :
    run roundMachine (PakFixedShapeNondeterministicRound.path raw i) (initial roundMachine raw)=
      some ⟨roundMachine.accept,0,inputTape roundMachine (checkedRound (labelAt i) raw)⟩ := by
  apply (StandardMachineNondeterministicCommonAlphabet.left_all_raw_inverse
    PakFixedShapeNondeterministicRound.machine (StandardBitFiniteChoiceContinuation.positive L) raw _ _).mpr
  refine ⟨_,PakFixedShapeNondeterministicRound.path_run raw i,?_⟩
  apply StandardBitMachineComposition.config_ext
  · rfl
  · rfl
  · exact (relabel_clean PakFixedShapeNondeterministicRound.machine roundMap
      (checkedRound (labelAt i) raw) _ rfl rfl).2.symm

theorem round_accepted_clean (raw : List Bool) (slots : List (Fin (L+1)))
    (out : Configuration (StandardBitFiniteChoicePrefix.ns L+PakFixedShapeNondeterministicRound.implementation.states+2)
      (roundAlphabet+extraAlphabet+3)) (hr : run roundMachine slots (initial roundMachine raw)=some out)
    (ha : out.state=roundMachine.accept) :
    ∃ i : Fin L,slots=PakFixedShapeNondeterministicRound.path raw i ∧ out.head=0 ∧
      out.tape=inputTape roundMachine (checkedRound (labelAt i) raw) := by
  obtain ⟨i,hi⟩ := (round_accepted_iff raw slots).mp ((accepted_iff _ _ _).mpr ⟨out,hr,ha⟩)
  rw [hi,round_path_run] at hr
  have he := Option.some.inj hr
  subst out
  exact ⟨i,hi,rfl,rfl⟩

theorem nondeterministic_phases_spec :
    ComputesWithin prepareMachine prepare (fun n => preparation.polynomial.eval n) ∧
    ComputesWithin stripMachine (fun raw : List Bool => raw.tail) (fun n => 4*n+4) ∧
    (∀ raw,RunsAtMost roundMachine raw (PakFixedShapeNondeterministicRound.polynomial.eval raw.length)) ∧
    ∀ raw slots,Accepted roundMachine raw slots ↔ ∃ i : Fin L,slots=PakFixedShapeNondeterministicRound.path raw i :=
  ⟨prepare_computes,strip_computes,round_prefix_bound,round_accepted_iff⟩
end
end PakFixedPolyomino.PakFixedShapeNondeterministicPhases
