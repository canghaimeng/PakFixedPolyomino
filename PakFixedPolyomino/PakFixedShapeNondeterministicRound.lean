import PakFixedPolyomino.StandardBitFiniteChoiceContinuation
import PakFixedPolyomino.PakFixedShapeFiniteLabelRound

/-! ONE fixed ordinary nondeterministic choice/check phase for the ORIGINAL
tile family. Every label has one raw accepting phase path, whose exact clean
output carries the valid/invalid flag. The feedback control rejects false;
this phase count alone is not the square tiling count. -/
namespace PakFixedPolyomino.PakFixedShapeNondeterministicRound
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeFiniteLabelRound (L round checkedRound labelAt)

structure Implementation where
  states : Nat
  alphabet : Nat
  machine : DeterministicMachine states alphabet
  polynomial : Polynomial Nat

theorem exists_implementation : ∃ d : Implementation,
    ComputesWithin d.machine round (fun n => d.polynomial.eval n) := by
  obtain ⟨ns,nt,N,p,h⟩ := PakFixedShapeFiniteLabelRound.round_polyBitTime
  exact ⟨⟨ns,nt,N,p⟩,h⟩

def implementation : Implementation := Classical.choose exists_implementation

theorem implementation_computes : ComputesWithin implementation.machine round
    (fun n => implementation.polynomial.eval n) := Classical.choose_spec exists_implementation

def machine := StandardBitFiniteChoiceContinuation.machine implementation.machine L
def polynomial := StandardBitFiniteChoiceContinuation.bound L implementation.polynomial
def path (raw : List Bool) (i : Fin L) := StandardBitFiniteChoiceContinuation.path
  implementation.machine L round implementation.polynomial implementation_computes raw i

theorem all_prefix_bound (raw : List Bool) : RunsAtMost machine raw (polynomial.eval raw.length) :=
  StandardBitFiniteChoiceContinuation.all_prefix_bound implementation.machine L round
    implementation.polynomial implementation_computes raw

theorem accepted_iff_path (raw : List Bool) (slots : List (Fin (L+1))) :
    Accepted machine raw slots ↔ ∃ i : Fin L,slots=path raw i :=
  StandardBitFiniteChoiceContinuation.accepted_iff_path implementation.machine L round
    implementation.polynomial implementation_computes raw slots

theorem path_injective (raw : List Bool) : Function.Injective (path raw) :=
  StandardBitFiniteChoiceContinuation.path_injective implementation.machine L round
    implementation.polynomial implementation_computes raw

theorem path_run (raw : List Bool) (i : Fin L) :
    run machine (path raw i) (initial machine raw)=
      some ⟨machine.accept,0,inputTape machine (checkedRound (labelAt i) raw)⟩ := by
  simpa only [machine,path,StandardBitFiniteChoiceContinuation.input,PakFixedShapeFiniteLabelRound.round_code] using
    StandardBitFiniteChoiceContinuation.path_run implementation.machine L round
      implementation.polynomial implementation_computes raw i

theorem accepted_clean (raw : List Bool) (slots : List (Fin (L+1))) (out : Configuration
    (StandardBitFiniteChoicePrefix.ns L+implementation.states+2) (3+implementation.alphabet+3))
    (hr : run machine slots (initial machine raw)=some out) (ha : out.state=machine.accept) :
    ∃ i : Fin L,slots=path raw i ∧ out.head=0 ∧
      out.tape=inputTape machine (checkedRound (labelAt i) raw) := by
  simpa only [machine,path,StandardBitFiniteChoiceContinuation.input,PakFixedShapeFiniteLabelRound.round_code] using
    StandardBitFiniteChoiceContinuation.accepted_clean implementation.machine L round
      implementation.polynomial implementation_computes raw slots out hr ha

theorem count_labels (raw : List Bool) : acceptingCount machine raw (polynomial.eval raw.length)=L :=
  StandardBitFiniteChoiceContinuation.count_eq implementation.machine L round
    implementation.polynomial implementation_computes raw

theorem nondeterministic_round_spec :
    (∀ raw,RunsAtMost machine raw (polynomial.eval raw.length)) ∧
    (∀ raw slots,Accepted machine raw slots ↔ ∃ i : Fin L,slots=path raw i) ∧
    (∀ raw,Function.Injective (path raw)) ∧
    (∀ raw i,run machine (path raw i) (initial machine raw)=
      some ⟨machine.accept,0,inputTape machine (checkedRound (labelAt i) raw)⟩) ∧
    ∀ raw,acceptingCount machine raw (polynomial.eval raw.length)=L :=
  ⟨all_prefix_bound,accepted_iff_path,path_injective,path_run,count_labels⟩
end
end PakFixedPolyomino.PakFixedShapeNondeterministicRound
