import PakFixedPolyomino.StandardBitRetainedPairBitTime
import PakFixedPolyomino.StandardBitPairFirstCompaction

/-! A physical polynomial-time computation can retain EVERY original input
bit beside its result. The ordinary prepend, projection, loader, pairing and
cleanup machines supply the construction internally, including empty input
and arbitrary high zero bits. This is a component for arithmetic stacks;
it does not provide a variable-iteration or weighted-DP compiler. -/
namespace PakFixedPolyomino.StandardBitRetainedInput
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitTimeComposition (polyBitTime_comp)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)

def fork (f : List Bool → List Bool) (raw : List Bool) : List Bool :=
  pairBits (f raw) raw

def duplicate (raw : List Bool) : List Bool := fork id raw

theorem empty_first (raw : List Bool) : false :: raw=pairBits [] raw := rfl

theorem fork_compiler (f : List Bool → List Bool) :
    StandardBitRetainedPairBitTime.lifting (f ∘ secondBits) ∘ List.cons false=fork f := by
  funext raw
  simp only [Function.comp_apply,empty_first,StandardBitRetainedPairBitTime.lifting_pair,
    secondBits_pair,fork]

theorem fork_polyBitTime (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (fork f) := by
  have hsource : PolyBitTime (f ∘ secondBits) := polyBitTime_comp secondBits_polyBitTime hf
  have h := polyBitTime_comp (StandardBitPrepend.prepend_polyBitTime false)
    (StandardBitRetainedPairBitTime.lifting_polyBitTime _ hsource)
  rwa [fork_compiler] at h

theorem fork_first (f : List Bool → List Bool) (raw : List Bool) :
    firstBits (fork f raw)=f raw := firstBits_pair _ _

theorem fork_second (f : List Bool → List Bool) (raw : List Bool) :
    secondBits (fork f raw)=raw := secondBits_pair _ _

theorem fork_unpair (f : List Bool → List Bool) (raw : List Bool) :
    unpairBits (fork f raw)=some (f raw,raw) := unpair_pairBits _ _

theorem fork_length (f : List Bool → List Bool) (raw : List Bool) :
    (fork f raw).length=2*(f raw).length+1+raw.length := pairBits_length _ _

theorem fork_injective (f : List Bool → List Bool) : Function.Injective (fork f) := by
  intro x y h
  have := congrArg secondBits h
  simpa only [fork_second] using this

theorem duplicate_polyBitTime : PolyBitTime duplicate := fork_polyBitTime id identity_polyBitTime

theorem duplicate_pair (raw : List Bool) : duplicate raw=pairBits raw raw := rfl

theorem duplicate_length (raw : List Bool) : (duplicate raw).length=3*raw.length+1 := by
  rw [duplicate,fork_length]
  simp only [id_eq]
  omega

theorem duplicate_injective : Function.Injective duplicate := fork_injective id

theorem fork_spec (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (fork f) ∧
    (∀ raw,unpairBits (fork f raw)=some (f raw,raw)) ∧
    (∀ raw,firstBits (fork f raw)=f raw ∧ secondBits (fork f raw)=raw) ∧
    (∀ raw,(fork f raw).length=2*(f raw).length+1+raw.length) ∧
    Function.Injective (fork f) :=
  ⟨fork_polyBitTime f hf,fork_unpair f,fun raw => ⟨fork_first f raw,fork_second f raw⟩,
    fork_length f,fork_injective f⟩

theorem duplicate_spec :
    PolyBitTime duplicate ∧
    (∀ raw,duplicate raw=pairBits raw raw) ∧
    (∀ raw,unpairBits (duplicate raw)=some (raw,raw)) ∧
    (∀ raw,(duplicate raw).length=3*raw.length+1) ∧
    Function.Injective duplicate :=
  ⟨duplicate_polyBitTime,duplicate_pair,fork_unpair id,duplicate_length,duplicate_injective⟩

end PakFixedPolyomino.StandardBitRetainedInput
