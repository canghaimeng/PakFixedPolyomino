import PakFixedPolyomino.StandardBitRetainedFirstBitTime
import PakFixedPolyomino.StandardBitRetainedInput

/-! Physical pairing of two computed operands. All compilers below use
ordinary finite tape machines, complete input/output tapes and actual
polynomial tick counts inherited from the proved pairing and composition
machines. Malformed internal pairs have explicit empty-field defaults;
the domain remains EVERY raw binary word. Dynamic iteration is separate. -/
namespace PakFixedPolyomino.StandardBitPairMaps
open StandardBitTime StandardBitMetric
open StandardBitTimeComposition (polyBitTime_comp)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open StandardBitRetainedInput (fork fork_polyBitTime)

def swap : List Bool → List Bool := StandardBitRetainedFirstBitTime.lifting secondBits
def mapFirst (f : List Bool → List Bool) : List Bool → List Bool :=
  StandardBitRetainedPairBitTime.lifting (f ∘ firstBits)
def mapSecond (f : List Bool → List Bool) : List Bool → List Bool := swap ∘ mapFirst f ∘ swap
def parallel (f g : List Bool → List Bool) : List Bool → List Bool := mapSecond g ∘ fork f

theorem swap_pair (x y : List Bool) : swap (pairBits x y)=pairBits y x := by
  simp only [swap,StandardBitRetainedFirstBitTime.lifting_pair,secondBits_pair]

theorem swap_none (raw : List Bool) (h : unpairBits raw=none) : swap raw=[false] := by
  rw [swap,StandardBitRetainedFirstBitTime.lifting_none _ raw h]
  rfl

theorem swap_polyBitTime : PolyBitTime swap :=
  StandardBitRetainedFirstBitTime.lifting_polyBitTime _ secondBits_polyBitTime

theorem swap_twice_pair (x y : List Bool) : swap (swap (pairBits x y))=pairBits x y := by
  rw [swap_pair,swap_pair]

theorem mapFirst_pair (f : List Bool → List Bool) (x y : List Bool) :
    mapFirst f (pairBits x y)=pairBits (f x) y := by
  simp only [mapFirst,StandardBitRetainedPairBitTime.lifting_pair,Function.comp_apply,firstBits_pair]

theorem mapFirst_none (f : List Bool → List Bool) (raw : List Bool) (h : unpairBits raw=none) :
    mapFirst f raw=pairBits (f []) [] := by
  rw [mapFirst,StandardBitRetainedPairBitTime.lifting_none _ raw h]
  rfl

theorem mapFirst_polyBitTime (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (mapFirst f) :=
  StandardBitRetainedPairBitTime.lifting_polyBitTime _ (polyBitTime_comp first_polyBitTime hf)

theorem mapSecond_pair (f : List Bool → List Bool) (x y : List Bool) :
    mapSecond f (pairBits x y)=pairBits x (f y) := by
  simp only [mapSecond,Function.comp_apply,swap_pair,mapFirst_pair]

theorem mapSecond_none (f : List Bool → List Bool) (raw : List Bool) (h : unpairBits raw=none) :
    mapSecond f raw=pairBits [] (f []) := by
  simp only [mapSecond,Function.comp_apply,swap_none raw h]
  change swap (mapFirst f (pairBits [] []))=pairBits [] (f [])
  rw [mapFirst_pair,swap_pair]

theorem mapSecond_polyBitTime (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (mapSecond f) :=
  polyBitTime_comp (polyBitTime_comp swap_polyBitTime (mapFirst_polyBitTime f hf)) swap_polyBitTime

theorem parallel_pair (f g : List Bool → List Bool) (raw : List Bool) :
    parallel f g raw=pairBits (f raw) (g raw) := mapSecond_pair g _ _

theorem parallel_unpair (f g : List Bool → List Bool) (raw : List Bool) :
    unpairBits (parallel f g raw)=some (f raw,g raw) := by rw [parallel_pair,unpair_pairBits]

theorem parallel_length (f g : List Bool → List Bool) (raw : List Bool) :
    (parallel f g raw).length=2*(f raw).length+1+(g raw).length := by rw [parallel_pair,pairBits_length]

theorem parallel_polyBitTime (f g : List Bool → List Bool) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (parallel f g) := polyBitTime_comp (fork_polyBitTime f hf) (mapSecond_polyBitTime g hg)

theorem swap_spec :
    PolyBitTime swap ∧ (∀ x y,swap (pairBits x y)=pairBits y x) ∧
    (∀ raw,unpairBits raw=none → swap raw=[false]) ∧
    (∀ x y,swap (swap (pairBits x y))=pairBits x y) :=
  ⟨swap_polyBitTime,swap_pair,swap_none,swap_twice_pair⟩

theorem parallel_spec (f g : List Bool → List Bool) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (parallel f g) ∧
    (∀ raw,parallel f g raw=pairBits (f raw) (g raw)) ∧
    (∀ raw,unpairBits (parallel f g raw)=some (f raw,g raw)) ∧
    (∀ raw,(parallel f g raw).length=2*(f raw).length+1+(g raw).length) :=
  ⟨parallel_polyBitTime f g hf hg,parallel_pair f g,parallel_unpair f g,parallel_length f g⟩

end PakFixedPolyomino.StandardBitPairMaps
