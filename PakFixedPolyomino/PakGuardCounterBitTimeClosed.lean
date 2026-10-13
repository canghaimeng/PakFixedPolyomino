import PakFixedPolyomino.PakMacroSideBitTimeClosed
import PakFixedPolyomino.StandardBitPairFirstCompaction
import PakFixedPolyomino.StandardBitProtectedLoader

/-! The original guard counter on every raw pair, computed on an actual work
tape while the complete original pair is retained on a passive raw track.
Constructing the counter/answer pair and evaluating the guard remain separate. -/
namespace PakFixedPolyomino.PakGuardCounterBitTimeClosed
open StandardNondeterministicMachine StandardBitTime StandardMachineProtectedTrack
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open PakMacroSideBitTimeClosed (macroBits macroBits_eq_encode macroBits_polyBitTime)

noncomputable def counterBits {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) : List Bool → List Bool := macroBits M p ∘ firstBits

theorem counter_pair {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x answer : List Bool) :
    counterBits M p (StandardBitMetric.pairBits x answer) =
      Computability.encodeNat (PakFixedWeightedOracleLengthGuard.macroSide M p x) := by
  simp only [counterBits,Function.comp_apply,firstBits_pair,macroBits_eq_encode]

theorem counter_value_pair {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x answer : List Bool) :
    PakFixedWeightedStandardBinaryCount.value (counterBits M p (StandardBitMetric.pairBits x answer)) =
      PakFixedWeightedOracleLengthGuard.macroSide M p x := by
  rw [counter_pair,PakFixedWeightedStandardBinaryCount.value_encode_nat]

theorem counter_malformed {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (w : List Bool) (h : StandardBitMetric.unpairBits w = none) :
    counterBits M p w = macroBits M p [] := by
  simp [counterBits,StandardBitPairFirstCompaction.firstBits,h]

theorem counter_polyBitTime {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (counterBits M p) :=
  StandardBitTimeComposition.polyBitTime_comp first_polyBitTime (macroBits_polyBitTime M p)

theorem protected_counter_bit_spec {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (counterBits M p) ∧
    ∃ (ks kt : Nat) (K : DeterministicMachine ks kt) (q : Polynomial Nat),
      ComputesWithin K (counterBits M p) (fun n => q.eval n) ∧
      ∀ w, ∃ n out, n ≤ q.eval w.length ∧
        run (StandardBitProtectedLoader.loader K) (ticks (2*w.length+4+n))
          (initial (StandardBitProtectedLoader.loader K) w) =
          some (StandardBitProtectedLoader.lift (embed (StandardBitProtectedLoader.rawTape w) out)) ∧
        Output K (counterBits M p w) out ∧
        RunsAtMost (StandardBitProtectedLoader.loader K) w (2*w.length+4+q.eval w.length) ∧
        ∀ z, (unpack ((StandardBitProtectedLoader.lift
          (embed (StandardBitProtectedLoader.rawTape w) out)).tape z)).1 =
          StandardBitProtectedLoader.rawTape w z := by
  have hc := counter_polyBitTime M p
  refine ⟨hc,?_⟩
  obtain ⟨ks,kt,K,q,hK⟩ := hc
  refine ⟨ks,kt,K,q,hK,?_⟩
  intro w
  obtain ⟨n,out,hn,hr,ho⟩ := hK w
  change n ≤ q.eval w.length at hn
  have hrun : run (StandardBitProtectedLoader.loader K) (ticks (2*w.length+4+n))
      (initial (StandardBitProtectedLoader.loader K) w) =
      some (StandardBitProtectedLoader.lift (embed (StandardBitProtectedLoader.rawTape w) out)) := by
    rw [ticks_add,StandardBitProtectedLoader.loader_source_exact,hr]
    rfl
  have ha : (StandardBitProtectedLoader.lift (embed (StandardBitProtectedLoader.rawTape w) out)).state =
      (StandardBitProtectedLoader.loader K).accept := by
    simp [StandardBitProtectedLoader.lift,embed,StandardBitProtectedLoader.loader,ho.1]
  have hb := halting_runsAtMost _ w _ _ hrun ha
  refine ⟨n,out,hn,hrun,ho,?_,?_⟩
  · intro slots middle hmiddle
    exact (hb slots middle hmiddle).trans (by omega)
  · intro z
    simp [StandardBitProtectedLoader.lift,embed]

end PakFixedPolyomino.PakGuardCounterBitTimeClosed
