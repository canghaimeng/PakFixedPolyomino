import PakFixedPolyomino.StandardBitRetainedPairCleanup
import PakFixedPolyomino.StandardBitProtectedLoader
import PakFixedPolyomino.StandardBitCommonAlphabetJoin

/-! Genuine ordinary loading and source computation before physical pairing.
The exact initialized result below covers all valid literal pairs. Total
malformed-input handling and all-raw polynomial closure remain separate. -/
namespace PakFixedPolyomino.StandardBitRetainedPairJoin
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardMachineProtectedTrack (protect embed)
open StandardBitRetainedPairStage (Alphabet joint startTape startConfig finalConfig)
open StandardBitRetainedPairCleanup (stageFuel stage_run stageFuel_le)
variable {ns nt : Nat}

def loaded (M : DeterministicMachine ns nt) : DeterministicMachine (ns+4) (4*(2*(4*nt))) :=
  protect (nr:=4) (protect (nr:=2) (StandardBitProtectedLoader.loader M) 0) 2

def wrap (c : Configuration (ns+4) (4*nt)) : Configuration (ns+4) (4*(2*(4*nt))) :=
  embed (fun _ => (2 : Fin 4)) (embed (fun _ => (0 : Fin 2)) c)

def loadedFinal (M : DeterministicMachine ns nt) (r u : List Bool) :
    Configuration (ns+4) (4*(2*(4*nt))) := ⟨(loaded M).accept,0,startTape M r u⟩

theorem loaded_source_exact (M : DeterministicMachine ns nt) (r : List Bool)
    (slots : List (Fin 1)) :
    run (loaded M) (ticks (2*r.length+4)++slots) (initial (loaded M) r)=
      (run M slots (initial M r)).map (fun out =>
        wrap (StandardBitProtectedLoader.lift (embed (StandardBitProtectedLoader.rawTape r) out))) := by
  unfold loaded
  rw [← StandardMachineProtectedTrack.initial_eq,StandardMachineProtectedTrack.run_exact,
    ← StandardMachineProtectedTrack.initial_eq,StandardMachineProtectedTrack.run_exact,
    StandardBitProtectedLoader.loader_source_exact]
  simp only [Option.map_map,Function.comp_def]
  rfl

theorem loaded_run (M : DeterministicMachine ns nt) (r u : List Bool)
    (n : Nat) (out : Configuration ns nt)
    (hr : run M (ticks n) (initial M r)=some out) (ho : Output M u out) :
    run (loaded M) (ticks (2*r.length+4+n)) (initial (loaded M) r)=
      some (loadedFinal M r u) := by
  rw [ticks_add,loaded_source_exact,hr,Option.map_some]
  apply congrArg some
  apply StandardMachineProtectedTrack.config_ext
  · simp [wrap,embed,StandardBitProtectedLoader.lift,loadedFinal,loaded,
      StandardBitProtectedLoader.loader,ho.1]
  · simpa only [wrap,embed,StandardBitProtectedLoader.lift,loadedFinal] using ho.2.1
  · funext z
    simp only [wrap,embed,StandardBitProtectedLoader.lift,loadedFinal,ho.2.2,startTape,joint]
    rfl

def pairMachine (M : DeterministicMachine ns nt) :
    DeterministicMachine ((ns+4)+30+2) (4*(2*(4*nt))) :=
  StandardBitCommonAlphabetJoin.machine (nsA:=ns+4) (nsB:=30)
    (loaded M) (StandardBitRetainedPairStage.machine M)

def pairFinal (M : DeterministicMachine ns nt) (v : List Bool) :
    Configuration ((ns+4)+30+2) (4*(2*(4*nt))) :=
  StandardBitCommonAlphabetJoin.configB (nsA:=ns+4) (nsB:=30)
    (StandardBitRetainedPairStage.machine M) (finalConfig M v)

theorem pair_input (M : DeterministicMachine ns nt) (v : List Bool) :
    inputTape (pairMachine M) v=inputTape (StandardBitRetainedPairStage.machine M) v := rfl

theorem pair_output (M : DeterministicMachine ns nt) (v : List Bool) :
    Output (pairMachine M) v (pairFinal M v) := by
  refine ⟨?_,rfl,?_⟩
  · change StandardBitMachineComposition.encodeStateB
      (StandardBitRetainedPairStage.machine M) (StandardBitRetainedPairStage.machine M).accept=
      StandardBitMachineComposition.acceptC
    simp [StandardBitMachineComposition.encodeStateB,StandardBitMachineComposition.acceptC]
  · exact (pair_input M v).symm

theorem initialized_pair_run (M : DeterministicMachine ns nt) (x y u : List Bool)
    (n : Nat) (out : Configuration ns nt)
    (hr : run M (ticks n) (initial M (pairBits x y))=some out) (ho : Output M u out) :
    run (pairMachine M) (ticks ((2*(pairBits x y).length+4+n)+1+stageFuel x y u))
      (initial (pairMachine M) (pairBits x y))=some (pairFinal M (pairBits u y)) := by
  have hsource := loaded_run M (pairBits x y) u n out hr ho
  have hstage : run (StandardBitRetainedPairStage.machine M) (ticks (stageFuel x y u))
      ⟨(StandardBitRetainedPairStage.machine M).start,(loadedFinal M (pairBits x y) u).head,
        (loadedFinal M (pairBits x y) u).tape⟩=some (finalConfig M (pairBits u y)) :=
    stage_run M x y u
  exact StandardBitCommonAlphabetJoin.joined_run (loaded M) (StandardBitRetainedPairStage.machine M)
    (initial (loaded M) (pairBits x y)) (loadedFinal M (pairBits x y) u)
    (finalConfig M (pairBits u y)) (2*(pairBits x y).length+4+n) (stageFuel x y u)
    hsource rfl hstage

theorem initialized_pair_prefix_bound (M : DeterministicMachine ns nt) (x y u : List Bool)
    (n : Nat) (out : Configuration ns nt)
    (hr : run M (ticks n) (initial M (pairBits x y))=some out) (ho : Output M u out) :
    RunsAtMost (pairMachine M) (pairBits x y)
      ((2*(pairBits x y).length+4+n)+1+stageFuel x y u) :=
  halting_runsAtMost (pairMachine M) (pairBits x y) _ _
    (initialized_pair_run M x y u n out hr ho) (pair_output M _).1

theorem initialized_pair_spec (M : DeterministicMachine ns nt) (x y u : List Bool)
    (n : Nat) (out : Configuration ns nt)
    (hr : run M (ticks n) (initial M (pairBits x y))=some out) (ho : Output M u out) :
    run (pairMachine M) (ticks ((2*(pairBits x y).length+4+n)+1+stageFuel x y u))
      (initial (pairMachine M) (pairBits x y))=some (pairFinal M (pairBits u y)) ∧
    Output (pairMachine M) (pairBits u y) (pairFinal M (pairBits u y)) ∧
    stageFuel x y u≤64*(x.length+y.length+u.length+1)*(x.length+y.length+u.length+1) ∧
    RunsAtMost (pairMachine M) (pairBits x y)
      ((2*(pairBits x y).length+4+n)+1+stageFuel x y u) :=
  ⟨initialized_pair_run M x y u n out hr ho,pair_output M _,stageFuel_le x y u,
    initialized_pair_prefix_bound M x y u n out hr ho⟩

end PakFixedPolyomino.StandardBitRetainedPairJoin
