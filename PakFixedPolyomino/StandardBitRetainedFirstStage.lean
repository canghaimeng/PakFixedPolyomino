import PakFixedPolyomino.StandardBitRetainedPairStage

/-! Complementary literal finite pairing stage. Its counter phases use the
same physical tracks as the retained-answer stage. It then consumes both
cells of each first-field bit, preserving the original zero separator, and
copies the payload bit to the output. All operational proofs are separate. -/
namespace PakFixedPolyomino.StandardBitRetainedFirstStage
open StandardNondeterministicMachine StandardBitTime
open StandardBitRetainedPairStage hiding machine
variable {ns nt : Nat}

def machine (M : DeterministicMachine ns nt) : DeterministicMachine 30 (4*(2*(4*nt))) :=
  { StandardBitRetainedPairStage.machine M with
  rule := fun q s slot =>
    if q=15 then
      if output s=3 then some ⟨s,18,.right⟩ else some ⟨s,15,.left⟩
    else if q=18 then
      if raw s=3 then some ⟨s,18,.right⟩
      else if raw s=1 then some ⟨setRaw s 3,29,.right⟩
      else if raw s=0 then some ⟨s,25,.left⟩
      else none
    else if q=29 then
      if raw s=0 then some ⟨setRaw s 3,19,.left⟩
      else if raw s=1 then some ⟨setRaw s 3,22,.left⟩
      else none
    else if q=24 then
      if output s=3 then some ⟨s,18,.right⟩ else some ⟨s,24,.left⟩
    else (StandardBitRetainedPairStage.machine M).rule q s slot
  accept_terminal := by intro s slot;simp [StandardBitRetainedPairStage.machine]
  reject_terminal := by intro s slot;simp [StandardBitRetainedPairStage.machine] }

theorem counter_zero_setup (M : DeterministicMachine ns nt) (r u : List Bool) :
    run (machine M) (ticks 2) (startConfig M r u)=some (counterConfig M r u 0) := by
  have h := StandardBitRetainedPairStage.counter_zero_setup M r u
  simpa [machine,StandardBitRetainedPairStage.machine,ticks,run,step,startConfig] using h

end PakFixedPolyomino.StandardBitRetainedFirstStage
