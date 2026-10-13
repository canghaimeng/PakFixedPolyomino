import PakFixedPolyomino.ULogFiniteTapePrefixGrowth
import PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts

/-! Literal finite-arrow prefix footprints transfer to the same labelled
zipper word. Equal transition effects do not identify the two slots. -/
namespace PakFixedPolyomino.ULogFiniteProgramPrefixFootprint
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapePrefixGrowth
open ULogFiniteProgramZipperRunBridge (TerminalTable arrowSlotBool successful_arrows_to_zipper)
open StandardMachineZipperBridge (physical)
variable {ns : Nat}

theorem transfer_prefix_heads (p : BoundedProgram ns 3) (hp : TerminalTable p)
    (word : List (FiniteOneTapeProgram.Arrow (toFiniteProgram p))) (slots : List Bool)
    (H lo hi : Int) (z : BoundedConfig ns 3)
    (hslots : word.map (arrowSlotBool p) = slots)
    (foot : ∀ k ≤ word.length, ∃ middle,
      FiniteOneTapeSemantics.run (toFiniteProgram p) (fun _ => true) (word.take k)
        (physical (2 : Fin 3) H z) = some middle ∧ lo ≤ middle.head ∧ middle.head ≤ hi) :
    PrefixHeads p 2 slots H z lo hi := by
  intro k hk hf out hw
  have hlen : word.length = slots.length := by
    simpa only [List.length_map] using congrArg List.length hslots
  obtain ⟨middle, hm, hlo, hhi⟩ := foot k (by omega)
  obtain ⟨hmid, zmid, hz, hphys⟩ := successful_arrows_to_zipper p hp (word.take k) H z hm
  have he : (word.take k).map (arrowSlotBool p) = slots.take k := by
    rw [List.map_take, hslots]
  rw [he, ULogFiniteTapeGuardedStageLeafCounts.zipperSlotRun_eq_run] at hz
  have hh := (Prod.mk.inj (Option.some.inj (hz.symm.trans hw))).1
  have hmHead := congrArg FiniteOneTapeSemantics.Config.head hphys
  have hmHead' : hmid = middle.head := by simpa only [StandardMachineZipperBridge.physical_head] using hmHead
  exact ⟨by omega, by omega⟩

theorem zero_growth_from_word_footprint (p : BoundedProgram ns 3) (hp : TerminalTable p)
    (word : List (FiniteOneTapeProgram.Arrow (toFiniteProgram p))) (slots : List Bool)
    (H hf : Int) (z out : BoundedConfig ns 3)
    (hslots : word.map (arrowSlotBool p) = slots)
    (foot : ∀ k ≤ word.length, ∃ middle,
      FiniteOneTapeSemantics.run (toFiniteProgram p) (fun _ => true) (word.take k)
        (physical (2 : Fin 3) H z) = some middle ∧
          ULogFiniteTapeGrowthLedger.leftEdge H z ≤ middle.head ∧
          middle.head ≤ ULogFiniteTapeGrowthLedger.rightEdge H z)
    (hw : run p 2 slots H z = some (hf, out)) :
    ULogFiniteTapeGrowthLedger.GrowthRun p 2 slots H z hf out 0 0 :=
  no_growth_of_prefix_heads p 2 slots H hf z out
    (transfer_prefix_heads p hp word slots H _ _ z hslots foot) hw

end PakFixedPolyomino.ULogFiniteProgramPrefixFootprint
