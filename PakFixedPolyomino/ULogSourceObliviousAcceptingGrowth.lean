import PakFixedPolyomino.ULogFiniteProgramPrefixFootprint
import PakFixedPolyomino.ULogSourceObliviousExteriorZipper

/-! Every accepting labelled scanner word has its whole chronological
footprint inside the two delimiters. On the actual exterior zipper this
implies zero allocated-cell growth, including immediate acceptance. The
source time bound is an ordinary machine bound; no image certificate is
supplied for the scanner word. Physical microtime is separate. -/
namespace PakFixedPolyomino.ULogSourceObliviousAcceptingGrowth
open StandardNondeterministicMachine StandardMachineWindowBridge
open ULogCompiler ULogSourceObliviousBytecode ULogSourceObliviousBytecodeRunBridge
open ULogSourceObliviousExteriorZipper
open ULogSourceObliviousInitialWindowExecution (initialWindowConfig)
open ULogSourceObliviousHaltingLeaves ULogSourceObliviousHaltingAcceptance
open ULogFiniteProgramZipperRunBridge ULogFiniteProgramPrefixFootprint
open ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger ULogFiniteTapePrefixGrowth
open StandardMachineZipperBridge (physical)
variable {ns nt : Nat}

/-- The inverse is defined on every accepting numerical word. -/
theorem numerical_accepting_prefix_heads (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (word : List (FiniteOneTapeProgram.Arrow (numericalProgram M)))
    (out : FiniteOneTapeSemantics.Config (Fin (2 + Fintype.card (Active M))) (Fin 3))
    (hw : FiniteOneTapeSemantics.run (numericalProgram M) (fun _ => true) word
      (physical (2 : Fin 3) 0 (zipper M (inputWindow M x bound) left suffix)) = some out)
    (ha : out.state.val = 0) :
    ∀ k ≤ word.length, ∃ middle,
      FiniteOneTapeSemantics.run (numericalProgram M) (fun _ => true) (word.take k)
        (physical (2 : Fin 3) 0 (zipper M (inputWindow M x bound) left suffix)) = some middle ∧
      0 ≤ middle.head ∧
      middle.head ≤ (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int) := by
  let ext := exterior M (inputWindow M x bound) left suffix
  let leaf : AcceptingNumericalLeaves M x bound ext := ⟨word, out, by
    rw [← zipper_physical]
    exact hw, ha⟩
  let raw := (numericalLeavesEquiv M x bound ext).symm leaf
  have hrestore : raw.val.map (arrowEquiv M) = word :=
    congrArg Subtype.val ((numericalLeavesEquiv M x bound ext).apply_symm_apply leaf)
  have foot := (all_physical_leaf_resources M x bound ht ext raw).2.2
  intro k hk
  have hlen : raw.val.length = word.length := by
    simpa only [List.length_map] using congrArg List.length hrestore
  obtain ⟨middle, hm, hlo, hhi⟩ := foot k (by omega)
  refine ⟨encodeConfig M middle, ?_, hlo, hhi⟩
  have hprefix : word.take k = (raw.val.take k).map (arrowEquiv M) := by
    rw [List.map_take, hrestore]
  rw [hprefix, zipper_physical, run_arrowEquiv, hm]
  rfl

/-- The same slots, with both labels kept, inherit the delimiter footprint. -/
theorem accepting_prefix_heads (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3)
    (hw : run (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out))
    (ha : out.state.val = 0) :
    PrefixHeads (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) 0
      (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int) := by
  have hz : zipperSlotRun (boundedProgram M) slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out) := by
    rw [ULogFiniteTapeGuardedStageLeafCounts.zipperSlotRun_eq_run]
    exact hw
  obtain ⟨word, hslots, _, hword⟩ := successful_zipper_to_arrows
    (boundedProgram M) slots 0 _ hf out hz
  apply transfer_prefix_heads (boundedProgram M) (scanner_terminal_table M) word slots
    0 0 _ _ hslots
  exact numerical_accepting_prefix_heads M x bound ht left suffix word
    (physical (2 : Fin 3) hf out) hword ha

/-- Arbitrary allocated exterior cells are retained; none are extended. -/
theorem accepting_zero_growth (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3)
    (hw : run (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out))
    (ha : out.state.val = 0) :
    GrowthRun (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) hf out 0 0 := by
  have heads := accepting_prefix_heads M x bound ht left suffix slots hf out hw ha
  apply no_growth_of_prefix_heads (boundedProgram M) 2 slots 0 hf _ out _ hw
  intro k hk hmid middle hrun
  obtain ⟨hl, hr⟩ := heads k hk hmid middle hrun
  have width : (inputWindow M x bound).encode.length =
      (x.length + 2 * bound + 3) * (nt + 1) := by
    change ULogSourceObliviousUpdateExecution.windowWidth (inputWindow M x bound) = _
    rw [ULogSourceObliviousUpdateExecution.windowWidth_eq, inputWindow_length]
  simp only [leftEdge, rightEdge, zipper, List.length_append, List.length_cons,
    Nat.cast_add, Nat.cast_one, zero_sub, zero_add]
  rw [width]
  constructor <;> omega

end PakFixedPolyomino.ULogSourceObliviousAcceptingGrowth
