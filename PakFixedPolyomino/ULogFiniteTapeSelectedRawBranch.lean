import PakFixedPolyomino.ULogSemanticFrameSelectedRightCapacity
import PakFixedPolyomino.ULogFiniteTapeSelectedCapacityBridge
import PakFixedPolyomino.ULogSelectedExactTerminalCycles

/-! A literal accepting micro-path chooses an occupied bounded-program slot.
Only its actual selected nonhalting action is capacity-ready. The alternative
slot is unrestricted. -/
namespace PakFixedPolyomino.ULogFiniteTapeSelectedRawBranch
open ULogCompiler ULogBootstrapExecution ULogProgram
open ULogFiniteTapeNondeterministicMicroInverse ULogSemanticFrameSelectedTargetCapacity
open ULogSemanticFrameSelectedRightCapacity ULogSelectedExactTerminalCycles
open MStarParserExecution (Zipper)
variable {ns : Nat}

theorem selected_bounded_lookup {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (hp : compile p ≠ []) (z : BoundedConfig ns 3)
    (frame : SemanticCycleFrame input suffix) (config : frame.config = liftConfig p z)
    (runtime : PassivePath frame.runtime) (slot : Bool) (rest : List (Fin 2))
    (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) :
    ∃ a, p.rule z.state z.focus slot = some a ∧
      ULogBytecode.lookupRule frame.config.program frame.config.state
        frame.config.focus slot = some (actionCode a) := by
  have focus : frame.config.focus < 3 := by rw [config]; exact z.focus.isLt
  have nonempty : frame.config.program ≠ [] := by simpa only [config, liftConfig] using hp
  have reads : ∀ r ∈ frame.config.program, r.read < 3 := by
    intro r member
    exact (compile_rule_bounded p (by simpa only [config, liftConfig] using member)).2.1
  obtain ⟨action, occupied⟩ := selected_lookup_exists frame focus nonempty reads runtime
    slot rest tape raw
  cases rule : p.rule z.state z.focus slot with
  | none =>
      have bad := occupied
      rw [config] at bad
      change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot = some action at bad
      rw [lookup_compile, rule] at bad
      cases bad
  | some a =>
      refine ⟨a, rfl, ?_⟩
      rw [config]
      change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot = _
      rw [lookup_compile, rule]
      rfl

theorem first_selected_raw_branch {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (hp : compile p ≠ []) (z : BoundedConfig ns 3)
    (frame : SemanticCycleFrame input suffix) (config : frame.config = liftConfig p z)
    (runtime : PassivePath frame.runtime) (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath frame.encode labels (.accepted tape)) :
    ∃ slot rest a,
      labels = List.replicate (frame_first_choice frame
        (by rw [config]; exact z.focus.isLt)).steps 0 ++
        ULogBytecode.slotIndex slot :: rest ∧
      ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
        (.accepted tape) ∧
      p.rule z.state z.focus slot = some a ∧
      ULogBytecode.lookupRule frame.config.program frame.config.state
        frame.config.focus slot = some (actionCode a) := by
  have focus : frame.config.focus < 3 := by rw [config]; exact z.focus.isLt
  obtain ⟨slot, rest, word, selected⟩ := split_frame_choice frame focus labels tape raw
  obtain ⟨a, rule, lookup⟩ := selected_bounded_lookup p hp z frame config runtime
    slot rest tape selected
  exact ⟨slot, rest, a, word, selected, rule, lookup⟩

theorem selected_nonhalting_raw_capacity {input : List Bool}
    (p : BoundedProgram ns 3) (z : BoundedConfig ns 3) (C : Nat)
    (frame : SemanticCycleFrame input ([] : List Tape))
    (config : frame.config = liftConfig p z) (capacity : frame.capacity = C)
    (runtime : PassivePath frame.runtime) (current : z.state.val ≤ C)
    (slot : Bool) (a : BoundedAction ns 3)
    (lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some (actionCode a)) (nonhalting : 2 ≤ a.target.val)
    (rest : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) : SemanticCapacityReady (liftConfig p z) (actionCode a) C := by
  have focus : frame.config.focus < 3 := by rw [config]; exact z.focus.isLt
  have reads : ∀ r ∈ frame.config.program, r.read < 3 := by
    intro r member
    exact (compile_rule_bounded p (by simpa only [config, liftConfig] using member)).2.1
  have state : frame.config.state ≤ frame.capacity := by simpa only [config, liftConfig, capacity] using current
  have ready := selected_nonhalting_capacity_ready frame focus reads runtime state slot
    (actionCode a) lookup a.write.isLt nonhalting rest tape raw
  simpa only [config, capacity] using ready

end PakFixedPolyomino.ULogFiniteTapeSelectedRawBranch
