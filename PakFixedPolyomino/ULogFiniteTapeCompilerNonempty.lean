import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! A real nonempty successful word supplies an occupied compiled rule. -/
namespace PakFixedPolyomino.ULogFiniteTapeCompilerNonempty
open ULogCompiler ULogFiniteTapeZipperRun
variable {ns nt : Nat}

theorem compiled_nonempty_of_run (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (head hf : Int) (z out : BoundedConfig ns nt)
    (nonempty : w ≠ []) (word : run p blank w head z = some (hf, out)) : compile p ≠ [] := by
  cases w with
  | nil => exact (nonempty rfl).elim
  | cons slot rest =>
    cases halt : boundedHalted z with
    | true => simp [run, halt] at word
    | false =>
      cases rule : p.rule z.state z.focus slot with
      | none => simp [run, halt, rule] at word
      | some a =>
        have lookup : ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot =
            some (actionCode a) := by rw [lookup_compile, rule]; rfl
        obtain ⟨r, mem, _⟩ := ULogBytecode.lookupRule_some_mem lookup
        intro empty
        rw [empty] at mem
        exact List.not_mem_nil mem

end PakFixedPolyomino.ULogFiniteTapeCompilerNonempty
