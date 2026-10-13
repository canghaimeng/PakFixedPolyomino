import PakFixedPolyomino.ULogFreshEntryExteriorBoot
import PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts

/-! Every accepting word from the actual exterior fresh-entry configuration
has one false LEFT tick followed by the same old labelled word. Immediate
old acceptance is included; no canonical image or runtime premise is used. -/
namespace PakFixedPolyomino.ULogFiniteTapeFreshAcceptingSplit
open ULogCompiler ULogFiniteTapeZipperRun ULogFreshEntry
open ULogFiniteTapeGuardedStageLeafCounts (zipperSlotRun_eq_run)
variable {k : Nat}

theorem accepting_split (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (3 + k) 3)
    (hw : run (program p z.state) 2 w (H + 1) (ULogFreshEntryExteriorBoot.initial z) = some (hf, out))
    (ha : out.state.val = 0) :
    ∃ rest old, w = false :: rest ∧ run p 2 rest H z = some (hf, old) ∧
      old.state.val = 0 ∧ out = insertConfig old := by
  cases w with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨_, rfl⟩
      cases hz : z.right <;>
        simp [ULogFreshEntryExteriorBoot.initial, applyBounded, hz, entryState] at ha
  | cons slot rest =>
      cases slot with
      | true =>
          cases hz : z.right with
          | nil => exact (hr hz).elim
          | cons a right =>
              simp [run, ULogFreshEntryExteriorBoot.initial, applyBounded, hz,
                boundedHalted, entryState, program] at hw
      | false =>
          change run (program p z.state) 2 ([false] ++ rest) (H + 1)
            (ULogFreshEntryExteriorBoot.initial z) = some (hf, out) at hw
          rw [run_append, ULogFreshEntryExteriorBoot.actual_left_tick p z hr H, Option.bind_some] at hw
          have he := ULogFreshEntryRunBridge.zipperSlotRun_insertConfig p z.state rest H z
          rw [zipperSlotRun_eq_run, zipperSlotRun_eq_run, hw] at he
          obtain ⟨⟨hf0, old⟩, hrun, hout⟩ := Option.map_eq_some_iff.mp he.symm
          have hhead := (Prod.mk.inj hout).1
          have hconfig := (Prod.mk.inj hout).2
          change hf0 = hf at hhead
          change insertConfig old = out at hconfig
          subst hf0
          refine ⟨rest, old, rfl, hrun, ?_, hconfig.symm⟩
          rw [← hconfig] at ha
          exact (insertState_accepting old.state).mp ha

end PakFixedPolyomino.ULogFiniteTapeFreshAcceptingSplit
