import PakFixedPolyomino.PakFullFrameFirstBranch
import PakFixedPolyomino.MStarParserSoundness

/-! # Slot-one full-frame reflection

This module begins the reverse analysis of the nontrivial first branch.  It
records only facts extracted from an actual literal full-frame run; no encoded
word, side, or parser certificate is accepted as an input. -/

namespace PakFixedPolyomino.PakSlotOneFullFrameReflection

open PakMStarCouplingCorrectness
open PakFullFrameTableauReadback

abbrev SlotOneFullFrame (n : ℕ) :=
  {F : FullFrame n n //
    ((FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 1}

/-- The first labelled arrow of a slot-one full frame is an actual successful
outer-machine transition from the literal readback configuration. -/
theorem slotOne_first_step {n : ℕ} (F : SlotOneFullFrame n) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      ((FullFrame.toUniformWindowedRun F.1).config ⟨0, Nat.zero_lt_succ n⟩)
      ((FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩) =
        some ((FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩) := by
  simpa using (FullFrame.toUniformWindowedRun F.1).step ⟨0, F.1.width_pos⟩

/-- The source of that extracted transition is the literal outer start state;
the conclusion is read from the east scanner/tableau column, not assumed. -/
theorem slotOne_first_source_start {n : ℕ} (F : SlotOneFullFrame n) :
    (FiniteOneTapeProgram.transition MStarULogAssembly.program
      ((FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩)).sourceState =
        MStarOuterProgram.State.start := by
  have hstep := slotOne_first_step F
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
    ((FullFrame.toUniformWindowedRun F.1).config ⟨0, Nat.zero_lt_succ n⟩)
    ((FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
    ((FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩) hstep
  rw [← hsource.1]
  exact FullFrame.uniform_initial_state_start F.1

/-- The complete arrow word of a literal slot-one frame is an actual finite
accepting suffix: every entry executes and its final configuration is accept.
This is the semantic object that a later minimal outer-to-parser bridge must
project into `MStarParserSoundness.CanAcceptResult`. -/
structure SlotOneOuterAcceptingTrace {n : ℕ} (F : SlotOneFullFrame n) where
  /-- The literal operational trace read from this frame. -/
  run : UniformWindowedMStarRun n n
  /-- It is definitionally the frame readback, so no external trace is supplied. -/
  run_eq : run = FullFrame.toUniformWindowedRun F.1
  first_slot_one : run.arrow ⟨0, F.1.width_pos⟩ |>.1.2 = 1

noncomputable def slotOneOuterAcceptingTrace {n : ℕ}
    (F : SlotOneFullFrame n) : SlotOneOuterAcceptingTrace F where
  run := FullFrame.toUniformWindowedRun F.1
  run_eq := rfl
  first_slot_one := F.2

end PakFixedPolyomino.PakSlotOneFullFrameReflection
