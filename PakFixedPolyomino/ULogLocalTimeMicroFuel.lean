import PakFixedPolyomino.ULogConcreteSlotMicroExpansion
import PakFixedPolyomino.PakULogTraceResourceBound

/-! The accumulated physical fuel is the length of an actual labelled
micro-word, rather than a count of arithmetic or semantic operations. -/

namespace PakFixedPolyomino.ULogLocalTimeMicroFuel
open ULogBootstrapExecution ULogConcreteSlotMicroExpansion PakULogTraceResourceBound

theorem bounded_fuel_expansion {P fuel : Nat} {start finish : Result} {slots : List Bool}
    {run : ExactConcreteSlotRun start slots finish}
    (bounded : ExactSlotRunBoundedFuel P run fuel) :
    ∃ labels, SlotMicroExpansion start slots labels finish ∧ labels.length = fuel := by
  induction bounded with
  | nil r => exact ⟨[], .nil r, rfl⟩
  | cons start next finish slot slots cycle tail tailFuel cycleBound tailBound ih =>
      obtain ⟨labels, expansion, length⟩ := ih
      refine ⟨cycleWord cycle ++ labels,
        .cons start next finish slot slots labels cycle expansion, ?_⟩
      simp only [List.length_append, cycleWord, List.length_replicate,
        List.length_cons, length]
      omega

theorem accepting_bounded_actual_word {P : Nat} {start : Result} {slots : List Bool}
    (bounded : ExactConcreteAcceptingBoundedFuel P start slots) :
    ∃ labels tape, ConcreteMicroPath start labels (.accepted tape) ∧
      labels.length ≤ slots.length * P := by
  obtain ⟨finish, run, fuel, accepts, bound⟩ := bounded
  obtain ⟨labels, expansion, length⟩ := bounded_fuel_expansion bound
  have physical := to_micro_path expansion
  have size := exactSlotRunFuel_le_length_mul bound
  cases finish with
  | accepted tape => exact ⟨labels, tape, physical, by simpa only [length] using size⟩
  | running q z => simp [concreteAccepting] at accepts
  | rejected => simp [concreteAccepting] at accepts
  | stuck => simp [concreteAccepting] at accepts

end PakFixedPolyomino.ULogLocalTimeMicroFuel
