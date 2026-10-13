import PakFixedPolyomino.ULogConcreteMicroTimeCounts
import Mathlib.Data.Fintype.Vector

/-! Every literal cutoff domain is finite and embeds into every later
cutoff without changing its physical label word or actual path. -/
namespace PakFixedPolyomino.ULogConcreteMicroCutoffMonotonicity
open ULogProgram ULogConcreteMicroTimeCounts

def cutoffWordIndex (T : Nat) (start : ULogBootstrapExecution.Result)
    (raw : RawAcceptingMicroWordsAtMost T start) :
    Σ n : Fin (T + 1), List.Vector (Fin 2) n.val :=
  ⟨⟨raw.val.length, by have h := raw.property.1; omega⟩, ⟨raw.val, rfl⟩⟩

theorem cutoffWordIndex_injective (T : Nat) (start : ULogBootstrapExecution.Result) :
    Function.Injective (cutoffWordIndex T start) := by
  intro a b same
  apply Subtype.ext
  exact congrArg (fun pair : Σ n : Fin (T + 1), List.Vector (Fin 2) n.val =>
    pair.2.val) same

theorem finite_raw_cutoff (T : Nat) (start : ULogBootstrapExecution.Result) :
    Finite (RawAcceptingMicroWordsAtMost T start) :=
  Finite.of_injective (cutoffWordIndex T start) (cutoffWordIndex_injective T start)

theorem accepting_micro_paths_mono (start : ULogBootstrapExecution.Result) (B T : Nat) (later : B ≤ T) :
    acceptingMicroPaths B start ≤ acceptingMicroPaths T start := by
  letI := finite_raw_cutoff T start
  let f : RawAcceptingMicroWordsAtMost B start → RawAcceptingMicroWordsAtMost T start :=
    fun raw => ⟨raw.val, raw.property.1.trans later, raw.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro a b same
  apply Subtype.ext
  exact congrArg (fun raw : RawAcceptingMicroWordsAtMost T start => raw.val) same

end PakFixedPolyomino.ULogConcreteMicroCutoffMonotonicity
