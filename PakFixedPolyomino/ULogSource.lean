import PakFixedPolyomino.ULogClocked
import PakFixedPolyomino.MetricComposition
import Mathlib.Tactic

/-!
# Normalized bounded-machine source theorem

This is the semantic source theorem immediately below the eventual standard
`#EXP` normalization.  It packages finite two-slot one-tape witnesses and
proves, without an assumption, that every such exponential-time count reduces
parsimoniously to the single clocked universal count.
-/

namespace PakFixedPolyomino.ULogSource

open ULogCompiler ULogClocked

noncomputable section

structure Certificate (f : BitString → ℕ) where
  ns : ℕ
  nt : ℕ
  program : BoundedProgram ns nt
  qStart : Fin ns
  zero : Fin nt
  one : Fin nt
  blank : Fin nt
  qStart_val : qStart.1 = ULogSemantics.startCode
  zero_val : zero.1 = 0
  one_val : one.1 = 1
  blank_val : blank.1 = ULogSemantics.blankCode
  exponent : Polynomial ℕ
  count_correct : ∀ x,
    f x =
      (boundedMachine program blank
        (boundedInitial qStart zero one blank)).acceptingPaths
          (2 ^ exponent.eval x.length)
          (boundedInitial qStart zero one blank x)

def Class (f : BitString → ℕ) : Prop := Nonempty (Certificate f)

def padding {f : BitString → ℕ} (C : Certificate f)
    (x : BitString) : BitString :=
  List.replicate (C.exponent.eval x.length) false

def instanceMap {f : BitString → ℕ} (C : Certificate f)
    (x : BitString) : BitString :=
  encodePaddedInstance C.program x (padding C x)

def instanceSizePolynomial {f : BitString → ℕ} (C : Certificate f) :
    Polynomial ℕ :=
  C.exponent + Polynomial.C 2 * Polynomial.X +
    Polynomial.C
      ((ULogBytecode.encodeProgram (compile C.program)).length + 1)

theorem instanceMap_length {f : BitString → ℕ} (C : Certificate f)
    (x : BitString) :
    (instanceMap C x).length = (instanceSizePolynomial C).eval x.length := by
  simp [instanceMap, padding, instanceSizePolynomial]
  omega

theorem instanceMap_injective {f : BitString → ℕ}
    (C : Certificate f) : Function.Injective (instanceMap C) := by
  exact ULogClocked.encodePaddedInstance_injective C.program (padding C)

theorem universalCount_instance {f : BitString → ℕ}
    (C : Certificate f) (x : BitString) :
    ULogClocked.universalCount (instanceMap C x) = f x := by
  unfold instanceMap padding
  rw [ULogClocked.universalCount_paddedInstance C.program C.qStart
    C.zero C.one C.blank C.qStart_val C.zero_val C.one_val C.blank_val]
  simp only [List.length_replicate]
  exact (C.count_correct x).symm

def reduction {f : BitString → ℕ} (C : Certificate f) :
    MetricReduction f ULogClocked.universalCount where
  instanceMap := instanceMap C
  postprocess := fun _ y => y
  correct x := by rw [universalCount_instance]

theorem hard : HardFor Class ULogClocked.universalCount := by
  intro f hf
  rcases hf with ⟨C⟩
  exact ⟨reduction C⟩

theorem reduces {f : BitString → ℕ} (hf : Class f) :
    Reduces f ULogClocked.universalCount := hard f hf

def regressionAction (target : Fin 3) : BoundedAction 3 3 :=
  ⟨0, target, .stay⟩

/-- Small executable regression: the start pair has two distinct labels, one
accepting and one rejecting.  The universal count must preserve the single
accepting branch. -/
def regressionProgram : BoundedProgram 3 3 where
  rule q _read slot :=
    if q = 2 then
      if slot then some (regressionAction 1)
      else some (regressionAction 0)
    else none

theorem regression_bounded_count (input : BitString) :
    BinaryNondeterministicMachine.acceptingPaths
      (boundedMachine regressionProgram (2 : Fin 3)
        (boundedInitial (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)))
      1 (boundedInitial (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
        (2 : Fin 3) input) = 1 := by
  cases input with
  | nil => native_decide
  | cons b bits =>
      cases b <;>
        simp [BinaryNondeterministicMachine.acceptingPaths,
          boundedMachine, boundedInitial, boundedNext, boundedStepSlot,
          boundedHalted, boundedAccepting, regressionProgram,
          regressionAction, applyBounded, ULogSemantics.acceptCode]

theorem regression_universal_count (input : BitString) :
    ULogClocked.universalCount
      (ULogClocked.encodePaddedInstance regressionProgram input []) = 1 := by
  rw [ULogClocked.universalCount_paddedInstance regressionProgram
    (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    (by rfl) (by rfl) (by rfl) (by rfl)]
  simpa using regression_bounded_count input

end

end PakFixedPolyomino.ULogSource
