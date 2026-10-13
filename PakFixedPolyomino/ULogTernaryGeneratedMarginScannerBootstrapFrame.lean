import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClockSlack
import PakFixedPolyomino.PakULogGeneralCapacityBootstrapFirstHit
import PakFixedPolyomino.ULogBootstrapAllMicroCounts

/-! The literal OWN compact input of the whole nondeterministic scanner
has this real decoded-payload frame and genuine first bootstrap hit.
Initialization only requires C >= 2. This does not prove acceptance in
the shortage bands or a physical time bound. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapFrame
open ULogCompiler ULogBootstrapExecution ULogAlphabet ULogProgram
open ULogTernaryGeneratedMarginScanner (program input initial states states_ge start_input)
open StandardNondeterministicMachine (Machine)
open PakULogGeneralCapacityBootstrap
open ULogFiniteTapeNondeterministicMicroCounts (RawAcceptingMicroWords)
variable {ns nt : Nat}

noncomputable def payload (nt : Nat) (p : Polynomial Nat) (x : List Bool) : List Bool :=
  StandardBitCountedPolynomialPayload.payload
    (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x

noncomputable def frame (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (tail : List Tape) : SemanticCycleFrame (payload nt p x) ([] : List Tape) where
  config := ULogSemantics.start (input M p x)
  clockZeros := ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x
  runtime := [ulogCore clockSep]
  capacity := C
  outer := MStarConcreteAlphabet.work :: tail

theorem decoded_start (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input M p x) =
      ULogSemantics.startFrom (compile (program M p)) (payload nt p x) := by
  simp [input, payload, ULogPayloadClockBitWrapper.wrap, ULogSemantics.start]

theorem initial_not_halted (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    boundedHalted (initial M p x) = false := by
  rw [ULogTernaryGeneratedMarginScanner.initial_bounded]
  cases ULogTernaryRetainedCounterPump.sourceInput
      (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
      (ULogTernaryGuardedPumpSentinel.source (ULogTernaryGeneratedMarginLoop.depth nt p)
        (ULogTernaryGeneratedMarginLoop.seed nt p) x) <;>
    simp [boundedInitial, boundedHalted]

theorem clock_separator_passive : PassivePath [ulogCore clockSep] := by
  intro cell hcell
  rw [List.mem_singleton.mp hcell]
  constructor <;> decide

theorem frame_clock_decode (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (tail : List Tape) :
    decodeBinaryClock
      (List.replicate (frame M p x C tail).clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: (frame M p x C tail).runtime) =
      some (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x) :=
  ULogRetainedPumpClockBitInput.power_clock_decode _ []

theorem padding_length (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    (ULogPayloadClockBitWrapper.padding (payload nt p x)).length =
      ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x := by
  rw [ULogTernaryGeneratedMarginScannerClock.clock_width_payload]
  simp [payload, ULogPayloadClockBitWrapper.padding]

theorem frame_eq_bootstrap (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (tail : List Tape) :
    frame M p x C tail = bootstrapSemanticFrame (compile (program M p))
      (payload nt p x) (ULogPayloadClockBitWrapper.padding (payload nt p x)) C tail := by
  simp only [frame, bootstrapSemanticFrame, decoded_start, padding_length]

theorem payload_nonempty (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    payload nt p x ≠ [] := by
  rw [payload, StandardBitCountedPolynomialPayload.payload_layout]
  simp

theorem workspace_overhead (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    bootstrapWorkspaceOverhead (payload nt p x) = 6 := by
  have nonempty := payload_nonempty nt p x
  cases h : payload nt p x with
  | nil => exact (nonempty h).elim
  | cons b bs => rfl

theorem semantic_capacity (nt : Nat) (p : Polynomial Nat) (x : List Bool) (C : Nat)
    (hC : 2 ≤ C) : generalSemanticCapacity (payload nt p x) (C + 4) = C := by
  simp only [generalSemanticCapacity, generalBootstrapTail, workspace_overhead, List.length_replicate]
  omega

noncomputable def outerTail (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : List Tape :=
  List.replicate (PakOuterULogBridge.copiedCoreRadius (input M p x) - 1) MStarConcreteAlphabet.work

theorem actual_frame_eq_general_capacity (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) (hC : 2 ≤ C) :
    frame M p x C (outerTail M p x) = generalCapacitySemanticFrame (input M p x)
      (compile (program M p)) (payload nt p x)
      (ULogPayloadClockBitWrapper.padding (payload nt p x)) (C + 4) := by
  rw [frame_eq_bootstrap]
  simp only [generalCapacitySemanticFrame, semantic_capacity nt p x C hC, outerTail]

noncomputable def bootstrapStart (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) : Result :=
  .running ULogControl.qStart (generalCapacityCoreZipper (input M p x) (C + 4))

noncomputable def actual_bootstrap_prefix (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) (hC : 2 ≤ C) :
    FirstValidZeroHit IsConcreteCycleBoundary (bootstrapStart M p x C)
      (frame M p x C (outerTail M p x)).encode := by
  rw [actual_frame_eq_general_capacity M p x C hC]
  apply PakULogGeneralCapacityBootstrapFirstHit.generalCapacity_firstValidZeroHit
    (input M p x) (compile (program M p)) (payload nt p x)
    (ULogPayloadClockBitWrapper.padding (payload nt p x)) (C + 4)
  · rfl
  · rw [workspace_overhead]
    omega

theorem all_bootstrap_micro_card_eq (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (C : Nat) (hC : 2 ≤ C) :
    Nat.card (RawAcceptingMicroWords (bootstrapStart M p x C)) =
      Nat.card (RawAcceptingMicroWords (frame M p x C (outerTail M p x)).encode) := by
  exact ULogBootstrapAllMicroCounts.raw_card_eq (actual_bootstrap_prefix M p x C hC) rfl

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapFrame
