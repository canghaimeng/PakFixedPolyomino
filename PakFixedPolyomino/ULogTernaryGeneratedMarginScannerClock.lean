import PakFixedPolyomino.ULogTernaryGeneratedMarginLoopClock
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCounts
import PakFixedPolyomino.ULogClocked

/-! The actual whole loader/scanner input decodes the literal existing
clock. ALL logical accepting paths agree with the ordinary source at that
clock, and every successful logical word fits. This clocked semantic
wrapper is distinct from the physical interpreter and its square-time. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClock
open ULogCompiler ULogFiniteTapeZipperRun ULogTernaryGeneratedMarginScanner
open ULogTernaryGeneratedMarginScannerCounts
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

theorem start_wrap (q : BoundedProgram ns nt) (y : List Bool) :
    ULogClocked.start (ULogPayloadClockBitWrapper.wrap q y) =
      ⟨ULogSemantics.start (ULogPayloadClockBitWrapper.wrap q y), 2 ^ (2 * y.length + 1)⟩ := by
  simp [ULogClocked.start, ULogSemantics.start, ULogPayloadClockBitWrapper.wrap,
    ULogPayloadClockBitWrapper.padding]

theorem clock_width_payload (nt : Nat) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x =
      2 * (StandardBitCountedPolynomialPayload.payload
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1 := by
  rw [StandardBitCountedPolynomialPayload.payload_layout]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  rfl

theorem actual_clocked_start (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogClocked.start (input M p x) =
      ⟨liftConfig (program M p) (initial M p x),
        2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x⟩ := by
  have h := start_wrap (program M p)
    (StandardBitCountedPolynomialPayload.payload (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x)
  change ULogClocked.start (input M p x) = ⟨ULogSemantics.start (input M p x), _⟩ at h
  rw [← clock_width_payload, start_input] at h
  exact h

theorem budget_le_clock (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    budget M p x ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x :=
  ULogTernaryGeneratedMarginLoopClock.full_budget_le_clock M p x

theorem all_semantic_words_fit (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input M p x)) w = some out) :
    w.length ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x :=
  (all_semantic_raw_length M p x ht w out hw).trans (budget_le_clock M p x)

theorem ordinary_clocked_count (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (extra : Nat) :
    acceptingCount M x (2 ^ p.eval x.length) =
      ULogClocked.machine.acceptingPaths
        (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x + extra)
        (ULogClocked.start (input M p x)) := by
  rw [actual_clocked_start, ULogClocked.acceptingPaths_extra]
  rw [← start_input]
  exact large_cutoff_count M p x ht _ (budget_le_clock M p x)

theorem whole_logical_clock_count_spec (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    ULogClocked.start (input M p x) =
      ⟨liftConfig (program M p) (initial M p x),
        2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x⟩ ∧
    (∀ w out, semanticRun (ULogSemantics.start (input M p x)) w = some out →
      w.length ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x) ∧
    (∀ extra, acceptingCount M x (2 ^ p.eval x.length) =
      ULogClocked.machine.acceptingPaths
        (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x + extra)
        (ULogClocked.start (input M p x))) :=
  ⟨input_polyBitTime M p, actual_clocked_start M p x,
    all_semantic_words_fit M p x ht, ordinary_clocked_count M p x ht⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerClock
