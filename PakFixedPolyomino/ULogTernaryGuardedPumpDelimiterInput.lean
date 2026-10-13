import PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterResources
import PakFixedPolyomino.ULogTernaryGuardedPumpSentinelInput

/-! Ordinary polynomial BIT input for actual guarded generator/parser/real
left sentinel/source delimiter. The old clock has enough real ticks for
all four stages and their five literal handoff ticks; every raw word is bounded. Original
source and all but one generated buffer cell survive. Physical bootstrap,
compact loading and the original square theorem are separate. -/

namespace PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterInput

open ULogCompiler ULogFiniteTapeZipperRun ULogBootstrapExecution ULogAlphabet
open ULogTernaryGuardedPumpDelimiter (program initial final)

def depth (p : Polynomial Nat) : Nat := p.natDegree + 1
def seedWidth (p : Polynomial Nat) : Nat := StandardBitPolynomialPayload.coefficientTotal p + 2
def width (p : Polynomial Nat) (x : List Bool) : Nat := StandardBitCountedPolynomialPayload.width p x
def source (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogTernaryGuardedPumpSentinel.source (depth p) (seedWidth p) x
def deadline (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGuardedPumpDelimiter.deadline (width p x) (depth p) (seedWidth p) x
def clockWidth (p : Polynomial Nat) (x : List Bool) : Nat :=
  2 * (width p x + (source p x).length + 1) + 1
def input (p : Polynomial Nat) (x : List Bool) : List Bool :=
  ULogPayloadClockBitWrapper.wrap (program (depth p) (seedWidth p))
    (StandardBitCountedPolynomialPayload.payload p x)

theorem seed_positive (p : Polynomial Nat) : 0 < seedWidth p := by
  unfold seedWidth
  omega

theorem source_eq (p : Polynomial Nat) (x : List Bool) :
    source p x = StandardBitCountedPolynomialPayload.source p x := rfl

theorem source_length_ge (p : Polynomial Nat) (x : List Bool) : 2 ≤ (source p x).length :=
  ULogTernaryPolynomialPumpClockInput.source_length_ge p (StandardBitRetainedPayload.payload x)

theorem source_fits (p : Polynomial Nat) (x : List Bool) : (source p x).length ≤ 2 ^ width p x :=
  ULogTernaryPolynomialPumpClockInput.source_fits p (StandardBitRetainedPayload.payload x)

theorem input_polyBitTime (p : Polynomial Nat) : StandardBitTime.PolyBitTime (input p) :=
  StandardBitTimeComposition.polyBitTime_comp
    (StandardBitCountedPolynomialPayload.payload_polyBitTime p)
    (ULogPayloadClockBitWrapper.wrap_polyBitTime (program (depth p) (seedWidth p)))

theorem start_input (p : Polynomial Nat) (x : List Bool) :
    ULogSemantics.start (input p x) =
      liftConfig (program (depth p) (seedWidth p)) (initial (width p x) (depth p) (seedWidth p) x) := by
  rw [input, ULogPayloadClockBitWrapper.same_start,
    StandardBitCountedPolynomialPayload.payload_layout, ← source_eq]
  exact (ULogTernaryGuardedPumpDelimiter.initial_lift (width p x) (depth p) (seedWidth p) x).symm

theorem deadline_upper (p : Polynomial Nat) (x : List Bool) :
    deadline p x ≤ 43 * (2 ^ width p x) ^ 2 := by
  have hD : ULogTernaryGuardedPumpSentinelInput.deadline p x ≤
      23 * (2 ^ width p x) ^ 2 := ULogTernaryGuardedPumpSentinelInput.deadline_upper p x
  have hs := source_fits p x
  have hsrc : (source p x).length =
      (ULogTernaryNestedHeaderParser.header (depth p) (seedWidth p) x).length +
        2 * x.length + 1 := by
    simp [source, ULogTernaryGuardedPumpSentinel.source,
      ULogTernaryNestedHeaderParser.nested_length,
      ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
  have hn : x.length ≤ 2 ^ width p x := by omega
  have hn2 := Nat.mul_le_mul hn hn
  have hRpos : 0 < 2 ^ width p x := by positivity
  have hR : 1 ≤ 2 ^ width p x := by omega
  have hR2 : 2 ^ width p x ≤ (2 ^ width p x) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  change ULogTernaryGuardedPumpSentinelInput.deadline p x + 2 +
    ULogTernaryCountedSourceDelimiter.deadline x.length ≤ _
  unfold ULogTernaryCountedSourceDelimiter.deadline
  rw [pow_two] at hD hR2 ⊢
  nlinarith

theorem deadline_le_clock (p : Polynomial Nat) (x : List Bool) :
    deadline p x ≤ 2 ^ clockWidth p x := by
  have hD := deadline_upper p x
  have hs := source_length_ge p x
  have hfactor : 64 ≤ 2 ^ (2 * (source p x).length + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 6 ≤ 2 * (source p x).length + 3)
  have hsum : clockWidth p x = 2 * width p x + (2 * (source p x).length + 3) := by
    unfold clockWidth
    omega
  have hsq : (2 ^ width p x) ^ 2 = 2 ^ (2 * width p x) := by
    rw [Nat.mul_comm 2, pow_mul]
  rw [hsq] at hD
  rw [hsum, pow_add]
  exact hD.trans (by nlinarith)

theorem actual_run (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input p x)) (List.replicate (deadline p x) false) =
      some (liftConfig (program (depth p) (seedWidth p)) (final (width p x) (depth p) (seedWidth p) x)) := by
  rw [start_input, ← run_lift (program (depth p) (seedWidth p)) (2 : Fin 3) rfl _ 0]
  rw [show run (program (depth p) (seedWidth p)) 2 (List.replicate (deadline p x) false)
      0 (initial (width p x) (depth p) (seedWidth p) x) = _ from
    ULogTernaryGuardedPumpDelimiter.actual_run (width p x) (depth p) (seedWidth p) (seed_positive p) x]
  rfl

theorem all_cutoff_counts (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if deadline p x ≤ T then 1 else 0 := by
  rw [start_input]
  exact ULogTernaryGuardedPumpDelimiter.all_cutoff_counts (width p x) (depth p) (seedWidth p) T (seed_positive p) x

theorem every_raw_clock (p : Polynomial Nat) (x w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input p x)) w = some out) :
    w.length ≤ 2 ^ clockWidth p x := by
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, _⟩ := ULogFiniteAlphabetDeterministicRuns.successful_semantic_of_zipper
    (2 : Fin 3) rfl (program (depth p) (seedWidth p)) hw (head := 0)
  exact (ULogTernaryGuardedPumpDelimiter.every_raw_length (width p x) (depth p) (seedWidth p) (seed_positive p) x w hf zf hz).2.trans
    (deadline_le_clock p x)

theorem every_raw_clock_symbols_space (p : Polynomial Nat) (x w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (ULogSemantics.start (input p x)) w = some out) :
    w.length ≤ 2 ^ clockWidth p x ∧ SemanticTapeSymbolsLtThree out ∧
      out.leftRev.length + 1 + out.right.length ≤
        ULogTernaryGuardedPumpDelimiterSpace.peak (width p x) (depth p) (seedWidth p) x := by
  have ht := every_raw_clock p x w out hw
  rw [start_input] at hw
  obtain ⟨⟨hf, zf⟩, hz, he⟩ := ULogFiniteAlphabetDeterministicRuns.successful_semantic_of_zipper
    (2 : Fin 3) rfl (program (depth p) (seedWidth p)) hw (head := 0)
  rw [← he]
  refine ⟨ht, ULogTernaryPumpInputSpec.lift_symbols _ _, ?_⟩
  have hs := (ULogTernaryGuardedPumpDelimiterSpace.every_raw_space (width p x) (depth p) (seedWidth p) (seed_positive p)
    x w hf zf hz).1
  simpa [liftConfig, ULogFiniteTapeGrowthLedger.cellCount] using hs

theorem actual_delimiter_resource_spec (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, semanticRun (ULogSemantics.start (input p x)) (List.replicate (deadline p x) false) =
      some (liftConfig (program (depth p) (seedWidth p)) (final (width p x) (depth p) (seedWidth p) x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if deadline p x ≤ T then 1 else 0) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input p x)) w = some out →
      w.length ≤ 2 ^ clockWidth p x ∧ SemanticTapeSymbolsLtThree out ∧
        out.leftRev.length + 1 + out.right.length ≤
          ULogTernaryGuardedPumpDelimiterSpace.peak (width p x) (depth p) (seedWidth p) x) ∧
    (∀ x w hf zf,
      run (program (depth p) (seedWidth p)) 2 w 0 (initial (width p x) (depth p) (seedWidth p) x) =
        some (hf, zf) →
      ∃ lg rg, ULogFiniteTapeGrowthLedger.GrowthRun (program (depth p) (seedWidth p)) 2 w 0
        (initial (width p x) (depth p) (seedWidth p) x) hf zf lg rg ∧ lg ≤ 1 ∧ rg ≤ 2 ^ width p x ∧
        ∀ C tail, 2 ^ width p x + (ULogTernaryGuardedPumpDelimiter.totalStates (depth p) (seedWidth p) - 1) ≤ C →
          ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program (depth p) (seedWidth p)) w 0
            (initial (width p x) (depth p) (seedWidth p) x) C (MStarConcreteAlphabet.work :: tail) ∧
          ULogFiniteTapePhysicalResourceLedger.resourceRun (program (depth p) (seedWidth p)) 2 w 0
            (initial (width p x) (depth p) (seedWidth p) x) C (MStarConcreteAlphabet.work :: tail) =
              some (hf, zf, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg)) ∧
    (∀ x, decodeBinaryClock (List.replicate (clockWidth p x) (ulogCore clockZero) ++
      ulogCore clockOne :: [ulogCore clockSep]) = some (2 ^ clockWidth p x)) ∧
    (∀ x C tail,
      ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program (depth p) (seedWidth p))
        (List.replicate (deadline p x) false) 0 (initial (width p x) (depth p) (seedWidth p) x)
        C (MStarConcreteAlphabet.work :: tail) ↔
      2 ^ width p x + (ULogTernaryGuardedPumpDelimiter.totalStates (depth p) (seedWidth p) - 1) ≤ C) := by
  refine ⟨input_polyBitTime p, StandardBitCountedPolynomialPayload.width_dominates p,
    actual_run p, all_cutoff_counts p, every_raw_clock_symbols_space p, ?_, ?_, ?_⟩
  · intro x w hf zf hw
    exact ULogTernaryGuardedPumpDelimiterSpace.every_raw_ready (width p x) (depth p) (seedWidth p) (seed_positive p) x w hf zf hw
  · intro x
    exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth p x) []
  · intro x C tail
    exact ULogTernaryGuardedPumpDelimiterResources.full_active_ready_iff
      (width p x) (depth p) (seedWidth p) (seed_positive p) x C tail

theorem actual_delimiter_input_spec (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, semanticRun (ULogSemantics.start (input p x)) (List.replicate (deadline p x) false) =
      some (liftConfig (program (depth p) (seedWidth p)) (final (width p x) (depth p) (seedWidth p) x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if deadline p x ≤ T then 1 else 0) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input p x)) w = some out → w.length ≤ 2 ^ clockWidth p x) ∧
    (∀ x, decodeBinaryClock (List.replicate (clockWidth p x) (ulogCore clockZero) ++
      ulogCore clockOne :: [ulogCore clockSep]) = some (2 ^ clockWidth p x)) := by
  refine ⟨input_polyBitTime p, StandardBitCountedPolynomialPayload.width_dominates p,
    actual_run p, all_cutoff_counts p, every_raw_clock p, ?_⟩
  intro x
  exact ULogRetainedPumpClockBitInput.power_clock_decode (clockWidth p x) []

end PakFixedPolyomino.ULogTernaryGuardedPumpDelimiterInput
