import PakFixedPolyomino.ULogRetainedCounterPumpCounts

/-! Actual decoded one-cell time estimates for the source-retaining pump.
Source length is charged, and its comparison with the generated window is
explicit. Physical interpreter time, prefix peak and input BIT construction
are separate obligations; these are not arithmetic-operation cost claims. -/

namespace PakFixedPolyomino.ULogRetainedCounterPumpResourceBounds

open ULogRetainedCounterPumpCounts

theorem bodyFuel_lower (k : Nat) (source : List Bool) :
    (2 ^ k) ^ 2 ≤ bodyFuel k source := by
  have hp : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (by positivity)
  have hm := Nat.mul_le_mul_left (2 * k + 2 * source.length + 8) hp
  simp only [Nat.mul_one] at hm
  unfold bodyFuel
  omega

theorem deadline_upper (k : Nat) (source : List Bool)
    (hsource : source.length ≤ 2 ^ k) : deadline k source ≤ 15 * (2 ^ k) ^ 2 := by
  have hp : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (by positivity)
  have hk : k + 1 ≤ 2 ^ k := k.lt_two_pow_self
  have hs := Nat.mul_le_mul_right (2 ^ k) hsource
  have hb : bodyFuel k source ≤
      (2 ^ k) ^ 2 + (2 * k + 2 * source.length + 8) * 2 ^ k := by
    unfold bodyFuel; omega
  unfold deadline
  nlinarith

theorem every_raw_time_upper (k : Nat) (source : List Bool)
    (hsource : source.length ≤ 2 ^ k) (w : List Bool) (out : ULogSemantics.Config)
    (hw : ULogFiniteTapeZipperRun.semanticRun
      (ULogSemantics.start (ULogRetainedCounterPump.input k source)) w = some out) :
    w.length ≤ 15 * (2 ^ k) ^ 2 :=
  (every_raw_prefix_length_le k source w out hw).trans (deadline_upper k source hsource)

theorem width_length_time (x : List Bool) (w : List Bool) (out : ULogSemantics.Config)
    (hw : ULogFiniteTapeZipperRun.semanticRun
      (ULogSemantics.start (ULogRetainedCounterPump.input x.length x)) w = some out) :
    w.length ≤ 15 * (2 ^ x.length) ^ 2 :=
  every_raw_time_upper x.length x (by have h := x.length.lt_two_pow_self; omega) w out hw

theorem final_right (k : Nat) (source : List Bool) :
    (finalConfig k source).right = source.map ULogSemantics.bitCode ++
      List.replicate (2 ^ k) 0 := by
  have hcells : (ULogCounterPumpBinarySteps.cells source).map Fin.val =
      source.map ULogSemantics.bitCode := by
    simp only [ULogCounterPumpBinarySteps.cells, List.map_map]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  simp [finalConfig, final, ULogCounterPump.fromCells, ULogCompiler.liftConfig, hcells]

theorem final_source_prefix (k : Nat) (source : List Bool) :
    (finalConfig k source).right.take source.length = source.map ULogSemantics.bitCode := by
  rw [final_right]
  simp

end PakFixedPolyomino.ULogRetainedCounterPumpResourceBounds
