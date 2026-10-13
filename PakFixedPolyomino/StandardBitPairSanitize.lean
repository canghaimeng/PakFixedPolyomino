import PakFixedPolyomino.StandardBitConditionalBitTime
import PakFixedPolyomino.StandardBitPairValidity
import PakFixedPolyomino.StandardBitPairProjection
import PakFixedPolyomino.StandardBitMealy
import PakFixedPolyomino.StandardBitNormalize
import PakFixedPolyomino.StandardBitPrepend

/-! Total physical format sanitization. Every valid literal pair is unchanged;
malformed words become the literal empty pair [false]. -/
namespace PakFixedPolyomino.StandardBitPairSanitize
open StandardBitTime StandardBitMetric StandardBinaryWordNormalization

def zeroDelta (q : Fin 1) (_b : Bool) : Fin 1 × Bool := (q,false)

theorem zero_scan_normalize (w : List Bool) :
    normalizeBits (StandardBitMealy.transform zeroDelta 0 w)=[] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [StandardBitMealy.transform,zeroDelta,normalizeBits,ih]

theorem empty_polyBitTime : PolyBitTime (fun _ : List Bool => []) := by
  have h := StandardBitTimeComposition.polyBitTime_comp
    (StandardBitMealy.transducer_polyBitTime zeroDelta 0) StandardBitNormalize.normalize_polyBitTime
  have he : normalizeBits ∘ StandardBitMealy.transform zeroDelta 0=(fun _ : List Bool => []) :=
    funext zero_scan_normalize
  exact he ▸ h

theorem false_polyBitTime : PolyBitTime (fun _ : List Bool => [false]) := by
  simpa only [Function.comp_def] using StandardBitTimeComposition.polyBitTime_comp
    empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)

def sanitize (w : List Bool) : List Bool :=
  if StandardBitPairValidity.valid w then w else [false]

theorem sanitize_polyBitTime : PolyBitTime sanitize :=
  StandardBitConditionalBitTime.conditional_polyBitTime StandardBitPairValidity.valid
    (fun _ => [false]) id StandardBitPairValidity.validity_polyBitTime false_polyBitTime identity_polyBitTime

theorem sanitize_pair (x y : List Bool) : sanitize (pairBits x y)=pairBits x y := by
  simp [sanitize,StandardBitPairValidity.valid]

theorem sanitize_none (w : List Bool) (h : unpairBits w=none) : sanitize w=[false] := by
  simp [sanitize,StandardBitPairValidity.valid,h]

theorem sanitize_valid (w : List Bool) : ∃ x y, sanitize w=pairBits x y := by
  cases h : unpairBits w with
  | none => exact ⟨[],[],sanitize_none w h⟩
  | some z =>
    obtain ⟨x,y⟩ := z
    have he : w=pairBits x y := StandardBitPairProjection.unpairBits_eq_some.mp h
    exact ⟨x,y,by rw [he,sanitize_pair]⟩

theorem sanitize_length (w : List Bool) : (sanitize w).length≤w.length+1 := by
  unfold sanitize
  split <;> simp <;> omega

end PakFixedPolyomino.StandardBitPairSanitize
