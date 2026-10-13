import PakFixedPolyomino.StandardBitConditionalBitTime
import PakFixedPolyomino.StandardBitAppend
import PakFixedPolyomino.StandardBitPairSanitize

/-! Ordinary tape-time compilation of fixed literal constants and Boolean
combinations. Conditional control physically restores its input before the
selected branch. These closures carry all tape costs, rather than counting
Boolean operations as standard time. -/
namespace PakFixedPolyomino.StandardBitBooleanMaps
open StandardBitTime StandardBitTimeComposition

theorem constant_word_polyBitTime (w : List Bool) :
    PolyBitTime (fun _ : List Bool => w) := by
  simpa only [Function.comp_def,List.nil_append] using polyBitTime_comp
    StandardBitPairSanitize.empty_polyBitTime (StandardBitAppend.fixed_suffix_polyBitTime w)

theorem constant_bool_polyBitTime (b : Bool) :
    PolyBitTime (fun _ : List Bool => [b]) := constant_word_polyBitTime [b]

theorem not_polyBitTime (b : List Bool → Bool) (hb : PolyBitTime (fun raw => [b raw])) :
    PolyBitTime (fun raw => [!b raw]) := by
  have h := StandardBitConditionalBitTime.conditional_polyBitTime b
    (fun _ => [true]) (fun _ => [false]) hb
    (constant_bool_polyBitTime true) (constant_bool_polyBitTime false)
  have he : StandardBitProtectedConditional.conditional b (fun _ => [true])
      (fun _ => [false])=(fun raw => [!b raw]) := by
    funext raw;unfold StandardBitProtectedConditional.conditional;cases b raw <;> rfl
  rwa [he] at h

theorem and_polyBitTime (b c : List Bool → Bool)
    (hb : PolyBitTime (fun raw => [b raw])) (hc : PolyBitTime (fun raw => [c raw])) :
    PolyBitTime (fun raw => [b raw && c raw]) := by
  have h := StandardBitConditionalBitTime.conditional_polyBitTime b
    (fun _ => [false]) (fun raw => [c raw]) hb (constant_bool_polyBitTime false) hc
  have he : StandardBitProtectedConditional.conditional b (fun _ => [false])
      (fun raw => [c raw])=(fun raw => [b raw && c raw]) := by
    funext raw;unfold StandardBitProtectedConditional.conditional;cases b raw <;> rfl
  rwa [he] at h

theorem or_polyBitTime (b c : List Bool → Bool)
    (hb : PolyBitTime (fun raw => [b raw])) (hc : PolyBitTime (fun raw => [c raw])) :
    PolyBitTime (fun raw => [b raw || c raw]) := by
  have h := StandardBitConditionalBitTime.conditional_polyBitTime b
    (fun raw => [c raw]) (fun _ => [true]) hb hc (constant_bool_polyBitTime true)
  have he : StandardBitProtectedConditional.conditional b (fun raw => [c raw])
      (fun _ => [true])=(fun raw => [b raw || c raw]) := by
    funext raw;unfold StandardBitProtectedConditional.conditional;cases b raw <;> rfl
  rwa [he] at h

end PakFixedPolyomino.StandardBitBooleanMaps
