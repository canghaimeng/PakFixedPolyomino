import PakFixedPolyomino.Lattice
import Mathlib.Tactic

namespace PakFixedPolyomino

/-- The common three-cell plug from accepted Fact `de84a98c2f64a47e`. -/
def plugL : Polyomino := {(0, 1), (1, 0), (1, 1)}

@[simp] theorem mem_plugL (p : Cell) :
    p ∈ plugL ↔ p = (0, 1) ∨ p = (1, 0) ∨ p = (1, 1) := by
  simp [plugL]

@[simp] theorem card_plugL : plugL.card = 3 := by
  decide

theorem plugL_fourConnected : FourConnected plugL := by
  refine ⟨by simp [plugL], ?_⟩
  intro a ha b hb
  have toHub : ∀ ⦃z⦄, z ∈ plugL → Walk4In plugL z (1, 1) := by
    intro z hz
    simp only [mem_plugL] at hz
    rcases hz with rfl | rfl | rfl
    · exact .cons (by simp [plugL]) (by simp [Adj4]) (.nil (by simp [plugL]))
    · exact .cons (by simp [plugL]) (by simp [Adj4]) (.nil (by simp [plugL]))
    · exact .nil (by simp [plugL])
  let append : ∀ {x y z}, Walk4In plugL x y → Walk4In plugL y z → Walk4In plugL x z := by
    intro x y z w₁ w₂
    induction w₁ with
    | nil _ => exact w₂
    | cons hx hxy _ ih => exact .cons hx hxy (ih w₂)
  exact append (toHub ha) (toHub hb).symm

/-- The cavity at origin `q`; it is an exact translate of `plugL`. -/
def cavity (q : Cell) : Polyomino := translate plugL q

@[simp] theorem card_cavity (q : Cell) : (cavity q).card = 3 := by
  simp [cavity]

theorem cavity_fourConnected (q : Cell) : FourConnected (cavity q) := by
  exact plugL_fourConnected.translate q

theorem cavity_coordinate_sum (q : Cell) :
    ((cavity q).sum fun p => p.1, (cavity q).sum fun p => p.2) =
      (3 * q.1 + 2, 3 * q.2 + 2) := by
  simp [cavity, translate, plugL]
  constructor <;> ring

/-- Cavity positions are geometric identities, not invisible labels. -/
theorem cavity_injective : Function.Injective cavity := by
  intro q r h
  have hs := congrArg (fun P : Polyomino =>
    (P.sum fun p => p.1, P.sum fun p => p.2)) h
  rw [cavity_coordinate_sum, cavity_coordinate_sum] at hs
  apply Prod.ext
  · have := congrArg Prod.fst hs
    dsimp at this ⊢
    omega
  · have := congrArg Prod.snd hs
    dsimp at this ⊢
    omega

/-- The mixed-radix boundary code used on horizontal and vertical sides. -/
def registerCode (s idx ell a b : ℕ) : ℕ :=
  8 + 4 * (s * idx + ell) + 2 * a + b

theorem registerCode_bounds {s h idx ell a b : ℕ}
    (hs : 0 < s) (hi : idx < h) (hell : ell < s) (ha : a < 2) (hb : b < 2) :
    8 ≤ registerCode s idx ell a b ∧
      registerCode s idx ell a b ≤ 4 * s * h + 7 := by
  constructor
  · unfold registerCode
    omega
  · unfold registerCode
    have hmix : s * idx + ell < s * h := by
      calc
        s * idx + ell < s * idx + s := Nat.add_lt_add_left hell _
        _ = s * (idx + 1) := by rw [Nat.mul_succ]
        _ ≤ s * h := Nat.mul_le_mul_left s (Nat.succ_le_iff.mpr hi)
    have hsmall : 2 * a + b ≤ 3 := by omega
    have hqsucc : s * idx + ell + 1 ≤ s * h := Nat.succ_le_iff.mpr hmix
    have hnear : 4 * (s * idx + ell) + (2 * a + b) <
        4 * (s * idx + ell + 1) := by omega
    have hscale : 4 * (s * idx + ell + 1) ≤ 4 * (s * h) :=
      Nat.mul_le_mul_left 4 hqsucc
    have hterm : 4 * (s * idx + ell) + (2 * a + b) < 4 * (s * h) :=
      lt_of_lt_of_le hnear hscale
    rw [show 4 * (s * h) = 4 * s * h by ring] at hterm
    omega

private theorem mixedRadix_injective {s i j e f : ℕ} (hs : 0 < s)
    (he : e < s) (hf : f < s) (h : s * i + e = s * j + f) : i = j ∧ e = f := by
  have hdivi : (s * i + e) / s = i := by
    rw [Nat.mul_add_div hs, Nat.div_eq_of_lt he]
    simp
  have hdivj : (s * j + f) / s = j := by
    rw [Nat.mul_add_div hs, Nat.div_eq_of_lt hf]
    simp
  have hij : i = j := by simpa [hdivi, hdivj] using congrArg (· / s) h
  subst j
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- Exact injectivity of `(side bits, colour index, amplifier label)`. -/
theorem registerCode_injective {s i j e f a b c d : ℕ}
    (hs : 0 < s) (he : e < s) (hf : f < s)
    (ha : a < 2) (hb : b < 2) (hc : c < 2) (hd : d < 2)
    (hcode : registerCode s i e a b = registerCode s j f c d) :
    i = j ∧ e = f ∧ a = c ∧ b = d := by
  have hrem₁ : 2 * a + b < 4 := by omega
  have hrem₂ : 2 * c + d < 4 := by omega
  have hq : s * i + e = s * j + f := by
    unfold registerCode at hcode
    omega
  have hr : 2 * a + b = 2 * c + d := by
    unfold registerCode at hcode
    omega
  obtain ⟨hij, hef⟩ := mixedRadix_injective hs he hf hq
  have hab : a = c ∧ b = d := by omega
  exact ⟨hij, hef, hab.1, hab.2⟩

/-- Closed carriers retain geometric tile identity through their cavities. -/
def closedCarrier (p : ℕ) (q : Cell) : Polyomino := square p \ cavity q

theorem closedCarrier_injective_on {p : ℕ} {q r : Cell}
    (hq : cavity q ⊆ square p) (hr : cavity r ⊆ square p)
    (h : closedCarrier p q = closedCarrier p r) : q = r := by
  apply cavity_injective
  ext x
  have hxq := hq
  have hxr := hr
  have hc := Finset.ext_iff.mp h x
  simp only [closedCarrier, Finset.mem_sdiff] at hc
  by_cases hx : x ∈ square p
  · simpa [hx] using not_congr hc
  · have hnq : x ∉ cavity q := fun hmem => hx (hq hmem)
    have hnr : x ∉ cavity r := fun hmem => hx (hr hmem)
    simp [hnq, hnr]

end PakFixedPolyomino
