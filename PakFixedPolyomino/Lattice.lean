import Mathlib

namespace PakFixedPolyomino

abbrev Cell := ℤ × ℤ
abbrev Polyomino := Finset Cell

/-- The integer cells with coordinates `0, ..., n-1`. -/
def natInterval (n : ℕ) : Finset ℤ :=
  (Finset.range n).image Int.ofNat

/-- A discrete rectangle based at the origin. -/
def rectangle (w h : ℕ) : Polyomino :=
  (natInterval w).product (natInterval h)

/-- The discrete `n × n` square. -/
def square (n : ℕ) : Polyomino := rectangle n n

/-- Translation is the only allowed motion. -/
def translate (P : Polyomino) (v : Cell) : Polyomino :=
  P.image fun p => (p.1 + v.1, p.2 + v.2)

@[simp] theorem mem_natInterval {z : ℤ} {n : ℕ} :
    z ∈ natInterval n ↔ ∃ k < n, (k : ℤ) = z := by
  simp [natInterval]

@[simp] theorem card_natInterval (n : ℕ) : (natInterval n).card = n := by
  simpa [natInterval] using
    Finset.card_image_of_injective (Finset.range n) Int.ofNat_injective

@[simp] theorem card_rectangle (w h : ℕ) : (rectangle w h).card = w * h := by
  simp [rectangle]

@[simp] theorem ofNat_pair_mem_rectangle {x y w h : ℕ} :
    ((x : ℤ), (y : ℤ)) ∈ rectangle w h ↔ x < w ∧ y < h := by
  simp [rectangle]

@[simp] theorem ofNat_pair_mem_square {x y n : ℕ} :
    ((x : ℤ), (y : ℤ)) ∈ square n ↔ x < n ∧ y < n := by
  simp [square]

@[simp] theorem card_square (n : ℕ) : (square n).card = n ^ 2 := by
  simp [square, pow_two]

@[simp] theorem square_zero : square 0 = ∅ := by
  simp [square, rectangle, natInterval]

theorem mem_square_coord_bounds {n : ℕ} {z : Cell} (hz : z ∈ square n) :
    0 ≤ z.1 ∧ z.1 < n ∧ 0 ≤ z.2 ∧ z.2 < n := by
  have hp := Finset.mem_product.mp hz
  rcases mem_natInterval.mp hp.1 with ⟨x, hx, hxeq⟩
  rcases mem_natInterval.mp hp.2 with ⟨y, hy, hyeq⟩
  omega

@[simp] theorem mem_translate {P : Polyomino} {v p : Cell} :
    p ∈ translate P v ↔ (p.1 - v.1, p.2 - v.2) ∈ P := by
  constructor
  · simp only [translate, Finset.mem_image]
    rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    refine Finset.mem_image.mpr ⟨(p.1 - v.1, p.2 - v.2), hp, ?_⟩
    ext <;> simp

@[simp] theorem translate_zero (P : Polyomino) : translate P (0, 0) = P := by
  ext p
  simp

theorem translate_translate (P : Polyomino) (u v : Cell) :
    translate (translate P u) v = translate P (u.1 + v.1, u.2 + v.2) := by
  ext z
  simp [mem_translate]
  constructor <;> intro h <;> convert h using 1 <;> ext <;> ring

theorem disjoint_translate_both {P Q : Polyomino} {v : Cell}
    (h : Disjoint P Q) : Disjoint (translate P v) (translate Q v) := by
  rw [Finset.disjoint_left] at h ⊢
  intro z hzP hzQ
  exact h (mem_translate.mp hzP) (mem_translate.mp hzQ)

theorem translate_injective (v : Cell) : Function.Injective (fun P => translate P v) := by
  intro P Q h
  ext p
  have hp := Finset.ext_iff.mp h (p.1 + v.1, p.2 + v.2)
  simpa using hp

@[simp] theorem card_translate (P : Polyomino) (v : Cell) :
    (translate P v).card = P.card := by
  unfold translate
  apply Finset.card_image_of_injective
  intro a b h
  apply Prod.ext
  · exact add_right_cancel (congrArg Prod.fst h)
  · exact add_right_cancel (congrArg Prod.snd h)

/-- Four-neighbour adjacency on lattice cells. -/
def Adj4 (a b : Cell) : Prop :=
  b = (a.1 + 1, a.2) ∨ b = (a.1 - 1, a.2) ∨
  b = (a.1, a.2 + 1) ∨ b = (a.1, a.2 - 1)

theorem adj4_symm {a b : Cell} : Adj4 a b → Adj4 b a := by
  rintro (h | h | h | h) <;> subst b <;> simp [Adj4]

theorem adj4_translate {a b v : Cell} (h : Adj4 a b) :
    Adj4 (a.1 + v.1, a.2 + v.2) (b.1 + v.1, b.2 + v.2) := by
  rcases h with h | h | h | h <;> subst b
  · left; apply Prod.ext <;> simp <;> omega
  · right; left; apply Prod.ext <;> simp <;> omega
  · right; right; left; apply Prod.ext <;> simp <;> omega
  · right; right; right; apply Prod.ext <;> simp <;> omega

/-- A finite walk whose vertices stay in `P`. -/
inductive Walk4In (P : Polyomino) : Cell → Cell → Prop
  | nil {a} (ha : a ∈ P) : Walk4In P a a
  | cons {a b c} (ha : a ∈ P) (hab : Adj4 a b) (w : Walk4In P b c) :
      Walk4In P a c

def FourConnected (P : Polyomino) : Prop :=
  P.Nonempty ∧ ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → Walk4In P a b

theorem Walk4In.translate {P : Polyomino} {a b v : Cell} (w : Walk4In P a b) :
    Walk4In (translate P v) (a.1 + v.1, a.2 + v.2) (b.1 + v.1, b.2 + v.2) := by
  induction w with
  | nil ha =>
      exact .nil (Finset.mem_image.mpr ⟨_, ha, rfl⟩)
  | cons ha hab _ ih =>
      exact .cons (Finset.mem_image.mpr ⟨_, ha, rfl⟩) (adj4_translate hab) ih

theorem Walk4In.symm {P : Polyomino} {a b : Cell} (w : Walk4In P a b) :
    Walk4In P b a := by
  let sourceMem : ∀ {x y}, Walk4In P x y → x ∈ P := by
    intro x y walk
    cases walk with
    | nil hx => exact hx
    | cons hx _ _ => exact hx
  let append : ∀ {x y z}, Walk4In P x y → Walk4In P y z → Walk4In P x z := by
    intro x y z w₁ w₂
    induction w₁ with
    | nil _ => exact w₂
    | cons hx hxy _ ih => exact .cons hx hxy (ih w₂)
  induction w with
  | nil ha => exact .nil ha
  | @cons a b c ha hab w ih =>
      exact append ih (.cons (sourceMem w) (adj4_symm hab) (.nil ha))

theorem FourConnected.translate {P : Polyomino} (hP : FourConnected P) (v : Cell) :
    FourConnected (translate P v) := by
  constructor
  · rcases hP.1 with ⟨p, hp⟩
    exact ⟨(p.1 + v.1, p.2 + v.2), Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  · intro a ha b hb
    let a₀ : Cell := (a.1 - v.1, a.2 - v.2)
    let b₀ : Cell := (b.1 - v.1, b.2 - v.2)
    have ha₀ : a₀ ∈ P := by simpa [a₀] using (mem_translate.mp ha)
    have hb₀ : b₀ ∈ P := by simpa [b₀] using (mem_translate.mp hb)
    have w := (hP.2 ha₀ hb₀).translate (v := v)
    convert w using 1 <;> ext <;> simp [a₀, b₀]

/-- A certified horizontal segment gives a four-neighbour walk. -/
theorem walk4_right {P : Polyomino} (x y : ℤ) (k : ℕ)
    (hmem : ∀ i ≤ k, (x + i, y) ∈ P) :
    Walk4In P (x, y) (x + k, y) := by
  induction k generalizing x with
  | zero => simpa using Walk4In.nil (hmem 0 (by decide))
  | succ k ih =>
      have h0 : (x, y) ∈ P := by simpa using hmem 0 (by omega)
      have hadj : Adj4 (x, y) (x + 1, y) := by left; rfl
      have htail : ∀ i ≤ k, (x + 1 + i, y) ∈ P := by
        intro i hi
        have hm := hmem (i + 1) (by omega)
        convert hm using 1 <;> norm_num <;> push_cast <;> ring
      have w := ih (x + 1) htail
      apply Walk4In.cons h0 hadj
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> ring

/-- A certified vertical segment gives a four-neighbour walk. -/
theorem walk4_up {P : Polyomino} (x y : ℤ) (k : ℕ)
    (hmem : ∀ i ≤ k, (x, y + i) ∈ P) :
    Walk4In P (x, y) (x, y + k) := by
  induction k generalizing y with
  | zero => simpa using Walk4In.nil (hmem 0 (by decide))
  | succ k ih =>
      have h0 : (x, y) ∈ P := by simpa using hmem 0 (by omega)
      have hadj : Adj4 (x, y) (x, y + 1) := by right; right; left; rfl
      have htail : ∀ i ≤ k, (x, y + 1 + i) ∈ P := by
        intro i hi
        have hm := hmem (i + 1) (by omega)
        convert hm using 1 <;> norm_num <;> push_cast <;> ring
      have w := ih (y + 1) htail
      apply Walk4In.cons h0 hadj
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> ring

theorem walk4_left {P : Polyomino} (x y : ℤ) (k : ℕ)
    (hmem : ∀ i ≤ k, (x + i, y) ∈ P) :
    Walk4In P (x + k, y) (x, y) := (walk4_right x y k hmem).symm

theorem walk4_down {P : Polyomino} (x y : ℤ) (k : ℕ)
    (hmem : ∀ i ≤ k, (x, y + i) ∈ P) :
    Walk4In P (x, y + k) (x, y) := (walk4_up x y k hmem).symm

theorem Walk4In.mono {P Q : Polyomino} (hPQ : P ⊆ Q)
    {a b : Cell} (w : Walk4In P a b) : Walk4In Q a b := by
  induction w with
  | nil ha => exact .nil (hPQ ha)
  | cons ha hab _ ih => exact .cons (hPQ ha) hab ih

theorem Walk4In.trans {P : Polyomino} {a b c : Cell}
    (w₁ : Walk4In P a b) (w₂ : Walk4In P b c) : Walk4In P a c := by
  induction w₁ with
  | nil _ => exact w₂
  | cons ha hab _ ih => exact .cons ha hab (ih w₂)

/-- A connected spine plus a route from every vertex to the spine proves
four-connectivity. -/
theorem fourConnected_of_spine {P S : Polyomino}
    (hS : FourConnected S) (hSP : S ⊆ P)
    (hroute : ∀ ⦃x⦄, x ∈ P → ∃ s ∈ S, Walk4In P x s) : FourConnected P := by
  constructor
  · rcases hS.1 with ⟨s, hs⟩
    exact ⟨s, hSP hs⟩
  · intro a ha b hb
    rcases hroute ha with ⟨sa, hsa, wa⟩
    rcases hroute hb with ⟨sb, hsb, wb⟩
    have ws := (hS.2 hsa hsb).mono hSP
    exact wa.trans (ws.trans wb.symm)

end PakFixedPolyomino
