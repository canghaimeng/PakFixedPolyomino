import PakFixedPolyomino.AnchoredRealization
import PakFixedPolyomino.MacroBijection
import PakFixedPolyomino.FinalReadout
import PakFixedPolyomino.TilingFinite
import Mathlib.Tactic

namespace PakFixedPolyomino

noncomputable section

set_option maxHeartbeats 4000000

local instance macroDataDecidableEqRegisterTile (P : RegisterParams) :
    DecidableEq (RegisterTile P) := Classical.decEq _

/-!
# The combinatorial decoder of an anchored register grid

This file is deliberately independent of the project root while it is being
developed.  It supplies the missing, unconditional equivalence between the
already extracted `AnchoredGrid` and the rectangular-partition/Wang/label
data counted by `MacroBijection`.
-/

/-- The Wang system literally stored in `RegisterParams`. -/
def registerWangTile (P : RegisterParams) :
    Fin P.tileCount → WangTile (Fin P.horizontalColours) (Fin P.verticalColours) :=
  fun u =>
    { west := P.west u
      east := P.east u
      south := P.south u
      north := P.north u }

/-- Number of macro cells in a grid rectangle. -/
def GridRectangle.area {n : ℕ} (B : GridRectangle n) : ℕ :=
  B.width.1 * B.height.1

/-- A rectangle is filled by an anchored opening pattern when every unit
edge whose two endpoints lie in it is open. -/
def GridRectangle.Filled {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (B : GridRectangle n) : Prop :=
  (∀ (i j : Fin n) (hi : i.1 + 1 < n),
      B.Contains (i, j) → B.Contains (⟨i.1 + 1, hi⟩, j) →
        A.openH i j = true) ∧
  (∀ (i j : Fin n) (hj : j.1 + 1 < n),
      B.Contains (i, j) → B.Contains (i, ⟨j.1 + 1, hj⟩) →
        A.openV i j = true)

instance {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) : Decidable (B.Filled A) := by
  unfold GridRectangle.Filled
  infer_instance

/-- The one-cell rectangle based at `p`. -/
def unitGridRectangle {n : ℕ} (p : MacroCell n) : GridRectangle n where
  x₀ := p.1
  y₀ := p.2
  width := ⟨1, Nat.lt_succ_iff.mpr (Nat.zero_lt_of_lt p.1.isLt)⟩
  height := ⟨1, Nat.lt_succ_iff.mpr (Nat.zero_lt_of_lt p.2.isLt)⟩
  width_pos := by exact Nat.zero_lt_one
  height_pos := by exact Nat.zero_lt_one
  x_bound := Nat.succ_le_iff.mpr p.1.isLt
  y_bound := Nat.succ_le_iff.mpr p.2.isLt

@[simp] theorem unitGridRectangle_contains {n : ℕ} (p : MacroCell n) :
    (unitGridRectangle p).Contains p := by
  simp [unitGridRectangle, GridRectangle.Contains]

@[simp] theorem unitGridRectangle_filled {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) :
    (unitGridRectangle p).Filled A := by
  constructor <;> intro i j hstep h₁ h₂ <;>
    simp [unitGridRectangle, GridRectangle.Contains] at h₁ h₂ <;> omega

/-- At every macro cell there is a filled rectangle of maximum area containing
that cell.  Finiteness makes the choice canonical enough for decoding; later
lemmas show that the result does not depend on any choice. -/
theorem exists_maximal_filled_rectangle {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) :
    ∃ B : GridRectangle n,
      B.Contains p ∧ B.Filled A ∧
      ∀ C : GridRectangle n, C.Contains p → C.Filled A → C.area ≤ B.area := by
  classical
  let candidates : Finset (GridRectangle n) :=
    Finset.univ.filter fun B => B.Contains p ∧ B.Filled A
  have hne : candidates.Nonempty := by
    refine ⟨unitGridRectangle p, ?_⟩
    simp [candidates]
  obtain ⟨B, hBmem, hBmax⟩ := candidates.exists_max_image GridRectangle.area hne
  refine ⟨B, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hBmem).2.1
  · exact (Finset.mem_filter.mp hBmem).2.2
  · intro C hp hfill
    exact hBmax C (by simp [candidates, hp, hfill])

def maximalFilledRectangle {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) : GridRectangle n :=
  Classical.choose (exists_maximal_filled_rectangle A p)

theorem maximalFilledRectangle_contains {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) :
    (maximalFilledRectangle A p).Contains p :=
  (Classical.choose_spec (exists_maximal_filled_rectangle A p)).1

theorem maximalFilledRectangle_filled {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) :
    (maximalFilledRectangle A p).Filled A :=
  (Classical.choose_spec (exists_maximal_filled_rectangle A p)).2.1

theorem maximalFilledRectangle_maximal {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (p : MacroCell n) (C : GridRectangle n)
    (hp : C.Contains p) (hfill : C.Filled A) :
    C.area ≤ (maximalFilledRectangle A p).area :=
  (Classical.choose_spec (exists_maximal_filled_rectangle A p)).2.2 C hp hfill

/-- Extend a rectangle by one row to the north. -/
def GridRectangle.extendNorth {n : ℕ} (B : GridRectangle n)
    (h : B.y₀.1 + B.height.1 < n) : GridRectangle n where
  x₀ := B.x₀
  y₀ := B.y₀
  width := B.width
  height := ⟨B.height.1 + 1, by omega⟩
  width_pos := B.width_pos
  height_pos := by
    change 0 < B.height.1 + 1
    omega
  x_bound := B.x_bound
  y_bound := by
    change B.y₀.1 + (B.height.1 + 1) ≤ n
    omega

theorem GridRectangle.contains_extendNorth {n : ℕ} (B : GridRectangle n)
    (h : B.y₀.1 + B.height.1 < n) {p : MacroCell n}
    (hp : B.Contains p) : (B.extendNorth h).Contains p := by
  unfold GridRectangle.Contains GridRectangle.extendNorth at *
  dsimp at *
  omega

theorem GridRectangle.contains_of_extendNorth_of_lt {n : ℕ}
    (B : GridRectangle n) (h : B.y₀.1 + B.height.1 < n)
    {p : MacroCell n} (hp : (B.extendNorth h).Contains p)
    (hy : p.2.1 < B.y₀.1 + B.height.1) : B.Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendNorth] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hy⟩

theorem GridRectangle.extendNorth_area {n : ℕ} (B : GridRectangle n)
    (h : B.y₀.1 + B.height.1 < n) :
    B.area < (B.extendNorth h).area := by
  simpa [GridRectangle.area, GridRectangle.extendNorth] using
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self B.height.1) B.width_pos

def HOpenAt {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (x y : ℕ) : Prop :=
  ∃ (hx : x < n) (hy : y < n), A.openH ⟨x, hx⟩ ⟨y, hy⟩ = true

def VOpenAt {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (x y : ℕ) : Prop :=
  ∃ (hx : x < n) (hy : y < n), A.openV ⟨x, hx⟩ ⟨y, hy⟩ = true

theorem hOpenAt_iff {P : RegisterParams} {n x y : ℕ}
    (A : AnchoredGrid P n) (hx : x < n) (hy : y < n) :
    HOpenAt A x y ↔ A.openH ⟨x, hx⟩ ⟨y, hy⟩ = true := by
  constructor
  · rintro ⟨hx', hy', h⟩
    simpa only [Subsingleton.elim hx' hx, Subsingleton.elim hy' hy] using h
  · exact fun h => ⟨hx, hy, h⟩

theorem vOpenAt_iff {P : RegisterParams} {n x y : ℕ}
    (A : AnchoredGrid P n) (hx : x < n) (hy : y < n) :
    VOpenAt A x y ↔ A.openV ⟨x, hx⟩ ⟨y, hy⟩ = true := by
  constructor
  · rintro ⟨hx', hy', h⟩
    simpa only [Subsingleton.elim hx' hx, Subsingleton.elim hy' hy] using h
  · exact fun h => ⟨hx, hy, h⟩

private theorem north_open_propagates_right
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ}
    (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : seed ≤ x) (hxHi : x < B.x₀.1 + B.width.1)
    (hnorth : B.y₀.1 + B.height.1 < n)
    (hseed : VOpenAt A seed (B.y₀.1 + B.height.1 - 1)) :
    VOpenAt A x (B.y₀.1 + B.height.1 - 1) := by
  induction x, hxLo using Nat.le_induction with
  | base => exact hseed
  | succ x hx ih =>
      have hxB : x < B.x₀.1 + B.width.1 := by omega
      have hxStep : x + 1 < n := by
        have hb := B.x_bound
        omega
      have hyStep : B.y₀.1 + B.height.1 - 1 + 1 < n := by
        have := B.height_pos
        omega
      have hxN : x < n := hxB.trans_le B.x_bound
      have hyN : B.y₀.1 + B.height.1 - 1 < n := by
        have hp := B.height_pos
        have hb := B.y_bound
        omega
      let ix : Fin n := ⟨x, hxN⟩
      let iy : Fin n := ⟨B.y₀.1 + B.height.1 - 1, hyN⟩
      have hbot : A.openH ix iy = true := by
        apply hfill.1 ix iy hxStep
        · unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          have := B.height_pos
          omega
        · unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          have := B.height_pos
          omega
      have ih' := (vOpenAt_iff A hxN hyN).mp (ih hxB)
      have hs := anchoredGrid_saturated A ix iy hxStep hyStep
      have hall := hs (Or.inr (Or.inr (Or.inr ⟨ih', hbot⟩)))
      exact (vOpenAt_iff A hxStep hyN).mpr (by simpa [ix, iy] using hall.2.1)

private theorem north_open_propagates_left
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ}
    (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : B.x₀.1 ≤ x) (hxHi : x ≤ seed)
    (hnorth : B.y₀.1 + B.height.1 < n)
    (hseed : VOpenAt A seed (B.y₀.1 + B.height.1 - 1)) :
    VOpenAt A x (B.y₀.1 + B.height.1 - 1) := by
  refine Nat.decreasingInduction' (n := seed) (m := x) ?_ hxHi hseed
  intro x hxseed hxbase ih
  have hxB : x < B.x₀.1 + B.width.1 := by omega
  have hxStep : x + 1 < n := by
    have hb := B.x_bound
    omega
  have hyStep : B.y₀.1 + B.height.1 - 1 + 1 < n := by
    have := B.height_pos
    omega
  have hxN : x < n := hxB.trans_le B.x_bound
  have hyN : B.y₀.1 + B.height.1 - 1 < n := by
    have hp := B.height_pos
    have hb := B.y_bound
    omega
  let ix : Fin n := ⟨x, hxN⟩
  let iy : Fin n := ⟨B.y₀.1 + B.height.1 - 1, hyN⟩
  have hbot : A.openH ix iy = true := by
    apply hfill.1 ix iy hxStep
    · unfold GridRectangle.Contains ix iy
      dsimp [ix, iy]
      have := B.height_pos
      omega
    · unfold GridRectangle.Contains ix iy
      dsimp [ix, iy]
      have := B.height_pos
      omega
  have ih' := (vOpenAt_iff A hxStep hyN).mp ih
  have hs := anchoredGrid_saturated A ix iy hxStep hyStep
  have hall := hs (Or.inl ⟨hbot, ih'⟩)
  exact (vOpenAt_iff A hxN hyN).mpr (by simpa [ix, iy] using hall.2.2.2)

private theorem north_open_everywhere
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ}
    (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : B.x₀.1 ≤ x) (hxHi : x < B.x₀.1 + B.width.1)
    (hnorth : B.y₀.1 + B.height.1 < n)
    (hseed : VOpenAt A seed (B.y₀.1 + B.height.1 - 1)) :
    VOpenAt A x (B.y₀.1 + B.height.1 - 1) := by
  by_cases h : seed ≤ x
  · exact north_open_propagates_right A B hfill hseedLo hseedHi h hxHi hnorth hseed
  · exact north_open_propagates_left A B hfill hseedLo hseedHi hxLo (by omega)
      hnorth hseed

/-- One open north-boundary edge of a filled rectangle forces the entire
north row, so adjoining that row is again filled. -/
theorem GridRectangle.extendNorth_filled
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    (hnorth : B.y₀.1 + B.height.1 < n)
    {seed : ℕ} (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hseed : VOpenAt A seed (B.y₀.1 + B.height.1 - 1)) :
    (B.extendNorth hnorth).Filled A := by
  constructor
  · intro i j hi hp hq
    by_cases hjOld : j.1 < B.y₀.1 + B.height.1
    · apply hfill.1 i j hi
      · exact B.contains_of_extendNorth_of_lt hnorth hp hjOld
      · exact B.contains_of_extendNorth_of_lt hnorth hq hjOld
    · have hj : j.1 = B.y₀.1 + B.height.1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hp
        dsimp at hp
        omega
      have hx0 : B.x₀.1 ≤ i.1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hp
        exact hp.1
      have hx1 : i.1 + 1 < B.x₀.1 + B.width.1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hq
        dsimp at hq
        omega
      have hv := north_open_everywhere A B hfill hseedLo hseedHi hx0
        (by omega) hnorth hseed
      let iy : Fin n := ⟨B.y₀.1 + B.height.1 - 1, by
        have := B.height_pos
        omega⟩
      have hbot : A.openH i iy = true := by
        apply hfill.1 i iy hi
        · unfold GridRectangle.Contains iy
          dsimp
          have := B.height_pos
          omega
        · unfold GridRectangle.Contains iy
          dsimp
          have := B.height_pos
          omega
      have hs := anchoredGrid_saturated A i iy hi (by
        dsimp [iy]
        have := B.height_pos
        omega)
      have hv' := (vOpenAt_iff (x := i.1)
        (y := B.y₀.1 + B.height.1 - 1) A i.isLt (by
        have hp := B.height_pos
        have hb := B.y_bound
        omega)).mp (by simpa only [Fin.eta] using hv)
      have hall := hs (Or.inr (Or.inr (Or.inr ⟨hv', hbot⟩)))
      have hjFin : ⟨iy.1 + 1, by
          dsimp [iy]
          have hp := B.height_pos
          omega⟩ = j := by
        apply Fin.ext
        dsimp [iy]
        have hp := B.height_pos
        omega
      simpa only [hjFin] using hall.2.2.1
  · intro i j hj hp hq
    by_cases htop : j.1 + 1 < B.y₀.1 + B.height.1
    · apply hfill.2 i j hj
      · exact B.contains_of_extendNorth_of_lt hnorth hp (by
          exact (Nat.lt_succ_self j.1).trans htop)
      · exact B.contains_of_extendNorth_of_lt hnorth hq htop
    · have hjEq : j.1 = B.y₀.1 + B.height.1 - 1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hp hq
        dsimp at hp hq
        have := B.height_pos
        omega
      have hx0 : B.x₀.1 ≤ i.1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hp
        exact hp.1
      have hx1 : i.1 < B.x₀.1 + B.width.1 := by
        unfold GridRectangle.Contains GridRectangle.extendNorth at hp
        exact hp.2.1
      have hv := north_open_everywhere A B hfill hseedLo hseedHi hx0 hx1
        hnorth hseed
      exact (vOpenAt_iff A i.isLt j.isLt).mp (by
        simpa only [hjEq, Fin.eta] using hv)

/-! The southern extension is the reflected version.  It is stated
separately so that no equality transport of dependent `AmpRecord`s enters the
pure opening argument. -/

def GridRectangle.extendSouth {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.y₀.1) : GridRectangle n where
  x₀ := B.x₀
  y₀ := ⟨B.y₀.1 - 1, by omega⟩
  width := B.width
  height := ⟨B.height.1 + 1, by
    have hb := B.y_bound
    omega⟩
  width_pos := B.width_pos
  height_pos := by change 0 < B.height.1 + 1; omega
  x_bound := B.x_bound
  y_bound := by
    change B.y₀.1 - 1 + (B.height.1 + 1) ≤ n
    have hb := B.y_bound
    omega

theorem GridRectangle.extendSouth_area {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.y₀.1) : B.area < (B.extendSouth h).area := by
  simpa [GridRectangle.area, GridRectangle.extendSouth] using
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self B.height.1) B.width_pos

theorem GridRectangle.contains_extendSouth {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.y₀.1) {p : MacroCell n} (hp : B.Contains p) :
    (B.extendSouth h).Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendSouth]
  have hb := B.y_bound
  omega

theorem GridRectangle.contains_of_extendSouth_of_ge {n : ℕ}
    (B : GridRectangle n) (h : 0 < B.y₀.1) {p : MacroCell n}
    (hp : (B.extendSouth h).Contains p) (hy : B.y₀.1 ≤ p.2.1) :
    B.Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendSouth] at hp
  have hb := B.y_bound
  omega

private theorem south_open_propagates_right
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ} (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : seed ≤ x) (hxHi : x < B.x₀.1 + B.width.1)
    (hsouth : 0 < B.y₀.1)
    (hseed : VOpenAt A seed (B.y₀.1 - 1)) :
    VOpenAt A x (B.y₀.1 - 1) := by
  induction x, hxLo using Nat.le_induction with
  | base => exact hseed
  | succ x hx ih =>
      have hxB : x < B.x₀.1 + B.width.1 := by omega
      have hxStep : x + 1 < n := by have hb := B.x_bound; omega
      have hyStep : B.y₀.1 - 1 + 1 < n := by
        have hb := B.y_bound
        omega
      have hxN : x < n := hxB.trans_le B.x_bound
      have hyN : B.y₀.1 - 1 < n := by omega
      let ix : Fin n := ⟨x, hxN⟩
      let iy : Fin n := ⟨B.y₀.1 - 1, hyN⟩
      have htop : A.openH ix ⟨iy.1 + 1, hyStep⟩ = true := by
        have hyEq : (⟨iy.1 + 1, hyStep⟩ : Fin n) = B.y₀ := by
          apply Fin.ext
          dsimp [iy]
          omega
        rw [hyEq]
        apply hfill.1 ix B.y₀ hxStep
        · unfold GridRectangle.Contains
          dsimp [ix]
          have hw := B.width_pos
          have hh := B.height_pos
          omega
        · unfold GridRectangle.Contains
          dsimp [ix]
          have hw := B.width_pos
          have hh := B.height_pos
          omega
      have ih' := (vOpenAt_iff A hxN hyN).mp (ih hxB)
      have hs := anchoredGrid_saturated A ix iy hxStep hyStep
      have hall := hs (Or.inr (Or.inr (Or.inl ⟨htop, ih'⟩)))
      exact (vOpenAt_iff A hxStep hyN).mpr (by simpa [ix, iy] using hall.2.1)

private theorem south_open_propagates_left
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ} (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : B.x₀.1 ≤ x) (hxHi : x ≤ seed)
    (hsouth : 0 < B.y₀.1)
    (hseed : VOpenAt A seed (B.y₀.1 - 1)) :
    VOpenAt A x (B.y₀.1 - 1) := by
  refine Nat.decreasingInduction' (n := seed) (m := x) ?_ hxHi hseed
  intro x hxseed hxbase ih
  have hxB : x < B.x₀.1 + B.width.1 := by omega
  have hxStep : x + 1 < n := by have hb := B.x_bound; omega
  have hyStep : B.y₀.1 - 1 + 1 < n := by
    have hb := B.y_bound
    omega
  have hxN : x < n := hxB.trans_le B.x_bound
  have hyN : B.y₀.1 - 1 < n := by omega
  let ix : Fin n := ⟨x, hxN⟩
  let iy : Fin n := ⟨B.y₀.1 - 1, hyN⟩
  have htop : A.openH ix ⟨iy.1 + 1, hyStep⟩ = true := by
    have hyEq : (⟨iy.1 + 1, hyStep⟩ : Fin n) = B.y₀ := by
      apply Fin.ext
      dsimp [iy]
      omega
    rw [hyEq]
    apply hfill.1 ix B.y₀ hxStep
    · unfold GridRectangle.Contains
      dsimp [ix]
      have hw := B.width_pos
      have hh := B.height_pos
      omega
    · unfold GridRectangle.Contains
      dsimp [ix]
      have hw := B.width_pos
      have hh := B.height_pos
      omega
  have ih' := (vOpenAt_iff A hxStep hyN).mp ih
  have hs := anchoredGrid_saturated A ix iy hxStep hyStep
  have hall := hs (Or.inr (Or.inl ⟨ih', htop⟩))
  exact (vOpenAt_iff A hxN hyN).mpr (by simpa [ix, iy] using hall.2.2.2)

private theorem south_open_everywhere
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed x : ℕ} (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hxLo : B.x₀.1 ≤ x) (hxHi : x < B.x₀.1 + B.width.1)
    (hsouth : 0 < B.y₀.1)
    (hseed : VOpenAt A seed (B.y₀.1 - 1)) :
    VOpenAt A x (B.y₀.1 - 1) := by
  by_cases h : seed ≤ x
  · exact south_open_propagates_right A B hfill hseedLo hseedHi h hxHi hsouth hseed
  · exact south_open_propagates_left A B hfill hseedLo hseedHi hxLo (by omega)
      hsouth hseed

theorem GridRectangle.extendSouth_filled
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A) (hsouth : 0 < B.y₀.1)
    {seed : ℕ} (hseedLo : B.x₀.1 ≤ seed)
    (hseedHi : seed < B.x₀.1 + B.width.1)
    (hseed : VOpenAt A seed (B.y₀.1 - 1)) :
    (B.extendSouth hsouth).Filled A := by
  constructor
  · intro i j hi hp hq
    by_cases hnew : j.1 < B.y₀.1
    · have hjEq : j.1 = B.y₀.1 - 1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendSouth] at hp
        omega
      have hx0 : B.x₀.1 ≤ i.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendSouth] at hp
        exact hp.1
      have hx1 : i.1 + 1 < B.x₀.1 + B.width.1 := by
        unfold GridRectangle.Contains at hq
        simp only [GridRectangle.extendSouth] at hq
        omega
      have hv := south_open_everywhere A B hfill hseedLo hseedHi hx0
        (by omega) hsouth hseed
      have hv' := (vOpenAt_iff (x := i.1) (y := j.1) A i.isLt j.isLt).mp
        (by simpa only [hjEq] using hv)
      have hs := anchoredGrid_saturated A i j hi (by omega)
      have htop : A.openH i ⟨j.1 + 1, by omega⟩ = true := by
        have hjTop : ⟨j.1 + 1, by omega⟩ = B.y₀ := by
          apply Fin.ext
          change j.1 + 1 = B.y₀.1
          omega
        rw [hjTop]
        apply hfill.1 i B.y₀ hi
        · unfold GridRectangle.Contains
          dsimp
          have hw := B.width_pos
          have hh := B.height_pos
          omega
        · unfold GridRectangle.Contains
          dsimp
          have hw := B.width_pos
          have hh := B.height_pos
          omega
      have hall := hs (Or.inr (Or.inr (Or.inl ⟨htop, hv'⟩)))
      exact hall.1
    · apply hfill.1 i j hi
      · exact B.contains_of_extendSouth_of_ge hsouth hp (Nat.le_of_not_gt hnew)
      · exact B.contains_of_extendSouth_of_ge hsouth hq (Nat.le_of_not_gt hnew)
  · intro i j hj hp hq
    by_cases hnew : j.1 < B.y₀.1
    · have hjEq : j.1 = B.y₀.1 - 1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendSouth] at hp
        omega
      have hx0 : B.x₀.1 ≤ i.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendSouth] at hp
        exact hp.1
      have hx1 : i.1 < B.x₀.1 + B.width.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendSouth] at hp
        exact hp.2.1
      have hv := south_open_everywhere A B hfill hseedLo hseedHi hx0 hx1
        hsouth hseed
      exact (vOpenAt_iff A i.isLt j.isLt).mp (by simpa [hjEq] using hv)
    · apply hfill.2 i j hj
      · exact B.contains_of_extendSouth_of_ge hsouth hp (Nat.le_of_not_gt hnew)
      · exact B.contains_of_extendSouth_of_ge hsouth hq (by
          exact (Nat.le_of_not_gt hnew).trans (Nat.le_succ j.1))

/-! Eastern extension. -/

def GridRectangle.extendEast {n : ℕ} (B : GridRectangle n)
    (h : B.x₀.1 + B.width.1 < n) : GridRectangle n where
  x₀ := B.x₀
  y₀ := B.y₀
  width := ⟨B.width.1 + 1, by omega⟩
  height := B.height
  width_pos := by change 0 < B.width.1 + 1; omega
  height_pos := B.height_pos
  x_bound := by change B.x₀.1 + (B.width.1 + 1) ≤ n; omega
  y_bound := B.y_bound

theorem GridRectangle.extendEast_area {n : ℕ} (B : GridRectangle n)
    (h : B.x₀.1 + B.width.1 < n) : B.area < (B.extendEast h).area := by
  simpa [GridRectangle.area, GridRectangle.extendEast, Nat.add_mul] using
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self B.width.1) B.height_pos

theorem GridRectangle.contains_extendEast {n : ℕ} (B : GridRectangle n)
    (h : B.x₀.1 + B.width.1 < n) {p : MacroCell n} (hp : B.Contains p) :
    (B.extendEast h).Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendEast]
  omega

theorem GridRectangle.contains_of_extendEast_of_lt {n : ℕ}
    (B : GridRectangle n) (h : B.x₀.1 + B.width.1 < n)
    {p : MacroCell n} (hp : (B.extendEast h).Contains p)
    (hx : p.1.1 < B.x₀.1 + B.width.1) : B.Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendEast] at hp
  exact ⟨hp.1, hx, hp.2.2.1, hp.2.2.2⟩

private theorem east_open_propagates_up
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : seed ≤ y) (hyHi : y < B.y₀.1 + B.height.1)
    (heast : B.x₀.1 + B.width.1 < n)
    (hseed : HOpenAt A (B.x₀.1 + B.width.1 - 1) seed) :
    HOpenAt A (B.x₀.1 + B.width.1 - 1) y := by
  induction y, hyLo using Nat.le_induction with
  | base => exact hseed
  | succ y hy ih =>
      have hyB : y < B.y₀.1 + B.height.1 := by omega
      have hyStep : y + 1 < n := by have hb := B.y_bound; omega
      have hxStep : B.x₀.1 + B.width.1 - 1 + 1 < n := by
        have hw := B.width_pos
        omega
      have hyN : y < n := hyB.trans_le B.y_bound
      have hxN : B.x₀.1 + B.width.1 - 1 < n := by
        have hw := B.width_pos
        have hb := B.x_bound
        omega
      let ix : Fin n := ⟨B.x₀.1 + B.width.1 - 1, hxN⟩
      let iy : Fin n := ⟨y, hyN⟩
      have hleft : A.openV ix iy = true := by
        apply hfill.2 ix iy hyStep
        · unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          have hw := B.width_pos
          omega
        · unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          have hw := B.width_pos
          omega
      have ih' := (hOpenAt_iff A hxN hyN).mp (ih hyB)
      have hs := anchoredGrid_saturated A ix iy hxStep hyStep
      have hall := hs (Or.inr (Or.inr (Or.inr ⟨hleft, ih'⟩)))
      exact (hOpenAt_iff A hxN hyStep).mpr (by simpa [ix, iy] using hall.2.2.1)

private theorem east_open_propagates_down
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : B.y₀.1 ≤ y) (hyHi : y ≤ seed)
    (heast : B.x₀.1 + B.width.1 < n)
    (hseed : HOpenAt A (B.x₀.1 + B.width.1 - 1) seed) :
    HOpenAt A (B.x₀.1 + B.width.1 - 1) y := by
  refine Nat.decreasingInduction' (n := seed) (m := y) ?_ hyHi hseed
  intro y hyseed hybase ih
  have hyB : y < B.y₀.1 + B.height.1 := by omega
  have hyStep : y + 1 < n := by have hb := B.y_bound; omega
  have hxStep : B.x₀.1 + B.width.1 - 1 + 1 < n := by
    have hw := B.width_pos
    omega
  have hyN : y < n := hyB.trans_le B.y_bound
  have hxN : B.x₀.1 + B.width.1 - 1 < n := by
    have hw := B.width_pos
    have hb := B.x_bound
    omega
  let ix : Fin n := ⟨B.x₀.1 + B.width.1 - 1, hxN⟩
  let iy : Fin n := ⟨y, hyN⟩
  have hleft : A.openV ix iy = true := by
    apply hfill.2 ix iy hyStep
    · unfold GridRectangle.Contains ix iy
      dsimp [ix, iy]
      have hw := B.width_pos
      omega
    · unfold GridRectangle.Contains ix iy
      dsimp [ix, iy]
      have hw := B.width_pos
      omega
  have ih' := (hOpenAt_iff A hxN hyStep).mp ih
  have hs := anchoredGrid_saturated A ix iy hxStep hyStep
  have hall := hs (Or.inr (Or.inr (Or.inl ⟨ih', hleft⟩)))
  exact (hOpenAt_iff A hxN hyN).mpr (by simpa [ix, iy] using hall.1)

private theorem east_open_everywhere
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : B.y₀.1 ≤ y) (hyHi : y < B.y₀.1 + B.height.1)
    (heast : B.x₀.1 + B.width.1 < n)
    (hseed : HOpenAt A (B.x₀.1 + B.width.1 - 1) seed) :
    HOpenAt A (B.x₀.1 + B.width.1 - 1) y := by
  by_cases h : seed ≤ y
  · exact east_open_propagates_up A B hfill hseedLo hseedHi h hyHi heast hseed
  · exact east_open_propagates_down A B hfill hseedLo hseedHi hyLo (by omega)
      heast hseed

theorem GridRectangle.extendEast_filled
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    (heast : B.x₀.1 + B.width.1 < n)
    {seed : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hseed : HOpenAt A (B.x₀.1 + B.width.1 - 1) seed) :
    (B.extendEast heast).Filled A := by
  constructor
  · intro i j hi hp hq
    by_cases hright : i.1 + 1 < B.x₀.1 + B.width.1
    · apply hfill.1 i j hi
      · exact B.contains_of_extendEast_of_lt heast hp
          ((Nat.lt_succ_self i.1).trans hright)
      · exact B.contains_of_extendEast_of_lt heast hq hright
    · have hiEq : i.1 = B.x₀.1 + B.width.1 - 1 := by
        unfold GridRectangle.Contains at hp hq
        simp only [GridRectangle.extendEast] at hp hq
        have hw := B.width_pos
        omega
      have hy0 : B.y₀.1 ≤ j.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendEast] at hp
        exact hp.2.2.1
      have hy1 : j.1 < B.y₀.1 + B.height.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendEast] at hp
        exact hp.2.2.2
      have hh := east_open_everywhere A B hfill hseedLo hseedHi hy0 hy1 heast hseed
      exact (hOpenAt_iff A i.isLt j.isLt).mp (by simpa [hiEq] using hh)
  · intro i j hj hp hq
    by_cases hiOld : i.1 < B.x₀.1 + B.width.1
    · apply hfill.2 i j hj
      · exact B.contains_of_extendEast_of_lt heast hp hiOld
      · exact B.contains_of_extendEast_of_lt heast hq hiOld
    · have hiEq : i.1 = B.x₀.1 + B.width.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendEast] at hp
        omega
      have hy0 : B.y₀.1 ≤ j.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendEast] at hp
        exact hp.2.2.1
      have hy1 : j.1 + 1 < B.y₀.1 + B.height.1 := by
        unfold GridRectangle.Contains at hq
        simp only [GridRectangle.extendEast] at hq
        omega
      have hh := east_open_everywhere A B hfill hseedLo hseedHi hy0
        (by omega) heast hseed
      have hh' := (hOpenAt_iff (x := B.x₀.1 + B.width.1 - 1)
        (y := j.1) A (by have hw := B.width_pos; have hb := B.x_bound; omega)
        j.isLt).mp hh
      let ix : Fin n := ⟨B.x₀.1 + B.width.1 - 1, by
        have hw := B.width_pos
        have hb := B.x_bound
        omega⟩
      have hleft : A.openV ix j = true := by
        apply hfill.2 ix j hj
        · unfold GridRectangle.Contains ix
          dsimp [ix]
          have hw := B.width_pos
          omega
        · unfold GridRectangle.Contains ix
          dsimp [ix]
          have hw := B.width_pos
          omega
      have hs := anchoredGrid_saturated A ix j (by
        dsimp [ix]
        have hw := B.width_pos
        omega) hj
      have hall := hs (Or.inr (Or.inr (Or.inr ⟨hleft, hh'⟩)))
      have hiFin : ⟨ix.1 + 1, by
          dsimp [ix]
          have hw := B.width_pos
          omega⟩ = i := by
        apply Fin.ext
        dsimp [ix]
        have hw := B.width_pos
        omega
      simpa only [hiFin] using hall.2.1

/-! Western extension. -/

def GridRectangle.extendWest {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.x₀.1) : GridRectangle n where
  x₀ := ⟨B.x₀.1 - 1, by omega⟩
  y₀ := B.y₀
  width := ⟨B.width.1 + 1, by have hb := B.x_bound; omega⟩
  height := B.height
  width_pos := by change 0 < B.width.1 + 1; omega
  height_pos := B.height_pos
  x_bound := by
    change B.x₀.1 - 1 + (B.width.1 + 1) ≤ n
    have hb := B.x_bound
    omega
  y_bound := B.y_bound

theorem GridRectangle.extendWest_area {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.x₀.1) : B.area < (B.extendWest h).area := by
  simpa [GridRectangle.area, GridRectangle.extendWest, Nat.add_mul] using
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self B.width.1) B.height_pos

theorem GridRectangle.contains_extendWest {n : ℕ} (B : GridRectangle n)
    (h : 0 < B.x₀.1) {p : MacroCell n} (hp : B.Contains p) :
    (B.extendWest h).Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendWest]
  have hb := B.x_bound
  omega

theorem GridRectangle.contains_of_extendWest_of_ge {n : ℕ}
    (B : GridRectangle n) (h : 0 < B.x₀.1) {p : MacroCell n}
    (hp : (B.extendWest h).Contains p) (hx : B.x₀.1 ≤ p.1.1) :
    B.Contains p := by
  unfold GridRectangle.Contains at hp ⊢
  simp only [GridRectangle.extendWest] at hp
  have hb := B.x_bound
  omega

private theorem west_open_propagates_up
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : seed ≤ y) (hyHi : y < B.y₀.1 + B.height.1)
    (hwest : 0 < B.x₀.1) (hseed : HOpenAt A (B.x₀.1 - 1) seed) :
    HOpenAt A (B.x₀.1 - 1) y := by
  induction y, hyLo using Nat.le_induction with
  | base => exact hseed
  | succ y hy ih =>
      have hyB : y < B.y₀.1 + B.height.1 := by omega
      have hyStep : y + 1 < n := by have hb := B.y_bound; omega
      have hxStep : B.x₀.1 - 1 + 1 < n := by have hb := B.x_bound; omega
      have hyN : y < n := hyB.trans_le B.y_bound
      have hxN : B.x₀.1 - 1 < n := by omega
      let ix : Fin n := ⟨B.x₀.1 - 1, hxN⟩
      let iy : Fin n := ⟨y, hyN⟩
      have hright : A.openV ⟨ix.1 + 1, hxStep⟩ iy = true := by
        have hxEq : (⟨ix.1 + 1, hxStep⟩ : Fin n) = B.x₀ := by
          apply Fin.ext
          dsimp [ix]
          omega
        rw [hxEq]
        apply hfill.2 B.x₀ iy hyStep
        · unfold GridRectangle.Contains
          dsimp [iy]
          have hw := B.width_pos
          omega
        · unfold GridRectangle.Contains
          dsimp [iy]
          have hw := B.width_pos
          omega
      have ih' := (hOpenAt_iff A hxN hyN).mp (ih hyB)
      have hs := anchoredGrid_saturated A ix iy hxStep hyStep
      have hall := hs (Or.inl ⟨ih', hright⟩)
      exact (hOpenAt_iff A hxN hyStep).mpr (by simpa [ix, iy] using hall.2.2.1)

private theorem west_open_propagates_down
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : B.y₀.1 ≤ y) (hyHi : y ≤ seed)
    (hwest : 0 < B.x₀.1) (hseed : HOpenAt A (B.x₀.1 - 1) seed) :
    HOpenAt A (B.x₀.1 - 1) y := by
  refine Nat.decreasingInduction' (n := seed) (m := y) ?_ hyHi hseed
  intro y hyseed hybase ih
  have hyB : y < B.y₀.1 + B.height.1 := by omega
  have hyStep : y + 1 < n := by have hb := B.y_bound; omega
  have hxStep : B.x₀.1 - 1 + 1 < n := by have hb := B.x_bound; omega
  have hyN : y < n := hyB.trans_le B.y_bound
  have hxN : B.x₀.1 - 1 < n := by omega
  let ix : Fin n := ⟨B.x₀.1 - 1, hxN⟩
  let iy : Fin n := ⟨y, hyN⟩
  have hright : A.openV ⟨ix.1 + 1, hxStep⟩ iy = true := by
    have hxEq : (⟨ix.1 + 1, hxStep⟩ : Fin n) = B.x₀ := by
      apply Fin.ext
      dsimp [ix]
      omega
    rw [hxEq]
    apply hfill.2 B.x₀ iy hyStep
    · unfold GridRectangle.Contains
      dsimp [iy]
      have hw := B.width_pos
      omega
    · unfold GridRectangle.Contains
      dsimp [iy]
      have hw := B.width_pos
      omega
  have ih' := (hOpenAt_iff A hxN hyStep).mp ih
  have hs := anchoredGrid_saturated A ix iy hxStep hyStep
  have hall := hs (Or.inr (Or.inl ⟨hright, ih'⟩))
  exact (hOpenAt_iff A hxN hyN).mpr (by simpa [ix, iy] using hall.1)

private theorem west_open_everywhere
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A)
    {seed y : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hyLo : B.y₀.1 ≤ y) (hyHi : y < B.y₀.1 + B.height.1)
    (hwest : 0 < B.x₀.1) (hseed : HOpenAt A (B.x₀.1 - 1) seed) :
    HOpenAt A (B.x₀.1 - 1) y := by
  by_cases h : seed ≤ y
  · exact west_open_propagates_up A B hfill hseedLo hseedHi h hyHi hwest hseed
  · exact west_open_propagates_down A B hfill hseedLo hseedHi hyLo (by omega)
      hwest hseed

theorem GridRectangle.extendWest_filled
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : GridRectangle n) (hfill : B.Filled A) (hwest : 0 < B.x₀.1)
    {seed : ℕ} (hseedLo : B.y₀.1 ≤ seed)
    (hseedHi : seed < B.y₀.1 + B.height.1)
    (hseed : HOpenAt A (B.x₀.1 - 1) seed) :
    (B.extendWest hwest).Filled A := by
  constructor
  · intro i j hi hp hq
    by_cases hnew : i.1 < B.x₀.1
    · have hiEq : i.1 = B.x₀.1 - 1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendWest] at hp
        omega
      have hy0 : B.y₀.1 ≤ j.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendWest] at hp
        exact hp.2.2.1
      have hy1 : j.1 < B.y₀.1 + B.height.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendWest] at hp
        exact hp.2.2.2
      have hh := west_open_everywhere A B hfill hseedLo hseedHi hy0 hy1 hwest hseed
      exact (hOpenAt_iff A i.isLt j.isLt).mp (by simpa [hiEq] using hh)
    · apply hfill.1 i j hi
      · exact B.contains_of_extendWest_of_ge hwest hp (Nat.le_of_not_gt hnew)
      · exact B.contains_of_extendWest_of_ge hwest hq (by
          exact (Nat.le_of_not_gt hnew).trans (Nat.le_succ i.1))
  · intro i j hj hp hq
    by_cases hnew : i.1 < B.x₀.1
    · have hiEq : i.1 = B.x₀.1 - 1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendWest] at hp
        omega
      have hy0 : B.y₀.1 ≤ j.1 := by
        unfold GridRectangle.Contains at hp
        simp only [GridRectangle.extendWest] at hp
        exact hp.2.2.1
      have hy1 : j.1 + 1 < B.y₀.1 + B.height.1 := by
        unfold GridRectangle.Contains at hq
        simp only [GridRectangle.extendWest] at hq
        omega
      have hh := west_open_everywhere A B hfill hseedLo hseedHi hy0
        (by omega) hwest hseed
      have hh' := (hOpenAt_iff (x := i.1) (y := j.1) A i.isLt j.isLt).mp
        (by simpa [hiEq] using hh)
      have hright : A.openV ⟨i.1 + 1, by omega⟩ j = true := by
        have hiRight : (⟨i.1 + 1, by omega⟩ : Fin n) = B.x₀ := by
          apply Fin.ext
          change i.1 + 1 = B.x₀.1
          omega
        rw [hiRight]
        apply hfill.2 B.x₀ j hj
        · unfold GridRectangle.Contains
          dsimp
          have hw := B.width_pos
          omega
        · unfold GridRectangle.Contains
          dsimp
          have hw := B.width_pos
          omega
      have hs := anchoredGrid_saturated A i j (by omega) hj
      have hall := hs (Or.inl ⟨hh', hright⟩)
      exact hall.2.2.2
    · apply hfill.2 i j hj
      · exact B.contains_of_extendWest_of_ge hwest hp (Nat.le_of_not_gt hnew)
      · exact B.contains_of_extendWest_of_ge hwest hq (Nat.le_of_not_gt hnew)

/-! Maximal filled rectangles have no open edge leaving any side. -/

theorem maximalFilledRectangle_no_north
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n)
    (hnorth : (maximalFilledRectangle A p).y₀.1 +
      (maximalFilledRectangle A p).height.1 < n)
    {seed : ℕ}
    (hlo : (maximalFilledRectangle A p).x₀.1 ≤ seed)
    (hhi : seed < (maximalFilledRectangle A p).x₀.1 +
      (maximalFilledRectangle A p).width.1) :
    ¬ VOpenAt A seed ((maximalFilledRectangle A p).y₀.1 +
      (maximalFilledRectangle A p).height.1 - 1) := by
  intro hopen
  let B := maximalFilledRectangle A p
  have hcontains : (B.extendNorth (by simpa [B] using hnorth)).Contains p :=
    B.contains_extendNorth _ (by simpa [B] using maximalFilledRectangle_contains A p)
  have hfilled : (B.extendNorth (by simpa [B] using hnorth)).Filled A :=
    B.extendNorth_filled A (by simpa [B] using maximalFilledRectangle_filled A p)
      (by simpa [B] using hnorth) (by simpa [B] using hlo)
      (by simpa [B] using hhi) (by simpa [B] using hopen)
  have hmax := maximalFilledRectangle_maximal A p
    (B.extendNorth (by simpa [B] using hnorth)) hcontains hfilled
  exact (not_lt_of_ge (by simpa [B] using hmax)) (B.extendNorth_area _)

theorem maximalFilledRectangle_no_south
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n)
    (hsouth : 0 < (maximalFilledRectangle A p).y₀.1)
    {seed : ℕ}
    (hlo : (maximalFilledRectangle A p).x₀.1 ≤ seed)
    (hhi : seed < (maximalFilledRectangle A p).x₀.1 +
      (maximalFilledRectangle A p).width.1) :
    ¬ VOpenAt A seed ((maximalFilledRectangle A p).y₀.1 - 1) := by
  intro hopen
  let B := maximalFilledRectangle A p
  have hcontains : (B.extendSouth (by simpa [B] using hsouth)).Contains p :=
    B.contains_extendSouth _ (by simpa [B] using maximalFilledRectangle_contains A p)
  have hfilled : (B.extendSouth (by simpa [B] using hsouth)).Filled A :=
    B.extendSouth_filled A (by simpa [B] using maximalFilledRectangle_filled A p)
      (by simpa [B] using hsouth) (by simpa [B] using hlo)
      (by simpa [B] using hhi) (by simpa [B] using hopen)
  have hmax := maximalFilledRectangle_maximal A p
    (B.extendSouth (by simpa [B] using hsouth)) hcontains hfilled
  exact (not_lt_of_ge (by simpa [B] using hmax)) (B.extendSouth_area _)

theorem maximalFilledRectangle_no_east
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n)
    (heast : (maximalFilledRectangle A p).x₀.1 +
      (maximalFilledRectangle A p).width.1 < n)
    {seed : ℕ}
    (hlo : (maximalFilledRectangle A p).y₀.1 ≤ seed)
    (hhi : seed < (maximalFilledRectangle A p).y₀.1 +
      (maximalFilledRectangle A p).height.1) :
    ¬ HOpenAt A ((maximalFilledRectangle A p).x₀.1 +
      (maximalFilledRectangle A p).width.1 - 1) seed := by
  intro hopen
  let B := maximalFilledRectangle A p
  have hcontains : (B.extendEast (by simpa [B] using heast)).Contains p :=
    B.contains_extendEast _ (by simpa [B] using maximalFilledRectangle_contains A p)
  have hfilled : (B.extendEast (by simpa [B] using heast)).Filled A :=
    B.extendEast_filled A (by simpa [B] using maximalFilledRectangle_filled A p)
      (by simpa [B] using heast) (by simpa [B] using hlo)
      (by simpa [B] using hhi) (by simpa [B] using hopen)
  have hmax := maximalFilledRectangle_maximal A p
    (B.extendEast (by simpa [B] using heast)) hcontains hfilled
  exact (not_lt_of_ge (by simpa [B] using hmax)) (B.extendEast_area _)

theorem maximalFilledRectangle_no_west
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n)
    (hwest : 0 < (maximalFilledRectangle A p).x₀.1)
    {seed : ℕ}
    (hlo : (maximalFilledRectangle A p).y₀.1 ≤ seed)
    (hhi : seed < (maximalFilledRectangle A p).y₀.1 +
      (maximalFilledRectangle A p).height.1) :
    ¬ HOpenAt A ((maximalFilledRectangle A p).x₀.1 - 1) seed := by
  intro hopen
  let B := maximalFilledRectangle A p
  have hcontains : (B.extendWest (by simpa [B] using hwest)).Contains p :=
    B.contains_extendWest _ (by simpa [B] using maximalFilledRectangle_contains A p)
  have hfilled : (B.extendWest (by simpa [B] using hwest)).Filled A :=
    B.extendWest_filled A (by simpa [B] using maximalFilledRectangle_filled A p)
      (by simpa [B] using hwest) (by simpa [B] using hlo)
      (by simpa [B] using hhi) (by simpa [B] using hopen)
  have hmax := maximalFilledRectangle_maximal A p
    (B.extendWest (by simpa [B] using hwest)) hcontains hfilled
  exact (not_lt_of_ge (by simpa [B] using hmax)) (B.extendWest_area _)

/-- Any filled rectangle meeting the maximal rectangle at `q` is contained
in it.  This is the component-rectangle theorem in the exact form needed to
build a literal partition. -/
theorem filledRectangle_subset_maximal
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p q : MacroCell n)
    (hqB : (maximalFilledRectangle A p).Contains q)
    (C : GridRectangle n) (hqC : C.Contains q) (hC : C.Filled A) :
    ∀ r : MacroCell n, C.Contains r → (maximalFilledRectangle A p).Contains r := by
  let B := maximalFilledRectangle A p
  change B.Contains q at hqB
  have hqBx0 : B.x₀.1 ≤ q.1.1 := hqB.1
  have hqBx1 : q.1.1 < B.x₀.1 + B.width.1 := hqB.2.1
  have hqBy0 : B.y₀.1 ≤ q.2.1 := hqB.2.2.1
  have hqBy1 : q.2.1 < B.y₀.1 + B.height.1 := hqB.2.2.2
  have hqCx0 : C.x₀.1 ≤ q.1.1 := hqC.1
  have hqCx1 : q.1.1 < C.x₀.1 + C.width.1 := hqC.2.1
  have hqCy0 : C.y₀.1 ≤ q.2.1 := hqC.2.2.1
  have hqCy1 : q.2.1 < C.y₀.1 + C.height.1 := hqC.2.2.2
  have hleft : B.x₀.1 ≤ C.x₀.1 := by
    by_contra h
    have hwest : 0 < B.x₀.1 := by omega
    have hi : B.x₀.1 - 1 + 1 < n := by omega
    let ix : Fin n := ⟨B.x₀.1 - 1, by omega⟩
    have hp0 : C.Contains (ix, q.2) := by
      unfold GridRectangle.Contains
      dsimp [ix]
      omega
    have hp1 : C.Contains (⟨ix.1 + 1, hi⟩, q.2) := by
      unfold GridRectangle.Contains
      dsimp [ix]
      omega
    have hopen : HOpenAt A (B.x₀.1 - 1) q.2.1 :=
      (hOpenAt_iff A ix.isLt q.2.isLt).mpr (hC.1 ix q.2 hi hp0 hp1)
    exact maximalFilledRectangle_no_west A p hwest hqBy0 hqBy1 hopen
  have hright : C.x₀.1 + C.width.1 ≤ B.x₀.1 + B.width.1 := by
    by_contra h
    have heast : B.x₀.1 + B.width.1 < n := by
      have hb := C.x_bound
      omega
    have hw := B.width_pos
    let ix : Fin n := ⟨B.x₀.1 + B.width.1 - 1, by omega⟩
    have hi : ix.1 + 1 < n := by dsimp [ix]; omega
    have hp0 : C.Contains (ix, q.2) := by
      unfold GridRectangle.Contains
      dsimp [ix]
      omega
    have hp1 : C.Contains (⟨ix.1 + 1, hi⟩, q.2) := by
      unfold GridRectangle.Contains
      dsimp [ix]
      omega
    have hopen : HOpenAt A (B.x₀.1 + B.width.1 - 1) q.2.1 :=
      (hOpenAt_iff A ix.isLt q.2.isLt).mpr (hC.1 ix q.2 hi hp0 hp1)
    exact maximalFilledRectangle_no_east A p heast hqBy0 hqBy1 hopen
  have hbottom : B.y₀.1 ≤ C.y₀.1 := by
    by_contra h
    have hsouth : 0 < B.y₀.1 := by omega
    have hj : B.y₀.1 - 1 + 1 < n := by omega
    let jy : Fin n := ⟨B.y₀.1 - 1, by omega⟩
    have hp0 : C.Contains (q.1, jy) := by
      unfold GridRectangle.Contains
      dsimp [jy]
      omega
    have hp1 : C.Contains (q.1, ⟨jy.1 + 1, hj⟩) := by
      unfold GridRectangle.Contains
      dsimp [jy]
      omega
    have hopen : VOpenAt A q.1.1 (B.y₀.1 - 1) :=
      (vOpenAt_iff A q.1.isLt jy.isLt).mpr (hC.2 q.1 jy hj hp0 hp1)
    exact maximalFilledRectangle_no_south A p hsouth hqBx0 hqBx1 hopen
  have htop : C.y₀.1 + C.height.1 ≤ B.y₀.1 + B.height.1 := by
    by_contra h
    have hnorth : B.y₀.1 + B.height.1 < n := by
      have hb := C.y_bound
      omega
    have hh := B.height_pos
    let jy : Fin n := ⟨B.y₀.1 + B.height.1 - 1, by omega⟩
    have hj : jy.1 + 1 < n := by dsimp [jy]; omega
    have hp0 : C.Contains (q.1, jy) := by
      unfold GridRectangle.Contains
      dsimp [jy]
      omega
    have hp1 : C.Contains (q.1, ⟨jy.1 + 1, hj⟩) := by
      unfold GridRectangle.Contains
      dsimp [jy]
      omega
    have hopen : VOpenAt A q.1.1 (B.y₀.1 + B.height.1 - 1) :=
      (vOpenAt_iff A q.1.isLt jy.isLt).mpr (hC.2 q.1 jy hj hp0 hp1)
    exact maximalFilledRectangle_no_north A p hnorth hqBx0 hqBx1 hopen
  intro r hr
  unfold GridRectangle.Contains at hqB hqC hr ⊢
  dsimp [B] at hleft hright hbottom htop ⊢
  omega

def GridRectangle.lowerLeft {n : ℕ} (B : GridRectangle n) : MacroCell n :=
  (B.x₀, B.y₀)

def GridRectangle.upperRight {n : ℕ} (B : GridRectangle n) : MacroCell n :=
  (⟨B.x₀.1 + B.width.1 - 1, by
      have hw := B.width_pos
      have hb := B.x_bound
      omega⟩,
   ⟨B.y₀.1 + B.height.1 - 1, by
      have hh := B.height_pos
      have hb := B.y_bound
      omega⟩)

@[simp] theorem GridRectangle.contains_lowerLeft {n : ℕ} (B : GridRectangle n) :
    B.Contains B.lowerLeft := by
  unfold GridRectangle.Contains GridRectangle.lowerLeft
  dsimp
  have hw := B.width_pos
  have hh := B.height_pos
  omega

@[simp] theorem GridRectangle.contains_upperRight {n : ℕ} (B : GridRectangle n) :
    B.Contains B.upperRight := by
  unfold GridRectangle.Contains GridRectangle.upperRight
  dsimp
  have hw := B.width_pos
  have hh := B.height_pos
  omega

theorem gridRectangle_eq_of_mutual_contains {n : ℕ} (B C : GridRectangle n)
    (hBC : ∀ p : MacroCell n, B.Contains p → C.Contains p)
    (hCB : ∀ p : MacroCell n, C.Contains p → B.Contains p) : B = C := by
  have hBll := hBC B.lowerLeft B.contains_lowerLeft
  have hCll := hCB C.lowerLeft C.contains_lowerLeft
  have hBur := hBC B.upperRight B.contains_upperRight
  have hCur := hCB C.upperRight C.contains_upperRight
  apply GridRectangle.ext
  · apply Fin.ext
    unfold GridRectangle.Contains GridRectangle.lowerLeft at hBll hCll
    dsimp at hBll hCll
    omega
  · apply Fin.ext
    unfold GridRectangle.Contains GridRectangle.lowerLeft at hBll hCll
    dsimp at hBll hCll
    omega
  · apply Fin.ext
    unfold GridRectangle.Contains GridRectangle.upperRight at hBur hCur
    unfold GridRectangle.Contains GridRectangle.lowerLeft at hBll hCll
    dsimp at hBur hCur hBll hCll
    have hBw := B.width_pos
    have hCw := C.width_pos
    omega
  · apply Fin.ext
    unfold GridRectangle.Contains GridRectangle.upperRight at hBur hCur
    unfold GridRectangle.Contains GridRectangle.lowerLeft at hBll hCll
    dsimp at hBur hCur hBll hCll
    have hBh := B.height_pos
    have hCh := C.height_pos
    omega

theorem maximalFilledRectangle_eq_of_contains
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p q : MacroCell n)
    (hq : (maximalFilledRectangle A p).Contains q) :
    maximalFilledRectangle A q = maximalFilledRectangle A p := by
  apply gridRectangle_eq_of_mutual_contains
  · exact filledRectangle_subset_maximal A p q hq (maximalFilledRectangle A q)
      (maximalFilledRectangle_contains A q) (maximalFilledRectangle_filled A q)
  · exact filledRectangle_subset_maximal A q q
      (maximalFilledRectangle_contains A q) (maximalFilledRectangle A p) hq
      (maximalFilledRectangle_filled A p)

/-- The literal rectangular partition decoded from the saturated openings. -/
def anchoredRectangularPartition {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) : RectangularPartition n where
  blocks := Finset.univ.image (maximalFilledRectangle A)
  unique_block p := by
    refine ⟨maximalFilledRectangle A p, ⟨Finset.mem_image.mpr
      ⟨p, Finset.mem_univ p, rfl⟩, maximalFilledRectangle_contains A p⟩, ?_⟩
    intro B hB
    rcases Finset.mem_image.mp hB.1 with ⟨q, -, rfl⟩
    exact (maximalFilledRectangle_eq_of_contains A q p hB.2).symm

theorem anchoredRectangularPartition_mem_filled
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    {B : GridRectangle n} (hB : B ∈ (anchoredRectangularPartition A).blocks) :
    B.Filled A := by
  rcases Finset.mem_image.mp hB with ⟨p, -, rfl⟩
  exact maximalFilledRectangle_filled A p

theorem anchoredRectangularPartition_sameBlock_iff
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p q : MacroCell n) :
    (anchoredRectangularPartition A).SameBlock p q ↔
      (maximalFilledRectangle A p).Contains q := by
  constructor
  · rintro ⟨B, hB, hp, hq⟩
    rcases Finset.mem_image.mp hB with ⟨r, -, rfl⟩
    have heq := maximalFilledRectangle_eq_of_contains A r p hp
    rw [heq]
    exact hq
  · intro hq
    exact ⟨maximalFilledRectangle A p,
      Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩,
      maximalFilledRectangle_contains A p, hq⟩

theorem anchoredPartition_horizontal_open_iff
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) (hi : i.1 + 1 < n) :
    (anchoredRectangularPartition A).SameBlock (i, j) (⟨i.1 + 1, hi⟩, j) ↔
      A.openH i j = true := by
  constructor
  · rintro ⟨B, hB, hp, hq⟩
    exact (anchoredRectangularPartition_mem_filled A hB).1 i j hi hp hq
  · intro hopen
    rw [anchoredRectangularPartition_sameBlock_iff]
    let B := maximalFilledRectangle A (i, j)
    change B.Contains (⟨i.1 + 1, hi⟩, j)
    have hp : B.Contains (i, j) := by
      simpa [B] using maximalFilledRectangle_contains A (i, j)
    by_contra hq
    have hqUpper : ¬ (i.1 + 1 < B.x₀.1 + B.width.1) := by
      intro hupper
      apply hq
      unfold GridRectangle.Contains at hp ⊢
      dsimp at hp ⊢
      exact ⟨by omega, hupper, hp.2.2.1, hp.2.2.2⟩
    have hright : B.x₀.1 + B.width.1 = i.1 + 1 := by
      unfold GridRectangle.Contains at hp
      dsimp at hp
      have hw := B.width_pos
      omega
    have heast : B.x₀.1 + B.width.1 < n := by omega
    have hy0 : B.y₀.1 ≤ j.1 := hp.2.2.1
    have hy1 : j.1 < B.y₀.1 + B.height.1 := hp.2.2.2
    have hraw : HOpenAt A (B.x₀.1 + B.width.1 - 1) j.1 := by
      rw [hright]
      have heq : i.1 + 1 - 1 = i.1 := by omega
      rw [heq]
      exact (hOpenAt_iff A i.isLt j.isLt).mpr hopen
    exact maximalFilledRectangle_no_east A (i, j) heast hy0 hy1 hraw

theorem anchoredPartition_vertical_open_iff
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) (hj : j.1 + 1 < n) :
    (anchoredRectangularPartition A).SameBlock (i, j) (i, ⟨j.1 + 1, hj⟩) ↔
      A.openV i j = true := by
  constructor
  · rintro ⟨B, hB, hp, hq⟩
    exact (anchoredRectangularPartition_mem_filled A hB).2 i j hj hp hq
  · intro hopen
    rw [anchoredRectangularPartition_sameBlock_iff]
    let B := maximalFilledRectangle A (i, j)
    change B.Contains (i, ⟨j.1 + 1, hj⟩)
    have hp : B.Contains (i, j) := by
      simpa [B] using maximalFilledRectangle_contains A (i, j)
    by_contra hq
    have hqUpper : ¬ (j.1 + 1 < B.y₀.1 + B.height.1) := by
      intro hupper
      apply hq
      unfold GridRectangle.Contains at hp ⊢
      dsimp at hp ⊢
      exact ⟨hp.1, hp.2.1, by omega, hupper⟩
    have htop : B.y₀.1 + B.height.1 = j.1 + 1 := by
      unfold GridRectangle.Contains at hp
      dsimp at hp
      have hh := B.height_pos
      omega
    have hnorth : B.y₀.1 + B.height.1 < n := by omega
    have hx0 : B.x₀.1 ≤ i.1 := hp.1
    have hx1 : i.1 < B.x₀.1 + B.width.1 := hp.2.1
    have hraw : VOpenAt A i.1 (B.y₀.1 + B.height.1 - 1) := by
      rw [htop]
      have heq : j.1 + 1 - 1 = j.1 := by omega
      rw [heq]
      exact (vOpenAt_iff A i.isLt j.isLt).mpr hopen
    exact maximalFilledRectangle_no_north A (i, j) hnorth hx0 hx1 hraw

/-! Decoding tile indices and amplifier labels on each rectangular block. -/

def GridRectangle.localCell {n : ℕ} (B : GridRectangle n)
    (i : Fin B.width.1) (j : Fin B.height.1) : MacroCell n :=
  (⟨B.x₀.1 + i.1, by
      have hb := B.x_bound
      omega⟩,
   ⟨B.y₀.1 + j.1, by
      have hb := B.y_bound
      omega⟩)

@[simp] theorem GridRectangle.localCell_contains {n : ℕ} (B : GridRectangle n)
    (i : Fin B.width.1) (j : Fin B.height.1) : B.Contains (B.localCell i j) := by
  unfold GridRectangle.Contains GridRectangle.localCell
  dsimp
  omega

def anchoredBlockWang
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (B : ↑(anchoredRectangularPartition A).blocks) :
    OpenWangTiling (registerWangTile P) B.1.width.1 B.1.height.1 := by
  let f : Fin B.1.width.1 → Fin B.1.height.1 → Fin P.tileCount :=
    fun i j => (A.cell (B.1.localCell i j).1 (B.1.localCell i j).2).tile
  refine ⟨f, ?_, ?_⟩
  · intro i j hi
    let q := B.1.localCell i j
    let ir : Fin B.1.width.1 := ⟨i.1 + 1, hi⟩
    let qr := B.1.localCell ir j
    have hqx : q.1.1 + 1 < n := by
      dsimp [q, GridRectangle.localCell]
      have hb := B.1.x_bound
      omega
    have hqr : qr = (⟨q.1.1 + 1, hqx⟩, q.2) := by
      apply Prod.ext
      · apply Fin.ext
        dsimp [q, qr, ir, GridRectangle.localCell]
        omega
      · apply Fin.ext
        rfl
    have hopen : A.openH q.1 q.2 = true := by
      apply (anchoredRectangularPartition_mem_filled A B.2).1 q.1 q.2 hqx
      · exact B.1.localCell_contains i j
      · rw [← hqr]
        exact B.1.localCell_contains ir j
    have hc := A.horizontal q.1 q.2 hqx
    have hcol := (hc.2 hopen).2.2.1
    change P.east (A.cell q.1 q.2).tile = P.west (A.cell qr.1 qr.2).tile
    rw [hqr]
    exact hcol
  · intro i j hj
    let q := B.1.localCell i j
    let jt : Fin B.1.height.1 := ⟨j.1 + 1, hj⟩
    let qt := B.1.localCell i jt
    have hqy : q.2.1 + 1 < n := by
      dsimp [q, GridRectangle.localCell]
      have hb := B.1.y_bound
      omega
    have hqt : qt = (q.1, ⟨q.2.1 + 1, hqy⟩) := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp [q, qt, jt, GridRectangle.localCell]
        omega
    have hopen : A.openV q.1 q.2 = true := by
      apply (anchoredRectangularPartition_mem_filled A B.2).2 q.1 q.2 hqy
      · exact B.1.localCell_contains i j
      · rw [← hqt]
        exact B.1.localCell_contains i jt
    have hc := A.vertical q.1 q.2 hqy
    have hcol := (hc.2 hopen).2.2.1
    change P.north (A.cell q.1 q.2).tile = P.south (A.cell qt.1 qt.2).tile
    rw [hqt]
    exact hcol

def anchoredOpenEdgeLabel
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (e : OpenMacroEdge (anchoredRectangularPartition A)) : Fin P.amp :=
  match e.1 with
  | .inl h => (A.cell
      ⟨h.1.1, lt_of_lt_of_le h.1.2 (Nat.sub_le n 1)⟩ h.2).labels.east
  | .inr v => (A.cell v.1
      ⟨v.2.1, lt_of_lt_of_le v.2.2 (Nat.sub_le n 1)⟩).labels.north

/-- Completely explicit forward decoder. -/
def anchoredGridToMacroData (P : RegisterParams) (n : ℕ) :
    AnchoredGrid P n → MacroData n (registerWangTile P) P.amp :=
  fun A => ⟨anchoredRectangularPartition A,
    (anchoredOpenEdgeLabel A, anchoredBlockWang A)⟩

/-! Reconstruction from rectangular macro data. -/

def RectangularPartition.blockAt {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) : ↑D.blocks :=
  ⟨Classical.choose (D.unique_block p),
    (Classical.choose_spec (D.unique_block p)).1.1⟩

theorem RectangularPartition.blockAt_contains {n : ℕ}
    (D : RectangularPartition n) (p : MacroCell n) :
    (D.blockAt p).1.Contains p :=
  (Classical.choose_spec (D.unique_block p)).1.2

theorem RectangularPartition.blockAt_eq_of_contains {n : ℕ}
    (D : RectangularPartition n) (p : MacroCell n) (B : ↑D.blocks)
    (hp : B.1.Contains p) : D.blockAt p = B := by
  apply Subtype.ext
  exact (D.unique_block p).unique
    ⟨(D.blockAt p).2, D.blockAt_contains p⟩ ⟨B.2, hp⟩

theorem RectangularPartition.blockAt_eq_of_sameBlock {n : ℕ}
    (D : RectangularPartition n) {p q : MacroCell n} (h : D.SameBlock p q) :
    D.blockAt p = D.blockAt q := by
  rcases h with ⟨B, hB, hp, hq⟩
  exact (D.blockAt_eq_of_contains p ⟨B, hB⟩ hp).trans
    (D.blockAt_eq_of_contains q ⟨B, hB⟩ hq).symm

def RectangularPartition.localX {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) : Fin (D.blockAt p).1.width.1 :=
  ⟨p.1.1 - (D.blockAt p).1.x₀.1, by
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega⟩

def RectangularPartition.localY {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) : Fin (D.blockAt p).1.height.1 :=
  ⟨p.2.1 - (D.blockAt p).1.y₀.1, by
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega⟩

theorem RectangularPartition.localCell_blockAt {n : ℕ}
    (D : RectangularPartition n) (p : MacroCell n) :
    (D.blockAt p).1.localCell (D.localX p) (D.localY p) = p := by
  apply Prod.ext <;> apply Fin.ext
  · dsimp [GridRectangle.localCell, RectangularPartition.localX]
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega
  · dsimp [GridRectangle.localCell, RectangularPartition.localY]
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega

def RectangularPartition.stateAt {n : ℕ} (D : RectangularPartition n)
    (p : MacroCell n) : MacroState :=
  { west := decide ((D.blockAt p).1.x₀.1 < p.1.1)
    east := decide (p.1.1 + 1 < (D.blockAt p).1.x₀.1 + (D.blockAt p).1.width.1)
    south := decide ((D.blockAt p).1.y₀.1 < p.2.1)
    north := decide (p.2.1 + 1 < (D.blockAt p).1.y₀.1 + (D.blockAt p).1.height.1) }

theorem RectangularPartition.east_open_iff {n : ℕ}
    (D : RectangularPartition n) (i j : Fin n) (hi : i.1 + 1 < n) :
    (D.stateAt (i, j)).east = true ↔
      D.SameBlock (i, j) (⟨i.1 + 1, hi⟩, j) := by
  let p : MacroCell n := (i, j)
  let q : MacroCell n := (⟨i.1 + 1, hi⟩, j)
  let B := D.blockAt p
  constructor
  · intro h
    have hin : i.1 + 1 < B.1.x₀.1 + B.1.width.1 := by
      simpa [RectangularPartition.stateAt, p, B] using h
    refine ⟨B.1, B.2, D.blockAt_contains p, ?_⟩
    unfold GridRectangle.Contains at ⊢
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    dsimp [p, q, B] at hp ⊢
    exact ⟨by omega, hin, hp.2.2.1, hp.2.2.2⟩
  · rintro ⟨C, hC, hp, hq⟩
    have hBC : B = ⟨C, hC⟩ := D.blockAt_eq_of_contains p ⟨C, hC⟩ hp
    have hin : i.1 + 1 < C.x₀.1 + C.width.1 := by
      unfold GridRectangle.Contains at hq
      exact hq.2.1
    simpa [RectangularPartition.stateAt, p, B, hBC] using hin

theorem RectangularPartition.west_open_iff {n : ℕ}
    (D : RectangularPartition n) (i j : Fin n) (hi : 0 < i.1) :
    (D.stateAt (i, j)).west = true ↔
      D.SameBlock (⟨i.1 - 1, by omega⟩, j) (i, j) := by
  let p : MacroCell n := (i, j)
  let q : MacroCell n := (⟨i.1 - 1, by omega⟩, j)
  let B := D.blockAt p
  constructor
  · intro h
    have hin : B.1.x₀.1 < i.1 := by
      simpa [RectangularPartition.stateAt, p, B] using h
    refine ⟨B.1, B.2, ?_, D.blockAt_contains p⟩
    have hp : B.1.Contains p := by simpa [B] using D.blockAt_contains p
    have hpx0 : B.1.x₀.1 ≤ i.1 := by simpa [p] using hp.1
    have hpx1 : i.1 < B.1.x₀.1 + B.1.width.1 := by simpa [p] using hp.2.1
    have hpy0 : B.1.y₀.1 ≤ j.1 := by simpa [p] using hp.2.2.1
    have hpy1 : j.1 < B.1.y₀.1 + B.1.height.1 := by simpa [p] using hp.2.2.2
    unfold GridRectangle.Contains
    dsimp [q]
    exact ⟨by omega, by omega, hpy0, hpy1⟩
  · rintro ⟨C, hC, hq, hp⟩
    have hBC : B = ⟨C, hC⟩ := D.blockAt_eq_of_contains p ⟨C, hC⟩ hp
    have hin : C.x₀.1 < i.1 := by
      unfold GridRectangle.Contains at hq
      dsimp [q] at hq
      omega
    simpa [RectangularPartition.stateAt, p, B, hBC] using hin

theorem RectangularPartition.north_open_iff {n : ℕ}
    (D : RectangularPartition n) (i j : Fin n) (hj : j.1 + 1 < n) :
    (D.stateAt (i, j)).north = true ↔
      D.SameBlock (i, j) (i, ⟨j.1 + 1, hj⟩) := by
  let p : MacroCell n := (i, j)
  let q : MacroCell n := (i, ⟨j.1 + 1, hj⟩)
  let B := D.blockAt p
  constructor
  · intro h
    have hin : j.1 + 1 < B.1.y₀.1 + B.1.height.1 := by
      simpa [RectangularPartition.stateAt, p, B] using h
    refine ⟨B.1, B.2, D.blockAt_contains p, ?_⟩
    unfold GridRectangle.Contains at ⊢
    have hp := D.blockAt_contains p
    unfold GridRectangle.Contains at hp
    dsimp [p, q, B] at hp ⊢
    exact ⟨hp.1, hp.2.1, by omega, hin⟩
  · rintro ⟨C, hC, hp, hq⟩
    have hBC : B = ⟨C, hC⟩ := D.blockAt_eq_of_contains p ⟨C, hC⟩ hp
    have hin : j.1 + 1 < C.y₀.1 + C.height.1 := by
      unfold GridRectangle.Contains at hq
      exact hq.2.2.2
    simpa [RectangularPartition.stateAt, p, B, hBC] using hin

theorem RectangularPartition.south_open_iff {n : ℕ}
    (D : RectangularPartition n) (i j : Fin n) (hj : 0 < j.1) :
    (D.stateAt (i, j)).south = true ↔
      D.SameBlock (i, ⟨j.1 - 1, by omega⟩) (i, j) := by
  let p : MacroCell n := (i, j)
  let q : MacroCell n := (i, ⟨j.1 - 1, by omega⟩)
  let B := D.blockAt p
  constructor
  · intro h
    have hin : B.1.y₀.1 < j.1 := by
      simpa [RectangularPartition.stateAt, p, B] using h
    refine ⟨B.1, B.2, ?_, D.blockAt_contains p⟩
    have hp : B.1.Contains p := by simpa [B] using D.blockAt_contains p
    have hpx0 : B.1.x₀.1 ≤ i.1 := by simpa [p] using hp.1
    have hpx1 : i.1 < B.1.x₀.1 + B.1.width.1 := by simpa [p] using hp.2.1
    have hpy0 : B.1.y₀.1 ≤ j.1 := by simpa [p] using hp.2.2.1
    have hpy1 : j.1 < B.1.y₀.1 + B.1.height.1 := by simpa [p] using hp.2.2.2
    unfold GridRectangle.Contains
    dsimp [q]
    exact ⟨hpx0, hpx1, by omega, by omega⟩
  · rintro ⟨C, hC, hq, hp⟩
    have hBC : B = ⟨C, hC⟩ := D.blockAt_eq_of_contains p ⟨C, hC⟩ hp
    have hin : C.y₀.1 < j.1 := by
      unfold GridRectangle.Contains at hq
      dsimp [q] at hq
      omega
    simpa [RectangularPartition.stateAt, p, B, hBC] using hin

def horizontalMacroEdge {n : ℕ} (i j : Fin n) (hi : i.1 + 1 < n) :
    MacroEdge n := .inl (⟨i.1, by omega⟩, j)

def verticalMacroEdge {n : ℕ} (i j : Fin n) (hj : j.1 + 1 < n) :
    MacroEdge n := .inr (i, ⟨j.1, by omega⟩)

@[simp] theorem horizontalMacroEdge_lo {n : ℕ} (i j : Fin n)
    (hi : i.1 + 1 < n) : (horizontalMacroEdge i j hi).lo = (i, j) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem horizontalMacroEdge_hi {n : ℕ} (i j : Fin n)
    (hi : i.1 + 1 < n) :
    (horizontalMacroEdge i j hi).hi = (⟨i.1 + 1, hi⟩, j) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem verticalMacroEdge_lo {n : ℕ} (i j : Fin n)
    (hj : j.1 + 1 < n) : (verticalMacroEdge i j hj).lo = (i, j) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem verticalMacroEdge_hi {n : ℕ} (i j : Fin n)
    (hj : j.1 + 1 < n) :
    (verticalMacroEdge i j hj).hi = (i, ⟨j.1 + 1, hj⟩) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

def macroEastLabel {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) : Fin P.amp :=
  if h : (M.1.stateAt p).east = true then
    have hi : p.1.1 + 1 < n := by
      have hp := M.1.blockAt_contains p
      have hopen : p.1.1 + 1 < (M.1.blockAt p).1.x₀.1 +
          (M.1.blockAt p).1.width.1 := by
        simpa [RectangularPartition.stateAt] using h
      have hb := (M.1.blockAt p).1.x_bound
      omega
    M.2.1 ⟨horizontalMacroEdge p.1 p.2 hi,
      by
        change M.1.SameBlock p (⟨p.1.1 + 1, hi⟩, p.2)
        simpa using (M.1.east_open_iff p.1 p.2 hi).mp h⟩
  else ⟨0, P.amp_pos⟩

def macroWestLabel {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) : Fin P.amp :=
  if h : (M.1.stateAt p).west = true then
    have hi0 : 0 < p.1.1 := by
      have hopen : (M.1.blockAt p).1.x₀.1 < p.1.1 := by
        simpa [RectangularPartition.stateAt] using h
      omega
    let il : Fin n := ⟨p.1.1 - 1, by omega⟩
    have hi : il.1 + 1 < n := by
      have hpN := p.1.isLt
      dsimp [il]
      omega
    M.2.1 ⟨horizontalMacroEdge il p.2 hi,
      by
        unfold RectangularPartition.IsOpen
        have hpEq : (⟨il.1 + 1, hi⟩ : Fin n) = p.1 := by
          apply Fin.ext
          dsimp [il]
          omega
        simpa only [horizontalMacroEdge_lo, horizontalMacroEdge_hi, hpEq]
          using (M.1.west_open_iff p.1 p.2 hi0).mp h⟩
  else ⟨0, P.amp_pos⟩

def macroNorthLabel {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) : Fin P.amp :=
  if h : (M.1.stateAt p).north = true then
    have hj : p.2.1 + 1 < n := by
      have hp := M.1.blockAt_contains p
      have hopen : p.2.1 + 1 < (M.1.blockAt p).1.y₀.1 +
          (M.1.blockAt p).1.height.1 := by
        simpa [RectangularPartition.stateAt] using h
      have hb := (M.1.blockAt p).1.y_bound
      omega
    M.2.1 ⟨verticalMacroEdge p.1 p.2 hj,
      by
        change M.1.SameBlock p (p.1, ⟨p.2.1 + 1, hj⟩)
        simpa using (M.1.north_open_iff p.1 p.2 hj).mp h⟩
  else ⟨0, P.amp_pos⟩

def macroSouthLabel {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) : Fin P.amp :=
  if h : (M.1.stateAt p).south = true then
    have hj0 : 0 < p.2.1 := by
      have hopen : (M.1.blockAt p).1.y₀.1 < p.2.1 := by
        simpa [RectangularPartition.stateAt] using h
      omega
    let jb : Fin n := ⟨p.2.1 - 1, by omega⟩
    have hj : jb.1 + 1 < n := by
      have hpN := p.2.isLt
      dsimp [jb]
      omega
    M.2.1 ⟨verticalMacroEdge p.1 jb hj,
      by
        unfold RectangularPartition.IsOpen
        have hpEq : (⟨jb.1 + 1, hj⟩ : Fin n) = p.2 := by
          apply Fin.ext
          dsimp [jb]
          omega
        simpa only [verticalMacroEdge_lo, verticalMacroEdge_hi, hpEq]
          using (M.1.south_open_iff p.1 p.2 hj0).mp h⟩
  else ⟨0, P.amp_pos⟩

def macroAmpRecordAt {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) :
    AmpRecord P (M.1.stateAt p) where
  west := macroWestLabel M p
  east := macroEastLabel M p
  south := macroSouthLabel M p
  north := macroNorthLabel M p
  west_closed := by
    intro hclosed
    simp only [macroWestLabel]
    split <;> rename_i h
    · rw [h] at hclosed
      contradiction
    · rfl
  east_closed := by
    intro hclosed
    simp only [macroEastLabel]
    split <;> rename_i h
    · rw [h] at hclosed
      contradiction
    · rfl
  south_closed := by
    intro hclosed
    simp only [macroSouthLabel]
    split <;> rename_i h
    · rw [h] at hclosed
      contradiction
    · rfl
  north_closed := by
    intro hclosed
    simp only [macroNorthLabel]
    split <;> rename_i h
    · rw [h] at hclosed
      contradiction
    · rfl

def CellTileRealizes {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (p : MacroCell n) (u : Fin P.tileCount) : Prop :=
  ∃ (B : ↑M.1.blocks) (i : Fin B.1.width.1) (j : Fin B.1.height.1),
    B.1.localCell i j = p ∧ (M.2.2 B).1 i j = u

theorem exists_unique_cellTileRealizes {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) :
    ∃! u : Fin P.tileCount, CellTileRealizes M p u := by
  let B := M.1.blockAt p
  let i := M.1.localX p
  let j := M.1.localY p
  refine ⟨(M.2.2 B).1 i j, ⟨B, i, j,
    by simpa [B, i, j] using M.1.localCell_blockAt p, rfl⟩, ?_⟩
  intro u hu
  rcases hu with ⟨C, i', j', hcell, rfl⟩
  have hCp : C.1.Contains p := by
    rw [← hcell]
    exact C.1.localCell_contains i' j'
  have hCB : C = B := (M.1.blockAt_eq_of_contains p C hCp).symm
  subst C
  have hi : i' = i := by
    apply Fin.ext
    have hc := congrArg (fun q : MacroCell n => q.1.1) hcell
    dsimp [GridRectangle.localCell, i, RectangularPartition.localX, B] at hc ⊢
    have hp := M.1.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega
  have hj : j' = j := by
    apply Fin.ext
    have hc := congrArg (fun q : MacroCell n => q.2.1) hcell
    dsimp [GridRectangle.localCell, j, RectangularPartition.localY, B] at hc ⊢
    have hp := M.1.blockAt_contains p
    unfold GridRectangle.Contains at hp
    omega
  subst i'
  subst j'
  rfl

def macroTileAt {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) :
    Fin P.tileCount := Classical.choose (exists_unique_cellTileRealizes M p)

theorem macroTileAt_spec {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) :
    CellTileRealizes M p (macroTileAt M p) :=
  (Classical.choose_spec (exists_unique_cellTileRealizes M p)).1

theorem macroTileAt_eq_of_realizes {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n)
    (u : Fin P.tileCount) (h : CellTileRealizes M p u) :
    macroTileAt M p = u :=
  ((Classical.choose_spec (exists_unique_cellTileRealizes M p)).2 u h).symm

def macroCarrierDatumAt {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) (p : MacroCell n) :
    CarrierDatum P :=
  { state := M.1.stateAt p
    tile := macroTileAt M p
    labels := macroAmpRecordAt M p }

theorem macroTileAt_horizontal
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hi : i.1 + 1 < n)
    (hsame : M.1.SameBlock (i, j) (⟨i.1 + 1, hi⟩, j)) :
    P.east (macroTileAt M (i, j)) =
      P.west (macroTileAt M (⟨i.1 + 1, hi⟩, j)) := by
  rcases hsame with ⟨B0, hBmem, hp, hq⟩
  let B : ↑M.1.blocks := ⟨B0, hBmem⟩
  have hpX0 : B0.x₀.1 ≤ i.1 := hp.1
  have hpX1 : i.1 < B0.x₀.1 + B0.width.1 := hp.2.1
  have hpY0 : B0.y₀.1 ≤ j.1 := hp.2.2.1
  have hpY1 : j.1 < B0.y₀.1 + B0.height.1 := hp.2.2.2
  have hqX0 : B0.x₀.1 ≤ i.1 + 1 := by simpa using hq.1
  have hqX1 : i.1 + 1 < B0.x₀.1 + B0.width.1 := by simpa using hq.2.1
  have hqY0 : B0.y₀.1 ≤ j.1 := by simpa using hq.2.2.1
  have hqY1 : j.1 < B0.y₀.1 + B0.height.1 := by simpa using hq.2.2.2
  let ip : Fin B0.width.1 := ⟨i.1 - B0.x₀.1, by
    omega⟩
  let jp : Fin B0.height.1 := ⟨j.1 - B0.y₀.1, by
    omega⟩
  let iq : Fin B0.width.1 := ⟨i.1 + 1 - B0.x₀.1, by
    omega⟩
  have hcellp : B0.localCell ip jp = (i, j) := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [GridRectangle.localCell, ip]
      omega
    · apply Fin.ext
      dsimp [GridRectangle.localCell, jp]
      omega
  have hcellq : B0.localCell iq jp = (⟨i.1 + 1, hi⟩, j) := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [GridRectangle.localCell, iq]
      omega
    · apply Fin.ext
      dsimp [GridRectangle.localCell, jp]
      omega
  have hip : ip.1 + 1 < B0.width.1 := by
    dsimp [ip]
    omega
  have hiq : (⟨ip.1 + 1, hip⟩ : Fin B0.width.1) = iq := by
    apply Fin.ext
    dsimp [ip, iq]
    omega
  have hpReal : CellTileRealizes M (i, j) ((M.2.2 B).1 ip jp) :=
    ⟨B, ip, jp, hcellp, rfl⟩
  have hqReal : CellTileRealizes M (⟨i.1 + 1, hi⟩, j) ((M.2.2 B).1 iq jp) :=
    ⟨B, iq, jp, hcellq, rfl⟩
  rw [macroTileAt_eq_of_realizes M _ _ hpReal,
    macroTileAt_eq_of_realizes M _ _ hqReal]
  have hc := (M.2.2 B).2.1 ip jp hip
  simpa [hiq, registerWangTile] using hc

theorem macroTileAt_vertical
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hj : j.1 + 1 < n)
    (hsame : M.1.SameBlock (i, j) (i, ⟨j.1 + 1, hj⟩)) :
    P.north (macroTileAt M (i, j)) =
      P.south (macroTileAt M (i, ⟨j.1 + 1, hj⟩)) := by
  rcases hsame with ⟨B0, hBmem, hp, hq⟩
  let B : ↑M.1.blocks := ⟨B0, hBmem⟩
  have hpX0 : B0.x₀.1 ≤ i.1 := hp.1
  have hpX1 : i.1 < B0.x₀.1 + B0.width.1 := hp.2.1
  have hpY0 : B0.y₀.1 ≤ j.1 := hp.2.2.1
  have hpY1 : j.1 < B0.y₀.1 + B0.height.1 := hp.2.2.2
  have hqX0 : B0.x₀.1 ≤ i.1 := by simpa using hq.1
  have hqX1 : i.1 < B0.x₀.1 + B0.width.1 := by simpa using hq.2.1
  have hqY0 : B0.y₀.1 ≤ j.1 + 1 := by simpa using hq.2.2.1
  have hqY1 : j.1 + 1 < B0.y₀.1 + B0.height.1 := by simpa using hq.2.2.2
  let ip : Fin B0.width.1 := ⟨i.1 - B0.x₀.1, by omega⟩
  let jp : Fin B0.height.1 := ⟨j.1 - B0.y₀.1, by omega⟩
  let jq : Fin B0.height.1 := ⟨j.1 + 1 - B0.y₀.1, by omega⟩
  have hcellp : B0.localCell ip jp = (i, j) := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [GridRectangle.localCell, ip]
      omega
    · apply Fin.ext
      dsimp [GridRectangle.localCell, jp]
      omega
  have hcellq : B0.localCell ip jq = (i, ⟨j.1 + 1, hj⟩) := by
    apply Prod.ext
    · apply Fin.ext
      dsimp [GridRectangle.localCell, ip]
      omega
    · apply Fin.ext
      dsimp [GridRectangle.localCell, jq]
      omega
  have hjp : jp.1 + 1 < B0.height.1 := by
    dsimp [jp]
    omega
  have hjq : (⟨jp.1 + 1, hjp⟩ : Fin B0.height.1) = jq := by
    apply Fin.ext
    dsimp [jp, jq]
    omega
  have hpReal : CellTileRealizes M (i, j) ((M.2.2 B).1 ip jp) :=
    ⟨B, ip, jp, hcellp, rfl⟩
  have hqReal : CellTileRealizes M (i, ⟨j.1 + 1, hj⟩) ((M.2.2 B).1 ip jq) :=
    ⟨B, ip, jq, hcellq, rfl⟩
  rw [macroTileAt_eq_of_realizes M _ _ hpReal,
    macroTileAt_eq_of_realizes M _ _ hqReal]
  have hc := (M.2.2 B).2.2 ip jp hjp
  simpa [hjq, registerWangTile] using hc

private theorem bool_eq_of_true_iff {a b : Bool} (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

theorem stateAt_horizontal_east_west
    {n : ℕ} (D : RectangularPartition n) (i j : Fin n)
    (hi : i.1 + 1 < n) :
    (D.stateAt (i, j)).east = (D.stateAt (⟨i.1 + 1, hi⟩, j)).west := by
  apply bool_eq_of_true_iff
  rw [D.east_open_iff i j hi]
  have hpos : 0 < (⟨i.1 + 1, hi⟩ : Fin n).1 := by simp
  rw [D.west_open_iff ⟨i.1 + 1, hi⟩ j hpos]
  have heq : (⟨(⟨i.1 + 1, hi⟩ : Fin n).1 - 1, by omega⟩ : Fin n) = i := by
    apply Fin.ext
    simp
  rw [heq]

theorem stateAt_vertical_north_south
    {n : ℕ} (D : RectangularPartition n) (i j : Fin n)
    (hj : j.1 + 1 < n) :
    (D.stateAt (i, j)).north = (D.stateAt (i, ⟨j.1 + 1, hj⟩)).south := by
  apply bool_eq_of_true_iff
  rw [D.north_open_iff i j hj]
  have hpos : 0 < (⟨j.1 + 1, hj⟩ : Fin n).1 := by simp
  rw [D.south_open_iff i ⟨j.1 + 1, hj⟩ hpos]
  have heq : (⟨(⟨j.1 + 1, hj⟩ : Fin n).1 - 1, by omega⟩ : Fin n) = j := by
    apply Fin.ext
    simp
  rw [heq]

theorem stateAt_horizontal_perpendicular
    {n : ℕ} (D : RectangularPartition n) (i j : Fin n)
    (hi : i.1 + 1 < n)
    (hsame : D.SameBlock (i, j) (⟨i.1 + 1, hi⟩, j)) :
    (D.stateAt (i, j)).south = (D.stateAt (⟨i.1 + 1, hi⟩, j)).south ∧
    (D.stateAt (i, j)).north = (D.stateAt (⟨i.1 + 1, hi⟩, j)).north := by
  have hB := congrArg Subtype.val (D.blockAt_eq_of_sameBlock hsame)
  constructor <;> simp [RectangularPartition.stateAt, hB]

theorem stateAt_vertical_perpendicular
    {n : ℕ} (D : RectangularPartition n) (i j : Fin n)
    (hj : j.1 + 1 < n)
    (hsame : D.SameBlock (i, j) (i, ⟨j.1 + 1, hj⟩)) :
    (D.stateAt (i, j)).west = (D.stateAt (i, ⟨j.1 + 1, hj⟩)).west ∧
    (D.stateAt (i, j)).east = (D.stateAt (i, ⟨j.1 + 1, hj⟩)).east := by
  have hB := congrArg Subtype.val (D.blockAt_eq_of_sameBlock hsame)
  constructor <;> simp [RectangularPartition.stateAt, hB]

theorem macroEastLabel_eq_macroWestLabel
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hi : i.1 + 1 < n)
    (he : (M.1.stateAt (i, j)).east = true)
    (hw : (M.1.stateAt (⟨i.1 + 1, hi⟩, j)).west = true) :
    macroEastLabel M (i, j) = macroWestLabel M (⟨i.1 + 1, hi⟩, j) := by
  unfold macroEastLabel macroWestLabel
  simp only [dif_pos he, dif_pos hw]
  apply congrArg M.2.1
  apply Subtype.ext
  apply congrArg Sum.inl
  apply Prod.ext
  · apply Fin.ext
    dsimp [horizontalMacroEdge]
  · rfl

theorem macroNorthLabel_eq_macroSouthLabel
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hj : j.1 + 1 < n)
    (hn : (M.1.stateAt (i, j)).north = true)
    (hs : (M.1.stateAt (i, ⟨j.1 + 1, hj⟩)).south = true) :
    macroNorthLabel M (i, j) = macroSouthLabel M (i, ⟨j.1 + 1, hj⟩) := by
  unfold macroNorthLabel macroSouthLabel
  simp only [dif_pos hn, dif_pos hs]
  apply congrArg M.2.1
  apply Subtype.ext
  apply congrArg Sum.inr
  apply Prod.ext
  · rfl
  · apply Fin.ext
    dsimp [verticalMacroEdge]

theorem macroEastLabel_of_isOpen
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hi : i.1 + 1 < n)
    (hopen : M.1.IsOpen (horizontalMacroEdge i j hi)) :
    macroEastLabel M (i, j) =
      M.2.1 ⟨horizontalMacroEdge i j hi, hopen⟩ := by
  have hs : (M.1.stateAt (i, j)).east = true := by
    apply (M.1.east_open_iff i j hi).mpr
    simpa [RectangularPartition.IsOpen] using hopen
  unfold macroEastLabel
  simp only [dif_pos hs]

theorem macroNorthLabel_of_isOpen
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (i j : Fin n) (hj : j.1 + 1 < n)
    (hopen : M.1.IsOpen (verticalMacroEdge i j hj)) :
    macroNorthLabel M (i, j) =
      M.2.1 ⟨verticalMacroEdge i j hj, hopen⟩ := by
  have hs : (M.1.stateAt (i, j)).north = true := by
    apply (M.1.north_open_iff i j hj).mpr
    simpa [RectangularPartition.IsOpen] using hopen
  unfold macroNorthLabel
  simp only [dif_pos hs]

/-- Explicit inverse constructor: every rectangular macro decoration gives
one anchored register grid, with no decoder or realization supplied as a
parameter. -/
def macroDataToAnchoredGrid (P : RegisterParams) (n : ℕ) :
    MacroData n (registerWangTile P) P.amp → AnchoredGrid P n := by
  intro M
  refine
    { cell := fun i j => macroCarrierDatumAt M (i, j)
      horizontal := ?_
      vertical := ?_
      westClosed := ?_
      eastClosed := ?_
      southClosed := ?_
      northClosed := ?_ }
  · intro i j hi
    let q : MacroCell n := (⟨i.1 + 1, hi⟩, j)
    refine ⟨stateAt_horizontal_east_west M.1 i j hi, ?_⟩
    intro hopen
    have hsame := (M.1.east_open_iff i j hi).mp hopen
    have hw : (M.1.stateAt q).west = true := by
      rw [← stateAt_horizontal_east_west M.1 i j hi]
      exact hopen
    have hperp := stateAt_horizontal_perpendicular M.1 i j hi hsame
    exact ⟨hperp.1, hperp.2,
      macroTileAt_horizontal M i j hi hsame,
      macroEastLabel_eq_macroWestLabel M i j hi hopen hw⟩
  · intro i j hj
    let q : MacroCell n := (i, ⟨j.1 + 1, hj⟩)
    refine ⟨stateAt_vertical_north_south M.1 i j hj, ?_⟩
    intro hopen
    have hsame := (M.1.north_open_iff i j hj).mp hopen
    have hs : (M.1.stateAt q).south = true := by
      rw [← stateAt_vertical_north_south M.1 i j hj]
      exact hopen
    have hperp := stateAt_vertical_perpendicular M.1 i j hj hsame
    exact ⟨hperp.1, hperp.2,
      macroTileAt_vertical M i j hj hsame,
      macroNorthLabel_eq_macroSouthLabel M i j hj hopen hs⟩
  · intro j
    change (M.1.stateAt (⟨0, Nat.zero_lt_of_lt j.isLt⟩, j)).west = false
    simp [RectangularPartition.stateAt]
  · intro j
    let i : Fin n := ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (by decide)⟩
    change (M.1.stateAt (i, j)).east = false
    have hb := (M.1.blockAt (i, j)).1.x_bound
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    have hiN : i.1 + 1 = n := by dsimp [i]; omega
    have hnot : ¬ (i.1 + 1 < (M.1.blockAt (i, j)).1.x₀.1 +
        (M.1.blockAt (i, j)).1.width.1) := by
      intro h
      omega
    simp [RectangularPartition.stateAt, hnot]
  · intro i
    change (M.1.stateAt (i, ⟨0, Nat.zero_lt_of_lt i.isLt⟩)).south = false
    simp [RectangularPartition.stateAt]
  · intro i
    let j : Fin n := ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (by decide)⟩
    change (M.1.stateAt (i, j)).north = false
    have hb := (M.1.blockAt (i, j)).1.y_bound
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have hjN : j.1 + 1 = n := by dsimp [j]; omega
    have hnot : ¬ (j.1 + 1 < (M.1.blockAt (i, j)).1.y₀.1 +
        (M.1.blockAt (i, j)).1.height.1) := by
      intro h
      omega
    simp [RectangularPartition.stateAt, hnot]

theorem rectangularPartition_eq_of_sameBlock_iff {n : ℕ}
    (D E : RectangularPartition n)
    (hrel : ∀ p q : MacroCell n, D.SameBlock p q ↔ E.SameBlock p q) :
    D = E := by
  apply RectangularPartition.ext
  ext B
  constructor
  · intro hBD
    let p := B.lowerLeft
    let C : ↑E.blocks := E.blockAt p
    have hpB : B.Contains p := B.contains_lowerLeft
    have hBC : ∀ q : MacroCell n, B.Contains q → C.1.Contains q := by
      intro q hq
      have hsD : D.SameBlock p q := ⟨B, hBD, hpB, hq⟩
      have hsE := (hrel p q).mp hsD
      have heq := E.blockAt_eq_of_sameBlock hsE
      change (E.blockAt p).1.Contains q
      rw [heq]
      exact E.blockAt_contains q
    have hCB : ∀ q : MacroCell n, C.1.Contains q → B.Contains q := by
      intro q hq
      have hpC : C.1.Contains p := by
        change (E.blockAt p).1.Contains p
        exact E.blockAt_contains p
      have hsE : E.SameBlock p q := ⟨C.1, C.2, hpC, hq⟩
      have hsD := (hrel p q).mpr hsE
      rcases hsD with ⟨B', hB', hp', hq'⟩
      have heq : B' = B := (D.unique_block p).unique ⟨hB', hp'⟩ ⟨hBD, hpB⟩
      simpa [heq] using hq'
    have heq : B = C.1 := gridRectangle_eq_of_mutual_contains B C.1 hBC hCB
    rw [heq]
    exact C.2
  · intro hBE
    let p := B.lowerLeft
    let C : ↑D.blocks := D.blockAt p
    have hpB : B.Contains p := B.contains_lowerLeft
    have hBC : ∀ q : MacroCell n, B.Contains q → C.1.Contains q := by
      intro q hq
      have hsE : E.SameBlock p q := ⟨B, hBE, hpB, hq⟩
      have hsD := (hrel p q).mpr hsE
      have heq := D.blockAt_eq_of_sameBlock hsD
      change (D.blockAt p).1.Contains q
      rw [heq]
      exact D.blockAt_contains q
    have hCB : ∀ q : MacroCell n, C.1.Contains q → B.Contains q := by
      intro q hq
      have hpC : C.1.Contains p := by
        change (D.blockAt p).1.Contains p
        exact D.blockAt_contains p
      have hsD : D.SameBlock p q := ⟨C.1, C.2, hpC, hq⟩
      have hsE := (hrel p q).mp hsD
      rcases hsE with ⟨B', hB', hp', hq'⟩
      have heq : B' = B := (E.unique_block p).unique ⟨hB', hp'⟩ ⟨hBE, hpB⟩
      simpa [heq] using hq'
    have heq : B = C.1 := gridRectangle_eq_of_mutual_contains B C.1 hBC hCB
    rw [heq]
    exact C.2

theorem reconstructed_filled_sameBlock
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp)
    (C : GridRectangle n)
    (hfill : C.Filled (macroDataToAnchoredGrid P n M))
    (p q : MacroCell n) (hp : C.Contains p) (hq : C.Contains q) :
    M.1.SameBlock p q := by
  have hxPath : ∀ (x : ℕ) (hx0 : C.x₀.1 ≤ x)
      (hxTop : x < C.x₀.1 + C.width.1),
      M.1.SameBlock (C.x₀, C.y₀)
        (⟨x, hxTop.trans_le C.x_bound⟩, C.y₀) := by
    intro x hx0 hxTop
    induction x, hx0 using Nat.le_induction with
    | base => exact M.1.sameBlock_refl _
    | succ x hbase ih =>
        have hxC : x + 1 < C.x₀.1 + C.width.1 := hxTop
        have hxN : x < n := by have hb := C.x_bound; omega
        have hsN : x + 1 < n := by have hb := C.x_bound; omega
        let ix : Fin n := ⟨x, hxN⟩
        let iy : Fin n := C.y₀
        have hp0 : C.Contains (ix, iy) := by
          unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          have hh := C.height_pos
          omega
        have hp1 : C.Contains (⟨x + 1, hsN⟩, iy) := by
          unfold GridRectangle.Contains iy
          dsimp [iy]
          have hh := C.height_pos
          omega
        have hopen := hfill.1 ix iy hsN hp0 hp1
        change (M.1.stateAt (ix, iy)).east = true at hopen
        have hedge := (M.1.east_open_iff ix iy hsN).mp hopen
        exact M.1.sameBlock_trans (ih (by omega)) hedge
  have hyPath : ∀ (x : Fin n), C.x₀.1 ≤ x.1 →
      x.1 < C.x₀.1 + C.width.1 →
      ∀ (y : ℕ) (hy0 : C.y₀.1 ≤ y)
        (hyTop : y < C.y₀.1 + C.height.1),
      M.1.SameBlock (x, C.y₀)
        (x, ⟨y, hyTop.trans_le C.y_bound⟩) := by
    intro x hx0 hx1 y hy0 hyTop
    induction y, hy0 using Nat.le_induction with
    | base => exact M.1.sameBlock_refl _
    | succ y hbase ih =>
        have hyC : y + 1 < C.y₀.1 + C.height.1 := by
          exact hyTop
        have hyN : y < n := by have hb := C.y_bound; omega
        have hsN : y + 1 < n := by have hb := C.y_bound; omega
        let ix : Fin n := x
        let iy : Fin n := ⟨y, hyN⟩
        have hp0 : C.Contains (ix, iy) := by
          unfold GridRectangle.Contains ix iy
          dsimp [ix, iy]
          omega
        have hp1 : C.Contains (ix, ⟨y + 1, hsN⟩) := by
          unfold GridRectangle.Contains ix
          dsimp [ix]
          omega
        have hopen := hfill.2 ix iy hsN hp0 hp1
        change (M.1.stateAt (ix, iy)).north = true at hopen
        have hedge := (M.1.north_open_iff ix iy hsN).mp hopen
        exact M.1.sameBlock_trans (ih (by omega)) hedge
  have hllp : M.1.SameBlock (C.x₀, C.y₀) (p.1, C.y₀) :=
    hxPath p.1.1 hp.1 hp.2.1
  have hllq : M.1.SameBlock (C.x₀, C.y₀) (q.1, C.y₀) :=
    hxPath q.1.1 hq.1 hq.2.1
  have hpv : M.1.SameBlock (p.1, C.y₀) p :=
    hyPath p.1 hp.1 hp.2.1 p.2.1 hp.2.2.1 hp.2.2.2
  have hqv : M.1.SameBlock (q.1, C.y₀) q :=
    hyPath q.1 hq.1 hq.2.1 q.2.1 hq.2.2.1 hq.2.2.2
  exact M.1.sameBlock_trans
    (M.1.sameBlock_symm (M.1.sameBlock_trans hllp hpv))
    (M.1.sameBlock_trans hllq hqv)

theorem anchoredPartition_macroDataToAnchoredGrid
    {P : RegisterParams} {n : ℕ}
    (M : MacroData n (registerWangTile P) P.amp) :
    anchoredRectangularPartition (macroDataToAnchoredGrid P n M) = M.1 := by
  let A := macroDataToAnchoredGrid P n M
  apply rectangularPartition_eq_of_sameBlock_iff
  intro p q
  constructor
  · rintro ⟨B, hB, hp, hq⟩
    exact reconstructed_filled_sameBlock M B
      (anchoredRectangularPartition_mem_filled A hB) p q hp hq
  · rintro ⟨B, hB, hp, hq⟩
    rw [anchoredRectangularPartition_sameBlock_iff]
    have hfill : B.Filled A := by
      constructor
      · intro i j hi hip hiq
        change (M.1.stateAt (i, j)).east = true
        apply (M.1.east_open_iff i j hi).mpr
        exact ⟨B, hB, hip, hiq⟩
      · intro i j hj hip hiq
        change (M.1.stateAt (i, j)).north = true
        apply (M.1.north_open_iff i j hj).mpr
        exact ⟨B, hB, hip, hiq⟩
    exact filledRectangle_subset_maximal A p p
      (maximalFilledRectangle_contains A p) B hp hfill q hq

/-- Extensionality through partition-independent observables.  This avoids
leaking any dependent proof transport into the public equivalence. -/
theorem macroData_ext
    {P : RegisterParams} {n : ℕ}
    (M N : MacroData n (registerWangTile P) P.amp)
    (hpart : M.1 = N.1)
    (htile : ∀ p : MacroCell n, macroTileAt M p = macroTileAt N p)
    (hedge : ∀ (e : MacroEdge n) (hM : M.1.IsOpen e) (hN : N.1.IsOpen e),
      M.2.1 ⟨e, hM⟩ = N.2.1 ⟨e, hN⟩) : M = N := by
  rcases M with ⟨D, d⟩
  rcases N with ⟨E, e⟩
  dsimp at hpart
  subst E
  apply congrArg (Sigma.mk D)
  apply Prod.ext
  · funext x
    exact hedge x.1 x.2 x.2
  · funext B
    apply Subtype.ext
    funext i j
    have hd : macroTileAt (⟨D, d⟩ :
        MacroData n (registerWangTile P) P.amp) (B.1.localCell i j) =
        (d.2 B).1 i j := by
      apply macroTileAt_eq_of_realizes
      exact ⟨B, i, j, rfl, rfl⟩
    have he : macroTileAt (⟨D, e⟩ :
        MacroData n (registerWangTile P) P.amp) (B.1.localCell i j) =
        (e.2 B).1 i j := by
      apply macroTileAt_eq_of_realizes
      exact ⟨B, i, j, rfl, rfl⟩
    exact hd.symm.trans ((htile (B.1.localCell i j)).trans he)

theorem anchoredGridToMacroData_macroDataToAnchoredGrid
    {P : RegisterParams} {n : ℕ}
    (M₀ : MacroData n (registerWangTile P) P.amp) :
    anchoredGridToMacroData P n (macroDataToAnchoredGrid P n M₀) = M₀ := by
  let A := macroDataToAnchoredGrid P n M₀
  change anchoredGridToMacroData P n A = M₀
  have hD : anchoredRectangularPartition A = M₀.1 := by
    simpa [A] using anchoredPartition_macroDataToAnchoredGrid M₀
  let F := anchoredGridToMacroData P n A
  change F = M₀
  apply macroData_ext F M₀ (by simpa [F, anchoredGridToMacroData] using hD)
  · intro p
    let B := F.1.blockAt p
    let i := F.1.localX p
    let j := F.1.localY p
    apply macroTileAt_eq_of_realizes
    refine ⟨B, i, j, F.1.localCell_blockAt p, ?_⟩
    change (A.cell (B.1.localCell i j).1 (B.1.localCell i j).2).tile =
      macroTileAt M₀ p
    rw [F.1.localCell_blockAt p]
    rfl
  · intro e hF hM
    cases e with
    | inl h =>
        let i : Fin n := ⟨h.1.1, lt_of_lt_of_le h.1.2 (Nat.sub_le n 1)⟩
        have hi : i.1 + 1 < n := by dsimp [i]; omega
        have hedge : horizontalMacroEdge i h.2 hi = Sum.inl h := by
          apply congrArg Sum.inl
          apply Prod.ext
          · apply Fin.ext
            rfl
          · rfl
        have hopen' : M₀.1.IsOpen (horizontalMacroEdge i h.2 hi) := by
          simpa [hedge] using hM
        have hl := macroEastLabel_of_isOpen M₀ i h.2 hi hopen'
        simpa [F, A, anchoredGridToMacroData, anchoredOpenEdgeLabel,
          macroDataToAnchoredGrid, macroCarrierDatumAt, macroAmpRecordAt,
          hedge] using hl
    | inr v =>
        let j : Fin n := ⟨v.2.1, lt_of_lt_of_le v.2.2 (Nat.sub_le n 1)⟩
        have hj : j.1 + 1 < n := by dsimp [j]; omega
        have hedge : verticalMacroEdge v.1 j hj = Sum.inr v := by
          apply congrArg Sum.inr
          apply Prod.ext
          · rfl
          · apply Fin.ext
            rfl
        have hopen' : M₀.1.IsOpen (verticalMacroEdge v.1 j hj) := by
          simpa [hedge] using hM
        have hl := macroNorthLabel_of_isOpen M₀ v.1 j hj hopen'
        simpa [F, A, anchoredGridToMacroData, anchoredOpenEdgeLabel,
          macroDataToAnchoredGrid, macroCarrierDatumAt, macroAmpRecordAt,
          hedge] using hl

theorem stateAt_anchoredPartition
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    (anchoredRectangularPartition A).stateAt p = (A.cell p.1 p.2).state := by
  apply MacroState.ext
  · by_cases h0 : p.1.1 = 0
    · have hp0 : p.1 = ⟨0, by omega⟩ := Fin.ext h0
      have hL : ((anchoredRectangularPartition A).stateAt p).west = false := by
        have hb := (anchoredRectangularPartition A).blockAt_contains p
        unfold GridRectangle.Contains at hb
        simp [RectangularPartition.stateAt]
        omega
      have hR : (A.cell p.1 p.2).state.west = false := by
        simpa [hp0] using A.westClosed p.2
      rw [hL, hR]
    · have hi0 : 0 < p.1.1 := by omega
      let il : Fin n := ⟨p.1.1 - 1, by omega⟩
      have hi : il.1 + 1 < n := by dsimp [il]; omega
      have hpEq : (⟨il.1 + 1, hi⟩ : Fin n) = p.1 := by
        apply Fin.ext
        dsimp [il]
        omega
      apply bool_eq_of_true_iff
      rw [(anchoredRectangularPartition A).west_open_iff p.1 p.2 hi0]
      have hc := A.horizontal il p.2 hi
      constructor
      · intro hs
        have hs' : (anchoredRectangularPartition A).SameBlock
            (il, p.2) (⟨il.1 + 1, hi⟩, p.2) := by
          simpa only [hpEq] using hs
        have hopen := (anchoredPartition_horizontal_open_iff A il p.2 hi).mp hs'
        change (A.cell il p.2).state.east = true at hopen
        have hw' : (A.cell ⟨il.1 + 1, hi⟩ p.2).state.west = true := by
          rw [← hc.1]
          exact hopen
        simpa only [hpEq] using hw'
      · intro hw
        have hw' : (A.cell ⟨il.1 + 1, hi⟩ p.2).state.west = true := by
          simpa only [hpEq] using hw
        have hopen : (A.cell il p.2).state.east = true := by
          rw [hc.1]
          exact hw'
        change A.openH il p.2 = true at hopen
        have hs := (anchoredPartition_horizontal_open_iff A il p.2 hi).mpr hopen
        simpa only [hpEq] using hs
  · by_cases hi : p.1.1 + 1 < n
    · apply bool_eq_of_true_iff
      rw [(anchoredRectangularPartition A).east_open_iff p.1 p.2 hi]
      rw [anchoredPartition_horizontal_open_iff A p.1 p.2 hi]
      rfl
    · have hpLast : p.1 = ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt p.1.isLt)
          (by decide)⟩ := by
        apply Fin.ext
        dsimp
        omega
      have hclosed := A.eastClosed p.2
      rw [← hpLast] at hclosed
      rw [hclosed]
      unfold RectangularPartition.stateAt
      simp only
      have hb := ((anchoredRectangularPartition A).blockAt p).1.x_bound
      simp
      omega
  · by_cases h0 : p.2.1 = 0
    · have hp0 : p.2 = ⟨0, by omega⟩ := Fin.ext h0
      have hL : ((anchoredRectangularPartition A).stateAt p).south = false := by
        have hb := (anchoredRectangularPartition A).blockAt_contains p
        unfold GridRectangle.Contains at hb
        simp [RectangularPartition.stateAt]
        omega
      have hR : (A.cell p.1 p.2).state.south = false := by
        simpa [hp0] using A.southClosed p.1
      rw [hL, hR]
    · have hj0 : 0 < p.2.1 := by omega
      let jb : Fin n := ⟨p.2.1 - 1, by omega⟩
      have hj : jb.1 + 1 < n := by dsimp [jb]; omega
      have hpEq : (⟨jb.1 + 1, hj⟩ : Fin n) = p.2 := by
        apply Fin.ext
        dsimp [jb]
        omega
      apply bool_eq_of_true_iff
      rw [(anchoredRectangularPartition A).south_open_iff p.1 p.2 hj0]
      have hc := A.vertical p.1 jb hj
      constructor
      · intro hs
        have hs' : (anchoredRectangularPartition A).SameBlock
            (p.1, jb) (p.1, ⟨jb.1 + 1, hj⟩) := by
          simpa only [hpEq] using hs
        have hopen := (anchoredPartition_vertical_open_iff A p.1 jb hj).mp hs'
        change (A.cell p.1 jb).state.north = true at hopen
        have hw' : (A.cell p.1 ⟨jb.1 + 1, hj⟩).state.south = true := by
          rw [← hc.1]
          exact hopen
        simpa only [hpEq] using hw'
      · intro hw
        have hw' : (A.cell p.1 ⟨jb.1 + 1, hj⟩).state.south = true := by
          simpa only [hpEq] using hw
        have hopen : (A.cell p.1 jb).state.north = true := by
          rw [hc.1]
          exact hw'
        change A.openV p.1 jb = true at hopen
        have hs := (anchoredPartition_vertical_open_iff A p.1 jb hj).mpr hopen
        simpa only [hpEq] using hs
  · by_cases hj : p.2.1 + 1 < n
    · apply bool_eq_of_true_iff
      rw [(anchoredRectangularPartition A).north_open_iff p.1 p.2 hj]
      rw [anchoredPartition_vertical_open_iff A p.1 p.2 hj]
      rfl
    · have hpLast : p.2 = ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt p.2.isLt)
          (by decide)⟩ := by
        apply Fin.ext
        dsimp
        omega
      have hclosed := A.northClosed p.1
      rw [← hpLast] at hclosed
      rw [hclosed]
      unfold RectangularPartition.stateAt
      simp only
      have hb := ((anchoredRectangularPartition A).blockAt p).1.y_bound
      simp
      omega

theorem macroTileAt_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroTileAt (anchoredGridToMacroData P n A) p = (A.cell p.1 p.2).tile := by
  let F := anchoredGridToMacroData P n A
  let B := F.1.blockAt p
  let i := F.1.localX p
  let j := F.1.localY p
  apply macroTileAt_eq_of_realizes
  refine ⟨B, i, j, F.1.localCell_blockAt p, ?_⟩
  change (A.cell (B.1.localCell i j).1 (B.1.localCell i j).2).tile =
    (A.cell p.1 p.2).tile
  rw [F.1.localCell_blockAt p]

theorem macroEastLabel_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroEastLabel (anchoredGridToMacroData P n A) p =
      (A.cell p.1 p.2).labels.east := by
  let F := anchoredGridToMacroData P n A
  by_cases h : (A.cell p.1 p.2).state.east = true
  · have hi : p.1.1 + 1 < n := by
      by_contra hstep
      have hpLast : p.1 = ⟨n - 1,
          Nat.sub_lt (Nat.zero_lt_of_lt p.1.isLt) (by decide)⟩ := by
        apply Fin.ext
        dsimp
        omega
      have hc := A.eastClosed p.2
      rw [← hpLast] at hc
      rw [h] at hc
      contradiction
    have hs : (F.1.stateAt p).east = true := by
      change ((anchoredRectangularPartition A).stateAt p).east = true
      rw [stateAt_anchoredPartition A p]
      exact h
    have hopen : F.1.IsOpen (horizontalMacroEdge p.1 p.2 hi) := by
      change (anchoredRectangularPartition A).IsOpen
        (horizontalMacroEdge p.1 p.2 hi)
      unfold RectangularPartition.IsOpen
      simpa using (anchoredPartition_horizontal_open_iff A p.1 p.2 hi).mpr h
    have hl := macroEastLabel_of_isOpen F p.1 p.2 hi hopen
    simpa [F, anchoredGridToMacroData, anchoredOpenEdgeLabel,
      horizontalMacroEdge] using hl
  · have hs : (F.1.stateAt p).east = false := by
      change ((anchoredRectangularPartition A).stateAt p).east = false
      rw [stateAt_anchoredPartition A p]
      exact Bool.eq_false_of_not_eq_true h
    rw [(A.cell p.1 p.2).labels.east_closed (Bool.eq_false_of_not_eq_true h)]
    unfold macroEastLabel
    simp [F, hs]

theorem macroWestLabel_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroWestLabel (anchoredGridToMacroData P n A) p =
      (A.cell p.1 p.2).labels.west := by
  let F := anchoredGridToMacroData P n A
  by_cases h : (A.cell p.1 p.2).state.west = true
  · have hi0 : 0 < p.1.1 := by
      by_contra hp0
      have hz : p.1.1 = 0 := Nat.eq_zero_of_not_pos hp0
      have hpEq : p.1 = ⟨0, Nat.zero_lt_of_lt p.1.isLt⟩ := Fin.ext hz
      have hc := A.westClosed p.2
      rw [← hpEq] at hc
      rw [h] at hc
      contradiction
    let il : Fin n := ⟨p.1.1 - 1, by omega⟩
    have hi : il.1 + 1 < n := by dsimp [il]; omega
    have hpEq : (⟨il.1 + 1, hi⟩ : Fin n) = p.1 := by
      apply Fin.ext
      dsimp [il]
      omega
    have hc := A.horizontal il p.2 hi
    have hleft : (A.cell il p.2).state.east = true := by
      rw [hc.1]
      simpa only [hpEq] using h
    have hsLeft : (F.1.stateAt (il, p.2)).east = true := by
      change ((anchoredRectangularPartition A).stateAt (il, p.2)).east = true
      rw [stateAt_anchoredPartition A (il, p.2)]
      exact hleft
    have hsRight : (F.1.stateAt p).west = true := by
      change ((anchoredRectangularPartition A).stateAt p).west = true
      rw [stateAt_anchoredPartition A p]
      exact h
    calc
      macroWestLabel F p = macroEastLabel F (il, p.2) := by
        symm
        simpa only [hpEq] using
          macroEastLabel_eq_macroWestLabel F il p.2 hi hsLeft
            (by simpa only [hpEq] using hsRight)
      _ = (A.cell il p.2).labels.east :=
        macroEastLabel_anchoredGridToMacroData A (il, p.2)
      _ = (A.cell p.1 p.2).labels.west := by
        have hl := (hc.2 hleft).2.2.2
        rw [hpEq] at hl
        exact hl
  · have hs : (F.1.stateAt p).west = false := by
      change ((anchoredRectangularPartition A).stateAt p).west = false
      rw [stateAt_anchoredPartition A p]
      exact Bool.eq_false_of_not_eq_true h
    rw [(A.cell p.1 p.2).labels.west_closed (Bool.eq_false_of_not_eq_true h)]
    unfold macroWestLabel
    simp [F, hs]

theorem macroNorthLabel_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroNorthLabel (anchoredGridToMacroData P n A) p =
      (A.cell p.1 p.2).labels.north := by
  let F := anchoredGridToMacroData P n A
  by_cases h : (A.cell p.1 p.2).state.north = true
  · have hj : p.2.1 + 1 < n := by
      by_contra hstep
      have hpLast : p.2 = ⟨n - 1,
          Nat.sub_lt (Nat.zero_lt_of_lt p.2.isLt) (by decide)⟩ := by
        apply Fin.ext
        dsimp
        omega
      have hc := A.northClosed p.1
      rw [← hpLast] at hc
      rw [h] at hc
      contradiction
    have hs : (F.1.stateAt p).north = true := by
      change ((anchoredRectangularPartition A).stateAt p).north = true
      rw [stateAt_anchoredPartition A p]
      exact h
    have hopen : F.1.IsOpen (verticalMacroEdge p.1 p.2 hj) := by
      change (anchoredRectangularPartition A).IsOpen
        (verticalMacroEdge p.1 p.2 hj)
      unfold RectangularPartition.IsOpen
      simpa using (anchoredPartition_vertical_open_iff A p.1 p.2 hj).mpr h
    have hl := macroNorthLabel_of_isOpen F p.1 p.2 hj hopen
    simpa [F, anchoredGridToMacroData, anchoredOpenEdgeLabel,
      verticalMacroEdge] using hl
  · have hs : (F.1.stateAt p).north = false := by
      change ((anchoredRectangularPartition A).stateAt p).north = false
      rw [stateAt_anchoredPartition A p]
      exact Bool.eq_false_of_not_eq_true h
    rw [(A.cell p.1 p.2).labels.north_closed (Bool.eq_false_of_not_eq_true h)]
    unfold macroNorthLabel
    simp [F, hs]

theorem macroSouthLabel_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroSouthLabel (anchoredGridToMacroData P n A) p =
      (A.cell p.1 p.2).labels.south := by
  let F := anchoredGridToMacroData P n A
  by_cases h : (A.cell p.1 p.2).state.south = true
  · have hj0 : 0 < p.2.1 := by
      by_contra hp0
      have hz : p.2.1 = 0 := Nat.eq_zero_of_not_pos hp0
      have hpEq : p.2 = ⟨0, Nat.zero_lt_of_lt p.2.isLt⟩ := Fin.ext hz
      have hc := A.southClosed p.1
      rw [← hpEq] at hc
      rw [h] at hc
      contradiction
    let jb : Fin n := ⟨p.2.1 - 1, by omega⟩
    have hj : jb.1 + 1 < n := by dsimp [jb]; omega
    have hpEq : (⟨jb.1 + 1, hj⟩ : Fin n) = p.2 := by
      apply Fin.ext
      dsimp [jb]
      omega
    have hc := A.vertical p.1 jb hj
    have hbelow : (A.cell p.1 jb).state.north = true := by
      rw [hc.1]
      simpa only [hpEq] using h
    have hsBelow : (F.1.stateAt (p.1, jb)).north = true := by
      change ((anchoredRectangularPartition A).stateAt (p.1, jb)).north = true
      rw [stateAt_anchoredPartition A (p.1, jb)]
      exact hbelow
    have hsTop : (F.1.stateAt p).south = true := by
      change ((anchoredRectangularPartition A).stateAt p).south = true
      rw [stateAt_anchoredPartition A p]
      exact h
    calc
      macroSouthLabel F p = macroNorthLabel F (p.1, jb) := by
        symm
        simpa only [hpEq] using
          macroNorthLabel_eq_macroSouthLabel F p.1 jb hj hsBelow
            (by simpa only [hpEq] using hsTop)
      _ = (A.cell p.1 jb).labels.north :=
        macroNorthLabel_anchoredGridToMacroData A (p.1, jb)
      _ = (A.cell p.1 p.2).labels.south := by
        have hl := (hc.2 hbelow).2.2.2
        rw [hpEq] at hl
        exact hl
  · have hs : (F.1.stateAt p).south = false := by
      change ((anchoredRectangularPartition A).stateAt p).south = false
      rw [stateAt_anchoredPartition A p]
      exact Bool.eq_false_of_not_eq_true h
    rw [(A.cell p.1 p.2).labels.south_closed (Bool.eq_false_of_not_eq_true h)]
    unfold macroSouthLabel
    simp [F, hs]

theorem carrierDatum_ext_fields {P : RegisterParams} (a b : CarrierDatum P)
    (hstate : a.state = b.state) (htile : a.tile = b.tile)
    (hwest : a.labels.west = b.labels.west)
    (heast : a.labels.east = b.labels.east)
    (hsouth : a.labels.south = b.labels.south)
    (hnorth : a.labels.north = b.labels.north) : a = b := by
  cases a with
  | mk η u l =>
    cases b with
    | mk θ v r =>
      dsimp at hstate htile hwest heast hsouth hnorth ⊢
      subst θ
      subst v
      have hl : l = r := by
        apply AmpRecord.ext <;> assumption
      subst r
      rfl

theorem macroCarrierDatum_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) (p : MacroCell n) :
    macroCarrierDatumAt (anchoredGridToMacroData P n A) p = A.cell p.1 p.2 := by
  apply carrierDatum_ext_fields
  · exact stateAt_anchoredPartition A p
  · exact macroTileAt_anchoredGridToMacroData A p
  · exact macroWestLabel_anchoredGridToMacroData A p
  · exact macroEastLabel_anchoredGridToMacroData A p
  · exact macroSouthLabel_anchoredGridToMacroData A p
  · exact macroNorthLabel_anchoredGridToMacroData A p

theorem anchoredGrid_eq_of_cell {P : RegisterParams} {n : ℕ}
    (A B : AnchoredGrid P n) (h : ∀ i j, A.cell i j = B.cell i j) : A = B := by
  have hc : A.cell = B.cell := by funext i j; exact h i j
  cases A with
  | mk ac ah av aw ae as an =>
    cases B with
    | mk bc bh bv bw be bs bn =>
      dsimp at hc
      subst bc
      congr

theorem macroDataToAnchoredGrid_anchoredGridToMacroData
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    macroDataToAnchoredGrid P n (anchoredGridToMacroData P n A) = A := by
  apply anchoredGrid_eq_of_cell
  intro i j
  exact macroCarrierDatum_anchoredGridToMacroData A (i, j)

/-- The unconditional combinatorial equivalence missing from the previous
formalization boundary. -/
def anchoredGridEquivMacroData (P : RegisterParams) (n : ℕ) :
    AnchoredGrid P n ≃ MacroData n (registerWangTile P) P.amp where
  toFun := anchoredGridToMacroData P n
  invFun := macroDataToAnchoredGrid P n
  left_inv := macroDataToAnchoredGrid_anchoredGridToMacroData
  right_inv := anchoredGridToMacroData_macroDataToAnchoredGrid

/-- End-to-end physical/combinatorial equivalence. -/
def physicalTilingEquivMacroData (P : RegisterParams) (n : ℕ) :
    Tiling (registerTileSupport P) (square (P.pitch * n)) ≃
      MacroData n (registerWangTile P) P.amp :=
  (physicalTilingEquivAnchoredGrid P n).trans (anchoredGridEquivMacroData P n)

noncomputable instance physicalTilingsFintypeForMacroData
    (P : RegisterParams) (n : ℕ) :
    Fintype (Tiling (registerTileSupport P) (square (P.pitch * n))) :=
  tilingFintype (registerTileSupport P) (square (P.pitch * n))
    (registerTileSupport_nonempty P)

/-- Exact physical count, with no anchoring, decoder, or realization
certificate left as a theorem parameter. -/
theorem physical_exact_macro_count (P : RegisterParams) (n : ℕ) :
    Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * n))) =
      ∑ D : RectangularPartition n, macroWeight (registerWangTile P) P.amp D := by
  rw [Fintype.card_congr (physicalTilingEquivMacroData P n)]
  exact card_macroData n (registerWangTile P) P.amp

/-- Unconditional exponent-zero readout. -/
theorem physical_floor_readout_one_unconditional (P : RegisterParams) :
    Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * 1))) /
        P.amp ^ amplifierExponent 1 =
      openWangCount (registerWangTile P) 1 1 := by
  have hanchor : LatticeAnchored
      (Tiling (registerTileSupport P) (square (P.pitch * 1)))
      (MacroData 1 (registerWangTile P) P.amp) :=
    LatticeAnchored.ofEquiv (physicalTilingEquivMacroData P 1)
  change Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * 1))) /
      (1024 * P.perimeterBase ^ 3) ^ amplifierExponent 1 = _
  exact anchored_amplified_floor_readout_one_whole P.perimeterBase
    (registerWangTile P) hanchor
      (lt_of_lt_of_le (by decide) P.perimeterBase_ge_two)

/-- For `n ≥ 2`, the only remaining premise is the independent finite
dissection census; the entire geometry/decoder/compiler is now internal. -/
theorem physical_floor_readout_unconditional_decoder
    (P : RegisterParams) {n : ℕ} (hn : 2 ≤ n)
    (J : SeamJunkCertificate n (amplifierExponent n) P.perimeterBase
      (macroJunk n (registerWangTile P) P.amp
        (wholePartition n (lt_of_lt_of_le (by decide) hn)))) :
    Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * n))) /
        P.amp ^ amplifierExponent n =
      openWangCount (registerWangTile P) n n := by
  have hanchor : LatticeAnchored
      (Tiling (registerTileSupport P) (square (P.pitch * n)))
      (MacroData n (registerWangTile P) P.amp) :=
    LatticeAnchored.ofEquiv (physicalTilingEquivMacroData P n)
  change Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * n))) /
      (1024 * P.perimeterBase ^ 3) ^ amplifierExponent n = _
  exact anchored_amplified_floor_readout_whole n P.perimeterBase
    (registerWangTile P) hanchor hn
      (lt_of_lt_of_le (by decide) P.perimeterBase_ge_two) J

/-! The independent dissection census seam.  The definitions below turn the
three concrete geometric estimates into the exact `SeamJunkCertificate`
consumed above; no informal regrouping of a finite sum remains. -/

theorem RectangularPartition.seamCount_le_edges {n : ℕ}
    (D : RectangularPartition n) : D.seamCount ≤ amplifierExponent n := by
  unfold RectangularPartition.seamCount amplifierExponent
  rw [← card_macroEdge]
  exact Nat.sub_le _ _

def seamClassTerm (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n) (i : ℕ) : ℕ :=
  ∑ D ∈ (Finset.univ.erase whole).filter (fun D => D.seamCount = i),
    macroWeight tile amp D

/-- Precisely the three independent facts used by the amplifier estimate:
nontrivial dissections have at least `n` seams, their `i`-seam census is at
most `256^i`, and the Wang block product obeys the perimeter exponent. -/
structure RectangularJunkBounds (n R : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (whole : RectangularPartition n) : Prop where
  nonwhole_seam_ge : ∀ D : RectangularPartition n, D ≠ whole → n ≤ D.seamCount
  census : ∀ i : ℕ,
    ((Finset.univ.erase whole).filter (fun D => D.seamCount = i)).card ≤ 256 ^ i
  block_product : ∀ D : RectangularPartition n,
    macroBlockCount tile D ≤ R ^ (2 * n + D.seamCount)

structure RectangularDissectionFacts (n : ℕ)
    (whole : RectangularPartition n) : Prop where
  nonwhole_seam_ge : ∀ D : RectangularPartition n, D ≠ whole → n ≤ D.seamCount
  census : ∀ i : ℕ,
    ((Finset.univ.erase whole).filter (fun D => D.seamCount = i)).card ≤ 256 ^ i
  perimeter : ∀ D : RectangularPartition n,
    ∑ B : ↑D.blocks, (B.1.width.1 + B.1.height.1) = 2 * n + D.seamCount

structure WangRectangleBound (R : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) : Prop where
  bound : ∀ w h : ℕ, openWangCount tile w h ≤ R ^ (w + h)

def RectangularJunkBounds.ofDissectionAndWang
    (n R : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (whole : RectangularPartition n) (D : RectangularDissectionFacts n whole)
    (Wb : WangRectangleBound R tile) : RectangularJunkBounds n R tile whole where
  nonwhole_seam_ge := D.nonwhole_seam_ge
  census := D.census
  block_product := fun E => by
    apply product_bound_from_perimeter
      (fun B : ↑E.blocks => openWangCount tile B.1.width.1 B.1.height.1)
      (fun B : ↑E.blocks => B.1.width.1)
      (fun B : ↑E.blocks => B.1.height.1) R n E.seamCount
    · exact fun B => Wb.bound B.1.width.1 B.1.height.1
    · exact D.perimeter E

theorem macroJunk_eq_seamClassSum
    (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n)
    (hmin : ∀ D : RectangularPartition n, D ≠ whole → n ≤ D.seamCount) :
    macroJunk n tile amp whole =
      ∑ i ∈ Finset.Icc n (amplifierExponent n),
        seamClassTerm n tile amp whole i := by
  classical
  unfold macroJunk seamClassTerm
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro D hD
  have hne : D ≠ whole := Finset.mem_erase.mp hD |>.1
  exact Finset.mem_Icc.mpr ⟨hmin D hne, D.seamCount_le_edges⟩

theorem seamClassTerm_bound
    (n R : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (whole : RectangularPartition n) (C : RectangularJunkBounds n R tile whole)
    (i : ℕ) :
    seamClassTerm n tile (1024 * R ^ 3) whole i ≤
      256 ^ i * (1024 * R ^ 3) ^ (amplifierExponent n - i) *
        R ^ (2 * n + i) := by
  classical
  let s := (Finset.univ.erase whole).filter (fun D => D.seamCount = i)
  let bound := (1024 * R ^ 3) ^ (amplifierExponent n - i) * R ^ (2 * n + i)
  have hpoint : ∀ D ∈ s, macroWeight tile (1024 * R ^ 3) D ≤ bound := by
    intro D hD
    have hseam : D.seamCount = i := (Finset.mem_filter.mp hD).2
    unfold macroWeight bound
    rw [D.openEdgeCount_eq_grid_sub_seams, hseam]
    exact Nat.mul_le_mul_left _ (by simpa [hseam] using C.block_product D)
  calc
    seamClassTerm n tile (1024 * R ^ 3) whole i =
        ∑ D ∈ s, macroWeight tile (1024 * R ^ 3) D := rfl
    _ ≤ s.card * bound := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s
        (fun D => macroWeight tile (1024 * R ^ 3) D) bound hpoint
    _ ≤ 256 ^ i * bound := Nat.mul_le_mul_right bound (C.census i)
    _ = 256 ^ i * (1024 * R ^ 3) ^ (amplifierExponent n - i) *
        R ^ (2 * n + i) := by simp [bound, Nat.mul_assoc]

def seamJunkCertificateOfBounds
    (n R : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (whole : RectangularPartition n) (C : RectangularJunkBounds n R tile whole) :
    SeamJunkCertificate n (amplifierExponent n) R
      (macroJunk n tile (1024 * R ^ 3) whole) where
  term := seamClassTerm n tile (1024 * R ^ 3) whole
  junk_eq := macroJunk_eq_seamClassSum n tile _ whole C.nonwhole_seam_ge
  raw_bound := fun i _ => seamClassTerm_bound n R tile whole C i

theorem physical_floor_readout_of_rectangular_bounds
    (P : RegisterParams) {n : ℕ} (hn : 2 ≤ n)
    (C : RectangularJunkBounds n P.perimeterBase (registerWangTile P)
      (wholePartition n (lt_of_lt_of_le (by decide) hn))) :
    Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * n))) /
        P.amp ^ amplifierExponent n =
      openWangCount (registerWangTile P) n n :=
  physical_floor_readout_unconditional_decoder P hn
    (seamJunkCertificateOfBounds n P.perimeterBase (registerWangTile P)
      (wholePartition n (lt_of_lt_of_le (by decide) hn)) C)

end
end PakFixedPolyomino
