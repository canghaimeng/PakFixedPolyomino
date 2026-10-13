import PakFixedPolyomino.Anchoring

namespace PakFixedPolyomino

noncomputable section

structure CarrierDatum (P : RegisterParams) where
  state : MacroState
  tile : Fin P.tileCount
  labels : AmpRecord P state

def CarrierDatum.support (P : RegisterParams) (d : CarrierDatum P) : Polyomino :=
  carrier P d.state d.tile d.labels

def HorizontalCompatibleDatum (P : RegisterParams)
    (a b : CarrierDatum P) : Prop :=
  HorizontalCompatible P a.state b.state a.tile b.tile a.labels b.labels

def VerticalCompatibleDatum (P : RegisterParams)
    (a b : CarrierDatum P) : Prop :=
  VerticalCompatible P a.state b.state a.tile b.tile a.labels b.labels

/-- A completely indexed anchored macro-grid with every actual interface law. -/
structure AnchoredGrid (P : RegisterParams) (n : ℕ) where
  cell : Fin n → Fin n → CarrierDatum P
  horizontal : ∀ (i j : Fin n) (hi : i.1 + 1 < n),
    HorizontalCompatibleDatum P (cell i j) (cell ⟨i.1 + 1, hi⟩ j)
  vertical : ∀ (i j : Fin n) (hj : j.1 + 1 < n),
    VerticalCompatibleDatum P (cell i j) (cell i ⟨j.1 + 1, hj⟩)
  westClosed : ∀ j, (cell ⟨0, Nat.zero_lt_of_lt j.isLt⟩ j).state.west = false
  eastClosed : ∀ j, (cell ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (by decide)⟩ j).state.east = false
  southClosed : ∀ i, (cell i ⟨0, Nat.zero_lt_of_lt i.isLt⟩).state.south = false
  northClosed : ∀ i, (cell i ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (by decide)⟩).state.north = false

def AnchoredGrid.openH {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) : Bool := (A.cell i j).state.east

def AnchoredGrid.openV {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) : Bool := (A.cell i j).state.north

/-- Local 2-by-2 saturation predicate. -/
def SaturatedFour (bottom right top left : Bool) : Prop :=
  ((bottom = true ∧ right = true) ∨
   (right = true ∧ top = true) ∨
   (top = true ∧ left = true) ∨
   (left = true ∧ bottom = true)) →
  bottom = true ∧ right = true ∧ top = true ∧ left = true

/-- The physical interface register forces SAT_mac on every 2-by-2. -/
theorem anchoredGrid_saturated
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) (hi : i.1 + 1 < n) (hj : j.1 + 1 < n) :
    SaturatedFour
      (A.openH i j)
      (A.openV ⟨i.1 + 1, hi⟩ j)
      (A.openH i ⟨j.1 + 1, hj⟩)
      (A.openV i j) := by
  let ir : Fin n := ⟨i.1 + 1, hi⟩
  let jt : Fin n := ⟨j.1 + 1, hj⟩
  have hB := A.horizontal i j hi
  have hT := A.horizontal i jt hi
  have hL := A.vertical i j hj
  have hR := A.vertical ir j hj
  unfold SaturatedFour
  intro hpair
  have br : A.openH i j = true → A.openV ir j = A.openV i j := by
    intro hb
    have hperp := hB.2 hb
    exact hperp.2.1.symm
  have rt : A.openV ir j = true → A.openH i jt = A.openH i j := by
    intro hr
    have hperp := hR.2 hr
    calc
      A.openH i jt = (A.cell ir jt).state.west := hT.1
      _ = (A.cell ir j).state.west := hperp.1.symm
      _ = A.openH i j := hB.1.symm
  have tl : A.openH i jt = true → A.openV i j = A.openV ir j := by
    intro ht
    have hperp := hT.2 ht
    calc
      A.openV i j = (A.cell i jt).state.south := hL.1
      _ = (A.cell ir jt).state.south := hperp.1
      _ = A.openV ir j := hR.1.symm
  have lb : A.openV i j = true → A.openH i j = A.openH i jt := by
    intro hl
    have hperp := hL.2 hl
    exact hperp.2.1
  rcases hpair with ⟨hb, hr⟩ | ⟨hr, ht⟩ | ⟨ht, hl⟩ | ⟨hl, hb⟩
  · have hl : A.openV i j = true := by rw [← br hb]; exact hr
    have ht : A.openH i jt = true := by rw [rt hr]; exact hb
    exact ⟨hb, hr, ht, hl⟩
  · have hb : A.openH i j = true := by rw [← rt hr]; exact ht
    have hl : A.openV i j = true := by rw [← br hb]; exact hr
    exact ⟨hb, hr, ht, hl⟩
  · have hr : A.openV ir j = true := by rw [← tl ht]; exact hl
    have hb : A.openH i j = true := by rw [← rt hr]; exact ht
    exact ⟨hb, hr, ht, hl⟩
  · have ht : A.openH i jt = true := by rw [← lb hl]; exact hb
    have hr : A.openV ir j = true := by rw [← tl ht]; exact hl
    exact ⟨hb, hr, ht, hl⟩

end
end PakFixedPolyomino
