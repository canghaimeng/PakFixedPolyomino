import PakFixedPolyomino.MacroGrid

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 1200000

def anchoredRowUnion (P : RegisterParams) {n : ℕ} (j : ℕ)
    (D : Fin n → CarrierDatum P) : Polyomino :=
  Finset.univ.biUnion fun i =>
    translate (CarrierDatum.support P (D i))
      (((i.1 * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ))

theorem mem_anchoredRowUnion (P : RegisterParams) {n j : ℕ}
    (D : Fin n → CarrierDatum P) (i : Fin n) {z : Cell}
    (hz : z ∈ translate (CarrierDatum.support P (D i))
      (((i.1 * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ))) :
    z ∈ anchoredRowUnion P j D := by
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩

/-- Concatenating locally NG3 carrier rows preserves NG3 across macro
interfaces because relative columns `P_s-2` and `1` are intact. -/
theorem anchoredRow_no_three_gap
    (P : RegisterParams) {n : ℕ} (hn : 0 < n) (j y x : ℕ)
    (hy : y < P.pitch) (hx : x + 2 < n * P.pitch)
    (D : Fin n → CarrierDatum P) :
    (((x : ℕ) : ℤ), ((j * P.pitch + y : ℕ) : ℤ)) ∈ anchoredRowUnion P j D ∨
    (((x + 1 : ℕ) : ℤ), ((j * P.pitch + y : ℕ) : ℤ)) ∈ anchoredRowUnion P j D ∨
    (((x + 2 : ℕ) : ℤ), ((j * P.pitch + y : ℕ) : ℤ)) ∈ anchoredRowUnion P j D := by
  have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  let q := x / P.pitch
  let r := x % P.pitch
  have hq : q < n := by
    apply (Nat.div_lt_iff_lt_mul hp0).2
    omega
  let qi : Fin n := ⟨q, hq⟩
  have hr : r < P.pitch := Nat.mod_lt x hp0
  have hxsplit : q * P.pitch + r = x := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod x P.pitch
  have hxsplitZ : ((q * P.pitch + r : ℕ) : ℤ) = (x : ℤ) := by
    exact_mod_cast hxsplit
  push_cast at hxsplitZ
  by_cases hinterior : r + 2 < P.pitch
  · let d := D qi
    have hlocal := carrier_no_three_gap_row P d.state d.tile d.labels hinterior hy
    rcases hlocal with h0 | h1 | h2
    · left
      apply mem_anchoredRowUnion P D qi
      apply Finset.mem_image.mpr
      refine ⟨((r : ℤ), (y : ℤ)), h0, ?_⟩
      apply Prod.ext <;> norm_num [qi] <;> push_cast <;> omega
    · right; left
      apply mem_anchoredRowUnion P D qi
      apply Finset.mem_image.mpr
      refine ⟨(((r + 1 : ℕ) : ℤ), (y : ℤ)), h1, ?_⟩
      apply Prod.ext <;> norm_num [qi] <;> push_cast <;> omega
    · right; right
      apply mem_anchoredRowUnion P D qi
      apply Finset.mem_image.mpr
      refine ⟨(((r + 2 : ℕ) : ℤ), (y : ℤ)), h2, ?_⟩
      apply Prod.ext <;> norm_num [qi] <;> push_cast <;> omega
  · have hrCases : r = P.pitch - 2 ∨ r = P.pitch - 1 := by omega
    rcases hrCases with hrE | hrE
    · left
      let d := D qi
      have hlocal := east_inner_column_mem_carrier P d.state d.tile d.labels hy
      apply mem_anchoredRowUnion P D qi
      apply Finset.mem_image.mpr
      refine ⟨(((P.pitch - 2 : ℕ) : ℤ), (y : ℤ)), hlocal, ?_⟩
      apply Prod.ext <;> norm_num [qi] <;> push_cast <;> omega
    · right; right
      have hqNext : q + 1 < n := by
        have hxLower : (q + 1) * P.pitch + 1 ≤ x + 2 := by
          rw [← hxsplit, hrE, Nat.add_mul]
          omega
        by_contra h
        have : n ≤ q + 1 := Nat.le_of_not_gt h
        have := Nat.mul_le_mul_right P.pitch this
        omega
      have hxNext : (q + 1) * P.pitch + 1 = x + 2 := by
        rw [← hxsplit, hrE, Nat.add_mul]
        omega
      have hxNextZ : (((q + 1) * P.pitch + 1 : ℕ) : ℤ) = ((x + 2 : ℕ) : ℤ) := by
        exact_mod_cast hxNext
      push_cast at hxNextZ
      let qn : Fin n := ⟨q + 1, hqNext⟩
      let d := D qn
      have hlocal := inner_col_mem_carrier P d.state d.tile d.labels hy (Or.inl rfl)
      apply mem_anchoredRowUnion P D qn
      apply Finset.mem_image.mpr
      refine ⟨((1 : ℤ), (y : ℤ)), hlocal, ?_⟩
      apply Prod.ext <;> norm_num [qn] <;> push_cast <;> omega

def anchoredColUnion (P : RegisterParams) {n : ℕ} (i : ℕ)
    (D : Fin n → CarrierDatum P) : Polyomino :=
  Finset.univ.biUnion fun j =>
    translate (CarrierDatum.support P (D j))
      (((i * P.pitch : ℕ) : ℤ), ((j.1 * P.pitch : ℕ) : ℤ))

theorem mem_anchoredColUnion (P : RegisterParams) {n i : ℕ}
    (D : Fin n → CarrierDatum P) (j : Fin n) {z : Cell}
    (hz : z ∈ translate (CarrierDatum.support P (D j))
      (((i * P.pitch : ℕ) : ℤ), ((j.1 * P.pitch : ℕ) : ℤ))) :
    z ∈ anchoredColUnion P i D :=
  Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hz⟩

theorem anchoredCol_no_three_gap
    (P : RegisterParams) {n : ℕ} (hn : 0 < n) (i x y : ℕ)
    (hx : x < P.pitch) (hy : y + 2 < n * P.pitch)
    (D : Fin n → CarrierDatum P) :
    (((i * P.pitch + x : ℕ) : ℤ), (y : ℤ)) ∈ anchoredColUnion P i D ∨
    (((i * P.pitch + x : ℕ) : ℤ), ((y + 1 : ℕ) : ℤ)) ∈ anchoredColUnion P i D ∨
    (((i * P.pitch + x : ℕ) : ℤ), ((y + 2 : ℕ) : ℤ)) ∈ anchoredColUnion P i D := by
  have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  let q := y / P.pitch
  let r := y % P.pitch
  have hq : q < n := (Nat.div_lt_iff_lt_mul hp0).2 (by omega)
  let qj : Fin n := ⟨q, hq⟩
  have hr : r < P.pitch := Nat.mod_lt y hp0
  have hysplit : q * P.pitch + r = y := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod y P.pitch
  have hysplitZ : (q : ℤ) * P.pitch + r = y := by exact_mod_cast hysplit
  by_cases hinterior : r + 2 < P.pitch
  · let d := D qj
    have hlocal := carrier_no_three_gap_col P d.state d.tile d.labels hx hinterior
    rcases hlocal with h0 | h1 | h2
    · left
      apply mem_anchoredColUnion P D qj
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), (r : ℤ)), h0, ?_⟩
      apply Prod.ext <;> norm_num [qj] <;> push_cast <;> omega
    · right; left
      apply mem_anchoredColUnion P D qj
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), ((r + 1 : ℕ) : ℤ)), h1, ?_⟩
      apply Prod.ext <;> norm_num [qj] <;> push_cast <;> omega
    · right; right
      apply mem_anchoredColUnion P D qj
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), ((r + 2 : ℕ) : ℤ)), h2, ?_⟩
      apply Prod.ext <;> norm_num [qj] <;> push_cast <;> omega
  · have hrCases : r = P.pitch - 2 ∨ r = P.pitch - 1 := by omega
    rcases hrCases with hrE | hrE
    · left
      let d := D qj
      have hlocal := north_inner_row_mem_carrier P d.state d.tile d.labels hx
      apply mem_anchoredColUnion P D qj
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), ((P.pitch - 2 : ℕ) : ℤ)), hlocal, ?_⟩
      apply Prod.ext <;> norm_num [qj] <;> push_cast <;> omega
    · right; right
      have hqNext : q + 1 < n := by
        have hyLower : (q + 1) * P.pitch + 1 ≤ y + 2 := by
          rw [← hysplit, hrE, Nat.add_mul]
          omega
        by_contra h
        have hle : n ≤ q + 1 := Nat.le_of_not_gt h
        have hmul := Nat.mul_le_mul_right P.pitch hle
        omega
      have hyNext : (q + 1) * P.pitch + 1 = y + 2 := by
        rw [← hysplit, hrE, Nat.add_mul]
        omega
      have hyNextZ : ((q + 1 : ℕ) : ℤ) * P.pitch + 1 = ((y + 2 : ℕ) : ℤ) := by
        exact_mod_cast hyNext
      let qn : Fin n := ⟨q + 1, hqNext⟩
      let d := D qn
      have hlocal := inner_row_mem_carrier P d.state d.tile d.labels hx (Or.inl rfl)
      apply mem_anchoredColUnion P D qn
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), (1 : ℤ)), hlocal, ?_⟩
      apply Prod.ext <;> norm_num [qn] <;> push_cast
      · omega
      · simpa [add_comm, add_left_comm, add_assoc] using hyNextZ

end
end PakFixedPolyomino
