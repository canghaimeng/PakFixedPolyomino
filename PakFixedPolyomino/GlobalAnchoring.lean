import PakFixedPolyomino.AnchoredRow

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 1600000

/-- A carrier covering macro-corner `(i,j)` cannot start in an earlier physical
row once row `j-1` has already been anchored. -/
theorem exclude_below_macro_row
    (P : RegisterParams) {n : ℕ} (hn : 0 < n) (i j : ℕ)
    (η : MacroState) (u : Fin P.tileCount) (l : AmpRecord P η) (v : Cell)
    (Dprev : Fin n → CarrierDatum P)
    (hcontained : translate (carrier P η u l) v ⊆ square (P.pitch * n))
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v)
    (hdis : 0 < j → Disjoint (anchoredRowUnion P (j - 1) Dprev)
      (translate (carrier P η u l) v)) :
    ¬ v.2 < ((j * P.pitch : ℕ) : ℤ) := by
  intro hvBelow
  have hb := carrier_origin_bounds P n i j η u l v hcontained hcorner
  by_cases hj : j = 0
  · subst j
    norm_num at hvBelow
    omega
  · have hjPos : 0 < j := Nat.pos_of_ne_zero hj
    have hvx0 : 0 ≤ v.1 := hb.1
    have hvy0 : 0 ≤ v.2 := hb.2.2.1
    obtain ⟨X, hX⟩ := Int.eq_ofNat_of_zero_le hvx0
    obtain ⟨Y, hY⟩ := Int.eq_ofNat_of_zero_le hvy0
    have hjDecomp : j - 1 + 1 = j := Nat.sub_add_cancel hjPos
    let yrel := Y - (j - 1) * P.pitch
    have hYlower : (j - 1) * P.pitch ≤ Y := by
      have hlow := hb.2.2.2.2.2.2.1
      have hjMul : j * P.pitch = (j - 1) * P.pitch + P.pitch := by
        calc
          j * P.pitch = (j - 1 + 1) * P.pitch := by rw [hjDecomp]
          _ = _ := by rw [Nat.add_mul, one_mul]
      have hjMulZ : (j : ℤ) * P.pitch = (j - 1 : ℕ) * P.pitch + P.pitch := by
        exact_mod_cast hjMul
      push_cast at hlow
      rw [hY, hjMulZ] at hlow
      have hz : (((j - 1) * P.pitch : ℕ) : ℤ) ≤ (Y : ℤ) := by
        push_cast
        omega
      exact_mod_cast hz
    have hyrel : yrel < P.pitch := by
      dsimp [yrel]
      push_cast at hvBelow
      rw [hY] at hvBelow
      have hjMul : j * P.pitch = (j - 1) * P.pitch + P.pitch := by
        calc
          j * P.pitch = (j - 1 + 1) * P.pitch := by rw [hjDecomp]
          _ = _ := by rw [Nat.add_mul, one_mul]
      omega
    have hYsplit : (j - 1) * P.pitch + yrel = Y := by
      dsimp [yrel]
      exact Nat.add_sub_of_le hYlower
    have hthree : X + 2 < n * P.pitch := by
      have hp2 : ((2 : ℤ), (0 : ℤ)) ∈ carrier P η u l :=
        inner_col_mem_carrier P η u l
          (lt_of_lt_of_le (by decide : 0 < 68) P.pitch_ge_sixty_eight) (Or.inr rfl)
      have hm : (((X + 2 : ℕ) : ℤ), (Y : ℤ)) ∈
          translate (carrier P η u l) v := by
        apply Finset.mem_image.mpr
        refine ⟨(2, 0), hp2, ?_⟩
        apply Prod.ext <;> norm_num <;> push_cast <;> omega
      have hs := mem_square_coord_bounds (hcontained hm)
      have hxBound := hs.2.1
      have hz : ((X + 2 : ℕ) : ℤ) < ((n * P.pitch : ℕ) : ℤ) := by
        simpa [Nat.mul_comm] using hxBound
      exact_mod_cast hz
    have hold := anchoredRow_no_three_gap P hn (j - 1) yrel X hyrel hthree Dprev
    have hnew0 : ((X : ℤ), (Y : ℤ)) ∈ translate (carrier P η u l) v := by
      apply Finset.mem_image.mpr
      refine ⟨(0, 0), origin_mem_carrier P η u l, ?_⟩
      apply Prod.ext <;> simp [hX, hY]
    have hnew1 : (((X + 1 : ℕ) : ℤ), (Y : ℤ)) ∈
        translate (carrier P η u l) v := by
      have hm := inner_col_mem_carrier P η u l
        (lt_of_lt_of_le (by decide : 0 < 68) P.pitch_ge_sixty_eight) (Or.inl rfl)
      apply Finset.mem_image.mpr
      refine ⟨(1, 0), hm, ?_⟩
      apply Prod.ext <;> norm_num <;> push_cast <;> omega
    have hnew2 : (((X + 2 : ℕ) : ℤ), (Y : ℤ)) ∈
        translate (carrier P η u l) v := by
      have hm := inner_col_mem_carrier P η u l
        (lt_of_lt_of_le (by decide : 0 < 68) P.pitch_ge_sixty_eight) (Or.inr rfl)
      apply Finset.mem_image.mpr
      refine ⟨(2, 0), hm, ?_⟩
      apply Prod.ext <;> norm_num <;> push_cast <;> omega
    have hyGlobal : ((j - 1) * P.pitch + yrel : ℕ) = Y := hYsplit
    have hd := Finset.disjoint_left.mp (hdis hjPos)
    rcases hold with h0 | h1 | h2
    · apply hd h0
      simpa [hyGlobal] using hnew0
    · apply hd h1
      simpa [hyGlobal] using hnew1
    · apply hd h2
      simpa [hyGlobal] using hnew2

/-- Once the vertical origin is fixed, the carrier cannot start to the left of
its macro-column: its three intact cells in relative column zero would meet the
already anchored left carrier by local column NG3. -/
theorem exclude_left_macro_col
    (P : RegisterParams) {n : ℕ} (i j : ℕ)
    (η ηL : MacroState) (u uL : Fin P.tileCount)
    (l : AmpRecord P η) (lL : AmpRecord P ηL) (v : Cell)
    (hcontained : translate (carrier P η u l) v ⊆ square (P.pitch * n))
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v)
    (hvy : v.2 = ((j * P.pitch : ℕ) : ℤ))
    (hleft : 0 < i → Disjoint
      (translate (carrier P ηL uL lL)
        ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)))
      (translate (carrier P η u l) v)) :
    ¬ v.1 < ((i * P.pitch : ℕ) : ℤ) := by
  intro hvLeft
  have hb := carrier_origin_bounds P n i j η u l v hcontained hcorner
  by_cases hi : i = 0
  · subst i
    norm_num at hvLeft
    omega
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi
    have hvx0 : 0 ≤ v.1 := hb.1
    obtain ⟨X, hX⟩ := Int.eq_ofNat_of_zero_le hvx0
    have hiDec : i - 1 + 1 = i := Nat.sub_add_cancel hiPos
    have hiMul : i * P.pitch = (i - 1) * P.pitch + P.pitch := by
      calc
        i * P.pitch = (i - 1 + 1) * P.pitch := by rw [hiDec]
        _ = _ := by rw [Nat.add_mul, one_mul]
    let xrel := X - (i - 1) * P.pitch
    have hXlower : (i - 1) * P.pitch ≤ X := by
      have hlow := hb.2.2.2.2.2.1
      have hiMulZ : (i : ℤ) * P.pitch = (i - 1 : ℕ) * P.pitch + P.pitch := by
        exact_mod_cast hiMul
      rw [hX] at hlow
      push_cast at hlow
      rw [hiMulZ] at hlow
      have hz : (((i - 1) * P.pitch : ℕ) : ℤ) ≤ (X : ℤ) := by
        push_cast
        omega
      exact_mod_cast hz
    have hxrel : xrel < P.pitch := by
      dsimp [xrel]
      rw [hX] at hvLeft
      have hiMulZ : ((i * P.pitch : ℕ) : ℤ) =
          (((i - 1) * P.pitch + P.pitch : ℕ) : ℤ) := by exact_mod_cast hiMul
      rw [hiMulZ] at hvLeft
      apply Nat.sub_lt_iff_lt_add hXlower |>.2
      have : X < (i - 1) * P.pitch + P.pitch := by exact_mod_cast hvLeft
      simpa [Nat.add_comm] using this
    have hXsplit : (i - 1) * P.pitch + xrel = X := Nat.add_sub_of_le hXlower
    have hXsplitZ :
        (((i - 1) * P.pitch : ℕ) : ℤ) + (xrel : ℤ) = (X : ℤ) := by
      exact_mod_cast hXsplit
    have hlocal := carrier_no_three_gap_col P ηL uL lL hxrel
      (show 0 + 2 < P.pitch by exact lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight)
    have new0 : ((X : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
        translate (carrier P η u l) v := by
      apply Finset.mem_image.mpr
      refine ⟨(0, 0), origin_mem_carrier P η u l, ?_⟩
      apply Prod.ext
      · simpa using hX
      · simpa using hvy
    have new1 : ((X : ℤ), ((j * P.pitch + 1 : ℕ) : ℤ)) ∈
        translate (carrier P η u l) v := by
      have hm := inner_row_mem_carrier P η u l
        (lt_of_lt_of_le (by decide : 0 < 68) P.pitch_ge_sixty_eight) (Or.inl rfl)
      apply Finset.mem_image.mpr
      refine ⟨(0, 1), hm, ?_⟩
      apply Prod.ext <;> norm_num <;> push_cast <;> omega
    have new2 : ((X : ℤ), ((j * P.pitch + 2 : ℕ) : ℤ)) ∈
        translate (carrier P η u l) v := by
      have hm := inner_row_mem_carrier P η u l
        (lt_of_lt_of_le (by decide : 0 < 68) P.pitch_ge_sixty_eight) (Or.inr rfl)
      apply Finset.mem_image.mpr
      refine ⟨(0, 2), hm, ?_⟩
      apply Prod.ext <;> norm_num <;> push_cast <;> omega
    have hd := Finset.disjoint_left.mp (hleft hiPos)
    rcases hlocal with h0 | h1 | h2
    · have old0 : ((X : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
          translate (carrier P ηL uL lL)
            ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) := by
        apply Finset.mem_image.mpr
        refine ⟨((xrel : ℤ), (0 : ℤ)), h0, ?_⟩
        apply Prod.ext
        · simpa [add_comm, add_left_comm, add_assoc] using hXsplitZ
        · norm_num
      exact hd old0 new0
    · have old1 : ((X : ℤ), ((j * P.pitch + 1 : ℕ) : ℤ)) ∈
          translate (carrier P ηL uL lL)
            ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) := by
        apply Finset.mem_image.mpr
        refine ⟨((xrel : ℤ), (1 : ℤ)), h1, ?_⟩
        apply Prod.ext
        · simpa [add_comm, add_left_comm, add_assoc] using hXsplitZ
        · norm_num [add_comm]
      exact hd old1 new1
    · have old2 : ((X : ℤ), ((j * P.pitch + 2 : ℕ) : ℤ)) ∈
          translate (carrier P ηL uL lL)
            ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) := by
        apply Finset.mem_image.mpr
        refine ⟨((xrel : ℤ), (2 : ℤ)), h2, ?_⟩
        apply Prod.ext
        · simpa [add_comm, add_left_comm, add_assoc] using hXsplitZ
        · norm_num [add_comm]
      exact hd old2 new2

/-- With the row already fixed, a one-column right shift would require a west
bump at tangential coordinate zero, contradicting its positive handshake. -/
theorem exclude_right_shift
    (P : RegisterParams) (i j : ℕ)
    (η : MacroState) (u : Fin P.tileCount) (l : AmpRecord P η) (v : Cell)
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v)
    (hvy : v.2 = ((j * P.pitch : ℕ) : ℤ)) :
    v.1 ≠ ((i * P.pitch : ℕ) : ℤ) + 1 := by
  intro hvx
  have hrel := mem_translate.mp hcorner
  have hmem : ((-1 : ℤ), (0 : ℤ)) ∈ carrier P η u l := by
    convert hrel using 1
    apply Prod.ext <;> dsimp <;> omega
  obtain ⟨_, hzero⟩ := carrier_west_outer_cell P η u l hmem
  have hh := P.handshake_eq
  have hpos := P.tileCount_pos
  omega

/-- The row-major anchoring step for a carrier.  Once the preceding macro-row
and (when present) the carrier immediately to the left are physically fixed,
any carrier covering the next macro-corner has exactly the prescribed origin.

This theorem is deliberately stated using actual translated finite supports
and `Finset.Disjoint`; no abstract placement or endpoint witness is hidden in
the conclusion. -/
theorem carrier_origin_exact
    (P : RegisterParams) {n : ℕ} (hn : 0 < n) (i j : ℕ)
    (η ηL : MacroState) (u uL : Fin P.tileCount)
    (l : AmpRecord P η) (lL : AmpRecord P ηL) (v : Cell)
    (Dprev : Fin n → CarrierDatum P)
    (hcontained : translate (carrier P η u l) v ⊆ square (P.pitch * n))
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v)
    (hprev : 0 < j → Disjoint (anchoredRowUnion P (j - 1) Dprev)
      (translate (carrier P η u l) v))
    (hleft : 0 < i → Disjoint
      (translate (carrier P ηL uL lL)
        ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)))
      (translate (carrier P η u l) v)) :
    v = (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) := by
  have hb := carrier_origin_bounds P n i j η u l v hcontained hcorner
  have hyvLower : ((j * P.pitch : ℕ) : ℤ) ≤ v.2 :=
    le_of_not_gt (exclude_below_macro_row P hn i j η u l v Dprev
      hcontained hcorner hprev)
  have hyvUpper : v.2 ≤ ((j * P.pitch : ℕ) : ℤ) + 1 := hb.2.2.2.2.2.2.2
  have hyvNot : v.2 ≠ ((j * P.pitch : ℕ) : ℤ) + 1 :=
    exclude_shifted_south_origin P n i j η ηL u uL l lL v
      hcontained hcorner hleft
  have hyv : v.2 = ((j * P.pitch : ℕ) : ℤ) := by omega
  have hvxLower : ((i * P.pitch : ℕ) : ℤ) ≤ v.1 :=
    le_of_not_gt (exclude_left_macro_col P i j η ηL u uL l lL v
      hcontained hcorner hyv hleft)
  have hvxUpper : v.1 ≤ ((i * P.pitch : ℕ) : ℤ) + 1 := hb.2.2.2.2.2.1
  have hvxNot : v.1 ≠ ((i * P.pitch : ℕ) : ℤ) + 1 :=
    exclude_right_shift P i j η u l v hcorner hyv
  apply Prod.ext
  · dsimp
    omega
  · dsimp
    omega

end
end PakFixedPolyomino
