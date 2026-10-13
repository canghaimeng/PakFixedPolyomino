import PakFixedPolyomino.TileSet

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 1600000

theorem mem_tileCavity_iff (P : RegisterParams) (u : Fin P.tileCount) (z : Cell) :
    z ∈ tileCavity u ↔
      z = (((16 + 4 * (u : ℕ) : ℕ) : ℤ), (17 : ℤ)) ∨
      z = (((17 + 4 * (u : ℕ) : ℕ) : ℤ), (16 : ℤ)) ∨
    z = (((17 + 4 * (u : ℕ) : ℕ) : ℤ), (17 : ℤ)) := by
  constructor
  · intro hz
    rw [tileCavity, cavity, mem_translate, mem_plugL] at hz
    rcases hz with h | h | h
    · left
      apply Prod.ext
      · have := congrArg Prod.fst h
        dsimp [cavityOrigin] at this ⊢
        omega
      · have := congrArg Prod.snd h
        dsimp [cavityOrigin] at this ⊢
        omega
    · right; left
      apply Prod.ext
      · have := congrArg Prod.fst h
        dsimp [cavityOrigin] at this ⊢
        omega
      · have := congrArg Prod.snd h
        dsimp [cavityOrigin] at this ⊢
        omega
    · right; right
      apply Prod.ext
      · have := congrArg Prod.fst h
        dsimp [cavityOrigin] at this ⊢
        omega
      · have := congrArg Prod.snd h
        dsimp [cavityOrigin] at this ⊢
        omega
  · rintro (rfl | rfl | rfl)
    all_goals rw [tileCavity, cavity, mem_translate, mem_plugL]
    · left; apply Prod.ext <;> norm_num [cavityOrigin] <;> omega
    · right; left; apply Prod.ext <;> norm_num [cavityOrigin] <;> omega
    · right; right; apply Prod.ext <;> norm_num [cavityOrigin] <;> omega

theorem mem_dents_cases
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {z : Cell} (hz : z ∈ dents P η u l) :
    z = ((0 : ℤ), (codeH P η.south η.north (P.west u) l.west : ℤ)) ∨
    z = (((P.pitch - 1 : ℕ) : ℤ), (P.handshake : ℤ)) ∨
    z = ((codeV P η.west η.east (P.south u) l.south : ℤ), (0 : ℤ)) ∨
    z = ((P.handshake : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) := by
  rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩
  cases d <;> simp [dentCell]

theorem mem_removed_cases
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {z : Cell}
    (hz : z ∈ dents P η u l ∪ tileCavity u) :
    z = ((0 : ℤ), (codeH P η.south η.north (P.west u) l.west : ℤ)) ∨
    z = (((P.pitch - 1 : ℕ) : ℤ), (P.handshake : ℤ)) ∨
    z = ((codeV P η.west η.east (P.south u) l.south : ℤ), (0 : ℤ)) ∨
    z = ((P.handshake : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) ∨
    z = (((16 + 4 * (u : ℕ) : ℕ) : ℤ), (17 : ℤ)) ∨
    z = (((17 + 4 * (u : ℕ) : ℕ) : ℤ), (16 : ℤ)) ∨
    z = (((17 + 4 * (u : ℕ) : ℕ) : ℤ), (17 : ℤ)) := by
  rcases Finset.mem_union.mp hz with hd | hc
  · rcases mem_dents_cases P η u l hd with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases (mem_tileCavity_iff P u _).mp hc with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- No physical row of one carrier body has three consecutive missing cells.
This is the local `NG3` invariant used by the anchoring induction. -/
theorem carrier_no_three_gap_row
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x y : ℕ}
    (hx : x + 2 < P.pitch) (hy : y < P.pitch) :
    ((x : ℤ), (y : ℤ)) ∈ carrier P η u l ∨
    (((x + 1 : ℕ) : ℤ), (y : ℤ)) ∈ carrier P η u l ∨
    (((x + 2 : ℕ) : ℤ), (y : ℤ)) ∈ carrier P η u l := by
  by_contra hnone
  push_neg at hnone
  have removed (k : ℕ) (hk : k ≤ 2) :
      (((x + k : ℕ) : ℤ), (y : ℤ)) ∈ dents P η u l ∪ tileCavity u := by
    by_contra hr
    have hb : (((x + k : ℕ) : ℤ), (y : ℤ)) ∈ square P.pitch :=
      ofNat_pair_mem_square.mpr ⟨by omega, hy⟩
    have hc : (((x + k : ℕ) : ℤ), (y : ℤ)) ∈ carrier P η u l := by
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hb, hr⟩)
    interval_cases k <;> simp_all
  have h0 := mem_removed_cases P η u l (removed 0 (by decide))
  have h1 := mem_removed_cases P η u l (removed 1 (by decide))
  have h2 := mem_removed_cases P η u l (removed 2 (by decide))
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hH := codeH_bounds P η.south η.north (P.west u) l.west
  have hV := codeV_bounds P η.west η.east (P.south u) l.south
  rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
  rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
  simp only [Prod.mk.injEq] at h0 h1 h2 <;> omega

theorem carrier_no_three_gap_col
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x y : ℕ}
    (hx : x < P.pitch) (hy : y + 2 < P.pitch) :
    ((x : ℤ), (y : ℤ)) ∈ carrier P η u l ∨
    ((x : ℤ), ((y + 1 : ℕ) : ℤ)) ∈ carrier P η u l ∨
    ((x : ℤ), ((y + 2 : ℕ) : ℤ)) ∈ carrier P η u l := by
  by_contra hnone
  push_neg at hnone
  have removed (k : ℕ) (hk : k ≤ 2) :
      ((x : ℤ), ((y + k : ℕ) : ℤ)) ∈ dents P η u l ∪ tileCavity u := by
    by_contra hr
    have hb : ((x : ℤ), ((y + k : ℕ) : ℤ)) ∈ square P.pitch :=
      ofNat_pair_mem_square.mpr ⟨hx, by omega⟩
    have hc : ((x : ℤ), ((y + k : ℕ) : ℤ)) ∈ carrier P η u l := by
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hb, hr⟩)
    interval_cases k <;> simp_all
  have h0 := mem_removed_cases P η u l (removed 0 (by decide))
  have h1 := mem_removed_cases P η u l (removed 1 (by decide))
  have h2 := mem_removed_cases P η u l (removed 2 (by decide))
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hH := codeH_bounds P η.south η.north (P.west u) l.west
  have hV := codeV_bounds P η.west η.east (P.south u) l.south
  rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
  rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
  simp only [Prod.mk.injEq] at h0 h1 h2 <;> omega

theorem topRight_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) :
    (((P.pitch - 1 : ℕ) : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide),
       Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide)⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      omega

/-- The southeast body corner is never one of the four register dents and is
far from the internal identity cavity. -/
theorem bottomRight_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) :
    (((P.pitch - 1 : ℕ) : ℤ), (0 : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide),
       lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      omega

/-- The northwest body corner is likewise intact. -/
theorem topLeft_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) :
    ((0 : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight,
       Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide)⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      omega

/-- Explicit physical overlap excluding a carrier whose south bump is shifted
one row above the next macro-corner. -/
theorem shifted_south_bump_overlap
    (P : RegisterParams) (i j : ℕ)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η') :
    ¬ Disjoint
      (translate (carrier P η u l)
        (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)))
      (translate (carrier P η' v l')
        (((i * P.pitch + 8 : ℕ) : ℤ), ((j * P.pitch + 1 : ℕ) : ℤ))) := by
  have hpitch := P.pitch_ge_sixty_eight
  rw [Finset.not_disjoint_iff]
  let w : Cell := (((i * P.pitch + 9 : ℕ) : ℤ), ((j * P.pitch + 2 : ℕ) : ℤ))
  refine ⟨w, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨((9 : ℤ), (2 : ℤ)),
      inner_row_mem_carrier P η u l
        (lt_of_lt_of_le (by decide : 9 < 68) hpitch) (Or.inr rfl), ?_⟩
    apply Prod.ext <;> norm_num [w] <;> push_cast <;> ring
  · apply Finset.mem_image.mpr
    refine ⟨((1 : ℤ), (1 : ℤ)),
      inner_row_mem_carrier P η' v l'
        (lt_of_lt_of_le (by decide : 1 < 68) hpitch) (Or.inl rfl), ?_⟩
    apply Prod.ext <;> norm_num [w] <;> push_cast <;> ring

/-- Exact origin bounds for a carrier contained in the large square and
covering the next macro-corner. -/
theorem carrier_origin_bounds
    (P : RegisterParams) (n i j : ℕ)
    (η : MacroState) (u : Fin P.tileCount) (l : AmpRecord P η)
    (v : Cell)
    (hcontained : translate (carrier P η u l) v ⊆ square (P.pitch * n))
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v) :
    0 ≤ v.1 ∧ v.1 + P.pitch ≤ P.pitch * n ∧
    0 ≤ v.2 ∧ v.2 + P.pitch ≤ P.pitch * n ∧
    (i * P.pitch : ℤ) - P.pitch ≤ v.1 ∧ v.1 ≤ (i * P.pitch : ℤ) + 1 ∧
    (j * P.pitch : ℤ) - P.pitch ≤ v.2 ∧ v.2 ≤ (j * P.pitch : ℤ) + 1 := by
  have horg : v ∈ translate (carrier P η u l) v := by
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), origin_mem_carrier P η u l, by ext <;> simp⟩
  have horgB := mem_square_coord_bounds (hcontained horg)
  have htop0 := topRight_mem_carrier P η u l
  have htop : (((P.pitch - 1 : ℕ) : ℤ) + v.1,
      ((P.pitch - 1 : ℕ) : ℤ) + v.2) ∈
      translate (carrier P η u l) v := Finset.mem_image.mpr ⟨_, htop0, rfl⟩
  have htopB := mem_square_coord_bounds (hcontained htop)
  have hrel := mem_translate.mp hcorner
  have hbox := carrier_subset_extendedBox P η u l hrel
  have hboxX := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).1
  have hboxY := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2
  have hp := P.pitch_ge_sixty_eight
  push_cast at htopB hboxX hboxY
  omega

/-- The three and only three PlugL translations that can cover a prescribed
macro-corner. -/
theorem plug_cover_corner_cases
    (P : RegisterParams) (i j : ℕ) (t : Cell)
    (h : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈ translate plugL t) :
    t = (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ) - 1) ∨
    t = (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ)) ∨
    t = (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ) - 1) := by
  rw [mem_translate, mem_plugL] at h
  rcases h with h | h | h
  · left
    apply Prod.ext
    · have := congrArg Prod.fst h
      dsimp at this ⊢
      omega
    · have := congrArg Prod.snd h
      dsimp at this ⊢
      omega
  · right; left
    apply Prod.ext
    · have := congrArg Prod.fst h
      dsimp at this ⊢
      omega
    · have := congrArg Prod.snd h
      dsimp at this ⊢
      omega
  · right; right
    apply Prod.ext
    · have := congrArg Prod.fst h
      dsimp at this ⊢
      omega
    · have := congrArg Prod.snd h
      dsimp at this ⊢
      omega

theorem plug_first_case_neighbour
    (P : RegisterParams) (i j : ℕ) :
    (((i * P.pitch : ℕ) : ℤ) + 1, ((j * P.pitch : ℕ) : ℤ) - 1) ∈
      translate plugL (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ) - 1) := by
  apply Finset.mem_image.mpr
  refine ⟨(1, 0), by simp [plugL], ?_⟩
  apply Prod.ext <;> simp <;> ring

theorem plug_second_case_neighbour
    (P : RegisterParams) (i j : ℕ) :
    (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ) + 1) ∈
      translate plugL (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ)) := by
  apply Finset.mem_image.mpr
  refine ⟨(0, 1), by simp [plugL], ?_⟩
  apply Prod.ext <;> simp <;> ring

theorem plug_third_case_neighbour
    (P : RegisterParams) (i j : ℕ) :
    (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ)) ∈
      translate plugL
        (((i * P.pitch : ℕ) : ℤ) - 1, ((j * P.pitch : ℕ) : ℤ) - 1) := by
  apply Finset.mem_image.mpr
  refine ⟨(0, 1), by simp [plugL], ?_⟩
  apply Prod.ext <;> simp <;> ring

/-- The `b = j P_s + 1` alternative in the row-major origin bounds is
impossible: the south bump forces the explicit overlap cell `(9,2)` with the
already anchored left carrier. -/
theorem exclude_shifted_south_origin
    (P : RegisterParams) (n i j : ℕ)
    (η ηL : MacroState) (u uL : Fin P.tileCount)
    (l : AmpRecord P η) (lL : AmpRecord P ηL)
    (v : Cell)
    (hcontained : translate (carrier P η u l) v ⊆ square (P.pitch * n))
    (hcorner : (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)) ∈
      translate (carrier P η u l) v)
    (hleft : 0 < i → Disjoint
      (translate (carrier P ηL uL lL)
        ((((i - 1) * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ)))
      (translate (carrier P η u l) v)) :
    v.2 ≠ ((j * P.pitch : ℕ) : ℤ) + 1 := by
  intro hv
  have hrel := mem_translate.mp hcorner
  have hrel' : (((i * P.pitch : ℕ) : ℤ) - v.1, (-1 : ℤ)) ∈ carrier P η u l := by
    convert hrel using 1
    apply Prod.ext
    · rfl
    · dsimp
      omega
  obtain ⟨_, hx⟩ := carrier_south_outer_cell P η u l hrel'
  have hvx : v.1 = ((i * P.pitch : ℕ) : ℤ) - P.handshake := by omega
  have hb := carrier_origin_bounds P n i j η u l v hcontained hcorner
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hhandPos : 0 < P.handshake := by omega
  by_cases hi : i = 0
  · subst i
    omega
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi
    have hiDecomp : i - 1 + 1 = i := Nat.sub_add_cancel hiPos
    have hiMul : i * P.pitch = (i - 1) * P.pitch + P.pitch := by
      calc
        i * P.pitch = (i - 1 + 1) * P.pitch := by rw [hiDecomp]
        _ = (i - 1) * P.pitch + P.pitch := by rw [Nat.add_mul, one_mul]
    have hhPitch : P.handshake = P.pitch - 8 := rfl
    have hvxNat : v.1 = ((((i - 1) * P.pitch + 8 : ℕ) : ℤ)) := by
      have hiMulZ : ((i * P.pitch : ℕ) : ℤ) =
          (((i - 1) * P.pitch + P.pitch : ℕ) : ℤ) := by exact_mod_cast hiMul
      push_cast at hiMulZ ⊢
      omega
    have hvEq : v =
        ((((i - 1) * P.pitch + 8 : ℕ) : ℤ), ((j * P.pitch + 1 : ℕ) : ℤ)) := by
      apply Prod.ext
      · exact hvxNat
      · push_cast
        omega
    have hd := hleft hiPos
    rw [hvEq] at hd
    exact shifted_south_bump_overlap P (i - 1) j ηL η uL u lL l hd

end
end PakFixedPolyomino
