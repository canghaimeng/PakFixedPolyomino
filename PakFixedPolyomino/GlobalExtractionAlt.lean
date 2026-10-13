import PakFixedPolyomino.GlobalAnchoring
import PakFixedPolyomino.Tiling

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 2000000

local instance (P : RegisterParams) : DecidableEq (RegisterTile P) :=
  Classical.decEq _

/-- The physical southwest corner of macro-cell `(i,j)`. -/
def macroCorner (P : RegisterParams) (i j : ℕ) : Cell :=
  (((i * P.pitch : ℕ) : ℤ), ((j * P.pitch : ℕ) : ℤ))

theorem macroCorner_mem_square (P : RegisterParams) {n : ℕ}
    (i j : Fin n) : macroCorner P i.1 j.1 ∈ square (P.pitch * n) := by
  apply ofNat_pair_mem_square.mpr
  have hp : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  constructor
  · simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right i.isLt hp
  · simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right j.isLt hp

/-- A canonical occurrence covering each macro-corner.  No geometric
conclusion is built into this choice. -/
def cornerPlacement (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) : Placement (RegisterTile P) :=
  Classical.choose (T.every_cell_covered (macroCorner_mem_square P i j))

theorem cornerPlacement_mem (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) : cornerPlacement P T i j ∈ T.placements :=
  (Classical.choose_spec
    (T.every_cell_covered (macroCorner_mem_square P i j))).1

theorem cornerPlacement_covers (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) :
    macroCorner P i.1 j.1 ∈
      Placement.cells (registerTileSupport P) (cornerPlacement P T i j) :=
  (Classical.choose_spec
    (T.every_cell_covered (macroCorner_mem_square P i j))).2

/-- The occurrence selected at a macro-corner is a carrier with the stated
physical origin. -/
def IsAnchoredCorner (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) : Prop :=
  ∃ d : CarrierDatum P,
    (cornerPlacement P T i j).tile =
      some ⟨d.state, d.tile, d.labels⟩ ∧
    (cornerPlacement P T i j).shift = macroCorner P i.1 j.1

theorem west_top_mem_carrier (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (l : AmpRecord P η) :
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
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      have hHL := codeH_lt_handshake P η.south η.north (P.west u) l.west
      have hVL := codeV_lt_handshake P η.west η.east (P.south u) l.south
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hHfar : codeH P η.south η.north (P.west u) l.west < P.pitch - 1 := by
        omega
      have hVfar : codeV P η.west η.east (P.south u) l.south < P.pitch - 1 := by
        omega
      have hhfar : P.handshake < P.pitch - 1 := by omega
      have hp1 : 0 < P.pitch - 1 := by omega
      have hHfarZ : (codeH P η.south η.north (P.west u) l.west : ℤ) <
          ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hHfar
      have hVfarZ : (codeV P η.west η.east (P.south u) l.south : ℤ) <
          ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hVfar
      have hhfarZ : (P.handshake : ℤ) < ((P.pitch - 1 : ℕ) : ℤ) := by
        exact_mod_cast hhfar
      have hp1Z : (0 : ℤ) < ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hp1
      cases d <;>
        have hx := congrArg Prod.fst heq <;>
        have hy := congrArg Prod.snd heq <;>
        dsimp [dentCell] at hx hy <;> omega
    · have hb := tileCavity_bounds hc
      have hp := P.pitch_ge_sixty_eight
      have : (16 : ℤ) ≤ 0 := by simpa using hb.1
      omega

theorem east_bottom_mem_carrier (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (l : AmpRecord P η) :
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
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      have hHL := codeH_lt_handshake P η.south η.north (P.west u) l.west
      have hVL := codeV_lt_handshake P η.west η.east (P.south u) l.south
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hHfar : codeH P η.south η.north (P.west u) l.west < P.pitch - 1 := by
        omega
      have hVfar : codeV P η.west η.east (P.south u) l.south < P.pitch - 1 := by
        omega
      have hhfar : P.handshake < P.pitch - 1 := by omega
      have hp1 : 0 < P.pitch - 1 := by omega
      have hHfarZ : (codeH P η.south η.north (P.west u) l.west : ℤ) <
          ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hHfar
      have hVfarZ : (codeV P η.west η.east (P.south u) l.south : ℤ) <
          ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hVfar
      have hhfarZ : (P.handshake : ℤ) < ((P.pitch - 1 : ℕ) : ℤ) := by
        exact_mod_cast hhfar
      have hp1Z : (0 : ℤ) < ((P.pitch - 1 : ℕ) : ℤ) := by exact_mod_cast hp1
      cases d <;>
        have hx := congrArg Prod.fst heq <;>
        have hy := congrArg Prod.snd heq <;>
        dsimp [dentCell] at hx hy <;> omega
    · have hb := tileCavity_bounds hc
      rcases hb.2.2 with h | h <;> norm_num at h

/-- An aligned carrier cannot also cover a strictly later row-major
macro-corner.  This is the occurrence-distinctness guard needed before using
the tiling's pairwise-disjointness field. -/
theorem aligned_carrier_not_later_corner
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {i₀ j₀ i j : ℕ}
    (hbefore : j₀ < j ∨ (j₀ = j ∧ i₀ < i)) :
    macroCorner P i j ∉
      translate (carrier P η u l) (macroCorner P i₀ j₀) := by
  intro hm
  have hr := mem_translate.mp hm
  have hb := carrier_subset_extendedBox P η u l hr
  have hbx := Finset.mem_Icc.mp (Finset.mem_product.mp hb).1
  have hby := Finset.mem_Icc.mp (Finset.mem_product.mp hb).2
  have hp : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  simp only [macroCorner] at hr hbx hby
  push_cast at hr hbx hby
  rcases hbefore with hj | ⟨rfl, hi⟩
  · have hjstep : j₀ + 1 ≤ j := Nat.succ_le_iff.mpr hj
    have hjmul : j₀ * P.pitch + P.pitch ≤ j * P.pitch := by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hjstep
    have hjmulZ : ((j₀ * P.pitch : ℕ) : ℤ) + P.pitch ≤
        ((j * P.pitch : ℕ) : ℤ) := by exact_mod_cast hjmul
    have hjEq : j = j₀ + 1 := by
      have hupperZ : ((j * P.pitch : ℕ) : ℤ) ≤
          ((j₀ * P.pitch : ℕ) : ℤ) + P.pitch := by omega
      have hupper : j * P.pitch ≤ (j₀ + 1) * P.pitch := by
        have : j * P.pitch ≤ j₀ * P.pitch + P.pitch := by exact_mod_cast hupperZ
        simpa [Nat.add_mul] using this
      have hjle : j ≤ j₀ + 1 := Nat.le_of_mul_le_mul_right hupper hp
      omega
    have hix : i = i₀ ∨ i = i₀ + 1 := by
      by_cases hle : i₀ ≤ i
      · have hupperZ : ((i * P.pitch : ℕ) : ℤ) ≤
            ((i₀ * P.pitch : ℕ) : ℤ) + P.pitch := by omega
        have hupper : i * P.pitch ≤ (i₀ + 1) * P.pitch := by
          have : i * P.pitch ≤ i₀ * P.pitch + P.pitch := by exact_mod_cast hupperZ
          simpa [Nat.add_mul] using this
        have : i ≤ i₀ + 1 := Nat.le_of_mul_le_mul_right hupper hp
        omega
      · have hlt : i < i₀ := Nat.lt_of_not_ge hle
        have hstep : i + 1 ≤ i₀ := Nat.succ_le_iff.mpr hlt
        have hn : i * P.pitch + P.pitch ≤ i₀ * P.pitch := by
          simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hstep
        have hnZ : ((i * P.pitch : ℕ) : ℤ) + P.pitch ≤
            ((i₀ * P.pitch : ℕ) : ℤ) := by exact_mod_cast hn
        push_cast at hnZ
        have hpZ : (67 : ℤ) < P.pitch := by exact_mod_cast P.pitch_ge_sixty_eight
        omega
    rcases hix with rfl | rfl
    · have hrel : (0, (P.pitch : ℤ)) ∈ carrier P η u l := by
        convert hr using 1 <;> ext <;> simp [hjEq] <;> push_cast <;> ring
      rcases Finset.mem_union.mp hrel with hs | hbump
      · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hs).1
        omega
      · rcases Finset.mem_image.mp hbump with ⟨d, _, hd⟩
        have hV := codeV_bounds P η.west η.east (P.north u) l.north
        have hh := P.handshake_eq
        cases d <;> simp [bumpCell] at hd <;> omega
    · have hrel : ((P.pitch : ℤ), (P.pitch : ℤ)) ∈ carrier P η u l := by
        convert hr using 1 <;> ext <;> simp [hjEq] <;> push_cast <;> ring
      exact carrier_not_far_corner P η u l hrel
  · have histep : i₀ + 1 ≤ i := Nat.succ_le_iff.mpr hi
    have himul : i₀ * P.pitch + P.pitch ≤ i * P.pitch := by
      simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch histep
    have himulZ : ((i₀ * P.pitch : ℕ) : ℤ) + P.pitch ≤
        ((i * P.pitch : ℕ) : ℤ) := by exact_mod_cast himul
    have hiEq : i = i₀ + 1 := by
      have hupperZ : ((i * P.pitch : ℕ) : ℤ) ≤
          ((i₀ * P.pitch : ℕ) : ℤ) + P.pitch := by omega
      have hupper : i * P.pitch ≤ (i₀ + 1) * P.pitch := by
        have : i * P.pitch ≤ i₀ * P.pitch + P.pitch := by exact_mod_cast hupperZ
        simpa [Nat.add_mul] using this
      have hile : i ≤ i₀ + 1 := Nat.le_of_mul_le_mul_right hupper hp
      omega
    have hrel : ((P.pitch : ℤ), 0) ∈ carrier P η u l := by
      convert hr using 1 <;> ext <;> simp [hiEq] <;> push_cast <;> ring
    rcases Finset.mem_union.mp hrel with hs | hbump
    · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hs).1
      omega
    · rcases Finset.mem_image.mp hbump with ⟨d, _, hd⟩
      have hH := codeH_bounds P η.south η.north (P.east u) l.east
      have hh := P.handshake_eq
      cases d <;> simp [bumpCell] at hd <;> omega

def rowMajorRank (n i j : ℕ) : ℕ := j * n + i

theorem registerTile_some_carrierDatum (P : RegisterParams)
    {t : RegisterTile P} (h : t ≠ none) :
    ∃ d : CarrierDatum P, t = some ⟨d.state, d.tile, d.labels⟩ := by
  rcases t with _ | ⟨η, u, l⟩
  · exact (h rfl).elim
  · exact ⟨⟨η, u, l⟩, rfl⟩

private theorem prior_row_rank_lt {n : ℕ} (i j : Fin n) (hj : 0 < j.1) :
    rowMajorRank n i.1 (j.1 - 1) < rowMajorRank n i.1 j.1 := by
  have hjEq : j.1 - 1 + 1 = j.1 := Nat.sub_add_cancel hj
  have hi := i.isLt
  unfold rowMajorRank
  conv_rhs => rw [← hjEq]
  rw [Nat.add_mul]
  omega

private theorem prior_any_row_rank_lt {n : ℕ} (i j k : Fin n) (hj : 0 < j.1) :
    rowMajorRank n k.1 (j.1 - 1) < rowMajorRank n i.1 j.1 := by
  have hjEq : j.1 - 1 + 1 = j.1 := Nat.sub_add_cancel hj
  have hk := k.isLt
  unfold rowMajorRank
  conv_rhs => rw [← hjEq]
  rw [Nat.add_mul]
  omega

private theorem prior_col_rank_lt {n : ℕ} (i j : Fin n) (hi : 0 < i.1) :
    rowMajorRank n (i.1 - 1) j.1 < rowMajorRank n i.1 j.1 := by
  unfold rowMajorRank
  omega

/-- Before the anchoring theorem is invoked, PlugL is excluded using an
actual outside-square cell on the south/west boundary, or an actual overlap
with the already anchored carrier immediately below/to the left. -/
theorem cornerPlacement_ne_plug_of_prior
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n)
    (hprior : ∀ (i' j' : Fin n),
      rowMajorRank n i'.1 j'.1 < rowMajorRank n i.1 j.1 →
      IsAnchoredCorner P T i' j') :
    (cornerPlacement P T i j).tile ≠ none := by
  intro hplug
  let p := cornerPlacement P T i j
  have hpMem : p ∈ T.placements := cornerPlacement_mem P T i j
  have hpCorner : macroCorner P i.1 j.1 ∈
      Placement.cells (registerTileSupport P) p := cornerPlacement_covers P T i j
  have hpCornerPlug : macroCorner P i.1 j.1 ∈ translate plugL p.shift := by
    simpa [p, Placement.cells, registerTileSupport, hplug] using hpCorner
  rcases plug_cover_corner_cases P i.1 j.1 p.shift hpCornerPlug with
      hsouth | hwest | hdiag
  · have hnew := plug_first_case_neighbour P i.1 j.1
    have hnewP :
        (((i.1 * P.pitch : ℕ) : ℤ) + 1,
          ((j.1 * P.pitch : ℕ) : ℤ) - 1) ∈
          Placement.cells (registerTileSupport P) p := by
      simpa [p, Placement.cells, registerTileSupport, hplug, hsouth] using hnew
    by_cases hj0 : j.1 = 0
    · have hs := T.placement_subset hpMem hnewP
      have hb := mem_square_coord_bounds hs
      have hnonneg := hb.2.2.1
      rw [hj0] at hnonneg
      norm_num at hnonneg
    · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj0
      let jp : Fin n := ⟨j.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
      obtain ⟨d, hdtile, hdshift⟩ :=
        hprior i jp (prior_row_rank_lt i j hjpos)
      let q := cornerPlacement P T i jp
      have hqMem : q ∈ T.placements := cornerPlacement_mem P T i jp
      have hpq : q ≠ p := by
        intro heq
        have ht := congrArg Placement.tile heq
        dsimp [q, p] at ht
        rw [hdtile, hplug] at ht
        contradiction
      have holdLocal : ((1 : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) ∈
          carrier P d.state d.tile d.labels :=
        inner_col_mem_carrier P d.state d.tile d.labels
          (Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide))
          (Or.inl rfl)
      have hold :
          (((i.1 * P.pitch : ℕ) : ℤ) + 1,
            ((j.1 * P.pitch : ℕ) : ℤ) - 1) ∈
          Placement.cells (registerTileSupport P) q := by
        rw [Placement.cells, hdtile, registerTileSupport, hdshift]
        apply Finset.mem_image.mpr
        refine ⟨_, holdLocal, ?_⟩
        apply Prod.ext
        · simp [macroCorner, add_comm]
        · dsimp [jp, macroCorner]
          have hjEq : j.1 - 1 + 1 = j.1 := Nat.sub_add_cancel hjpos
          have hjMul : j.1 * P.pitch = (j.1 - 1) * P.pitch + P.pitch := by
            conv_lhs => rw [← hjEq]
            rw [Nat.add_mul, one_mul]
          have hjMulZ : ((j.1 * P.pitch : ℕ) : ℤ) =
              (((j.1 - 1) * P.pitch : ℕ) : ℤ) + P.pitch := by exact_mod_cast hjMul
          have hp1 : 1 ≤ P.pitch := le_trans (by decide) P.pitch_ge_sixty_eight
          have hpSub : ((P.pitch - 1 : ℕ) : ℤ) = (P.pitch : ℤ) - 1 := by
            rw [Nat.cast_sub hp1]
            norm_num
          omega
      exact Finset.disjoint_left.mp (T.disjoint hqMem hpMem hpq) hold hnewP
  · have hnew := plug_second_case_neighbour P i.1 j.1
    have hnewP :
        (((i.1 * P.pitch : ℕ) : ℤ) - 1,
          ((j.1 * P.pitch : ℕ) : ℤ) + 1) ∈
          Placement.cells (registerTileSupport P) p := by
      simpa [p, Placement.cells, registerTileSupport, hplug, hwest] using hnew
    by_cases hi0 : i.1 = 0
    · have hs := T.placement_subset hpMem hnewP
      have hb := mem_square_coord_bounds hs
      have hnonneg := hb.1
      rw [hi0] at hnonneg
      norm_num at hnonneg
    · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
      let ip : Fin n := ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      obtain ⟨d, hdtile, hdshift⟩ :=
        hprior ip j (prior_col_rank_lt i j hipos)
      let q := cornerPlacement P T ip j
      have hqMem : q ∈ T.placements := cornerPlacement_mem P T ip j
      have hpq : q ≠ p := by
        intro heq
        have ht := congrArg Placement.tile heq
        dsimp [q, p] at ht
        rw [hdtile, hplug] at ht
        contradiction
      have holdLocal : (((P.pitch - 1 : ℕ) : ℤ), (1 : ℤ)) ∈
          carrier P d.state d.tile d.labels :=
        inner_row_mem_carrier P d.state d.tile d.labels
          (Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide))
          (Or.inl rfl)
      have hold :
          (((i.1 * P.pitch : ℕ) : ℤ) - 1,
            ((j.1 * P.pitch : ℕ) : ℤ) + 1) ∈
          Placement.cells (registerTileSupport P) q := by
        rw [Placement.cells, hdtile, registerTileSupport, hdshift]
        apply Finset.mem_image.mpr
        refine ⟨_, holdLocal, ?_⟩
        apply Prod.ext
        · dsimp [ip, macroCorner]
          have hiEq : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel hipos
          have hiMul : i.1 * P.pitch = (i.1 - 1) * P.pitch + P.pitch := by
            conv_lhs => rw [← hiEq]
            rw [Nat.add_mul, one_mul]
          have hiMulZ : ((i.1 * P.pitch : ℕ) : ℤ) =
              (((i.1 - 1) * P.pitch : ℕ) : ℤ) + P.pitch := by exact_mod_cast hiMul
          have hp1 : 1 ≤ P.pitch := le_trans (by decide) P.pitch_ge_sixty_eight
          have hpSub : ((P.pitch - 1 : ℕ) : ℤ) = (P.pitch : ℤ) - 1 := by
            rw [Nat.cast_sub hp1]
            norm_num
          omega
        · simp [macroCorner, add_comm]
      exact Finset.disjoint_left.mp (T.disjoint hqMem hpMem hpq) hold hnewP
  · have hnew := plug_third_case_neighbour P i.1 j.1
    have hnewP :
        (((i.1 * P.pitch : ℕ) : ℤ) - 1,
          ((j.1 * P.pitch : ℕ) : ℤ)) ∈
          Placement.cells (registerTileSupport P) p := by
      simpa [p, Placement.cells, registerTileSupport, hplug, hdiag] using hnew
    by_cases hi0 : i.1 = 0
    · have hs := T.placement_subset hpMem hnewP
      have hb := mem_square_coord_bounds hs
      have hnonneg := hb.1
      rw [hi0] at hnonneg
      norm_num at hnonneg
    · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
      let ip : Fin n := ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      obtain ⟨d, hdtile, hdshift⟩ :=
        hprior ip j (prior_col_rank_lt i j hipos)
      let q := cornerPlacement P T ip j
      have hqMem : q ∈ T.placements := cornerPlacement_mem P T ip j
      have hpq : q ≠ p := by
        intro heq
        have ht := congrArg Placement.tile heq
        dsimp [q, p] at ht
        rw [hdtile, hplug] at ht
        contradiction
      have holdLocal := east_bottom_mem_carrier P d.state d.tile d.labels
      have hold :
          (((i.1 * P.pitch : ℕ) : ℤ) - 1,
            ((j.1 * P.pitch : ℕ) : ℤ)) ∈
          Placement.cells (registerTileSupport P) q := by
        rw [Placement.cells, hdtile, registerTileSupport, hdshift]
        apply Finset.mem_image.mpr
        refine ⟨_, holdLocal, ?_⟩
        apply Prod.ext
        · dsimp [ip, macroCorner]
          have hiEq : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel hipos
          have hiMul : i.1 * P.pitch = (i.1 - 1) * P.pitch + P.pitch := by
            conv_lhs => rw [← hiEq]
            rw [Nat.add_mul, one_mul]
          have hiMulZ : ((i.1 * P.pitch : ℕ) : ℤ) =
              (((i.1 - 1) * P.pitch : ℕ) : ℤ) + P.pitch := by exact_mod_cast hiMul
          have hp1 : 1 ≤ P.pitch := le_trans (by decide) P.pitch_ge_sixty_eight
          have hpSub : ((P.pitch - 1 : ℕ) : ℤ) = (P.pitch : ℤ) - 1 := by
            rw [Nat.cast_sub hp1]
            norm_num
          omega
        · simp [macroCorner]
      exact Finset.disjoint_left.mp (T.disjoint hqMem hpMem hpq) hold hnewP

def anchoredDatumOf (P : RegisterParams) {n : ℕ}
    {T : Tiling (registerTileSupport P) (square (P.pitch * n))}
    {i j : Fin n} (h : IsAnchoredCorner P T i j) : CarrierDatum P :=
  Classical.choose h

theorem anchoredDatumOf_spec (P : RegisterParams) {n : ℕ}
    {T : Tiling (registerTileSupport P) (square (P.pitch * n))}
    {i j : Fin n} (h : IsAnchoredCorner P T i j) :
    (cornerPlacement P T i j).tile =
        some ⟨(anchoredDatumOf P h).state,
          (anchoredDatumOf P h).tile, (anchoredDatumOf P h).labels⟩ ∧
      (cornerPlacement P T i j).shift = macroCorner P i.1 j.1 :=
  Classical.choose_spec h

theorem cornerPlacement_ne_of_anchored_before
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {i₀ j₀ i j : Fin n} (hbefore :
      j₀.1 < j.1 ∨ (j₀.1 = j.1 ∧ i₀.1 < i.1))
    (hA : IsAnchoredCorner P T i₀ j₀) :
    cornerPlacement P T i₀ j₀ ≠ cornerPlacement P T i j := by
  intro heq
  obtain ⟨d, htile, hshift⟩ := hA
  have hc := cornerPlacement_covers P T i j
  rw [← heq, Placement.cells, htile, registerTileSupport, hshift] at hc
  exact aligned_carrier_not_later_corner P d.state d.tile d.labels hbefore hc

/-- Every row-major corner selection in an arbitrary exact tiling is a
carrier occurrence at the corresponding lattice origin.  The proof is a
strong induction over physical occurrences, not an assumed global grid. -/
theorem all_cornerPlacements_anchored
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    ∀ (i j : Fin n), IsAnchoredCorner P T i j := by
  have main : ∀ r : ℕ, ∀ (i j : Fin n),
      rowMajorRank n i.1 j.1 = r → IsAnchoredCorner P T i j := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro i j hrank
        have hprior : ∀ (i' j' : Fin n),
            rowMajorRank n i'.1 j'.1 < rowMajorRank n i.1 j.1 →
            IsAnchoredCorner P T i' j' := by
          intro i' j' hlt
          apply ih (rowMajorRank n i'.1 j'.1)
          · simpa [hrank] using hlt
          · exact rfl
        have hnplug := cornerPlacement_ne_plug_of_prior P T i j hprior
        obtain ⟨d, htile⟩ := registerTile_some_carrierDatum P hnplug
        let p := cornerPlacement P T i j
        have hpMem : p ∈ T.placements := cornerPlacement_mem P T i j
        have hpSub := T.placement_subset hpMem
        have hcontained : translate (carrier P d.state d.tile d.labels) p.shift ⊆
            square (P.pitch * n) := by
          simpa [p, Placement.cells, htile, registerTileSupport] using hpSub
        have hcorner : macroCorner P i.1 j.1 ∈
            translate (carrier P d.state d.tile d.labels) p.shift := by
          simpa [p, Placement.cells, htile, registerTileSupport] using
            (cornerPlacement_covers P T i j)
        let Dprev : Fin n → CarrierDatum P := fun k =>
          if hj : 0 < j.1 then
            anchoredDatumOf P
              (hprior k ⟨j.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
                (prior_any_row_rank_lt i j k hj))
          else d
        let dLeft : CarrierDatum P :=
          if hi : 0 < i.1 then
            anchoredDatumOf P
              (hprior ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ j
                (prior_col_rank_lt i j hi))
          else d
        have hprev : 0 < j.1 → Disjoint (anchoredRowUnion P (j.1 - 1) Dprev)
            (translate (carrier P d.state d.tile d.labels) p.shift) := by
          intro hj
          rw [Finset.disjoint_left]
          intro z hzprev hzcur
          rcases Finset.mem_biUnion.mp hzprev with ⟨k, _, hzk⟩
          let jp : Fin n := ⟨j.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
          have hA : IsAnchoredCorner P T k jp :=
            hprior k jp (prior_any_row_rank_lt i j k hj)
          have hD : Dprev k = anchoredDatumOf P hA := by
            simp [Dprev, hj, jp]
          have hspec := anchoredDatumOf_spec P hA
          have hzq : z ∈ Placement.cells (registerTileSupport P)
              (cornerPlacement P T k jp) := by
            rw [Placement.cells, hspec.1, registerTileSupport, hspec.2]
            rw [hD] at hzk
            simpa [anchoredRowUnion, CarrierDatum.support, macroCorner, jp] using hzk
          have hzp : z ∈ Placement.cells (registerTileSupport P) p := by
            simpa [p, Placement.cells, htile, registerTileSupport] using hzcur
          have hne : cornerPlacement P T k jp ≠ p := by
            apply cornerPlacement_ne_of_anchored_before P T (hA := hA)
            left
            dsimp [jp]
            omega
          exact Finset.disjoint_left.mp
            (T.disjoint (cornerPlacement_mem P T k jp) hpMem hne) hzq hzp
        have hleft : 0 < i.1 → Disjoint
            (translate (carrier P dLeft.state dLeft.tile dLeft.labels)
              (macroCorner P (i.1 - 1) j.1))
            (translate (carrier P d.state d.tile d.labels) p.shift) := by
          intro hi
          let ip : Fin n := ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
          have hA : IsAnchoredCorner P T ip j :=
            hprior ip j (prior_col_rank_lt i j hi)
          have hD : dLeft = anchoredDatumOf P hA := by
            simp [dLeft, hi, ip]
          have hspec := anchoredDatumOf_spec P hA
          rw [Finset.disjoint_left]
          intro z hzleft hzcur
          have hzq : z ∈ Placement.cells (registerTileSupport P)
              (cornerPlacement P T ip j) := by
            rw [Placement.cells, hspec.1, registerTileSupport, hspec.2]
            rw [hD] at hzleft
            simpa [macroCorner, ip] using hzleft
          have hzp : z ∈ Placement.cells (registerTileSupport P) p := by
            simpa [p, Placement.cells, htile, registerTileSupport] using hzcur
          have hne : cornerPlacement P T ip j ≠ p := by
            apply cornerPlacement_ne_of_anchored_before P T (hA := hA)
            right
            exact ⟨rfl, by dsimp [ip]; omega⟩
          exact Finset.disjoint_left.mp
            (T.disjoint (cornerPlacement_mem P T ip j) hpMem hne) hzq hzp
        have hshift : p.shift = macroCorner P i.1 j.1 := by
          exact carrier_origin_exact P (Nat.zero_lt_of_lt i.isLt) i.1 j.1
            d.state dLeft.state d.tile dLeft.tile d.labels dLeft.labels p.shift
            Dprev hcontained hcorner hprev hleft
        exact ⟨d, by simpa [p] using htile, by simpa [p] using hshift⟩
  intro i j
  exact main (rowMajorRank n i.1 j.1) i j rfl

/-- The carrier datum decoded from the actual occurrence at `(i,j)`. -/
def extractedDatum (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) : CarrierDatum P :=
  anchoredDatumOf P (all_cornerPlacements_anchored P T i j)

theorem extractedDatum_spec (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) :
    (cornerPlacement P T i j).tile =
        some ⟨(extractedDatum P T i j).state,
          (extractedDatum P T i j).tile,
          (extractedDatum P T i j).labels⟩ ∧
      (cornerPlacement P T i j).shift = macroCorner P i.1 j.1 :=
  anchoredDatumOf_spec P (all_cornerPlacements_anchored P T i j)

theorem macroCorner_pair_injective (P : RegisterParams) {n : ℕ} :
    Function.Injective
      (fun q : Fin n × Fin n => macroCorner P q.1.1 q.2.1) := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [macroCorner] at hx hy
  have hp : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  have hxN : a.1.1 * P.pitch = b.1.1 * P.pitch := by exact_mod_cast hx
  have hyN : a.2.1 * P.pitch = b.2.1 * P.pitch := by exact_mod_cast hy
  have hxi : a.1 = b.1 := Fin.ext (Nat.eq_of_mul_eq_mul_right hp hxN)
  have hyi : a.2 = b.2 := Fin.ext (Nat.eq_of_mul_eq_mul_right hp hyN)
  exact Prod.ext hxi hyi

/-- Distinct macro-cells select distinct physical placement occurrences. -/
theorem cornerPlacement_pair_injective
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    Function.Injective (fun q : Fin n × Fin n => cornerPlacement P T q.1 q.2) := by
  intro a b h
  have hs := congrArg Placement.shift h
  rw [(extractedDatum_spec P T a.1 a.2).2,
    (extractedDatum_spec P T b.1 b.2).2] at hs
  exact macroCorner_pair_injective P hs

def selectedCarrierPlacements
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    Finset (Placement (RegisterTile P)) :=
  Finset.univ.image (fun q : Fin n × Fin n => cornerPlacement P T q.1 q.2)

theorem card_selectedCarrierPlacements
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    (selectedCarrierPlacements P T).card = n ^ 2 := by
  classical
  rw [selectedCarrierPlacements, Finset.card_image_of_injective _
    (cornerPlacement_pair_injective P T)]
  simp [pow_two]

theorem selectedCarrierPlacements_subset
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    selectedCarrierPlacements P T ⊆ T.placements := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
  exact cornerPlacement_mem P T q.1 q.2

theorem selectedCarrierPlacement_is_carrier
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {p : Placement (RegisterTile P)}
    (hp : p ∈ selectedCarrierPlacements P T) : p.tile ≠ none := by
  rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
  rw [(extractedDatum_spec P T q.1 q.2).1]
  simp

theorem extractedCarrier_subset_square
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) :
    translate (CarrierDatum.support P (extractedDatum P T i j))
      (macroCorner P i.1 j.1) ⊆ square (P.pitch * n) := by
  have hs := T.placement_subset (cornerPlacement_mem P T i j)
  rw [Placement.cells, (extractedDatum_spec P T i j).1,
    registerTileSupport, (extractedDatum_spec P T i j).2] at hs
  exact hs

theorem extractedCarriers_disjoint
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {a b : Fin n × Fin n} (hab : a ≠ b) :
    Disjoint
      (translate (CarrierDatum.support P (extractedDatum P T a.1 a.2))
        (macroCorner P a.1.1 a.2.1))
      (translate (CarrierDatum.support P (extractedDatum P T b.1 b.2))
        (macroCorner P b.1.1 b.2.1)) := by
  have hpne : cornerPlacement P T a.1 a.2 ≠ cornerPlacement P T b.1 b.2 :=
    (cornerPlacement_pair_injective P T).ne hab
  have hd := T.disjoint (cornerPlacement_mem P T a.1 a.2)
    (cornerPlacement_mem P T b.1 b.2) hpne
  change Disjoint
    (translate (registerTileSupport P (cornerPlacement P T a.1 a.2).tile)
      (cornerPlacement P T a.1 a.2).shift)
    (translate (registerTileSupport P (cornerPlacement P T b.1 b.2).tile)
      (cornerPlacement P T b.1 b.2).shift) at hd
  rw [(extractedDatum_spec P T a.1 a.2).1,
    registerTileSupport, (extractedDatum_spec P T a.1 a.2).2,
    (extractedDatum_spec P T b.1 b.2).1,
    registerTileSupport, (extractedDatum_spec P T b.1 b.2).2] at hd
  exact hd

theorem extracted_horizontal_compatible
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) (hi : i.1 + 1 < n) :
    HorizontalCompatibleDatum P (extractedDatum P T i j)
      (extractedDatum P T ⟨i.1 + 1, hi⟩ j) := by
  let ir : Fin n := ⟨i.1 + 1, hi⟩
  let a := extractedDatum P T i j
  let b := extractedDatum P T ir j
  have hpair : (i, j) ≠ (ir, j) := by
    intro h
    have := congrArg (fun q : Fin n × Fin n => q.1.1) h
    dsimp [ir] at this
    omega
  have hd := extractedCarriers_disjoint P T hpair
  have hdt := disjoint_translate_both
    (v := (-(macroCorner P i.1 j.1).1, -(macroCorner P i.1 j.1).2)) hd
  rw [translate_translate, translate_translate] at hdt
  have hnorm : Disjoint (carrier P a.state a.tile a.labels)
      (translate (carrier P b.state b.tile b.labels) ((P.pitch : ℤ), 0)) := by
    convert hdt using 1 <;>
      simp [a, b, CarrierDatum.support, ir, macroCorner] <;> push_cast <;> ring
  exact horizontal_disjoint_implies_compatible P
    a.state b.state a.tile b.tile a.labels b.labels hnorm

theorem extracted_vertical_compatible
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i j : Fin n) (hj : j.1 + 1 < n) :
    VerticalCompatibleDatum P (extractedDatum P T i j)
      (extractedDatum P T i ⟨j.1 + 1, hj⟩) := by
  let jt : Fin n := ⟨j.1 + 1, hj⟩
  let a := extractedDatum P T i j
  let b := extractedDatum P T i jt
  have hpair : (i, j) ≠ (i, jt) := by
    intro h
    have := congrArg (fun q : Fin n × Fin n => q.2.1) h
    dsimp [jt] at this
    omega
  have hd := extractedCarriers_disjoint P T hpair
  have hdt := disjoint_translate_both
    (v := (-(macroCorner P i.1 j.1).1, -(macroCorner P i.1 j.1).2)) hd
  rw [translate_translate, translate_translate] at hdt
  have hnorm : Disjoint (carrier P a.state a.tile a.labels)
      (translate (carrier P b.state b.tile b.labels) (0, (P.pitch : ℤ))) := by
    convert hdt using 1 <;>
      simp [a, b, CarrierDatum.support, jt, macroCorner] <;> push_cast <;> ring
  exact vertical_disjoint_implies_compatible P
    a.state b.state a.tile b.tile a.labels b.labels hnorm

theorem extracted_west_closed
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (j : Fin n) :
    (extractedDatum P T ⟨0, Nat.zero_lt_of_lt j.isLt⟩ j).state.west = false := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  let d := extractedDatum P T i0 j
  cases hw : d.state.west
  · rfl
  · exfalso
    have hopen : Side.west ∈ activeSides d.state :=
      (mem_activeSides d.state .west).2 (by simpa [MacroState.isOpen] using hw)
    have hm0 : (-1, (P.handshake : ℤ)) ∈ carrier P d.state d.tile d.labels := by
      simpa [bumpCell] using
        (bumpCell_mem_carrier_iff P d.state d.tile d.labels .west).2 hopen
    have hm : (-1, ((j.1 * P.pitch : ℕ) : ℤ) + P.handshake) ∈
        translate (CarrierDatum.support P d) (macroCorner P 0 j.1) := by
      apply Finset.mem_image.mpr
      refine ⟨_, hm0, ?_⟩
      apply Prod.ext <;> dsimp [d, CarrierDatum.support, macroCorner] <;> ring
    have hs := extractedCarrier_subset_square P T i0 j hm
    have hb := mem_square_coord_bounds hs
    omega

theorem extracted_east_closed
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (j : Fin n) :
    (extractedDatum P T
      ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (by decide)⟩ j).state.east = false := by
  let il : Fin n := ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt j.isLt) (by decide)⟩
  let d := extractedDatum P T il j
  cases he : d.state.east
  · rfl
  · exfalso
    have hopen : Side.east ∈ activeSides d.state :=
      (mem_activeSides d.state .east).2 (by simpa [MacroState.isOpen] using he)
    have hm0 : ((P.pitch : ℤ),
        (codeH P d.state.south d.state.north (P.east d.tile) d.labels.east : ℤ)) ∈
        carrier P d.state d.tile d.labels := by
      simpa [bumpCell] using
        (bumpCell_mem_carrier_iff P d.state d.tile d.labels .east).2 hopen
    have hm :
        ((((n - 1) * P.pitch : ℕ) : ℤ) + P.pitch,
          ((j.1 * P.pitch : ℕ) : ℤ) +
            codeH P d.state.south d.state.north (P.east d.tile) d.labels.east) ∈
        translate (CarrierDatum.support P d) (macroCorner P (n - 1) j.1) := by
      apply Finset.mem_image.mpr
      refine ⟨_, hm0, ?_⟩
      apply Prod.ext <;> dsimp [d, CarrierDatum.support, macroCorner] <;> ring
    have hs := extractedCarrier_subset_square P T il j hm
    have hb := mem_square_coord_bounds hs
    have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
    have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hmul : (n - 1) * P.pitch + P.pitch = n * P.pitch := by
      conv_rhs => rw [← hnEq]
      rw [Nat.add_mul, one_mul]
    have hmulZ : ((((n - 1) * P.pitch : ℕ) : ℤ) + P.pitch) =
        ((n * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
    have hcomm : P.pitch * n = n * P.pitch := Nat.mul_comm _ _
    rw [hcomm] at hb
    omega

theorem extracted_south_closed
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i : Fin n) :
    (extractedDatum P T i ⟨0, Nat.zero_lt_of_lt i.isLt⟩).state.south = false := by
  let j0 : Fin n := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
  let d := extractedDatum P T i j0
  cases hsouth : d.state.south
  · rfl
  · exfalso
    have hopen : Side.south ∈ activeSides d.state :=
      (mem_activeSides d.state .south).2
        (by simpa [MacroState.isOpen] using hsouth)
    have hm0 : ((P.handshake : ℤ), -1) ∈ carrier P d.state d.tile d.labels := by
      simpa [bumpCell] using
        (bumpCell_mem_carrier_iff P d.state d.tile d.labels .south).2 hopen
    have hm :
        (((i.1 * P.pitch : ℕ) : ℤ) + P.handshake, -1) ∈
        translate (CarrierDatum.support P d) (macroCorner P i.1 0) := by
      apply Finset.mem_image.mpr
      refine ⟨_, hm0, ?_⟩
      apply Prod.ext <;> dsimp [d, CarrierDatum.support, macroCorner] <;> ring
    have hs := extractedCarrier_subset_square P T i j0 hm
    have hb := mem_square_coord_bounds hs
    omega

theorem extracted_north_closed
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (i : Fin n) :
    (extractedDatum P T i
      ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (by decide)⟩).state.north = false := by
  let jl : Fin n := ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt i.isLt) (by decide)⟩
  let d := extractedDatum P T i jl
  cases hnorth : d.state.north
  · rfl
  · exfalso
    have hopen : Side.north ∈ activeSides d.state :=
      (mem_activeSides d.state .north).2
        (by simpa [MacroState.isOpen] using hnorth)
    have hm0 :
        ((codeV P d.state.west d.state.east (P.north d.tile) d.labels.north : ℤ),
          (P.pitch : ℤ)) ∈ carrier P d.state d.tile d.labels := by
      simpa [bumpCell] using
        (bumpCell_mem_carrier_iff P d.state d.tile d.labels .north).2 hopen
    have hm :
        (((i.1 * P.pitch : ℕ) : ℤ) +
            codeV P d.state.west d.state.east (P.north d.tile) d.labels.north,
          (((n - 1) * P.pitch : ℕ) : ℤ) + P.pitch) ∈
        translate (CarrierDatum.support P d) (macroCorner P i.1 (n - 1)) := by
      apply Finset.mem_image.mpr
      refine ⟨_, hm0, ?_⟩
      apply Prod.ext <;> dsimp [d, CarrierDatum.support, macroCorner] <;> ring
    have hs := extractedCarrier_subset_square P T i jl hm
    have hb := mem_square_coord_bounds hs
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hmul : (n - 1) * P.pitch + P.pitch = n * P.pitch := by
      conv_rhs => rw [← hnEq]
      rw [Nat.add_mul, one_mul]
    have hmulZ : ((((n - 1) * P.pitch : ℕ) : ℤ) + P.pitch) =
        ((n * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
    have hcomm : P.pitch * n = n * P.pitch := Nat.mul_comm _ _
    rw [hcomm] at hb
    omega

/-- The carrier occurrences extracted from an arbitrary tiling form a fully
indexed anchored grid, including every interface register and all four
physical boundary closures. -/
def extractedAnchoredGrid
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    AnchoredGrid P n where
  cell := extractedDatum P T
  horizontal := extracted_horizontal_compatible P T
  vertical := extracted_vertical_compatible P T
  westClosed := extracted_west_closed P T
  eastClosed := extracted_east_closed P T
  southClosed := extracted_south_closed P T
  northClosed := extracted_north_closed P T

theorem tileCavity_disjoint_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) : Disjoint (tileCavity u) (carrier P η u l) := by
  rw [Finset.disjoint_left]
  intro z hzc hzcar
  rcases Finset.mem_union.mp hzcar with hb | hbump
  · exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_union.mpr (Or.inr hzc))
  · exact Finset.disjoint_left.mp
      (bumps_disjoint_body P η u l)
      hbump (tileCavity_subset_body P u hzc)

theorem macroCavity_eq_translate_tileCavity
    (P : RegisterParams) (i j : ℕ) (u : Fin P.tileCount) :
    macroCavity P i j u = translate (tileCavity u) (macroCorner P i j) := by
  ext z
  simp only [macroCavity, tileCavity, cavity, translate_translate, mem_translate]
  constructor <;> intro h <;> convert h using 1 <;>
    apply Prod.ext <;> dsimp [macroCavityOrigin, cavityOrigin, macroCorner] <;>
      push_cast <;> ring

/-- A tile-specific cavity lies too deep inside its own macro-cell to meet a
carrier based at any other macro origin. -/
theorem macroCavity_disjoint_other_alignedCarrier
    (P : RegisterParams) {i j i' j' : ℕ}
    (u : Fin P.tileCount) (η : MacroState) (v : Fin P.tileCount)
    (l : AmpRecord P η) (hne : (i, j) ≠ (i', j')) :
    Disjoint (macroCavity P i j u)
      (translate (carrier P η v l) (macroCorner P i' j')) := by
  rw [Finset.disjoint_left]
  intro z hzc hzcar
  have hc := macroCavity_bounds hzc
  have hr := mem_translate.mp hzcar
  have hb := carrier_subset_extendedBox P η v l hr
  have hbx := Finset.mem_Icc.mp (Finset.mem_product.mp hb).1
  have hby := Finset.mem_Icc.mp (Finset.mem_product.mp hb).2
  have hp := P.pitch_ge_sixty_eight
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hu := u.isLt
  simp only [macroCorner] at hbx hby
  push_cast at hbx hby
  by_cases hii : i = i'
  · subst i'
    have hjj : j ≠ j' := by
      intro h
      exact hne (by simp [h])
    rcases lt_or_gt_of_ne hjj with hjlt | hjgt
    · have hstep : j + 1 ≤ j' := Nat.succ_le_iff.mpr hjlt
      have hmul : j * P.pitch + P.pitch ≤ j' * P.pitch := by
        simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hstep
      have hmulZ : ((j * P.pitch : ℕ) : ℤ) + P.pitch ≤
          ((j' * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
      rcases hc.2.2 with hy | hy <;> omega
    · have hstep : j' + 1 ≤ j := Nat.succ_le_iff.mpr hjgt
      have hmul : j' * P.pitch + P.pitch ≤ j * P.pitch := by
        simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hstep
      have hmulZ : ((j' * P.pitch : ℕ) : ℤ) + P.pitch ≤
          ((j * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
      rcases hc.2.2 with hy | hy <;> omega
  · rcases lt_or_gt_of_ne hii with hilt | higt
    · have hstep : i + 1 ≤ i' := Nat.succ_le_iff.mpr hilt
      have hmul : i * P.pitch + P.pitch ≤ i' * P.pitch := by
        simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hstep
      have hmulZ : ((i * P.pitch : ℕ) : ℤ) + P.pitch ≤
          ((i' * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
      omega
    · have hstep : i' + 1 ≤ i := Nat.succ_le_iff.mpr higt
      have hmul : i' * P.pitch + P.pitch ≤ i * P.pitch := by
        simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch hstep
      have hmulZ : ((i' * P.pitch : ℕ) : ℤ) + P.pitch ≤
          ((i * P.pitch : ℕ) : ℤ) := by exact_mod_cast hmul
      omega

theorem macroCavity_disjoint_extractedCarrier
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (a b : Fin n × Fin n) :
    Disjoint
      (macroCavity P a.1.1 a.2.1 (extractedDatum P T a.1 a.2).tile)
      (translate (CarrierDatum.support P (extractedDatum P T b.1 b.2))
        (macroCorner P b.1.1 b.2.1)) := by
  by_cases hab : a = b
  · subst b
    rw [macroCavity_eq_translate_tileCavity]
    exact disjoint_translate_both
      (tileCavity_disjoint_carrier P
        (extractedDatum P T a.1 a.2).state
        (extractedDatum P T a.1 a.2).tile
        (extractedDatum P T a.1 a.2).labels)
  · exact macroCavity_disjoint_other_alignedCarrier P
      (extractedDatum P T a.1 a.2).tile
      (extractedDatum P T b.1 b.2).state
      (extractedDatum P T b.1 b.2).tile
      (extractedDatum P T b.1 b.2).labels
      (by
        intro h
        apply hab
        exact Prod.ext (Fin.ext (congrArg Prod.fst h))
          (Fin.ext (congrArg Prod.snd h)))

def extractedCarrierUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) : Polyomino :=
  Finset.univ.biUnion fun q : Fin n × Fin n =>
    translate (CarrierDatum.support P (extractedDatum P T q.1 q.2))
      (macroCorner P q.1.1 q.2.1)

def extractedCavityUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) : Polyomino :=
  Finset.univ.biUnion fun q : Fin n × Fin n =>
    macroCavity P q.1.1 q.2.1 (extractedDatum P T q.1 q.2).tile

theorem extractedCarrierUnion_subset_square
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    extractedCarrierUnion P T ⊆ square (P.pitch * n) := by
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨q, _, hzq⟩
  exact extractedCarrier_subset_square P T q.1 q.2 hzq

theorem card_extractedCarrierUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    (extractedCarrierUnion P T).card = n ^ 2 * (P.pitch ^ 2 - 3) := by
  classical
  unfold extractedCarrierUnion
  rw [Finset.card_biUnion]
  · simp [CarrierDatum.support, carrier_area, pow_two]
  · intro a _ b _ hab
    exact extractedCarriers_disjoint P T hab

theorem extractedCavityUnion_subset_square
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    extractedCavityUnion P T ⊆ square (P.pitch * n) := by
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨q, _, hzq⟩
  exact macroCavity_subset_square P q.1 q.2 (extractedDatum P T q.1 q.2).tile hzq

theorem card_extractedCavityUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    (extractedCavityUnion P T).card = 3 * n ^ 2 := by
  classical
  unfold extractedCavityUnion
  rw [Finset.card_biUnion]
  · simp [pow_two]
    ring
  · intro a _ b _ hab
    apply macroCavities_pairwise_disjoint P
    intro h
    apply hab
    exact Prod.ext (Fin.ext (congrArg Prod.fst h))
      (Fin.ext (congrArg Prod.snd h))

theorem extractedCavityUnion_disjoint_carriers
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    Disjoint (extractedCavityUnion P T) (extractedCarrierUnion P T) := by
  rw [Finset.disjoint_left]
  intro z hzc hzk
  rcases Finset.mem_biUnion.mp hzc with ⟨a, _, hza⟩
  rcases Finset.mem_biUnion.mp hzk with ⟨b, _, hzb⟩
  exact Finset.disjoint_left.mp
    (macroCavity_disjoint_extractedCarrier P T a b) hza hzb

theorem card_square_sdiff_extractedCarrierUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    (square (P.pitch * n) \ extractedCarrierUnion P T).card = 3 * n ^ 2 := by
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (extractedCarrierUnion_subset_square P T),
    card_square, card_extractedCarrierUnion]
  have hp2 : 3 ≤ P.pitch ^ 2 := by
    have hp := P.pitch_ge_sixty_eight
    nlinarith
  have hsq : (P.pitch * n) ^ 2 = n ^ 2 * P.pitch ^ 2 := by ring
  rw [hsq, Nat.mul_sub_left_distrib]
  have hle : n ^ 2 * 3 ≤ n ^ 2 * P.pitch ^ 2 := Nat.mul_le_mul_left _ hp2
  omega

/-- The area argument upgrades cavity containment to exact equality: after
the `n²` extracted carriers, no unidentified physical cell remains. -/
theorem square_sdiff_extractedCarrierUnion_eq_cavities
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    square (P.pitch * n) \ extractedCarrierUnion P T =
      extractedCavityUnion P T := by
  have hsub : extractedCavityUnion P T ⊆
      square (P.pitch * n) \ extractedCarrierUnion P T := by
    intro z hz
    exact Finset.mem_sdiff.mpr
      ⟨extractedCavityUnion_subset_square P T hz,
        fun hk => Finset.disjoint_left.mp
          (extractedCavityUnion_disjoint_carriers P T) hz hk⟩
  have hcard :
      (square (P.pitch * n) \ extractedCarrierUnion P T).card ≤
        (extractedCavityUnion P T).card := by
    rw [card_square_sdiff_extractedCarrierUnion,
      card_extractedCavityUnion]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- A compact occurrence-level certificate exported to the downstream
readout/bijection layer.  Every field is derived from the input tiling. -/
structure OccurrenceLevelExtraction
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) where
  grid : AnchoredGrid P n
  placementAt : Fin n × Fin n → Placement (RegisterTile P)
  datumAt : Fin n × Fin n → CarrierDatum P
  grid_eq : ∀ q, grid.cell q.1 q.2 = datumAt q
  placement_mem : ∀ q, placementAt q ∈ T.placements
  tile_eq : ∀ q, (placementAt q).tile =
    some ⟨(datumAt q).state, (datumAt q).tile, (datumAt q).labels⟩
  shift_eq : ∀ q, (placementAt q).shift = macroCorner P q.1.1 q.2.1
  placement_injective : Function.Injective placementAt
  carrier_occurrence_count :
    (Finset.univ.image placementAt).card = n ^ 2
  carrier_union : Polyomino
  carrier_union_eq : carrier_union = extractedCarrierUnion P T
  residual_eq : square (P.pitch * n) \ carrier_union = extractedCavityUnion P T

def occurrenceLevelExtraction
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    OccurrenceLevelExtraction P T where
  grid := extractedAnchoredGrid P T
  placementAt := fun q => cornerPlacement P T q.1 q.2
  datumAt := fun q => extractedDatum P T q.1 q.2
  grid_eq := fun _ => rfl
  placement_mem := fun q => cornerPlacement_mem P T q.1 q.2
  tile_eq := fun q => (extractedDatum_spec P T q.1 q.2).1
  shift_eq := fun q => (extractedDatum_spec P T q.1 q.2).2
  placement_injective := cornerPlacement_pair_injective P T
  carrier_occurrence_count := by
    simpa [selectedCarrierPlacements] using card_selectedCarrierPlacements P T
  carrier_union := extractedCarrierUnion P T
  carrier_union_eq := rfl
  residual_eq := square_sdiff_extractedCarrierUnion_eq_cavities P T

def remainingPlacements
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    Finset (Placement (RegisterTile P)) :=
  T.placements \ selectedCarrierPlacements P T

def remainingPlacementUnion
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) : Polyomino :=
  (remainingPlacements P T).biUnion (Placement.cells (registerTileSupport P))

theorem selectedCarrier_mem_union_iff
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) {z : Cell} :
    z ∈ extractedCarrierUnion P T ↔
      ∃ p ∈ selectedCarrierPlacements P T,
        z ∈ Placement.cells (registerTileSupport P) p := by
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨q, _, hzq⟩
    refine ⟨cornerPlacement P T q.1 q.2,
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [Placement.cells, (extractedDatum_spec P T q.1 q.2).1,
      registerTileSupport, (extractedDatum_spec P T q.1 q.2).2]
    exact hzq
  · rintro ⟨p, hp, hzp⟩
    rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    rw [Placement.cells, (extractedDatum_spec P T q.1 q.2).1,
      registerTileSupport, (extractedDatum_spec P T q.1 q.2).2] at hzp
    exact hzp

/-- The actual supports of precisely the non-selected placements are the
geometric residual, hence exactly the identity-cavity union. -/
theorem remainingPlacementUnion_eq_cavities
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    remainingPlacementUnion P T = extractedCavityUnion P T := by
  rw [← square_sdiff_extractedCarrierUnion_eq_cavities P T]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨p, hprem, hzp⟩
    have hp := (Finset.mem_sdiff.mp hprem).1
    have hnsel := (Finset.mem_sdiff.mp hprem).2
    apply Finset.mem_sdiff.mpr
    constructor
    · exact T.placement_subset hp hzp
    · intro hcarrier
      rcases (selectedCarrier_mem_union_iff P T).mp hcarrier with ⟨q, hqsel, hzq⟩
      have hq := selectedCarrierPlacements_subset P T hqsel
      have hpq : q ≠ p := by
        intro heq
        apply hnsel
        simpa [heq] using hqsel
      exact Finset.disjoint_left.mp (T.disjoint hq hp hpq) hzq hzp
  · intro hz
    have hzSquare := (Finset.mem_sdiff.mp hz).1
    obtain ⟨p, hp, hzp⟩ := T.every_cell_covered hzSquare
    have hnsel : p ∉ selectedCarrierPlacements P T := by
      intro hsel
      apply (Finset.mem_sdiff.mp hz).2
      exact (selectedCarrier_mem_union_iff P T).mpr ⟨p, hsel, hzp⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hnsel⟩, hzp⟩

theorem remainingPlacement_subset_cavities
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    {p : Placement (RegisterTile P)} (hp : p ∈ remainingPlacements P T) :
    Placement.cells (registerTileSupport P) p ⊆ extractedCavityUnion P T := by
  intro z hz
  rw [← remainingPlacementUnion_eq_cavities P T]
  exact Finset.mem_biUnion.mpr ⟨p, hp, hz⟩

end
end PakFixedPolyomino
