import PakFixedPolyomino.Carrier

namespace PakFixedPolyomino

private theorem bool_toNat_injective : Function.Injective Bool.toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Equality of horizontal register coordinates decodes every field. -/
theorem codeH_eq_iff (P : RegisterParams)
    (a b c d : Bool) (χ χ' : Fin P.horizontalColours) (l l' : Fin P.amp) :
    codeH P a b χ l = codeH P c d χ' l' ↔
      a = c ∧ b = d ∧ χ = χ' ∧ l = l' := by
  constructor
  · intro h
    obtain ⟨hχ, hl, ha, hb⟩ := registerCode_injective P.amp_pos l.isLt l'.isLt
      (bool_toNat_lt_two a) (bool_toNat_lt_two b)
      (bool_toNat_lt_two c) (bool_toNat_lt_two d) h
    exact ⟨bool_toNat_injective ha, bool_toNat_injective hb,
      Fin.ext hχ, Fin.ext hl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- Equality of vertical register coordinates decodes every field. -/
theorem codeV_eq_iff (P : RegisterParams)
    (a b c d : Bool) (χ χ' : Fin P.verticalColours) (l l' : Fin P.amp) :
    codeV P a b χ l = codeV P c d χ' l' ↔
      a = c ∧ b = d ∧ χ = χ' ∧ l = l' := by
  constructor
  · intro h
    obtain ⟨hχ, hl, ha, hb⟩ := registerCode_injective P.amp_pos l.isLt l'.isLt
      (bool_toNat_lt_two a) (bool_toNat_lt_two b)
      (bool_toNat_lt_two c) (bool_toNat_lt_two d) h
    exact ⟨bool_toNat_injective ha, bool_toNat_injective hb,
      Fin.ext hχ, Fin.ext hl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

def HorizontalCompatible (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η') : Prop :=
  η.east = η'.west ∧
  (η.east = true →
    η.south = η'.south ∧ η.north = η'.north ∧
    P.east u = P.west v ∧ l.east = l'.west)

def VerticalCompatible (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η') : Prop :=
  η.north = η'.south ∧
  (η.north = true →
    η.west = η'.west ∧ η.east = η'.east ∧
    P.north u = P.south v ∧ l.north = l'.south)

/-- On an open horizontal interface, equality of the physical code coordinate
is equivalent to equality of perpendicular bits, Wang colour, and amplifier
label. -/
theorem horizontal_open_code_iff (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    (_hopen : η.east = true) (_hrecip : η'.west = true) :
    codeH P η.south η.north (P.east u) l.east =
      codeH P η'.south η'.north (P.west v) l'.west ↔
    η.south = η'.south ∧ η.north = η'.north ∧
      P.east u = P.west v ∧ l.east = l'.west :=
  codeH_eq_iff P _ _ _ _ _ _ _ _

/-- Vertical analogue of `horizontal_open_code_iff`. -/
theorem vertical_open_code_iff (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    (_hopen : η.north = true) (_hrecip : η'.south = true) :
    codeV P η.west η.east (P.north u) l.north =
      codeV P η'.west η'.east (P.south v) l'.south ↔
    η.west = η'.west ∧ η.east = η'.east ∧
      P.north u = P.south v ∧ l.north = l'.south :=
  codeV_eq_iff P _ _ _ _ _ _ _ _

theorem dentCell_cross_side (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    {d e : Side} (h : dentCell P η u l d = dentCell P η' v l' e) : d = e := by
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hHw := codeH_bounds P η.south η.north (P.west u) l.west
  have hVs := codeV_bounds P η.west η.east (P.south u) l.south
  have hHw' := codeH_bounds P η'.south η'.north (P.west v) l'.west
  have hVs' := codeV_bounds P η'.west η'.east (P.south v) l'.south
  cases d <;> cases e <;> simp [dentCell] at h ⊢ <;> omega

theorem bumpCell_cross_side (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    {d e : Side} (h : bumpCell P η u l d = bumpCell P η' v l' e) : d = e := by
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hHe := codeH_bounds P η.south η.north (P.east u) l.east
  have hVn := codeV_bounds P η.west η.east (P.north u) l.north
  have hHe' := codeH_bounds P η'.south η'.north (P.east v) l'.east
  have hVn' := codeV_bounds P η'.west η'.east (P.north v) l'.north
  have hHep := codeH_lt_pitch P η.south η.north (P.east u) l.east
  have hVnp := codeV_lt_pitch P η.west η.east (P.north u) l.north
  have hHep' := codeH_lt_pitch P η'.south η'.north (P.east v) l'.east
  have hVnp' := codeV_lt_pitch P η'.west η'.east (P.north v) l'.north
  cases d <;> cases e <;> simp [bumpCell] at h ⊢ <;> omega

theorem dent_coordinate_of_set_eq (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    {d : Side} (hd : d ∈ activeSides η)
    (hset : dents P η u l = dents P η' v l') :
    dentCell P η u l d = dentCell P η' v l' d := by
  have hm : dentCell P η u l d ∈ dents P η' v l' := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rcases Finset.mem_image.mp hm with ⟨e, _, he⟩
  have hed : e = d := dentCell_cross_side P η' η v u l' l he
  subst e
  exact he.symm

theorem bump_coordinate_of_set_eq (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    {d : Side} (hd : d ∈ activeSides η)
    (hset : bumps P η u l = bumps P η' v l') :
    bumpCell P η u l d = bumpCell P η' v l' d := by
  have hm : bumpCell P η u l d ∈ bumps P η' v l' := by
    rw [← hset]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rcases Finset.mem_image.mp hm with ⟨e, _, he⟩
  have hed : e = d := bumpCell_cross_side P η' η v u l' l he
  subst e
  exact he.symm

private theorem bool_eq_false_or_true (b : Bool) : b = false ∨ b = true := by
  cases b <;> simp

/-- Once macro-state and tile identity agree, equality of geometric supports
recovers every amplifier label. -/
theorem carrier_eq_ampRecord
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l l' : AmpRecord P η)
    (hcar : carrier P η u l = carrier P η u l') : l = l' := by
  have hdents := carrier_eq_dents_of_tile_eq P η η u u l l' rfl hcar
  have hbumps := carrier_eq_bumps P η η u u l l' hcar
  apply AmpRecord.ext
  · rcases bool_eq_false_or_true η.west with hw | hw
    · exact (l.west_closed hw).trans (l'.west_closed hw).symm
    · have hc := dent_coordinate_of_set_eq P η η u u l l'
          (d := .west) (mem_activeSides η .west |>.2 hw) hdents
      have hcode : codeH P η.south η.north (P.west u) l.west =
          codeH P η.south η.north (P.west u) l'.west := by
        simpa [dentCell] using congrArg Prod.snd hc
      exact (codeH_eq_iff P η.south η.north η.south η.north
        (P.west u) (P.west u) l.west l'.west).mp hcode |>.2.2.2
  · rcases bool_eq_false_or_true η.east with he | he
    · exact (l.east_closed he).trans (l'.east_closed he).symm
    · have hc := bump_coordinate_of_set_eq P η η u u l l'
          (d := .east) (mem_activeSides η .east |>.2 he) hbumps
      have hcode : codeH P η.south η.north (P.east u) l.east =
          codeH P η.south η.north (P.east u) l'.east := by
        simpa [bumpCell] using congrArg Prod.snd hc
      exact (codeH_eq_iff P η.south η.north η.south η.north
        (P.east u) (P.east u) l.east l'.east).mp hcode |>.2.2.2
  · rcases bool_eq_false_or_true η.south with hs | hs
    · exact (l.south_closed hs).trans (l'.south_closed hs).symm
    · have hc := dent_coordinate_of_set_eq P η η u u l l'
          (d := .south) (mem_activeSides η .south |>.2 hs) hdents
      have hcode : codeV P η.west η.east (P.south u) l.south =
          codeV P η.west η.east (P.south u) l'.south := by
        simpa [dentCell] using congrArg Prod.fst hc
      exact (codeV_eq_iff P η.west η.east η.west η.east
        (P.south u) (P.south u) l.south l'.south).mp hcode |>.2.2.2
  · rcases bool_eq_false_or_true η.north with hn | hn
    · exact (l.north_closed hn).trans (l'.north_closed hn).symm
    · have hc := bump_coordinate_of_set_eq P η η u u l l'
          (d := .north) (mem_activeSides η .north |>.2 hn) hbumps
      have hcode : codeV P η.west η.east (P.north u) l.north =
          codeV P η.west η.east (P.north u) l'.north := by
        simpa [bumpCell] using congrArg Prod.fst hc
      exact (codeV_eq_iff P η.west η.east η.west η.east
        (P.north u) (P.north u) l.north l'.north).mp hcode |>.2.2.2

/-- Full aligned-support injectivity of the identity register. -/
theorem carrier_parameters_injective
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η')
    (hcar : carrier P η u l = carrier P η' v l') :
    ∃ hη : η = η', u = v ∧
      l = hη ▸ l' := by
  have hη := carrier_eq_macroState P η η' u v l l' hcar
  subst η'
  have huv := carrier_eq_tile P η η u v l l' hcar
  subst v
  exact ⟨rfl, rfl, carrier_eq_ampRecord P η u l l' hcar⟩

/-- Full unlabelled geometric injectivity, including the translation vector. -/
theorem translated_carrier_parameters_injective
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η')
    (t s : Cell)
    (hcar : translate (carrier P η u l) t = translate (carrier P η' v l') s) :
    t = s ∧ ∃ hη : η = η', u = v ∧ l = hη ▸ l' := by
  have ht : t ∈ translate (carrier P η u l) t := by
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), origin_mem_carrier P η u l, by ext <;> simp⟩
  have hs : s ∈ translate (carrier P η' v l') s := by
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), origin_mem_carrier P η' v l', by ext <;> simp⟩
  have ht' : t ∈ translate (carrier P η' v l') s := by simpa [hcar] using ht
  have hs' : s ∈ translate (carrier P η u l) t := by simpa [hcar] using hs
  have hst := (translated_carrier_origin P η' v l' s ht').1
  have hts := (translated_carrier_origin P η u l t hs').1
  have hsum : s.1 + s.2 = t.1 + t.2 := le_antisymm hst hts
  have htsEq : t = s := (translated_carrier_origin P η' v l' s ht').2 hsum
  subst s
  have haligned : carrier P η u l = carrier P η' v l' :=
    translate_injective t hcar
  exact ⟨rfl, carrier_parameters_injective P η η' u v l l' haligned⟩

/-- A safe west-body cell is present unless it is exactly the active west
dent.  The range excludes corners and the interior cavity. -/
theorem west_inner_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {y : ℕ}
    (hy0 : 8 ≤ y) (hyp : y < P.handshake)
    (hnot : η.west ≠ true ∨ y ≠ codeH P η.south η.north (P.west u) l.west) :
    ((0 : ℤ), (y : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight, hyp.trans P.handshake_lt_pitch⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, hactive, heq⟩
      have hW := mem_activeSides η d |>.1 hactive
      cases d
      · rcases hnot with hclosed | hne
        · exact (hclosed hW).elim
        · exact hne (by simpa [dentCell] using (congrArg Prod.snd heq).symm)
      · have hp := P.pitch_ge_sixty_eight
        simp [dentCell] at heq
        omega
      · have hV := (codeV_bounds P η.west η.east (P.south u) l.south).1
        simp [dentCell] at heq
        omega
      · have hh := P.handshake_eq
        simp [dentCell] at heq
        omega
    · have hb := tileCavity_bounds hc
      omega

theorem west_inner_mem_carrier_of_closed
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {y : ℕ} (hy0 : 8 ≤ y) (hyp : y < P.handshake)
    (hclosed : η.west = false) :
    ((0 : ℤ), (y : ℤ)) ∈ carrier P η u l :=
  west_inner_mem_carrier P η u l hy0 hyp (Or.inl (by simp [hclosed]))

/-- The fixed east handshake body cell is present when the east side is closed. -/
theorem east_handshake_mem_carrier_of_closed
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) (hclosed : η.east = false) :
    (((P.pitch - 1 : ℕ) : ℤ), (P.handshake : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide),
       P.handshake_lt_pitch⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, hactive, heq⟩
      have hD := mem_activeSides η d |>.1 hactive
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      cases d
      · simp [dentCell] at heq
        omega
      · simp [MacroState.isOpen, hclosed] at hD
      · simp [dentCell] at heq
        omega
      · simp [dentCell] at heq
        omega
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      omega

/-- Any horizontal non-overlap must satisfy the full reciprocal interface
register.  This is the difficult direction used when decoding a tiling. -/
theorem horizontal_disjoint_implies_compatible
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η')
    (hdis : Disjoint (carrier P η u l)
      (translate (carrier P η' v l') ((P.pitch : ℤ), 0))) :
    HorizontalCompatible P η η' u v l l' := by
  have noCollision {z : Cell} (hz : z ∈ carrier P η u l)
      (hz' : z ∈ translate (carrier P η' v l') ((P.pitch : ℤ), 0)) : False :=
    Finset.disjoint_left.mp hdis hz hz'
  have hrecip : η.east = η'.west := by
    cases he : η.east <;> cases hw : η'.west
    · rfl
    · exfalso
      let z : Cell := (((P.pitch - 1 : ℕ) : ℤ), (P.handshake : ℤ))
      have hz : z ∈ carrier P η u l := by
        exact east_handshake_mem_carrier_of_closed P η u l he
      have hr : (-1, (P.handshake : ℤ)) ∈ carrier P η' v l' := by
        have hopen : Side.west ∈ activeSides η' := mem_activeSides η' .west |>.2
          (by simpa [MacroState.isOpen] using hw)
        simpa [bumpCell] using (bumpCell_mem_carrier_iff P η' v l' .west).2 hopen
      have hz' : z ∈ translate (carrier P η' v l') ((P.pitch : ℤ), 0) := by
        apply Finset.mem_image.mpr
        refine ⟨(-1, (P.handshake : ℤ)), hr, ?_⟩
        apply Prod.ext
        · dsimp [z]
          have hp : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          push_cast
          omega
        · simp [z]
      exact noCollision hz hz'
    · exfalso
      let y := codeH P η.south η.north (P.east u) l.east
      let z : Cell := ((P.pitch : ℤ), (y : ℤ))
      have hz : z ∈ carrier P η u l := by
        have hopen : Side.east ∈ activeSides η := mem_activeSides η .east |>.2
          (by simpa [MacroState.isOpen] using he)
        simpa [bumpCell, y, z] using (bumpCell_mem_carrier_iff P η u l .east).2 hopen
      have hr : ((0 : ℤ), (y : ℤ)) ∈ carrier P η' v l' := by
        apply west_inner_mem_carrier_of_closed P η' v l'
        · exact (codeH_bounds P η.south η.north (P.east u) l.east).1
        · exact codeH_lt_handshake P η.south η.north (P.east u) l.east
        · exact hw
      have hz' : z ∈ translate (carrier P η' v l') ((P.pitch : ℤ), 0) := by
        apply Finset.mem_image.mpr
        refine ⟨((0 : ℤ), (y : ℤ)), hr, ?_⟩
        ext <;> simp [z]
      exact noCollision hz hz'
    · rfl
  refine ⟨hrecip, ?_⟩
  intro hopen
  have hwest : η'.west = true := hrecip ▸ hopen
  have hcode : codeH P η.south η.north (P.east u) l.east =
      codeH P η'.south η'.north (P.west v) l'.west := by
    by_contra hne
    let y := codeH P η.south η.north (P.east u) l.east
    let z : Cell := ((P.pitch : ℤ), (y : ℤ))
    have hz : z ∈ carrier P η u l := by
      have hs : Side.east ∈ activeSides η := mem_activeSides η .east |>.2 hopen
      simpa [bumpCell, y, z] using (bumpCell_mem_carrier_iff P η u l .east).2 hs
    have hr : ((0 : ℤ), (y : ℤ)) ∈ carrier P η' v l' := by
      apply west_inner_mem_carrier P η' v l'
      · exact (codeH_bounds P η.south η.north (P.east u) l.east).1
      · exact codeH_lt_handshake P η.south η.north (P.east u) l.east
      · exact Or.inr (by simpa [y] using hne)
    have hz' : z ∈ translate (carrier P η' v l') ((P.pitch : ℤ), 0) := by
      apply Finset.mem_image.mpr
      refine ⟨((0 : ℤ), (y : ℤ)), hr, ?_⟩
      ext <;> simp [z]
    exact noCollision hz hz'
  exact (horizontal_open_code_iff P η η' u v l l' hopen hwest).mp hcode

theorem carrier_west_outer_cell
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {y : ℤ}
    (hmem : (-1, y) ∈ carrier P η u l) :
    η.west = true ∧ y = P.handshake := by
  rcases Finset.mem_union.mp hmem with hb | hbump
  · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    norm_num at hc
  · rcases Finset.mem_image.mp hbump with ⟨d, hd, heq⟩
    have hopen := mem_activeSides η d |>.1 hd
    have hp := P.pitch_ge_sixty_eight
    have hH := (codeH_bounds P η.south η.north (P.east u) l.east).1
    have hV := (codeV_bounds P η.west η.east (P.north u) l.north).1
    cases d
    · exact ⟨by simpa [MacroState.isOpen] using hopen,
        by simpa [bumpCell] using (congrArg Prod.snd heq).symm⟩
    · simp [bumpCell] at heq
    · simp [bumpCell] at heq
    · simp [bumpCell] at heq

theorem carrier_east_outer_cell
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {y : ℤ}
    (hmem : ((P.pitch : ℤ), y) ∈ carrier P η u l) :
    η.east = true ∧ y = codeH P η.south η.north (P.east u) l.east := by
  rcases Finset.mem_union.mp hmem with hb | hbump
  · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    omega
  · rcases Finset.mem_image.mp hbump with ⟨d, hd, heq⟩
    have hopen := mem_activeSides η d |>.1 hd
    have hp := P.pitch_ge_sixty_eight
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    have hV := codeV_lt_pitch P η.west η.east (P.north u) l.north
    cases d
    · simp [bumpCell] at heq
    · exact ⟨by simpa [MacroState.isOpen] using hopen,
        by simpa [bumpCell] using (congrArg Prod.snd heq).symm⟩
    · simp [bumpCell] at heq
      omega
    · simp [bumpCell] at heq
      omega

/-- Full horizontal interface law: supports at adjacent macro-origins are
disjoint exactly when reciprocal bits and the identity register agree. -/
theorem horizontal_carriers_disjoint_iff
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η') :
    Disjoint (carrier P η u l)
      (translate (carrier P η' v l') ((P.pitch : ℤ), 0)) ↔
    HorizontalCompatible P η η' u v l l' := by
  constructor
  · exact horizontal_disjoint_implies_compatible P η η' u v l l'
  · intro hcompat
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hr := mem_translate.mp hz'
    have hbox := carrier_subset_extendedBox P η u l hz
    have hbox' := carrier_subset_extendedBox P η' v l' hr
    have hx := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).1
    have hx' := Finset.mem_Icc.mp (Finset.mem_product.mp hbox').1
    have hp := P.pitch_ge_sixty_eight
    have hxcases : z.1 = (P.pitch : ℤ) - 1 ∨ z.1 = P.pitch := by omega
    rcases hxcases with hxz | hxz
    · have hrelx : z.1 - P.pitch = -1 := by omega
      have hwmem : (-1, z.2) ∈ carrier P η' v l' := by
        convert hr using 1 <;> simp [hrelx]
      obtain ⟨hwest, hy⟩ := carrier_west_outer_cell P η' v l' hwmem
      have heast : η.east = true := by simpa [hcompat.1] using hwest
      have hnot := (dentCell_not_mem_carrier_iff P η u l .east).2
        (mem_activeSides η .east |>.2 (by simpa [MacroState.isOpen] using heast))
      apply hnot
      have hpoint : dentCell P η u l .east = z := by
        apply Prod.ext
        · simp [dentCell]
          have hpos : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          push_cast
          omega
        · simpa [dentCell] using hy.symm
      simpa [hpoint] using hz
    · have hzEq : z = ((P.pitch : ℤ), z.2) := Prod.ext hxz rfl
      rw [hzEq] at hz
      obtain ⟨heast, hy⟩ := carrier_east_outer_cell P η u l hz
      have hdata := hcompat.2 heast
      have hwest : η'.west = true := by simpa [hcompat.1] using heast
      have hcode : codeH P η.south η.north (P.east u) l.east =
          codeH P η'.south η'.north (P.west v) l'.west := by
        exact (horizontal_open_code_iff P η η' u v l l' heast hwest).2 hdata
      have hnot := (dentCell_not_mem_carrier_iff P η' v l' .west).2
        (mem_activeSides η' .west |>.2 (by simpa [MacroState.isOpen] using hwest))
      apply hnot
      have : (z.1 - P.pitch, z.2) =
          ((0 : ℤ), (codeH P η'.south η'.north (P.west v) l'.west : ℤ)) := by
        apply Prod.ext
        · simp [hxz]
        · simp [hy, hcode]
      change ((0 : ℤ), (codeH P η'.south η'.north (P.west v) l'.west : ℤ)) ∈
        carrier P η' v l'
      rw [← this]
      simpa using hr

theorem south_inner_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x : ℕ}
    (hx0 : 8 ≤ x) (hxp : x < P.handshake)
    (hnot : η.south ≠ true ∨ x ≠ codeV P η.west η.east (P.south u) l.south) :
    ((x : ℤ), (0 : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨hxp.trans P.handshake_lt_pitch,
       lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, hactive, heq⟩
      have hD := mem_activeSides η d |>.1 hactive
      cases d
      · have hH := (codeH_bounds P η.south η.north (P.west u) l.west).1
        simp [dentCell] at heq
        omega
      · have hp := P.pitch_ge_sixty_eight
        simp [dentCell] at heq
        omega
      · rcases hnot with hclosed | hne
        · exact (hclosed hD).elim
        · exact hne (by simpa [dentCell] using (congrArg Prod.fst heq).symm)
      · have hh := P.handshake_eq
        simp [dentCell] at heq
        omega
    · have hb := tileCavity_bounds hc
      omega

theorem south_inner_mem_carrier_of_closed
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x : ℕ} (hx0 : 8 ≤ x) (hxp : x < P.handshake)
    (hclosed : η.south = false) :
    ((x : ℤ), (0 : ℤ)) ∈ carrier P η u l :=
  south_inner_mem_carrier P η u l hx0 hxp (Or.inl (by simp [hclosed]))

theorem north_handshake_mem_carrier_of_closed
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) (hclosed : η.north = false) :
    ((P.handshake : ℤ), ((P.pitch - 1 : ℕ) : ℤ)) ∈ carrier P η u l := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr
      ⟨P.handshake_lt_pitch,
       Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide)⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, hactive, heq⟩
      have hD := mem_activeSides η d |>.1 hactive
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) l.west
      have hV := codeV_bounds P η.west η.east (P.south u) l.south
      cases d
      · simp [dentCell] at heq
        omega
      · simp [dentCell] at heq
        omega
      · simp [dentCell] at heq
        omega
      · simp [MacroState.isOpen, hclosed] at hD
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      omega

theorem carrier_south_outer_cell
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x : ℤ}
    (hmem : (x, -1) ∈ carrier P η u l) :
    η.south = true ∧ x = P.handshake := by
  rcases Finset.mem_union.mp hmem with hb | hbump
  · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    norm_num at hc
  · rcases Finset.mem_image.mp hbump with ⟨d, hd, heq⟩
    have hopen := mem_activeSides η d |>.1 hd
    have hp := P.pitch_ge_sixty_eight
    have hH := (codeH_bounds P η.south η.north (P.east u) l.east).1
    have hV := (codeV_bounds P η.west η.east (P.north u) l.north).1
    cases d
    · simp [bumpCell] at heq
    · simp [bumpCell] at heq
    · exact ⟨by simpa [MacroState.isOpen] using hopen,
        by simpa [bumpCell] using (congrArg Prod.fst heq).symm⟩
    · simp [bumpCell] at heq

theorem carrier_north_outer_cell
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) {x : ℤ}
    (hmem : (x, (P.pitch : ℤ)) ∈ carrier P η u l) :
    η.north = true ∧ x = codeV P η.west η.east (P.north u) l.north := by
  rcases Finset.mem_union.mp hmem with hb | hbump
  · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    omega
  · rcases Finset.mem_image.mp hbump with ⟨d, hd, heq⟩
    have hopen := mem_activeSides η d |>.1 hd
    have hp := P.pitch_ge_sixty_eight
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    have hH := codeH_lt_pitch P η.south η.north (P.east u) l.east
    cases d
    · simp [bumpCell] at heq
      omega
    · simp [bumpCell] at heq
      omega
    · simp [bumpCell] at heq
    · exact ⟨by simpa [MacroState.isOpen] using hopen,
        by simpa [bumpCell] using (congrArg Prod.fst heq).symm⟩

theorem vertical_disjoint_implies_compatible
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η')
    (hdis : Disjoint (carrier P η u l)
      (translate (carrier P η' v l') (0, (P.pitch : ℤ)))) :
    VerticalCompatible P η η' u v l l' := by
  have noCollision {z : Cell} (hz : z ∈ carrier P η u l)
      (hz' : z ∈ translate (carrier P η' v l') (0, (P.pitch : ℤ))) : False :=
    Finset.disjoint_left.mp hdis hz hz'
  have hrecip : η.north = η'.south := by
    cases hn : η.north <;> cases hs : η'.south
    · rfl
    · exfalso
      let z : Cell := ((P.handshake : ℤ), ((P.pitch - 1 : ℕ) : ℤ))
      have hz : z ∈ carrier P η u l := north_handshake_mem_carrier_of_closed P η u l hn
      have hr : ((P.handshake : ℤ), -1) ∈ carrier P η' v l' := by
        have hopen : Side.south ∈ activeSides η' := mem_activeSides η' .south |>.2
          (by simpa [MacroState.isOpen] using hs)
        simpa [bumpCell] using (bumpCell_mem_carrier_iff P η' v l' .south).2 hopen
      have hz' : z ∈ translate (carrier P η' v l') (0, (P.pitch : ℤ)) := by
        apply Finset.mem_image.mpr
        refine ⟨((P.handshake : ℤ), -1), hr, ?_⟩
        apply Prod.ext
        · simp [z]
        · dsimp [z]
          have hp : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          push_cast
          omega
      exact noCollision hz hz'
    · exfalso
      let x := codeV P η.west η.east (P.north u) l.north
      let z : Cell := ((x : ℤ), (P.pitch : ℤ))
      have hz : z ∈ carrier P η u l := by
        have hopen : Side.north ∈ activeSides η := mem_activeSides η .north |>.2
          (by simpa [MacroState.isOpen] using hn)
        simpa [bumpCell, x, z] using (bumpCell_mem_carrier_iff P η u l .north).2 hopen
      have hr : ((x : ℤ), (0 : ℤ)) ∈ carrier P η' v l' := by
        apply south_inner_mem_carrier_of_closed P η' v l'
        · exact (codeV_bounds P η.west η.east (P.north u) l.north).1
        · exact codeV_lt_handshake P η.west η.east (P.north u) l.north
        · exact hs
      have hz' : z ∈ translate (carrier P η' v l') (0, (P.pitch : ℤ)) := by
        apply Finset.mem_image.mpr
        refine ⟨((x : ℤ), (0 : ℤ)), hr, ?_⟩
        ext <;> simp [z]
      exact noCollision hz hz'
    · rfl
  refine ⟨hrecip, ?_⟩
  intro hopen
  have hsouth : η'.south = true := hrecip ▸ hopen
  have hcode : codeV P η.west η.east (P.north u) l.north =
      codeV P η'.west η'.east (P.south v) l'.south := by
    by_contra hne
    let x := codeV P η.west η.east (P.north u) l.north
    let z : Cell := ((x : ℤ), (P.pitch : ℤ))
    have hz : z ∈ carrier P η u l := by
      have hd : Side.north ∈ activeSides η := mem_activeSides η .north |>.2 hopen
      simpa [bumpCell, x, z] using (bumpCell_mem_carrier_iff P η u l .north).2 hd
    have hr : ((x : ℤ), (0 : ℤ)) ∈ carrier P η' v l' := by
      apply south_inner_mem_carrier P η' v l'
      · exact (codeV_bounds P η.west η.east (P.north u) l.north).1
      · exact codeV_lt_handshake P η.west η.east (P.north u) l.north
      · exact Or.inr (by simpa [x] using hne)
    have hz' : z ∈ translate (carrier P η' v l') (0, (P.pitch : ℤ)) := by
      apply Finset.mem_image.mpr
      refine ⟨((x : ℤ), (0 : ℤ)), hr, ?_⟩
      ext <;> simp [z]
    exact noCollision hz hz'
  exact (vertical_open_code_iff P η η' u v l l' hopen hsouth).mp hcode

theorem vertical_carriers_disjoint_iff
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η') :
    Disjoint (carrier P η u l)
      (translate (carrier P η' v l') (0, (P.pitch : ℤ))) ↔
    VerticalCompatible P η η' u v l l' := by
  constructor
  · exact vertical_disjoint_implies_compatible P η η' u v l l'
  · intro hcompat
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hr := mem_translate.mp hz'
    have hbox := carrier_subset_extendedBox P η u l hz
    have hbox' := carrier_subset_extendedBox P η' v l' hr
    have hy := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2
    have hy' := Finset.mem_Icc.mp (Finset.mem_product.mp hbox').2
    have hp := P.pitch_ge_sixty_eight
    have hycases : z.2 = (P.pitch : ℤ) - 1 ∨ z.2 = P.pitch := by omega
    rcases hycases with hyz | hyz
    · have hrel : (z.1, z.2 - P.pitch) = (z.1, -1) := by
        apply Prod.ext <;> simp <;> omega
      have hsmem : (z.1, -1) ∈ carrier P η' v l' := by
        rw [← hrel]
        simpa using hr
      obtain ⟨hsouth, hx⟩ := carrier_south_outer_cell P η' v l' hsmem
      have hnorth : η.north = true := by simpa [hcompat.1] using hsouth
      have hnot := (dentCell_not_mem_carrier_iff P η u l .north).2
        (mem_activeSides η .north |>.2 (by simpa [MacroState.isOpen] using hnorth))
      apply hnot
      have hpoint : dentCell P η u l .north = z := by
        apply Prod.ext
        · simpa [dentCell] using hx.symm
        · simp [dentCell]
          have hpos : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          push_cast
          omega
      simpa [hpoint] using hz
    · have hzEq : z = (z.1, (P.pitch : ℤ)) := Prod.ext rfl hyz
      rw [hzEq] at hz
      obtain ⟨hnorth, hx⟩ := carrier_north_outer_cell P η u l hz
      have hdata := hcompat.2 hnorth
      have hsouth : η'.south = true := by simpa [hcompat.1] using hnorth
      have hcode : codeV P η.west η.east (P.north u) l.north =
          codeV P η'.west η'.east (P.south v) l'.south :=
        (vertical_open_code_iff P η η' u v l l' hnorth hsouth).2 hdata
      have hnot := (dentCell_not_mem_carrier_iff P η' v l' .south).2
        (mem_activeSides η' .south |>.2 (by simpa [MacroState.isOpen] using hsouth))
      apply hnot
      change ((codeV P η'.west η'.east (P.south v) l'.south : ℤ), (0 : ℤ)) ∈
        carrier P η' v l'
      have hpair : (z.1, z.2 - P.pitch) =
          ((codeV P η'.west η'.east (P.south v) l'.south : ℤ), (0 : ℤ)) := by
        apply Prod.ext
        · simp [hx, hcode]
        · simp [hyz]
      rw [← hpair]
      simpa using hr

end PakFixedPolyomino
