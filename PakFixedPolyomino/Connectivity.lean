import PakFixedPolyomino.Interface

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 800000

/-- Body cell to which an exterior bump is attached. -/
def attachmentCell (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) : Side → Cell
  | .west => (0, P.handshake)
  | .east => (((P.pitch - 1 : ℕ) : ℤ), codeH P η.south η.north (P.east u) l.east)
  | .south => (P.handshake, 0)
  | .north => (codeV P η.west η.east (P.north u) l.north,
      ((P.pitch - 1 : ℕ) : ℤ))

theorem attachmentCell_in_body
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) (d : Side) :
    attachmentCell P η u l d ∈
      square P.pitch \ (dents P η u l ∪ tileCavity u) := by
  apply Finset.mem_sdiff.mpr
  constructor
  · cases d
    · exact ofNat_pair_mem_square.mpr
        ⟨lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight, P.handshake_lt_pitch⟩
    · exact ofNat_pair_mem_square.mpr
        ⟨Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide),
         codeH_lt_pitch P η.south η.north (P.east u) l.east⟩
    · exact ofNat_pair_mem_square.mpr
        ⟨P.handshake_lt_pitch, lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight⟩
    · exact ofNat_pair_mem_square.mpr
        ⟨codeV_lt_pitch P η.west η.east (P.north u) l.north,
         Nat.sub_lt (lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight) (by decide)⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨e, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hHw := codeH_bounds P η.south η.north (P.west u) l.west
      have hHe := codeH_bounds P η.south η.north (P.east u) l.east
      have hVs := codeV_bounds P η.west η.east (P.south u) l.south
      have hVn := codeV_bounds P η.west η.east (P.north u) l.north
      cases d <;> cases e <;> simp [attachmentCell, dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      cases d <;> simp [attachmentCell] at hb <;> omega

theorem bump_adj_attachment
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) (d : Side) :
    Adj4 (bumpCell P η u l d) (attachmentCell P η u l d) := by
  have hp := P.pitch_ge_sixty_eight
  cases d
  · change Adj4 (-1, (P.handshake : ℤ)) (0, (P.handshake : ℤ))
    left; rfl
  · change Adj4 ((P.pitch : ℤ),
      (codeH P η.south η.north (P.east u) l.east : ℤ))
      (((P.pitch - 1 : ℕ) : ℤ),
       (codeH P η.south η.north (P.east u) l.east : ℤ))
    right; left
    apply Prod.ext
    · push_cast
      omega
    · rfl
  · change Adj4 ((P.handshake : ℤ), -1) ((P.handshake : ℤ), 0)
    right; right; left; rfl
  · change Adj4
      ((codeV P η.west η.east (P.north u) l.north : ℤ), (P.pitch : ℤ))
      ((codeV P η.west η.east (P.north u) l.north : ℤ),
       ((P.pitch - 1 : ℕ) : ℤ))
    right; right; right
    apply Prod.ext
    · rfl
    · push_cast
      omega

/-- Full 4-connectivity of every explicit dented/bumped identity carrier. -/
theorem carrier_fourConnected
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (l : AmpRecord P η) : FourConnected (carrier P η u l) := by
  apply fourConnected_of_spine (carrierSpine_fourConnected P)
    (carrierSpine_subset P η u l)
  intro z hz
  rcases Finset.mem_union.mp hz with hbody | hbump
  · exact carrier_body_route_to_spine P η u l hbody
  · rcases Finset.mem_image.mp hbump with ⟨d, _, rfl⟩
    have hattBody := attachmentCell_in_body P η u l d
    rcases carrier_body_route_to_spine P η u l hattBody with ⟨s, hs, w⟩
    exact ⟨s, hs, Walk4In.cons
      (Finset.mem_union.mpr (Or.inr hbump)) (bump_adj_attachment P η u l d) w⟩

end
end PakFixedPolyomino
