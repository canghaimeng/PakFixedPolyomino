import PakFixedPolyomino.Residual

namespace PakFixedPolyomino

noncomputable section

abbrev CarrierIndex (P : RegisterParams) :=
  Σ η : MacroState, Σ u : Fin P.tileCount, AmpRecord P η

/-- `none` is PlugL; `some` carries the full identity-register index. -/
abbrev RegisterTile (P : RegisterParams) := Option (CarrierIndex P)

def registerTileSupport (P : RegisterParams) : RegisterTile P → Polyomino
  | none => plugL
  | some ⟨η, u, l⟩ => carrier P η u l

instance (P : RegisterParams) : Finite (AmpRecord P η) := by
  letI : Finite (Fin P.amp × Fin P.amp × Fin P.amp × Fin P.amp) := inferInstance
  exact Finite.of_injective
    (fun l => (l.west, l.east, l.south, l.north))
    (by
      intro a b h
      apply AmpRecord.ext
      · exact congrArg (fun x => x.1) h
      · exact congrArg (fun x => x.2.1) h
      · exact congrArg (fun x => x.2.2.1) h
      · exact congrArg (fun x => x.2.2.2) h)

instance (P : RegisterParams) : Fintype (RegisterTile P) := Fintype.ofFinite _

theorem registerTileSupport_nonempty (P : RegisterParams) (t : RegisterTile P) :
    (registerTileSupport P t).Nonempty := by
  rcases t with _ | ⟨η, u, l⟩
  · simp [registerTileSupport, plugL]
  · have hcard := carrier_area P η u l
    have hp := P.pitch_ge_sixty_eight
    have hp2 : 68 ^ 2 ≤ P.pitch ^ 2 := Nat.pow_le_pow_left hp 2
    norm_num at hp2
    apply Finset.card_pos.mp
    change 0 < (carrier P η u l).card
    rw [hcard]
    omega

theorem registerTileSupport_fourConnected (P : RegisterParams) (t : RegisterTile P) :
    FourConnected (registerTileSupport P t) := by
  rcases t with _ | ⟨η, u, l⟩
  · exact plugL_fourConnected
  · exact carrier_fourConnected P η u l

theorem plug_not_translate_carrier (P : RegisterParams)
    (η : MacroState) (u : Fin P.tileCount) (l : AmpRecord P η) (a b : Cell) :
    translate plugL a ≠ translate (carrier P η u l) b := by
  intro h
  have hc := congrArg Finset.card h
  simp [carrier_area P η u l] at hc
  have hp := P.pitch_ge_sixty_eight
  have hp2 : 68 ^ 2 ≤ P.pitch ^ 2 := Nat.pow_le_pow_left hp 2
  norm_num at hp2
  omega

/-- The fixed prototype collection has no geometric identity collapse, even
after arbitrary translations. -/
theorem registerTile_geometric_injective (P : RegisterParams)
    {t t' : RegisterTile P} {a b : Cell}
    (h : translate (registerTileSupport P t) a =
      translate (registerTileSupport P t') b) : t = t' ∧ a = b := by
  rcases t with _ | ⟨η, u, l⟩ <;> rcases t' with _ | ⟨η', v, l'⟩
  · have hab : a = b := cavity_injective (by simpa [registerTileSupport, cavity] using h)
    exact ⟨rfl, hab⟩
  · exact (plug_not_translate_carrier P η' v l' a b h).elim
  · exact (plug_not_translate_carrier P η u l b a h.symm).elim
  · obtain ⟨hab, hidx⟩ := translated_carrier_parameters_injective
      P η η' u v l l' a b h
    rcases hidx with ⟨hη, huv, hl⟩
    subst η'
    subst v
    have : l = l' := by simpa using hl
    subst l'
    exact ⟨rfl, hab⟩

end
end PakFixedPolyomino
