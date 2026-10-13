import PakFixedPolyomino.PakGeneralCapacityInitialWindow

/-! Actual post-write movable semantics preserve the entire hash-bounded
physical window of every successful occupied-arrow run. This supplies spatial
bounds from the literal capacity input, without a run-in-window certificate. -/
namespace PakFixedPolyomino.MStarHashWindowPersistence
open FiniteOneTapeSemantics FiniteOneTapeProgram
open PakGeneralCapacityInitialWindow PakSlotOneScannerMultiplicity
abbrev Config := PakMStarCouplingCorrectness.MStarConfig
abbrev Arrow := MStarULogAssembly.Arrow

def InHashInterval (left right : Int) (c : Config) : Prop :=
  left < c.head ∧ c.head < right ∧
    ∀ z, z ≤ left ∨ right ≤ z → c.tape z = .hash

theorem step_shape (c d : Config) (a : Arrow)
    (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d) :
    d.head = moveHead (transition MStarULogAssembly.program a).move c.head ∧
    d.tape = Function.update c.tape c.head (transition MStarULogAssembly.program a).write ∧
    MStarOuterProgram.movable (d.tape d.head) = true := by
  unfold step at hs
  dsimp only at hs
  split at hs
  · simp at hs
  · split at hs
    · rename_i hm
      cases Option.some.inj hs
      exact ⟨rfl, rfl, hm⟩
    · simp at hs

theorem step_preserves_hash_interval (left right : Int) (c d : Config) (a : Arrow)
    (hc : InHashInterval left right c)
    (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d) :
    InHashInterval left right d := by
  obtain ⟨_, htape, hmove⟩ := step_shape c d a hs
  obtain ⟨hcl, hcr, hch⟩ := hc
  have hhash : ∀ z, z ≤ left ∨ right ≤ z → d.tape z = .hash := by
    intro z hz
    have hne : z ≠ c.head := by rcases hz with hz | hz <;> omega
    rw [htape, Function.update_of_ne hne]
    exact hch z hz
  have hleft : left < d.head := by
    by_contra hn
    have hz := hhash d.head (Or.inl (by omega))
    rw [hz] at hmove
    cases hmove
  have hright : d.head < right := by
    by_contra hn
    have hz := hhash d.head (Or.inr (by omega))
    rw [hz] at hmove
    cases hmove
  exact ⟨hleft, hright, hhash⟩

theorem run_preserves_hash_interval (left right : Int) (c d : Config)
    (labels : List Arrow) (hc : InHashInterval left right c)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d) :
    InHashInterval left right d := by
  induction labels generalizing c with
  | nil => exact Option.some.inj hr ▸ hc
  | cons a labels ih =>
    cases hs : step MStarULogAssembly.program MStarOuterProgram.movable c a with
    | none => simp [run_cons, hs] at hr
    | some next =>
      exact ih next (step_preserves_hash_interval left right c next a hc hs)
        (by simpa [run_cons, hs] using hr)

theorem capacity_initial_hash_interval (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) :
    InHashInterval 0 (ConcretePakSide.sideValue x - 1 : Int)
      (capacityEncodedStartConfig x cap) := by
  have side := PakSideScanner.sideValue_ge_five x
  refine ⟨by simp [capacityEncodedStartConfig], ?_, ?_⟩
  · simp only [capacityEncodedStartConfig]
    omega
  · intro z hz
    change capacityInitialTape x cap z = .hash
    rcases hz with hl | hr
    · exact capacityInitialTape_left_hash x cap (by omega)
    · rw [capacityInitialTape, if_pos (by omega : 1 ≤ z)]
      apply List.getD_eq_default
      rw [capacityInitialCells_length]
      have height := PakSideScanner.sideScannerHeight x
      omega

theorem every_capacity_run_hash_interval (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d) :
    InHashInterval 0 (ConcretePakSide.sideValue x - 1 : Int) d :=
  run_preserves_hash_interval _ _ _ d labels (capacity_initial_hash_interval x cap) hr

def hash_window_persistence_spec : Prop :=
  (∀ (left right : Int) (c d : Config) (a : Arrow), InHashInterval left right c →
    step MStarULogAssembly.program MStarOuterProgram.movable c a = some d →
    InHashInterval left right d) ∧
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (labels : List Arrow) (d : Config),
    run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d →
    InHashInterval 0 (ConcretePakSide.sideValue x - 1 : Int) d)

theorem hash_window_persistence_spec_holds : hash_window_persistence_spec :=
  ⟨step_preserves_hash_interval, every_capacity_run_hash_interval⟩

end PakFixedPolyomino.MStarHashWindowPersistence
