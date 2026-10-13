import PakFixedPolyomino.FloorReadout

namespace PakFixedPolyomino

/-- Extensional, one-query metric reduction.  Complexity bounds are kept in a
separate predicate because this project does not formalize a machine model. -/
structure MetricReduction {Input : Type*}
    (f g : Input → ℕ) where
  instanceMap : Input → Input
  postprocess : Input → ℕ → ℕ
  correct : ∀ x, f x = postprocess x (g (instanceMap x))

def MetricReduction.comp {Input : Type*} {f g k : Input → ℕ}
    (fg : MetricReduction f g) (gk : MetricReduction g k) : MetricReduction f k where
  instanceMap x := gk.instanceMap (fg.instanceMap x)
  postprocess x y := fg.postprocess x (gk.postprocess (fg.instanceMap x) y)
  correct x := by rw [fg.correct, gk.correct]

/-- Abstract polynomial-time annotations.  No closure postulate is assumed: the
closure proof is supplied explicitly whenever the chosen machine library can
prove it. -/
structure PolyMetricReduction {Input : Type*} (f g : Input → ℕ)
    extends MetricReduction f g where
  instancePolytime : Prop
  postprocessPolytime : Prop

def Reduces {Input : Type*} (f g : Input → ℕ) : Prop := Nonempty (MetricReduction f g)

theorem Reduces.refl {Input : Type*} (f : Input → ℕ) : Reduces f f := by
  refine ⟨{ instanceMap := id, postprocess := fun _ y => y, correct := ?_ }⟩
  intro x
  rfl

theorem Reduces.trans {Input : Type*} {f g k : Input → ℕ} :
    Reduces f g → Reduces g k → Reduces f k := by
  rintro ⟨fg⟩ ⟨gk⟩
  exact ⟨fg.comp gk⟩

def HardFor {Input : Type*} (Class : (Input → ℕ) → Prop) (g : Input → ℕ) : Prop :=
  ∀ f, Class f → Reduces f g

def CompleteFor {Input : Type*} (Class : (Input → ℕ) → Prop) (g : Input → ℕ) : Prop :=
  Class g ∧ HardFor Class g

theorem hard_transfer {Input : Type*} {Class : (Input → ℕ) → Prop}
    {g k : Input → ℕ} (hg : HardFor Class g) (hgk : Reduces g k) :
    HardFor Class k := by
  intro f hf
  exact (hg f hf).trans hgk

theorem complete_of_member_of_hard {Input : Type*} {Class : (Input → ℕ) → Prop}
    {g : Input → ℕ} (hmem : Class g) (hhard : HardFor Class g) :
    CompleteFor Class g := ⟨hmem, hhard⟩

/-- The floor-readout map is a metric reduction once the exact arithmetic
identity is supplied for every instance. -/
def floorMetricReduction {Input : Type*}
    (wang geometric : Input → ℕ) (scale exponent : Input → ℕ)
    (hscale : ∀ x, 0 < scale x)
    (junk : Input → ℕ)
    (hcount : ∀ x, geometric x = scale x ^ exponent x * wang x + junk x)
    (hjunk : ∀ x, junk x < scale x ^ exponent x) :
    MetricReduction wang geometric where
  instanceMap := id
  postprocess x y := y / scale x ^ exponent x
  correct x := (floor_readout (hscale x) (hcount x) (hjunk x)).symm

/-- Final algebraic assembly: source hardness + floor readout + target
membership gives completeness. -/
theorem final_metric_composition {Input : Type*}
    {Class : (Input → ℕ) → Prop} {source wang poly : Input → ℕ}
    (hsource : HardFor Class source)
    (hsw : Reduces source wang)
    (hwp : Reduces wang poly)
    (hmember : Class poly) : CompleteFor Class poly := by
  refine complete_of_member_of_hard hmember ?_
  exact hard_transfer hsource (hsw.trans hwp)

end PakFixedPolyomino
