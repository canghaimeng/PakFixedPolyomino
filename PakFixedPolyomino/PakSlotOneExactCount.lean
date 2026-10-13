import PakFixedPolyomino.PakSlotZeroFullFrameBijection
import PakFixedPolyomino.PakSlotOneSideValueReflection
import PakFixedPolyomino.PakCoupledCoefficient

/-! # Exact first-branch decomposition

The literal first arrow of every full frame has slot zero or slot one.  This
file records that disjoint decomposition at the finite-cardinality level and
combines it with the parameter-free slot-one side reflection.  It deliberately
does not identify a slot-one fibre with semantic accepting words; that is the
subsequent raw-run/full-frame bijection.
-/

namespace PakFixedPolyomino.PakSlotOneExactCount

open PakMStarCouplingCorrectness
open PakFullFrameTableauReadback

abbrev SlotZeroFullFrame :=
  PakSlotZeroFullFrameBijection.SlotZeroFullFrame

abbrev SlotOneFullFrame :=
  PakSlotOneFullFrameReflection.SlotOneFullFrame

private noncomputable def firstSlot {n : ℕ} (F : FullFrame n n) : Fin 2 :=
  ((FullFrame.toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2

private noncomputable def toFirstBranch {n : ℕ} (F : FullFrame n n) :
    Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) := by
  by_cases hzero : firstSlot F = 0
  · exact Sum.inl ⟨F, hzero⟩
  · exact Sum.inr ⟨F, by
      rcases FullFrame.firstArrow_slot_zero_or_one F with h | h
      · exact (hzero h).elim
      · exact h⟩

private def fromFirstBranch {n : ℕ} :
    Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) → FullFrame n n :=
  Sum.elim Subtype.val Subtype.val

/-- The two occupied start slots form an actual disjoint partition of all
square full frames. -/
noncomputable def fullFrameEquivFirstBranch (n : ℕ) :
    FullFrame n n ≃ Sum (SlotZeroFullFrame n) (SlotOneFullFrame n) where
  toFun := toFirstBranch
  invFun := fromFirstBranch
  left_inv F := by
    classical
    by_cases hzero : firstSlot F = 0
    · simp [toFirstBranch, fromFirstBranch, hzero]
    · simp [toFirstBranch, fromFirstBranch, hzero]
  right_inv s := by
    classical
    rcases s with F | F
    ·
      have hzero : firstSlot F.1 = 0 := F.2
      simp [toFirstBranch, fromFirstBranch, hzero]
    ·
      have hne : firstSlot F.1 ≠ 0 := by
        intro hzero
        have : (0 : Fin 2) = 1 := hzero.symm.trans F.2
        exact Fin.zero_ne_one this
      simp [toFirstBranch, fromFirstBranch, hne]

noncomputable instance slotOneFullFrameFintype (n : ℕ) :
    Fintype (SlotOneFullFrame n) := inferInstance

/-- The exact number of full frames using the nontrivial start slot. -/
noncomputable def slotOneCount (n : ℕ) : ℕ :=
  Fintype.card (SlotOneFullFrame n)

/-- Exact branch accounting: the already-computable scanner baseline plus
the slot-one contribution is the entire full-frame coefficient. -/
theorem card_fullFrame_eq_baseline_add_slotOne (n : ℕ) :
    Fintype.card (FullFrame n n) =
      PakScannerBaselineAutomaton.baselineCount n + slotOneCount n := by
  rw [Fintype.card_congr (fullFrameEquivFirstBranch n), Fintype.card_sum]
  rw [PakSlotZeroFullFrameBijection.card_slotZeroFullFrame_eq_baselineCount]
  rfl

/-- A nonzero slot-one contribution forces the square side to lie in the
injective image of the self-delimiting side encoding. -/
theorem exists_sideValue_of_slotOneCount_pos {n : ℕ}
    (hpos : 0 < slotOneCount n) :
    ∃ x : ConcretePakSide.Word, n = ConcretePakSide.sideValue x := by
  have hnonempty : Nonempty (SlotOneFullFrame n) :=
    Fintype.card_pos_iff.mp hpos
  rcases hnonempty with ⟨F⟩
  exact PakSlotOneSideValueReflection.slotOne_prefix_forces_sideValue F

/-- Outside the side-code image the slot-one fibre is literally empty. -/
theorem slotOneCount_eq_zero_of_no_sideValue {n : ℕ}
    (hnone : ∀ x : ConcretePakSide.Word,
      n ≠ ConcretePakSide.sideValue x) :
    slotOneCount n = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  rcases exists_sideValue_of_slotOneCount_pos hpos with ⟨x, hx⟩
  exact hnone x hx

/-- Because `sideValue` is injective, a square side can encode at most one
input word. -/
theorem sideValue_witness_unique {n : ℕ}
    {x y : ConcretePakSide.Word}
    (hx : n = ConcretePakSide.sideValue x)
    (hy : n = ConcretePakSide.sideValue y) : x = y := by
  apply ConcretePakSide.sideValue_injective
  exact hx.symm.trans hy

/-! ## The first operational inverse law

The scanner path and the complete chronological operational run determine all
four physical tracks of a full frame.  This is the multiplicity-one statement
needed before a raw execution can be counted as a frame. -/

/-- Two full frames with the same scanner path and the same complete
operational readback are the same physical frame.  The proof uses the already
checked track reconstruction, rather than cardinal arithmetic. -/
theorem fullFrame_eq_of_same_scanner_and_uniformRun {n : ℕ}
    (F G : FullFrame n n)
    (hscanner : PakScannerBaselineAutomaton.FullFrame.toScannerPath F =
      PakScannerBaselineAutomaton.FullFrame.toScannerPath G)
    (hrun : FullFrame.toUniformWindowedRun F =
      FullFrame.toUniformWindowedRun G) : F = G := by
  have hscannerProjection : scannerProjection F.tiling =
      scannerProjection G.tiling :=
    PakSlotZeroFullFrameBijection.scannerProjection_eq_of_same_path
      F G hscanner
  have htableau : tableauProjection F.tiling = tableauProjection G.tiling := by
    calc
      tableauProjection F.tiling =
          (FullFrame.toUniformWindowedRun F).tableauTiling :=
        PakFullFrameTableauRoundtrip.FullFrame.tableauProjection_eq_roundtrip F
      _ = (FullFrame.toUniformWindowedRun G).tableauTiling :=
        congrArg UniformWindowedMStarRun.tableauTiling hrun
      _ = tableauProjection G.tiling :=
        (PakFullFrameTableauRoundtrip.FullFrame.tableauProjection_eq_roundtrip G).symm
  apply FullFrame.ext
  apply coupledTiling_ext_of_projections
  · exact PakSlotZeroFullFrameBijection.amplifierProjection_eq_of_fullFrames F G
  · exact PakSlotZeroFullFrameBijection.rippleProjection_eq_of_fullFrames F G
  · exact htableau
  · exact hscannerProjection

abbrev SlotOneOperationalSignature (n : ℕ) :=
  PakScannerBaselineAutomaton.ScannerPath n × UniformWindowedMStarRun n n

/-- Literal readback retained for counting: it contains both the whole east
scanner column and the whole chronological labelled run. -/
noncomputable def slotOneOperationalReadback {n : ℕ}
    (F : SlotOneFullFrame n) : SlotOneOperationalSignature n :=
  (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1,
    FullFrame.toUniformWindowedRun F.1)

/-- There is no hidden physical multiplicity over a scanner/run signature. -/
theorem slotOneOperationalReadback_injective {n : ℕ} :
    Function.Injective (slotOneOperationalReadback (n := n)) := by
  intro F G h
  apply Subtype.ext
  apply fullFrame_eq_of_same_scanner_and_uniformRun F.1 G.1
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The honest codomain for the first inverse is the image of literal
full-frame readback.  Subsequent junk completeness must identify this image
with exactly the framed raw accepting executions. -/
abbrev SlotOneOperationalImage (n : ℕ) :=
  Set.range (slotOneOperationalReadback (n := n))

/-- Explicit inverse onto the actual operational image. -/
noncomputable def slotOneOperationalEquiv (n : ℕ) :
    SlotOneFullFrame n ≃ SlotOneOperationalImage n :=
  Equiv.ofInjective (slotOneOperationalReadback (n := n))
    slotOneOperationalReadback_injective

noncomputable instance slotOneOperationalImageFintype (n : ℕ) :
    Fintype (SlotOneOperationalImage n) :=
  Fintype.ofEquiv (SlotOneFullFrame n) (slotOneOperationalEquiv n)

/-- Every literal scanner/run signature has at most one physical slot-one
frame above it. -/
theorem slotOne_operational_fibre_subsingleton {n : ℕ}
    (signature : SlotOneOperationalSignature n) :
    Subsingleton {F : SlotOneFullFrame n //
      slotOneOperationalReadback F = signature} := by
  constructor
  intro F G
  apply Subtype.ext
  exact slotOneOperationalReadback_injective (F.2.trans G.2.symm)

/-- Multiplicity theorem obtained from the explicit image equivalence. -/
theorem slotOneCount_eq_card_operationalImage (n : ℕ) :
    slotOneCount n = Fintype.card (SlotOneOperationalImage n) := by
  exact Fintype.card_congr (slotOneOperationalEquiv n)

end PakFixedPolyomino.PakSlotOneExactCount
