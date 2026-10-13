import PakFixedPolyomino.PakCanonicalScanner
import Mathlib.Tactic

/-!
# A concrete padded four-step run

The canonical scanner row is not an abstract boundary word.  This file gives
the corresponding literal execution of the fixed outer program: slot zero at
`start` enters `accept`, and three literal accepting stays provide the four
horizontal tableau columns required by the canonical ripple counter.
-/

namespace PakFixedPolyomino.PakCanonicalFullTrack

open FiniteOneTapeProgram FiniteOneTapeSemantics
open PakMStarCouplingCorrectness
open PakCanonicalScanner

namespace Fixed

abbrev State := PakMStarCouplingCorrectness.Fixed.State
abbrev Tape := PakMStarCouplingCorrectness.Fixed.Tape
abbrev Arrow := PakMStarCouplingCorrectness.Fixed.Arrow

end Fixed

def startAction : Action Fixed.State Fixed.Tape :=
  { write := .core MStarConcreteAlphabet.zero
    target := .accept
    move := .stay }

def acceptAction : Action Fixed.State Fixed.Tape :=
  { write := .core MStarConcreteAlphabet.zero
    target := .accept
    move := .stay }

theorem initial_zero_letter :
    MStarOuterProgram.isInitialLetter MStarULogAssembly.data
      MStarConcreteAlphabet.zero = true := by
  simp [MStarOuterProgram.isInitialLetter, MStarULogAssembly.data,
    MStarCopierMicrocode.attach]

theorem start_zero_rule :
    MStarULogAssembly.program.rule .start
      (.core MStarConcreteAlphabet.zero) 0 = some startAction := by
  simpa [startAction] using
    (MStarOuterProgram.start_slot_zero MStarULogAssembly.data initial_zero_letter)

theorem accept_zero_rule :
    MStarULogAssembly.program.rule .accept
      (.core MStarConcreteAlphabet.zero) 0 = some acceptAction := by
  have hne : (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero : Fixed.Tape) ≠
      .hash := by decide
  simpa [acceptAction] using
    (MStarOuterProgram.accept_unique_stay MStarULogAssembly.data hne).1

def startArrow : Fixed.Arrow :=
  ⟨((.start, .core MStarConcreteAlphabet.zero), (0 : Fin 2)), by
    simp [start_zero_rule]⟩

def acceptArrow : Fixed.Arrow :=
  ⟨((.accept, .core MStarConcreteAlphabet.zero), (0 : Fin 2)), by
    simp [accept_zero_rule]⟩

theorem actionOf_eq_of_rule_eq
    {State Tape : Type*} [Fintype State] [Fintype Tape]
    [DecidableEq State] [DecidableEq Tape]
    (P : Program State Tape) (a : Arrow P) (act : Action State Tape)
    (h : P.rule a.1.1.1 a.1.1.2 a.1.2 = some act) :
    actionOf P a = act := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.2 hnone).elim

theorem actionOf_startArrow :
    actionOf MStarULogAssembly.program startArrow = startAction := by
  apply actionOf_eq_of_rule_eq
  simpa [startArrow] using start_zero_rule

theorem actionOf_acceptArrow :
    actionOf MStarULogAssembly.program acceptArrow = acceptAction := by
  apply actionOf_eq_of_rule_eq
  simpa [acceptArrow] using accept_zero_rule

@[simp] theorem startArrow_source : startArrow.1.1.1 = (.start : Fixed.State) := rfl

@[simp] theorem startArrow_read : startArrow.1.1.2 =
    (.core MStarConcreteAlphabet.zero : Fixed.Tape) := rfl

@[simp] theorem acceptArrow_source : acceptArrow.1.1.1 = (.accept : Fixed.State) := rfl

@[simp] theorem acceptArrow_read : acceptArrow.1.1.2 =
    (.core MStarConcreteAlphabet.zero : Fixed.Tape) := rfl

def encodedAcceptConfig : MStarConfig :=
  { state := .accept
    head := 1
    tape := encodedInitialTape }

theorem update_encodedInitialTape :
    Function.update encodedInitialTape 1 (.core MStarConcreteAlphabet.zero) =
      encodedInitialTape := by
  funext z
  by_cases hz : z = 1
  · subst z
    simp [encodedInitialTape]
  · have hzne : (1 : Int) ≠ z := Ne.symm hz
    simp [Function.update, encodedInitialTape, hz, hzne]

theorem start_step :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      encodedInitialConfig startArrow = some encodedAcceptConfig := by
  simp [FiniteOneTapeSemantics.step, transition, writtenTape,
    actionOf_startArrow, encodedInitialConfig, encodedAcceptConfig,
    encodedInitialTape, MStarOuterProgram.movable, update_encodedInitialTape,
    startAction, FiniteOneTapeSemantics.moveHead]

theorem accept_step :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      encodedAcceptConfig acceptArrow = some encodedAcceptConfig := by
  simp [FiniteOneTapeSemantics.step, transition, writtenTape,
    actionOf_acceptArrow, encodedAcceptConfig, encodedInitialTape,
    MStarOuterProgram.movable, update_encodedInitialTape, acceptAction,
    FiniteOneTapeSemantics.moveHead]

def canonicalConfig (t : Fin 5) : MStarConfig :=
  if t.1 = 0 then encodedInitialConfig else encodedAcceptConfig

def canonicalArrow (t : Fin 4) : Fixed.Arrow :=
  if t.1 = 0 then startArrow else acceptArrow

def canonicalRun : UniformWindowedMStarRun 3 4 where
  config := canonicalConfig
  arrow := canonicalArrow
  step := by
    intro t
    fin_cases t
    · simpa [canonicalConfig, canonicalArrow] using start_step
    · simpa [canonicalConfig, canonicalArrow] using accept_step
    · simpa [canonicalConfig, canonicalArrow] using accept_step
    · simpa [canonicalConfig, canonicalArrow] using accept_step
  origin := 0
  width_ge_three := by decide
  head_index := fun _ => ⟨1, by decide⟩
  head_eq := by
    intro t
    change (canonicalConfig t).head = (0 : Int) + 1
    simp only [canonicalConfig]
    split <;> rfl
  head_interior_left := by
    intro t
    exact Nat.zero_lt_succ _
  head_interior_right := by
    intro t
    decide
  hash_outside := by
    intro t z hz
    have hz1 : z ≠ 1 := by omega
    by_cases ht : t.1 = 0 <;>
      simp [canonicalConfig, ht, encodedInitialConfig, encodedAcceptConfig,
        encodedInitialTape, hz1]
  final_accept := by
    simp [canonicalConfig, encodedAcceptConfig]

def canonicalPaddedRun : PaddedUniformWindowedMStarRun 3 4 where
  run := canonicalRun
  left_endpoint_hash := by
    intro t
    by_cases ht : t.1 = 0 <;>
      simp [canonicalRun, canonicalConfig, ht, encodedInitialConfig,
        encodedAcceptConfig, encodedInitialTape]
  right_endpoint_hash := by
    intro t
    by_cases ht : t.1 = 0 <;>
      simp [canonicalRun, canonicalConfig, ht, encodedInitialConfig,
        encodedAcceptConfig, encodedInitialTape]

/-! ## Diagnostic fixed frame

The remaining declarations in this section are deliberately a *sanity check*,
not a reduction instance: the fixed word is a single zero and `start` takes
slot zero directly to `accept`.  It proves that the literal four tracks can be
assembled into a full frame without an oracle.  The headline construction must
instead use `ConcretePakSide.sideValue x`, the slot-one parser/copy/ULog path,
and the `digits_sideValue` correspondence for arbitrary `x`.
-/

/-- The four literal tracks at one cell of the diagnostic `4 × 3` frame. -/
def canonicalTrack (i : Fin 4) (j : Fin 3) :
    PakMStarCouplingCorrectness.Fixed.Tracks :=
  Prod.mk
    (Prod.mk
      (Prod.mk
        ((PakRippleCanonical.canonicalFullAmpTiling
          PakMStarCouplingCorrectness.Fixed.Q 4 3).1 i j)
        ((PakRippleCanonical.canonicalTiling 4 3).1 i j))
      (canonicalPaddedRun.run.tableauTiling.1 i j))
    (PakCanonicalScanner.canonicalTiling.1 i j)

/-- The five generated local tables accept all twelve cells of the canonical
frame.  This is an exhaustive check of the literal finite predicates after
the four tracks above have been constructed; it is not an assumed coupling
field. -/
theorem canonicalTrack_coupled (i : Fin 4) (j : Fin 3) :
    PakMStarCouplingCorrectness.Fixed.Coupled (canonicalTrack i j) := by
  change
    (MStarULogAssembly.fiveCouplings PakMStarCouplingCorrectness.Fixed.Q).west
        (canonicalTrack i j) = true ∧
      (MStarULogAssembly.fiveCouplings PakMStarCouplingCorrectness.Fixed.Q).east
        (canonicalTrack i j) = true ∧
      (MStarULogAssembly.fiveCouplings PakMStarCouplingCorrectness.Fixed.Q).south
        (canonicalTrack i j) = true ∧
      (MStarULogAssembly.fiveCouplings PakMStarCouplingCorrectness.Fixed.Q).north
        (canonicalTrack i j) = true ∧
      (MStarULogAssembly.fiveCouplings PakMStarCouplingCorrectness.Fixed.Q).nonEast
        (canonicalTrack i j) = true
  fin_cases i <;> fin_cases j <;> native_decide

/-- An actual `FullTrackRunCertificate`, assembled from the literal padded
run, the canonical ripple/grid amplifier, and the literal scanner path. -/
def canonicalFullTrackCertificate : FullTrackRunCertificate canonicalPaddedRun where
  time_pos := by decide
  amplifier := PakRippleCanonical.canonicalFullAmpTiling
    PakMStarCouplingCorrectness.Fixed.Q 4 3
  ripple := PakRippleCanonical.canonicalTiling 4 3
  scanner := PakCanonicalScanner.canonicalTiling
  coupled := by
    intro i j
    change PakMStarCouplingCorrectness.Fixed.Coupled (canonicalTrack i j)
    exact canonicalTrack_coupled i j
  west_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_west
      PakMStarCouplingCorrectness.Fixed.Q 4 3 (by decide) j
  east_boundary := by
    intro j
    exact PakRippleCanonical.canonicalFullAmp_east
      PakMStarCouplingCorrectness.Fixed.Q 4 3 (by decide) j
  south_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_south
      PakMStarCouplingCorrectness.Fixed.Q 4 3 i (by decide)
  north_boundary := by
    intro i
    exact PakRippleCanonical.canonicalFullAmp_north
      PakMStarCouplingCorrectness.Fixed.Q 4 3 i (by decide)

end PakFixedPolyomino.PakCanonicalFullTrack
