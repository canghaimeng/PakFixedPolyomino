import PakFixedPolyomino.MStarCopierExecution
import PakFixedPolyomino.ULogSemanticInitialization
import PakFixedPolyomino.PakCouplingGenerated

/-! The literal `M_star` outer shell instantiated with the finite `U_log` table. -/

namespace PakFixedPolyomino.MStarULogAssembly

open OneTapeTableau FiniteOneTapeProgram

abbrev ParserControl := MStarCopierMicrocode.Control
abbrev UniversalState := ULogControl.State
abbrev CoreTape := MStarConcreteAlphabet.CoreTape
abbrev State := MStarOuterProgram.State ParserControl UniversalState
abbrev Tape := MStarOuterProgram.Tape CoreTape

/-- The concrete parser/copier/ULog data; no machine field remains abstract. -/
def data : MStarOuterProgram.Data
    (ParserState := ParserControl) (UState := UniversalState)
    (UTape := CoreTape) :=
  MStarCopierMicrocode.attach ULogProgram.program
    ULogControl.qAccept ULogControl.qReject ULogControl.qStart

abbrev program : Program State Tape := MStarOuterProgram.program data
abbrev Arrow := FiniteOneTapeProgram.Arrow program
abbrev ULogArrow := FiniteOneTapeProgram.Arrow ULogProgram.program

def tableauData : TableauMachineData State Tape Arrow :=
  MStarOuterProgram.tableauData data

def boundaryData :
    PakCouplingGenerated.MachineBoundaryData State Tape :=
  MStarOuterProgram.boundaryData data

/-- The exact local five-track coupling table at any nonzero amplifier colour
cardinality. -/
def fiveCouplings (Q : ℕ) [NeZero Q] :=
  PakCouplingGenerated.fiveCouplings boundaryData tableauData Q

@[simp] theorem card_parserControl : Fintype.card ParserControl = 220 := by
  exact MStarCopierMicrocode.card_control

@[simp] theorem card_universalState : Fintype.card UniversalState = 315 := by
  exact ULogControl.card_state

@[simp] theorem card_coreTape : Fintype.card CoreTape = 53 := by
  native_decide

@[simp] theorem card_state : Fintype.card State = 538 := by
  native_decide

@[simp] theorem card_tape : Fintype.card Tape = 64 := by
  native_decide

theorem program_binary_branching (q : State) (x : Tape) :
    Fintype.card {a : Arrow //
      (FiniteOneTapeProgram.transition program a).sourceState = q ∧
        (FiniteOneTapeProgram.transition program a).read = x} ≤ 2 := by
  exact MStarOuterProgram.program_binary_branching data q x

theorem sim_rule_eq (q : UniversalState) (x : CoreTape) (i : Fin 2) :
    program.rule (.sim q) (.core x) i =
      (ULogProgram.program.rule q x i).map
        (MStarOuterProgram.mapUAction data) := by
  exact MStarOuterProgram.sim_rule_eq data q x i

/-- Every occupied labelled ULog slot is literally an occupied labelled slot
of the outer M-star program. -/
def simArrow (a : ULogArrow) : Arrow :=
  ⟨((.sim a.1.1.1, .core a.1.1.2), a.1.2), by
    rw [sim_rule_eq]
    cases h : ULogProgram.program.rule a.1.1.1 a.1.1.2 a.1.2 with
    | none => exact (a.2 h).elim
    | some action => simp [h]⟩

theorem simArrow_injective : Function.Injective simArrow := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  simp only [simArrow, Subtype.mk.injEq, Prod.mk.injEq,
    MStarOuterProgram.State.sim.injEq,
    MStarOuterProgram.Tape.core.injEq] at hv
  exact Prod.ext (Prod.ext hv.1.1 hv.1.2) hv.2

private theorem actionOf_eq_of_rule_eq
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (P : Program S T) (a : FiniteOneTapeProgram.Arrow P)
    (action : Action S T)
    (h : P.rule a.1.1.1 a.1.1.2 a.1.2 = some action) :
    FiniteOneTapeProgram.actionOf P a = action := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.2 hnone).elim

theorem actionOf_simArrow (a : ULogArrow) :
    FiniteOneTapeProgram.actionOf program (simArrow a) =
      MStarOuterProgram.mapUAction data
        (FiniteOneTapeProgram.actionOf ULogProgram.program a) := by
  cases h : ULogProgram.program.rule a.1.1.1 a.1.1.2 a.1.2 with
  | none => exact (a.2 h).elim
  | some action =>
      have hout : program.rule (MStarOuterProgram.State.sim a.1.1.1)
          (MStarOuterProgram.Tape.core a.1.1.2) a.1.2 =
          some (MStarOuterProgram.mapUAction data action) := by
        rw [sim_rule_eq, h]
        rfl
      rw [actionOf_eq_of_rule_eq ULogProgram.program a action h]
      exact actionOf_eq_of_rule_eq program (simArrow a)
        (MStarOuterProgram.mapUAction data action) (by
          simpa [simArrow] using hout)

theorem transition_simArrow (a : ULogArrow) :
    FiniteOneTapeProgram.transition program (simArrow a) =
      { sourceState := MStarOuterProgram.State.sim a.1.1.1
        read := MStarOuterProgram.Tape.core a.1.1.2
        write := (MStarOuterProgram.mapUAction data
          (FiniteOneTapeProgram.actionOf ULogProgram.program a)).write
        targetState := (MStarOuterProgram.mapUAction data
          (FiniteOneTapeProgram.actionOf ULogProgram.program a)).target
        move := (MStarOuterProgram.mapUAction data
          (FiniteOneTapeProgram.actionOf ULogProgram.program a)).move } := by
  unfold FiniteOneTapeProgram.transition
  rw [actionOf_simArrow]
  rfl

theorem accept_is_ulog_accept : data.uAccept = ULogControl.qAccept := rfl
theorem reject_is_ulog_reject : data.uReject = ULogControl.qReject := rfl
theorem start_is_ulog_start : data.uStart = ULogControl.qStart := rfl

theorem parser_slot_one_empty (q : ParserControl) (x : Tape) :
    program.rule (.parser q) x 1 = none := by
  exact MStarCopierMicrocode.combined_slot_one_empty ULogProgram.program
    ULogControl.qAccept ULogControl.qReject ULogControl.qStart q x

theorem simulated_accept_maps_to_outer_accept :
    MStarOuterProgram.mapUState data ULogControl.qAccept = .accept := by
  native_decide

theorem simulated_reject_maps_to_outer_reject :
    MStarOuterProgram.mapUState data ULogControl.qReject = .reject := by
  native_decide

theorem simulated_start_maps_to_sim :
    MStarOuterProgram.mapUState data ULogControl.qStart =
      .sim ULogControl.qStart := by
  native_decide

end PakFixedPolyomino.MStarULogAssembly
