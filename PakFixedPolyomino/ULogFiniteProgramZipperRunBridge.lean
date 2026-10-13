import PakFixedPolyomino.ULogCompiler
import PakFixedPolyomino.StandardMachineZipperBridge
import PakFixedPolyomino.FiniteOneTapeRunSlots
import PakFixedPolyomino.ULogSourceObliviousBytecode

/-! Finite occupied-arrow runs into actual ULogSemantics list-zipper slot runs.
Terminal codes 0/1 are an explicit hypothesis, proved internally for the
scanner `boundedProgram`. Compact window loading remains open. -/

namespace PakFixedPolyomino.ULogFiniteProgramZipperRunBridge

open FiniteOneTapeProgram (Program Arrow actionOf transition)
open FiniteOneTapeSemantics (Config step run writtenTape moveHead run_nil run_cons
  arrowSlots successful_runs_eq_of_slots_eq)
open ULogCompiler
open StandardMachineZipperBridge (physical applyBounded_physical physical_state
  physical_head physical_tape_head)
open ULogSourceObliviousBytecode
open ULogSourceObliviousHaltingProgram
open StandardNondeterministicMachine (Machine)

variable {ns : Nat}

def semanticRun : ULogSemantics.Config → List Bool → Option ULogSemantics.Config
  | c, [] => some c
  | c, slot :: rest =>
      (ULogSemantics.stepSlot slot c).bind (fun c' => semanticRun c' rest)

def zipperSlotRun (p : BoundedProgram ns 3) :
    List Bool → Int → BoundedConfig ns 3 → Option (Int × BoundedConfig ns 3)
  | [], head, z => some (head, z)
  | slot :: rest, head, z =>
      if boundedHalted z then none
      else
        match p.rule z.state z.focus slot with
        | none => none
        | some a =>
            zipperSlotRun p rest (moveHead a.move head)
              (applyBounded (2 : Fin 3) z a)

theorem blank2 : (2 : Fin 3).val = ULogSemantics.blankCode := rfl

def TerminalTable (p : BoundedProgram ns 3) : Prop :=
  ∀ (q : Fin ns) (read : Fin 3) (slot : Bool),
    q.val < 2 → p.rule q read slot = none

theorem zipperSlotRun_lift (p : BoundedProgram ns 3) (slots : List Bool)
    (head : Int) (z : BoundedConfig ns 3) :
    (zipperSlotRun p slots head z).map (fun hz => liftConfig p hz.2) =
      semanticRun (liftConfig p z) slots := by
  induction slots generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      have hstep :=
        stepSlot_liftConfig p (2 : Fin 3) blank2 slot z
      dsimp [zipperSlotRun, semanticRun]
      cases hh : boundedHalted z with
      | true =>
          have hsem : ULogSemantics.stepSlot slot (liftConfig p z) = none := by
            simpa [boundedStepSlot, hh] using hstep
          simp [hh, hsem]
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none =>
              have hsem : ULogSemantics.stepSlot slot (liftConfig p z) = none := by
                simpa [boundedStepSlot, hh, hr] using hstep
              simp [hh, hr, hsem]
          | some a =>
              have hsem :
                  ULogSemantics.stepSlot slot (liftConfig p z) =
                    some (liftConfig p (applyBounded (2 : Fin 3) z a)) := by
                simpa [boundedStepSlot, hh, hr] using hstep
              simp [hh, hr, hsem]
              exact ih (moveHead a.move head) (applyBounded (2 : Fin 3) z a)

theorem slotToBool_slotIndex (b : Bool) :
    decide (ULogBytecode.slotIndex b = 1) = b := by
  cases b <;> rfl

theorem slotIndex_slotToBool (s : Fin 2) :
    ULogBytecode.slotIndex (decide (s = 1)) = s := by
  fin_cases s <;> rfl

theorem slotToBool_inj {s t : Fin 2}
    (h : decide (s = 1) = decide (t = 1)) : s = t := by
  fin_cases s <;> fin_cases t <;> simp at h <;> rfl

def arrowSlotBool (p : BoundedProgram ns 3)
    (a : Arrow (toFiniteProgram p)) : Bool :=
  decide (a.1.2 = 1)

theorem arrowSlotBool_length (p : BoundedProgram ns 3)
    (word : List (Arrow (toFiniteProgram p))) :
    (word.map (arrowSlotBool p)).length = word.length := by
  simp

theorem toFiniteProgram_rule (p : BoundedProgram ns 3)
    (q : Fin ns) (read : Fin 3) (slot : Fin 2) :
    (toFiniteProgram p).rule q read slot =
      (p.rule q read (decide (slot = 1))).map
        fun a => ⟨a.write, a.target, a.move⟩ :=
  rfl

theorem actionOf_of_rule {State' Tape' : Type*}
    [Fintype State'] [Fintype Tape'] [DecidableEq State'] [DecidableEq Tape']
    (P : Program State' Tape') (arrow : Arrow P)
    (act : FiniteOneTapeProgram.Action State' Tape')
    (h : P.rule arrow.1.1.1 arrow.1.1.2 arrow.1.2 = some act) :
    actionOf P arrow = act := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact False.elim (by simp [h] at hnone)

theorem boundedHalted_false_of_rule (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (z : BoundedConfig ns 3) (slot : Bool)
    {a : BoundedAction ns 3} (hr : p.rule z.state z.focus slot = some a) :
    boundedHalted z = false := by
  have hnot : ¬ z.state.val < 2 := by
    intro hlt
    have := hterminal z.state z.focus slot hlt
    simp [this] at hr
  simp [boundedHalted, hnot]

theorem occupied_of_bounded_rule (p : BoundedProgram ns 3)
    (q : Fin ns) (read : Fin 3) (slot : Bool) {a : BoundedAction ns 3}
    (hr : p.rule q read slot = some a) :
    (toFiniteProgram p).rule q read (ULogBytecode.slotIndex slot) =
      some ⟨a.write, a.target, a.move⟩ := by
  rw [toFiniteProgram_rule, slotToBool_slotIndex, hr]
  rfl

def occupyArrow (p : BoundedProgram ns 3) (q : Fin ns) (read : Fin 3)
    (slot : Bool) {a : BoundedAction ns 3}
    (hr : p.rule q read slot = some a) :
    Arrow (toFiniteProgram p) :=
  ⟨((q, read), ULogBytecode.slotIndex slot), by
    intro hnone
    have := occupied_of_bounded_rule p q read slot hr
    simp [this] at hnone⟩

theorem occupyArrow_slot (p : BoundedProgram ns 3) (q : Fin ns) (read : Fin 3)
    (slot : Bool) {a : BoundedAction ns 3}
    (hr : p.rule q read slot = some a) :
    arrowSlotBool p (occupyArrow p q read slot hr) = slot := by
  simp [arrowSlotBool, occupyArrow]
  exact slotToBool_slotIndex slot

theorem step_occupyArrow (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (slot : Bool) {a : BoundedAction ns 3}
    (hr : p.rule z.state z.focus slot = some a) :
    step (toFiniteProgram p) (fun _ => true) (physical (2 : Fin 3) head z)
        (occupyArrow p z.state z.focus slot hr) =
      some (physical (2 : Fin 3) (moveHead a.move head)
        (applyBounded (2 : Fin 3) z a)) := by
  have hrule := occupied_of_bounded_rule p z.state z.focus slot hr
  have hact :=
    actionOf_of_rule (toFiniteProgram p)
      (occupyArrow p z.state z.focus slot hr)
      ⟨a.write, a.target, a.move⟩ (by simpa [occupyArrow] using hrule)
  unfold step
  have hsrc :
      (physical (2 : Fin 3) head z).state =
        (transition (toFiniteProgram p)
          (occupyArrow p z.state z.focus slot hr)).sourceState := by
    simp [transition, occupyArrow, physical_state]
  have hread :
      (physical (2 : Fin 3) head z).tape (physical (2 : Fin 3) head z).head =
        (transition (toFiniteProgram p)
          (occupyArrow p z.state z.focus slot hr)).read := by
    simp [transition, occupyArrow, physical_head, physical_tape_head]
  have hbad :
      ¬((physical (2 : Fin 3) head z).state ≠
          (transition (toFiniteProgram p)
            (occupyArrow p z.state z.focus slot hr)).sourceState ∨
        (physical (2 : Fin 3) head z).tape (physical (2 : Fin 3) head z).head ≠
          (transition (toFiniteProgram p)
            (occupyArrow p z.state z.focus slot hr)).read) := by
    simp [hsrc, hread]
  rw [if_neg hbad]
  simp [transition, hact, physical_head]
  exact (applyBounded_physical (2 : Fin 3) head z a).symm

theorem step_arrow_to_zipper (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3)
    (ar : Arrow (toFiniteProgram p)) {c' : Config (Fin ns) (Fin 3)}
    (hstep : step (toFiniteProgram p) (fun _ => true)
      (physical (2 : Fin 3) head z) ar = some c') :
    ∃ a : BoundedAction ns 3,
      p.rule z.state z.focus (arrowSlotBool p ar) = some a ∧
        boundedHalted z = false ∧
        c' = physical (2 : Fin 3) (moveHead a.move head)
          (applyBounded (2 : Fin 3) z a) := by
  have hforce :=
    FiniteOneTapeSemantics.step_some_forces_source (toFiniteProgram p)
      (fun _ => true) (physical (2 : Fin 3) head z) c' ar hstep
  have hst : ar.1.1.1 = z.state := by
    simpa [transition, physical_state] using hforce.1.symm
  have hrd : ar.1.1.2 = z.focus := by
    simpa [transition, physical_head, physical_tape_head] using hforce.2.symm
  cases hrFin : (toFiniteProgram p).rule ar.1.1.1 ar.1.1.2 ar.1.2 with
  | none => exact (ar.2 hrFin).elim
  | some _ =>
      rw [toFiniteProgram_rule, hst, hrd] at hrFin
      cases hb : p.rule z.state z.focus (decide (ar.1.2 = 1)) with
      | none => simp [hb] at hrFin
      | some a =>
          have hterm := boundedHalted_false_of_rule p hterminal z
            (decide (ar.1.2 = 1)) hb
          have hb' : p.rule z.state z.focus (arrowSlotBool p ar) = some a := by
            simpa [arrowSlotBool] using hb
          have har :
              ar = occupyArrow p z.state z.focus (arrowSlotBool p ar) hb' := by
            apply Subtype.ext
            apply Prod.ext
            · apply Prod.ext
              · exact hst
              · exact hrd
            · simp [occupyArrow, arrowSlotBool, slotIndex_slotToBool]
          refine ⟨a, hb', hterm, ?_⟩
          rw [har] at hstep
          have hocc := step_occupyArrow p head z (arrowSlotBool p ar) hb'
          exact Option.some.inj (hstep.symm.trans hocc)

theorem successful_arrows_to_zipper (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (word : List (Arrow (toFiniteProgram p)))
    (head : Int) (z : BoundedConfig ns 3) {out : Config (Fin ns) (Fin 3)}
    (hrun : run (toFiniteProgram p) (fun _ => true) word
      (physical (2 : Fin 3) head z) = some out) :
    ∃ head' z',
      zipperSlotRun p (word.map (arrowSlotBool p)) head z = some (head', z') ∧
        physical (2 : Fin 3) head' z' = out := by
  induction word generalizing head z out with
  | nil =>
      refine ⟨head, z, rfl, Option.some.inj hrun⟩
  | cons ar word ih =>
      simp only [List.map_cons, zipperSlotRun, run_cons] at hrun ⊢
      cases hstep : step (toFiniteProgram p) (fun _ => true)
          (physical (2 : Fin 3) head z) ar with
      | none => simp [hstep] at hrun
      | some c' =>
          obtain ⟨a, hb, hhalt, hc⟩ :=
            step_arrow_to_zipper p hterminal head z ar hstep
          simp [hstep] at hrun
          subst hc
          simp [hb, hhalt]
          exact ih (moveHead a.move head) (applyBounded (2 : Fin 3) z a) hrun

theorem successful_zipper_to_arrows (p : BoundedProgram ns 3)
    (slots : List Bool) (head : Int) (z : BoundedConfig ns 3)
    (head' : Int) (z' : BoundedConfig ns 3)
    (hzip : zipperSlotRun p slots head z = some (head', z')) :
    ∃ word : List (Arrow (toFiniteProgram p)),
      word.map (arrowSlotBool p) = slots ∧
        word.length = slots.length ∧
        run (toFiniteProgram p) (fun _ => true) word
          (physical (2 : Fin 3) head z) =
            some (physical (2 : Fin 3) head' z') := by
  induction slots generalizing head z with
  | nil =>
      have h := Option.some.inj hzip
      refine ⟨[], rfl, rfl, ?_⟩
      simp [run]
      cases h
      rfl
  | cons slot rest ih =>
      simp only [zipperSlotRun] at hzip
      cases hh : boundedHalted z with
      | true => simp [hh] at hzip
      | false =>
          simp [hh] at hzip
          cases hr : p.rule z.state z.focus slot with
          | none => simp [hr] at hzip
          | some a =>
              simp [hr] at hzip
              obtain ⟨word, hmap, hlen, hrun⟩ :=
                ih (moveHead a.move head) (applyBounded (2 : Fin 3) z a) hzip
              refine ⟨occupyArrow p z.state z.focus slot hr :: word, ?_, ?_, ?_⟩
              · simp [occupyArrow_slot, hmap]
              · simp [hlen]
              · simp [run_cons, step_occupyArrow p head z slot hr, hrun]

def RawFiniteLeaves (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) :=
  {word : List (Arrow (toFiniteProgram p)) //
    ∃ out, run (toFiniteProgram p) (fun _ => true) word
        (physical (2 : Fin 3) head z) = some out ∧
      out.state.val = 0}

def SemanticLeaves (p : BoundedProgram ns 3) (z : BoundedConfig ns 3) :=
  {slots : List Bool //
    ∃ out, semanticRun (liftConfig p z) slots = some out ∧ out.state = 0}

theorem arrowSlots_eq_of_bools (p : BoundedProgram ns 3)
    {as bs : List (Arrow (toFiniteProgram p))}
    (h : as.map (arrowSlotBool p) = bs.map (arrowSlotBool p)) :
    arrowSlots (toFiniteProgram p) as = arrowSlots (toFiniteProgram p) bs := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons => simp at h
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          have hp := List.cons.inj h
          have hs := slotToBool_inj hp.1
          simp [arrowSlots, hs]
          exact ih hp.2

def toSemanticLeaves (p : BoundedProgram ns 3) (hterminal : TerminalTable p)
    (head : Int) (z : BoundedConfig ns 3) (w : RawFiniteLeaves p head z) :
    SemanticLeaves p z :=
  ⟨w.1.map (arrowSlotBool p), by
    obtain ⟨out, hrun, hacc⟩ := w.2
    obtain ⟨head', z', hzip, hphys⟩ :=
      successful_arrows_to_zipper p hterminal w.1 head z hrun
    refine ⟨liftConfig p z', ?_, ?_⟩
    · have hsem := zipperSlotRun_lift p (w.1.map (arrowSlotBool p)) head z
      simpa [hzip] using hsem.symm
    · have hs : out.state = z'.state := by
        simpa [physical_state] using (congrArg Config.state hphys).symm
      simpa [liftConfig, hs] using hacc⟩

theorem toSemanticLeaves_injective (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3) :
    Function.Injective (toSemanticLeaves p hterminal head z) := by
  intro a b h
  have hbool : a.1.map (arrowSlotBool p) = b.1.map (arrowSlotBool p) :=
    congrArg Subtype.val h
  obtain ⟨outA, hrunA, _⟩ := a.2
  obtain ⟨outB, hrunB, _⟩ := b.2
  apply Subtype.ext
  exact (successful_runs_eq_of_slots_eq (toFiniteProgram p) (fun _ => true)
    a.1 b.1 (physical (2 : Fin 3) head z) outA outB hrunA hrunB
    (arrowSlots_eq_of_bools p hbool)).1

theorem toSemanticLeaves_surjective (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3) :
    Function.Surjective (toSemanticLeaves p hterminal head z) := by
  intro s
  obtain ⟨out, hsem, hacc⟩ := s.2
  have hmap :
      (zipperSlotRun p s.1 head z).map (fun hz => liftConfig p hz.2) =
        some out := by
    rw [zipperSlotRun_lift, hsem]
  obtain ⟨hz, hzip, hlift⟩ := Option.map_eq_some_iff.mp hmap
  obtain ⟨word, hslots, _, hrun⟩ :=
    successful_zipper_to_arrows p s.1 head z hz.1 hz.2 hzip
  have hacc' : (physical (2 : Fin 3) hz.1 hz.2).state.val = 0 := by
    have hs : (physical (2 : Fin 3) hz.1 hz.2).state.val =
        (liftConfig p hz.2).state := by
      simp [physical_state, liftConfig]
    simpa [hs, hlift] using hacc
  refine ⟨⟨word, ⟨physical (2 : Fin 3) hz.1 hz.2, hrun, hacc'⟩⟩, ?_⟩
  apply Subtype.ext
  simpa [toSemanticLeaves] using hslots

noncomputable def finiteLeavesEquiv (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3) :
    RawFiniteLeaves p head z ≃ SemanticLeaves p z :=
  Equiv.ofBijective (toSemanticLeaves p hterminal head z)
    ⟨toSemanticLeaves_injective p hterminal head z,
      toSemanticLeaves_surjective p hterminal head z⟩

theorem finiteLeavesEquiv_length (p : BoundedProgram ns 3)
    (hterminal : TerminalTable p) (head : Int) (z : BoundedConfig ns 3)
    (w : RawFiniteLeaves p head z) :
    ((finiteLeavesEquiv p hterminal head z) w).1.length = w.1.length := by
  simpa [finiteLeavesEquiv, Equiv.ofBijective, toSemanticLeaves] using
    arrowSlotBool_length p w.1

variable {nt : Nat}

theorem scanner_terminal (M : Machine ns nt 2)
    (q : Fin (2 + Fintype.card (Active M))) (read : Fin 3) (slot : Bool)
    (hq : q.val < 2) :
    (boundedProgram M).rule q read slot = none := by
  have h01 : q.val = 0 ∨ q.val = 1 := by omega
  have hform :
      (boundedProgram M).rule q read slot =
        ((haltProgram M).rule ((stateEquiv M).symm q) read
          (ULogBytecode.slotIndex slot)).map
          (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3))) := by
    simp [boundedProgram, ofFiniteProgram]
  rw [hform]
  rcases h01 with h0 | h1
  · have hqeq : q = stateEquiv M (.atLeft M.accept) := by
      apply Fin.ext
      simpa [stateEquiv_accept] using h0
    simp [hqeq, haltProgram_accept_terminal]
  · have hqeq : q = stateEquiv M .reject := by
      apply Fin.ext
      simpa [stateEquiv_reject] using h1
    simp [hqeq, haltProgram_reject_terminal]

theorem scanner_terminal_table (M : Machine ns nt 2) :
    TerminalTable (boundedProgram M) :=
  scanner_terminal M

noncomputable def scannerLeavesEquiv (M : Machine ns nt 2) (head : Int)
    (z : BoundedConfig (2 + Fintype.card (Active M)) 3) :
    RawFiniteLeaves (boundedProgram M) head z ≃
      SemanticLeaves (boundedProgram M) z :=
  finiteLeavesEquiv (boundedProgram M) (scanner_terminal_table M) head z

end PakFixedPolyomino.ULogFiniteProgramZipperRunBridge
