import PakFixedPolyomino.ULogSourceObliviousInitialZipper
import PakFixedPolyomino.ULogFiniteProgramZipperRunBridge
import PakFixedPolyomino.ULogSourceObliviousRunTime

/-! Ordinary source acceptingCount equals genuine ULogSemantics.machine.acceptingPaths
at the internally derived scannerBudget, from the materialized zipper initializer.
ALL successful semantic prefixes are bounded; cutoff multiplicities are internal.
Compact startup/loading and the original Pak headline remain open. -/

namespace PakFixedPolyomino.ULogSourceObliviousSemanticAcceptance

open StandardNondeterministicMachine
open ULogCompiler
open ULogFiniteProgramZipperRunBridge
open ULogSourceObliviousBytecode
open ULogSourceObliviousBytecodeRunBridge
open ULogSourceObliviousInitialZipper
open ULogSourceObliviousRunTime
open ULogSourceObliviousUpdateExecution (physBlank)
open ULogSourceObliviousHaltingProgram
open ULogSourceObliviousInitialWindowExecution (initialWindowConfig)
open StandardMachineWindowBridge (inputWindow)
open StandardMachineZipperBridge (physical)
open FiniteOneTapeProgram (Arrow)
open FiniteOneTapeSemantics (run)

variable {ns nt : Nat}

noncomputable def initialSemantic (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) : ULogSemantics.Config :=
  liftConfig (boundedProgram M)
    (initialZipper M (inputWindow M x bound))

def scannerBudget (nt : Nat) (x : List Bool) (bound : Nat) : Nat :=
  (bound + 1) * (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6)

theorem ordinary_leaf_count_semantic (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound) :
    acceptingCount M x bound =
      Nat.card (SemanticLeaves (boundedProgram M)
        (initialZipper M (inputWindow M x bound))) := by
  rw [ordinary_leaf_count_initialZipper M x bound htime]
  exact Nat.card_congr
    (scannerLeavesEquiv M 0 (initialZipper M (inputWindow M x bound)))

theorem all_semantic_runs_length_le (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound)
    (slots : List Bool) (out : ULogSemantics.Config)
    (hsem : semanticRun (initialSemantic M x bound) slots = some out) :
    slots.length ≤ scannerBudget nt x bound := by
  let p := boundedProgram M
  let z := initialZipper M (inputWindow M x bound)
  have hmap :
      (zipperSlotRun p slots 0 z).map (fun hz => liftConfig p hz.2) = some out := by
    simpa [initialSemantic, zipperSlotRun_lift] using hsem
  obtain ⟨hz, hzip, _⟩ := Option.map_eq_some_iff.mp hmap
  obtain ⟨word, _, hlen, hrun⟩ :=
    successful_zipper_to_arrows p slots 0 z hz.1 hz.2 hzip
  let haltWord := word.map (arrowEquiv M).symm
  have hrestore : haltWord.map (arrowEquiv M) = word :=
    map_arrowEquiv_right M word
  have hnum :
      run (numericalProgram M) (fun _ => true) (haltWord.map (arrowEquiv M))
        (encodeConfig M (initialWindowConfig M.start (inputWindow M x bound)
          (fun _ => physBlank))) =
        some (physical (2 : Fin 3) hz.1 hz.2) := by
    rw [hrestore, ← initialZipper_physical]
    exact hrun
  have hhaltmap :
      (run (haltProgram M) (fun _ => true) haltWord
        (initialWindowConfig M.start (inputWindow M x bound)
          (fun _ => physBlank))).map (encodeConfig M) =
        some (physical (2 : Fin 3) hz.1 hz.2) := by
    simpa [run_arrowEquiv] using hnum
  obtain ⟨outHalt, hhaltRun, _⟩ := Option.map_eq_some_iff.mp hhaltmap
  have hbound :=
    all_halt_runs_length_le M x bound htime (fun _ => physBlank)
      haltWord outHalt hhaltRun
  have hlenHalt : haltWord.length = word.length := by
    dsimp [haltWord]
    exact List.length_map (arrowEquiv M).symm
  exact (hlenHalt.trans hlen).symm ▸ hbound

def SemanticCutoff (c : ULogSemantics.Config) (T : Nat) :=
  {slots : List Bool //
    (∃ out, semanticRun c slots = some out ∧ out.state = 0) ∧
      slots.length ≤ T}

theorem semanticRun_nil (c : ULogSemantics.Config) :
    semanticRun c [] = some c := rfl

theorem semanticRun_cons (c : ULogSemantics.Config) (slot : Bool)
    (rest : List Bool) :
    semanticRun c (slot :: rest) =
      (ULogSemantics.stepSlot slot c).bind (fun c' => semanticRun c' rest) :=
  rfl

theorem accepting_state (c : ULogSemantics.Config) :
    ULogSemantics.accepting c = true ↔ c.state = 0 := by
  constructor
  · intro h
    simp [ULogSemantics.accepting, ULogSemantics.acceptCode] at h
    exact of_decide_eq_true h
  · intro h
    simp [ULogSemantics.accepting, ULogSemantics.acceptCode, h]

theorem nonempty_of_halted {c : ULogSemantics.Config} {slot : Bool}
    {rest : List Bool} (hh : ULogSemantics.halted c = true) :
    semanticRun c (slot :: rest) = none := by
  simp [semanticRun, ULogSemantics.stepSlot, hh]

theorem not_halted_state_ne_zero {c : ULogSemantics.Config}
    (hnh : ULogSemantics.halted c = false) : c.state ≠ 0 := by
  intro hs
  have : ULogSemantics.halted c = true := by
    simp [ULogSemantics.halted, hs]
  simp [this] at hnh

theorem step_of_cons {c out : ULogSemantics.Config} {slot : Bool}
    {rest : List Bool} (h : semanticRun c (slot :: rest) = some out) :
    ∃ c', ULogSemantics.stepSlot slot c = some c' ∧
      semanticRun c' rest = some out := by
  cases hstep : ULogSemantics.stepSlot slot c with
  | none => simp [semanticRun, hstep] at h
  | some c' =>
      refine ⟨c', rfl, ?_⟩
      simpa [semanticRun, hstep] using h

noncomputable def emptyCutoff (c : ULogSemantics.Config)
    (ha : ULogSemantics.accepting c = true) (T : Nat) :
    SemanticCutoff c T :=
  ⟨[], ⟨c, semanticRun_nil c, (accepting_state c).mp ha⟩, Nat.zero_le T⟩

@[reducible]
noncomputable def cutoff_accept_unique (c : ULogSemantics.Config)
    (ha : ULogSemantics.accepting c = true) (T : Nat) :
    Unique (SemanticCutoff c T) where
  default := emptyCutoff c ha T
  uniq s := by
    apply Subtype.ext
    cases hs : s.1 with
    | nil => rfl
    | cons slot rest =>
        obtain ⟨out, hrun, _⟩ := s.2.1
        have hh := ULogSemantics.accepting_halted ha
        simp [hs, nonempty_of_halted hh] at hrun

theorem cutoff_reject_empty (c : ULogSemantics.Config)
    (hh : ULogSemantics.halted c = true)
    (ha : ULogSemantics.accepting c = false) (T : Nat) :
    IsEmpty (SemanticCutoff c T) :=
  ⟨fun s => by
    obtain ⟨out, hrun, hacc⟩ := s.2.1
    cases hs : s.1 with
    | nil =>
        have hout : out = c :=
          (Option.some.inj (by simpa [semanticRun_nil, hs] using hrun)).symm
        have : ULogSemantics.accepting c = true :=
          (accepting_state c).mpr (by simpa [hout] using hacc)
        simp [this] at ha
    | cons slot rest =>
        simp [hs, nonempty_of_halted hh] at hrun⟩

theorem cutoff_zero_nonaccept (c : ULogSemantics.Config)
    (ha : ULogSemantics.accepting c = false) :
    IsEmpty (SemanticCutoff c 0) :=
  ⟨fun s => by
    have hnil : s.1 = [] :=
      List.eq_nil_of_length_eq_zero (Nat.le_zero.mp s.2.2)
    obtain ⟨out, hrun, hacc⟩ := s.2.1
    have hout : out = c :=
      (Option.some.inj (by simpa [semanticRun_nil, hnil] using hrun)).symm
    have : ULogSemantics.accepting c = true :=
      (accepting_state c).mpr (by simpa [hout] using hacc)
    simp [this] at ha⟩

theorem empty_not_in_nonhalt {c : ULogSemantics.Config} {T : Nat}
    (hnh : ULogSemantics.halted c = false)
    (s : SemanticCutoff c T) : s.1 ≠ [] := by
  intro hnil
  obtain ⟨out, hrun, hacc⟩ := s.2.1
  have hout : out = c :=
    (Option.some.inj (by simpa [semanticRun_nil, hnil] using hrun)).symm
  exact not_halted_state_ne_zero hnh (by simpa [hout] using hacc)

def TailsAfter (c : ULogSemantics.Config) (T : Nat) (slot : Bool) :=
  {rest : List Bool //
    (∃ c' out, ULogSemantics.stepSlot slot c = some c' ∧
      semanticRun c' rest = some out ∧ out.state = 0) ∧
    rest.length ≤ T}

theorem tails_none (c : ULogSemantics.Config) (T : Nat) (slot : Bool)
    (h : ULogSemantics.stepSlot slot c = none) :
    IsEmpty (TailsAfter c T slot) :=
  ⟨fun t => by
    obtain ⟨c', out, hc, _, _⟩ := t.2.1
    simp [h] at hc⟩

noncomputable def tailsEquiv (c : ULogSemantics.Config) (T : Nat)
    (slot : Bool) (c' : ULogSemantics.Config)
    (h : ULogSemantics.stepSlot slot c = some c') :
    TailsAfter c T slot ≃ SemanticCutoff c' T where
  toFun t :=
    ⟨t.1, by
      obtain ⟨⟨c'', out, hc, hrun, hacc⟩, hlen⟩ := t.2
      have hc' : c'' = c' := Option.some.inj (hc.symm.trans h)
      exact ⟨⟨out, hc' ▸ hrun, hacc⟩, hlen⟩⟩
  invFun s :=
    ⟨s.1, by
      obtain ⟨⟨out, hrun, hacc⟩, hlen⟩ := s.2
      exact ⟨⟨c', out, h, hrun, hacc⟩, hlen⟩⟩
  left_inv t := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

noncomputable def consToSum (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false)
    (s : SemanticCutoff c (T + 1)) :
    (slots : List Bool) → slots = s.1 →
      TailsAfter c T false ⊕ TailsAfter c T true
  | [], heq => False.elim (empty_not_in_nonhalt hnh s heq.symm)
  | false :: rest, heq =>
      Sum.inl ⟨rest, by
        obtain ⟨out, hrun, hacc⟩ := s.2.1
        have hrun' : semanticRun c (false :: rest) = some out := by
          simpa [heq] using hrun
        obtain ⟨c', hstep, hrest⟩ := step_of_cons hrun'
        refine ⟨⟨c', out, hstep, hrest, hacc⟩, ?_⟩
        have hlen := s.2.2
        rw [← heq] at hlen
        simp at hlen
        omega⟩
  | true :: rest, heq =>
      Sum.inr ⟨rest, by
        obtain ⟨out, hrun, hacc⟩ := s.2.1
        have hrun' : semanticRun c (true :: rest) = some out := by
          simpa [heq] using hrun
        obtain ⟨c', hstep, hrest⟩ := step_of_cons hrun'
        refine ⟨⟨c', out, hstep, hrest, hacc⟩, ?_⟩
        have hlen := s.2.2
        rw [← heq] at hlen
        simp at hlen
        omega⟩

noncomputable def toSuccSum (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false)
    (s : SemanticCutoff c (T + 1)) :
    TailsAfter c T false ⊕ TailsAfter c T true :=
  consToSum c T hnh s s.1 rfl

noncomputable def fromSuccSum (c : ULogSemantics.Config) (T : Nat)
    (x : TailsAfter c T false ⊕ TailsAfter c T true) :
    SemanticCutoff c (T + 1) :=
  match x with
  | Sum.inl t =>
      ⟨false :: t.1, by
        obtain ⟨⟨c', out, hstep, hrun, hacc⟩, hlen⟩ := t.2
        refine ⟨⟨out, ?_, hacc⟩, ?_⟩
        · simp [semanticRun, hstep, hrun]
        · simp
          omega⟩
  | Sum.inr t =>
      ⟨true :: t.1, by
        obtain ⟨⟨c', out, hstep, hrun, hacc⟩, hlen⟩ := t.2
        refine ⟨⟨out, ?_, hacc⟩, ?_⟩
        · simp [semanticRun, hstep, hrun]
        · simp
          omega⟩

theorem consToSum_elim (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false)
    (s : SemanticCutoff c (T + 1)) (slots : List Bool)
    (heq : slots = s.1) :
    Sum.elim (fun t : TailsAfter c T false => false :: t.1)
      (fun t : TailsAfter c T true => true :: t.1)
      (consToSum c T hnh s slots heq) = slots := by
  cases slots with
  | nil => exact (empty_not_in_nonhalt hnh s heq.symm).elim
  | cons slot rest =>
      cases slot <;> rfl

theorem toSuccSum_slots (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false)
    (s : SemanticCutoff c (T + 1)) :
    Sum.elim (fun t : TailsAfter c T false => false :: t.1)
      (fun t : TailsAfter c T true => true :: t.1)
      (toSuccSum c T hnh s) = s.1 :=
  consToSum_elim c T hnh s s.1 rfl

theorem toSuccSum_injective (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false) :
    Function.Injective (toSuccSum c T hnh) := by
  intro a b h
  apply Subtype.ext
  have ha := toSuccSum_slots c T hnh a
  have hb := toSuccSum_slots c T hnh b
  rw [← ha, ← hb, h]

theorem toSuccSum_fromSuccSum (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false)
    (x : TailsAfter c T false ⊕ TailsAfter c T true) :
    toSuccSum c T hnh (fromSuccSum c T x) = x := by
  cases x with
  | inl t =>
      apply congrArg Sum.inl
      exact Subtype.ext rfl
  | inr t =>
      apply congrArg Sum.inr
      exact Subtype.ext rfl

theorem toSuccSum_surjective (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false) :
    Function.Surjective (toSuccSum c T hnh) := by
  intro x
  exact ⟨fromSuccSum c T x, toSuccSum_fromSuccSum c T hnh x⟩

noncomputable def cutoffSuccEquiv (c : ULogSemantics.Config) (T : Nat)
    (hnh : ULogSemantics.halted c = false) :
    SemanticCutoff c (T + 1) ≃
      TailsAfter c T false ⊕ TailsAfter c T true :=
  Equiv.ofBijective (toSuccSum c T hnh)
    ⟨toSuccSum_injective c T hnh, toSuccSum_surjective c T hnh⟩

theorem tails_finite (c : ULogSemantics.Config) (T : Nat) (slot : Bool)
    (hfin : ∀ c', Finite (SemanticCutoff c' T)) :
    Finite (TailsAfter c T slot) := by
  cases h : ULogSemantics.stepSlot slot c with
  | none =>
      haveI := tails_none c T slot h
      infer_instance
  | some c' =>
      exact Finite.of_equiv _ (tailsEquiv c T slot c' h).symm

theorem tails_card (c : ULogSemantics.Config) (T : Nat) (slot : Bool)
    (_hfin : ∀ c', Finite (SemanticCutoff c' T)) :
    Nat.card (TailsAfter c T slot) =
      match ULogSemantics.stepSlot slot c with
      | none => 0
      | some c' => Nat.card (SemanticCutoff c' T) := by
  cases h : ULogSemantics.stepSlot slot c with
  | none =>
      haveI := tails_none c T slot h
      simp
  | some c' =>
      rw [Nat.card_congr (tailsEquiv c T slot c' h)]

theorem map_sum_nil (f : ULogSemantics.Config → ℕ) :
    (List.map f []).sum = 0 := rfl

theorem map_sum_one (f : ULogSemantics.Config → ℕ) (a : ULogSemantics.Config) :
    (List.map f [a]).sum = f a := by
  change f a + (List.map f []).sum = f a
  simp

theorem map_sum_two (f : ULogSemantics.Config → ℕ)
    (a b : ULogSemantics.Config) :
    (List.map f [a, b]).sum = f a + f b := by
  change f a + (f b + (List.map f []).sum) = f a + f b
  simp

theorem next_paths_sum (c : ULogSemantics.Config) (T : Nat)
    (ih : ∀ c', Nat.card (SemanticCutoff c' T) =
      ULogSemantics.machine.acceptingPaths T c') :
    ((ULogSemantics.next c).map
        (ULogSemantics.machine.acceptingPaths T)).sum =
      (match ULogSemantics.stepSlot false c with
        | none => 0
        | some c0 => Nat.card (SemanticCutoff c0 T)) +
      (match ULogSemantics.stepSlot true c with
        | none => 0
        | some c1 => Nat.card (SemanticCutoff c1 T)) := by
  cases hf : ULogSemantics.stepSlot false c <;>
    cases ht : ULogSemantics.stepSlot true c
  · simp [ULogSemantics.next, hf, ht]
    exact map_sum_nil _
  · simp [ULogSemantics.next, hf, ht, ih]
    exact map_sum_one _ _
  · simp [ULogSemantics.next, hf, ht, ih]
    exact map_sum_one _ _
  · simp [ULogSemantics.next, hf, ht, ih]
    exact map_sum_two _ _ _

theorem cutoff_finite_and_card (c : ULogSemantics.Config) (T : Nat) :
    Finite (SemanticCutoff c T) ∧
      Nat.card (SemanticCutoff c T) =
        ULogSemantics.machine.acceptingPaths T c := by
  induction T generalizing c with
  | zero =>
      cases ha : ULogSemantics.accepting c with
      | true =>
          letI := cutoff_accept_unique c ha 0
          refine ⟨Finite.of_subsingleton, ?_⟩
          have hh := ULogSemantics.accepting_halted ha
          simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine,
            hh, ha]
      | false =>
          letI := cutoff_zero_nonaccept c ha
          refine ⟨Finite.of_subsingleton, ?_⟩
          simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine,
            ha]
  | succ T ih =>
      cases hh : ULogSemantics.halted c with
      | true =>
          cases ha : ULogSemantics.accepting c with
          | true =>
              letI := cutoff_accept_unique c ha (T + 1)
              refine ⟨Finite.of_subsingleton, ?_⟩
              simp [BinaryNondeterministicMachine.acceptingPaths,
                ULogSemantics.machine, hh, ha]
          | false =>
              letI := cutoff_reject_empty c hh ha (T + 1)
              refine ⟨Finite.of_subsingleton, ?_⟩
              simp [BinaryNondeterministicMachine.acceptingPaths,
                ULogSemantics.machine, hh, ha]
      | false =>
          let e := cutoffSuccEquiv c T hh
          have hfin : ∀ c', Finite (SemanticCutoff c' T) := fun c' => (ih c').1
          haveI := tails_finite c T false hfin
          haveI := tails_finite c T true hfin
          haveI : Finite (SemanticCutoff c (T + 1)) := Finite.of_equiv _ e.symm
          refine ⟨inferInstance, ?_⟩
          have hcard := Nat.card_congr e
          rw [hcard, Nat.card_sum, tails_card c T false hfin,
            tails_card c T true hfin]
          have hpaths :=
            BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
              ULogSemantics.machine hh T
          rw [hpaths]
          exact (next_paths_sum c T (fun c' => (ih c').2)).symm

theorem cutoff_finite (c : ULogSemantics.Config) (T : Nat) :
    Finite (SemanticCutoff c T) :=
  (cutoff_finite_and_card c T).1

theorem cutoff_card (c : ULogSemantics.Config) (T : Nat) :
    Nat.card (SemanticCutoff c T) =
      ULogSemantics.machine.acceptingPaths T c :=
  (cutoff_finite_and_card c T).2

noncomputable def leavesCutoffEquiv (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound) :
    SemanticLeaves (boundedProgram M)
        (initialZipper M (inputWindow M x bound)) ≃
      SemanticCutoff (initialSemantic M x bound)
        (scannerBudget nt x bound) where
  toFun s :=
    ⟨s.1, s.2, by
      obtain ⟨out, hrun, _⟩ := s.2
      exact all_semantic_runs_length_le M x bound htime s.1 out hrun⟩
  invFun s := ⟨s.1, s.2.1⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

theorem ordinary_count_eq_semantic_acceptingPaths (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound) :
    acceptingCount M x bound =
      ULogSemantics.machine.acceptingPaths (scannerBudget nt x bound)
        (initialSemantic M x bound) := by
  rw [ordinary_leaf_count_semantic M x bound htime]
  rw [Nat.card_congr (leavesCutoffEquiv M x bound htime)]
  exact cutoff_card (initialSemantic M x bound) (scannerBudget nt x bound)

end PakFixedPolyomino.ULogSourceObliviousSemanticAcceptance
