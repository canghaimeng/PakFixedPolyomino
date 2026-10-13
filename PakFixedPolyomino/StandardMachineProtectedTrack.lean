import PakFixedPolyomino.StandardNondeterministicMachine
import Mathlib.Logic.Equiv.Fin.Basic

/-! Ordinary finite product-alphabet compiler that preserves a passive tape track. -/
namespace PakFixedPolyomino.StandardMachineProtectedTrack

open StandardNondeterministicMachine
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (moveHead writtenTape)

variable {ns nt nr branching : ℕ}

def pack (r : Fin nr) (a : Fin nt) : Fin (nr * nt) :=
  finProdFinEquiv (r, a)

def unpack (s : Fin (nr * nt)) : Fin nr × Fin nt :=
  finProdFinEquiv.symm s

@[simp] theorem unpack_pack (r : Fin nr) (a : Fin nt) :
    unpack (pack r a) = (r, a) :=
  finProdFinEquiv.symm_apply_apply _

@[simp] theorem pack_unpack (s : Fin (nr * nt)) :
    pack (unpack s).1 (unpack s).2 = s := by
  change finProdFinEquiv (finProdFinEquiv.symm s) = s
  exact finProdFinEquiv.apply_symm_apply s

theorem pack_inj_right {r : Fin nr} {a b : Fin nt}
    (h : pack r a = pack r b) : a = b :=
  congrArg Prod.snd (finProdFinEquiv.injective h)

def protectRule (M : Machine ns nt branching) (q : Fin ns)
    (s : Fin (nr * nt)) (slot : Fin branching) :
    Option (Action (Fin ns) (Fin (nr * nt))) :=
  (M.rule q (unpack s).2 slot).map fun a =>
    ⟨pack (unpack s).1 a.write, a.target, a.move⟩

def protect (M : Machine ns nt branching) (rawBlank : Fin nr) :
    Machine ns (nr * nt) branching where
  rule := protectRule M
  start := M.start
  accept := M.accept
  reject := M.reject
  accept_ne_reject := M.accept_ne_reject
  blank := pack rawBlank M.blank
  zero := pack rawBlank M.zero
  one := pack rawBlank M.one
  blank_ne_zero := fun h => M.blank_ne_zero (pack_inj_right h)
  blank_ne_one := fun h => M.blank_ne_one (pack_inj_right h)
  zero_ne_one := fun h => M.zero_ne_one (pack_inj_right h)
  accept_terminal := by intro s slot; simp [protectRule, M.accept_terminal]
  reject_terminal := by intro s slot; simp [protectRule, M.reject_terminal]

@[simp] theorem protect_rule (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).rule = protectRule M := rfl
@[simp] theorem protect_start (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).start = M.start := rfl
@[simp] theorem protect_accept (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).accept = M.accept := rfl
@[simp] theorem protect_reject (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).reject = M.reject := rfl
@[simp] theorem protect_blank (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).blank = pack rawBlank M.blank := rfl
@[simp] theorem protect_zero (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).zero = pack rawBlank M.zero := rfl
@[simp] theorem protect_one (M : Machine ns nt branching) (rawBlank : Fin nr) :
    (protect M rawBlank).one = pack rawBlank M.one := rfl

theorem protectRule_pack (M : Machine ns nt branching) (q : Fin ns)
    (r : Fin nr) (a : Fin nt) (slot : Fin branching) :
    protectRule M q (pack r a) slot =
      (M.rule q a slot).map fun act => ⟨pack r act.write, act.target, act.move⟩ := by
  simp [protectRule]

def embed (R : Int → Fin nr) (c : Configuration ns nt) :
    Configuration ns (nr * nt) :=
  { state := c.state, head := c.head, tape := fun z => pack (R z) (c.tape z) }

def project (c : Configuration ns (nr * nt)) : Configuration ns nt :=
  { state := c.state, head := c.head, tape := fun z => (unpack (c.tape z)).2 }

@[simp] theorem project_embed (R : Int → Fin nr) (c : Configuration ns nt) :
    project (embed R c) = c := by
  cases c; simp [project, embed]

theorem embed_injective (R : Int → Fin nr) :
    Function.Injective (embed (ns := ns) (nt := nt) R) := by
  intro c d h
  simpa [project_embed] using congrArg project h

theorem embed_passive (R : Int → Fin nr) (c : Configuration ns nt) (z : Int) :
    (unpack ((embed R c).tape z)).1 = R z := by
  simp [embed]

theorem embed_written (R : Int → Fin nr) (c : Configuration ns nt) (w : Fin nt) :
    writtenTape (embed R c) (pack (R c.head) w) =
      fun z => pack (R z) (writtenTape c w z) := by
  funext z
  by_cases hz : z = c.head
  · subst hz; simp [writtenTape, embed]
  · simp [writtenTape, Function.update_of_ne hz, embed]

theorem config_ext {n m : ℕ} (c₁ c₂ : Configuration n m)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

theorem step_exact (M : Machine ns nt branching) (rawBlank : Fin nr)
    (R : Int → Fin nr) (slot : Fin branching) (c : Configuration ns nt) :
    step (protect M rawBlank) slot (embed R c) =
      (step M slot c).map (embed R) := by
  simp only [step, protect_rule]
  simp only [embed, protectRule_pack]
  cases M.rule c.state (c.tape c.head) slot with
  | none => simp
  | some a =>
      simp only [Option.map_some]
      apply congrArg some
      apply config_ext
      · rfl
      · rfl
      · exact embed_written R c a.write

theorem run_exact (M : Machine ns nt branching) (rawBlank : Fin nr)
    (R : Int → Fin nr) (slots : List (Fin branching)) (c : Configuration ns nt) :
    run (protect M rawBlank) slots (embed R c) =
      (run M slots c).map (embed R) := by
  induction slots generalizing c with
  | nil => simp
  | cons slot slots ih =>
      simp only [run_cons, step_exact]
      cases hs : step M slot c with
      | none => simp
      | some d => simp [ih]

theorem run_some_iff (M : Machine ns nt branching) (rawBlank : Fin nr)
    (R : Int → Fin nr) (slots : List (Fin branching))
    (c : Configuration ns nt) (out : Configuration ns (nr * nt)) :
    run (protect M rawBlank) slots (embed R c) = some out ↔
      ∃ d, run M slots c = some d ∧ out = embed R d := by
  constructor
  · intro h
    cases hd : run M slots c with
    | none =>
        have : run (protect M rawBlank) slots (embed R c) = none := by
          simp [run_exact, hd]
        simp [this] at h
    | some d =>
        refine ⟨d, rfl, ?_⟩
        have h' := h
        simp [run_exact, hd] at h'
        exact h'.symm
  · rintro ⟨d, hd, rfl⟩
    simp [run_exact, hd]

theorem passive_preserved (M : Machine ns nt branching) (rawBlank : Fin nr)
    (R : Int → Fin nr) (slots : List (Fin branching))
    (c : Configuration ns nt) (out : Configuration ns (nr * nt))
    (h : run (protect M rawBlank) slots (embed R c) = some out) :
    ∀ z : Int, (unpack (out.tape z)).1 = R z := by
  obtain ⟨d, -, rfl⟩ := (run_some_iff M rawBlank R slots c out).mp h
  exact embed_passive R d

theorem initial_eq (M : Machine ns nt branching) (rawBlank : Fin nr)
    (x : List Bool) :
    embed (fun _ => rawBlank) (initial M x) = initial (protect M rawBlank) x := by
  apply config_ext
  · simp [embed, initial]
  · simp [embed, initial]
  · funext z
    simp [embed, initial, inputTape]
    split_ifs <;> simp

theorem accepted_iff (M : Machine ns nt branching) (rawBlank : Fin nr)
    (x : List Bool) (slots : List (Fin branching)) :
    Accepted (protect M rawBlank) x slots ↔ Accepted M x slots := by
  unfold Accepted
  rw [← initial_eq M rawBlank x, run_exact, Option.map_map, protect_accept]
  simp [Function.comp, embed]

theorem runsAtMost_iff (M : Machine ns nt branching) (rawBlank : Fin nr)
    (x : List Bool) (bound : ℕ) :
    RunsAtMost (protect M rawBlank) x bound ↔ RunsAtMost M x bound := by
  constructor
  · intro h slots out hrun
    have : run (protect M rawBlank) slots (initial (protect M rawBlank) x) =
        some (embed (fun _ => rawBlank) out) := by
      simp [← initial_eq, run_exact, hrun]
    exact h slots _ this
  · intro h slots out hrun
    have hrun' :
        run (protect M rawBlank) slots
          (embed (fun _ => rawBlank) (initial M x)) = some out := by
      rwa [initial_eq]
    obtain ⟨d, hd, _⟩ :=
      (run_some_iff M rawBlank (fun _ => rawBlank) slots (initial M x) out).mp hrun'
    exact h slots d hd

def acceptingCode_id (M : Machine ns nt branching) (rawBlank : Fin nr)
    (x : List Bool) (bound : ℕ) :
    AcceptingCode (protect M rawBlank) x bound ≃ AcceptingCode M x bound where
  toFun code := ⟨code.val, (accepted_iff M rawBlank x code.val.toList).mp code.property⟩
  invFun code := ⟨code.val, (accepted_iff M rawBlank x code.val.toList).mpr code.property⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

theorem acceptingCount_eq (M : Machine ns nt branching) (rawBlank : Fin nr)
    (x : List Bool) (bound : ℕ) :
    acceptingCount (protect M rawBlank) x bound = acceptingCount M x bound :=
  Fintype.card_congr (acceptingCode_id M rawBlank x bound)

theorem protected_track_spec (M : Machine ns nt branching) (rawBlank : Fin nr)
    (R : Int → Fin nr) (c : Configuration ns nt) (slots : List (Fin branching)) :
    run (protect M rawBlank) slots (embed R c) = (run M slots c).map (embed R) ∧
      ∀ out, run (protect M rawBlank) slots (embed R c) = some out →
        (∃ d, run M slots c = some d ∧ out = embed R d) ∧
          ∀ z, (unpack (out.tape z)).1 = R z :=
  ⟨run_exact M rawBlank R slots c, fun out hout =>
    ⟨(run_some_iff M rawBlank R slots c out).mp hout,
      passive_preserved M rawBlank R slots c out hout⟩⟩

end PakFixedPolyomino.StandardMachineProtectedTrack
