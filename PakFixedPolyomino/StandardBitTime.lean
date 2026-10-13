import PakFixedPolyomino.StandardMachineRunResources

/-! # Bit time measured by ordinary deterministic tape transitions

A computation uses the branching-one instance of the ordinary source machine.
Its output is a binary word on the actual tape, with the head returned to zero
and all other cells blank. There are no arithmetic primitives, configuration
initializers, or external time certificates in this definition. Successful
termination implies the bound on every raw deterministic prefix internally.

This module does not assert polynomial-time composition or implement the Pak
metric maps. Those require concrete machines and their operational proofs.
-/

namespace PakFixedPolyomino.StandardBitTime

open StandardNondeterministicMachine

abbrev DeterministicMachine (ns nt : ℕ) := Machine ns nt 1

def ticks (n : ℕ) : List (Fin 1) := List.replicate n 0

@[simp] theorem ticks_length (n : ℕ) : (ticks n).length = n := by
  simp [ticks]

@[simp] theorem ticks_add (n m : ℕ) : ticks (n + m) = ticks n ++ ticks m := by
  exact List.replicate_add n m 0

theorem deterministic_word (slots : List (Fin 1)) : slots = ticks slots.length := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      have hslot : slot = 0 := Subsingleton.elim _ _
      change slot :: slots = 0 :: ticks slots.length
      rw [hslot]
      exact congrArg (List.cons 0) ih

variable {ns nt : ℕ}

@[simp] theorem run_ticks_one (M : DeterministicMachine ns nt)
    (c : Configuration ns nt) : run M (ticks 1) c = step M 0 c := by
  simp [ticks, run]

/-- Clean binary output on the entire physical tape, not an arbitrary decoder. -/
def Output (M : DeterministicMachine ns nt) (y : List Bool)
    (out : Configuration ns nt) : Prop :=
  out.state = M.accept ∧ out.head = 0 ∧ out.tape = inputTape M y

/-- Every counted tick is one actual write/move transition of the standard
finite machine. The output is its actual halting configuration. -/
def ComputesWithin (M : DeterministicMachine ns nt)
    (f : List Bool → List Bool) (bound : ℕ → ℕ) : Prop :=
  ∀ x, ∃ n out, n ≤ bound x.length ∧
    run M (ticks n) (initial M x) = some out ∧ Output M (f x) out

def PolyBitTime (f : List Bool → List Bool) : Prop :=
  ∃ (ns nt : ℕ) (M : DeterministicMachine ns nt) (p : Polynomial ℕ),
    ComputesWithin M f (fun n => p.eval n)

/-- A halting deterministic run bounds ALL successful raw prefixes. The
definition of bit time needs no separate, assumed runtime certificate. -/
theorem halting_runsAtMost (M : DeterministicMachine ns nt) (x : List Bool)
    (n : ℕ) (out : Configuration ns nt)
    (hrun : run M (ticks n) (initial M x) = some out)
    (haccept : out.state = M.accept) : RunsAtMost M x n := by
  apply (runsAtMost_iff_blocked_at_bound M x n).mpr
  intro slots middle hlen hmiddle
  have hslots : slots = ticks n := (deterministic_word slots).trans (by rw [hlen])
  have heq : out = middle := by
    rw [hslots, hrun] at hmiddle
    exact Option.some.inj hmiddle
  subst middle
  exact fun slot => step_accept_none M slot out haccept

theorem halting_run_unique (M : DeterministicMachine ns nt) (x : List Bool)
    (n m : ℕ) (out other : Configuration ns nt)
    (hrun : run M (ticks n) (initial M x) = some out)
    (haccept : out.state = M.accept)
    (hother : run M (ticks m) (initial M x) = some other)
    (hotherAccept : other.state = M.accept) : n = m ∧ out = other := by
  have hmn := halting_runsAtMost M x n out hrun haccept (ticks m) other hother
  have hnm := halting_runsAtMost M x m other hother hotherAccept (ticks n) out hrun
  simp only [ticks_length] at hmn hnm
  have hnmEq : n = m := by omega
  subst m
  rw [hrun] at hother
  exact ⟨rfl, Option.some.inj hother⟩

theorem ComputesWithin.actual_bounds (M : DeterministicMachine ns nt)
    (f : List Bool → List Bool) (bound : ℕ → ℕ)
    (hcompute : ComputesWithin M f bound) (x : List Bool) :
    RunsAtMost M x (bound x.length) ∧
    ∀ slots out, run M slots (initial M x) = some out →
      -(bound x.length : Int) ≤ out.head ∧
      out.head ≤ (bound x.length : Int) ∧
      ∀ z : Int, z < -(bound x.length : Int) ∨
        (x.length : Int) + (bound x.length : Int) + 1 ≤ z →
        out.tape z = M.blank := by
  obtain ⟨n, final, hn, hrun, hout⟩ := hcompute x
  have htime := halting_runsAtMost M x n final hrun hout.1
  have hbound : RunsAtMost M x (bound x.length) := by
    intro slots out hslots
    exact (htime slots out hslots).trans hn
  refine ⟨hbound, ?_⟩
  intro slots out hslots
  have hlen := hbound slots out hslots
  have hgeom := run_geometry M slots (initial M x) out hslots
  refine ⟨?_, ?_, ?_⟩
  · simp only [initial] at hgeom
    omega
  · simp only [initial] at hgeom
    omega
  · intro z hz
    apply initialized_run_exterior M x slots out hslots z
    rcases hz with hz | hz
    · left; omega
    · right; omega

/-- Output size is bounded by physical time and initialized input size.
In particular a natural number cannot be emitted in one unbounded tape cell. -/
theorem ComputesWithin.output_length (M : DeterministicMachine ns nt)
    (f : List Bool → List Bool) (bound : ℕ → ℕ)
    (hcompute : ComputesWithin M f bound) (x : List Bool) :
    (f x).length ≤ x.length + bound x.length + 1 := by
  obtain ⟨n, out, hn, hrun, hout⟩ := hcompute x
  by_contra hlong
  let k := x.length + bound x.length + 1
  have hk : k < (f x).length := by dsimp [k]; omega
  have hblank := initialized_run_exterior M x (ticks n) out hrun (k : Int)
    (Or.inr (by simp only [ticks_length]; dsimp [k]; omega))
  rw [hout.2.2, inputTape_ofNat M (f x) k hk] at hblank
  split at hblank
  · exact M.blank_ne_one hblank.symm
  · exact M.blank_ne_zero hblank.symm

/-- Identity halts immediately because its input already is its output. -/
def identityMachine : DeterministicMachine 2 3 where
  rule := fun _ _ _ => none
  start := 0
  accept := 0
  reject := 1
  accept_ne_reject := by decide
  blank := 2
  zero := 0
  one := 1
  blank_ne_zero := by decide
  blank_ne_one := by decide
  zero_ne_one := by decide
  accept_terminal := by intros; rfl
  reject_terminal := by intros; rfl

theorem identity_computes : ComputesWithin identityMachine id (fun _ => 0) := by
  intro x
  refine ⟨0, initial identityMachine x, by rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

theorem identity_polyBitTime : PolyBitTime id := by
  exact ⟨2, 3, identityMachine, 0, by simpa using identity_computes⟩

end PakFixedPolyomino.StandardBitTime
