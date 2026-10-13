import PakFixedPolyomino.FloorReadout
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import Mathlib.Tactic

namespace PakFixedPolyomino

open Computability

noncomputable section

/-- Binary strings are the inputs used in the complexity statement. -/
abbrev BitString := List Bool

/-- A finite-branching nondeterministic binary machine interface.  Duplicate
entries of `next c` are distinct nondeterministic choices and are intentionally
counted with multiplicity. -/
structure BinaryNondeterministicMachine where
  Config : Type
  start : BitString → Config
  next : Config → List Config
  halt : Config → Bool
  accept : Config → Bool
  accept_halts : ∀ c, accept c = true → halt c = true
  binary_branching : ∀ c, (next c).length ≤ 2

namespace BinaryNondeterministicMachine

/-- A halted accepting configuration contributes once for every remaining
budget; a nonhalting configuration branches once.  Consequently a halting run
is never counted again at later clock ticks. -/
def acceptingPaths (M : BinaryNondeterministicMachine) : ℕ → M.Config → ℕ
  | 0, c => if M.halt c then if M.accept c then 1 else 0 else 0
  | t + 1, c =>
      if M.halt c then
        if M.accept c then 1 else 0
      else
        ((M.next c).map (acceptingPaths M t)).sum

@[simp] theorem acceptingPaths_halt_accept (M : BinaryNondeterministicMachine)
    {c : M.Config} (hh : M.halt c = true) (ha : M.accept c = true) (t : ℕ) :
    M.acceptingPaths t c = 1 := by
  cases t <;> simp [acceptingPaths, hh, ha]

@[simp] theorem acceptingPaths_halt_reject (M : BinaryNondeterministicMachine)
    {c : M.Config} (hh : M.halt c = true) (ha : M.accept c = false) (t : ℕ) :
    M.acceptingPaths t c = 0 := by
  cases t <;> simp [acceptingPaths, hh, ha]

theorem acceptingPaths_succ_nonhalt (M : BinaryNondeterministicMachine)
    {c : M.Config} (hh : M.halt c = false) (t : ℕ) :
    M.acceptingPaths (t + 1) c = ((M.next c).map (M.acceptingPaths t)).sum := by
  simp [acceptingPaths, hh]

/-- Binary branching gives the expected universal accepting-path bound. -/
theorem acceptingPaths_le_two_pow (M : BinaryNondeterministicMachine)
    (t : ℕ) (c : M.Config) : M.acceptingPaths t c ≤ 2 ^ t := by
  induction t generalizing c with
  | zero =>
      unfold acceptingPaths
      by_cases hh : M.halt c = true
      · by_cases ha : M.accept c = true <;> simp [hh, ha]
      · simp [hh]
  | succ t ih =>
      by_cases hh : M.halt c = true
      · by_cases ha : M.accept c = true
        · simp [acceptingPaths, hh, ha]
          exact Nat.one_le_iff_ne_zero.mpr (by positivity)
        · have ha' : M.accept c = false := by
            cases h : M.accept c <;> simp_all
          simp [acceptingPaths, hh, ha']
      · have hh' : M.halt c = false := by
          cases h : M.halt c <;> simp_all
        rw [acceptingPaths_succ_nonhalt M hh']
        have list_bound : ∀ qs : List M.Config,
            (qs.map (M.acceptingPaths t)).sum ≤ qs.length * 2 ^ t := by
          intro qs
          induction qs with
          | nil => simp
          | cons q qs ihqs =>
              simp only [List.map_cons, List.sum_cons, List.length_cons]
              calc
                M.acceptingPaths t q + (qs.map (M.acceptingPaths t)).sum
                    ≤ 2 ^ t + qs.length * 2 ^ t := Nat.add_le_add (ih q) ihqs
                _ = (qs.length + 1) * 2 ^ t := by ring
        have hsum : ((M.next c).map (M.acceptingPaths t)).sum ≤
            (M.next c).length * 2 ^ t := list_bound (M.next c)
        calc
          ((M.next c).map (M.acceptingPaths t)).sum
              ≤ (M.next c).length * 2 ^ t := hsum
          _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_right _ (M.binary_branching c)
          _ = 2 ^ (t + 1) := by rw [pow_succ]; ring

def countOn (M : BinaryNondeterministicMachine) (clock : ℕ → ℕ)
    (x : BitString) : ℕ := M.acceptingPaths (clock x.length) (M.start x)

theorem countOn_le (M : BinaryNondeterministicMachine) (clock : ℕ → ℕ)
    (x : BitString) : M.countOn clock x ≤ 2 ^ clock x.length :=
  M.acceptingPaths_le_two_pow _ _

end BinaryNondeterministicMachine

/-- A clock bounded by `2^(p(n))` for an explicit natural-coefficient
polynomial. -/
def ExponentialClock (clock : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, clock n ≤ 2 ^ p.eval n

/-- Mathlib currently provides a deterministic finite TM2 model and
time-bounded polynomial computations, but not a nondeterministic accepting-run
counter.  This structure connects the deterministic subroutines of our
nondeterministic interface to that existing model. -/
structure EffectiveBinaryNDTM extends BinaryNondeterministicMachine where
  configEncoding : Encoding Config Bool
  successorEncoding : Encoding (List Config) Bool
  start_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime id configEncoding.encode start)
  next_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime configEncoding.encode successorEncoding.encode next)
  halt_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime configEncoding.encode encodeBool halt)
  accept_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime configEncoding.encode encodeBool accept)
  start_size : ∃ p : Polynomial ℕ, ∀ x,
    (configEncoding.encode (start x)).length ≤ p.eval x.length
  local_growth : ∃ c : ℕ, ∀ q r, r ∈ next q →
    (configEncoding.encode r).length ≤ (configEncoding.encode q).length + c

/-- The strongest machine-counting class supported by the present library
without silently assuming a compiler from the interface above to a standard
single-step nondeterministic Turing machine. -/
def SharpEXPInterface (f : BitString → ℕ) : Prop :=
  ∃ M : EffectiveBinaryNDTM, ∃ clock : ℕ → ℕ,
    ExponentialClock clock ∧ ∀ x, f x = M.toBinaryNondeterministicMachine.countOn clock x

/-- A transparent membership certificate for a concrete counting function. -/
structure SharpEXPCertificate (f : BitString → ℕ) where
  machine : EffectiveBinaryNDTM
  clock : ℕ → ℕ
  clock_exp : ExponentialClock clock
  count_correct : ∀ x,
    f x = machine.toBinaryNondeterministicMachine.countOn clock x

theorem SharpEXPCertificate.mem {f : BitString → ℕ}
    (C : SharpEXPCertificate f) : SharpEXPInterface f :=
  ⟨C.machine, C.clock, C.clock_exp, C.count_correct⟩

/-- A fixed finite tile verifier is represented by the exact equivalence
between its valid geometric tilings and the accepting paths of one effective
machine.  Constructing this certificate for the concrete polyomino set is the
remaining implementation task; the theorem below does not conceal it. -/
structure FiniteTileVerifierCertificate
    (squareTilingCount : BitString → ℕ) extends SharpEXPCertificate squareTilingCount

theorem finite_tile_count_mem_interface {squareTilingCount : BitString → ℕ}
    (C : FiniteTileVerifierCertificate squareTilingCount) :
    SharpEXPInterface squareTilingCount := C.toSharpEXPCertificate.mem

/-- Semantic part of a one-query metric reduction. -/
structure BinaryMetricReduction (f g : BitString → ℕ) where
  instanceMap : BitString → BitString
  postprocess : BitString → ℕ → ℕ
  correct : ∀ x, f x = postprocess x (g (instanceMap x))

/-- A metric reduction carrying actual Mathlib TM2 polynomial-time
certificates for both maps.  The postprocessor encoding is explicit, because
the standard library has no canonical self-delimiting encoding of
`BitString × ℕ` into bits. -/
structure EffectiveBinaryMetricReduction (f g : BitString → ℕ)
    extends BinaryMetricReduction f g where
  pairEncoding : Encoding (BitString × ℕ) Bool
  instance_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime id id instanceMap)
  postprocess_polytime : Nonempty
    (Turing.TM2ComputableInPolyTime pairEncoding.encode encodingNatBool.encode
      (fun z => postprocess z.1 z.2))

def EffectiveReduces (f g : BitString → ℕ) : Prop :=
  Nonempty (EffectiveBinaryMetricReduction f g)

/-- The exact closure obligation missing from Mathlib's current TM2
polynomial-time development.  Supplying it makes reduction transitivity an
ordinary theorem rather than an implicit complexity assumption. -/
def EffectiveMetricComposition : Prop :=
  ∀ f g h : BitString → ℕ,
    EffectiveReduces f g → EffectiveReduces g h → EffectiveReduces f h

def EffectiveHardFor (Class : (BitString → ℕ) → Prop)
    (g : BitString → ℕ) : Prop :=
  ∀ f, Class f → EffectiveReduces f g

def EffectiveCompleteFor (Class : (BitString → ℕ) → Prop)
    (g : BitString → ℕ) : Prop :=
  Class g ∧ EffectiveHardFor Class g

theorem effective_hard_transfer
    {Class : (BitString → ℕ) → Prop} {source target : BitString → ℕ}
    (hcomp : EffectiveMetricComposition)
    (hsource : EffectiveHardFor Class source)
    (hst : EffectiveReduces source target) :
    EffectiveHardFor Class target := by
  intro f hf
  exact hcomp f source target (hsource f hf) hst

theorem effective_complete_of_source
    {Class : (BitString → ℕ) → Prop} {source target : BitString → ℕ}
    (hcomp : EffectiveMetricComposition)
    (hsource : EffectiveHardFor Class source)
    (hst : EffectiveReduces source target)
    (htarget : Class target) :
    EffectiveCompleteFor Class target := by
  exact ⟨htarget, effective_hard_transfer hcomp hsource hst⟩

/-- The algebraic floor map used by the geometric reduction.  Polynomial-time
implementability is deliberately not asserted here; it belongs in an
`EffectiveBinaryMetricReduction` certificate. -/
def floorPostprocess (scale exponent : BitString → ℕ)
    (x : BitString) (y : ℕ) : ℕ := y / scale x ^ exponent x

theorem floor_postprocess_correct
    {source target scale exponent junk : BitString → ℕ}
    (hscale : ∀ x, 0 < scale x)
    (hcount : ∀ x, target x = scale x ^ exponent x * source x + junk x)
    (hjunk : ∀ x, junk x < scale x ^ exponent x) :
    ∀ x, source x = floorPostprocess scale exponent x (target x) := by
  intro x
  exact (floor_readout (hscale x) (hcount x) (hjunk x)).symm

/-- Final honest assembly theorem.  It consumes, rather than fabricates, the
three machine-level certificates still required by the full formalization. -/
theorem final_effective_complexity_assembly
    {source poly : BitString → ℕ}
    (hcomp : EffectiveMetricComposition)
    (hsource : EffectiveHardFor SharpEXPInterface source)
    (hgeometry : EffectiveReduces source poly)
    (hmembership : FiniteTileVerifierCertificate poly) :
    EffectiveCompleteFor SharpEXPInterface poly := by
  exact effective_complete_of_source hcomp hsource hgeometry
    (finite_tile_count_mem_interface hmembership)

end
end PakFixedPolyomino
