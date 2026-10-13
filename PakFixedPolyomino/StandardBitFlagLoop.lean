import PakFixedPolyomino.StandardBitFlagLoopCycle
import PakFixedPolyomino.StandardBitTimeComposition

/-! A fixed finite tape machine executes a flag-controlled bounded iteration.
The semantic iteration and intermediate-word bounds are explicit hypotheses
of this generic compiler. They must be proved separately for a concrete DP.
Every runtime unit below counts actual transitions, including flag stripping.
-/
namespace PakFixedPolyomino.StandardBitFlagLoop
open StandardNondeterministicMachine StandardBitTime
open StandardBitFlagLoopCycle (machine startConfig finalConfig cycle_run initial_eq final_output)
variable {ns nt : Nat}

/-- One body call produces flag :: payload; true repeats on payload and false
halts with payload. L bounds every input word supplied to the body. -/
inductive Eval (f : List Bool → List Bool) (L : Nat) : List Bool → List Bool → Nat → Prop
  | stop {x : List Bool} (hlen : x.length ≤ L) (hflag : (f x).headD false = false) :
      Eval f L x (f x).tail 1
  | next {x y : List Bool} {k : Nat} (hlen : x.length ≤ L)
      (hflag : (f x).headD false = true) (rest : Eval f L (f x).tail y k) :
      Eval f L x y (k+1)

def cycleBound (p : Nat → Nat) (L : Nat) : Nat := 5*p L+4*L+11

theorem eval_run (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (L : Nat)
    (hp : ∀ a, a ≤ L → p a ≤ p L) {x y : List Bool} {k : Nat}
    (h : Eval f L x y k) :
    ∃ t, t ≤ k*cycleBound p L ∧
      run (machine M) (ticks t) (startConfig M x) = some (finalConfig M y) := by
  induction h with
  | @stop x hlen hflag =>
    obtain ⟨t,ht,hr⟩ := cycle_run M f p hf x
    have hpx := hp x.length hlen
    refine ⟨t,?_,?_⟩
    · simp only [Nat.one_mul,cycleBound]
      omega
    · simpa only [hflag,Bool.false_eq_true,if_false] using hr
  | @next x y k hlen hflag rest ih =>
    obtain ⟨a,ha,hr⟩ := cycle_run M f p hf x
    obtain ⟨b,hb,hs⟩ := ih
    have hpx := hp x.length hlen
    have hac : a ≤ cycleBound p L := by unfold cycleBound;omega
    refine ⟨a+b,?_,?_⟩
    · calc
        a+b ≤ cycleBound p L+k*cycleBound p L := Nat.add_le_add hac hb
        _ = (k+1)*cycleBound p L := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
    · have hr' : run (machine M) (ticks a) (startConfig M x) =
          some (startConfig M (f x).tail) := by
        simpa only [hflag,ite_true] using hr
      rw [ticks_add,run_append,hr',Option.bind_some]
      exact hs

noncomputable def loopBound (p lengthBound iterations : Polynomial Nat) : Polynomial Nat :=
  iterations * (5 * p.comp lengthBound + 4 * lengthBound + 11)

theorem loopBound_eval (p lengthBound iterations : Polynomial Nat) (n : Nat) :
    (loopBound p lengthBound iterations).eval n =
      iterations.eval n * cycleBound (fun a => p.eval a) (lengthBound.eval n) := by
  simp [loopBound,cycleBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp]

/-- The same finite machine works for every input and every iteration bound.
The hypotheses here describe the pure iteration, not assumed tape executions. -/
theorem computes (M : DeterministicMachine ns nt) (f g : List Bool → List Bool)
    (p lengthBound iterations : Polynomial Nat)
    (hf : ComputesWithin M f (fun a => p.eval a))
    (hiteration : ∀ x, ∃ k, Eval f (lengthBound.eval x.length) x (g x) k ∧
      k ≤ iterations.eval x.length) :
    ComputesWithin (machine M) g (fun n => (loopBound p lengthBound iterations).eval n) := by
  intro x
  obtain ⟨k,hk,hbound⟩ := hiteration x
  obtain ⟨t,ht,hr⟩ := eval_run M f _ hf _
    (fun _ h => StandardBitTimeComposition.eval_mono p h) hk
  refine ⟨t,finalConfig M (g x),?_,?_,final_output M (g x)⟩
  · change t ≤ (loopBound p lengthBound iterations).eval x.length
    rw [loopBound_eval]
    exact ht.trans (Nat.mul_le_mul_right _ hbound)
  · rw [initial_eq]
    exact hr

theorem polyBitTime (f g : List Bool → List Bool) (hf : PolyBitTime f)
    (lengthBound iterations : Polynomial Nat)
    (hiteration : ∀ x, ∃ k, Eval f (lengthBound.eval x.length) x (g x) k ∧
      k ≤ iterations.eval x.length) : PolyBitTime g := by
  obtain ⟨ns,nt,M,p,hM⟩ := hf
  exact ⟨ns+25,nt+7,machine M,loopBound p lengthBound iterations,
    computes M f g p lengthBound iterations hM hiteration⟩

end PakFixedPolyomino.StandardBitFlagLoop
