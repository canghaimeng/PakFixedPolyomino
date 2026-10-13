import PakFixedPolyomino.StandardBitUnaryBudgetCleanup

/-! The budget induction, with the two physical borrow runs still explicit.
The induction runs over literal answer cells, never the counter's numeric value.
The closed comparator must instantiate both hypotheses with proved runs. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetLoop
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitUnaryBudgetCompare
open StandardBitUnaryBudgetSetup (setup_budget_run seek_L)
open StandardBitUnaryBudgetCleanup (exhausted_false_run underflow_true_run)
open StandardBitPairProjection (natInt unpairBits_eq_some)
open StandardBitDecrementWord (borrowBits borrow_none_iff borrow_value borrow_length)
open StandardBitDecrementAlignment (value_eq_original)

set_option maxHeartbeats 800000

def entryTicks (x : List Bool) (k : Nat) : Nat := D x+2*k+3
def iterationTicks (x : List Bool) (k : Nat) : Nat := 2*D x+2*k+4
def iterationBound (x y : List Bool) : Nat := 2*D x+2*y.length+4
def cleanupTicks (x y : List Bool) : Nat := y.length+Eidx x y+3
def loopBound (x y : List Bool) (k : Nat) : Nat :=
  (y.length-k)*iterationBound x y+cleanupTicks x y

theorem reach_borrow (x y u : List Bool) (k : Nat) (hk : k<y.length) :
    run machine (ticks (entryTicks x k))
      ⟨8,natInt (D x+1),budgetTape x y k u⟩=
      some ⟨10,0,budgetTape x y (k+1) u⟩ := by
  have ht : entryTicks x k=k+1+(D x+k+2) := by unfold entryTicks;omega
  rw [ht,ticks_add,ticks_add,run_append,run_append,skip_consumed x y k u (by omega),
    Option.bind_some,run_ticks_one,consume_step x y k u hk,Option.bind_some]
  exact seek_L x y u k

variable
  (hsuccess : ∀ (x y u v : List Bool) (k : Nat), k≤y.length → u.length=x.length →
    borrowBits u=some v →
    run machine (ticks (D x+1)) ⟨10,0,budgetTape x y k u⟩=
      some ⟨8,natInt (D x+1),budgetTape x y k v⟩)
  (hunderflow : ∀ (x y u : List Bool) (k : Nat), k≤y.length → u.length=x.length →
    borrowBits u=none →
    run machine (ticks (D x+1)) ⟨10,0,budgetTape x y k u⟩=
      some ⟨13,natInt (D x+1),Function.update
        (budgetTape x y k (List.replicate x.length true)) (natInt (D x)) 2⟩)

include hsuccess in
theorem successful_iteration (x y u v : List Bool) (k : Nat)
    (hk : k<y.length) (hw : u.length=x.length) (hb : borrowBits u=some v) :
    run machine (ticks (iterationTicks x k))
      ⟨8,natInt (D x+1),budgetTape x y k u⟩=
      some ⟨8,natInt (D x+1),budgetTape x y (k+1) v⟩ := by
  have ht : iterationTicks x k=entryTicks x k+(D x+1) := by
    unfold iterationTicks entryTicks;omega
  rw [ht,ticks_add,run_append,reach_borrow x y u k hk,Option.bind_some]
  exact hsuccess x y u v (k+1) (by omega) hw hb

include hunderflow in
theorem underflow_iteration (x y u : List Bool) (k : Nat)
    (hk : k<y.length) (hw : u.length=x.length) (hb : borrowBits u=none) :
    run machine (ticks (iterationTicks x k+cleanupTicks x y))
      ⟨8,natInt (D x+1),budgetTape x y k u⟩=some (finalConfig true) := by
  have ht : iterationTicks x k=entryTicks x k+(D x+1) := by
    unfold iterationTicks entryTicks;omega
  rw [ht,ticks_add,ticks_add,run_append,run_append,reach_borrow x y u k hk,
    Option.bind_some,hunderflow x y u (k+1) (by omega) hw hb,Option.bind_some]
  exact underflow_true_run x y (k+1) (by omega)

include hsuccess hunderflow
theorem budget_loop (x y u : List Bool) (k : Nat)
    (hk : k≤y.length) (hw : u.length=x.length)
    (hv : PakFixedWeightedStandardBinaryCount.value u+k=
      PakFixedWeightedStandardBinaryCount.value x) :
    ∃ n≤loopBound x y k,
      run machine (ticks n) ⟨8,natInt (D x+1),budgetTape x y k u⟩=
        some (finalConfig (decide (PakFixedWeightedStandardBinaryCount.value x<y.length))) := by
  have hmain : ∀ m k u, y.length-k=m → k≤y.length → u.length=x.length →
      PakFixedWeightedStandardBinaryCount.value u+k=PakFixedWeightedStandardBinaryCount.value x →
      ∃ n≤loopBound x y k,
        run machine (ticks n) ⟨8,natInt (D x+1),budgetTape x y k u⟩=
          some (finalConfig (decide (PakFixedWeightedStandardBinaryCount.value x<y.length))) := by
    intro m
    induction m with
    | zero =>
      intro k u hm hk hw hv
      have he : k=y.length := by omega
      subst k
      have hf : ¬ PakFixedWeightedStandardBinaryCount.value x<y.length := by omega
      refine ⟨cleanupTicks x y, by simp [loopBound], ?_⟩
      simpa only [cleanupTicks,decide_eq_false hf] using exhausted_false_run x y u
    | succ m ih =>
      intro k u hm hk hw hv
      have hlt : k<y.length := by omega
      have hstep : iterationTicks x k ≤ iterationBound x y := by
        unfold iterationTicks iterationBound;omega
      cases hb : borrowBits u with
      | none =>
        have hz := (borrow_none_iff u).mp hb
        rw [value_eq_original] at hz
        have ht : PakFixedWeightedStandardBinaryCount.value x<y.length := by omega
        refine ⟨iterationTicks x k+cleanupTicks x y, ?_, ?_⟩
        · unfold loopBound
          have hp : 1≤y.length-k := by omega
          nlinarith
        · simpa only [decide_eq_true ht] using underflow_iteration hunderflow x y u k hlt hw hb
      | some v =>
        have hlen := borrow_length hb
        have hval := borrow_value hb
        rw [value_eq_original,value_eq_original] at hval
        have hnext : y.length-(k+1)=m := by omega
        obtain ⟨n,hn,hrun⟩ := ih (k+1) v hnext (by omega)
          (by omega) (by omega)
        refine ⟨iterationTicks x k+n, ?_, ?_⟩
        · unfold loopBound at hn ⊢
          have hsub : y.length-k=(y.length-(k+1))+1 := by omega
          rw [hsub]
          nlinarith
        · rw [ticks_add,run_append,successful_iteration hsuccess x y u v k hlt hw hb,
            Option.bind_some,hrun]
  exact hmain (y.length-k) k u rfl hk hw hv

omit hsuccess hunderflow in
theorem pair_bound (x y : List Bool) :
    2*x.length+2*y.length+5+loopBound x y 0≤
      128*((pairBits x y).length+1)*((pairBits x y).length+1) := by
  rw [pairBits_length]
  unfold loopBound iterationBound cleanupTicks D Eidx
  simp only [Nat.sub_zero]
  nlinarith

theorem initialized_pair (x y : List Bool) :
    ∃ n≤128*((pairBits x y).length+1)*((pairBits x y).length+1),
      run machine (ticks n) (initial machine (pairBits x y))=
        some (finalConfig (decide (PakFixedWeightedStandardBinaryCount.value x<y.length))) := by
  obtain ⟨n,hn,hrun⟩ := budget_loop hsuccess hunderflow x y x 0 (Nat.zero_le _) rfl (by omega)
  refine ⟨2*x.length+2*y.length+5+n, (Nat.add_le_add_left hn _).trans (pair_bound x y), ?_⟩
  rw [ticks_add,run_append,setup_budget_run x y,Option.bind_some,hrun]

theorem compare_computes :
    ComputesWithin machine compareBits (fun n => 128*(n+1)*(n+1)) := by
  intro w
  cases hp : unpairBits w with
  | none =>
    obtain ⟨n,hn,hrun,hout⟩ := mal_output w hp
    exact ⟨n,finalConfig false,hn,hrun,hout⟩
  | some p =>
    rcases p with ⟨x,y⟩
    have he := unpairBits_eq_some.mp hp
    subst w
    obtain ⟨n,hn,hrun⟩ := initialized_pair hsuccess hunderflow x y
    refine ⟨n,_,hn,hrun,?_⟩
    rw [compare_pair]
    exact output_final _

theorem compare_polyBitTime : PolyBitTime compareBits := by
  refine ⟨19,8,machine,Polynomial.C 128*(Polynomial.X+1)*(Polynomial.X+1),?_⟩
  simpa using compare_computes hsuccess hunderflow

end PakFixedPolyomino.StandardBitUnaryBudgetLoop
