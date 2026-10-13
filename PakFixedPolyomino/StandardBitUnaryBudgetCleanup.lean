import PakFixedPolyomino.StandardBitUnaryBudgetSetup

/-! Physical cleanup after exhausting the literal answer budget. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetCleanup
open StandardNondeterministicMachine StandardBitTime
open StandardBitUnaryBudgetCompare
open StandardBitUnaryBudgetSetup (budget_nat_ne_L)
open StandardBitPairProjection (natInt natInt_ne_neg1 natInt_inj)

theorem budget_far_blank (x y u : List Bool) (k : Nat) (hk : k ≤ y.length)
    (z : Int) (hp : 0 ≤ z) (hz : Eidx x y < z.toNat) : budgetTape x y k u z=2 := by
  have hL : z ≠ -1 := by omega
  unfold budgetTape
  rw [if_neg hL,dif_pos hp]
  unfold budgetNat
  have h1 : ¬ z.toNat < D x := by unfold Eidx D at*;omega
  have h2 : z.toNat ≠ D x := by unfold Eidx D at*;omega
  have h3 : ¬ z.toNat < D x+1+k := by unfold Eidx D at*;omega
  rw [if_neg h1,if_neg h2,if_neg h3,if_neg (by omega),if_neg (by omega)]

theorem budget_negative (x y u : List Bool) (k : Nat)
    (z : Int) (hz : z < 0) (hL : z ≠ -1) : budgetTape x y k u z=2 := by
  simp [budgetTape,hL,show ¬ 0 ≤ z by omega]

theorem erase_E_wipe (x y u : List Bool) (k : Nat) (hk : k ≤ y.length) :
    Function.update (budgetTape x y k u) (natInt (Eidx x y)) 2=
      wipe (budgetTape x y k u) (Eidx x y) := by
  funext z
  by_cases he : z=natInt (Eidx x y)
  · subst z
    have hL : natInt (Eidx x y) ≠ -1 := natInt_ne_neg1 _
    simp [wipe,hL,natInt]
  · rw [Function.update_of_ne he]
    unfold wipe
    by_cases hL : z=(-1 : Int)
    · subst z;rw [if_pos rfl,budget_L]
    · rw [if_neg hL]
      by_cases hp : 0 ≤ z
      · by_cases hge : Eidx x y ≤ z.toNat
        · have hstrict : Eidx x y < z.toNat := by
            have ht := Int.toNat_of_nonneg hp
            unfold natInt at he
            omega
          rw [dif_pos ⟨hp,hge⟩]
          exact budget_far_blank x y u k hk z hp hstrict
        · rw [dif_neg (by tauto)]
      · rw [dif_neg (by tauto)]

theorem exhausted_false_run (x y u : List Bool) :
    run machine (ticks (y.length+Eidx x y+3))
      ⟨8,natInt (D x+1),budgetTape x y y.length u⟩=
      some (finalConfig false) := by
  have hepos : 1 ≤ Eidx x y := by unfold Eidx;omega
  have hhead : natInt (Eidx x y)-1=natInt (Eidx x y-1) := by unfold natInt;omega
  have hskip := skip_consumed x y y.length u le_rfl
  have hidx : D x+1+y.length=Eidx x y := by unfold D Eidx;omega
  rw [hidx] at hskip
  have hclean := false_from (budgetTape x y y.length u) (Eidx x y-1)
    (fun i => budget_nat_ne_L x y u y.length i)
    (budget_negative x y u y.length) (budget_L x y y.length u)
  have he : Eidx x y-1+1=Eidx x y := by omega
  rw [he] at hclean
  have hf : y.length+Eidx x y+3=y.length+1+(Eidx x y-1+3) := by omega
  rw [hf,ticks_add,ticks_add,run_append,run_append,hskip,Option.bind_some,
    run_ticks_one,exhaust_step,Option.bind_some,hhead,erase_E_wipe x y u y.length le_rfl]
  exact hclean

theorem exhausted_false_output (x y u : List Bool) :
    run machine (ticks (y.length+Eidx x y+3))
      ⟨8,natInt (D x+1),budgetTape x y y.length u⟩=
      some (finalConfig false) ∧ Output machine [false] (finalConfig false) :=
  ⟨exhausted_false_run x y u,output_final false⟩

def rightTape (t : Int → Fin 8) (a n : Nat) (z : Int) : Fin 8 :=
  if 0 ≤ z ∧ a ≤ z.toNat ∧ z.toNat < a+n then 2 else t z

theorem rightTape_zero (t : Int → Fin 8) (a : Nat) : rightTape t a 0=t := by
  funext z;simp [rightTape]

theorem rightTape_read (t : Int → Fin 8) (a n : Nat) :
    rightTape t a n (natInt (a+n))=t (natInt (a+n)) := by
  have hn : (natInt (a+n)).toNat=a+n := Int.toNat_natCast _
  unfold rightTape
  exact if_neg (by intro h;have hu := h.2.2;rw [hn] at hu;omega)

theorem rightTape_write (t : Int → Fin 8) (a n : Nat) :
    Function.update (rightTape t a n) (natInt (a+n)) 2=rightTape t a (n+1) := by
  funext z
  by_cases hz : z=natInt (a+n)
  · subst z
    rw [Function.update_self]
    have hn : (natInt (a+n)).toNat=a+n := Int.toNat_natCast _
    unfold rightTape
    rw [if_pos (show 0 ≤ natInt (a+n) ∧ a ≤ (natInt (a+n)).toNat ∧
      (natInt (a+n)).toNat < a+(n+1) from ⟨Nat.cast_nonneg _,by rw [hn];omega,by rw [hn];omega⟩)]
  · rw [Function.update_of_ne hz]
    have he : (0 ≤ z ∧ a ≤ z.toNat ∧ z.toNat < a+n) ↔
        (0 ≤ z ∧ a ≤ z.toNat ∧ z.toNat < a+(n+1)) := by
      constructor
      · intro h;exact ⟨h.1,h.2.1,by omega⟩
      · intro h
        have ht := Int.toNat_of_nonneg h.1
        unfold natInt at hz
        exact ⟨h.1,h.2.1,by omega⟩
    simp only [rightTape,he]

theorem erase_right_run (t : Int → Fin 8) (a n : Nat)
    (hscan : ∀ i, i<n → t (natInt (a+i)) ≠ 5) :
    run machine (ticks n) ⟨13,natInt a,t⟩=
      some ⟨13,natInt (a+n),rightTape t a n⟩ := by
  have hmain : ∀ k, k ≤ n →
      run machine (ticks k) ⟨13,natInt a,rightTape t a 0⟩=
        some ⟨13,natInt (a+k),rightTape t a k⟩ := by
    intro k;induction k with
    | zero => simp [ticks]
    | succ k ih =>
      intro hk
      rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one]
      have hr := rightTape_read t a k
      have hn : rightTape t a k (natInt (a+k)) ≠ 5 := by rw [hr];exact hscan k (by omega)
      simp only [step,rule_cleanR _ hn,FiniteOneTapeSemantics.writtenTape,
        FiniteOneTapeSemantics.moveHead,Option.map_some]
      rw [rightTape_write,StandardBitPairProjection.natInt_succ]
      simp only [Nat.add_assoc]
  simpa only [rightTape_zero] using hmain n le_rfl

theorem budget_before_E_ne_E (x y u : List Bool) (k i : Nat) (hi : i < Eidx x y) :
    budgetTape x y k u (natInt i) ≠ (5 : Fin 8) := by
  rw [budget_at]
  unfold budgetNat
  split_ifs <;> try decide
  all_goals unfold enc;split_ifs <;> decide

theorem underflow_true_run (x y : List Bool) (k : Nat) (hk : k ≤ y.length) :
    run machine (ticks (y.length+Eidx x y+3))
      ⟨13,natInt (D x+1),Function.update
        (budgetTape x y k (List.replicate x.length true)) (natInt (D x)) 2⟩=
      some (finalConfig true) := by
  let t := Function.update (budgetTape x y k (List.replicate x.length true)) (natInt (D x)) 2
  let r := rightTape t (D x+1) y.length
  have hidx : D x+1+y.length=Eidx x y := by unfold D Eidx;omega
  have hscan : ∀ i, i<y.length → t (natInt (D x+1+i)) ≠ 5 := by
    intro i hi
    have hn : natInt (D x+1+i) ≠ natInt (D x) := by intro h;have := natInt_inj.mp h;omega
    dsimp only [t];rw [Function.update_of_ne hn]
    exact budget_before_E_ne_E x y _ k _ (by unfold Eidx D;omega)
  have hright := erase_right_run t (D x+1) y.length hscan
  rw [hidx] at hright
  have hrE : r (natInt (Eidx x y))=5 := by
    have hr := rightTape_read t (D x+1) y.length
    rw [hidx] at hr
    change rightTape t (D x+1) y.length (natInt (Eidx x y))=5
    rw [hr]
    have hn : natInt (Eidx x y) ≠ natInt (D x) := by intro h;have := natInt_inj.mp h;unfold Eidx D at*;omega
    dsimp only [t];rw [Function.update_of_ne hn,budget_E x y k _ hk]
  have hL : r (-1)=3 := by
    have hn : (-1 : Int) ≠ natInt (D x) := (natInt_ne_neg1 _).symm
    simp [r,rightTape,t,hn,budget_L]
  have hneg : ∀ z : Int, z<0 → z ≠ -1 → r z=2 := by
    intro z hz hne
    have hn : z ≠ natInt (D x) := by unfold natInt;omega
    simp [r,rightTape,t,show ¬ 0 ≤ z by omega,hn,budget_negative x y _ k z hz hne]
  have hnat : ∀ i : Nat, r (natInt i) ≠ 3 := by
    intro i
    dsimp only [r,rightTape]
    split_ifs
    · decide
    · dsimp only [t]
      by_cases hn : natInt i=natInt (D x)
      · rw [hn,Function.update_self];decide
      · rw [Function.update_of_ne hn]
        exact budget_nat_ne_L x y _ k i
  have hfar : ∀ z : Int, 0 ≤ z → Eidx x y<z.toNat → r z=2 := by
    intro z hp hz
    have hn : z ≠ natInt (D x) := by have ht := Int.toNat_of_nonneg hp;unfold natInt Eidx D at*;omega
    have hcond : ¬(0 ≤ z ∧ D x+1 ≤ z.toNat ∧ z.toNat < D x+1+y.length) := by rw [hidx];omega
    dsimp only [r,rightTape];rw [if_neg hcond]
    dsimp only [t];rw [Function.update_of_ne hn]
    exact budget_far_blank x y _ k hk z hp hz
  have hwipe : Function.update r (natInt (Eidx x y)) 2=wipe r (Eidx x y) := by
    funext z
    by_cases he : z=natInt (Eidx x y)
    · subst z;simp [wipe,natInt]
    · rw [Function.update_of_ne he]
      unfold wipe
      by_cases hm : z=(-1 : Int)
      · subst z;rw [if_pos rfl,hL]
      · rw [if_neg hm]
        by_cases hp : 0 ≤ z
        · by_cases hg : Eidx x y ≤ z.toNat
          · have hz : Eidx x y<z.toNat := by have ht := Int.toNat_of_nonneg hp;unfold natInt at he;omega
            rw [dif_pos ⟨hp,hg⟩];exact hfar z hp hz
          · rw [dif_neg (by tauto)]
        · rw [dif_neg (by tauto)]
  have hepos : 1 ≤ Eidx x y := by unfold Eidx;omega
  have hhead : natInt (Eidx x y)-1=natInt (Eidx x y-1) := by unfold natInt;omega
  have hclean := true_from r (Eidx x y-1) hnat hneg hL
  rw [show Eidx x y-1+1=Eidx x y by omega] at hclean
  have hf : y.length+Eidx x y+3=y.length+1+(Eidx x y-1+3) := by omega
  rw [hf,ticks_add,ticks_add,run_append,run_append,hright,Option.bind_some,run_ticks_one]
  change _=some (finalConfig true)
  have hstep : step machine 0 ⟨13,natInt (Eidx x y),r⟩=
      some ⟨15,natInt (Eidx x y-1),wipe r (Eidx x y)⟩ := by
    simp only [step,hrE,rule_cleanE,FiniteOneTapeSemantics.writtenTape,
      FiniteOneTapeSemantics.moveHead,Option.map_some]
    rw [hwipe,hhead]
  rw [hstep,Option.bind_some,hclean]

end PakFixedPolyomino.StandardBitUnaryBudgetCleanup
