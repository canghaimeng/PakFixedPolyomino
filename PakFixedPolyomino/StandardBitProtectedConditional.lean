import PakFixedPolyomino.StandardBitCommonAlphabetBranch
import PakFixedPolyomino.StandardBitProtectedRestore
import PakFixedPolyomino.StandardBitProtectedCleanup

/-! Initialized physical conditional control over one common finite alphabet.
The predicate emits one clean bit. Each selected branch first restores the
retained original input, executes its actual core, and erases the raw track.
Core computation hypotheses are explicit; no original guard is claimed here. -/
namespace PakFixedPolyomino.StandardBitProtectedConditional
open StandardNondeterministicMachine StandardBitTime StandardMachineProtectedTrack

variable {nsP nsF nsT nt : Nat}

def SameCodes (P : DeterministicMachine nsP nt) (F : DeterministicMachine nsF nt) : Prop :=
  P.blank=F.blank ∧ P.zero=F.zero ∧ P.one=F.one

theorem input_eq (P : DeterministicMachine nsP nt) (F : DeterministicMachine nsF nt)
    (h : SameCodes P F) (x : List Bool) : inputTape P x = inputTape F x := by
  funext z
  simp only [inputTape,h.1,h.2.1,h.2.2]

def body (P : DeterministicMachine nsP nt) (F : DeterministicMachine nsF nt) :
    DeterministicMachine (6+nsF+2) (4*nt) :=
  StandardBitCommonAlphabetJoin.machine (StandardBitProtectedRestore.machine P) (protect F (2 : Fin 4))

def pick (P : DeterministicMachine nsP nt) (s : Fin (4*nt)) : Bool :=
  decide ((unpack s).2=P.one)

def branches (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) :
    DeterministicMachine ((6+nsF+2)+(6+nsT+2)+3) (4*nt) :=
  StandardBitCommonAlphabetBranch.machine (body P F) (body P T) (pick P)

def predicateBranch (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) :
    DeterministicMachine ((nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2) (4*nt) :=
  StandardBitCommonAlphabetJoin.machine (StandardBitProtectedLoader.loader P) (branches P F T)

def machine (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) :
    DeterministicMachine (((nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2)+6+2) (4*nt) :=
  StandardBitCommonAlphabetJoin.machine
    (nsA:=((nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2)) (nsB:=6)
    (predicateBranch P F T) (StandardBitProtectedCleanup.machine P)

def finalConfig (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) (y : List Bool) :
    Configuration (((nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2)+6+2) (4*nt) :=
  StandardBitCommonAlphabetJoin.configB (nsA := (nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2)
    (StandardBitProtectedCleanup.machine P) (StandardBitProtectedCleanup.finalConfig P y)

def fuel (x y : List Bool) (n m : Nat) : Nat :=
  (2*x.length+4+n)+1+(1+(2*x.length+4+1+m)+1)+1+(2*max x.length y.length+4)

theorem body_run (P : DeterministicMachine nsP nt) (F : DeterministicMachine nsF nt)
    (hcodes : SameCodes P F) (x : List Bool) (b : Bool) (m : Nat)
    (out : Configuration nsF nt) (hr : run F (ticks m) (initial F x)=some out) :
    run (body P F) (ticks (2*x.length+4+1+m))
      (StandardBitCommonAlphabetJoin.configA (nsB:=nsF) (StandardBitProtectedRestore.startConfig P x b)) =
      some (StandardBitCommonAlphabetJoin.configB (nsA:=6) (protect F (2 : Fin 4)) (embed (StandardBitProtectedLoader.rawTape x) out)) := by
  have hstart : (⟨(protect F (2 : Fin 4)).start,
      (StandardBitProtectedRestore.finalConfig P x).head,(StandardBitProtectedRestore.finalConfig P x).tape⟩ : Configuration nsF (4*nt)) =
      embed (StandardBitProtectedLoader.rawTape x) (initial F x) := by
    apply config_ext
    · rfl
    · rfl
    · simp only [StandardBitProtectedRestore.finalConfig,embed,initial,input_eq P F hcodes]
  have hcore : run (protect F (2 : Fin 4)) (ticks m)
      ⟨(protect F (2 : Fin 4)).start,(StandardBitProtectedRestore.finalConfig P x).head,(StandardBitProtectedRestore.finalConfig P x).tape⟩ =
      some (embed (StandardBitProtectedLoader.rawTape x) out) := by
    rw [hstart,run_exact,hr]
    rfl
  exact StandardBitCommonAlphabetJoin.joined_run (StandardBitProtectedRestore.machine P) (protect F (2 : Fin 4))
    (StandardBitProtectedRestore.startConfig P x b) (StandardBitProtectedRestore.finalConfig P x) _
    (2*x.length+4) m (StandardBitProtectedRestore.restore_run P x b) rfl hcore

theorem body_output (P : DeterministicMachine nsP nt) (F : DeterministicMachine nsF nt)
    (hcodes : SameCodes P F) (x y : List Bool) (out : Configuration nsF nt)
    (ho : Output F y out) :
    (StandardBitCommonAlphabetJoin.configB (nsA:=6) (protect F (2 : Fin 4)) (embed (StandardBitProtectedLoader.rawTape x) out)).state=
      (body P F).accept ∧
    (StandardBitCommonAlphabetJoin.configB (nsA:=6) (protect F (2 : Fin 4)) (embed (StandardBitProtectedLoader.rawTape x) out)).head=0 ∧
    (StandardBitCommonAlphabetJoin.configB (nsA:=6) (protect F (2 : Fin 4)) (embed (StandardBitProtectedLoader.rawTape x) out)).tape=
      fun z => pack (StandardBitProtectedLoader.rawTape x z) (inputTape P y z) := by
  refine ⟨?_,ho.2.1,?_⟩
  · simp [StandardBitCommonAlphabetJoin.configB,embed,ho.1,body,StandardBitCommonAlphabetJoin.machine,
      StandardBitMachineComposition.encodeStateB,StandardBitMachineComposition.acceptC]
  · simp only [StandardBitCommonAlphabetJoin.configB,embed,ho.2.2,input_eq P F hcodes]

theorem select_read (P : DeterministicMachine nsP nt) (x : List Bool) (b : Bool) :
    pick P (pack (StandardBitProtectedLoader.rawTape x 0) (inputTape P [b] 0)) = b := by
  cases b <;> simp [pick,inputTape,P.zero_ne_one]

def mixedTape (P : DeterministicMachine nsP nt) (x y : List Bool) : Int → Fin (4*nt) :=
  fun z => pack (StandardBitProtectedLoader.rawTape x z) (inputTape P y z)

def branchFinal (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) (x y : List Bool) :
    Configuration ((6+nsF+2)+(6+nsT+2)+3) (4*nt) := ⟨0,0,mixedTape P x y⟩

theorem branch_run (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T) (x y : List Bool) (b : Bool) (m : Nat)
    (hfalse : b=false → ∃ out, run F (ticks m) (initial F x)=some out ∧ Output F y out)
    (htrue : b=true → ∃ out, run T (ticks m) (initial T x)=some out ∧ Output T y out) :
    run (branches P F T) (ticks (1+(2*x.length+4+1+m)+1))
      (StandardBitCommonAlphabetBranch.selection 0 (mixedTape P x [b])) =
      some (branchFinal P F T x y) := by
  cases b with
  | false =>
    obtain ⟨out,hr,ho⟩ := hfalse rfl
    have hbody := body_run P F hF x false m out hr
    have hout := body_output P F hF x y out ho
    have hp : pick P (mixedTape P x [false] 0)=false := select_read P x false
    have h := StandardBitCommonAlphabetBranch.selected_false_run (body P F) (body P T)
      (pick P) 0 (mixedTape P x [false]) _ (2*x.length+4+1+m) hp hbody hout.1
    rw [hout.2.1,hout.2.2] at h
    exact h
  | true =>
    obtain ⟨out,hr,ho⟩ := htrue rfl
    have hbody := body_run P T hT x true m out hr
    have hout := body_output P T hT x y out ho
    have hp : pick P (mixedTape P x [true] 0)=true := select_read P x true
    have h := StandardBitCommonAlphabetBranch.selected_true_run (body P F) (body P T)
      (pick P) 0 (mixedTape P x [true]) _ (2*x.length+4+1+m) hp hbody hout.1
    rw [hout.2.1,hout.2.2] at h
    exact h

def predicateBranchFinal (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) (x y : List Bool) :
    Configuration ((nsP+4)+((6+nsF+2)+(6+nsT+2)+3)+2) (4*nt) :=
  StandardBitCommonAlphabetJoin.configB (nsA:=nsP+4) (branches P F T) (branchFinal P F T x y)

theorem predicate_branch_run (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T) (x y : List Bool) (b : Bool) (n m : Nat)
    (outP : Configuration nsP nt) (hrP : run P (ticks n) (initial P x)=some outP)
    (hoP : Output P [b] outP)
    (hfalse : b=false → ∃ out, run F (ticks m) (initial F x)=some out ∧ Output F y out)
    (htrue : b=true → ∃ out, run T (ticks m) (initial T x)=some out ∧ Output T y out) :
    run (predicateBranch P F T)
      (ticks ((2*x.length+4+n)+1+(1+(2*x.length+4+1+m)+1)))
      (initial (predicateBranch P F T) x) = some (predicateBranchFinal P F T x y) := by
  let middle := StandardBitProtectedLoader.lift (embed (StandardBitProtectedLoader.rawTape x) outP)
  have hload : run (StandardBitProtectedLoader.loader P) (ticks (2*x.length+4+n))
      (initial (StandardBitProtectedLoader.loader P) x)=some middle := by
    rw [ticks_add,StandardBitProtectedLoader.loader_source_exact,hrP]
    rfl
  have ha : middle.state=(StandardBitProtectedLoader.loader P).accept := by
    simp [middle,StandardBitProtectedLoader.lift,embed,hoP.1,StandardBitProtectedLoader.loader]
  have hstart : (⟨(branches P F T).start,middle.head,middle.tape⟩ :
      Configuration ((6+nsF+2)+(6+nsT+2)+3) (4*nt)) =
      StandardBitCommonAlphabetBranch.selection 0 (mixedTape P x [b]) := by
    apply config_ext
    · rfl
    · exact hoP.2.1
    · simp only [middle,StandardBitProtectedLoader.lift,embed,hoP.2.2]
      rfl
  have hbranch := branch_run P F T hF hT x y b m hfalse htrue
  rw [← hstart] at hbranch
  simpa only [predicateBranch,predicateBranchFinal,StandardBitCommonAlphabetJoin.initial_eq] using
    StandardBitCommonAlphabetJoin.joined_run (StandardBitProtectedLoader.loader P)
      (branches P F T) _ middle _ (2*x.length+4+n) (1+(2*x.length+4+1+m)+1) hload ha hbranch

theorem run_output (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T) (x y : List Bool) (b : Bool) (n m : Nat)
    (outP : Configuration nsP nt) (hrP : run P (ticks n) (initial P x)=some outP)
    (hoP : Output P [b] outP)
    (hfalse : b=false → ∃ out, run F (ticks m) (initial F x)=some out ∧ Output F y out)
    (htrue : b=true → ∃ out, run T (ticks m) (initial T x)=some out ∧ Output T y out) :
    run (machine P F T) (ticks (fuel x y n m)) (initial (machine P F T) x)=
      some (finalConfig P F T y) := by
  have hp := predicate_branch_run P F T hF hT x y b n m outP hrP hoP hfalse htrue
  have ha : (predicateBranchFinal P F T x y).state=(predicateBranch P F T).accept := by
    simp [predicateBranchFinal,branchFinal,branches,predicateBranch,
      StandardBitCommonAlphabetJoin.configB,StandardBitCommonAlphabetJoin.machine,
      StandardBitCommonAlphabetBranch.machine,StandardBitMachineComposition.encodeStateB,
      StandardBitMachineComposition.acceptC]
  have hstart : (⟨(StandardBitProtectedCleanup.machine P).start,
      (predicateBranchFinal P F T x y).head,(predicateBranchFinal P F T x y).tape⟩ :
      Configuration 6 (4*nt)) = StandardBitProtectedCleanup.startConfig P x y := by
    rfl
  have hclean := StandardBitProtectedCleanup.cleanup_run P x y
  rw [← hstart] at hclean
  simpa only [machine,fuel,finalConfig,StandardBitCommonAlphabetJoin.initial_eq] using
    StandardBitCommonAlphabetJoin.joined_run (predicateBranch P F T)
      (StandardBitProtectedCleanup.machine P) _ (predicateBranchFinal P F T x y) _
      ((2*x.length+4+n)+1+(1+(2*x.length+4+1+m)+1))
      (2*max x.length y.length+4) hp ha hclean

theorem final_output (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt) (y : List Bool) :
    Output (machine P F T) y (finalConfig P F T y) := by
  refine ⟨?_,rfl,rfl⟩
  simp [finalConfig,StandardBitCommonAlphabetJoin.configB,
    StandardBitProtectedCleanup.finalConfig,StandardBitProtectedCleanup.machine,
    StandardBitMachineComposition.encodeStateB,machine,
    StandardBitCommonAlphabetJoin.machine,StandardBitMachineComposition.acceptC]

def conditional (b : List Bool → Bool) (f g : List Bool → List Bool) (x : List Bool) : List Bool :=
  if b x then g x else f x

theorem computes (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T)
    (b : List Bool → Bool) (f g : List Bool → List Bool) (p q r : Nat → Nat)
    (hP : ComputesWithin P (fun x => [b x]) p)
    (hcF : ComputesWithin F f q) (hcT : ComputesWithin T g r) :
    ComputesWithin (machine P F T) (conditional b f g)
      (fun k => 6*k+p k+3*(q k+r k)+19) := by
  intro x
  obtain ⟨n,outP,hn,hrP,hoP⟩ := hP x
  change Output P [b x] outP at hoP
  cases hb : b x with
  | false =>
    obtain ⟨m,out,hm,hr,ho⟩ := hcF x
    have hlen := ComputesWithin.output_length F f q hcF x
    rw [hb] at hoP
    have hmax : max x.length (f x).length ≤ x.length+q x.length+r x.length+1 :=
      max_le (by omega) (by omega)
    have hrun := run_output P F T hF hT x (f x) false n m outP hrP hoP
      (fun _ => ⟨out,hr,ho⟩) (by intro h;cases h)
    refine ⟨fuel x (f x) n m,finalConfig P F T (f x),?_,?_,?_⟩
    · change fuel x (f x) n m ≤ 6*x.length+p x.length+3*(q x.length+r x.length)+19
      unfold fuel
      omega
    · simpa only [conditional,hb,Bool.false_eq_true,if_false] using hrun
    · simpa only [conditional,hb,Bool.false_eq_true,if_false] using final_output P F T (f x)
  | true =>
    obtain ⟨m,out,hm,hr,ho⟩ := hcT x
    have hlen := ComputesWithin.output_length T g r hcT x
    rw [hb] at hoP
    have hmax : max x.length (g x).length ≤ x.length+q x.length+r x.length+1 :=
      max_le (by omega) (by omega)
    have hrun := run_output P F T hF hT x (g x) true n m outP hrP hoP
      (by intro h;cases h) (fun _ => ⟨out,hr,ho⟩)
    refine ⟨fuel x (g x) n m,finalConfig P F T (g x),?_,?_,?_⟩
    · change fuel x (g x) n m ≤ 6*x.length+p x.length+3*(q x.length+r x.length)+19
      unfold fuel
      omega
    · simpa only [conditional,hb,ite_true] using hrun
    · simpa only [conditional,hb,ite_true] using final_output P F T (g x)

theorem polynomial_computes (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T)
    (b : List Bool → Bool) (f g : List Bool → List Bool) (p q r : Polynomial Nat)
    (hP : ComputesWithin P (fun x => [b x]) (fun k => p.eval k))
    (hcF : ComputesWithin F f (fun k => q.eval k))
    (hcT : ComputesWithin T g (fun k => r.eval k)) :
    ComputesWithin (machine P F T) (conditional b f g)
      (fun k => (6*Polynomial.X+p+3*(q+r)+19).eval k) := by
  have h := computes P F T hF hT b f g (fun k => p.eval k)
    (fun k => q.eval k) (fun k => r.eval k) hP hcF hcT
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X] using h

theorem conditional_bit_spec (P : DeterministicMachine nsP nt)
    (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (hF : SameCodes P F) (hT : SameCodes P T)
    (b : List Bool → Bool) (f g : List Bool → List Bool) (p q r : Polynomial Nat)
    (hP : ComputesWithin P (fun x => [b x]) (fun k => p.eval k))
    (hcF : ComputesWithin F f (fun k => q.eval k))
    (hcT : ComputesWithin T g (fun k => r.eval k)) :
    PolyBitTime (conditional b f g) ∧
    ComputesWithin (machine P F T) (conditional b f g)
      (fun k => (6*Polynomial.X+p+3*(q+r)+19).eval k) ∧
    ∀ x, RunsAtMost (machine P F T) x ((6*Polynomial.X+p+3*(q+r)+19).eval x.length) ∧
      ∀ slots out, run (machine P F T) slots (initial (machine P F T) x)=some out →
        -(((6*Polynomial.X+p+3*(q+r)+19).eval x.length : Nat) : Int) ≤ out.head ∧
        out.head ≤ (((6*Polynomial.X+p+3*(q+r)+19).eval x.length : Nat) : Int) ∧
        ∀ z : Int, z < -(((6*Polynomial.X+p+3*(q+r)+19).eval x.length : Nat) : Int) ∨
          (x.length : Int)+(((6*Polynomial.X+p+3*(q+r)+19).eval x.length : Nat) : Int)+1 ≤ z →
          out.tape z=(machine P F T).blank := by
  have h := polynomial_computes P F T hF hT b f g p q r hP hcF hcT
  exact ⟨⟨_,_,machine P F T,6*Polynomial.X+p+3*(q+r)+19,h⟩,h,
    fun x => ComputesWithin.actual_bounds (machine P F T) (conditional b f g) _ h x⟩

end PakFixedPolyomino.StandardBitProtectedConditional
