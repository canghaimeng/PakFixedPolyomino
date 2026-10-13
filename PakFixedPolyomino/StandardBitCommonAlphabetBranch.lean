import PakFixedPolyomino.StandardBitCommonAlphabetJoin

/-! Literal finite branch selection. A stay/write selects one disjoint core;
one more stay/write maps its accepting state to the shared accept state. -/
namespace PakFixedPolyomino.StandardBitCommonAlphabetBranch
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition (ticks_succ)
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (writtenTape moveHead)
variable {nsF nsT nt : Nat}

def encF (q : Fin nsF) : Fin (nsF+nsT+3) := ⟨2+q.val,by have := q.isLt;omega⟩
def encT (q : Fin nsT) : Fin (nsF+nsT+3) := ⟨2+nsF+q.val,by have := q.isLt;omega⟩
def decF (q : Fin (nsF+nsT+3)) : Option (Fin nsF) :=
  if h : 2 ≤ q.val ∧ q.val < 2+nsF then some ⟨q.val-2,by omega⟩ else none
def decT (q : Fin (nsF+nsT+3)) : Option (Fin nsT) :=
  if h : 2+nsF ≤ q.val ∧ q.val < 2+nsF+nsT then some ⟨q.val-(2+nsF),by omega⟩ else none
def selectState : Fin (nsF+nsT+3) := ⟨nsF+nsT+2,by omega⟩

theorem decF_encF (q : Fin nsF) : decF (encF (nsT:=nsT) q) = some q := by
  have h := q.isLt
  simp [decF,encF]
theorem decT_encT (q : Fin nsT) : decT (encT (nsF:=nsF) q) = some q := by
  have h := q.isLt
  simp [decT,encT]
theorem decF_encT (q : Fin nsT) : decF (encT (nsF:=nsF) q) = none := by
  simp [decF,encT] <;> omega

def liftF (a : Action (Fin nsF) (Fin nt)) : Action (Fin (nsF+nsT+3)) (Fin nt) :=
  ⟨a.write,encF a.target,a.move⟩
def liftT (a : Action (Fin nsT) (Fin nt)) : Action (Fin (nsF+nsT+3)) (Fin nt) :=
  ⟨a.write,encT a.target,a.move⟩
def finish (s : Fin nt) : Action (Fin (nsF+nsT+3)) (Fin nt) := ⟨s,0,.stay⟩

def rule (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (q : Fin (nsF+nsT+3)) (s : Fin nt) (_ : Fin 1) :
    Option (Action (Fin (nsF+nsT+3)) (Fin nt)) :=
  if q=selectState then some ⟨s,if pick s then encT T.start else encF F.start,.stay⟩
  else (decF q).elim
    ((decT q).elim none fun t =>
      if t=T.accept then some (finish s) else (T.rule t s 0).map liftT)
    fun f => if f=F.accept then some (finish s) else (F.rule f s 0).map liftF

def machine (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) : DeterministicMachine (nsF+nsT+3) nt where
  rule := rule F T pick
  start := selectState
  accept := 0
  reject := 1
  accept_ne_reject := by intro h;have := congrArg Fin.val h;simpa using this
  blank := F.blank
  zero := F.zero
  one := F.one
  blank_ne_zero := F.blank_ne_zero
  blank_ne_one := F.blank_ne_one
  zero_ne_one := F.zero_ne_one
  accept_terminal := by
    intro s slot
    have hn : (0 : Fin (nsF+nsT+3)) ≠ selectState := by intro h;have := congrArg Fin.val h;simp [selectState] at this
    simp [rule,hn,decF,decT]
  reject_terminal := by
    intro s slot
    have hn : (1 : Fin (nsF+nsT+3)) ≠ selectState := by intro h;have := congrArg Fin.val h;simp [selectState] at this
    have hd : ¬(2+nsF ≤ 1 ∧ 1 < 2+nsF+nsT) := by omega
    simp [rule,hn,decF,decT,hd]

def configF (c : Configuration nsF nt) : Configuration (nsF+nsT+3) nt :=
  ⟨encF c.state,c.head,c.tape⟩
def configT (c : Configuration nsT nt) : Configuration (nsF+nsT+3) nt :=
  ⟨encT c.state,c.head,c.tape⟩
def selection (head : Int) (tape : Int → Fin nt) : Configuration (nsF+nsT+3) nt :=
  ⟨selectState,head,tape⟩

theorem step_F (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (c : Configuration nsF nt) (ha : c.state ≠ F.accept) :
    step (machine F T pick) 0 (configF c) = (step F 0 c).map configF := by
  have hn : encF (nsT:=nsT) c.state ≠ selectState := by
    intro h;have := congrArg Fin.val h;have := c.state.isLt;simp [encF,selectState] at *;omega
  simp only [step,machine,configF,rule,if_neg hn,decF_encF,Option.elim_some,ha,if_false]
  cases hh : F.rule c.state (c.tape c.head) 0 <;> simp [hh,liftF,configF,writtenTape]

theorem step_T (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (c : Configuration nsT nt) (ha : c.state ≠ T.accept) :
    step (machine F T pick) 0 (configT c) = (step T 0 c).map configT := by
  have hn : encT (nsF:=nsF) c.state ≠ selectState := by
    intro h;have := congrArg Fin.val h;have := c.state.isLt;simp [encT,selectState] at *;omega
  simp only [step,machine,configT,rule,if_neg hn,decF_encT,decT_encT,
    Option.elim_none,Option.elim_some,ha,if_false]
  cases hh : T.rule c.state (c.tape c.head) 0 <;> simp [hh,liftT,configT,writtenTape]

theorem run_F (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (c out : Configuration nsF nt) (n : Nat)
    (hr : run F (ticks n) c = some out) :
    run (machine F T pick) (ticks n) (configF c) = some (configF out) := by
  induction n generalizing c with
  | zero => have he := Option.some.inj hr;subst out;simp [ticks]
  | succ n ih =>
    rw [ticks_succ] at hr ⊢
    have hn : c.state ≠ F.accept := by
      intro h;have hb := run_accept_nonempty_none F c h (0::ticks n) (List.cons_ne_nil _ _)
      rw [hb] at hr;cases hr
    rw [run_cons] at hr ⊢
    cases hs : step F 0 c with
    | none => simp [hs] at hr
    | some mid => simp [hs] at hr;simp [step_F F T pick c hn,hs];exact ih mid hr

theorem run_T (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (c out : Configuration nsT nt) (n : Nat)
    (hr : run T (ticks n) c = some out) :
    run (machine F T pick) (ticks n) (configT c) = some (configT out) := by
  induction n generalizing c with
  | zero => have he := Option.some.inj hr;subst out;simp [ticks]
  | succ n ih =>
    rw [ticks_succ] at hr ⊢
    have hn : c.state ≠ T.accept := by
      intro h;have hb := run_accept_nonempty_none T c h (0::ticks n) (List.cons_ne_nil _ _)
      rw [hb] at hr;cases hr
    rw [run_cons] at hr ⊢
    cases hs : step T 0 c with
    | none => simp [hs] at hr
    | some mid => simp [hs] at hr;simp [step_T F T pick c hn,hs];exact ih mid hr

theorem select_step (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (h : Int) (t : Int → Fin nt) :
    step (machine F T pick) 0 (selection h t) =
      some (if pick (t h) then configT ⟨T.start,h,t⟩ else configF ⟨F.start,h,t⟩) := by
  simp [step,machine,rule,selection,configT,configF,writtenTape,moveHead]
  cases pick (t h) <;> rfl

theorem finish_F (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (out : Configuration nsF nt) (ha : out.state=F.accept) :
    step (machine F T pick) 0 (configF out) = some ⟨0,out.head,out.tape⟩ := by
  have hn : encF (nsT:=nsT) out.state ≠ selectState := by
    intro h;have := congrArg Fin.val h;have := out.state.isLt;simp [encF,selectState] at *;omega
  have hn' : encF (nsT:=nsT) F.accept ≠ selectState := by simpa only [ha] using hn
  simp [step,machine,rule,configF,hn',decF_encF,ha,finish,writtenTape,moveHead]

theorem finish_T (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (out : Configuration nsT nt) (ha : out.state=T.accept) :
    step (machine F T pick) 0 (configT out) = some ⟨0,out.head,out.tape⟩ := by
  have hn : encT (nsF:=nsF) out.state ≠ selectState := by
    intro h;have := congrArg Fin.val h;have := out.state.isLt;simp [encT,selectState] at *;omega
  have hn' : encT (nsF:=nsF) T.accept ≠ selectState := by simpa only [ha] using hn
  simp [step,machine,rule,configT,hn',decF_encT,decT_encT,ha,finish,writtenTape,moveHead]

theorem selected_false_run (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (h : Int) (t : Int → Fin nt) (out : Configuration nsF nt)
    (n : Nat) (hp : pick (t h)=false) (hr : run F (ticks n) ⟨F.start,h,t⟩ = some out)
    (ha : out.state=F.accept) :
    run (machine F T pick) (ticks (1+n+1)) (selection h t) = some ⟨0,out.head,out.tape⟩ := by
  rw [ticks_add,ticks_add,run_append,run_append,run_ticks_one,select_step,hp]
  simp only [Bool.false_eq_true,if_false,Option.bind_some]
  rw [run_F F T pick _ out n hr,Option.bind_some,run_ticks_one,finish_F F T pick out ha]

theorem selected_true_run (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (h : Int) (t : Int → Fin nt) (out : Configuration nsT nt)
    (n : Nat) (hp : pick (t h)=true) (hr : run T (ticks n) ⟨T.start,h,t⟩ = some out)
    (ha : out.state=T.accept) :
    run (machine F T pick) (ticks (1+n+1)) (selection h t) = some ⟨0,out.head,out.tape⟩ := by
  rw [ticks_add,ticks_add,run_append,run_append,run_ticks_one,select_step,hp]
  simp only [ite_true,Option.bind_some]
  rw [run_T F T pick _ out n hr,Option.bind_some,run_ticks_one,finish_T F T pick out ha]

theorem branch_spec (F : DeterministicMachine nsF nt) (T : DeterministicMachine nsT nt)
    (pick : Fin nt → Bool) (h : Int) (t : Int → Fin nt) :
    (∀ (out : Configuration nsF nt) (n : Nat), pick (t h)=false →
      run F (ticks n) ⟨F.start,h,t⟩ = some out → out.state=F.accept →
      run (machine F T pick) (ticks (1+n+1)) (selection h t) = some ⟨0,out.head,out.tape⟩) ∧
    (∀ (out : Configuration nsT nt) (n : Nat), pick (t h)=true →
      run T (ticks n) ⟨T.start,h,t⟩ = some out → out.state=T.accept →
      run (machine F T pick) (ticks (1+n+1)) (selection h t) = some ⟨0,out.head,out.tape⟩) :=
  ⟨fun out n hp hr ha => selected_false_run F T pick h t out n hp hr ha,
    fun out n hp hr ha => selected_true_run F T pick h t out n hp hr ha⟩

end PakFixedPolyomino.StandardBitCommonAlphabetBranch
