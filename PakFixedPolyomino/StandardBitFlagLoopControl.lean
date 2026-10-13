import PakFixedPolyomino.StandardBitCommonAlphabetBranch

/-! Finite control for a body that emits a literal Boolean flag followed by
the next state word. Two copies of a stripping machine retain the flag in
their finite control: false halts, true restarts the same body. -/
namespace PakFixedPolyomino.StandardBitFlagLoopControl
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition (encodeStateA encodeStateB encodeStateB_other ticks_succ)
open FiniteOneTapeSemantics (writtenTape moveHead)

variable {ns nh nt : Nat}

def branch (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt) :=
  StandardBitCommonAlphabetBranch.machine H H (fun a => decide (a=M.one))

def base (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt) :=
  StandardBitCommonAlphabetJoin.machine M (branch M H)

def continueState (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt) :
    Fin (ns+(nh+nh+3)+2) := ⟨4+ns+nh+H.accept.val,by have := H.accept.isLt;omega⟩

theorem encF_ne_zero (q : Fin nh) : StandardBitCommonAlphabetBranch.encF (nsT:=nh) q≠0 := by
  intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.encF] at this

theorem encF_ne_one (q : Fin nh) : StandardBitCommonAlphabetBranch.encF (nsT:=nh) q≠1 := by
  intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.encF] at this;omega

theorem encT_ne_zero (q : Fin nh) : StandardBitCommonAlphabetBranch.encT (nsF:=nh) q≠0 := by
  intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.encT] at this

theorem encT_ne_one (q : Fin nh) : StandardBitCommonAlphabetBranch.encT (nsF:=nh) q≠1 := by
  intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.encT] at this;omega

theorem stateF_val (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (q : Fin nh) : (encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encF q)).val=4+ns+q.val := by
  rw [encodeStateB_other _ _ (encF_ne_zero q) (encF_ne_one q)]
  simp [StandardBitCommonAlphabetBranch.encF]
  omega

theorem stateT_val (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (q : Fin nh) : (encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encT q)).val=4+ns+nh+q.val := by
  rw [encodeStateB_other _ _ (encT_ne_zero q) (encT_ne_one q)]
  simp [StandardBitCommonAlphabetBranch.encT]
  omega

theorem continueState_eq (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt) :
    continueState M H=encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encT H.accept) := by
  apply Fin.ext
  rw [stateT_val]
  rfl

def machine (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt) :
    DeterministicMachine (ns+(nh+nh+3)+2) nt :=
  { base M H with
    rule := fun q a slot => if q=continueState M H then
      some ⟨a,encodeStateA M.start,.stay⟩ else (base M H).rule q a slot
    accept_terminal := by
      intro a slot
      have hn : (0 : Fin (ns+(nh+nh+3)+2))≠continueState M H := by
        intro h;have := congrArg Fin.val h;simp [continueState] at this;omega
      change (if (0 : Fin (ns+(nh+nh+3)+2))=continueState M H then
        some ⟨a,encodeStateA M.start,.stay⟩ else (base M H).rule 0 a slot)=none
      rw [if_neg hn]
      exact (base M H).accept_terminal a slot
    reject_terminal := by
      intro a slot
      have hn : (1 : Fin (ns+(nh+nh+3)+2))≠continueState M H := by
        intro h;have := congrArg Fin.val h;simp [continueState] at this;omega
      change (if (1 : Fin (ns+(nh+nh+3)+2))=continueState M H then
        some ⟨a,encodeStateA M.start,.stay⟩ else (base M H).rule 1 a slot)=none
      rw [if_neg hn]
      exact (base M H).reject_terminal a slot }

def bodyConfig (c : Configuration ns nt) : Configuration (ns+(nh+nh+3)+2) nt := StandardBitCommonAlphabetJoin.configA c
def falseConfig (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration nh nt) := StandardBitCommonAlphabetJoin.configB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.configF c)
def trueConfig (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration nh nt) := StandardBitCommonAlphabetJoin.configB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.configT c)
def checkConfig (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (h : Int) (t : Int → Fin nt) := StandardBitCommonAlphabetJoin.configB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.selection h t)

theorem step_base (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration (ns+(nh+nh+3)+2) nt) (hn : c.state≠continueState M H) :
    step (machine M H) 0 c=step (base M H) 0 c := by
  simp only [step,machine,if_neg hn]

theorem step_body (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration ns nt) (ha : c.state≠M.accept) :
    step (machine M H) 0 (bodyConfig (nh:=nh) c)=
      (step M 0 c).map (bodyConfig (nh:=nh)) := by
  have hn : (bodyConfig (nh:=nh) c).state≠continueState M H := by
    intro h;have := congrArg Fin.val h;have := c.state.isLt
    simp [bodyConfig,StandardBitCommonAlphabetJoin.configA,encodeStateA,continueState] at *;omega
  rw [step_base M H _ hn]
  exact StandardBitCommonAlphabetJoin.step_A M (branch M H) c ha

theorem step_false (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration nh nt) (ha : c.state≠H.accept) :
    step (machine M H) 0 (falseConfig M H c)=(step H 0 c).map (falseConfig M H) := by
  have hn : (falseConfig M H c).state≠continueState M H := by
    intro h;have he := congrArg Fin.val h
    change (encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encF c.state)).val=_ at he
    rw [stateF_val] at he
    have := c.state.isLt
    simp [continueState] at he;omega
  rw [step_base M H _ hn]
  have h := StandardBitCommonAlphabetJoin.step_B M (branch M H) (StandardBitCommonAlphabetBranch.configF c) (encF_ne_zero _) (encF_ne_one _)
  unfold branch at h
  rw [StandardBitCommonAlphabetBranch.step_F H H _ c ha] at h
  simp only [Option.map_map] at h
  exact h

theorem step_true (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration nh nt) (ha : c.state≠H.accept) :
    step (machine M H) 0 (trueConfig M H c)=(step H 0 c).map (trueConfig M H) := by
  have hn : (trueConfig M H c).state≠continueState M H := by
    intro h;have he := congrArg Fin.val h
    change (encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encT c.state)).val=_ at he
    rw [stateT_val] at he
    have heq : c.state=H.accept := by apply Fin.ext;simp [continueState] at he;omega
    exact ha heq
  rw [step_base M H _ hn]
  have h := StandardBitCommonAlphabetJoin.step_B M (branch M H) (StandardBitCommonAlphabetBranch.configT c) (encT_ne_zero _) (encT_ne_one _)
  unfold branch at h
  rw [StandardBitCommonAlphabetBranch.step_T H H _ c ha] at h
  simp only [Option.map_map] at h
  exact h

theorem lift_run {ns' nt' : Nat} (S : DeterministicMachine ns nt)
    (T : DeterministicMachine ns' nt')
    (embed : Configuration ns nt → Configuration ns' nt')
    (hs : ∀ c, c.state≠S.accept → step T 0 (embed c)=(step S 0 c).map embed)
    (c out : Configuration ns nt) (n : Nat) (hr : run S (ticks n) c=some out) :
    run T (ticks n) (embed c)=some (embed out) := by
  induction n generalizing c with
  | zero => have he := Option.some.inj hr;subst out;rfl
  | succ n ih =>
    rw [ticks_succ,run_cons] at hr ⊢
    have hn : c.state≠S.accept := by
      intro ha
      have hb := run_accept_nonempty_none S c ha (0::ticks n) (List.cons_ne_nil _ _)
      simp only [run_cons] at hb
      rw [hb] at hr
      cases hr
    rw [hs c hn]
    cases he : step S 0 c with
    | none => simp [he] at hr
    | some mid => simp only [he,Option.bind_some] at hr;simp only [Option.map_some,Option.bind_some];exact ih mid hr

theorem run_body (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c out : Configuration ns nt) (n : Nat) (hr : run M (ticks n) c=some out) :
    run (machine M H) (ticks n) (bodyConfig (nh:=nh) c)=some (bodyConfig (nh:=nh) out) :=
  lift_run M (machine M H) _ (step_body M H) c out n hr

theorem run_false (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c out : Configuration nh nt) (n : Nat) (hr : run H (ticks n) c=some out) :
    run (machine M H) (ticks n) (falseConfig M H c)=some (falseConfig M H out) :=
  lift_run H (machine M H) _ (step_false M H) c out n hr

theorem run_true (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c out : Configuration nh nt) (n : Nat) (hr : run H (ticks n) c=some out) :
    run (machine M H) (ticks n) (trueConfig M H c)=some (trueConfig M H out) :=
  lift_run H (machine M H) _ (step_true M H) c out n hr

theorem finish_body (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (c : Configuration ns nt) (ha : c.state=M.accept) :
    step (machine M H) 0 (bodyConfig (nh:=nh) c)=some (checkConfig M H c.head c.tape) := by
  have hn : (bodyConfig (nh:=nh) c).state≠continueState M H := by
    intro h;have := congrArg Fin.val h;have := c.state.isLt
    simp [bodyConfig,StandardBitCommonAlphabetJoin.configA,encodeStateA,continueState] at *;omega
  rw [step_base M H _ hn]
  exact StandardBitCommonAlphabetJoin.step_handoff M (branch M H) c ha

theorem check_ne_continue (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (h : Int) (t : Int → Fin nt) : (checkConfig M H h t).state≠continueState M H := by
  have hn0 : StandardBitCommonAlphabetBranch.selectState (nsF:=nh) (nsT:=nh)≠0 := by
    intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.selectState] at this
  have hn1 : StandardBitCommonAlphabetBranch.selectState (nsF:=nh) (nsT:=nh)≠1 := by
    intro h;have := congrArg Fin.val h;simp [StandardBitCommonAlphabetBranch.selectState] at this
  intro he
  have he' := congrArg Fin.val he
  change (encodeStateB (nsA:=ns) (branch M H) StandardBitCommonAlphabetBranch.selectState).val=_ at he'
  rw [encodeStateB_other _ _ hn0 hn1] at he'
  have := H.accept.isLt
  simp [StandardBitCommonAlphabetBranch.selectState,continueState] at he'
  omega

theorem check_step (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (h : Int) (t : Int → Fin nt) :
    step (machine M H) 0 (checkConfig M H h t)=some
      (if t h=M.one then trueConfig M H ⟨H.start,h,t⟩ else falseConfig M H ⟨H.start,h,t⟩) := by
  rw [step_base M H _ (check_ne_continue M H h t)]
  have hn0 : (StandardBitCommonAlphabetBranch.selection (nsF:=nh) (nsT:=nh) h t).state≠0 := by
    intro he;have := congrArg Fin.val he;simp [StandardBitCommonAlphabetBranch.selection,
      StandardBitCommonAlphabetBranch.selectState] at this
  have hn1 : (StandardBitCommonAlphabetBranch.selection (nsF:=nh) (nsT:=nh) h t).state≠1 := by
    intro he;have := congrArg Fin.val he;simp [StandardBitCommonAlphabetBranch.selection,
      StandardBitCommonAlphabetBranch.selectState] at this
  have hs := StandardBitCommonAlphabetJoin.step_B M (branch M H)
    (StandardBitCommonAlphabetBranch.selection h t) hn0 hn1
  unfold branch at hs
  rw [StandardBitCommonAlphabetBranch.select_step] at hs
  by_cases hp : t h=M.one
  · simpa only [base,checkConfig,trueConfig,branch,hp,decide_true,ite_true,Option.map_some] using hs
  · simpa only [base,checkConfig,falseConfig,branch,hp,decide_false,if_false,Bool.false_eq_true,Option.map_some] using hs

theorem finish_false (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (out : Configuration nh nt) (ha : out.state=H.accept) :
    step (machine M H) 0 (falseConfig M H out)=some ⟨0,out.head,out.tape⟩ := by
  have hn : (falseConfig M H out).state≠continueState M H := by
    intro h;have he := congrArg Fin.val h
    change (encodeStateB (nsA:=ns) (branch M H) (StandardBitCommonAlphabetBranch.encF out.state)).val=_ at he
    rw [stateF_val] at he
    have := out.state.isLt
    simp [continueState] at he;omega
  rw [step_base M H _ hn]
  have hs := StandardBitCommonAlphabetJoin.step_B M (branch M H)
    (StandardBitCommonAlphabetBranch.configF out) (encF_ne_zero _) (encF_ne_one _)
  unfold branch at hs
  rw [StandardBitCommonAlphabetBranch.finish_F H H _ out ha] at hs
  simp only [Option.map_some] at hs
  exact hs

theorem finish_true (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (out : Configuration nh nt) (ha : out.state=H.accept) :
    step (machine M H) 0 (trueConfig M H out)=some (bodyConfig (nh:=nh) ⟨M.start,out.head,out.tape⟩) := by
  simp [step,machine,trueConfig,bodyConfig,StandardBitCommonAlphabetJoin.configB,
    StandardBitCommonAlphabetBranch.configT,StandardBitCommonAlphabetJoin.configA,
    continueState_eq,ha,writtenTape,moveHead]

theorem selected_false_run (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (h : Int) (t : Int → Fin nt) (out : Configuration nh nt) (m : Nat)
    (hp : t h≠M.one) (hr : run H (ticks m) ⟨H.start,h,t⟩=some out)
    (ha : out.state=H.accept) :
    run (machine M H) (ticks (1+m+1)) (checkConfig M H h t)=some ⟨0,out.head,out.tape⟩ := by
  rw [ticks_add,ticks_add,run_append,run_append,run_ticks_one,check_step,if_neg hp,
    Option.bind_some,run_false M H _ out m hr,Option.bind_some,run_ticks_one,finish_false M H out ha]

theorem selected_true_run (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (h : Int) (t : Int → Fin nt) (out : Configuration nh nt) (m : Nat)
    (hp : t h=M.one) (hr : run H (ticks m) ⟨H.start,h,t⟩=some out)
    (ha : out.state=H.accept) :
    run (machine M H) (ticks (1+m+1)) (checkConfig M H h t)=
      some (bodyConfig (nh:=nh) ⟨M.start,out.head,out.tape⟩) := by
  rw [ticks_add,ticks_add,run_append,run_append,run_ticks_one,check_step,if_pos hp,
    Option.bind_some,run_true M H _ out m hr,Option.bind_some,run_ticks_one,finish_true M H out ha]

theorem cycle_false (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (start middle : Configuration ns nt) (out : Configuration nh nt) (n m : Nat)
    (hrM : run M (ticks n) start=some middle) (haM : middle.state=M.accept)
    (hp : middle.tape middle.head≠M.one)
    (hrH : run H (ticks m) ⟨H.start,middle.head,middle.tape⟩=some out)
    (haH : out.state=H.accept) :
    run (machine M H) (ticks (n+m+3)) (bodyConfig (nh:=nh) start)=some ⟨0,out.head,out.tape⟩ := by
  rw [show n+m+3=n+1+(1+m+1) by omega,ticks_add,ticks_add,run_append,run_append,
    run_body M H start middle n hrM,Option.bind_some,run_ticks_one,finish_body M H middle haM,
    Option.bind_some,selected_false_run M H _ _ out m hp hrH haH]

theorem cycle_true (M : DeterministicMachine ns nt) (H : DeterministicMachine nh nt)
    (start middle : Configuration ns nt) (out : Configuration nh nt) (n m : Nat)
    (hrM : run M (ticks n) start=some middle) (haM : middle.state=M.accept)
    (hp : middle.tape middle.head=M.one)
    (hrH : run H (ticks m) ⟨H.start,middle.head,middle.tape⟩=some out)
    (haH : out.state=H.accept) :
    run (machine M H) (ticks (n+m+3)) (bodyConfig (nh:=nh) start)=
      some (bodyConfig (nh:=nh) ⟨M.start,out.head,out.tape⟩) := by
  rw [show n+m+3=n+1+(1+m+1) by omega,ticks_add,ticks_add,run_append,run_append,
    run_body M H start middle n hrM,Option.bind_some,run_ticks_one,finish_body M H middle haM,
    Option.bind_some,selected_true_run M H _ _ out m hp hrH haH]

end PakFixedPolyomino.StandardBitFlagLoopControl
