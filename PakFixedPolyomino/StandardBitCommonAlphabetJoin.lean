import PakFixedPolyomino.StandardBitMachineComposition

/-! Sequential control for two ordinary machines sharing a literal alphabet.
The handoff preserves the ENTIRE tape, including retained raw tracks. -/
namespace PakFixedPolyomino.StandardBitCommonAlphabetJoin
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition
open FiniteOneTapeSemantics (moveHead writtenTape)
open FiniteOneTapeProgram (Action)
variable {nsA nsB nt : Nat}

def liftA (a : Action (Fin nsA) (Fin nt)) : Action (Fin (nsA+nsB+2)) (Fin nt) :=
  ⟨a.write,encodeStateA a.target,a.move⟩
def liftB (N : DeterministicMachine nsB nt) (a : Action (Fin nsB) (Fin nt)) :
    Action (Fin (nsA+nsB+2)) (Fin nt) := ⟨a.write,encodeStateB N a.target,a.move⟩

def handoff (N : DeterministicMachine nsB nt) (s : Fin nt) : Action (Fin (nsA+nsB+2)) (Fin nt) :=
  ⟨s,encodeStateB N N.start,.stay⟩

def rule (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (q : Fin (nsA+nsB+2)) (s : Fin nt) (_slot : Fin 1) :
    Option (Action (Fin (nsA+nsB+2)) (Fin nt)) :=
  (decodeStateA (nsB := nsB) q).elim
    ((decodeStateB (nsA := nsA) q).elim none fun qB =>
      if qB = N.accept ∨ qB = N.reject then none else (N.rule qB s 0).map (liftB N))
    fun qA => if qA = M.accept then some (handoff N s) else (M.rule qA s 0).map liftA

def machine (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt) :
    DeterministicMachine (nsA+nsB+2) nt where
  rule := rule M N
  start := encodeStateA M.start
  accept := acceptC
  reject := rejectC
  accept_ne_reject := by intro h;exact Nat.zero_ne_one (congrArg Fin.val h)
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal := by
    intro s slot
    have hA : decodeStateA (nsB := nsB) (acceptC (nsA := nsA) (nsB := nsB)) = none := by
      have hn : ¬(2 ≤ (0 : Nat) ∧ 0 < 2+nsA) := by omega
      simp [decodeStateA,acceptC,hn]
    have hB : decodeStateB (nsA := nsA) (acceptC (nsA := nsA) (nsB := nsB)) = none := by
      have hn : ¬(2+nsA ≤ (0 : Nat) ∧ 0 < 2+nsA+nsB) := by omega
      simp [decodeStateB,acceptC,hn]
    simp [rule,hA,hB]
  reject_terminal := by
    intro s slot
    have hA : decodeStateA (nsB := nsB) (rejectC (nsA := nsA) (nsB := nsB)) = none := by
      have hn : ¬(2 ≤ (1 : Nat) ∧ 1 < 2+nsA) := by omega
      simp [decodeStateA,rejectC,hn]
    have hB : decodeStateB (nsA := nsA) (rejectC (nsA := nsA) (nsB := nsB)) = none := by
      have hn : ¬(2+nsA ≤ (1 : Nat) ∧ 1 < 2+nsA+nsB) := by omega
      simp [decodeStateB,rejectC,hn]
    simp [rule,hA,hB]

def configA (c : Configuration nsA nt) : Configuration (nsA+nsB+2) nt :=
  ⟨encodeStateA c.state,c.head,c.tape⟩
def configB (N : DeterministicMachine nsB nt) (c : Configuration nsB nt) :
    Configuration (nsA+nsB+2) nt := ⟨encodeStateB N c.state,c.head,c.tape⟩

theorem initial_eq (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (x : List Bool) : initial (machine M N) x = configA (initial M x) := rfl

theorem rule_A (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (q : Fin nsA) (s : Fin nt) (h : q ≠ M.accept) :
    rule M N (encodeStateA q) s 0 = (M.rule q s 0).map liftA := by
  simp [rule,decodeStateA_encode,h]

theorem rule_handoff (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (s : Fin nt) : rule M N (encodeStateA M.accept) s 0 = some (handoff N s) := by
  simp [rule,decodeStateA_encode]

theorem rule_B (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (q : Fin nsB) (s : Fin nt) (ha : q ≠ N.accept) (hr : q ≠ N.reject) :
    rule M N (encodeStateB N q) s 0 = (N.rule q s 0).map (liftB N) := by
  have hA : decodeStateA (nsB := nsB) (encodeStateB (nsA := nsA) N q) = none := by
    have henc := encodeStateB_other (nsA := nsA) N q ha hr
    have hn : ¬(2 ≤ (encodeStateB (nsA := nsA) N q).val ∧
        (encodeStateB (nsA := nsA) N q).val < 2+nsA) := by
      rw [henc]
      have := q.isLt
      simp
    simp [decodeStateA,hn]
  simp [rule,hA,decodeStateB_encode_other,ha,hr]

theorem step_A (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (c : Configuration nsA nt) (h : c.state ≠ M.accept) :
    step (machine M N) 0 (configA c) = (step M 0 c).map configA := by
  simp only [step,machine,configA]
  rw [rule_A M N c.state (c.tape c.head) h]
  cases hr : M.rule c.state (c.tape c.head) 0 <;>
    simp [liftA,configA,writtenTape,hr]

theorem step_handoff (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (c : Configuration nsA nt) (h : c.state = M.accept) :
    step (machine M N) 0 (configA c) = some (configB N ⟨N.start,c.head,c.tape⟩) := by
  simp only [step,machine,configA,h]
  rw [rule_handoff]
  simp [handoff,configB,moveHead,writtenTape]

theorem step_B (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (c : Configuration nsB nt) (ha : c.state ≠ N.accept) (hr : c.state ≠ N.reject) :
    step (machine M N) 0 (configB N c) = (step N 0 c).map (configB N) := by
  simp only [step,machine,configB]
  rw [rule_B M N c.state (c.tape c.head) ha hr]
  cases hs : N.rule c.state (c.tape c.head) 0 <;>
    simp [liftB,configB,writtenTape,hs]

theorem run_A (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (c out : Configuration nsA nt) (n : Nat) (hr : run M (ticks n) c = some out) :
    run (machine M N) (ticks n) (configA c) = some (configA out) := by
  induction n generalizing c with
  | zero =>
    have he : c = out := Option.some.inj hr
    subst out
    simp [ticks]
  | succ n ih =>
    rw [ticks_succ] at hr ⊢
    have hn : c.state ≠ M.accept := by
      intro ha
      have hbad := run_accept_nonempty_none M c ha (0 :: ticks n) (List.cons_ne_nil _ _)
      rw [hbad] at hr
      cases hr
    rw [run_cons] at hr ⊢
    cases hs : step M 0 c with
    | none => simp [hs] at hr
    | some middle =>
      simp [hs] at hr
      simp [step_A M N c hn,hs]
      exact ih middle hr

theorem run_B (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (c out : Configuration nsB nt) (n : Nat) (hr : run N (ticks n) c = some out) :
    run (machine M N) (ticks n) (configB N c) = some (configB N out) := by
  induction n generalizing c with
  | zero =>
    have he : c = out := Option.some.inj hr
    subst out
    simp [ticks]
  | succ n ih =>
    rw [ticks_succ] at hr ⊢
    have hnA : c.state ≠ N.accept := by
      intro ha
      have hbad := run_accept_nonempty_none N c ha (0 :: ticks n) (List.cons_ne_nil _ _)
      rw [hbad] at hr
      cases hr
    have hnR : c.state ≠ N.reject := by
      intro ha
      have hbad : run N (0 :: ticks n) c = none := by
        simp [run_cons,step_reject_none N 0 c ha]
      rw [hbad] at hr
      cases hr
    rw [run_cons] at hr ⊢
    cases hs : step N 0 c with
    | none => simp [hs] at hr
    | some middle =>
      simp [hs] at hr
      simp [step_B M N c hnA hnR,hs]
      exact ih middle hr

theorem joined_run (M : DeterministicMachine nsA nt) (N : DeterministicMachine nsB nt)
    (start middle : Configuration nsA nt) (out : Configuration nsB nt) (n m : Nat)
    (hM : run M (ticks n) start = some middle) (ha : middle.state = M.accept)
    (hN : run N (ticks m) ⟨N.start,middle.head,middle.tape⟩ = some out) :
    run (machine M N) (ticks (n+1+m)) (configA start) = some (configB N out) := by
  rw [ticks_add,run_append,ticks_add,run_append,run_A M N start middle n hM,
    Option.bind_some,run_ticks_one,step_handoff M N middle ha,Option.bind_some,run_B M N _ out m hN]

end PakFixedPolyomino.StandardBitCommonAlphabetJoin
