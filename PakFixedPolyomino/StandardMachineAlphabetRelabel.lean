import PakFixedPolyomino.StandardBitMachineComposition

/-! Literal finite-alphabet relabeling. One source tick is one target tick.
The inverse below covers every raw slot word from the encoded initialization.
Explicit A/B embeddings instantiate the common binary and blank codes. -/
namespace PakFixedPolyomino.StandardMachineAlphabetRelabel
open StandardNondeterministicMachine StandardBitTime StandardBitMachineComposition
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (writtenTape moveHead)

structure AlphabetMap (nt mt : Nat) where
  encode : Fin nt → Fin mt
  decode : Fin mt → Option (Fin nt)
  decode_encode : ∀ a, decode (encode a)=some a

variable {ns nt mt branching : Nat}

theorem encode_injective (E : AlphabetMap nt mt) : Function.Injective E.encode := by
  intro a b h
  have he := congrArg E.decode h
  simpa only [E.decode_encode,Option.some.injEq] using he

def liftAction (E : AlphabetMap nt mt) (a : Action (Fin ns) (Fin nt)) :
    Action (Fin ns) (Fin mt) := ⟨E.encode a.write,a.target,a.move⟩

def rule (M : Machine ns nt branching) (E : AlphabetMap nt mt)
    (q : Fin ns) (s : Fin mt) (slot : Fin branching) :
    Option (Action (Fin ns) (Fin mt)) :=
  (E.decode s).bind fun a => (M.rule q a slot).map (liftAction E)

def machine (M : Machine ns nt branching) (E : AlphabetMap nt mt) : Machine ns mt branching where
  rule := rule M E
  start := M.start
  accept := M.accept
  reject := M.reject
  accept_ne_reject := M.accept_ne_reject
  blank := E.encode M.blank
  zero := E.encode M.zero
  one := E.encode M.one
  blank_ne_zero := fun h => M.blank_ne_zero (encode_injective E h)
  blank_ne_one := fun h => M.blank_ne_one (encode_injective E h)
  zero_ne_one := fun h => M.zero_ne_one (encode_injective E h)
  accept_terminal := by
    intro s slot
    simp only [rule]
    cases E.decode s <;> simp [M.accept_terminal]
  reject_terminal := by
    intro s slot
    simp only [rule]
    cases E.decode s <;> simp [M.reject_terminal]

def config (E : AlphabetMap nt mt) (c : Configuration ns nt) : Configuration ns mt :=
  ⟨c.state,c.head,fun z => E.encode (c.tape z)⟩

theorem update_eq (E : AlphabetMap nt mt) (t : Int → Fin nt) (h : Int) (a : Fin nt) :
    Function.update (fun z => E.encode (t z)) h (E.encode a)=
      fun z => E.encode (Function.update t h a z) := by
  funext z
  by_cases hz : z=h
  · subst z;simp
  · simp [Function.update_of_ne hz]

theorem step_exact (M : Machine ns nt branching) (E : AlphabetMap nt mt)
    (slot : Fin branching) (c : Configuration ns nt) :
    step (machine M E) slot (config E c)=(step M slot c).map (config E) := by
  simp only [step,machine,rule,config,E.decode_encode,Option.bind_some]
  cases hs : M.rule c.state (c.tape c.head) slot with
  | none => simp
  | some a =>
    simp only [Option.map_some,liftAction]
    congr 1
    apply config_ext
    · rfl
    · rfl
    · exact update_eq E c.tape c.head a.write

theorem run_exact (M : Machine ns nt branching) (E : AlphabetMap nt mt)
    (slots : List (Fin branching)) (c : Configuration ns nt) :
    run (machine M E) slots (config E c)=(run M slots c).map (config E) := by
  induction slots generalizing c with
  | nil => simp
  | cons slot slots ih =>
    rw [run_cons,run_cons,step_exact]
    cases hs : step M slot c <;> simp [hs,ih]

theorem initial_eq (M : Machine ns nt branching) (E : AlphabetMap nt mt) (x : List Bool) :
    config E (initial M x)=initial (machine M E) x := by
  apply config_ext
  · rfl
  · rfl
  · funext z
    simp only [config,initial,inputTape,machine]
    split_ifs <;> rfl

theorem all_raw_run_inverse (M : Machine ns nt branching) (E : AlphabetMap nt mt)
    (x : List Bool) (slots : List (Fin branching)) (out : Configuration ns mt) :
    run (machine M E) slots (initial (machine M E) x)=some out ↔
      ∃ source, run M slots (initial M x)=some source ∧ out=config E source := by
  rw [← initial_eq,run_exact]
  cases hs : run M slots (initial M x) <;> simp
  exact eq_comm

theorem accepted_iff (M : Machine ns nt branching) (E : AlphabetMap nt mt)
    (x : List Bool) (slots : List (Fin branching)) :
    Accepted (machine M E) x slots ↔ Accepted M x slots := by
  unfold Accepted
  rw [← initial_eq,run_exact,Option.map_map]
  simp [machine,config,Function.comp]

theorem output (M : DeterministicMachine ns nt) (E : AlphabetMap nt mt)
    (y : List Bool) (out : Configuration ns nt) (ho : Output M y out) :
    Output (machine M E) y (config E out) := by
  refine ⟨ho.1,ho.2.1,?_⟩
  funext z
  simp only [config,ho.2.2,inputTape,machine]
  split_ifs <;> rfl

theorem computes (M : DeterministicMachine ns nt) (E : AlphabetMap nt mt)
    (f : List Bool → List Bool) (p : Nat → Nat) (hc : ComputesWithin M f p) :
    ComputesWithin (machine M E) f p := by
  intro x
  obtain ⟨n,out,hn,hr,ho⟩ := hc x
  refine ⟨n,config E out,hn,?_,output M E (f x) out ho⟩
  rw [← initial_eq,run_exact,hr]
  rfl

def mapA {ntB : Nat} (M : DeterministicMachine ns nt) : AlphabetMap nt (nt+ntB+3) where
  encode := encodeTapeA M
  decode := decodeTapeA M
  decode_encode := decodeTapeA_encode M

def mapB {ntA : Nat} (M : DeterministicMachine ns nt) : AlphabetMap nt (ntA+nt+3) where
  encode := encodeTapeB M
  decode := decodeTapeB M
  decode_encode := decodeTapeB_encode M

theorem codes_A {ntB : Nat} (M : DeterministicMachine ns nt) :
    (machine M (mapA (ntB:=ntB) M)).blank=2 ∧
    (machine M (mapA (ntB:=ntB) M)).zero=0 ∧
    (machine M (mapA (ntB:=ntB) M)).one=1 := by
  simp [machine,mapA,encodeTapeA_blank,encodeTapeA_zero,encodeTapeA_one]
  apply Fin.ext
  change 2 = 2 % (nt+ntB+3)
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem codes_B {ntA : Nat} (M : DeterministicMachine ns nt) :
    (machine M (mapB (ntA:=ntA) M)).blank=2 ∧
    (machine M (mapB (ntA:=ntA) M)).zero=0 ∧
    (machine M (mapB (ntA:=ntA) M)).one=1 := by
  simp [machine,mapB,encodeTapeB_blank,encodeTapeB_zero,encodeTapeB_one]
  apply Fin.ext
  change 2 = 2 % (ntA+nt+3)
  exact (Nat.mod_eq_of_lt (by omega)).symm

end PakFixedPolyomino.StandardMachineAlphabetRelabel
