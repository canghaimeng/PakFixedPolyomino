import PakFixedPolyomino.ULogSemantics
import Mathlib.Tactic

/-!
# Compilation of finite two-slot programs to universal bytecode

This normal form removes dependent finite alphabets from the universality
proof.  A bounded program has states `Fin ns`, letters `Fin nt`, and exactly
two Boolean-labelled rule slots.  Its compiler enumerates every source/read
pair in numeric order and emits precisely the occupied slots.
-/

namespace PakFixedPolyomino.ULogCompiler

open OneTapeTableau FiniteOneTapeProgram ULogBytecode

structure BoundedAction (ns nt : ℕ) where
  write : Fin nt
  target : Fin ns
  move : Move
  deriving DecidableEq, Fintype, Repr

structure BoundedProgram (ns nt : ℕ) where
  rule : Fin ns → Fin nt → Bool → Option (BoundedAction ns nt)

def actionCode {ns nt : ℕ} (a : BoundedAction ns nt) : ActionCode :=
  ⟨a.write.1, a.target.1, a.move⟩

def ruleCode {ns nt : ℕ} (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) : RuleCode :=
  ⟨q.1, read.1, slot, actionCode a⟩

def emitSlot {ns nt : ℕ} (p : BoundedProgram ns nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) : Option RuleCode :=
  (p.rule q read slot).map (ruleCode q read slot)

def emitPair {ns nt : ℕ} (p : BoundedProgram ns nt)
    (q : Fin ns) (read : Fin nt) : List RuleCode :=
  [emitSlot p q read false, emitSlot p q read true].filterMap id

def compile {ns nt : ℕ} (p : BoundedProgram ns nt) : ProgramCode :=
  (List.finRange ns).flatMap fun q =>
    (List.finRange nt).flatMap fun read => emitPair p q read

def toFiniteProgram {ns nt : ℕ} (p : BoundedProgram ns nt) :
    Program (Fin ns) (Fin nt) where
  rule q read slot := (p.rule q read (slot = 1)).map fun a =>
    ⟨a.write, a.target, a.move⟩

def ofFiniteAction {State Tape : Type*} {ns nt : ℕ}
    (eState : State ≃ Fin ns) (eTape : Tape ≃ Fin nt)
    (a : Action State Tape) : BoundedAction ns nt :=
  ⟨eTape a.write, eState a.target, a.move⟩

def ofFiniteProgram {State Tape : Type*} {ns nt : ℕ}
    (eState : State ≃ Fin ns) (eTape : Tape ≃ Fin nt)
    (p : Program State Tape) : BoundedProgram ns nt where
  rule q read slot :=
    (p.rule (eState.symm q) (eTape.symm read) (slotIndex slot)).map
      (ofFiniteAction eState eTape)

@[simp] theorem ofFiniteProgram_rule {State Tape : Type*} {ns nt : ℕ}
    (eState : State ≃ Fin ns) (eTape : Tape ≃ Fin nt)
    (p : Program State Tape) (q : State) (read : Tape) (slot : Bool) :
    (ofFiniteProgram eState eTape p).rule (eState q) (eTape read) slot =
      (p.rule q read (slotIndex slot)).map
        (ofFiniteAction eState eTape) := by
  simp [ofFiniteProgram]

@[simp] theorem emitPair_length_le_two {ns nt : ℕ}
    (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt) :
    (emitPair p q read).length ≤ 2 := by
  cases h₀ : emitSlot p q read false <;>
    cases h₁ : emitSlot p q read true <;>
      simp [emitPair, h₀, h₁]

theorem mem_emitPair {ns nt : ℕ} {p : BoundedProgram ns nt}
    {q : Fin ns} {read : Fin nt} {r : RuleCode}
    (h : r ∈ emitPair p q read) :
    (∃ a, p.rule q read false = some a ∧
      r = ruleCode q read false a) ∨
    ∃ a, p.rule q read true = some a ∧
      r = ruleCode q read true a := by
  unfold emitPair at h
  cases h₀ : emitSlot p q read false <;>
    cases h₁ : emitSlot p q read true <;>
      simp [h₀, h₁] at h
  · subst r
    right
    unfold emitSlot at h₁
    cases hp : p.rule q read true with
    | none => simp [hp] at h₁
    | some a =>
        simp [hp] at h₁
        subst h₁
        exact ⟨a, rfl, rfl⟩
  · subst r
    left
    unfold emitSlot at h₀
    cases hp : p.rule q read false with
    | none => simp [hp] at h₀
    | some a =>
        simp [hp] at h₀
        subst h₀
        exact ⟨a, rfl, rfl⟩
  · rcases h with rfl | rfl
    · left
      unfold emitSlot at h₀
      cases hp : p.rule q read false with
      | none => simp [hp] at h₀
      | some a =>
          simp [hp] at h₀
          subst h₀
          exact ⟨a, rfl, rfl⟩
    · right
      unfold emitSlot at h₁
      cases hp : p.rule q read true with
      | none => simp [hp] at h₁
      | some a =>
          simp [hp] at h₁
          subst h₁
          exact ⟨a, rfl, rfl⟩

theorem compile_rule_bounded {ns nt : ℕ} (p : BoundedProgram ns nt)
    {r : RuleCode} (h : r ∈ compile p) :
    r.source < ns ∧ r.read < nt ∧ r.action.write < nt ∧
      r.action.target < ns := by
  simp only [compile, List.mem_flatMap, List.mem_finRange] at h
  rcases h with ⟨q, -, read, -, hr⟩
  rcases mem_emitPair hr with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩ <;>
    exact ⟨q.2, read.2, a.write.2, a.target.2⟩

theorem compile_length_le {ns nt : ℕ} (p : BoundedProgram ns nt) :
    (compile p).length ≤ 2 * ns * nt := by
  have inner (q : Fin ns) : ∀ reads : List (Fin nt),
      (reads.flatMap fun read => emitPair p q read).length ≤
        reads.length * 2 := by
    intro reads
    induction reads with
    | nil => simp
    | cons read reads ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hpair := emitPair_length_le_two p q read
        omega
  have outer : ∀ qs : List (Fin ns),
      (qs.flatMap fun q =>
        (List.finRange nt).flatMap fun read => emitPair p q read).length ≤
          qs.length * (2 * nt) := by
    intro qs
    induction qs with
    | nil => simp
    | cons q qs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hq := inner q (List.finRange nt)
        simp only [List.length_finRange] at hq
        have hq' : ((List.finRange nt).flatMap fun read =>
            emitPair p q read).length ≤ 2 * nt := by
          simpa [Nat.mul_comm] using hq
        calc
          ((List.finRange nt).flatMap fun read => emitPair p q read).length +
              (qs.flatMap fun q =>
                (List.finRange nt).flatMap fun read => emitPair p q read).length
              ≤ 2 * nt + qs.length * (2 * nt) := Nat.add_le_add hq' ih
          _ = (qs.length + 1) * (2 * nt) := by ring
  unfold compile
  calc
    ((List.finRange ns).flatMap fun q =>
        (List.finRange nt).flatMap fun read => emitPair p q read).length
        ≤ (List.finRange ns).length * (2 * nt) := outer _
    _ = 2 * ns * nt := by simp; ring

theorem compile_mem_ruleCode {ns nt : ℕ} (p : BoundedProgram ns nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (h : p.rule q read slot = some a) :
    ruleCode q read slot a ∈ compile p := by
  simp only [compile, List.mem_flatMap, List.mem_finRange]
  refine ⟨q, trivial, read, trivial, ?_⟩
  cases slot <;> simp [emitPair, emitSlot, h]

theorem compile_mem_origin {ns nt : ℕ} {p : BoundedProgram ns nt}
    {r : RuleCode} (h : r ∈ compile p) :
    ∃ (q : Fin ns) (read : Fin nt) (slot : Bool)
      (a : BoundedAction ns nt),
      p.rule q read slot = some a ∧ r = ruleCode q read slot a := by
  simp only [compile, List.mem_flatMap, List.mem_finRange] at h
  rcases h with ⟨q, -, read, -, hr⟩
  rcases mem_emitPair hr with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact ⟨q, read, false, a, ha, rfl⟩
  · exact ⟨q, read, true, a, ha, rfl⟩

@[simp] theorem ruleMatches_ruleCode {ns nt : ℕ}
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt) :
    ruleMatches q.1 read.1 slot (ruleCode q read slot a) = true := by
  simp [ruleMatches, ruleCode]

theorem compiled_matching_rule_unique {ns nt : ℕ}
    (p : BoundedProgram ns nt) (q : Fin ns) (read : Fin nt)
    (slot : Bool) (a : BoundedAction ns nt) (ha : p.rule q read slot = some a)
    {r : RuleCode} (hr : r ∈ compile p)
    (hmatch : ruleMatches q.1 read.1 slot r = true) :
    r = ruleCode q read slot a := by
  rcases compile_mem_origin hr with ⟨q', read', slot', a', ha', rfl⟩
  change decide (q'.1 = q.1 ∧ read'.1 = read.1 ∧ slot' = slot) = true
    at hmatch
  have hm : q'.1 = q.1 ∧ read'.1 = read.1 ∧ slot' = slot :=
    of_decide_eq_true hmatch
  have hq : q' = q := Fin.ext hm.1
  have hread : read' = read := Fin.ext hm.2.1
  have hslot : slot' = slot := hm.2.2
  subst q'
  subst read'
  subst slot'
  rw [ha] at ha'
  have haa : a' = a := (Option.some.inj ha').symm
  subst a'
  rfl

theorem find?_eq_some_of_unique {A : Type*} (pred : A → Bool)
    (xs : List A) (x : A) (hx : x ∈ xs) (hpred : pred x = true)
    (hunique : ∀ y, y ∈ xs → pred y = true → y = x) :
    xs.find? pred = some x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      by_cases hy : pred y = true
      · have hyx := hunique y (by simp) hy
        subst y
        simp [List.find?, hpred]
      · have hyf : pred y = false := by
          cases hval : pred y <;> simp_all
        have hxy : x ∈ ys := by
          rcases (List.mem_cons.mp hx) with hxy | hxy
          · subst y
            exact (hy hpred).elim
          · exact hxy
        have hi := ih hxy (fun z hz => hunique z (by simp [hz]))
        simp [List.find?, hyf, hi]

theorem lookup_compile {ns nt : ℕ} (p : BoundedProgram ns nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) :
    lookupRule (compile p) q.1 read.1 slot =
      (p.rule q read slot).map actionCode := by
  cases ha : p.rule q read slot with
  | none =>
      cases hl : lookupRule (compile p) q.1 read.1 slot with
      | none => simp [ha, hl]
      | some a =>
          exfalso
          rcases lookupRule_some_mem hl with
            ⟨r, hr, hq, hread, hslot, haction⟩
          rcases compile_mem_origin hr with
            ⟨q', read', slot', a', ha', rfl⟩
          simp [ruleCode] at hq hread hslot
          have eqq : q' = q := Fin.ext hq
          have eqread : read' = read := Fin.ext hread
          subst q'
          subst read'
          subst slot'
          rw [ha] at ha'
          cases ha'
  | some a =>
      unfold lookupRule
      have hmem := compile_mem_ruleCode p q read slot a ha
      have hfind := find?_eq_some_of_unique
        (ruleMatches q.1 read.1 slot) (compile p)
        (ruleCode q read slot a) hmem (ruleMatches_ruleCode q read slot a)
        (fun r hr hm => compiled_matching_rule_unique p q read slot a ha hr hm)
      rw [hfind]
      simp [ha, ruleCode, actionCode]

structure BoundedConfig (ns nt : ℕ) where
  state : Fin ns
  leftRev : List (Fin nt)
  focus : Fin nt
  right : List (Fin nt)
  deriving DecidableEq, Repr

def liftConfig {ns nt : ℕ} (p : BoundedProgram ns nt)
    (c : BoundedConfig ns nt) : ULogSemantics.Config :=
  ⟨compile p, c.state.1, c.leftRev.map Fin.val, c.focus.1,
    c.right.map Fin.val⟩

def applyBounded {ns nt : ℕ} (blank : Fin nt)
    (c : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    BoundedConfig ns nt :=
  match a.move with
  | .stay => { c with state := a.target, focus := a.write }
  | .right =>
      match c.right with
      | [] => ⟨a.target, a.write :: c.leftRev, blank, []⟩
      | y :: ys => ⟨a.target, a.write :: c.leftRev, y, ys⟩
  | .left =>
      match c.leftRev with
      | [] => ⟨a.target, [], blank, a.write :: c.right⟩
      | y :: ys => ⟨a.target, ys, y, a.write :: c.right⟩

theorem liftConfig_applyBounded {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (hblank : blank.1 = ULogSemantics.blankCode)
    (c : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    liftConfig p (applyBounded blank c a) =
      ULogSemantics.applyAction (liftConfig p c) (actionCode a) := by
  cases hm : a.move with
  | stay => simp [applyBounded, ULogSemantics.applyAction, actionCode, hm,
      liftConfig]
  | right =>
      cases hr : c.right <;>
        simp [applyBounded, ULogSemantics.applyAction, actionCode, hm, hr,
          liftConfig, hblank]
  | left =>
      cases hl : c.leftRev <;>
        simp [applyBounded, ULogSemantics.applyAction, actionCode, hm, hl,
          liftConfig, hblank]

def boundedHalted {ns nt : ℕ} (c : BoundedConfig ns nt) : Bool :=
  decide (c.state.1 < 2)

def boundedAccepting {ns nt : ℕ} (c : BoundedConfig ns nt) : Bool :=
  decide (c.state.1 = ULogSemantics.acceptCode)

def boundedStepSlot {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (slot : Bool) (c : BoundedConfig ns nt) :
    Option (BoundedConfig ns nt) :=
  if boundedHalted c then none
  else (p.rule c.state c.focus slot).map (applyBounded blank c)

def boundedNext {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (c : BoundedConfig ns nt) : List (BoundedConfig ns nt) :=
  [boundedStepSlot p blank false c,
    boundedStepSlot p blank true c].filterMap id

@[simp] theorem boundedNext_length_le_two {ns nt : ℕ}
    (p : BoundedProgram ns nt) (blank : Fin nt) (c : BoundedConfig ns nt) :
    (boundedNext p blank c).length ≤ 2 := by
  cases h₀ : boundedStepSlot p blank false c <;>
    cases h₁ : boundedStepSlot p blank true c <;>
      simp [boundedNext, h₀, h₁]

theorem stepSlot_liftConfig {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (hblank : blank.1 = ULogSemantics.blankCode)
    (slot : Bool) (c : BoundedConfig ns nt) :
    ULogSemantics.stepSlot slot (liftConfig p c) =
      (boundedStepSlot p blank slot c).map (liftConfig p) := by
  unfold ULogSemantics.stepSlot boundedStepSlot
  have hhalt : ULogSemantics.halted (liftConfig p c) = boundedHalted c := by
    rfl
  rw [hhalt]
  cases hh : boundedHalted c <;> simp [hh]
  change Option.map (ULogSemantics.applyAction (liftConfig p c))
      (lookupRule (compile p) c.state.1 c.focus.1 slot) =
    Option.map (liftConfig p ∘ applyBounded blank c)
      (p.rule c.state c.focus slot)
  rw [lookup_compile]
  cases ha : p.rule c.state c.focus slot with
  | none => simp [ha]
  | some a =>
      simp [ha]
      exact (liftConfig_applyBounded p blank hblank c a).symm

theorem next_liftConfig {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (hblank : blank.1 = ULogSemantics.blankCode)
    (c : BoundedConfig ns nt) :
    ULogSemantics.next (liftConfig p c) =
      (boundedNext p blank c).map (liftConfig p) := by
  rw [show ULogSemantics.next (liftConfig p c) =
      [ULogSemantics.stepSlot false (liftConfig p c),
        ULogSemantics.stepSlot true (liftConfig p c)].filterMap id by rfl,
    stepSlot_liftConfig p blank hblank,
    stepSlot_liftConfig p blank hblank]
  unfold boundedNext
  cases boundedStepSlot p blank false c <;>
    cases boundedStepSlot p blank true c <;> rfl

theorem boundedAccepting_halted {ns nt : ℕ} {c : BoundedConfig ns nt}
    (h : boundedAccepting c = true) : boundedHalted c = true := by
  have hs : c.state.1 = ULogSemantics.acceptCode := by
    simpa [boundedAccepting] using h
  simp [boundedHalted, hs, ULogSemantics.acceptCode]

def boundedMachine {ns nt : ℕ} (p : BoundedProgram ns nt)
    (blank : Fin nt) (start : BitString → BoundedConfig ns nt) :
    BinaryNondeterministicMachine where
  Config := BoundedConfig ns nt
  start := start
  next := boundedNext p blank
  halt := boundedHalted
  accept := boundedAccepting
  accept_halts := fun _ h => boundedAccepting_halted h
  binary_branching := boundedNext_length_le_two p blank

theorem acceptingPaths_liftConfig {ns nt : ℕ}
    (p : BoundedProgram ns nt) (blank : Fin nt)
    (hblank : blank.1 = ULogSemantics.blankCode)
    (start : BitString → BoundedConfig ns nt) (t : ℕ)
    (c : BoundedConfig ns nt) :
    ULogSemantics.machine.acceptingPaths t (liftConfig p c) =
      (boundedMachine p blank start).acceptingPaths t c := by
  induction t generalizing c with
  | zero =>
      simp [BinaryNondeterministicMachine.acceptingPaths,
        ULogSemantics.machine, boundedMachine, ULogSemantics.halted,
        ULogSemantics.accepting, boundedHalted, boundedAccepting, liftConfig]
  | succ t ih =>
      simp only [BinaryNondeterministicMachine.acceptingPaths]
      simp only [ULogSemantics.machine, boundedMachine]
      have hh : ULogSemantics.halted (liftConfig p c) = boundedHalted c := rfl
      by_cases hc : boundedHalted c = true
      · have hu : ULogSemantics.halted (liftConfig p c) = true :=
          hh.trans hc
        have ha : ULogSemantics.accepting (liftConfig p c) =
            boundedAccepting c := rfl
        simp [hu, hc, ha]
        rfl
      · have hcf : boundedHalted c = false := by
          cases hv : boundedHalted c <;> simp_all
        have hu : ULogSemantics.halted (liftConfig p c) = false :=
          hh.trans hcf
        simp only [hu, hcf, Bool.false_eq_true, if_false]
        rw [next_liftConfig p blank hblank]
        simp only [List.map_map, Function.comp_def]
        apply congrArg List.sum
        apply List.map_congr_left
        intro x hx
        simpa [ULogSemantics.machine, boundedMachine] using ih x

def encodeInstance {ns nt : ℕ} (p : BoundedProgram ns nt)
    (input : BitString) : BitString :=
  encodeProgram (compile p) ++ encodePayload input []

@[simp] theorem decodeProgramPrefix_encodeInstance {ns nt : ℕ}
    (p : BoundedProgram ns nt) (input : BitString) :
    decodeProgramPrefix (encodeInstance p input) =
      some (compile p, encodePayload input []) := by
  simp [encodeInstance]

def boundedBit {nt : ℕ} (zero one : Fin nt) : Bool → Fin nt
  | false => zero
  | true => one

def boundedInitial {ns nt : ℕ} (qStart : Fin ns)
    (zero one blank : Fin nt) (input : BitString) : BoundedConfig ns nt :=
  match input with
  | [] => ⟨qStart, [], blank, []⟩
  | b :: bs => ⟨qStart, [], boundedBit zero one b,
      bs.map (boundedBit zero one)⟩

theorem map_boundedBit_val {nt : ℕ} (zero one : Fin nt)
    (hzero : zero.1 = 0) (hone : one.1 = 1) (bits : List Bool) :
    (bits.map (boundedBit zero one)).map Fin.val =
      bits.map ULogSemantics.bitCode := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      cases b <;> simp [boundedBit, ULogSemantics.bitCode, hzero, hone, ih]

theorem liftConfig_boundedInitial {ns nt : ℕ}
    (p : BoundedProgram ns nt) (qStart : Fin ns)
    (zero one blank : Fin nt)
    (hq : qStart.1 = ULogSemantics.startCode)
    (hzero : zero.1 = 0) (hone : one.1 = 1)
    (hblank : blank.1 = ULogSemantics.blankCode) (input : BitString) :
    liftConfig p (boundedInitial qStart zero one blank input) =
      ULogSemantics.start (encodeInstance p input) := by
  cases input with
  | nil =>
      unfold ULogSemantics.start encodeInstance
      rw [decodeProgramPrefix_encode_prefix]
      simp [boundedInitial, liftConfig, ULogSemantics.startFrom,
        ULogSemantics.initialTape, hq, hblank]
  | cons b bits =>
      cases b <;>
        simp [boundedInitial, liftConfig, ULogSemantics.start, encodeInstance,
          encodePayload, decodePayload, boundedBit,
          ULogSemantics.startFrom, ULogSemantics.initialTape,
          ULogSemantics.bitCode,
          hq, hzero, hone, hblank, map_boundedBit_val]

/-- Semantic parsimonious universality at every explicit clock value.  The
remaining source-hardness layer only has to supply the standard padding clock
and the effective one-tape normalization; no accepting-path accounting is
left in the bytecode compiler. -/
theorem acceptingPaths_encodeInstance {ns nt : ℕ}
    (p : BoundedProgram ns nt) (qStart : Fin ns)
    (zero one blank : Fin nt)
    (hq : qStart.1 = ULogSemantics.startCode)
    (hzero : zero.1 = 0) (hone : one.1 = 1)
    (hblank : blank.1 = ULogSemantics.blankCode)
    (t : ℕ) (input : BitString) :
    ULogSemantics.machine.acceptingPaths t
        (ULogSemantics.start (encodeInstance p input)) =
      (boundedMachine p blank
        (boundedInitial qStart zero one blank)).acceptingPaths t
          (boundedInitial qStart zero one blank input) := by
  rw [← liftConfig_boundedInitial p qStart zero one blank hq hzero hone
    hblank input]
  exact acceptingPaths_liftConfig p blank hblank
    (boundedInitial qStart zero one blank) t _

end PakFixedPolyomino.ULogCompiler
