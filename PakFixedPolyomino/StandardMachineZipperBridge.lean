import PakFixedPolyomino.StandardMachinePathRecursion
import PakFixedPolyomino.StandardMachineCanonicalCodes
import PakFixedPolyomino.ULogSource

/-! # Counted ordinary-machine to zipper bridge

Convert an ordinary two-slot machine with accept code 0 and reject code 1
into `ULogCompiler.BoundedProgram` data. The physical zipper denotation
commutes with genuine one-cell transitions and with arbitrary labelled
raw runs. For every cutoff, `acceptingCount` equals
`boundedMachine.acceptingPaths`.
-/

namespace PakFixedPolyomino.StandardMachineZipperBridge

open StandardNondeterministicMachine
open StandardMachinePathRecursion
open ULogCompiler
open FiniteOneTapeSemantics (Config moveHead writtenTape)
open FiniteOneTapeProgram (Action)

variable {ns nt : ℕ}

def slotIndex : Bool → Fin 2
  | false => ⟨0, by omega⟩
  | true => ⟨1, by omega⟩

theorem slotIndex_false : slotIndex false = ⟨0, by omega⟩ := rfl
theorem slotIndex_true : slotIndex true = ⟨1, by omega⟩ := rfl

def toBoundedAction (a : Action (Fin ns) (Fin nt)) : BoundedAction ns nt :=
  ⟨a.write, a.target, a.move⟩

@[simp] theorem toBoundedAction_write (a : Action (Fin ns) (Fin nt)) :
    (toBoundedAction a).write = a.write := rfl
@[simp] theorem toBoundedAction_target (a : Action (Fin ns) (Fin nt)) :
    (toBoundedAction a).target = a.target := rfl
@[simp] theorem toBoundedAction_move (a : Action (Fin ns) (Fin nt)) :
    (toBoundedAction a).move = a.move := rfl

def toBounded (M : Machine ns nt 2) : BoundedProgram ns nt where
  rule q read slot := (M.rule q read (slotIndex slot)).map toBoundedAction

def physical (blank : Fin nt) (head : Int) (z : BoundedConfig ns nt) :
    Configuration ns nt where
  state := z.state
  head := head
  tape := fun p =>
    if p = head then z.focus
    else if p < head then
      z.leftRev.getD (Int.toNat (head - p - 1)) blank
    else
      z.right.getD (Int.toNat (p - head - 1)) blank

theorem config_ext {c₁ c₂ : Configuration ns nt}
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

theorem physical_state (blank : Fin nt) (head : Int)
    (z : BoundedConfig ns nt) :
    (physical blank head z).state = z.state := rfl

theorem physical_head (blank : Fin nt) (head : Int)
    (z : BoundedConfig ns nt) :
    (physical blank head z).head = head := rfl

theorem physical_tape_head (blank : Fin nt) (head : Int)
    (z : BoundedConfig ns nt) :
    (physical blank head z).tape head = z.focus := by
  simp [physical]

theorem toNat_add_one {z : ℤ} (h : 0 ≤ z) : (z + 1).toNat = z.toNat + 1 := by
  have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
  have h1 : 0 ≤ z + 1 := by omega
  have hsucc : ((z.toNat + 1 : ℕ) : ℤ) = z + 1 := by simp [hz]
  exact Int.ofNat_inj.mp (by
    have := Int.toNat_of_nonneg h1
    simp [this, hsucc])

theorem toNat_sub_one {p : ℤ} (hp : 0 < p) : (p - 1).toNat = p.toNat - 1 := by
  have hnn : 0 ≤ p - 1 := by omega
  have hsucc := toNat_add_one hnn
  have : p - 1 + 1 = p := by omega
  rw [this] at hsucc
  omega

theorem getD_cons_zero {α} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a := rfl

theorem getD_cons_succ {α} (a : α) (l : List α) (n : ℕ) (d : α) :
    (a :: l).getD (n + 1) d = l.getD n d := rfl

theorem eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem boundedBit_spec (zero one : Fin nt) (b : Bool) :
    boundedBit zero one b = if b then one else zero := by
  cases b <;> rfl

theorem getD_map_boundedBit (zero one blank : Fin nt) (bs : List Bool) (k : ℕ) :
    (bs.map (boundedBit zero one)).getD k blank =
      if hk : k < bs.length then if bs[k] then one else zero else blank := by
  by_cases hk : k < bs.length
  · have hk' : k < (bs.map (boundedBit zero one)).length := by simpa using hk
    rw [dif_pos hk, List.getD_eq_getElem _ _ hk', List.getElem_map,
      boundedBit_spec]
  · rw [dif_neg hk]
    apply List.getD_eq_default
    simpa using Nat.not_lt.mp hk

theorem getElem_cons_pos_bool (b : Bool) (bs : List Bool) (n : ℕ)
    (hpos : 0 < n) (hlen : n < bs.length + 1) :
    (b :: bs)[n] = bs[n - 1]'(by omega) := by
  cases n with
  | zero => omega
  | succ k => simp

theorem halt_iff (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (z : BoundedConfig ns nt) :
    boundedHalted z = true ↔ z.state = M.accept ∨ z.state = M.reject := by
  constructor
  · intro h
    have hlt : z.state.val < 2 := by simpa [boundedHalted] using h
    have : z.state.val = 0 ∨ z.state.val = 1 := by omega
    rcases this with h0 | h1
    · left; apply Fin.ext; exact h0.trans hacc.symm
    · right; apply Fin.ext; exact h1.trans hrej.symm
  · intro h
    rcases h with h | h
    · simp [boundedHalted, h, hacc]
    · simp [boundedHalted, h, hrej]

theorem accept_iff (M : Machine ns nt 2) (hacc : M.accept.val = 0)
    (z : BoundedConfig ns nt) :
    boundedAccepting z = true ↔ z.state = M.accept := by
  constructor
  · intro h
    have hs : z.state.val = ULogSemantics.acceptCode := by
      simpa [boundedAccepting] using h
    apply Fin.ext
    simpa [ULogSemantics.acceptCode, hacc] using hs
  · intro h
    simp [boundedAccepting, ULogSemantics.acceptCode, h, hacc]

theorem written_at_head (c : Configuration ns nt) (w : Fin nt) :
    writtenTape c w c.head = w := by
  unfold writtenTape
  exact Function.update_self c.head w c.tape

theorem written_off_head (c : Configuration ns nt) (w : Fin nt) (p : Int)
    (hp : p ≠ c.head) : writtenTape c w p = c.tape p := by
  unfold writtenTape
  exact Function.update_of_ne hp w c.tape

theorem applyBounded_physical (blank : Fin nt) (head : Int)
    (z : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    physical blank (moveHead a.move head) (applyBounded blank z a) =
      { state := a.target
        head := moveHead a.move head
        tape := writtenTape (physical blank head z) a.write } := by
  apply config_ext
  · cases hm : a.move with
    | stay => simp [applyBounded, hm, physical]
    | right => cases hr : z.right <;> simp [applyBounded, hm, hr, physical]
    | left => cases hl : z.leftRev <;> simp [applyBounded, hm, hl, physical]
  · simp [physical]
  · funext p
    change
      (physical blank (moveHead a.move head) (applyBounded blank z a)).tape p =
        writtenTape (physical blank head z) a.write p
    by_cases hp : p = head
    · subst p
      have hwrite :
          writtenTape (physical blank head z) a.write head = a.write := by
        simpa [physical_head] using
          written_at_head (physical blank head z) a.write
      rw [hwrite]
      cases hm : a.move with
      | stay =>
          simp only [applyBounded, hm, moveHead, physical, ↓reduceIte]
      | right =>
          have hne : head ≠ head + 1 := by omega
          have hlt : head < head + 1 := by omega
          have hidx0 : (head + 1 - head - 1).toNat = 0 := by
            have : head + 1 - head - 1 = (0 : ℤ) := by omega
            simp [this]
          cases hr : z.right <;>
            simp only [applyBounded, hm, hr, moveHead, physical, hne, hlt,
              ↓reduceIte, hidx0, getD_cons_zero]
      | left =>
          have hne : head ≠ head - 1 := by omega
          have hnlt : ¬ head < head - 1 := by omega
          have hidx0 : (head - (head - 1) - 1).toNat = 0 := by
            have : head - (head - 1) - 1 = (0 : ℤ) := by omega
            simp [this]
          cases hl : z.leftRev <;>
            simp only [applyBounded, hm, hl, moveHead, physical, hne, hnlt,
              ↓reduceIte, hidx0, getD_cons_zero]
    · have hwrite :
          writtenTape (physical blank head z) a.write p =
            (physical blank head z).tape p := by
        simpa [physical_head] using
          written_off_head (physical blank head z) a.write p hp
      rw [hwrite]
      cases hm : a.move with
      | stay =>
          simp only [applyBounded, hm, moveHead, physical, hp, ↓reduceIte]
      | right =>
          cases hr : z.right with
          | nil =>
              simp only [applyBounded, hm, hr, moveHead, physical]
              by_cases hnew : p = head + 1
              · subst p
                have hnlt : ¬ head + 1 < head := by omega
                have hne : head + 1 ≠ head := by omega
                simp [physical, hne, hnlt]
              · by_cases hlt : p < head
                · have hnewlt : p < head + 1 := by omega
                  have hidx : (head + 1 - p - 1).toNat =
                      (head - p - 1).toNat + 1 := by
                    have : head + 1 - p - 1 = (head - p - 1) + 1 := by omega
                    have hnn : 0 ≤ head - p - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hnew, hnewlt, hidx, getD_cons_succ]
                · have hnnew : ¬ p < head + 1 := by omega
                  simp [physical, hp, hlt, hnew, hnnew]
          | cons y ys =>
              simp only [applyBounded, hm, hr, moveHead, physical]
              by_cases hnew : p = head + 1
              · subst p
                have hnlt : ¬ head + 1 < head := by omega
                have hne : head + 1 ≠ head := by omega
                simp [physical, hne, hnlt]
              · by_cases hlt : p < head
                · have hnewlt : p < head + 1 := by omega
                  have hidx : (head + 1 - p - 1).toNat =
                      (head - p - 1).toNat + 1 := by
                    have : head + 1 - p - 1 = (head - p - 1) + 1 := by omega
                    have hnn : 0 ≤ head - p - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hnew, hnewlt, hidx, getD_cons_succ]
                · have hnnew : ¬ p < head + 1 := by omega
                  have hidx : (p - head - 1).toNat =
                      (p - (head + 1) - 1).toNat + 1 := by
                    have : p - head - 1 = (p - (head + 1) - 1) + 1 := by omega
                    have hnn : 0 ≤ p - (head + 1) - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hnew, hnnew, hidx, getD_cons_succ]
      | left =>
          cases hl : z.leftRev with
          | nil =>
              simp only [applyBounded, hm, hl, moveHead, physical]
              by_cases hnew : p = head - 1
              · subst p
                have hlt : head - 1 < head := by omega
                have hne : head - 1 ≠ head := by omega
                simp [physical, hne, hlt]
              · by_cases hlt : p < head - 1
                · have hold : p < head := by omega
                  simp [physical, hp, hlt, hold, hnew]
                · have hold : ¬ p < head := by omega
                  have hidx : (p - (head - 1) - 1).toNat =
                      (p - head - 1).toNat + 1 := by
                    have : p - (head - 1) - 1 = (p - head - 1) + 1 := by omega
                    have hnn : 0 ≤ p - head - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hold, hnew, hidx, getD_cons_succ]
          | cons y ys =>
              simp only [applyBounded, hm, hl, moveHead, physical]
              by_cases hnew : p = head - 1
              · subst p
                have hlt : head - 1 < head := by omega
                have hne : head - 1 ≠ head := by omega
                simp [physical, hne, hlt]
              · by_cases hlt : p < head - 1
                · have hold : p < head := by omega
                  have hidx : (head - p - 1).toNat =
                      (head - 1 - p - 1).toNat + 1 := by
                    have : head - p - 1 = (head - 1 - p - 1) + 1 := by omega
                    have hnn : 0 ≤ head - 1 - p - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hold, hnew, hidx, getD_cons_succ]
                · have hold : ¬ p < head := by omega
                  have hidx : (p - (head - 1) - 1).toNat =
                      (p - head - 1).toNat + 1 := by
                    have : p - (head - 1) - 1 = (p - head - 1) + 1 := by omega
                    have hnn : 0 ≤ p - head - 1 := by omega
                    rw [this, toNat_add_one hnn]
                  simp [physical, hp, hlt, hold, hnew, hidx, getD_cons_succ]

theorem step_none_of_halt (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (slot : Bool) (head : Int) (z : BoundedConfig ns nt)
    (hh : boundedHalted z = true) :
    boundedStepSlot (toBounded M) M.blank slot z = none ∧
      step M (slotIndex slot) (physical M.blank head z) = none := by
  have hterm := (halt_iff M hacc hrej z).mp hh
  constructor
  · simp [boundedStepSlot, hh]
  · rcases hterm with hs | hs
    · exact step_accept_none M _ _ (physical_state _ _ _ ▸ hs)
    · exact step_reject_none M _ _ (physical_state _ _ _ ▸ hs)

theorem step_physical (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (slot : Bool) (head : Int) (z : BoundedConfig ns nt) :
    step M (slotIndex slot) (physical M.blank head z) =
      if boundedHalted z then none
      else
        match M.rule z.state z.focus (slotIndex slot) with
        | none => none
        | some a =>
            some (physical M.blank (moveHead a.move head)
              (applyBounded M.blank z (toBoundedAction a))) := by
  by_cases hh : boundedHalted z = true
  · simp [hh]
    exact (step_none_of_halt M hacc hrej slot head z hh).2
  · have hhf : boundedHalted z = false := eq_false_of_ne_true hh
    rw [if_neg (show boundedHalted z ≠ true by simp [hhf])]
    simp [step, physical_state, physical_tape_head, physical_head]
    cases hr : M.rule z.state z.focus (slotIndex slot) with
    | none => rfl
    | some a =>
        refine congrArg some ?_
        simpa using
          (applyBounded_physical M.blank head z (toBoundedAction a)).symm

/-- Literal Bool-labelled zipper run, carrying the actual physical head. -/
def zipperRun (M : Machine ns nt 2) :
    List Bool → Int → BoundedConfig ns nt →
      Option (Int × BoundedConfig ns nt)
  | [], head, z => some (head, z)
  | slot :: rest, head, z =>
      if boundedHalted z then none
      else
        match M.rule z.state z.focus (slotIndex slot) with
        | none => none
        | some a =>
            zipperRun M rest (moveHead a.move head)
              (applyBounded M.blank z (toBoundedAction a))

theorem zipperRun_physical (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (slots : List Bool) (head : Int) (z : BoundedConfig ns nt) :
    (zipperRun M slots head z).map
        (fun p => physical M.blank p.1 p.2) =
      run M (slots.map slotIndex) (physical M.blank head z) := by
  induction slots generalizing head z with
  | nil => simp [zipperRun]
  | cons slot rest ih =>
      by_cases hh : boundedHalted z = true
      · simp [zipperRun, hh, run_cons,
          (step_none_of_halt M hacc hrej slot head z hh).2]
      · have hhf : boundedHalted z = false := eq_false_of_ne_true hh
        simp [zipperRun, hhf, run_cons, step_physical M hacc hrej slot head z]
        cases hr : M.rule z.state z.focus (slotIndex slot) with
        | none => simp [hr]
        | some a =>
            simp [hr]
            exact ih (moveHead a.move head)
              (applyBounded M.blank z (toBoundedAction a))

def zipperMachine (M : Machine ns nt 2) : BinaryNondeterministicMachine :=
  boundedMachine (toBounded M) M.blank
    (boundedInitial M.start M.zero M.one M.blank)

@[simp] theorem zipperMachine_halt (M : Machine ns nt 2)
    (z : BoundedConfig ns nt) :
    (zipperMachine M).halt z = boundedHalted z := rfl

@[simp] theorem zipperMachine_accept (M : Machine ns nt 2)
    (z : BoundedConfig ns nt) :
    (zipperMachine M).accept z = boundedAccepting z := rfl

@[simp] theorem zipperMachine_next (M : Machine ns nt 2)
    (z : BoundedConfig ns nt) :
    (zipperMachine M).next z =
      boundedNext (toBounded M) M.blank z := rfl

theorem physical_initial (M : Machine ns nt 2) (x : List Bool) :
    physical M.blank 0 (boundedInitial M.start M.zero M.one M.blank x) =
      initial M x := by
  apply config_ext
  · cases x <;> simp [physical, boundedInitial, initial]
  · cases x <;> simp [physical, boundedInitial, initial]
  · funext p
    cases x with
    | nil =>
        have hphys :
            (physical M.blank 0 ⟨M.start, [], M.blank, []⟩).tape p =
              M.blank := by
          simp only [physical]
          by_cases hp : p = 0
          · simp [hp]
          · by_cases hn : p < 0 <;> simp [hp, hn]
        have hin : inputTape M [] p = M.blank := by
          simp only [inputTape]
          by_cases hnn : 0 ≤ p <;> simp [hnn]
        simpa [physical, boundedInitial, initial] using hphys.trans hin.symm
    | cons b bs =>
        by_cases hp : p = 0
        · subst p
          cases b <;> simp [physical, boundedInitial, initial, inputTape,
            boundedBit_spec]
        · by_cases hneg : p < 0
          · have hnnf : ¬ 0 ≤ p := by omega
            simp [physical, boundedInitial, initial, inputTape, hp, hneg,
              hnnf]
          · have hnn : 0 ≤ p := by omega
            have hppos : 0 < p := by omega
            have hidx : (p - 0 - 1).toNat = p.toNat - 1 := by
              have : p - 0 - 1 = p - 1 := by omega
              rw [this, toNat_sub_one hppos]
            have hpos : 0 < p.toNat := by
              have hpz : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hnn
              omega
            have hphys :
                (physical M.blank 0
                    (boundedInitial M.start M.zero M.one M.blank
                      (b :: bs))).tape p =
                  (bs.map (boundedBit M.zero M.one)).getD (p.toNat - 1)
                    M.blank := by
              simp only [physical, boundedInitial, hp, hneg]
              exact congrArg (fun n =>
                  (bs.map (boundedBit M.zero M.one)).getD n M.blank) hidx
            rw [hphys, getD_map_boundedBit]
            by_cases htl : p.toNat - 1 < bs.length
            · have hlen : p.toNat < (b :: bs).length := by simp; omega
              rw [dif_pos htl]
              simp only [initial]
              unfold inputTape
              rw [dif_pos hnn, dif_pos hlen]
              have hget :=
                getElem_cons_pos_bool b bs p.toNat hpos (by simpa using hlen)
              rw [hget]
            · have hlen : ¬ p.toNat < (b :: bs).length := by simp; omega
              rw [dif_neg htl]
              simp only [initial]
              unfold inputTape
              rw [dif_pos hnn, dif_neg hlen]

theorem zipperRun_initial (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (slots : List Bool) (x : List Bool) :
    (zipperRun M slots 0
        (boundedInitial M.start M.zero M.one M.blank x)).map
        (fun p => physical M.blank p.1 p.2) =
      run M (slots.map slotIndex) (initial M x) := by
  simpa [physical_initial] using
    zipperRun_physical M hacc hrej slots 0
      (boundedInitial M.start M.zero M.one M.blank x)

def zipperPaths (M : Machine ns nt 2) (T : ℕ)
    (z : BoundedConfig ns nt) : ℕ :=
  (zipperMachine M).acceptingPaths T z

theorem boundedNext_sum (p : BoundedProgram ns nt) (blank : Fin nt)
    (z : BoundedConfig ns nt) (AP : BoundedConfig ns nt → ℕ) :
    ((boundedNext p blank z).map AP).sum =
      (match boundedStepSlot p blank false z with
        | none => 0
        | some z0 => AP z0) +
      (match boundedStepSlot p blank true z with
        | none => 0
        | some z1 => AP z1) := by
  cases h0 : boundedStepSlot p blank false z <;>
    cases h1 : boundedStepSlot p blank true z <;>
      simp [boundedNext, h0, h1]

theorem localCount_physical (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (z : BoundedConfig ns nt) (head : Int) (T : ℕ) :
    localCount M (physical M.blank head z) T =
      (zipperMachine M).acceptingPaths T z := by
  induction T generalizing z head with
  | zero =>
      simp only [BinaryNondeterministicMachine.acceptingPaths,
        zipperMachine_halt, zipperMachine_accept, zipperMachine_next]
      by_cases hh : boundedHalted z = true
      · by_cases ha : boundedAccepting z = true
        · have hs : (physical M.blank head z).state = M.accept :=
            (accept_iff M hacc z).mp ha
          simp [hh, ha]
          exact localCount_accept M _ hs 0
        · have haf : boundedAccepting z = false := eq_false_of_ne_true ha
          have hs : (physical M.blank head z).state = M.reject := by
            have hterm := (halt_iff M hacc hrej z).mp hh
            rcases hterm with h | h
            · have : boundedAccepting z = true := (accept_iff M hacc z).mpr h
              simp [this] at ha
            · exact h
          simp [hh, haf]
          exact localCount_reject M _ hs 0
      · have hhf : boundedHalted z = false := eq_false_of_ne_true hh
        have hna : (physical M.blank head z).state ≠ M.accept := by
          intro hs
          have : boundedHalted z = true :=
            (halt_iff M hacc hrej z).mpr (Or.inl hs)
          simp [this] at hhf
        simp [hhf]
        exact localCount_zero_nonaccept M _ hna
  | succ T ih =>
      simp only [BinaryNondeterministicMachine.acceptingPaths,
        zipperMachine_halt, zipperMachine_accept, zipperMachine_next]
      by_cases hh : boundedHalted z = true
      · by_cases ha : boundedAccepting z = true
        · have hs : (physical M.blank head z).state = M.accept :=
            (accept_iff M hacc z).mp ha
          simp [hh, ha]
          exact localCount_accept M _ hs (T + 1)
        · have haf : boundedAccepting z = false := eq_false_of_ne_true ha
          have hs : (physical M.blank head z).state = M.reject := by
            have hterm := (halt_iff M hacc hrej z).mp hh
            rcases hterm with h | h
            · have : boundedAccepting z = true := (accept_iff M hacc z).mpr h
              simp [this] at ha
            · exact h
          simp [hh, haf]
          exact localCount_reject M _ hs (T + 1)
      · have hhf : boundedHalted z = false := eq_false_of_ne_true hh
        have hna : (physical M.blank head z).state ≠ M.accept := by
          intro hs
          have : boundedHalted z = true :=
            (halt_iff M hacc hrej z).mpr (Or.inl hs)
          simp [this] at hhf
        rw [localCount_succ M _ hna]
        simp [hhf]
        change _ =
          ((boundedNext (toBounded M) M.blank z).map (zipperPaths M T)).sum
        rw [boundedNext_sum]
        simp only [boundedStepSlot, hhf, toBounded, Option.map_map]
        have hstep0 := step_physical M hacc hrej false head z
        have hstep1 := step_physical M hacc hrej true head z
        simp [slotIndex] at hstep0 hstep1
        rw [hstep0, hstep1]
        simp [hhf, slotIndex]
        cases h0 : M.rule z.state z.focus 0 with
        | none =>
            cases h1 : M.rule z.state z.focus 1 with
            | none => simp [h0, h1, zipperPaths]
            | some a1 =>
                simp [h0, h1, zipperPaths]
                exact ih (applyBounded M.blank z (toBoundedAction a1))
                  (moveHead a1.move head)
        | some a0 =>
            cases h1 : M.rule z.state z.focus 1 with
            | none =>
                simp [h0, h1, zipperPaths]
                exact ih (applyBounded M.blank z (toBoundedAction a0))
                  (moveHead a0.move head)
            | some a1 =>
                simp [h0, h1, zipperPaths]
                rw [ih (applyBounded M.blank z (toBoundedAction a0))
                      (moveHead a0.move head),
                    ih (applyBounded M.blank z (toBoundedAction a1))
                      (moveHead a1.move head)]

theorem acceptingCount_eq_acceptingPaths (M : Machine ns nt 2)
    (hacc : M.accept.val = 0) (hrej : M.reject.val = 1)
    (x : List Bool) (T : ℕ) :
    acceptingCount M x T =
      (zipperMachine M).acceptingPaths T
        (boundedInitial M.start M.zero M.one M.blank x) := by
  have hcount := localCount_physical M hacc hrej
    (boundedInitial M.start M.zero M.one M.blank x) 0 T
  simpa [localCount_initial, physical_initial] using hcount

theorem sharpEXP_to_class (f : List Bool → ℕ) (hf : SharpEXP f) :
    ULogSource.Class f := by
  obtain ⟨ns, nt, M, exponent, hcodes, hM⟩ :=
    StandardMachineCanonicalCodes.sharpEXP_to_canonical f hf
  rcases hcodes with ⟨hstart, hacc, hrej, hzero, hone, hblank⟩
  refine ⟨{
    ns := ns
    nt := nt
    program := toBounded M
    qStart := M.start
    zero := M.zero
    one := M.one
    blank := M.blank
    qStart_val := by simpa [ULogSemantics.startCode] using hstart
    zero_val := hzero
    one_val := hone
    blank_val := by simpa [ULogSemantics.blankCode] using hblank
    exponent := exponent
    count_correct := by
      intro x
      obtain ⟨_, hcount⟩ := hM x
      exact hcount.trans
        (acceptingCount_eq_acceptingPaths M hacc hrej x
          (2 ^ exponent.eval x.length))
  }⟩

end PakFixedPolyomino.StandardMachineZipperBridge
