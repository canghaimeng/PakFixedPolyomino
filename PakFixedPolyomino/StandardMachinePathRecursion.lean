import PakFixedPolyomino.StandardNondeterministicMachine

/-! # Finite local accepting-code recursion for ordinary two-slot machines

Accepted `WordCode`s at an arbitrary ordinary configuration obey the same
two-slot next-list recursion as zipper `acceptingPaths`. Terminal accept has
only the empty code; terminal reject contributes zero. A non-accepting
configuration at cutoff `T+1` splits every accepted word into its literal
first slot and an accepted tail at cutoff `T`. Duplicate coincident
successors remain two codes. At the ordinary initial configuration the
cardinal is `acceptingCount`.
-/

namespace PakFixedPolyomino.StandardMachinePathRecursion

open StandardNondeterministicMachine
open FiniteOneTapeSemantics (Config)

variable {ns nt : ℕ}

def LocalAccepted (M : Machine ns nt 2) (c : Configuration ns nt)
    (slots : List (Fin 2)) : Prop :=
  (run M slots c).map (fun cfg => cfg.state) = some M.accept

instance (M : Machine ns nt 2) (c : Configuration ns nt)
    (slots : List (Fin 2)) : Decidable (LocalAccepted M c slots) :=
  inferInstanceAs (Decidable (_ = _))

theorem localAccepted_iff (M : Machine ns nt 2) (c : Configuration ns nt)
    (slots : List (Fin 2)) :
    LocalAccepted M c slots ↔
      ∃ out, run M slots c = some out ∧ out.state = M.accept := by
  cases hr : run M slots c with
  | none => simp [LocalAccepted, hr]
  | some out => simp [LocalAccepted, hr]

theorem localAccepted_nil (M : Machine ns nt 2) (c : Configuration ns nt) :
    LocalAccepted M c [] ↔ c.state = M.accept := by
  simp [LocalAccepted]

theorem localAccepted_cons (M : Machine ns nt 2) (c : Configuration ns nt)
    (slot : Fin 2) (rest : List (Fin 2)) :
    LocalAccepted M c (slot :: rest) ↔
      ((step M slot c).isSome = true) ∧
        LocalAccepted M ((step M slot c).getD c) rest := by
  cases hs : step M slot c with
  | none => simp [LocalAccepted, hs]
  | some c' => simp [LocalAccepted, hs, run_cons]

abbrev LocalCode (M : Machine ns nt 2) (c : Configuration ns nt) (T : ℕ) :=
  {code : WordCode 2 T // LocalAccepted M c code.toList}

def localCount (M : Machine ns nt 2) (c : Configuration ns nt) (T : ℕ) : ℕ :=
  Fintype.card (LocalCode M c T)

def emptyWord (T : ℕ) : WordCode 2 T :=
  ⟨⟨0, Nat.succ_pos _⟩, fun i => nomatch i⟩

theorem emptyWord_toList (T : ℕ) : (emptyWord T).toList = [] := by
  simp [emptyWord, WordCode.toList]

theorem word_eq_empty {T : ℕ} (code : WordCode 2 T)
    (h : code.toList = []) : code = emptyWord T := by
  apply WordCode.toList_injective
  simp [emptyWord_toList, h]

theorem wordCode_zero (code : WordCode 2 0) : code = emptyWord 0 := by
  have hlen : code.toList.length = 0 := by
    have : code.1.val = 0 := Nat.lt_one_iff.mp code.1.isLt
    simpa [WordCode.toList_length]
  exact word_eq_empty code (List.eq_nil_of_length_eq_zero hlen)

def consWord {T : ℕ} (slot : Fin 2) (tail : WordCode 2 T) : WordCode 2 (T + 1) :=
  ⟨⟨tail.1.val + 1, Nat.add_lt_add_right tail.1.isLt 1⟩,
    fun i : Fin (tail.1.val + 1) =>
      if hi : i.val = 0 then slot
      else tail.2 ⟨i.val - 1, Nat.lt_of_succ_lt_succ (by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)]
        exact i.isLt)⟩⟩

theorem consWord_toList {T : ℕ} (slot : Fin 2) (tail : WordCode 2 T) :
    (consWord slot tail).toList = slot :: tail.toList := by
  apply List.ext_getElem
  · simp [consWord, WordCode.toList]
  · intro i hi hi2
    have hi' : i < tail.1.val + 1 := by
      simpa [consWord, WordCode.toList] using hi
    by_cases hz : i = 0
    · subst i
      simp [consWord, WordCode.toList, List.getElem_ofFn]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hz
      have htail : i - 1 < tail.1.val := Nat.lt_of_succ_lt_succ (by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
        exact hi')
      simp [consWord, WordCode.toList, List.getElem_ofFn, hz, htail]

theorem consWord_injective {T : ℕ} (slot : Fin 2) :
    Function.Injective (consWord (T := T) slot) := by
  intro a b h
  apply WordCode.toList_injective
  have := congrArg WordCode.toList h
  simp [consWord_toList] at this
  exact this

def consEmb {T : ℕ} (slot : Fin 2) : WordCode 2 T ↪ WordCode 2 (T + 1) :=
  ⟨consWord slot, consWord_injective slot⟩

def firstBit? {T : ℕ} (code : WordCode 2 (T + 1)) : Option (Fin 2) :=
  if h : 0 < code.1.val then some (code.2 ⟨0, h⟩) else none

theorem firstBit_cons {T : ℕ} (slot : Fin 2) (tail : WordCode 2 T) :
    firstBit? (consWord slot tail) = some slot := by
  simp [firstBit?, consWord]

theorem firstBit_empty {T : ℕ} {code : WordCode 2 (T + 1)}
    (h : code.toList = []) : firstBit? code = none := by
  have hlen : code.toList.length = 0 := by simp [h]
  have : code.1.val = 0 := by simpa [WordCode.toList_length] using hlen
  simp [firstBit?, this]

def headSlot {T : ℕ} (code : WordCode 2 (T + 1)) (h : 0 < code.1.val) : Fin 2 :=
  code.2 ⟨0, h⟩

def tailWord {T : ℕ} (code : WordCode 2 (T + 1)) (h : 0 < code.1.val) :
    WordCode 2 T :=
  ⟨⟨code.1.val - 1, by have := code.1.isLt; omega⟩,
    fun i : Fin (code.1.val - 1) =>
      code.2 ⟨i.val + 1, by
        have := i.isLt
        omega⟩⟩

theorem getElem_cons_pos {α : Type*} (a : α) (l : List α) (i : ℕ)
    (hpos : 0 < i) (hi : i < (a :: l).length) :
    (a :: l)[i] = l[i - 1]'(by simp at hi; omega) := by
  cases i with
  | zero => cases hpos
  | succ k => simp [List.getElem_cons_succ]

theorem toList_uncons {T : ℕ} (code : WordCode 2 (T + 1))
    (h : 0 < code.1.val) :
    code.toList = headSlot code h :: (tailWord code h).toList := by
  apply List.ext_getElem
  · simp [headSlot, tailWord, WordCode.toList]
    omega
  · intro i hi hi2
    have hlen : i < code.1.val := by simpa [WordCode.toList] using hi
    have hL : code.toList[i] = code.2 ⟨i, hlen⟩ := by
      simp [WordCode.toList, List.getElem_ofFn]
    rw [hL]
    by_cases hz : i = 0
    · subst i
      rw [List.getElem_cons_zero]
      simp [headSlot]
    · have hpos : 0 < i := Nat.pos_of_ne_zero hz
      rw [getElem_cons_pos (headSlot code h) (tailWord code h).toList i hpos hi2]
      simp [WordCode.toList, tailWord, List.getElem_ofFn]
      apply congrArg code.2
      apply Fin.ext
      exact (Nat.sub_add_cancel hpos).symm

theorem cons_uncons {T : ℕ} (code : WordCode 2 (T + 1)) (h : 0 < code.1.val) :
    consWord (headSlot code h) (tailWord code h) = code := by
  apply WordCode.toList_injective
  rw [consWord_toList, toList_uncons]

theorem firstBit_some {T : ℕ} {code : WordCode 2 (T + 1)} {slot : Fin 2}
    (h : firstBit? code = some slot) :
    ∃ hp : 0 < code.1.val, headSlot code hp = slot ∧
      consWord slot (tailWord code hp) = code := by
  have hp : 0 < code.1.val := by
    by_contra hnp
    simp [firstBit?, hnp] at h
  have hhead : headSlot code hp = slot := by
    simp [firstBit?, hp, headSlot] at h
    exact h
  refine ⟨hp, hhead, ?_⟩
  simpa [hhead] using cons_uncons code hp

theorem localAccepted_empty_of_accept (M : Machine ns nt 2)
    (c : Configuration ns nt) (h : c.state = M.accept) (T : ℕ) :
    LocalAccepted M c (emptyWord T).toList := by
  simp [emptyWord_toList, localAccepted_nil, h]

theorem localAccepted_nonempty_of_accept (M : Machine ns nt 2)
    (c : Configuration ns nt) (h : c.state = M.accept)
    (slots : List (Fin 2)) (hne : slots ≠ []) :
    ¬ LocalAccepted M c slots := by
  intro ha
  have := run_accept_nonempty_none M c h slots hne
  simp [LocalAccepted, this] at ha

def acceptUnitEquiv (M : Machine ns nt 2) (c : Configuration ns nt)
    (h : c.state = M.accept) (T : ℕ) : LocalCode M c T ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => ⟨emptyWord T, localAccepted_empty_of_accept M c h T⟩
  left_inv := by
    intro w
    apply Subtype.ext
    have hnil : w.val.toList = [] := by
      by_contra hne
      exact localAccepted_nonempty_of_accept M c h w.val.toList hne w.property
    exact (word_eq_empty w.val hnil).symm
  right_inv := fun _ => rfl

theorem localCount_accept (M : Machine ns nt 2) (c : Configuration ns nt)
    (h : c.state = M.accept) (T : ℕ) : localCount M c T = 1 := by
  simpa [localCount] using Fintype.card_congr (acceptUnitEquiv M c h T)

theorem localAccepted_reject (M : Machine ns nt 2) (c : Configuration ns nt)
    (h : c.state = M.reject) (slots : List (Fin 2)) :
    ¬ LocalAccepted M c slots := by
  intro ha
  obtain ⟨out, hrun, hst⟩ := (localAccepted_iff M c slots).mp ha
  cases slots with
  | nil =>
      simp at hrun
      subst out
      exact M.accept_ne_reject (hst.symm.trans h)
  | cons slot rest =>
      simp [run_cons, step_reject_none M slot c h] at hrun

theorem localCount_reject (M : Machine ns nt 2) (c : Configuration ns nt)
    (h : c.state = M.reject) (T : ℕ) : localCount M c T = 0 := by
  have : IsEmpty (LocalCode M c T) :=
    ⟨fun w => localAccepted_reject M c h w.val.toList w.property⟩
  exact Fintype.card_eq_zero

theorem localCount_zero_nonaccept (M : Machine ns nt 2)
    (c : Configuration ns nt) (h : c.state ≠ M.accept) :
    localCount M c 0 = 0 := by
  have : IsEmpty (LocalCode M c 0) :=
    ⟨fun w => by
      have hw := wordCode_zero w.val
      have : LocalAccepted M c [] := by
        simpa [hw, emptyWord_toList] using w.property
      exact h ((localAccepted_nil M c).mp this)⟩
  exact Fintype.card_eq_zero

theorem localCount_eq_filter (M : Machine ns nt 2) (c : Configuration ns nt)
    (T : ℕ) :
    localCount M c T =
      (Finset.univ.filter fun code : WordCode 2 T =>
        LocalAccepted M c code.toList).card :=
  Fintype.card_subtype _

def acceptedFilter (M : Machine ns nt 2) (c : Configuration ns nt) (T : ℕ) :
    Finset (WordCode 2 T) :=
  Finset.univ.filter fun code => LocalAccepted M c code.toList

def acceptedSlot (M : Machine ns nt 2) (c : Configuration ns nt) (T : ℕ)
    (slot : Fin 2) : Finset (WordCode 2 (T + 1)) :=
  Finset.univ.filter fun code =>
    LocalAccepted M c code.toList ∧ firstBit? code = some slot

theorem acceptedFilter_nonaccept_eq_union (M : Machine ns nt 2)
    (c : Configuration ns nt) (hna : c.state ≠ M.accept) (T : ℕ) :
    acceptedFilter M c (T + 1) =
      acceptedSlot M c T ⟨0, by omega⟩ ∪ acceptedSlot M c T ⟨1, by omega⟩ := by
  ext code
  simp [acceptedFilter, acceptedSlot]
  constructor
  · intro ha
    have hne : code.toList ≠ [] := by
      intro he
      have : LocalAccepted M c [] := by simpa [he] using ha
      exact hna ((localAccepted_nil M c).mp this)
    have hpos : 0 < code.1.val := by
      have : 0 < code.toList.length := List.length_pos_of_ne_nil hne
      simpa [WordCode.toList_length] using this
    have hbit : firstBit? code = some (headSlot code hpos) := by
      simp [firstBit?, hpos, headSlot]
    have : (headSlot code hpos).val = 0 ∨ (headSlot code hpos).val = 1 := by
      have := (headSlot code hpos).isLt
      omega
    rcases this with hz | hone
    · left
      refine ⟨ha, ?_⟩
      have hslot : headSlot code hpos = ⟨0, by omega⟩ := by
        apply Fin.ext
        exact hz
      simp [hbit, hslot]
    · right
      refine ⟨ha, ?_⟩
      have hslot : headSlot code hpos = ⟨1, by omega⟩ := by
        apply Fin.ext
        exact hone
      simp [hbit, hslot]
  · intro h
    rcases h with ⟨ha, _⟩ | ⟨ha, _⟩ <;> exact ha

theorem acceptedSlot_disjoint (M : Machine ns nt 2) (c : Configuration ns nt)
    (T : ℕ) :
    Disjoint (acceptedSlot M c T ⟨0, by omega⟩)
      (acceptedSlot M c T ⟨1, by omega⟩) := by
  refine Finset.disjoint_left.2 ?_
  intro code h0 h1
  have hb0 : firstBit? code = some ⟨0, by omega⟩ := by
    simp [acceptedSlot] at h0
    exact h0.2
  have hb1 : firstBit? code = some ⟨1, by omega⟩ := by
    simp [acceptedSlot] at h1
    exact h1.2
  have h01 : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
    Option.some.inj (hb0.symm.trans hb1)
  have : (0 : ℕ) = 1 := congrArg Fin.val h01
  omega

theorem acceptedSlot_eq_map (M : Machine ns nt 2) (c : Configuration ns nt)
    (T : ℕ) (slot : Fin 2) :
    acceptedSlot M c T slot =
      match step M slot c with
      | none => ∅
      | some c' => (acceptedFilter M c' T).map (consEmb slot) := by
  cases hs : step M slot c with
  | none =>
      ext code
      constructor
      · intro hmem
        simp [acceptedSlot, hs] at hmem
        obtain ⟨ha, hbit⟩ := hmem
        obtain ⟨hp, _, hcons⟩ := firstBit_some hbit
        have hlist : code.toList = slot :: (tailWord code hp).toList := by
          rw [← congrArg WordCode.toList hcons, consWord_toList]
        have hacc : LocalAccepted M c (slot :: (tailWord code hp).toList) := by
          rwa [← hlist]
        simp [localAccepted_cons, hs] at hacc
      · intro hmem
        simp at hmem
  | some c' =>
      ext code
      constructor
      · intro hmem
        simp [acceptedSlot] at hmem
        obtain ⟨ha, hbit⟩ := hmem
        obtain ⟨hp, _, hcons⟩ := firstBit_some hbit
        refine Finset.mem_map.2 ⟨tailWord code hp, ?_, ?_⟩
        · simp [acceptedFilter]
          have hlist : code.toList = slot :: (tailWord code hp).toList := by
            rw [← congrArg WordCode.toList hcons, consWord_toList]
          have hacc :=
            (localAccepted_cons M c slot (tailWord code hp).toList).mp
              (by simpa [hlist] using ha)
          simpa [hs] using hacc.2
        · simp [consEmb]
          exact hcons
      · intro hmem
        rcases Finset.mem_map.1 hmem with ⟨tail, htail, hcode⟩
        have hcode' : consWord slot tail = code := by
          simpa [consEmb] using hcode
        simp [acceptedSlot]
        constructor
        · have : LocalAccepted M c (slot :: tail.toList) := by
            simp [acceptedFilter] at htail
            simp [localAccepted_cons, hs, htail]
          simpa [← hcode', consWord_toList] using this
        · simpa [← hcode'] using firstBit_cons slot tail

theorem card_acceptedSlot (M : Machine ns nt 2) (c : Configuration ns nt)
    (T : ℕ) (slot : Fin 2) :
    (acceptedSlot M c T slot).card =
      match step M slot c with
      | none => 0
      | some c' => localCount M c' T := by
  cases hstep : step M slot c with
  | none => simp [acceptedSlot_eq_map, hstep]
  | some c' =>
      simp [acceptedSlot_eq_map, hstep, Finset.card_map, localCount_eq_filter,
        acceptedFilter]

theorem localCount_succ (M : Machine ns nt 2) (c : Configuration ns nt)
    (hna : c.state ≠ M.accept) (T : ℕ) :
    localCount M c (T + 1) =
      (match step M ⟨0, by omega⟩ c with
        | none => 0
        | some c0 => localCount M c0 T) +
      (match step M ⟨1, by omega⟩ c with
        | none => 0
        | some c1 => localCount M c1 T) := by
  rw [localCount_eq_filter]
  change (acceptedFilter M c (T + 1)).card = _
  rw [acceptedFilter_nonaccept_eq_union M c hna T,
    Finset.card_union_of_disjoint (acceptedSlot_disjoint M c T),
    card_acceptedSlot, card_acceptedSlot]

theorem localCount_initial (M : Machine ns nt 2) (x : List Bool) (T : ℕ) :
    localCount M (initial M x) T = acceptingCount M x T :=
  rfl

end PakFixedPolyomino.StandardMachinePathRecursion
