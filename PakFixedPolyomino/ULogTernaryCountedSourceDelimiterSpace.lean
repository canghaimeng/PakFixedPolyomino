import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
/-! EVERY successful raw word of the counted-source delimiter. Occupied
cells and GrowthRun 0 0 come from equal initial/final cellCount on the
unique accepting word. Head bounds come from monotonic prefixes of that
word: a completed LEFT (resp. RIGHT) segment of length L ends at head-L
(resp. head+L), so every prefix is exact. Physical loader/headline remain
separate. -/
namespace PakFixedPolyomino.ULogTernaryCountedSourceDelimiterSpace
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter
open ULogTernaryRetainedCounterPump (cell cells)
open FiniteOneTapeSemantics (moveHead)
def occupied (x : List Bool) (under buffer : List (Fin 3)) : Nat :=
  under.length + 2 * x.length + 3 + buffer.length
def leftLen (i : Nat) : Nat := 2 * i + 2
def rightLen (i : Nat) : Nat := 2 * i + 3
theorem leftLen_add (i : Nat) : leftLen i + rightLen i = roundCost i := by
  simp [leftLen, rightLen, roundCost]; omega
theorem program_falseOnly : FalseOnly program :=
  fun q read => rule_true q read
theorem replicate_split (n t : Nat) (ht : t ≤ n) :
    List.replicate n false =
      List.replicate t false ++ List.replicate (n - t) false := by
  conv_lhs => rw [← Nat.add_sub_of_le ht]
  exact List.replicate_add t (n - t) false
theorem replicate_one_false : List.replicate 1 false = [false] := rfl
theorem no_stay {q : Fin 24} {r : Fin 3} {a : BoundedAction 24 3}
    (h : program.rule q r false = some a) : a.move ≠ .stay := by
  have : q.val < 24 := q.isLt
  interval_cases hval : q.val
  all_goals (simp [program, hval] at h; try split_ifs at h)
  all_goals (try cases h)
  all_goals (try simp at *)
  all_goals (try contradiction)
theorem move_pm1 {q : Fin 24} {r : Fin 3} {a : BoundedAction 24 3}
    (h : program.rule q r false = some a) (head : Int) :
    moveHead a.move head = head + 1 ∨ moveHead a.move head = head - 1 := by
  have hns := no_stay h
  cases hm : a.move with
  | stay => exact (hns hm).elim
  | left => simp [moveHead, hm]
  | right => simp [moveHead, hm]
theorem step_head_pm1 {head hf : Int} {z zf : BoundedConfig 24 3}
    (h : run program 2 [false] head z = some (hf, zf)) :
    hf = head + 1 ∨ hf = head - 1 := by
  cases hh : boundedHalted z with
  | true => simp [run, hh] at h
  | false =>
      cases hr : program.rule z.state z.focus false with
      | none => simp [run, hh, hr] at h
      | some a =>
          simp [run, hh, hr] at h
          obtain ⟨rfl, rfl⟩ := h
          exact move_pm1 hr head
theorem run_head_bound {t : Nat} {head hf : Int} {z zf : BoundedConfig 24 3}
    (h : run program 2 (List.replicate t false) head z = some (hf, zf)) :
    head - (t : Int) ≤ hf ∧ hf ≤ head + t := by
  induction t generalizing head z hf zf with
  | zero =>
      simp [run] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
  | succ t ih =>
      have hw : List.replicate (t + 1) false =
          [false] ++ List.replicate t false := by
        simp [List.replicate_succ]
      rw [hw, run_append] at h
      cases h1 : run program 2 [false] head z with
      | none => simp [h1] at h
      | some p =>
          simp [h1, bind_run] at h
          have hpm := step_head_pm1 h1
          have ⟨lo, hi⟩ := ih h
          omega
theorem prefix_of_success {ns nt : Nat} {p : BoundedProgram ns nt}
    {blank : Fin nt} {L t : Nat} {head : Int} {z : BoundedConfig ns nt}
    {hz : Int × BoundedConfig ns nt}
    (ht : t ≤ L)
    (hfull : run p blank (List.replicate L false) head z = some hz) :
    ∃ hf zf, run p blank (List.replicate t false) head z = some (hf, zf) := by
  have hsplit := replicate_split L t ht
  rw [hsplit, run_append] at hfull
  cases hpre : run p blank (List.replicate t false) head z with
  | none => simp [hpre] at hfull
  | some p => exact ⟨p.1, p.2, rfl⟩
theorem prefix_exact_right {L t : Nat} {head : Int} {z zf : BoundedConfig 24 3}
    (hfull : run program 2 (List.replicate L false) head z =
      some (head + L, zf))
    (ht : t ≤ L) :
    ∃ z', run program 2 (List.replicate t false) head z =
      some (head + t, z') := by
  obtain ⟨hf, z', hpre⟩ := prefix_of_success ht hfull
  have ⟨lo, hi⟩ := run_head_bound hpre
  have hsplit := replicate_split L t ht
  have hrest :
      run program 2 (List.replicate (L - t) false) hf z' =
        some (head + L, zf) := by
    rw [hsplit, run_append, hpre, bind_run] at hfull
    exact hfull
  have ⟨lo2, hi2⟩ := run_head_bound hrest
  have : hf = head + t := by omega
  subst this
  exact ⟨z', hpre⟩
theorem prefix_exact_left {L t : Nat} {head : Int} {z zf : BoundedConfig 24 3}
    (hfull : run program 2 (List.replicate L false) head z =
      some (head - L, zf))
    (ht : t ≤ L) :
    ∃ z', run program 2 (List.replicate t false) head z =
      some (head - t, z') := by
  obtain ⟨hf, z', hpre⟩ := prefix_of_success ht hfull
  have ⟨lo, hi⟩ := run_head_bound hpre
  have hsplit := replicate_split L t ht
  have hrest :
      run program 2 (List.replicate (L - t) false) hf z' =
        some (head - L, zf) := by
    rw [hsplit, run_append, hpre, bind_run] at hfull
    exact hfull
  have ⟨lo2, hi2⟩ := run_head_bound hrest
  have : hf = head - t := by omega
  subst this
  exact ⟨z', hpre⟩
theorem cellCount_of_cells {ns : Nat} (q : Fin ns)
    (left tape : List (Fin 3)) (hne : tape ≠ []) :
    cellCount (fromCells q left tape) = left.length + tape.length := by
  cases tape with
  | nil => exact (hne rfl).elim
  | cons _ rest =>
      simp [cellCount, fromCells]
      omega
theorem initial_ne (x : List Bool) (buffer : List (Fin 3)) :
    zeros x.length ++ 1 :: (cells x ++ 0 :: buffer) ≠ [] := by
  intro h
  cases x.length <;> simp [zeros] at h
theorem final_ne (x : List Bool) (buffer : List (Fin 3)) :
    cells x ++ 2 :: buffer ≠ [] := by
  intro h
  simp at h
theorem occupied_initial (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (initial x under buffer) = occupied x under buffer := by
  unfold initial
  have hne : List.replicate x.length (0 : Fin 3) ++
      1 :: (cells x ++ 0 :: buffer) ≠ [] := by
    simpa [zeros] using initial_ne x buffer
  rw [cellCount_of_cells _ _ _ hne]
  simp [occupied, cells]
  omega
theorem occupied_final (x : List Bool) (under buffer : List (Fin 3)) :
    cellCount (finalConfig x under buffer) = occupied x under buffer := by
  unfold finalConfig
  rw [cellCount_of_cells _ _ _ (final_ne x buffer)]
  simp [occupied, ones, cells]
  omega
theorem replicate_add_run {ns nt : Nat} (p : BoundedProgram ns nt)
    (blank : Fin nt) (n m : Nat) (head : Int) (z : BoundedConfig ns nt)
    {hf : Int} {zf : BoundedConfig ns nt} {hf' : Int}
    {zf' : BoundedConfig ns nt}
    (h1 : run p blank (List.replicate n false) head z = some (hf, zf))
    (h2 : run p blank (List.replicate m false) hf zf = some (hf', zf')) :
    run p blank (List.replicate (n + m) false) head z =
      some (hf', zf') := by
  have hw : List.replicate (n + m) false =
      List.replicate n false ++ List.replicate m false :=
    List.replicate_add n m false
  rw [hw, run_append, h1, bind_run, h2]
theorem growth_append_le {ns nt : Nat} {p : BoundedProgram ns nt}
    {blank : Fin nt} {w1 w2 : List Bool} {h0 hf hm : Int}
    {z0 zf zm : BoundedConfig ns nt} {lg rg lg1 rg1 : Nat}
    (hfull : GrowthRun p blank (w1 ++ w2) h0 z0 hf zf lg rg)
    (hpre : GrowthRun p blank w1 h0 z0 hm zm lg1 rg1) :
    lg1 ≤ lg ∧ rg1 ≤ rg := by
  induction w1 generalizing h0 z0 hm zm lg rg lg1 rg1 hf zf with
  | nil =>
      cases hpre
      omega
  | cons slot rest ih =>
      cases hpre with
      | cons halt rule tail =>
          have hcons :
              GrowthRun p blank (slot :: (rest ++ w2)) h0 z0 hf zf lg rg := by
            simpa [List.cons_append] using hfull
          cases hcons with
          | cons halt' rule' tail' =>
              have ha := Option.some.inj (rule.symm.trans rule')
              subst ha
              have ⟨hL, hR⟩ := ih tail' tail
              constructor <;> omega
theorem final_state (x : List Bool) (under buffer : List (Fin 3)) :
    (finalConfig x under buffer).state.val = 0 := by
  simp [finalConfig, fromCells_state]
theorem word4 (n : Nat) :
    List.replicate (2 * n + 2) false =
      [false] ++ (List.replicate n false ++
        ([false] ++ List.replicate n false)) := by
  have h : 2 * n + 2 = 1 + (n + (1 + n)) := by omega
  rw [h, List.replicate_add, List.replicate_add, List.replicate_add]
  simp [List.replicate_succ]
theorem init_head (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) (t : Nat) (ht : t ≤ x.length + 1) :
    ∃ zf, run program 2 (List.replicate t false) H (initial x under buffer) =
      some (H + t, zf) := by
  have hfull := init_run x under buffer H
  have hfull' :
      run program 2 (List.replicate (x.length + 1) false) H
        (initial x under buffer) =
        some (H + (x.length + 1 : Nat), atCursor x under buffer 0) := by
    have hend : H + (x.length + 1 : Nat) = H + x.length + 1 := by
      rw [natCast_succ]; omega
    rw [hend]
    exact hfull
  exact prefix_exact_right hfull' ht
theorem round_left_zero (b : Bool) (xs : List Bool)
    (under buffer : List (Fin 3)) (h : Int) :
    ∃ zL, run program 2 (List.replicate (leftLen 0) false) h
      (atCursor (b :: xs) under buffer 0) = some (h - 2, zL) := by
  have hcfg :
      atCursor (b :: xs) under buffer 0 =
        fromCells 3 (2 :: (zeros (xs.length + 1) ++ 2 :: under))
          (cell b :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ ?_
    · rw [cursorLeft_zero, List.length_cons, List.cons_append]
    · simp [cursorTape, cells_cons]
  have h1 :=
    step3 b h 2 (zeros (xs.length + 1) ++ 2 :: under)
      (cells xs ++ 0 :: buffer)
  have hz :
      fromCells (mem4 b) (zeros (xs.length + 1) ++ 2 :: under)
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) =
        fromCells (mem4 b) (0 :: (zeros xs.length ++ 2 :: under))
          (2 :: 2 :: (cells xs ++ 0 :: buffer)) := by
    refine fromCells_eq rfl ?_ rfl
    rw [zeros_succ, List.cons_append]
  have h2 :=
    step45_sep b (h - 1) 0 (zeros xs.length ++ 2 :: under)
      (2 :: (cells xs ++ 0 :: buffer))
  have h1' :
      run program 2 (List.replicate 1 false) h
        (fromCells 3 (2 :: (zeros (xs.length + 1) ++ 2 :: under))
          (cell b :: (cells xs ++ 0 :: buffer))) =
        some (h - 1,
          fromCells (mem4 b) (zeros (xs.length + 1) ++ 2 :: under)
            (2 :: 2 :: (cells xs ++ 0 :: buffer))) := by
    simpa [replicate_one_false] using h1
  have h2' :
      run program 2 (List.replicate 1 false) (h - 1)
        (fromCells (mem4 b) (zeros (xs.length + 1) ++ 2 :: under)
          (2 :: 2 :: (cells xs ++ 0 :: buffer))) =
        some (h - 2,
          fromCells (mem6 b) (zeros xs.length ++ 2 :: under)
            (0 :: 2 :: 2 :: (cells xs ++ 0 :: buffer))) := by
    have hend : h - 1 - 1 = h - 2 := by omega
    simpa [replicate_one_false, hz, hend] using h2
  have hrun :=
    replicate_add_run program (2 : Fin 3) 1 1 h
      (fromCells 3 (2 :: (zeros (xs.length + 1) ++ 2 :: under))
        (cell b :: (cells xs ++ 0 :: buffer))) h1' h2'
  exact ⟨_, by simpa [hcfg, leftLen] using hrun⟩
theorem round_left_succ (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (j : Nat) (hj : j + 1 < x.length) :
    ∃ zL, run program 2 (List.replicate (leftLen (j + 1)) false) h
      (atCursor x under buffer (j + 1)) =
        some (h - (leftLen (j + 1) : Int), zL) := by
  have hi : j < x.length := by omega
  rw [atCursor_succ_eq x under buffer j hj, reverse_take_succ x j hi]
  refine ⟨fromCells (mem6 (x[j + 1]))
      (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      (0 :: ones (j + 1) ++
        2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))), ?_⟩
  have hw : List.replicate (leftLen (j + 1)) false =
      [false] ++ (List.replicate (j + 1) false ++
        ([false] ++ List.replicate (j + 1) false)) := by
    simpa [leftLen] using word4 (j + 1)
  rw [hw]
  have hmark :=
    step3 (x[j + 1]) h (cell x[j])
      ((cells (x.take j)).reverse ++ 2 :: headerL x.length (j + 1) ++ 2 :: under)
      (cells (x.drop (j + 2)) ++ 0 :: buffer)
  have hL :
      cell x[j] :: (cells (x.take j)).reverse ++
          2 :: headerL x.length (j + 1) ++ 2 :: under =
        cell x[j] ::
          ((cells (x.take j)).reverse ++
            2 :: headerL x.length (j + 1) ++ 2 :: under) := by
    simp [List.cons_append, List.append_assoc]
  rw [hL, run_append, hmark, bind_run]
  have has : ∀ a ∈ (cells (x.take j)).reverse, a.val < 2 := by
    intro a ha
    exact cells_val_lt (x.take j) a (List.mem_reverse.mp ha)
  have hsrc :=
    scan45_cells (x[j + 1]) (cell x[j]) (cells (x.take j)).reverse
      (cell_val_lt _) has (h - 1) 2
      (headerL x.length (j + 1) ++ 2 :: under)
      (2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  have hlenas : (cells (x.take j)).reverse.length = j := by
    simp [cells_length, take_len x j (Nat.le_of_lt hi)]
  simp [hlenas, natCast_succ] at hsrc
  rw [show
      (cells (x.take j)).reverse ++ 2 :: headerL x.length (j + 1) ++ 2 :: under =
        (cells (x.take j)).reverse ++ 2 ::
          (headerL x.length (j + 1) ++ 2 :: under)
      from List.append_assoc _ _ _,
    run_append, hsrc, bind_run]
  have hleft :
      headerL x.length (j + 1) ++ 2 :: under =
        1 :: (ones j ++ zeros (x.length - (j + 1)) ++ 2 :: under) := by
    simp [headerL, ones_succ, List.cons_append]
  have hright :
      cells (x.take j) ++ cell x[j] ::
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer) =
        cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer) := by
    rw [← List.singleton_append, ← List.append_assoc, cells_take_concat x j hi]
  have hsepl :=
    step45_sep (x[j + 1]) (h - 1 - ((j : Int) + 1)) 1
      (ones j ++ zeros (x.length - (j + 1)) ++ 2 :: under)
      (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
  rw [hleft]
  rw [show
      2 :: (cells (x.take j) ++ cell x[j] ::
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)) =
        2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))
      from congrArg (List.cons 2) hright]
  rw [run_append, hsepl, bind_run]
  have hz : zeros (x.length - (j + 1)) =
      0 :: zeros (x.length - (j + 1) - 1) := by
    have : x.length - (j + 1) = Nat.succ (x.length - (j + 1) - 1) := by omega
    rw [this, zeros_succ, Nat.succ_sub_one]
  have hctr :=
    scan67_ones (x[j + 1]) j (h - 1 - ((j : Int) + 1) - 1) 0
      (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      (2 :: (cells (x.take (j + 1)) ++
        2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)))
  have hrest1 :
      1 :: 2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer)) =
        1 :: (2 :: (cells (x.take (j + 1)) ++
          2 :: (cells (x.drop (j + 2)) ++ 0 :: buffer))) := rfl
  rw [hz, show
      ones j ++ 0 :: zeros (x.length - (j + 1) - 1) ++ 2 :: under =
        ones j ++ 0 :: (zeros (x.length - (j + 1) - 1) ++ 2 :: under)
      from List.append_assoc _ _ _,
    ← hrest1, hctr]
  apply congrArg some
  apply Prod.ext
  · simp [leftLen]; omega
  · rfl
theorem round_left (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (i : Nat) (hi : i < x.length) :
    ∃ zL, run program 2 (List.replicate (leftLen i) false) h
      (atCursor x under buffer i) =
        some (h - (leftLen i : Int), zL) := by
  cases i with
  | zero =>
      cases x with
      | nil => simp at hi
      | cons b xs => simpa [leftLen] using round_left_zero b xs under buffer h
  | succ j => exact round_left_succ x under buffer h j hi
theorem round_head (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (i s : Nat) (hi : i < x.length) (hs : s ≤ roundCost i) :
    ∃ hf zf,
      run program 2 (List.replicate s false) h
        (atCursor x under buffer i) = some (hf, zf) ∧
        h - (leftLen i : Int) ≤ hf ∧ hf ≤ h + 1 := by
  have ⟨zL, hL⟩ := round_left x under buffer h i hi
  have hC := copy_round x under buffer h i hi
  have hsplit :
      List.replicate (roundCost i) false =
        List.replicate (leftLen i) false ++
          List.replicate (rightLen i) false := by
    rw [← leftLen_add i]
    exact List.replicate_add (leftLen i) (rightLen i) false
  have hR :
      run program 2 (List.replicate (rightLen i) false)
        (h - (leftLen i : Int)) zL =
        some (h + 1, atCursor x under buffer (i + 1)) := by
    rw [hsplit, run_append, hL, bind_run] at hC
    exact hC
  have hend :
      (h - (leftLen i : Int)) + (rightLen i : Int) = h + 1 := by
    simp [leftLen, rightLen]; omega
  have hR' :
      run program 2 (List.replicate (rightLen i) false)
        (h - (leftLen i : Int)) zL =
        some ((h - (leftLen i : Int)) + (rightLen i : Int),
          atCursor x under buffer (i + 1)) := by
    simpa [hend] using hR
  by_cases hle : s ≤ leftLen i
  · obtain ⟨zf, hz⟩ := prefix_exact_left hL hle
    exact ⟨h - s, zf, hz, by omega, by omega⟩
  · have hsR : s - leftLen i ≤ rightLen i := by
      have := leftLen_add i
      omega
    obtain ⟨zf, hz⟩ := prefix_exact_right hR' hsR
    refine ⟨(h - (leftLen i : Int)) + (s - leftLen i : Nat), zf, ?_, by omega,
      by omega⟩
    have hrun := replicate_add_run program (2 : Fin 3)
      (leftLen i) (s - leftLen i) h (atCursor x under buffer i) hL hz
    have hlen : leftLen i + (s - leftLen i) = s := by omega
    simpa [hlen] using hrun
theorem copies_head_aux (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (k : Nat) (hk : k ≤ x.length) (t : Nat)
    (ht : t ≤ copiesCost k) :
    ∃ hf zf,
      run program 2 (List.replicate t false) h
        (atCursor x under buffer 0) = some (hf, zf) ∧
        h - (k + 2 : Int) ≤ hf ∧ hf ≤ h + k := by
  induction k generalizing t with
  | zero =>
      have : t = 0 := by simp [copiesCost] at ht; omega
      subst this
      exact ⟨h, atCursor x under buffer 0, by simp [run], by omega, by omega⟩
  | succ k ih =>
      have hk0 : k ≤ x.length := by omega
      have hlt : k < x.length := by omega
      by_cases hle : t ≤ copiesCost k
      · obtain ⟨hf, zf, hr, hlo, hhi⟩ := ih hk0 t hle
        exact ⟨hf, zf, hr, by omega, by omega⟩
      · have hs : t - copiesCost k ≤ roundCost k := by
          have hcs := copiesCost_succ k
          omega
        have hpre := copies_prefix x under buffer h k hk0
        obtain ⟨hf, zf, hr, hlo, hhi⟩ :=
          round_head x under buffer (h + k) k (t - copiesCost k) hlt hs
        refine ⟨hf, zf, ?_, by simp [leftLen] at hlo ⊢; omega, by omega⟩
        have hrun := replicate_add_run program (2 : Fin 3)
          (copiesCost k) (t - copiesCost k) h
          (atCursor x under buffer 0) hpre hr
        have hlen : copiesCost k + (t - copiesCost k) = t := by omega
        simpa [hlen] using hrun
theorem copies_head (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (t : Nat) (ht : t ≤ copiesCost x.length) :
    ∃ hf zf,
      run program 2 (List.replicate t false) h
        (atCursor x under buffer 0) = some (hf, zf) ∧
        h - (x.length + 2 : Int) ≤ hf ∧ hf ≤ h + x.length :=
  copies_head_aux x under buffer h x.length le_rfl t ht
theorem fail_left_zero (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate 2 false) h (atCursor [] under buffer 0) =
      some (h - 2,
        fromCells (mem6 false) under (2 :: 2 :: 2 :: buffer)) := by
  have hcfg : atCursor [] under buffer 0 =
      fromCells 3 (2 :: 2 :: under) (cell false :: buffer) := by
    refine fromCells_eq rfl ?_ ?_
    · simp [cursorLeft, headerL_zero, cells, zeros, List.take]
    · simp [cursorTape, cells, cell]
  have hw : List.replicate 2 false = [false] ++ [false] := rfl
  rw [hcfg, hw, run_append]
  have hm := step3 false h 2 (2 :: under) buffer
  rw [hm, bind_run]
  have hend : h - 1 - 1 = h - 2 := by omega
  simpa [hend] using step45_sep false (h - 1) 2 under (2 :: buffer)
theorem fail_right_zero (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate 2 false) (h - 2)
      (fromCells (mem6 false) under (2 :: 2 :: 2 :: buffer)) =
      some (h, fromCells 15 (2 :: 2 :: under) (2 :: buffer)) := by
  have hw : List.replicate 2 false = [false] ++ [false] := rfl
  rw [hw, run_append]
  have ht := step67_two false (h - 2) under (2 :: 2 :: buffer)
  rw [ht, bind_run]
  have hend : h - 2 + 1 + 1 = h := by omega
  simpa [hend] using step14_two (h - 2 + 1) (2 :: under) (2 :: buffer)
theorem fail_back_zero (under buffer : List (Fin 3)) (h : Int) :
    run program 2 (List.replicate 1 false) h
      (fromCells 15 (2 :: 2 :: under) (2 :: buffer)) =
      some (h - 1, fromCells 16 (2 :: under) (2 :: 2 :: buffer)) := by
  simpa [replicate_one_false] using
    step15_two h 2 (2 :: under) buffer
theorem fail_left_pos (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (hx : 0 < x.length) :
    run program 2 (List.replicate (2 * x.length + 2) false) h
      (atCursor x under buffer x.length) =
      some (h - (2 * x.length + 2 : Int),
        fromCells (mem6 false) under
          (2 :: (ones x.length ++ 2 :: (cells x ++ 2 :: buffer)))) := by
  rw [word4, atCursor_done]
  have hrev := cells_reverse_last x hx
  have hL :
      (cells x).reverse ++ 2 :: ones x.length ++ 2 :: under =
        cell x[x.length - 1] ::
          ((cells (x.take (x.length - 1))).reverse ++
            2 :: ones x.length ++ 2 :: under) := by
    rw [hrev]
    simp [List.cons_append, List.append_assoc]
  rw [hL]
  have htape0 :
      fromCells (3 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              2 :: ones x.length ++ 2 :: under))
          (0 :: buffer) =
        fromCells (3 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              2 :: ones x.length ++ 2 :: under))
          (cell false :: buffer) := by
    refine fromCells_eq rfl rfl ?_
    simp [cell]
  rw [htape0, run_append]
  have hm :=
    step3 false h (cell x[x.length - 1])
      ((cells (x.take (x.length - 1))).reverse ++
        2 :: ones x.length ++ 2 :: under) buffer
  rw [hm, bind_run]
  have has : ∀ a ∈ (cells (x.take (x.length - 1))).reverse, a.val < 2 := by
    intro a ha
    exact cells_val_lt (x.take (x.length - 1)) a (List.mem_reverse.mp ha)
  have hsrc :=
    scan45_cells false (cell x[x.length - 1])
      (cells (x.take (x.length - 1))).reverse (cell_val_lt _) has
      (h - 1) 2 (ones x.length ++ 2 :: under) (2 :: buffer)
  have hlenas : (cells (x.take (x.length - 1))).reverse.length =
      x.length - 1 := by
    simp [cells_length, take_len x (x.length - 1) (Nat.sub_le _ _)]
  have hk1 : (x.length - 1) + 1 = x.length :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
  simp only [hlenas] at hsrc
  rw [← natCast_succ (x.length - 1), hk1] at hsrc
  have hL2 :
      (cells (x.take (x.length - 1))).reverse ++
          2 :: ones x.length ++ 2 :: under =
        (cells (x.take (x.length - 1))).reverse ++
          2 :: (ones x.length ++ 2 :: under) :=
    List.append_assoc _ _ _
  rw [hL2, run_append, hsrc, bind_run]
  have htk :
      cells (x.take (x.length - 1)) ++ [cell x[x.length - 1]] = cells x := by
    have hj : x.length - 1 < x.length := by omega
    have hadd : x.length - 1 + 1 = x.length :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
    simpa [hadd, take_all] using cells_take_concat x (x.length - 1) hj
  have hsepl :=
    step45_sep false (h - 1 - (x.length : Int)) 1
      (ones (x.length - 1) ++ 2 :: under)
      (cells x ++ 2 :: buffer)
  have hones : ones x.length = 1 :: ones (x.length - 1) := by
    rw [← hk1]
    exact ones_succ (x.length - 1)
  rw [hones]
  have hseplCfg :
      fromCells (mem4 false)
          (1 :: ones (x.length - 1) ++ 2 :: under)
          (2 :: (cells (x.take (x.length - 1))).reverse.reverse ++
            cell x[x.length - 1] :: 2 :: buffer) =
        fromCells (mem4 false)
          (1 :: (ones (x.length - 1) ++ 2 :: under))
          (2 :: (cells x ++ 2 :: buffer)) := by
    refine fromCells_eq rfl ?_ ?_
    · simp [List.cons_append]
    · simp [List.reverse_reverse, List.cons_append]
      rw [← List.singleton_append, ← List.append_assoc, htk]
  rw [hseplCfg, run_append, hsepl, bind_run]
  have hctr :=
    scan67_ones false (x.length - 1) (h - 1 - (x.length : Int) - 1) 2
      under (2 :: (cells x ++ 2 :: buffer))
  simp only [hk1] at hctr
  rw [← natCast_succ (x.length - 1), hk1] at hctr
  rw [show
      1 :: 2 :: (cells x ++ 2 :: buffer) =
        1 :: (2 :: (cells x ++ 2 :: buffer)) from rfl,
    hctr]
  apply congrArg some
  congr 1
  · omega
  · simp [hones, List.cons_append]
theorem fail_right_pos (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (hx : 0 < x.length) :
    run program 2 (List.replicate (2 * x.length + 2) false)
      (h - (2 * x.length + 2 : Int))
      (fromCells (mem6 false) under
        (2 :: (ones x.length ++ 2 :: (cells x ++ 2 :: buffer)))) =
      some (h,
        fromCells 15 ((cells x).reverse ++ (2 :: ones x.length ++ 2 :: under))
          (2 :: buffer)) := by
  rw [word4, run_append]
  have hturn :=
    step67_two false (h - (2 * x.length + 2 : Int)) under
      (ones x.length ++ 2 :: (cells x ++ 2 :: buffer))
  rw [hturn, bind_run]
  have hfwd :=
    scan14_ones x.length (h - (2 * x.length + 2 : Int) + 1)
      (2 :: under) (2 :: (cells x ++ 2 :: buffer))
  rw [run_append, hfwd, bind_run]
  have h14 :=
    step14_two
      (h - (2 * x.length + 2 : Int) + 1 + x.length)
      (ones x.length ++ 2 :: under) (cells x ++ 2 :: buffer)
  rw [run_append, h14, bind_run]
  have hsrcf :=
    scan15_bits x
      (h - (2 * x.length + 2 : Int) + 1 + x.length + 1)
      (2 :: ones x.length ++ 2 :: under) (2 :: buffer)
  have h15L :
      fromCells (15 : Fin 24) (2 :: (ones x.length ++ 2 :: under))
          (cells x ++ 2 :: buffer) =
        fromCells (15 : Fin 24) (2 :: ones x.length ++ 2 :: under)
          (cells x ++ 2 :: buffer) := by
    refine fromCells_eq rfl ?_ rfl
    simp [List.cons_append]
  rw [h15L, hsrcf]
  apply congrArg some
  apply Prod.ext
  · omega
  · rfl
theorem fail_back_pos (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (hx : 0 < x.length) :
    run program 2 (List.replicate (x.length + 1) false) h
      (fromCells 15 ((cells x).reverse ++ (2 :: ones x.length ++ 2 :: under))
        (2 :: buffer)) =
      some (h - (x.length + 1 : Int),
        fromCells 16 (ones x.length ++ 2 :: under)
          (2 :: (cells x ++ 2 :: buffer))) := by
  have hrev := cells_reverse_last x hx
  have has : ∀ a ∈ (cells (x.take (x.length - 1))).reverse, a.val < 2 := by
    intro a ha
    exact cells_val_lt (x.take (x.length - 1)) a (List.mem_reverse.mp ha)
  have hlenas : (cells (x.take (x.length - 1))).reverse.length =
      x.length - 1 := by
    simp [cells_length, take_len x (x.length - 1) (Nat.sub_le _ _)]
  have hk1 : (x.length - 1) + 1 = x.length :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
  have hw : List.replicate (x.length + 1) false =
      [false] ++ List.replicate x.length false := by
    simp [List.replicate_add, List.replicate_succ]
  rw [hw, run_append]
  have h15R :
      fromCells (15 : Fin 24)
          ((cells x).reverse ++ (2 :: ones x.length ++ 2 :: under))
          (2 :: buffer) =
        fromCells (15 : Fin 24)
          (cell x[x.length - 1] ::
            ((cells (x.take (x.length - 1))).reverse ++
              (2 :: ones x.length ++ 2 :: under)))
          (2 :: buffer) := by
    refine fromCells_eq rfl ?_ rfl
    rw [hrev]
    simp [List.cons_append]
  rw [h15R]
  have h15 :=
    step15_two h (cell x[x.length - 1])
      ((cells (x.take (x.length - 1))).reverse ++
        (2 :: ones x.length ++ 2 :: under)) buffer
  rw [h15, bind_run]
  have hback :=
    scan16_cells (cell x[x.length - 1])
      (cells (x.take (x.length - 1))).reverse (cell_val_lt _) has
      (h - 1) 2 (ones x.length ++ 2 :: under) (2 :: buffer)
  simp only [hlenas, hk1] at hback
  rw [← natCast_succ (x.length - 1), hk1] at hback
  have hbackL :
      (cells (x.take (x.length - 1))).reverse ++
          (2 :: ones x.length ++ 2 :: under) =
        (cells (x.take (x.length - 1))).reverse ++
          2 :: (ones x.length ++ 2 :: under) := by
    simp [List.cons_append]
  have htk :
      cells (x.take (x.length - 1)) ++ [cell x[x.length - 1]] = cells x := by
    have hj : x.length - 1 < x.length := by omega
    have hadd : x.length - 1 + 1 = x.length :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hx)
    simpa [hadd, take_all] using cells_take_concat x (x.length - 1) hj
  rw [hbackL, hback]
  apply congrArg some
  congr 1
  · omega
  · refine fromCells_eq rfl rfl ?_
    rw [List.reverse_reverse, List.cons_append]
    refine congrArg (List.cons 2) ?_
    rw [show cell x[x.length - 1] :: 2 :: buffer =
        [cell x[x.length - 1]] ++ 2 :: buffer from rfl,
      ← List.append_assoc, htk]
theorem fail_head (x : List Bool) (under buffer : List (Fin 3))
    (h : Int) (t : Nat) (ht : t ≤ failCost x.length) :
    ∃ hf zf,
      run program 2 (List.replicate t false) h
        (atCursor x under buffer x.length) = some (hf, zf) ∧
        h - (2 * x.length + 2 : Int) ≤ hf ∧ hf ≤ h := by
  cases x with
  | nil =>
      have hL := fail_left_zero under buffer h
      have hR := fail_right_zero under buffer h
      have hB := fail_back_zero under buffer h
      have hfull := fail_run_zero under buffer h
      simp [failCost] at ht
      have ht' : t ≤ 6 := ht
      by_cases h2 : t ≤ 2
      · have hL' :
            run program 2 (List.replicate 2 false) h
              (atCursor [] under buffer 0) =
              some (h - (2 : Nat),
                fromCells (mem6 false) under (2 :: 2 :: 2 :: buffer)) := by
          convert hL
          omega
        obtain ⟨zf, hz⟩ := prefix_exact_left hL' h2
        exact ⟨h - t, zf, hz, by omega, by omega⟩
      · by_cases h4 : t ≤ 4
        · have hs : t - 2 ≤ 2 := by omega
          have hR' :
              run program 2 (List.replicate 2 false) (h - 2)
                (fromCells (mem6 false) under (2 :: 2 :: 2 :: buffer)) =
                some ((h - 2) + (2 : Nat),
                  fromCells 15 (2 :: 2 :: under) (2 :: buffer)) := by
            convert hR
            omega
          obtain ⟨zf, hz⟩ := prefix_exact_right hR' hs
          refine ⟨(h - 2) + (t - 2 : Nat), zf, ?_, by omega, by omega⟩
          have hrun := replicate_add_run program (2 : Fin 3) 2 (t - 2) h
            (atCursor [] under buffer 0) hL hz
          have hlen : 2 + (t - 2) = t := by omega
          simpa [hlen] using hrun
        · by_cases h5 : t ≤ 5
          · have hmid := replicate_add_run program (2 : Fin 3) 2 2 h
              (atCursor [] under buffer 0) hL hR
            have hs : t - 4 ≤ 1 := by omega
            have hB' :
                run program 2 (List.replicate 1 false) h
                  (fromCells 15 (2 :: 2 :: under) (2 :: buffer)) =
                  some (h - (1 : Nat),
                    fromCells 16 (2 :: under) (2 :: 2 :: buffer)) := by
              convert hB
              omega
            obtain ⟨zf, hz⟩ := prefix_exact_left hB' hs
            refine ⟨h - (t - 4 : Nat), zf, ?_, by omega, by omega⟩
            have hmid' :
                run program 2 (List.replicate 4 false) h
                  (atCursor [] under buffer 0) =
                  some (h, fromCells 15 (2 :: 2 :: under) (2 :: buffer)) := by
              simpa using hmid
            have hrun := replicate_add_run program (2 : Fin 3) 4 (t - 4) h
              (atCursor [] under buffer 0) hmid' hz
            have hlen : 4 + (t - 4) = t := by omega
            simpa [hlen] using hrun
          · have : t = 6 := by omega
            subst this
            exact ⟨h, finalConfig [] under buffer,
              by simpa [failCost] using hfull, by omega, by omega⟩
  | cons b xs =>
      set n := (b :: xs).length
      have hx : 0 < n := Nat.succ_pos _
      have hL := fail_left_pos (b :: xs) under buffer h hx
      have hR := fail_right_pos (b :: xs) under buffer h hx
      have hB := fail_back_pos (b :: xs) under buffer h hx
      have hfull := fail_run_pos (b :: xs) under buffer h hx
      have hn : n = (b :: xs).length := rfl
      by_cases h2 : t ≤ 2 * n + 2
      · obtain ⟨zf, hz⟩ := prefix_exact_left hL h2
        exact ⟨h - t, zf, hz, by omega, by omega⟩
      · by_cases h4 : t ≤ 4 * n + 4
        · have hs : t - (2 * n + 2) ≤ 2 * n + 2 := by omega
          have hR' :
              run program 2 (List.replicate (2 * n + 2) false)
                (h - (2 * n + 2 : Int))
                (fromCells (mem6 false) under
                  (2 :: (ones n ++ 2 :: (cells (b :: xs) ++ 2 :: buffer)))) =
                some ((h - (2 * n + 2 : Int)) + (2 * n + 2 : Nat),
                  fromCells 15
                    ((cells (b :: xs)).reverse ++
                      (2 :: ones n ++ 2 :: under))
                    (2 :: buffer)) := by
            convert hR
            omega
          obtain ⟨zf, hz⟩ := prefix_exact_right hR' hs
          refine ⟨(h - (2 * n + 2 : Int)) + (t - (2 * n + 2) : Nat), zf, ?_,
            by omega, by omega⟩
          have hrun := replicate_add_run program (2 : Fin 3)
            (2 * n + 2) (t - (2 * n + 2)) h
            (atCursor (b :: xs) under buffer n) hL hz
          have hlen : 2 * n + 2 + (t - (2 * n + 2)) = t := by omega
          convert hrun
          rw [hlen]
        · by_cases h5 : t ≤ 5 * n + 5
          · have hmid := replicate_add_run program (2 : Fin 3)
              (2 * n + 2) (2 * n + 2) h
              (atCursor (b :: xs) under buffer n) hL hR
            have hs : t - (4 * n + 4) ≤ n + 1 := by omega
            have hB' :
                run program 2 (List.replicate (n + 1) false) h
                  (fromCells 15
                    ((cells (b :: xs)).reverse ++
                      (2 :: ones n ++ 2 :: under))
                    (2 :: buffer)) =
                  some (h - (n + 1 : Nat),
                    fromCells 16 (ones n ++ 2 :: under)
                      (2 :: (cells (b :: xs) ++ 2 :: buffer))) := by
              convert hB
              omega
            obtain ⟨zf, hz⟩ := prefix_exact_left hB' hs
            refine ⟨h - (t - (4 * n + 4) : Nat), zf, ?_, by omega, by omega⟩
            have hmid' :
                run program 2 (List.replicate (4 * n + 4) false) h
                  (atCursor (b :: xs) under buffer n) =
                  some (h,
                    fromCells 15
                      ((cells (b :: xs)).reverse ++
                        (2 :: ones (b :: xs).length ++ 2 :: under))
                      (2 :: buffer)) := by
              have hlen : 2 * n + 2 + (2 * n + 2) = 4 * n + 4 := by omega
              simpa [hlen] using hmid
            have hrun := replicate_add_run program (2 : Fin 3)
              (4 * n + 4) (t - (4 * n + 4)) h
              (atCursor (b :: xs) under buffer n) hmid' hz
            have hlen : 4 * n + 4 + (t - (4 * n + 4)) = t := by omega
            convert hrun
            rw [hlen]
          · have : t = failCost n := by simp [failCost] at ht ⊢; omega
            subst this
            exact ⟨h - n, finalConfig (b :: xs) under buffer, hfull, by omega,
              by omega⟩
theorem prefix_head (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) (t : Nat) (ht : t ≤ deadline x.length) :
    ∃ hf zf,
      run program 2 (List.replicate t false) H
        (initial x under buffer) = some (hf, zf) ∧
        H - 1 ≤ hf ∧ hf ≤ H + (2 * x.length + 1 : Int) := by
  by_cases h1 : t ≤ x.length + 1
  · obtain ⟨zf, hz⟩ := init_head x under buffer H t h1
    exact ⟨H + t, zf, hz, by omega, by omega⟩
  · have hinit := init_run x under buffer H
    by_cases h2 : t - (x.length + 1) ≤ copiesCost x.length
    · obtain ⟨hf, zf, hz, hlo, hhi⟩ :=
        copies_head x under buffer (H + x.length + 1)
          (t - (x.length + 1)) h2
      refine ⟨hf, zf, ?_, by omega, by omega⟩
      have hlen : x.length + 1 + (t - (x.length + 1)) = t := by omega
      have hrun := replicate_add_run program 2 (x.length + 1)
        (t - (x.length + 1)) H (initial x under buffer) hinit hz
      simpa [hlen] using hrun
    · have hD := deadline_split x.length
      have hle : x.length + 1 + copiesCost x.length ≤ t := by omega
      have hc : t - (x.length + 1 + copiesCost x.length) ≤
          failCost x.length := by omega
      have hcopies :=
        copies_prefix x under buffer (H + x.length + 1) x.length le_rfl
      obtain ⟨hf, zf, hz, hlo, hhi⟩ :=
        fail_head x under buffer (H + x.length + 1 + x.length)
          (t - (x.length + 1 + copiesCost x.length)) hc
      refine ⟨hf, zf, ?_, by omega, by omega⟩
      have hrun1 := replicate_add_run program 2 (x.length + 1)
        (copiesCost x.length) H (initial x under buffer) hinit hcopies
      have hlen1 : x.length + 1 + copiesCost x.length +
          (t - (x.length + 1 + copiesCost x.length)) = t := by omega
      have hrun := replicate_add_run program 2
        (x.length + 1 + copiesCost x.length)
        (t - (x.length + 1 + copiesCost x.length)) H
        (initial x under buffer) hrun1 hz
      simpa [hlen1] using hrun
theorem every_raw (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
    {w : List Bool} {hf : Int} {zf : BoundedConfig 24 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    w = List.replicate w.length false ∧
      w.length ≤ deadline x.length ∧
      H - 1 ≤ hf ∧ hf ≤ H + (2 * x.length + 1 : Int) ∧
      cellCount zf = occupied x under buffer := by
  have hwfalse :=
    successful_zipper_is_false (2 : Fin 3) program program_falseOnly hw
  have hlen :=
    successful_zipper_length_le (2 : Fin 3) program program_falseOnly
      (deadline x.length) H (initial x under buffer)
      (finalConfig x under buffer) (H + x.length + 1)
      (delimiter_run x under buffer H) (final_state x under buffer) hw
  refine ⟨hwfalse, hlen, ?_⟩
  have ⟨hf', zf', hpre, hlo, hhi⟩ := prefix_head x under buffer H w.length hlen
  have hw' : run program 2 (List.replicate w.length false) H
      (initial x under buffer) = some (hf, zf) := by
    rwa [← hwfalse]
  have heq := hw'.symm.trans hpre
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
  refine ⟨hlo, hhi, ?_⟩
  have ⟨lg, rg, hG⟩ :=
    every_actual_run program 2 (List.replicate (deadline x.length) false) H
      (H + x.length + 1) (initial x under buffer) (finalConfig x under buffer)
      (delimiter_run x under buffer H)
  have hF := hG.exact_ledger
  have hcntF :
      cellCount (finalConfig x under buffer) =
        cellCount (initial x under buffer) + lg + rg :=
    hF.2.2.1
  have hcnt :
      cellCount (finalConfig x under buffer) =
        cellCount (initial x under buffer) := by
    rw [occupied_final, occupied_initial]
  have h0 : lg = 0 ∧ rg = 0 := by omega
  have hsplit :
      List.replicate (deadline x.length) false =
        List.replicate w.length false ++
          List.replicate (deadline x.length - w.length) false :=
    replicate_split (deadline x.length) w.length hlen
  have hGfull : GrowthRun program 2
      (List.replicate w.length false ++
        List.replicate (deadline x.length - w.length) false)
      H (initial x under buffer) (H + x.length + 1)
      (finalConfig x under buffer) lg rg := by
    simpa [hsplit] using hG
  obtain ⟨lg1, rg1, hG1⟩ :=
    every_actual_run program 2 (List.replicate w.length false) H hf
      (initial x under buffer) zf hw'
  have ⟨hleL, hleR⟩ := growth_append_le hGfull hG1
  have hP := hG1.exact_ledger
  have hcntP :
      cellCount zf = cellCount (initial x under buffer) + lg1 + rg1 :=
    hP.2.2.1
  have hocc := occupied_initial x under buffer
  omega
theorem every_raw_no_growth (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) {w : List Bool} {hf : Int} {zf : BoundedConfig 24 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf)) :
    GrowthRun program 2 w H (initial x under buffer) hf zf 0 0 := by
  obtain ⟨lg, rg, hg⟩ :=
    every_actual_run program 2 w H hf (initial x under buffer) zf hw
  have hraw := every_raw x under buffer H hw
  have he := hg.exact_ledger
  have h0 := occupied_initial x under buffer
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa [hl, hr] using hg
theorem accepting_word (x : List Bool) (under buffer : List (Fin 3))
    (H : Int) {w : List Bool} {hf : Int} {zf : BoundedConfig 24 3}
    (hw : run program 2 w H (initial x under buffer) = some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (deadline x.length) false ∧
      hf = H + x.length + 1 ∧
      zf = finalConfig x under buffer :=
  accepting_zipper_word_eq (2 : Fin 3) program program_falseOnly
    (deadline x.length) H (initial x under buffer)
    (finalConfig x under buffer) (H + x.length + 1)
    (delimiter_run x under buffer H) (final_state x under buffer) hw ha
theorem delimiter_spec :
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int),
      run program 2 (List.replicate (deadline x.length) false) H
        (initial x under buffer) =
      some (H + x.length + 1, finalConfig x under buffer)) ∧
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig 24 3),
      run program 2 w H (initial x under buffer) = some (hf, zf) →
      w = List.replicate w.length false ∧
        w.length ≤ deadline x.length ∧
        H - 1 ≤ hf ∧ hf ≤ H + (2 * x.length + 1 : Int) ∧
        cellCount zf = occupied x under buffer ∧
        GrowthRun program 2 w H (initial x under buffer) hf zf 0 0) ∧
    (∀ (x : List Bool) (under buffer : List (Fin 3)) (H : Int)
      (w : List Bool) (hf : Int) (zf : BoundedConfig 24 3),
      run program 2 w H (initial x under buffer) = some (hf, zf) →
      zf.state.val = 0 →
      w = List.replicate (deadline x.length) false ∧
        hf = H + x.length + 1 ∧
        zf = finalConfig x under buffer) ∧
    (∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3) := by
  refine ⟨delimiter_run, ?_, ?_, compiled_symbols⟩
  · intro x under buffer H w hf zf hw
    have h := every_raw x under buffer H hw
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      every_raw_no_growth x under buffer H hw⟩
  · intro x under buffer H w hf zf hw ha
    exact accepting_word x under buffer H hw ha
end PakFixedPolyomino.ULogTernaryCountedSourceDelimiterSpace
