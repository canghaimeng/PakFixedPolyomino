import PakFixedPolyomino.ULogTernaryNestedHeaderParser
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Every successful raw word of the ternary nested-header positioning
parser. Occupied cells and the integer head come from operational prefix
identities, including d = 0, c = 0, empty x, and arbitrary left/suffix. -/

namespace PakFixedPolyomino.ULogTernaryNestedHeaderParserSpace

open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteAlphabetDeterministicRuns
open ULogTernaryNestedHeaderParser
open ULogTernaryRetainedCounterPump (cell cells)

def cellCount {ns nt : Nat} (z : BoundedConfig ns nt) : Nat :=
  z.leftRev.length + 1 + z.right.length

def headerLen (d c : Nat) (x : List Bool) : Nat :=
  (header d c x).length

def consumedTrues (d c t : Nat) (x : List Bool) : Nat :=
  List.count true ((header d c x).take t)

def consumedSeed (d c t : Nat) (x : List Bool) : Nat :=
  t - (squareHeaders d c x).length

def prefixQNat (d c t : Nat) (x : List Bool) : Nat :=
  2 + consumedTrues d c t x + consumedSeed d c t x

theorem parser_falseOnly (d c : Nat) : FalseOnly (parserProgram d c) :=
  fun q read => rule_true d c q read

theorem squareHeaders_count_true (d c : Nat) (x : List Bool) :
    List.count true (squareHeaders d c x) = d := by
  induction d with
  | zero => simp [squareHeaders]
  | succ d ih =>
      simp [squareHeaders, List.count_cons, List.count_append,
        List.count_replicate, ih]

theorem header_count_true (d c : Nat) (x : List Bool) :
    List.count true (header d c x) = d := by
  simp [header_eq_square_seed, List.count_append, List.count_replicate,
    squareHeaders_count_true]

theorem count_true_take_le (d c t : Nat) (x : List Bool) :
    consumedTrues d c t x ≤ d := by
  have hsplit := List.take_append_drop t (header d c x)
  have hc :
      List.count true ((header d c x).take t) +
        List.count true ((header d c x).drop t) = d := by
    rw [← List.count_append, hsplit, header_count_true]
  unfold consumedTrues
  exact (Nat.le_add_right _ _).trans_eq hc

theorem headerLen_eq (d c : Nat) (x : List Bool) :
    headerLen d c x = (squareHeaders d c x).length + c := by
  simp [headerLen, header_eq_square_seed]

theorem consumedSeed_le (d c t : Nat) (x : List Bool)
    (ht : t ≤ headerLen d c x) :
    consumedSeed d c t x ≤ c := by
  have hlen := headerLen_eq d c x
  unfold consumedSeed headerLen at *
  omega

theorem prefixQNat_le (d c t : Nat) (x : List Bool)
    (ht : t ≤ headerLen d c x) :
    prefixQNat d c t x ≤ 2 + d + c := by
  have h1 := count_true_take_le d c t x
  have h2 := consumedSeed_le d c t x ht
  unfold prefixQNat
  omega

theorem prefixQNat_lt (d c t : Nat) (x : List Bool)
    (ht : t ≤ headerLen d c x) :
    prefixQNat d c t x < d + c + 4 := by
  have h := prefixQNat_le d c t x ht
  omega

def prefixQ (d c t : Nat) (x : List Bool) (ht : t ≤ headerLen d c x) :
    Fin (d + c + 4) :=
  ⟨prefixQNat d c t x, prefixQNat_lt d c t x ht⟩

theorem prefixQNat_zero (d c : Nat) (x : List Bool) :
    prefixQNat d c 0 x = 2 := by
  unfold prefixQNat consumedTrues consumedSeed
  simp

theorem prefixQ_zero (d c : Nat) (x : List Bool) :
    prefixQ d c 0 x (Nat.zero_le _) = startState d c :=
  Fin.ext (by
    change prefixQNat d c 0 x = (startState d c).val
    rw [prefixQNat_zero, startState_val])

theorem prefixQNat_full (d c : Nat) (x : List Bool) :
    prefixQNat d c (headerLen d c x) x = 2 + d + c := by
  have htake : (header d c x).take (headerLen d c x) = header d c x := by
    unfold headerLen; simp
  unfold prefixQNat consumedTrues consumedSeed
  rw [htake, header_count_true]
  have hlen := headerLen_eq d c x
  unfold headerLen at *
  omega

theorem prefixQ_full (d c : Nat) (x : List Bool) :
    prefixQ d c (headerLen d c x) x le_rfl = haltState d c :=
  Fin.ext (by
    change prefixQNat d c (headerLen d c x) x = (haltState d c).val
    rw [prefixQNat_full, haltState_val])

theorem cellCount_cons {ns : Nat} (q : Fin ns) (left : List (Fin 3))
    (a : Fin 3) (rest : List (Fin 3)) :
    cellCount (fromCells q left (a :: rest)) =
      left.length + rest.length + 1 := by
  unfold cellCount fromCells
  simp
  omega

theorem cellCount_of_cells {ns : Nat} (q : Fin ns) (left tape : List (Fin 3))
    (hne : tape ≠ []) :
    cellCount (fromCells q left tape) = left.length + tape.length := by
  cases tape with
  | nil => exact (hne rfl).elim
  | cons a rest =>
      simp [cellCount_cons]; omega

theorem fromCells_state {ns : Nat} (q : Fin ns) (left right : List (Fin 3)) :
    (fromCells q left right).state = q := by
  cases right <;> rfl

theorem getElem_proof_irrel {α : Type*} (l : List α) (t : Nat)
    (h1 h2 : t < l.length) : l[t]'h1 = l[t]'h2 := by
  congr

theorem remaining_length (d c t : Nat) (x : List Bool)
    (suffix : List (Fin 3)) (ht : t ≤ headerLen d c x) :
    (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix).length =
      (headerLen d c x - t) + (counted x).length + suffix.length := by
  have hdrop : ((header d c x).drop t).length = headerLen d c x - t := by
    unfold headerLen at *
    simp [List.length_drop]
    try omega
  simp [cells_length, hdrop]
  try omega

theorem remaining_ne_nil (d c t : Nat) (x : List Bool)
    (suffix : List (Fin 3)) (ht : t ≤ headerLen d c x) :
    cells ((header d c x).drop t) ++ cells (counted x) ++ suffix ≠ [] := by
  intro hempty
  have hl := congrArg List.length hempty
  have hlen := remaining_length d c t x suffix ht
  simp [cells_length, counted_length] at hl hlen
  try omega

theorem nested_cells_split (d c : Nat) (x : List Bool) (t : Nat)
    (suffix : List (Fin 3)) :
    cells (nested d c x) ++ suffix =
      cells ((header d c x).take t) ++
        (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix) := by
  rw [cells_nested]
  rw [show header d c x =
      (header d c x).take t ++ (header d c x).drop t from
    (List.take_append_drop t (header d c x)).symm]
  rw [cells_append]
  simp [List.append_assoc]

theorem take_succ_append_get (l : List Bool) (t : Nat) (ht : t < l.length) :
    l.take (t + 1) = l.take t ++ [l[t]] := by
  induction t generalizing l with
  | zero =>
      cases l with
      | nil => simp at ht
      | cons b bs => simp
  | succ t ih =>
      cases l with
      | nil => simp at ht
      | cons b bs =>
          have ht' : t < bs.length := by
            simp only [List.length_cons] at ht
            omega
          simp [List.take]
          try exact congrArg (List.cons b) (ih bs ht')

theorem drop_cons_get {α : Type*} (l : List α) (t : Nat)
    (ht : t < l.length) :
    l.drop t = l[t] :: l.drop (t + 1) := by
  induction t generalizing l with
  | zero =>
      cases l with
      | nil => simp at ht
      | cons b bs => simp
  | succ t ih =>
      cases l with
      | nil => simp at ht
      | cons _ bs =>
          have ht' : t < bs.length := by
            simp only [List.length_cons] at ht
            omega
          simp [List.drop]
          try exact ih bs ht'

theorem append_right_ne_nil {α : Type*} (as bs : List α) (hbs : bs ≠ []) :
    as ++ bs ≠ [] := by
  cases as <;> simp [hbs]

theorem getLast_cons_ne {α : Type*} (a : α) (as : List α) (h : as ≠ []) :
    (a :: as).getLast (by simp) = as.getLast h := by
  cases as with
  | nil => exact (h rfl).elim
  | cons _ _ => rfl

theorem getLast_append_right {α : Type*} (as bs : List α)
    (h : as ++ bs ≠ []) (hbs : bs ≠ []) :
    (as ++ bs).getLast h = bs.getLast hbs := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have hne : as ++ bs ≠ [] := append_right_ne_nil as bs hbs
      simp [getLast_cons_ne a (as ++ bs) hne]
      exact ih hne

theorem squareHeaders_getLast_true (d c : Nat) (x : List Bool)
    (hne : squareHeaders d c x ≠ []) :
    (squareHeaders d c x).getLast hne = true := by
  induction d with
  | zero => simp [squareHeaders] at hne
  | succ d ih =>
      simp only [squareHeaders]
      have hr : true :: squareHeaders d c x ≠ [] := by simp
      have happ : List.replicate ((nested d c x).length ^ 2) false ++
          true :: squareHeaders d c x ≠ [] := by simp
      rw [getLast_append_right _ _ happ hr]
      cases d with
      | zero => simp [squareHeaders]
      | succ d =>
          have hinner : squareHeaders (d + 1) c x ≠ [] := by
            have hc := squareHeaders_count_true (d + 1) c x
            have : 0 < List.count true (squareHeaders (d + 1) c x) := by omega
            exact List.ne_nil_of_mem (List.count_pos_iff.mp this)
          rw [getLast_cons_ne true _ hinner, ih hinner]

theorem getLast_eq_drop_getLast {α : Type*} (l : List α) (t : Nat)
    (ht : t < l.length) (hne : l ≠ []) (hdrop : l.drop t ≠ []) :
    l.getLast hne = (l.drop t).getLast hdrop := by
  have hsplit := List.take_append_drop t l
  have happ : l.take t ++ l.drop t ≠ [] := by
    rw [List.take_append_drop]
    exact hne
  have hlast := getLast_append_right (l.take t) (l.drop t) happ hdrop
  have : l.getLast hne = (l.take t ++ l.drop t).getLast happ := by
    simp [hsplit]
  exact this.trans hlast

theorem true_mem_drop_square (d c t : Nat) (x : List Bool)
    (ht : t < (squareHeaders d c x).length) :
    true ∈ (squareHeaders d c x).drop t := by
  have hne : squareHeaders d c x ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hdrop : (squareHeaders d c x).drop t ≠ [] := by
    intro h
    simp [List.drop_eq_nil_iff] at h
    omega
  have hlast := squareHeaders_getLast_true d c x hne
  have heq := getLast_eq_drop_getLast (squareHeaders d c x) t ht hne hdrop
  rw [hlast] at heq
  exact (heq ▸ List.getLast_mem hdrop)

theorem consumedTrues_lt_d (d c t : Nat) (x : List Bool)
    (ht : t < (squareHeaders d c x).length) :
    consumedTrues d c t x < d := by
  have htake : (header d c x).take t = (squareHeaders d c x).take t := by
    rw [header_eq_square_seed]
    exact List.take_append_of_le_length (le_of_lt ht)
  have hfull := squareHeaders_count_true d c x
  have hsplit := List.take_append_drop t (squareHeaders d c x)
  have hc :
      List.count true ((squareHeaders d c x).take t) +
        List.count true ((squareHeaders d c x).drop t) = d := by
    rw [← List.count_append, hsplit, hfull]
  have hpos : 0 < List.count true ((squareHeaders d c x).drop t) :=
    List.count_pos_iff.mpr (true_mem_drop_square d c t x ht)
  unfold consumedTrues
  rw [htake]
  omega

theorem prefixQ_header_range (d c t : Nat) (x : List Bool)
    (ht : t < (squareHeaders d c x).length) :
    2 ≤ prefixQNat d c t x ∧ prefixQNat d c t x ≤ d + 1 := by
  have hsub : consumedSeed d c t x = 0 := by
    unfold consumedSeed; omega
  have hlt := consumedTrues_lt_d d c t x ht
  unfold prefixQNat
  omega

theorem count_true_take_append_false (l : List Bool) (m t : Nat)
    (hle : l.length ≤ t) (hhi : t ≤ l.length + m) :
    List.count true ((l ++ List.replicate m false).take t) =
      List.count true l := by
  induction l generalizing t with
  | nil =>
      simp [List.take_replicate, List.count_replicate]
  | cons b bs ih =>
      cases t with
      | zero =>
          simp at hle
      | succ t =>
          have hle' : bs.length ≤ t := by simp at hle; exact hle
          have hhi' : t ≤ bs.length + m := by simp at hhi; omega
          simp [List.take, List.count_cons, ih t hle' hhi']

theorem prefixQ_seed_range (d c t : Nat) (x : List Bool)
    (hlo : (squareHeaders d c x).length ≤ t)
    (hhi : t < headerLen d c x) :
    2 + d ≤ prefixQNat d c t x ∧ prefixQNat d c t x < 2 + d + c := by
  have hhi' : t ≤ (squareHeaders d c x).length + c := by
    have := headerLen_eq d c x
    unfold headerLen at hhi this
    omega
  have hct : consumedTrues d c t x = d := by
    unfold consumedTrues
    rw [header_eq_square_seed]
    rw [count_true_take_append_false _ c t hlo hhi']
    exact squareHeaders_count_true d c x
  have hlen := headerLen_eq d c x
  unfold prefixQNat consumedSeed headerLen at *
  omega

theorem header_get_seed (d c t : Nat) (x : List Bool)
    (hlo : (squareHeaders d c x).length ≤ t)
    (hhi : t < headerLen d c x) :
    (header d c x)[t] = false := by
  have hx :
      (header d c x)[t] =
        (squareHeaders d c x ++ List.replicate c false)[t]'(by
          unfold headerLen at hhi
          simpa [header_eq_square_seed] using hhi) := by
    simp [header_eq_square_seed]
  rw [hx, List.getElem_append_right]
  · simp
  · omega

theorem cells_drop_head (d c t : Nat) (x : List Bool)
    (ht : t < headerLen d c x) :
    cells ((header d c x).drop t) =
      cell ((header d c x)[t]) :: cells ((header d c x).drop (t + 1)) := by
  have hd := drop_cons_get (header d c x) t (by unfold headerLen at ht; exact ht)
  simp [hd, cells, cell]

theorem take_succ_cells (d c t : Nat) (x : List Bool)
    (ht : t < headerLen d c x) :
    cells ((header d c x).take (t + 1)) =
      cells ((header d c x).take t) ++ [cell ((header d c x)[t])] := by
  rw [take_succ_append_get _ t (by unfold headerLen at ht; exact ht)]
  simp [cells, cell]

theorem prefixQNat_succ_false_header (d c t : Nat) (x : List Bool)
    (ht : t < (squareHeaders d c x).length)
    (hb : (header d c x)[t]'(by
        have := headerLen_eq d c x
        unfold headerLen at *
        omega) = false) :
    prefixQNat d c (t + 1) x = prefixQNat d c t x := by
  have hsub0 : consumedSeed d c t x = 0 := by unfold consumedSeed; omega
  have hsub1 : consumedSeed d c (t + 1) x = 0 := by unfold consumedSeed; omega
  have ht' : t < headerLen d c x := by
    have := headerLen_eq d c x; unfold headerLen at *; omega
  have hct : consumedTrues d c (t + 1) x = consumedTrues d c t x := by
    unfold consumedTrues
    rw [take_succ_append_get (header d c x) t (by unfold headerLen at ht'; exact ht')]
    simp [List.count_append]
    have hb' : (header d c x)[t] = false := hb
    simp [hb']
  unfold prefixQNat
  omega

theorem prefixQNat_succ_true (d c t : Nat) (x : List Bool)
    (ht : t < (squareHeaders d c x).length)
    (hb : (header d c x)[t]'(by
        have := headerLen_eq d c x
        unfold headerLen at *
        omega) = true) :
    prefixQNat d c (t + 1) x = prefixQNat d c t x + 1 := by
  have hsub0 : consumedSeed d c t x = 0 := by unfold consumedSeed; omega
  have hsub1 : consumedSeed d c (t + 1) x = 0 := by unfold consumedSeed; omega
  have ht' : t < headerLen d c x := by
    have := headerLen_eq d c x; unfold headerLen at *; omega
  have hct : consumedTrues d c (t + 1) x = consumedTrues d c t x + 1 := by
    unfold consumedTrues
    rw [take_succ_append_get (header d c x) t (by unfold headerLen at ht'; exact ht')]
    simp [List.count_append]
    have hb' : (header d c x)[t] = true := hb
    simp [hb']
  unfold prefixQNat
  omega

theorem prefixQNat_succ_seed (d c t : Nat) (x : List Bool)
    (hlo : (squareHeaders d c x).length ≤ t)
    (hhi : t < headerLen d c x) :
    prefixQNat d c (t + 1) x = prefixQNat d c t x + 1 := by
  have hb := header_get_seed d c t x hlo hhi
  have hct : consumedTrues d c (t + 1) x = consumedTrues d c t x := by
    unfold consumedTrues
    rw [take_succ_append_get (header d c x) t (by unfold headerLen at hhi; exact hhi)]
    simp [List.count_append]
    have hb' : (header d c x)[t] = false := hb
    simp [hb']
  have hsub : consumedSeed d c (t + 1) x = consumedSeed d c t x + 1 := by
    unfold consumedSeed; omega
  unfold prefixQNat
  omega

theorem cellCount_prefix_config (d c t : Nat) (x : List Bool)
    (left suffix : List (Fin 3)) (ht : t ≤ headerLen d c x) :
    cellCount
      (fromCells (prefixQ d c t x ht)
        ((cells ((header d c x).take t)).reverse ++ left)
        (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix)) =
      left.length + (nested d c x).length + suffix.length := by
  have hne := remaining_ne_nil d c t x suffix ht
  have hcells :=
    cellCount_of_cells (prefixQ d c t x ht)
      ((cells ((header d c x).take t)).reverse ++ left)
      (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix) hne
  have htk : ((header d c x).take t).length = t :=
    List.length_take_of_le (by unfold headerLen at ht; exact ht)
  have hdrop : ((header d c x).drop t).length = headerLen d c x - t := by
    unfold headerLen at *
    simp [List.length_drop]
  have hleft :
      ((cells ((header d c x).take t)).reverse ++ left).length =
        t + left.length := by
    simp [List.length_append, List.length_reverse, cells_length, htk]
  have hright :
      (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix).length =
        headerLen d c x - t + ((counted x).length + suffix.length) := by
    simp [List.length_append, cells_length, hdrop]
  rw [hcells, hleft, hright, nested_length]
  unfold headerLen at *
  omega

theorem prefix_run (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) (t : Nat) (ht : t ≤ headerLen d c x) :
    run (parserProgram d c) 2 (List.replicate t false) head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
      some (head + t,
        fromCells (prefixQ d c t x ht)
          ((cells ((header d c x).take t)).reverse ++ left)
          (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix)) := by
  induction t with
  | zero =>
      simp [run]
      refine fromCells_eq ?_ (by simp [cells]) ?_
      · apply Fin.ext
        simp [prefixQ, prefixQNat_zero, startState]
      · rw [cells_nested]
        simp [List.append_assoc]
  | succ t ih =>
      have ht0 : t ≤ headerLen d c x := by omega
      have htlt : t < headerLen d c x := by omega
      have hw : List.replicate (t + 1) false =
          List.replicate t false ++ [false] := by
        simp [List.replicate_add]
      rw [hw, run_append, ih ht0, bind_run]
      have hdrop := cells_drop_head d c t x htlt
      have htk := take_succ_cells d c t x htlt
      by_cases hsq : t < (squareHeaders d c x).length
      · have hq : 2 ≤ (prefixQ d c t x ht0).val ∧
            (prefixQ d c t x ht0).val ≤ d + 1 := by
          simpa [prefixQ] using prefixQ_header_range d c t x hsq
        cases hb : (header d c x)[t]'(by unfold headerLen at htlt; exact htlt) with
        | false =>
            have htape :
                cells ((header d c x).drop t) ++ cells (counted x) ++ suffix =
                  (0 : Fin 3) ::
                    (cells ((header d c x).drop (t + 1)) ++
                      cells (counted x) ++ suffix) := by
              simp [hdrop, hb, cell, List.append_assoc]
            rw [htape, step_right_zero d c (prefixQ d c t x ht0) (head + t)
              ((cells ((header d c x).take t)).reverse ++ left)
              (cells ((header d c x).drop (t + 1)) ++ cells (counted x) ++
                suffix) hq]
            refine congrArg some ?_
            apply Prod.ext
            · omega
            · refine fromCells_eq ?_ ?_ (by simp [List.append_assoc])
              · apply Fin.ext
                have hsucc := prefixQNat_succ_false_header d c t x hsq
                  ((getElem_proof_irrel (header d c x) t _ _).trans hb)
                simpa [prefixQ] using hsucc.symm
              · simp [htk, hb, cell, List.reverse_append]
        | true =>
            have htape :
                cells ((header d c x).drop t) ++ cells (counted x) ++ suffix =
                  (1 : Fin 3) ::
                    (cells ((header d c x).drop (t + 1)) ++
                      cells (counted x) ++ suffix) := by
              simp [hdrop, hb, cell, List.append_assoc]
            rw [htape, step_right_one d c (prefixQ d c t x ht0) (head + t)
              ((cells ((header d c x).take t)).reverse ++ left)
              (cells ((header d c x).drop (t + 1)) ++ cells (counted x) ++
                suffix) hq]
            refine congrArg some ?_
            apply Prod.ext
            · omega
            · refine fromCells_eq ?_ ?_ (by simp [List.append_assoc])
              · apply Fin.ext
                have hsucc := prefixQNat_succ_true d c t x hsq
                  ((getElem_proof_irrel (header d c x) t _ _).trans hb)
                simpa [prefixQ] using hsucc.symm
              · simp [htk, hb, cell, List.reverse_append]
      · have hlo : (squareHeaders d c x).length ≤ t := by omega
        have hq : 2 + d ≤ (prefixQ d c t x ht0).val ∧
            (prefixQ d c t x ht0).val < 2 + d + c := by
          simpa [prefixQ] using prefixQ_seed_range d c t x hlo htlt
        have hb := header_get_seed d c t x hlo htlt
        have htape :
            cells ((header d c x).drop t) ++ cells (counted x) ++ suffix =
              (0 : Fin 3) ::
                (cells ((header d c x).drop (t + 1)) ++
                  cells (counted x) ++ suffix) := by
          simp [hdrop, hb, cell, List.append_assoc]
        rw [htape, step_seed d c (prefixQ d c t x ht0) 0 (head + t)
          ((cells ((header d c x).take t)).reverse ++ left)
          (cells ((header d c x).drop (t + 1)) ++ cells (counted x) ++ suffix) hq]
        refine congrArg some ?_
        apply Prod.ext
        · omega
        · refine fromCells_eq ?_ ?_ (by simp [List.append_assoc])
          · apply Fin.ext
            have hsucc := prefixQNat_succ_seed d c t x hlo htlt
            simpa [prefixQ] using hsucc.symm
          · simp [htk, hb, cell, List.reverse_append]

theorem every_successful_false (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) {w : List Bool}
    {hz : Int × BoundedConfig (d + c + 4) 3}
    (hw : run (parserProgram d c) 2 w head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some hz) :
    w = List.replicate w.length false :=
  successful_zipper_is_false (2 : Fin 3) (parserProgram d c)
    (parser_falseOnly d c) hw

theorem every_successful_length (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) {w : List Bool}
    {hz : Int × BoundedConfig (d + c + 4) 3}
    (hw : run (parserProgram d c) 2 w head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some hz) :
    w.length ≤ headerLen d c x + 1 := by
  have hfull := parser_run d c x head left suffix
  exact successful_zipper_length_le (2 : Fin 3) (parserProgram d c)
    (parser_falseOnly d c) (headerLen d c x + 1) head
    (fromCells (startState d c) left (cells (nested d c x) ++ suffix))
    (fromCells (acceptState d c)
      ((cells (header d c x)).reverse ++ left)
      (cells (counted x) ++ suffix))
    (head + (header d c x).length) (by simpa [headerLen] using hfull)
    (by simp [fromCells_state, acceptState]) hw

theorem prefix_or_full (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) (t : Nat)
    (ht : t ≤ headerLen d c x + 1) :
    run (parserProgram d c) 2 (List.replicate t false) head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
      some
        (if t ≤ headerLen d c x then head + t else
          head + (headerLen d c x : Int),
        if hle : t ≤ headerLen d c x then
          fromCells (prefixQ d c t x hle)
            ((cells ((header d c x).take t)).reverse ++ left)
            (cells ((header d c x).drop t) ++ cells (counted x) ++ suffix)
        else
          fromCells (acceptState d c)
            ((cells (header d c x)).reverse ++ left)
            (cells (counted x) ++ suffix)) := by
  by_cases hle : t ≤ headerLen d c x
  · simp [hle, prefix_run d c x head left suffix t hle]
  · have ht' : t = headerLen d c x + 1 := by omega
    subst ht'
    simpa [headerLen] using parser_run d c x head left suffix

theorem every_raw (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) {w : List Bool} {hf : Int}
    {zf : BoundedConfig (d + c + 4) 3}
    (hw : run (parserProgram d c) 2 w head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some (hf, zf)) :
    w = List.replicate w.length false ∧
      w.length ≤ headerLen d c x + 1 ∧
      head ≤ hf ∧ hf ≤ head + (headerLen d c x : Int) ∧
      cellCount zf =
        left.length + (nested d c x).length + suffix.length := by
  have hwfalse := every_successful_false d c x head left suffix hw
  have hlen := every_successful_length d c x head left suffix hw
  refine ⟨hwfalse, hlen, ?_⟩
  have hrun := prefix_or_full d c x head left suffix w.length hlen
  rw [hwfalse] at hw
  rw [hrun] at hw
  by_cases hle : w.length ≤ headerLen d c x
  · rw [if_pos hle, dif_pos hle] at hw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hw
    refine ⟨by omega, by omega, ?_⟩
    exact cellCount_prefix_config d c w.length x left suffix hle
  · rw [if_neg hle, dif_neg hle] at hw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hw
    refine ⟨by omega, by omega, ?_⟩
    have hne : cells (counted x) ++ suffix ≠ [] := by
      intro hempty
      have hl := congrArg List.length hempty
      simp [cells_length, counted_length] at hl
      try omega
    rw [cellCount_of_cells (acceptState d c)
      ((cells (header d c x)).reverse ++ left)
      (cells (counted x) ++ suffix) hne]
    simp only [List.length_append, List.length_reverse, cells_length,
      nested_length]
    omega

theorem accepting_word (d c : Nat) (x : List Bool) (head : Int)
    (left suffix : List (Fin 3)) {w : List Bool} {hf : Int}
    {zf : BoundedConfig (d + c + 4) 3}
    (hw : run (parserProgram d c) 2 w head
      (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some (hf, zf))
    (ha : zf.state.val = 0) :
    w = List.replicate (headerLen d c x + 1) false ∧
      hf = head + (headerLen d c x : Int) ∧
      zf = fromCells (acceptState d c)
        ((cells (header d c x)).reverse ++ left)
        (cells (counted x) ++ suffix) := by
  have hfull := parser_run d c x head left suffix
  exact accepting_zipper_word_eq (2 : Fin 3) (parserProgram d c)
    (parser_falseOnly d c) (headerLen d c x + 1) head
    (fromCells (startState d c) left (cells (nested d c x) ++ suffix))
    (fromCells (acceptState d c)
      ((cells (header d c x)).reverse ++ left)
      (cells (counted x) ++ suffix))
    (head + (header d c x).length) (by simpa [headerLen] using hfull)
    (by simp [fromCells_state, acceptState]) hw ha

theorem parser_spec (d c : Nat) :
    (∀ (x : List Bool) (head : Int) (left suffix : List (Fin 3)),
      run (parserProgram d c) 2
        (List.replicate ((header d c x).length + 1) false) head
        (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
      some (head + (header d c x).length,
        fromCells (acceptState d c)
          ((cells (header d c x)).reverse ++ left)
          (cells (counted x) ++ suffix))) ∧
    (∀ (x : List Bool) (head : Int) (left suffix : List (Fin 3))
      (w : List Bool) (hf : Int) (zf : BoundedConfig (d + c + 4) 3),
      run (parserProgram d c) 2 w head
        (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some (hf, zf) →
      w = List.replicate w.length false ∧
        w.length ≤ (header d c x).length + 1 ∧
        head ≤ hf ∧ hf ≤ head + ((header d c x).length : Int) ∧
        cellCount zf =
          left.length + (nested d c x).length + suffix.length) ∧
    (∀ (x : List Bool) (head : Int) (left suffix : List (Fin 3))
      (w : List Bool) (hf : Int) (zf : BoundedConfig (d + c + 4) 3),
      run (parserProgram d c) 2 w head
        (fromCells (startState d c) left (cells (nested d c x) ++ suffix)) =
        some (hf, zf) →
      zf.state.val = 0 →
      w = List.replicate ((header d c x).length + 1) false ∧
        hf = head + ((header d c x).length : Int) ∧
        zf = fromCells (acceptState d c)
          ((cells (header d c x)).reverse ++ left)
          (cells (counted x) ++ suffix)) ∧
    (∀ r ∈ compile (parserProgram d c), r.read < 3 ∧ r.action.write < 3) := by
  refine ⟨parser_run d c, ?_, ?_, compiled_symbols d c⟩
  · intro x head left suffix w hf zf hw
    simpa [headerLen] using every_raw d c x head left suffix hw
  · intro x head left suffix w hf zf hw ha
    simpa [headerLen] using accepting_word d c x head left suffix hw ha

end PakFixedPolyomino.ULogTernaryNestedHeaderParserSpace
